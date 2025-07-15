use aiken/builtin
use aiken/collection/list
use aiken/option.{is_none}
use cardano/transaction.{OutputReference, Transaction, InlineDatum}
use cardano/assets.{quantity_of, lovelace_of}
use cardano/address.{Credential}
use aiken/interval.{IntervalBound, IntervalBoundType, Finite}

pub type Datum {
  lender_pkh: ByteArray,
  daily_fee: Int,     // Lovelace per day
  min_days: Int,
  max_days: Int,
  auto_relist: Bool,
  renter_pkh: Option<ByteArray>,  // None if available
  deadline: Option<Int>,          // None if available
  nft_policy: ByteArray,          // NFT policy ID
  nft_name: ByteArray             // NFT asset name
}

pub type Redeemer {
  Rent { days: Int }
  Extend { days: Int }
  Claim
}

validator nft_rental {
  spend(
    datum_opt: Option<Datum>, 
    rdx: Redeemer, 
    output_ref: OutputReference,
    tx: Transaction
  ) {
    expect Some(dat) = datum_opt
    
    // Get validity range bounds
    let lower_bound = tx.validity_range.lower_bound
    let upper_bound = tx.validity_range.upper_bound
    
    // Extract time values from bounds
    let lower = when lower_bound is {
      IntervalBound { bound_type: Finite(x), .. } -> x
      _ -> fail @"Non-finite lower bound"
    }
    
    let upper = when upper_bound is {
      IntervalBound { bound_type: Finite(x), .. } -> x
      _ -> fail @"Non-finite upper bound"
    }
    
    // Get the signer
    let signer_opt = when tx.extra_signatories is {
      [] -> None
      [first, ..] -> Some(first)
    }
    let signer = when signer_opt is {
      Some(s) -> s
      None -> fail @"No signer"
    }

    // Find the input being spent
    let input_opt = list.find(
      tx.inputs,
      fn(i) { i.output_reference == output_ref }
    )
    let input = when input_opt is {
      Some(i) -> i
      None -> fail @"Own input not found"
    }
    
    let own_addr = input.output.address

    // Verify input contains the NFT
    let has_nft = quantity_of(
      input.output.value, 
      dat.nft_policy, 
      dat.nft_name
    ) == 1
    
    expect has_nft

    // Helper to calculate total paid to lender
    let total_paid_to_lender = fn(required: Int) -> Bool {
      let total = list.foldr(
        tx.outputs,
        0,
        fn(out, acc) {
          // Check if payment credential matches lender's pubkey hash
          when out.address.payment_credential is {
            Credential.VerificationKey(pkh) ->
              if pkh == dat.lender_pkh {
                acc + lovelace_of(out.value)
              } else {
                acc
              }
            _ -> acc
          }
        }
      )
      total >= required
    }

    when rdx is {
      Rent { days } -> {
        // Only if available (no renter)
        is_none(dat.renter_pkh) &&
        days >= dat.min_days &&
        days <= dat.max_days &&
        days > 0 &&
        // Payment to lender (summed)
        total_paid_to_lender(dat.daily_fee * days) &&
        // Produce new UTxO at same addr with updated datum and NFT preserved
        list.any(
          tx.outputs,
          fn(out) {
            let new_datum = Datum {
              lender_pkh: dat.lender_pkh,
              daily_fee: dat.daily_fee,
              min_days: dat.min_days,
              max_days: dat.max_days,
              auto_relist: dat.auto_relist,
              renter_pkh: Some(signer),
              deadline: Some(lower + days * 86400000),  // milliseconds per day
              nft_policy: dat.nft_policy,
              nft_name: dat.nft_name
            }
            
            out.address == own_addr &&
            out.datum == InlineDatum(new_datum) &&
            quantity_of(out.value, dat.nft_policy, dat.nft_name) == 1
          }
        )
      }
      
      Extend { days } -> {
        // Only active renter can extend
        let current_renter_opt = dat.renter_pkh
        let current_renter = when current_renter_opt is {
          Some(r) -> r
          None -> fail @"No active renter"
        }
        let deadline_opt = dat.deadline
        let deadline = when deadline_opt is {
          Some(d) -> d
          None -> fail @"No deadline for active rental"
        }
        
        current_renter == signer &&
        upper < deadline &&
        days > 0 &&
        // Payment for extension
        total_paid_to_lender(dat.daily_fee * days) &&
        // Produce new UTxO with extended deadline
        list.any(
          tx.outputs,
          fn(out) {
            let new_datum = Datum {
              lender_pkh: dat.lender_pkh,
              daily_fee: dat.daily_fee,
              min_days: dat.min_days,
              max_days: dat.max_days,
              auto_relist: dat.auto_relist,
              renter_pkh: dat.renter_pkh,
              deadline: Some(deadline + days * 86400000),
              nft_policy: dat.nft_policy,
              nft_name: dat.nft_name
            }
            
            out.address == own_addr &&
            out.datum == InlineDatum(new_datum) &&
            quantity_of(out.value, dat.nft_policy, dat.nft_name) == 1
          }
        )
      }
      
      Claim -> {
        // Only lender can claim
        signer == dat.lender_pkh &&
        
        // Check if claimable (available or expired rental)
        (when dat.renter_pkh is {
          None -> True  // Available
          Some(_) -> {
            let deadline_opt = dat.deadline
            let deadline = when deadline_opt is {
              Some(d) -> d
              None -> fail @"No deadline for active rental"
            }
            lower > deadline  // Expired
          }
        }) &&
        
        // Prevent redundant relist if already available and auto_relist
        (when dat.renter_pkh is {
          None -> !dat.auto_relist
          Some(_) -> True
        }) &&
        
        // Output NFT to lender or relist
        if dat.auto_relist {
          list.any(
            tx.outputs,
            fn(out) {
              let new_datum = Datum {
                lender_pkh: dat.lender_pkh,
                daily_fee: dat.daily_fee,
                min_days: dat.min_days,
                max_days: dat.max_days,
                auto_relist: dat.auto_relist,
                renter_pkh: None,
                deadline: None,
                nft_policy: dat.nft_policy,
                nft_name: dat.nft_name
              }
              
              out.address == own_addr &&
              out.datum == InlineDatum(new_datum) &&
              quantity_of(out.value, dat.nft_policy, dat.nft_name) == 1
            }
          )
        } else {
          list.any(
            tx.outputs,
            fn(out) {
              (when out.address.payment_credential is {
                Credential.VerificationKey(pkh) -> pkh == dat.lender_pkh
                _ -> False
              }) &&
              quantity_of(out.value, dat.nft_policy, dat.nft_name) == 1
            }
          )
        }
      }
    }
  }

  else(_) {
    fail @"unsupported purpose"
  }
}
