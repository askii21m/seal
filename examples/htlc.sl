// Hash time-locked contract: the building block for atomic swaps and
// Lightning-style payment routing. Funds leave by one of two script paths,
// or cooperatively by the key path:
//
//   swap    the counterparty reveals a preimage of `hashlock` and signs
//   refund  the original owner reclaims after `timelock` expires
//
// If both parties agree they never touch the script: they close on the key
// path with a single aggregate signature, indistinguishable from an ordinary
// payment.

contract Htlc {
    extern const refund_key: PublicKey;
    extern const swap_key:   PublicKey;
    extern const timelock:   LockTime.Absolute;
    extern const hashlock:   Bytes<32>;

    // The counterparty reveals the preimage and signs.
    spend swap(preimage: Bytes<32>, signature: Signature) {
        require {
            sha256(preimage) == hashlock,
            swap_key.check(signature)
        }
    }

    // The swap timed out: the owner reclaims after the locktime.
    spend refund(signature: Signature) {
        require {
            after(timelock),
            refund_key.check(signature)
        }
    }

    // Cooperative close: both parties sign jointly on the key path.
    keypath PublicKey.MuSig2([swap_key, refund_key]);
}
