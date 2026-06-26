// Degrading-multisig vault: the kind of tiered custody a Liana-style wallet
// produces, with no covenants required.
//
// The everyday path is a 2-of-2 of the hot key and a cosigner on the key path:
// one aggregate signature, no script revealed. Two timed fallbacks recover the
// funds if a key goes missing:
//
//   fallback  the hot key alone, after roughly 30 days, if the cosigner is gone
//   recover   the cold key alone, after roughly 90 days, if the hot key is lost
//
// The longer delay on the cold path is the window to notice a compromise and
// rotate through the key path first.

contract Vault {
    extern const hot:      PublicKey;
    extern const cosigner: PublicKey;
    extern const cold:     PublicKey;

    // Cosigner unresponsive: the hot key alone after ~30 days of blocks.
    spend fallback(signature: Signature) {
        require {
            after(LockTime.Relative(blocks: 4320)),
            hot.check(signature)
        }
    }

    // Deep recovery: the cold key alone after ~90 days of blocks.
    spend recover(signature: Signature) {
        require {
            after(LockTime.Relative(blocks: 12960)),
            cold.check(signature)
        }
    }

    // Everyday cooperative spend: hot + cosigner, aggregated off chain.
    keypath PublicKey.MuSig2([hot, cosigner]);
}
