// CatBounty: a quantized linear classifier expressed as a spending condition.
//
// The output is claimable by the registered solver who supplies a 28x28
// binarized image that the baked-in logistic-regression model scores above a
// threshold. The sigmoid is monotone, so "probability above p0" reduces to
// "linear score above threshold", and the on-chain check is a single weighted
// sum compared against a constant.
//
// This is the corpus stress test for lowering and certification: 784 weighted
// inputs unroll into one conditional-add chain, pixels whose weight is zero are
// dropped from both the script and the witness, and the score interval folds
// exactly from the instantiated weights so the leaf certifies over its full
// symbolic domain.

contract CatBounty {
    extern const weights:   [Int; 784];   // trained int8 weights, row-major
    extern const bias:      Int;
    extern const threshold: Int;
    extern const solver:    PublicKey;     // the registered claimant

    spend claim(relaxed drawing: [Bool; 784], signature: Signature) {
        // Each set pixel contributes its weight; unset pixels contribute zero.
        // The parallel binders zip `drawing` against `weights` (lengths are
        // const and checked equal at compile time).
        let score = bias + sum(px in drawing, w in weights where px => w);

        require {
            score > threshold,
            solver.check(signature)
        }
    }

    keypath None;
}
