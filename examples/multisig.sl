// Generic M-of-N multisig, the standard taproot arrangement: unanimous
// cooperation on the key path (a MuSig2 aggregate over all N keys, a single
// signature that reveals no script), with an M-of-N threshold in a script-path
// leaf for when not everyone can sign.
//
// M, N, and the key list are template parameters bound before compilation, so
// each instantiation is fully concrete and the compiler checks len(keys) == N.
// The contract-level `require` is an instantiation-time precondition and costs
// nothing on chain.
//
// Every signature slot is always present in the fallback witness: a slot that
// declines is an empty push, a valid signature counts toward the threshold, and
// anything else aborts the script. The threshold is `== M`, not `>= M`:
// requiring EXACTLY M valid signatures keeps the witness unique and so
// non-malleable, whereas `>= M` would let a third party strip an excess
// signature to a different valid witness. `== M` still spends with any M of the
// N: M sign and the rest decline. This is Miniscript's `multi_a`.

contract Multisig {
    extern const M:    Int;
    extern const N:    Int;
    extern const keys: [PublicKey; N];

    require 1 <= M <= N;

    spend fallback(sigs: [Signature; N]) {
        require sum(k in keys, s in sigs => k.check(s)) == M;
    }

    // Cooperative spend by all N keys, aggregated off chain.
    keypath PublicKey.MuSig2(keys);
}
