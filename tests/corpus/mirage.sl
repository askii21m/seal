// Mirage: a redundant-constraint fixture for the interval engine.
//
// Every clause after `bid in 0..1000` is implied by that range, so all four
// are tautologies the moment the bid is known to be in bounds:
//
//   bid >= 0                always true once bid is in 0..1000
//   bid < 5000              always true
//   bid + bid < 3000        always true (2 * bid is at most 1998)
//   min(bid, 9999) <= 1000  always true (min(bid, 9999) is bid)
//
// The interval analysis recognizes each as constant-true and drops it, so the
// compiled leaf is just the real range check and the signature
// (`0 1000 WITHIN VERIFY <key> CHECKSIG`). The fixture pins that the redundant
// clauses are eliminated and the leaf still certifies over the full Int domain.

contract Mirage {
    extern const k: PublicKey;

    spend claim(relaxed bid: Int, s: Signature) {
        require {
            bid in 0..1000,
            bid >= 0,
            bid < 5000,
            bid + bid < 3000,
            min(bid, 9999) <= 1000,
            k.check(s)
        }
    }

    keypath None;
}
