// Quorum: a common-subexpression fixture.
//
// A committee action needs between 3 and 6 yes-votes, written as two bounds on
// the same tally:
//
//   count(...) >= 3
//   count(...) <= 6
//
// The tally is the same pure expression in both bounds, so the compiler emits
// it once rather than walking the eight votes twice, and it fuses the two
// comparisons into a single range check (`3 7 WITHIN`). The fixture pins that
// the shared work is shared and that both bounds stay independently enforced.

contract Quorum {
    extern const k: PublicKey;

    spend act(relaxed votes: [Bool; 8], s: Signature) {
        require {
            count(v in votes where v => true) >= 3,
            count(v in votes where v => true) <= 6,
            k.check(s)
        }
    }

    keypath None;
}
