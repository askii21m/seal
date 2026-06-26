// Phase 4 consensus differential harness.
//
// Runs a tapscript leaf script + witness stack through Bitcoin Core's REAL
// script interpreter (vendor/bitcoin, EvalScript under SigVersion::TAPSCRIPT),
// with a mock signature checker mirroring our test oracle (a signature is valid
// iff it equals the 64-byte 0xAA marker). This isolates T4 -- the tapscript
// EXECUTION semantics our interpreter models -- from the crypto (T5), so no
// real BIP340 signing or sighash is needed; the differential then asks only:
// does our interpreter accept/reject exactly as Core's does, on OUR scripts?
//
// Protocol: one case per stdin line,
//     <leaf_hex>|<witelem0_hex>|<witelem1_hex>|...
// where witness elements are bottom-to-top and an empty element is an empty
// field. Prints "1" (accept) or "0" (reject) per line. Tapscript success is
// EvalScript returning true with exactly one truthy element left (Core's
// CLEANSTACK + EVAL_FALSE tail), which our interpreter also enforces.

#include <script/interpreter.h>
#include <script/script.h>
#include <script/script_error.h>
#include <uint256.h>

#include <algorithm>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>

static std::vector<unsigned char> from_hex(const std::string& s) {
    std::vector<unsigned char> out;
    for (size_t i = 0; i + 1 < s.size(); i += 2) {
        out.push_back(static_cast<unsigned char>(std::stoi(s.substr(i, 2), nullptr, 16)));
    }
    return out;
}

// CastToBool is file-local in Core; reimplement it (true unless all-zero or a
// single trailing 0x80 negative zero).
static bool cast_to_bool(const std::vector<unsigned char>& v) {
    for (size_t i = 0; i < v.size(); ++i) {
        if (v[i] != 0) {
            return !(i == v.size() - 1 && v[i] == 0x80);
        }
    }
    return false;
}

class MockChecker : public BaseSignatureChecker {
public:
    bool CheckSchnorrSignature(std::span<const unsigned char> sig, std::span<const unsigned char>,
                               SigVersion, ScriptExecutionData&, ScriptError* serror) const override {
        static const std::vector<unsigned char> kMarker(64, 0xAA);
        if (sig.size() == kMarker.size() && std::equal(sig.begin(), sig.end(), kMarker.begin())) {
            return true;
        }
        // A non-empty but invalid signature aborts (BIP342); empty is handled
        // before this is called (pushes false). Matches our interpreter.
        if (serror) *serror = SCRIPT_ERR_SCHNORR_SIG;
        return false;
    }
};

int main() {
    MockChecker checker;
    std::string line;
    while (std::getline(std::cin, line)) {
        std::vector<std::string> fields;
        size_t start = 0;
        while (true) {
            size_t p = line.find('|', start);
            if (p == std::string::npos) {
                fields.push_back(line.substr(start));
                break;
            }
            fields.push_back(line.substr(start, p - start));
            start = p + 1;
        }
        std::vector<unsigned char> leaf = from_hex(fields[0]);
        std::vector<std::vector<unsigned char>> stack;
        for (size_t i = 1; i < fields.size(); ++i) {
            stack.push_back(from_hex(fields[i]));
        }

        CScript script(leaf.begin(), leaf.end());
        ScriptExecutionData execdata;
        execdata.m_tapleaf_hash_init = true;
        execdata.m_tapleaf_hash = uint256();
        execdata.m_codeseparator_pos_init = true;
        execdata.m_codeseparator_pos = 0xFFFFFFFF;
        execdata.m_annex_init = true;
        execdata.m_annex_present = false;
        execdata.m_validation_weight_left_init = true;
        execdata.m_validation_weight_left = 1'000'000'000; // never trips for our leaves

        ScriptError err;
        bool ok = EvalScript(stack, script, SCRIPT_VERIFY_NONE, checker, SigVersion::TAPSCRIPT,
                             execdata, &err);
        bool success = ok && stack.size() == 1 && cast_to_bool(stack.back());
        std::cout << (success ? "1" : "0") << "\n";
    }
    return 0;
}
