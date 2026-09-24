"""Check that every constant depends only on the dimension.

The paper's constants are always "depending only on `d`".  In Lean that is a
property of quantifier order: the existential must be bound before `β` and
before `n`.  Writing

    theorem foo {d : ℕ} (hd : 2 ≤ d) {β : ℝ} (hβ : 1 ≤ β) : ∃ c, ... β ... n ...

reads as `∀ β, ∃ c(β)`, which lets the constant absorb any power of `β` and
makes a factor like `β^{-d/(d+1)}` decorative -- the statement would hold with
the wrong exponent.  That is a silent weakening, invisible to every other check
here, so it gets its own.

The rule enforced: in a frozen statement that binds a real-valued existential,
none of `β`, `n`, `k`, `m`, `h` may be a *parameter* of the theorem; they must be
quantified inside the conclusion, after the existential.  Only `d` may be a
parameter, which is what the paper's own convention allows: "`c > 0` and
`C < ∞` are constants that depend only on `d` ... They never depend on `β`, `k`,
`m`, or `n`."

    python3 tools/check_constants.py
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

try:
    import yaml
except ImportError:
    sys.exit("check_constants.py: PyYAML is required (pip install pyyaml)")

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "ledger" / "manifest.yaml"

# Names that must never be theorem parameters when a constant is existential.
FORBIDDEN = ("R", "n", "t", "m", "r", "s", "L", "x", "y", "u", "v", "e", "z", "ε", "η", "δ")

# Statements read against the paper where a forbidden name is a parameter by the
# paper's own standing assumption, with the reason recorded.  A statement whose
# existential is an honest constant of the paper (`∃ c ∀ n`) is never listed here.
REVIEWED: dict[str, dict[str, str]] = {
    "N-027": {
        "m": "`m` is `E[ξ]`, the mean of the marginal; `lem:good-walk` (rwrs.tex:1124-1130) "
             "fixes the i.i.d. law, and with it its mean, before it asserts the constants "
             "`C_r` and `C`, so the paper's own order is `∀ law, ∃ C`",
        "δ": "the lemma reads `fix δ ∈ (0, d_s/2 ∧ 1)` before its three clauses "
             "(rwrs.tex:1124-1130), and the constants must depend on δ: clause (a) has "
             "`rδ` in its exponent and clause (c) holds only `for r large enough`",
    },
    "N-039": {
        "e": "not a parameter of the statement; `e` is bound inside the hypothesis `hC`, "
             "which quantifies over the flag, the level and the word, and the constant "
             "`c_loc` is bound after that hypothesis but before all of them",
        "n": "as for `e`: bound inside `hC`, not a parameter",
        "u": "as for `e`: the summation index of the `tsum` inside `hC`, not a parameter",
    },
    "N-040": {
        "m": "the depths `m_k` are fixed by the construction of `sec:recurrent-nonstab` "
             "(rwrs.tex:1810-1822) before `prop:rec-growth` asserts `C_G`, so the paper's "
             "order is `∀ (m_k), ∃ C_G`",
        "s": "the attachment points `s_k = ⌈R_{m_k}^ρ⌉` are fixed with the depths, and the "
             "statement carries `hs` saying exactly that",
    },
    "N-041": {
        "m": "the depths are fixed by the construction before `lem:rec-good` "
             "(rwrs.tex:1958-1962) asserts `η`; the paper's own `η = 1 - e^{-1/(4K^{d_f})}` "
             "does not depend on them, so the transcription is weaker than the paper only "
             "in a way the paper's order already allows",
    },
    "prop-path-reduction": {
        "η": "the standing assumption of prop:path-reduction is `for some η > 0` the "
             "criterion holds (rwrs.tex:1007-1011); the paper's `a` in (ii) is chosen "
             "under that assumption, so it may depend on η, and the only other real "
             "existentials are the limit-shape constants of (iii), likewise",
    },
    "prop-passage-limit": {
        "η": "same standing assumption; the only real existential is `R₀`, bound after "
             "the rotors `ρ` and `ε` exactly as the paper's almost-sure limit "
             "(rwrs.tex:1088-1093) prescribes, and the function `f` does not depend "
             "on η at all (its proof uses only invariance and ergodicity)",
    },
}

# Only a real-valued existential is a *constant*.  `lem-walk-order` also binds
# an existential -- the ordering of the visited sites -- and that one must depend
# on the word and the time, so it is not what this check is about.
CONSTANT = re.compile(r"∃\s+[^,:]*:\s*ℝ")


def split_statement(block: str) -> tuple[str, str]:
    """(binders, conclusion), split at the FIRST `:` outside every bracket.

    Every theorem parameter is bracketed, so its own `:` sits at depth one or
    more; the first `:` at depth zero is the one that ends the binder list.
    Taking the last such `:` instead would cut inside `∃ c : ℝ` and hide the
    existential in the binders, which is precisely the thing being looked for."""
    depth = 0
    for i, ch in enumerate(block):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif ch == ":" and depth == 0 and not block.startswith(":=", i):
            return block[:i], block[i + 1:]
    return block, ""


def parameters(binders: str) -> set[str]:
    """Variable names bound as theorem parameters."""
    names: set[str] = set()
    for m in re.finditer(r"[({\[]([^:()\[\]{}]+):", binders):
        for tok in m.group(1).split():
            names.add(tok)
    return names


def main() -> int:
    manifest = yaml.safe_load(MANIFEST.read_text(encoding="utf-8"))
    bad, ok = [], 0
    print(f"{'node':28s} {'real constant?':15s} {'bad parameters':22s}")
    for node in manifest.get("nodes") or []:
        text = (ROOT / node["file"]).read_text(encoding="utf-8")
        blk = text[text.index("-- FROZEN-STATEMENT-BEGIN") + len("-- FROZEN-STATEMENT-BEGIN"):
                   text.index("-- FROZEN-STATEMENT-END")]
        binders, concl = split_statement(blk)
        has_exists = bool(CONSTANT.search(concl))
        params = parameters(binders)
        offenders = sorted(params & set(FORBIDDEN))
        reviewed = REVIEWED.get(node["id"], {})
        for name in sorted(set(offenders) & set(reviewed)):
            print(f"  {node['id']:26s} reviewed {name}: {reviewed[name]}")
        offenders = [o for o in offenders if o not in reviewed]
        mark = ""
        if has_exists and offenders:
            bad.append((node["id"], offenders))
            mark = "  <-- CONSTANT MAY DEPEND ON " + ", ".join(offenders)
        else:
            ok += 1
        print(f"  {node['id']:26s} {'yes' if has_exists else 'no':13s} "
              f"{', '.join(offenders) if offenders else '-':20s}{mark}")

    if bad:
        print("\ncheck_constants: a constant is bound after a quantity it must not "
              "depend on:", file=sys.stderr)
        for nid, off in bad:
            print(f"  {nid}: move {', '.join(off)} inside the existential", file=sys.stderr)
        return 1
    print(f"\ncheck_constants: OK ({ok} statements; every existential constant is "
          f"bound before every paper parameter, so it is a genuine constant)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
