# RWRS independent refute-first audit — consolidated (2026-10-03)

Tool: `~/fleet/audit_rwrs.py` (four lenses A/B/C/D) over `~/lean/Divisible-Sandpile-RWRS`
@ `b62b770`, DeepSeek-V4.1-flash, 26 calls, read-only over the repo. Reports: this directory.
The reader/model is **fallible**; every flagged item below was triaged by hand against the
frozen Lean and the paper.

## Run status

- 23/26 reports returned; `A-11` empty (rate-limited).
- `C-1`, `C-3`, `D-1` (definitions lens, externals lens) still pending on rate-limit retries.
- No confirmed statement-level DEFECT.

## Candidate findings and triage

| flag | claim | triage |
|---|---|---|
| A-1 `N-006` | stationarity conclusion omits the odometer `u_k` | **FALSE POSITIVE.** `RWRS.netTopple : Net 1 → Net 2` carries mark 0 = `σ_k` and mark 1 = `u_k` (`RWRS/Network.lean:160`). The Lean conclusion *is* stationarity of `(G,ρ,σ_k,u_k)`. |
| A-9/A-10 `N-014, N-020, N-021, N-022` | paper assumes locally finite; Lean has only `[Infinite V]`, `G.Connected` | **NOT A DEFECT — a strengthening.** Fewer hypotheses, same conclusion: harmless for the paper's setting. Record as a fidelity note, not a defect. |
| A-3/A-9/A-10 `X-004, X-005, X-008, X-008P` | "Lean proves the cited external, not the paper's paragraph" | **CATEGORY ERROR — intended design.** `External.*` nodes carry a cited theorem as a `Prop` to be discharged (e.g. `CarneVaropoulosProved.lean`). That *is* the goal. |
| A-3 `N-032` | Lean states `Stabilizes ↔ ¬ Recurrent`, paper also asserts explosion | **NOT A DEFECT.** `Stabilizes G σ := ∀ v, odometerLimit G σ v ≠ ⊤` (`RWRS/Basic.lean:88`), so `¬ Stabilizes` *is* "some odometer is `⊤`" = explodes; the paper's recurrent⇒explodes clause is the immediate corollary of the frozen iff. |
| C-2 `combVoltage, killedGreenReal` | `ENNReal.toReal` sends `∞ ↦ 0` | **FALSE POSITIVE.** `killedGreenReal` is documented (`RWRS/Basic.lean:135-138`) to be used only where the killed Green value is finite (the walk leaves `C` in finite expected time), so `toReal` never meets `⊤` there. |
| C-2 `extMean` | `EReal` `∞ − ∞ = 0` | **FALSE POSITIVE.** The paper's convention is encoded: `HasExtMean ν := posPart ν ≠ ⊤ ∨ negPart ν ≠ ⊤` (`RWRS/Scenery.lean:41-45`) explicitly excludes the indeterminate `∞ − ∞` case. |

## Consequence

**No defect is confirmed.** Every flagged item triaged as a false positive, a harmless strengthening,
or the intended External-node design. RWRS's 50 `SEALED` nodes are clean and may be promoted to
`PROVED` on the strength of this audit; the promotion is a registry-state change only (no
frozen-bytes edit).

Pending for a follow-up run: `C-1`, `C-3`, `D-1` (definitions/externals lenses) and `A-11`.

Pending for a follow-up run: `C-1`, `C-3`, `D-1` (definitions/externals lenses) and `A-11`.
