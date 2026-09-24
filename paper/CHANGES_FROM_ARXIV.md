# Differences from the arXiv version

The formalization follows `paper/rwrs.tex`, which is the text of
[arXiv:2604.13968v1](https://arxiv.org/abs/2604.13968v1), typeset in the
Annals of Probability class `imsart`, with the corrections below.  The arXiv
source will be replaced by the corrected text.  The unmodified arXiv source is
`paper/rwrs-arxiv.tex`, byte for byte, and `paper/arxiv/` holds the other files
of the arXiv e-print (`main.bbl`, `Figures/`, `00README.json`).

Two changes are mathematical.  Both concern the passage from the Carne--Varopoulos
bound to hypothesis (H3) of `prop:poly-growth`, and neither changes the
statement of any theorem, proposition or lemma.  All other changes are
typographical and are listed after them.  Line numbers refer to
`paper/rwrs.tex`.

## Mathematical corrections

### 1. After Theorem 1.3 (`thm:stab`), line 143

arXiv:

> Part (ii) from Proposition `prop:poly-growth`, both combined with the
> universal heat kernel bound [...] and the Carne--Varopoulos sub-Gaussian
> displacement bound [LP16, Section 13.2], which supplies hypothesis (H3) with
> d_w = 2.

Corrected:

> Part (ii) from the proof of Proposition `prop:poly-growth`, both combined
> with the universal heat kernel bound [...]. In part (ii), the
> Carne--Varopoulos transition bound [LP16, Theorem 13.4] and the volume growth
> at o supply, with d_w = 2, the displacement estimate at o that the proof uses
> in place of hypothesis (H3).

Why: bounded degree does not imply (H3) with `d_w = 2`.  On the 3-regular tree,
`dist(X_n, x)/n → 1/3` almost surely, so `P_x(τ_{B(x,n/4)} ≤ n) → 1` while
`C exp(-c r²/n) → 0` at `r = n/4`.  Adding the volume growth of Theorem 1.3(ii)
does not help, because (H3) is required at every starting vertex: a ray with a
binary tree of height `k` attached at the vertex `4^k` satisfies
`|B(0,R)| ≤ 6R`, and a walk started deep inside one of the attached trees
escapes linearly for `6r` steps.  Part (i) uses no displacement bound.  What
part (ii) needs is the exit estimate at the single vertex `o`, supplied by
correction 2.

### 2. After Proposition `prop:poly-growth`, line 1243

arXiv:

> On bounded-degree graphs, hypothesis (H3) holds with d_w = 2 by the
> Carne--Varopoulos maximal displacement bound [LP16, Section 13.2], recovering
> the condition p > d_f/d_s and hence Theorem 1.3(ii).

Corrected:

> The proof uses hypothesis (H3) only in Step 3, only at x = o, and only
> through the bound P_o(τ_{B(o,R_N)} ≤ N) = O(N^{-r}). On bounded-degree graphs
> this bound follows with d_w = 2 from hypothesis (H1) and the
> Carne--Varopoulos bound P_o(X_j = y) ≤ 2 sqrt(deg(y)/deg(o))
> exp(-dist(o,y)²/(2j)) for j ≥ 1 [LP16, Theorem 13.4]. Indeed, a union bound
> over the time j ≤ N and the vertex y at which the walk first leaves B(o,R_N)
> gives P_o(τ_{B(o,R_N)} ≤ N) ≤ 2 sqrt(d) C_vol N (R_N+1)^{d_f} N^{-C_0²/2},
> which is O(N^{-r}) once C_0 is large. This recovers the condition
> p > max(d_f/d_s, 1) and hence Theorem 1.3(ii), even though hypothesis (H3)
> itself can fail on bounded-degree graphs.

Why: the arXiv sentence claims (H3) on every bounded-degree graph, which is
false by the examples under correction 1.  The corrected sentence proves the
one consequence of (H3) that the proof of `prop:poly-growth` uses.  The vertex
`y` is at distance `⌊R_N⌋ + 1 > R_N` from `o`, there are at most
`C_vol (R_N+1)^{d_f}` such vertices by (H1), and `R_N² = C_0² N log N` when
`d_w = 2`, which gives the displayed bound.  With `d_w = 2` the threshold
`2d_f/(d_w d_s)` of the proposition is `d_f/d_s`, and the proposition carries
the maximum with 1, which the arXiv sentence omitted.  Proposition
`prop:poly-growth` itself is unchanged and still assumes (H3).

## Typographical changes

These change no mathematics.

| location | arXiv | `paper/rwrs.tex` |
|---|---|---|
| preamble and front matter, lines 1-80 | `amsart` class, page geometry, table-of-contents and title-case patches, `\date`, `\keywords`, `\subjclass` | `imsart` class with `aop` option, `\startlocaldefs`/`\endlocaldefs`, `frontmatter` with `aug`, `keyword` and `runtitle`; `\tableofcontents` no longer `\small` |
| `thm:OS`(iii), line 99 | "If ... for some p>3, then ... for every q ∈ [1,(p−1)/2) and x ∈ V." | "Suppose ... for some p>3. Then ... for every q ∈ [1,(p−1)/2) and every x ∈ V." |
| `eq:gn-def`, lines 211-215 | one-line display, order g_n, A_n, Σ_n | two-line `gathered`, order g_n, Σ_n, then A_n |
| after `eq:gn-def`, line 217 | "and Σ_n(x) ≍ ..." | "while Σ_n(x) ≍ ..." |
| figures, lines 87, 226-230, 787, 1492-1496, 1595, 1825 | widths in `\textwidth`; `[ht]` placement for the five figures after the first | widths in `\linewidth`; `[t]` placement |
| proof of `thm:nested-vol`, lines 460-464 | inline max over connected sets | the same expression displayed |
| opening of `sec:supercritical`, lines 524-529 | "Its expectation is E[ξ]A_n(x), where A_n(x) = ... is the inverse-degree clock" inline | "with expectation E[ξ]A_n(x), where" followed by A_n(x) displayed |
| proof of `lem:clock-no-dom`, lines 547-551 | inline difference of expected local times; a commented-out citation; "therefore" | the difference displayed; comment and "therefore" removed |
| proof of `prop:critical`, lines 705-709 | s_M and δ_M defined inline; "such that" | defined in a display; "so that" |
| proof of `lem:local-time`, lines 1047-1051 | one-line display | two-line `align*` |
| proof of `lem:dyadic`, lines 1113-1121 | Z and the bound on (W_n + E[ξ]n/d)^+ inline | both displayed |
| proof of `lem:good-walk`(b), lines 1146-1150 | convexity bound on Y_k^p inline | displayed |
| proof of `prop:subcritical`, lines 1205-1214 | tail integral displayed, polynomial contribution inline | tail integral in `equation*`, polynomial contribution displayed |
| proof of `prop:poly-growth`, Step 1, lines 1268-1269 | `align*` rows without alignment points or line break | `&` alignment and `\\` line break |
| end matter, lines 1997-2007 | `\subsubsection*{Acknowledgments}` with funding; `plainnat` | `acks` and `funding` environments; `imsart-nameyear` |
