# Erdős Problem #132: second-largest and minimum distance multiplicities

Lean 4 / Mathlib formalisation, paper and verification scripts for

> **Wingate Jones**, *Second-largest and minimum distance multiplicities in planar point sets:
> an upper bound of 15/11, and related results on Erdős Problem #132* (2026).
> The paper is in [`paper/`](paper/) (`paper.pdf`, source `paper.tex`, `refs.bib`).

The author used an AI assistant (Claude, Anthropic) for exploration, computation, formalisation and drafting.

## What is proved

**Summary.** The paper (v2) proves `L ≤ 15/11` for Clemen–Dumitrescu–Liu's Problem 1.6, and `4/3` in Region II.
The Lean formalisation in this repository covers the earlier bound `54/37` (Theorem 1 below, fully formalised).
A Lean formalisation of `15/11` is in progress and not yet included. The paper also proves `k ≥ 3` rare distances
for convex sets with `6 ≤ n ≤ 18`, and a linear lower bound for almost-cocircular convex sets (see the paper).

Throughout, `X ⊂ ℝ²` is finite with `|X| = n`, `Δ`, `Δ₂` and `δ` are the largest, second-largest and smallest
distances determined by `X`, and `μ(d)` is the number of unordered pairs of `X` at distance `d`.

### Theorem 1 (the 54/37 bound): fully formalised, standard axioms only

Clemen, Dumitrescu and Liu (Problem 1.6) asked for
`L = limsup_{n→∞} max_{|X|=n} min{μ(Δ₂), μ(δ)} / n`. The known bounds were `9/7 ≤ L ≤ 3/2`, the upper bound
coming from Vesztergombi's inequality `μ(Δ₂) ≤ 3n/2`. We prove

    min{μ(Δ₂), μ(δ)} ≤ (54/37)·n + C₀      for an absolute constant C₀,

so `L ≤ 54/37 < 3/2`. In Lean (`Erdos132/E132Main.lean`, `Pt = EuclideanSpace ℝ (Fin 2)`):

```lean
theorem Erdos132Main.erdos132_main :
    ∃ C₀ : ℝ, ∀ X : Finset Pt, 2 ≤ X.card →
      ((min (mult X (dist2 X)) (mult X (minDist X)) : ℕ) : ℝ) ≤ 54 / 37 * X.card + C₀
```

`mult X d` counts unordered pairs of distinct points at distance `d`; `diam`, `dist2`, `minDist` are the largest,
second-largest and smallest distances (each `0` if it does not exist, and `mult X 0 = 0`, so no side conditions
beyond `2 ≤ X.card` are needed). The constant is explicit: `C₀ = 5·10⁹`.

### Also formalised (sorry-free, standard axioms only)

- **Vesztergombi 1987** (`Erdos132Ve87.vesztergombi87`, `E132Ve87.lean`): `μ(Δ₂) ≤ 3n/2` for every planar set.
  The paper cites this; here it is proved (2-core argument on the `Δ₂`-graph of `L₁ ∪ L₂`).
- **Hopf–Pannwitz 1934** (`Erdos132Main.hopf_pannwitz`, `E132MainDefs.lean`): `μ(Δ) ≤ n`.
- **Layer bound / Corollary A1** (`E132Layer.lean`, namespace `Erdos132Layer`), with `L₁, L₂` the first two convex
  layers: Theorem A (`theoremA`), Corollary A1 (`corA1`: if no point of `L₁` has 4 points at distance `Δ₂`, then
  `2μ(Δ₂) ≤ 3|L₁| + 2|L₂|`), `corA1_le_card` (`μ(Δ₂) ≤ n` when `|L₁| ≤ 2·|X \ (L₁ ∪ L₂)|`), the unconditional
  form `corA1_uncond`, the CDL layer bound `cdl_layer_bound`, Prop 3 (`deg_core_L2`) and the degree-≤-4 lemma
  (`deg_core_L1_le_four`).

### Convex position, n = 7, 11, 13 (uses `bv_decide`; axiom disclosed below)

At least three distances occur between 1 and n times (`rareDistsS S = {d | 1 ≤ μ(d) ≤ n}`):

```lean
theorem Erdos132Convex.erdos132_convex7_finset  (S : Finset Pt) (hn : S.card = 7)
    (hS : ConvexIndependent ℝ ((↑) : S → Pt)) : 3 ≤ (rareDistsS S).card
theorem Erdos132Convex.erdos132_convex11_finset (S : Finset Pt) (hn : S.card = 11)
    (hS : ConvexIndependent ℝ ((↑) : S → Pt)) : 3 ≤ (rareDistsS S).card
theorem Erdos132Convex.erdos132_convex13_finset (S : Finset Pt) (hn : S.card = 13)
    (hS : ConvexIndependent ℝ ((↑) : S → Pt)) : 3 ≤ (rareDistsS S).card
```

plus the ordered-polygon versions `erdos132_convex7/11/13 (p : Fin n → Pt) (hp : StrictConvexPolygon p)`.
The geometry (Lemma Q, Lemma R, ranks, the point-set-to-polygon bridge) and the correctness of the BitVec encoding
(`ordNoCE_of_bv`) are proved in Lean; only the final finite unsatisfiability check is done by `bv_decide`.
The n = 7 LRAT certificate is pinned in `Erdos132/lrat/bvNoCE7.lrat` (1.6 MB) and replayed with `bv_check`;
n = 11 and n = 13 run the bundled CaDiCaL on every build (their certificates, 23 MB and 97 MB, are not stored).

## `#print axioms`

The `#print axioms` commands are at the end of the respective files, so `lake build` prints them.

```
'Erdos132Main.erdos132_main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`E132Ve87.lean` (`ve87`, `vesztergombi87`) and `E132Layer.lean` (`theoremA`, `corA1`, `corA1_uncond`,
`cdl_layer_bound`, `corA1_le_card`, `deg_core_L2`, `deg_core_L1_le_four`, `isExt_iff_notMem_convexHull`,
`exists_twoLargest`):

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

Convex position:

```
'Erdos132Convex.erdos132_convex7' depends on axioms:
  [propext, Classical.choice, Quot.sound, Erdos132Convex.bvNoCE7._native.bv_decide.ax_1_14]
'Erdos132Convex.erdos132_convex11' depends on axioms:
  [propext, Classical.choice, Quot.sound, Erdos132Convex.bvNoCE11._native.bv_decide.ax_1_14]
'Erdos132Convex.erdos132_convex13' depends on axioms:
  [propext, Classical.choice, Quot.sound, Erdos132Convex.bvNoCE13._native.bv_decide.ax_1_10]
'Erdos132Convex.erdos132_convex7_finset' depends on axioms:
  [propext, Classical.choice, Quot.sound, Erdos132Convex.bvNoCE7._native.bv_decide.ax_1_14]
'Erdos132Convex.erdos132_convex11_finset' depends on axioms:
  [propext, Classical.choice, Quot.sound, Erdos132Convex.bvNoCE11._native.bv_decide.ax_1_14]
'Erdos132Convex.erdos132_convex13_finset' depends on axioms:
  [propext, Classical.choice, Quot.sound, Erdos132Convex.bvNoCE13._native.bv_decide.ax_1_10]
```

**The `bv_decide` axioms.** In this toolchain (Lean v4.35.0-rc2) `bv_decide` records its one unverified step as an
auxiliary axiom of the form

```
axiom Erdos132Convex.bvNoCE7._native.bv_decide.ax_1_14 :
  Std.Tactic.BVDecide.Reflect.verifyBVExpr bvNoCE7._expr_def_1_10 bvNoCE7._cert_def_1_10 = true
```

Older toolchains used `Lean.ofReduceBool` for the same step; the trust base is the same as for `native_decide`.
The axiom states that Lean's LRAT checker `verifyBVExpr`, which is itself proved correct in Lean together with
the bit-blaster and the AIG→CNF translation, returns `true` on these concrete inputs. The `true` comes from
running the compiled checker, not from the kernel. Trusted: the Lean compiler and runtime. **Not** trusted:
CaDiCaL, the Python CNF encoder `scripts/b3_sat.py`, drat-trim. None of them is involved. Theorem 1,
Vesztergombi, Hopf–Pannwitz and the layer bound use neither `bv_decide` nor `native_decide`.

## Building and checking

Requirements: [elan](https://github.com/leanprover/elan). The toolchain `leanprover/lean4:v4.35.0-rc2` is picked
up from `lean-toolchain`; Mathlib is pinned to tag `v4.35.0-rc2` (rev `065356127b1dc0016f66b7283ce0ce2c4055aa55`).

```sh
lake exe cache get     # download prebuilt Mathlib
lake build             # builds all 11 modules and prints the #print axioms output
```

Build time (Apple silicon laptop, 16 GB RAM, Mathlib from cache): about 6 minutes wall-clock for all 11 modules
(peak about 3 GB RSS). The slowest module is `E132Convex13.lean`, about 4 minutes on its own (CaDiCaL + LRAT check
for n = 13). To skip it, build only the modules you need:

```sh
lake build Erdos132.E132Main           # Theorem 1 (+ Vesztergombi, Hopf–Pannwitz, layer bound)
lake build Erdos132.E132ConvexFinset   # n = 7, 11
lake build Erdos132.E132Convex13       # n = 13 (about 4 min)
```

A single file can be checked with `lake env lean Erdos132/<File>.lean`. There is no `sorry` in any proof;
the remaining occurrences of the word are in comments.

## File map

| path | contents |
|---|---|
| `Erdos132.lean` | root; imports every module below |
| `Erdos132/E132Convex.lean` | convex position, ordered polygons: Lemma Q, ranks, Lemma R, BitVec encoding and its correctness, n = 7 (pinned LRAT) and n = 11 |
| `Erdos132/lrat/bvNoCE7.lrat` | pinned LRAT certificate for n = 7 |
| `Erdos132/E132ConvexFinset.lean` | point-set versions for n = 7, 11; bridge from `ConvexIndependent` to a strictly convex polygon |
| `Erdos132/E132Convex13.lean` | n = 13, both versions (about 4 min) |
| `Erdos132/E132Layer.lean` | layer bound: location lemma, Prop 3, degree ≤ 4, Theorem A, Corollary A1, 2-core |
| `Erdos132/E132Ve87.lean` | Vesztergombi 1987, `μ(Δ₂) ≤ 3n/2` |
| `Erdos132/E132MainDefs.lean` | definitions for Theorem 1 (`mult`, `diam`, `dist2`, `minDist`, direction fields, constants), Hopf–Pannwitz, LP certificates |
| `Erdos132/E132ConvexCurve.lean` | direction-measure counting on convex curves (walk lemmas, edge counts) |
| `Erdos132/E132MainLocal.lean` | local geometry: exact identities, T-edges, rungs, (R1)/(R2)/(R3), corner lemma, bad-edge bounds |
| `Erdos132/E132MainRegions.lean` | Regions I, II, III; ownership/pairing bookkeeping |
| `Erdos132/E132MainDegen.lean` | degenerate regime `Δ > 1.94 Δ₂` |
| `Erdos132/E132Main.lean` | assembly: `erdos132_main` |
| `paper/` | `paper.tex`, `refs.bib`, `paper.pdf` |
| `scripts/` | verification scripts cited in the paper's appendix (see below) |

### Scripts

Python 3 with `numpy`, `scipy`, `sympy`, `mpmath`, and `python-sat` (for `b3_*`). None of these computations is a
proof step of Theorem 1; they are independent checks, described in the appendix "Computational verification" of
the paper. The paper refers to the directory as `problems/132/scripts/`; in this repository it is `scripts/`.

- Theorem 1: `writeup_a2_checks.py` (58 exact assertions, sections C1–C11), `ref2_numeric.py`,
  `ref2_ownership.py`, `ref_degen.py`, `degen_check.py`, `ref2_degen.py`, `ref_checks.py`, `a2_checks.py`.
- Layer bound: `va1b_exact.py`, `va1b_cases.py`, `va1b_case1.py`, `va1b_case2_margin.py`, `va1c_sympy.py`,
  `va1c_local.py`, `va1_clique.py`, `va1_cyclo.py`, `va1c_random.py` (helper: `va1_common.py`).
- Convex position: `ver_classification_k.py`, `ver_hexagons.py`, `counting_parity.py`, `b3_sat.py`, `b3_enum.py`,
  `b3_validate.py`, `b3_drup_check.py`, `b3_drat_trim.py`, `b3_core.py`, `b3_run_all.sh`.

## Deviations of the formalisation from the paper

The Lean proof of Theorem 1 follows the paper's proof, with these differences:

- **Vesztergombi's inequality is proved, not cited** (`E132Ve87.lean`, 2-core double counting on the `Δ₂`-graph
  of `L₁ ∪ L₂`). Hopf–Pannwitz is proved in `E132MainDefs.lean`.
- **The bad-edge bounds (KK, DD, (c2)) use direction-measure counting** (`E132ConvexCurve.lean`) instead of arc
  length. The paper's lens arc-length lemma is not needed and is not formalised.
- **`turning_sum_le` needs a closedness hypothesis.** The form without it is false (a Bernstein-set
  counterexample); `turning_sum_le_closure` is used instead.
- **Lemma 7.1 is restated with support points** instead of a boundary path, and the resulting bound on mixed
  T-edges is `1200` instead of `71`. This only changes the additive constant.
- **Constants.** All region bounds use the uniform additive constant `cBad + 100` with `cBad = 2·10⁷`, and
  `C₀ = 5·10⁹ ≥ 3N₀ + cBad + 100` with `N₀ = 1.51·10⁹`.
- **Conventions.** `mult` counts unordered pairs of distinct points; `diam`, `dist2`, `minDist` are `0` when
  undefined, so the only hypothesis is `2 ≤ X.card`.

Some docstrings in the `E132Main*` files date from the skeleton phase of the formalisation and still mention
remaining `sorry`s or a cited `vesztergombi87`. They are historical; the `#print axioms` output is authoritative.

## License

- Code (Lean sources, LRAT certificate, scripts, build files): Apache License 2.0, see [`LICENSE`](LICENSE),
  the same license as Mathlib.
- Paper (`paper/`): Creative Commons Attribution 4.0 International (CC BY 4.0), see
  [`LICENSE-paper`](LICENSE-paper).

## Citation

See [`CITATION.cff`](CITATION.cff).
