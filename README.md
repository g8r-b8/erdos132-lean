# Erdős Problem #132: second-largest and minimum distance multiplicities

Lean 4 / Mathlib formalisation, paper and verification scripts for

> **Wingate Jones**, *Second-largest and minimum distance multiplicities in planar point sets:
> an upper bound of 4/3, and related results on Erdős Problem #132* (2026).
> The paper is in [`paper/`](paper/) (`paper.pdf`, source `paper.tex`, `refs.bib`).

The author used an AI assistant (Claude, Anthropic) for exploration, computation, formalisation and drafting.

## What is proved

**Summary (paper v3).** The paper proves `L ≤ 4/3` for Clemen–Dumitrescu–Liu's Problem 1.6 (Theorem 1(a));
`21/16` when τ ≤ √3/2 − 1/50 or τ ≥ √3/2 + 3/100 (Theorem 1(b)); and `9n/7 + O(n^{2/3})` for τ > 1, matching the
global lower bound 9/7 (Theorem 1(c)). **Theorem 1(a), the `4/3` bound, is fully formalised in Lean** (standard
axioms only; the compiled modules also pass `leanchecker`). Theorems 1(b) and 1(c) are not yet formalised
(in progress).

The earlier bounds `15/11` (paper v2's main theorem, kept in v3 as the backbone of the proof) and `54/37`
(Appendix B of the paper) are also fully formalised. The paper also proves `k ≥ 3` rare distances
for convex sets with `6 ≤ n ≤ 18`, and a linear lower bound for almost-cocircular convex sets (see the paper).

Throughout, `X ⊂ ℝ²` is finite with `|X| = n`, `Δ`, `Δ₂` and `δ` are the largest, second-largest and smallest
distances determined by `X`, and `μ(d)` is the number of unordered pairs of `X` at distance `d`.

### Theorem 1(a) (the 4/3 bound): fully formalised, standard axioms only

Clemen, Dumitrescu and Liu (Problem 1.6) asked for
`L = limsup_{n→∞} max_{|X|=n} min{μ(Δ₂), μ(δ)} / n`. The known bounds were `9/7 ≤ L ≤ 3/2`, the upper bound
coming from Vesztergombi's inequality `μ(Δ₂) ≤ 3n/2`. We prove

    min{μ(Δ₂), μ(δ)} ≤ (4/3)·n + C₀      for an absolute constant C₀,

so `L ≤ 4/3`. In Lean (`Erdos132/E132Main43.lean`):

```lean
theorem Erdos132Main.erdos132_main43 :
    ∃ C₀ : ℝ, ∀ X : Finset Pt, 2 ≤ X.card →
      (min (mult X (dist2 X)) (mult X (minDist X)) : ℝ) ≤ 4 / 3 * X.card + C₀
```

The six `E132Main43*.lean` files (about 4,300 lines) add the paper's Theorem N3 (the average weight of `R` is at
most `8`: `Σ_{y∈R}(deg y + m_y) ≤ 8|R| + C₃`, via the classification of heavy points, Lemma Pin and a charging
argument) to the `15/11` development below, which they import unchanged.

### The 15/11 bound: fully formalised, standard axioms only

The previous version of the paper proved

    min{μ(Δ₂), μ(δ)} ≤ (15/11)·n + C₀.

In Lean (`Erdos132/E132Main15.lean`, `Pt = EuclideanSpace ℝ (Fin 2)`):

```lean
theorem Erdos132Main.erdos132_main15 :
    ∃ C₀ : ℝ, ∀ X : Finset Pt, 2 ≤ X.card →
      (min (mult X (dist2 X)) (mult X (minDist X)) : ℝ) ≤ 15 / 11 * X.card + C₀
```

The six `E132Main15*.lean` files (about 5,300 lines) build on the `54/37` development below, which they import
unchanged. The constant is the same explicit `C₀ = 5·10⁹`. The refinement `4/3` in Region II of paper v2 (via Theorem N2) is
**not** formalised; it is not needed for `15/11` and is superseded by the `4/3` bound above.

### The 54/37 bound: fully formalised, standard axioms only

The paper's Appendix B proves the weaker bound

    min{μ(Δ₂), μ(δ)} ≤ (54/37)·n + C₀,

by a different argument in Regions II and III and without the `R`-term bound. In Lean (`Erdos132/E132Main.lean`):

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
'Erdos132Main.erdos132_main43' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos132Main.erdos132_main15' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos132Main.erdos132_main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The six `E132Main43*` and the six `E132Main15*` modules were also replayed with the kernel checker `leanchecker`
(shipped with the toolchain), which re-checks every declaration of a compiled module:

```sh
for m in Defs Good Frame Classify Charge ""; do lake env leanchecker Erdos132.E132Main43$m; done
for m in Defs N1 RegionII Exact RegionIII ""; do lake env leanchecker Erdos132.E132Main15$m; done
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
CaDiCaL, the Python CNF encoder `scripts/b3_sat.py`, drat-trim. None of them is involved. The `4/3`, `15/11` and
`54/37` bounds, Vesztergombi, Hopf–Pannwitz and the layer bound use neither `bv_decide` nor `native_decide`.

## Building and checking

Requirements: [elan](https://github.com/leanprover/elan). The toolchain `leanprover/lean4:v4.35.0-rc2` is picked
up from `lean-toolchain`; Mathlib is pinned to tag `v4.35.0-rc2` (rev `065356127b1dc0016f66b7283ce0ce2c4055aa55`).

```sh
lake exe cache get     # download prebuilt Mathlib
lake build             # builds all 23 modules and prints the #print axioms output
```

Build time (Apple silicon laptop, 16 GB RAM, Mathlib from cache): about 7 minutes wall-clock for the first 17 modules
(peak about 3 GB RSS); the six `E132Main15*` modules take about 1 minute on top of the `54/37` development, and the
six `E132Main43*` modules about 1 minute more. On a machine with little memory, build the modules one at a
time (`lake build Erdos132.<Module>` in import order), since `lake build` compiles independent modules in parallel.
The slowest module is `E132Convex13.lean`, about 4 minutes on its own (CaDiCaL + LRAT check
for n = 13). To skip it, build only the modules you need:

```sh
lake build Erdos132.E132Main43         # 4/3 bound (+ 15/11, 54/37, Vesztergombi, Hopf–Pannwitz, layer bound)
lake build Erdos132.E132Main15         # 15/11 bound (+ 54/37, Vesztergombi, Hopf–Pannwitz, layer bound)
lake build Erdos132.E132Main           # 54/37 bound (+ Vesztergombi, Hopf–Pannwitz, layer bound)
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
| `Erdos132/E132Main.lean` | assembly of the `54/37` bound: `erdos132_main` |
| `Erdos132/E132Main15Defs.lean` | definitions for the `15/11` bound (`degδ`, `mS`, two-rung vertices, breaks, slots, constants), the exact identity for `μ(δ)`, the linear combination `lp15` |
| `Erdos132/E132Main15N1.lean` | Theorem N1 (`m_y ≤ 4` for all but `10⁷` points of `R`) in Euclidean-local form; `E_bound15` |
| `Erdos132/E132Main15RegionII.lean` | Lemmas A, B, C; Region II: `e(S) ≤ |S| + |P₁| + C` |
| `Erdos132/E132Main15Exact.lean` | the case `τ = √3/2` of Region III: circle-arc rigidity and `exact_breaks` |
| `Erdos132/E132Main15RegionIII.lean` | Region III by slots (`τ < √3/2`) and breaks (`τ = √3/2`) |
| `Erdos132/E132Main15.lean` | assembly: `erdos132_main15` |
| `Erdos132/E132Main43Defs.lean` | definitions for the `4/3` bound (weight `vR`, depth, receivers `Low`, heavy and good points, the structure `Frame43`, fan/cap predicates, constants); the charging lemma `charge_sum`, the linear combination `lp43` |
| `Erdos132/E132Main43Good.lean` | good points without arc length: at most `10¹⁵` heavy points are not good (thin case, big turning); `frame_of_good` |
| `Erdos132/E132Main43Frame.lean` | consequences of a frame: points outside `int K`, D-points, Lemma DN, D–D heights, receivers |
| `Erdos132/E132Main43Classify.lean` | Lemma P (pairs), Lemma M, the hexagon lemma, Lemma H, Lemma Pin; classification of heavy points (fans, caps) |
| `Erdos132/E132Main43Charge.lean` | receivers lie in `R` and have weight `≤ 7`; each receiver has one owner (fans, caps, HF2–HF2) |
| `Erdos132/E132Main43.lean` | Theorem N3, assembly: `erdos132_main43` |
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

### The 4/3 bound

The Lean proof of Theorem 1(a) follows Section 9 of the paper (Theorem N3 and the proof of Theorem 1(a)) on top
of the `15/11` development. It differs from the text in these places (also listed in the paper, Section 14.2):

- **Goodness without arc length.** `y` is good if all unit outer normals of `K` at boundary points within
  *Euclidean* distance `Λ = 464` of `y` are pairwise within `ε₀ = 1/50` (in norm). A heavy point that is not good
  is *thin* (two nearly opposite normals; then `|X ∖ D|` is bounded by a box-packing argument at scale `Λ`, split
  according to `Δ₂ ≥ 10⁶` or not) or has *big turning* in `∂K ∩ B̄(y, 150Λ)`, which happens for `O(1)` points.
  The paper's Lemma T* (packing in thin `K`) is not needed. Exceptional set: at most `10¹⁵` points.
- **Frame without the graph `f`.** The frame lemma is replaced by the structure `Frame43`: the unit outer normal
  `n` at a nearest boundary point, closeness of all normals within distance `6` to `n`, and two points of `K` at
  abscissa `±463` and height `≥ h − 9.31`. (G1) becomes `q_z ≥ h − |q_x|/49` for `q ∉ int K` (slope `1/49`);
  Lemma DN uses the far points and gives `3/100` and `9/400` (paper: `0.0267`, `0.0224`).
- **Intrinsic receivers.** Receivers are the `δ`-neighbours `a ∈ K` of `y` at least `2/3` deeper than `y`; an HF
  point sends one unit to each of its two lower neighbours (the paper: to one). The owner-uniqueness argument works
  for every receiver.
- **Classification and Lemma Pin** use the formal constants with slot tolerance `1/20`; Lemma Pin is proved in
  Euclidean form (law of cosines), with windows `t ≥ 0.7` (fans) and `t ≤ 0.6` (caps) in place of
  `[0.75, 0.95]` and `[0.44, 0.56]`.
- **Not formalised:** Theorems 1(b) (`21/16`) and 1(c) (`9/7` for `τ > 1`); in progress.

### The 15/11 bound

The Lean proof of Theorem 1(a) follows Sections 2–8 of the paper, reusing the `54/37` development for the set-up,
bad edges, Region I, the corner lemma and the degenerate regime (with the deviations listed further below). It
differs from the text in these places:

- **Theorem N1 without arc length.** The paper's arc `γ_y` and the concave-graph description of the flat case are
  replaced by a Euclidean-local split at `y ∈ R ∖ D`, by the outer normals of `K` at `∂K ∩ B̄(y,1)`: *flat* (all
  within `1/4` of one unit vector `ν`; then every `S`-neighbour `q` has `(q−y)·ν > −1/4`, and an open arc of angle
  `2 arccos(−1/4) < 240°` holds at most 4 points `60°` apart, so `m_y ≤ 4`); *thin* (two nearly opposite normals;
  the paper's fatness step puts `K` in a bounded box, so `|X ∖ D|` is bounded); *big turning* (otherwise the
  turning of `∂K ∩ B̄(y,150)` is at least `1/4`, which happens for `O(1)` points). Exceptional set: at most `10⁷`
  points (paper: `7.1·10⁷`).
- **Region III by slots and breaks.** For `τ < √3/2` the bound `#T ≤ |S| − q₂ + C` is proved by counting free
  *slots* (`card_tEdges_slots`, with the paper's slot-killing lemma); at `τ = √3/2` by counting *breaks*, points
  without a pure right T-neighbour (`exact_breaks`, with the paper's circle-arc rigidity). The paper's lemma
  "rows are cyclic orders" is not used.
- **Lemma C by exact reflection.** Instead of the angle estimate of the text, the T-step is decomposed exactly with
  respect to the reflection exchanging the two `Δ₂`-partners, and Lemma B's threshold is applied to both.
- **Region II** uses the rung K-ends of `Δ₂`-degree 1 (`P1set`) in the role of `Q`, as in the `54/37` Region III.
- **Not formalised:** Theorem N2 and hence Theorem 1(b) (`4/3` in Region II).

### The 54/37 bound (and shared parts)

The Lean proof of the `54/37` bound follows the paper's Appendix B, with these differences:

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

Some docstrings in the `E132Main*`, `E132Main15*` and `E132Main43*` files date from the skeleton phase of the formalisation and
still mention remaining `sorry`s, `TODO`s, a cited `vesztergombi87`, or internal planning notes that are not part of
this repository. They are historical; the `#print axioms` output is authoritative.

## License

- Code (Lean sources, LRAT certificate, scripts, build files): Apache License 2.0, see [`LICENSE`](LICENSE),
  the same license as Mathlib.
- Paper (`paper/`): Creative Commons Attribution 4.0 International (CC BY 4.0), see
  [`LICENSE-paper`](LICENSE-paper).

## Citation

See [`CITATION.cff`](CITATION.cff).
