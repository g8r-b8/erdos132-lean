import Erdos132.E132ConvexFinset
import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Erdős Problem 132: the layer bound (Theorem A, Corollary A1)

This file formalises `problems/132/paper/paper.tex`, section "A layer bound and a new class of
sets" (= `angle_C.md` Theorem A / Corollary A1, `VERIFY_A1b.md`, `VERIFY_A1c.md`).

For a finite set `X ⊆ ℝ²` let `Δ > Δ₂` be its two largest distances (`TwoLargest X Δ Δ₂`),
`L₁ = L1 X` the extreme points of `X`, `L₂ = L2 X` the extreme points of `X \ L₁`, `G` the
`Δ₂`-graph on `L₁ ∪ L₂` and `G′` its 2-core (`core`).  We prove

* (location) every `Δ₂`-pair has an endpoint in `L₁` and both in `L₁ ∪ L₂`; the endpoints of a
  `Δ`-pair are extreme; a non-extreme point has no `Δ`-partner;
* (Prop 3) every `q ∈ L₂ ∩ V(G′)` has `deg_{G′} q = 2`;
* (degree ≤ 4) every `p ∈ L₁ ∩ V(G′)` has `deg_{G′} p ≤ 4`;
* (Theorem A) `2 μ(Δ₂) ≤ 2|L₁| + 2|L₂| + Σ_{p ∈ L₁′} (deg′ p − 2)`;
* (Corollary A1) if no point of `L₁` has 4 or more points at distance `Δ₂`, then
  `2 μ(Δ₂) ≤ 3|L₁| + 2|L₂|`; unconditionally
  `2 μ(Δ₂) ≤ 2|L₁| + 2|L₂| + Σ_{p ∈ L₁} (min(h p, 4) − 2)`, hence `μ(Δ₂) ≤ 2|L₁| + |L₂|`.

## Design choices

* **Distances.**  `μ(d) = multS X d` (unordered pairs, from `E132ConvexFinset`).  Internally we
  work with squared distances `sqd` (polynomials in the coordinates).
* **The two largest distances** are given by the predicate `TwoLargest X Δ Δ₂` (`Δ` is the
  largest element of `distSetS X`, `Δ₂` the largest one below it); `exists_twoLargest` shows it
  is satisfiable as soon as `X` determines two distances.
* **Extreme points** (`IsExt`) are *exposed* points: some open half-plane bounded by a line
  through `p` contains `S \ {p}`.  For finite sets this is the same as `p ∉ conv(S \ {p})`
  (`isExt_iff_notMem_convexHull`, via Hahn–Banach), i.e. `L₁` is the vertex set of `conv X`.
* **The 2-core** `core V d` is the union of all `S ⊆ V` in which every vertex has at least two
  `d`-neighbours inside `S` (`MinDeg2`).  This is the largest such set, i.e. what repeated
  deletion of vertices of degree `< 2` leaves.  Instead of simulating the deletion process we
  prove its only consequence used here, `esum_le_core`: the (doubled) edge count drops by at most
  `2` per vertex outside the core.
* **Edges** are counted twice, as `esum V d = Σ_{v ∈ V} deg_V v` (handshake `two_mul_multS`).
* **Frames.**  The planar case analyses are done in the orthonormal frame `(fx q v ·, fy q v ·)`
  centred at `q` with first axis `v − q`, scaled so that `v ↦ (1,0)`; squared distances are
  divided by `sqd q v` (`frame_sqd`).  The core computations are lemmas about real numbers
  (suffix `_real`), closed by `nlinarith` / `linear_combination`.
-/

open Finset

namespace Erdos132Layer

open Erdos132Convex

/-! ## Squared distances, dot products and frames -/

/-- Squared Euclidean distance, in coordinates. -/
noncomputable def sqd (x y : Pt) : ℝ := (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2

/-- Dot product of `a − q` and `b − q`. -/
noncomputable def dotp (q a b : Pt) : ℝ := (a 0 - q 0) * (b 0 - q 0) + (a 1 - q 1) * (b 1 - q 1)

/-- `dist² = sqd`. -/
theorem dist_sq_eq_sqd (x y : Pt) : dist x y ^ 2 = sqd x y := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _),
    Fin.sum_univ_two, sqd]
  simp only [Real.dist_eq, sq_abs]

/-- Distances vs squared distances (equality). -/
theorem dist_eq_iff_sqd {x y : Pt} {r : ℝ} (hr : 0 ≤ r) : dist x y = r ↔ sqd x y = r ^ 2 := by
  rw [← dist_sq_eq_sqd, sq_eq_sq₀ dist_nonneg hr]

/-- Distances vs squared distances (inequality). -/
theorem dist_le_iff_sqd {x y : Pt} {r : ℝ} (hr : 0 ≤ r) : dist x y ≤ r ↔ sqd x y ≤ r ^ 2 := by
  rw [← dist_sq_eq_sqd, sq_le_sq₀ dist_nonneg hr]

/-- `sqd` is symmetric. -/
theorem sqd_comm (x y : Pt) : sqd x y = sqd y x := by
  simp only [sqd]; ring

/-- Distinct points have positive squared distance. -/
theorem sqd_pos_of_ne {x y : Pt} (h : x ≠ y) : 0 < sqd x y := by
  have h' : 0 < dist x y := dist_pos.2 h
  rw [← dist_sq_eq_sqd]; positivity

/-- First frame coordinate of `P` in the frame at `q` with axis `v` (so `fx q v v = 1`). -/
noncomputable def fx (q v P : Pt) : ℝ := dotp q v P / sqd q v

/-- Second frame coordinate of `P` in the frame at `q` with axis `v` (counter-clockwise). -/
noncomputable def fy (q v P : Pt) : ℝ := orient q v P / sqd q v

/-- The frame is a similarity with squared ratio `1 / sqd q v`. -/
theorem frame_sqd {q v : Pt} (h : q ≠ v) (P Q : Pt) :
    (fx q v P - fx q v Q) ^ 2 + (fy q v P - fy q v Q) ^ 2 = sqd P Q / sqd q v := by
  have hpos := sqd_pos_of_ne h
  simp only [fx, fy]
  rw [← sub_div, ← sub_div, div_pow, div_pow, ← add_div, div_eq_div_iff (by positivity) hpos.ne']
  simp only [dotp, orient, sqd]; ring

/-- `q` has frame coordinates `(0, 0)`. -/
theorem frame_base (q v : Pt) : fx q v q = 0 ∧ fy q v q = 0 := by
  simp [fx, fy, dotp, orient]

/-- `v` has frame coordinates `(1, 0)`. -/
theorem frame_axis {q v : Pt} (h : q ≠ v) : fx q v v = 1 ∧ fy q v v = 0 := by
  have hpos := sqd_pos_of_ne h
  refine ⟨?_, ?_⟩
  · rw [fx, show dotp q v v = sqd q v by simp only [dotp, sqd]; ring, div_self hpos.ne']
  · rw [fy, show orient q v v = 0 by simp only [orient]; ring, zero_div]

/-- Frame coordinates preserve dot products (up to the factor `sqd q v`). -/
theorem frame_dot {q v : Pt} (h : q ≠ v) (P Q : Pt) :
    fx q v P * fx q v Q + fy q v P * fy q v Q = dotp q P Q / sqd q v := by
  have hpos := sqd_pos_of_ne h
  simp only [fx, fy]
  rw [div_mul_div_comm, div_mul_div_comm, ← add_div, div_eq_div_iff (by positivity) hpos.ne']
  simp only [dotp, orient, sqd]; ring

/-- Frame coordinates preserve orientation (up to the factor `sqd q v`). -/
theorem frame_cross {q v : Pt} (h : q ≠ v) (P Q : Pt) :
    fx q v P * fy q v Q - fy q v P * fx q v Q = orient q P Q / sqd q v := by
  have hpos := sqd_pos_of_ne h
  simp only [fx, fy]
  rw [div_mul_div_comm, div_mul_div_comm, ← sub_div, div_eq_div_iff (by positivity) hpos.ne']
  simp only [dotp, orient, sqd]; ring

/-! ## The two largest distances -/

/-- `Δ` is the largest and `Δ₂` the second largest distance determined by `X`. -/
structure TwoLargest (X : Finset Pt) (Δ Δ₂ : ℝ) : Prop where
  mem_max : Δ ∈ distSetS X
  mem_snd : Δ₂ ∈ distSetS X
  snd_lt : Δ₂ < Δ
  le_max : ∀ d ∈ distSetS X, d ≤ Δ
  le_snd : ∀ d ∈ distSetS X, d < Δ → d ≤ Δ₂

/-- Distances of distinct points of `X` lie in `distSetS X`. -/
theorem dist_mem_distSetS {X : Finset Pt} {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) :
    dist x y ∈ distSetS X := by
  unfold distSetS pairsS
  refine mem_image.2 ⟨s(x, y), mem_filter.2 ⟨mk_mem_sym2_iff.2 ⟨hx, hy⟩, ?_⟩, ?_⟩
  · simpa using hxy
  · simp [pairDist]

/-- Elements of `distSetS X` are positive. -/
theorem pos_of_mem_distSetS {X : Finset Pt} {d : ℝ} (hd : d ∈ distSetS X) : 0 < d := by
  unfold distSetS pairsS at hd
  obtain ⟨z, hz, rfl⟩ := mem_image.1 hd
  induction z using Sym2.ind with
  | h a b =>
    have hab : a ≠ b := by simpa using (mem_filter.1 hz).2
    simpa [pairDist] using dist_pos.2 hab

/-- `TwoLargest` is satisfiable whenever `X` determines at least two distances. -/
theorem exists_twoLargest (X : Finset Pt) (h : 2 ≤ (distSetS X).card) :
    ∃ Δ Δ₂, TwoLargest X Δ Δ₂ := by
  have hne : (distSetS X).Nonempty := card_pos.1 (by omega)
  set Δ := (distSetS X).max' hne with hΔ
  have hne' : ((distSetS X).erase Δ).Nonempty := by
    rw [← card_pos, card_erase_of_mem (max'_mem _ _)]; omega
  set Δ₂ := ((distSetS X).erase Δ).max' hne' with hΔ₂
  have h2 := max'_mem _ hne'
  rw [← hΔ₂] at h2
  refine ⟨Δ, Δ₂, max'_mem _ _, mem_of_mem_erase h2,
    lt_of_le_of_ne (le_max' _ _ (mem_of_mem_erase h2)) (ne_of_mem_erase h2),
    fun d hd => le_max' _ _ hd, fun d hd hlt => le_max' _ _ (mem_erase.2 ⟨hlt.ne, hd⟩)⟩

namespace TwoLargest

variable {X : Finset Pt} {Δ Δ₂ : ℝ}

/-- `0 < Δ₂`. -/
theorem pos (hT : TwoLargest X Δ Δ₂) : 0 < Δ₂ := by
  exact pos_of_mem_distSetS hT.mem_snd

/-- All distances are at most `Δ`. -/
theorem dist_le (hT : TwoLargest X Δ Δ₂) {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) :
    dist x y ≤ Δ := by
  by_cases hxy : x = y
  · subst hxy; simp only [dist_self]; linarith [hT.pos, hT.snd_lt]
  · exact hT.le_max _ (dist_mem_distSetS hx hy hxy)

/-- No distance lies strictly between `Δ₂` and `Δ`. -/
theorem dist_gap (hT : TwoLargest X Δ Δ₂) {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) :
    dist x y ≤ Δ₂ ∨ dist x y = Δ := by
  by_cases hxy : x = y
  · subst hxy; left; simp only [dist_self]; exact hT.pos.le
  · rcases (hT.dist_le hx hy).lt_or_eq with h | h
    · exact Or.inl (hT.le_snd _ (dist_mem_distSetS hx hy hxy) h)
    · exact Or.inr h

/-- Squared version of `dist_le`. -/
theorem sqd_le (hT : TwoLargest X Δ Δ₂) {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) :
    sqd x y ≤ Δ ^ 2 := by
  exact (dist_le_iff_sqd (hT.pos.trans hT.snd_lt).le).1 (hT.dist_le hx hy)

/-- Squared version of `dist_gap`. -/
theorem sqd_gap (hT : TwoLargest X Δ Δ₂) {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) :
    sqd x y ≤ Δ₂ ^ 2 ∨ sqd x y = Δ ^ 2 := by
  rcases hT.dist_gap hx hy with h | h
  · exact Or.inl ((dist_le_iff_sqd hT.pos.le).1 h)
  · exact Or.inr ((dist_eq_iff_sqd (hT.pos.trans hT.snd_lt).le).1 h)

end TwoLargest

/-! ## Extreme points and convex layers -/

/-- `p` is an extreme point of `S`: `p ∈ S` and some open half-plane bounded by a line through
`p` contains `S \ {p}`. -/
def IsExt (S : Finset Pt) (p : Pt) : Prop :=
  p ∈ S ∧ ∃ a b : ℝ, ∀ x ∈ S, x ≠ p → a * (x 0 - p 0) + b * (x 1 - p 1) < 0

/-- For finite sets, `IsExt S p` (exposed point) is equivalent to `p ∉ conv(S \ {p})`, so `L1 X` is
the vertex set of `conv X`.  (→) the open half-plane is convex and misses `p`; (←) Hahn–Banach
(`geometric_hahn_banach_point_closed`) against the compact set `conv(S \ {p})`.  Documentation
of the definition; not used below. -/
theorem isExt_iff_notMem_convexHull {S : Finset Pt} {p : Pt} (hp : p ∈ S) :
    IsExt S p ↔ p ∉ convexHull ℝ ((S : Set Pt) \ {p}) := by
  constructor
  · rintro ⟨-, a, b, hab⟩ hmem
    have hconv : Convex ℝ {x : Pt | a * (x 0 - p 0) + b * (x 1 - p 1) < 0} := by
      intro x hx y hy s t hs ht hst
      simp only [Set.mem_ofPred_eq] at hx hy ⊢
      have e : a * ((s • x + t • y) 0 - p 0) + b * ((s • x + t • y) 1 - p 1) =
          s * (a * (x 0 - p 0) + b * (x 1 - p 1)) + t * (a * (y 0 - p 0) + b * (y 1 - p 1)) := by
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        linear_combination (a * p 0 + b * p 1) * hst
      rw [e]
      rcases hs.lt_or_eq with hs' | hs'
      · have := mul_neg_of_pos_of_neg hs' hx
        have := mul_nonpos_of_nonneg_of_nonpos ht hy.le
        linarith
      · rw [← hs'] at hst ⊢
        rw [zero_add] at hst
        rw [hst]; linarith
    have hsub : (S : Set Pt) \ {p} ⊆ {x : Pt | a * (x 0 - p 0) + b * (x 1 - p 1) < 0} := by
      rintro x ⟨hx, hxp⟩
      exact hab x hx hxp
    have := convexHull_min hsub hconv hmem
    simp at this
  · intro hn
    refine ⟨hp, ?_⟩
    have hfin : ((S : Set Pt) \ {p}).Finite := S.finite_toSet.sdiff
    obtain ⟨f, u, hfp, hfb⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ _)
      (hfin.isCompact_convexHull ℝ).isClosed hn
    refine ⟨-f (EuclideanSpace.single 0 1), -f (EuclideanSpace.single 1 1), fun x hx hxp => ?_⟩
    have hx' : u < f x := hfb x (subset_convexHull ℝ _ ⟨hx, hxp⟩)
    have hv : x - p = (x 0 - p 0) • EuclideanSpace.single 0 (1 : ℝ) +
        (x 1 - p 1) • EuclideanSpace.single 1 (1 : ℝ) := by
      ext i; fin_cases i <;> simp
    have h1 : f (x - p) = (x 0 - p 0) * f (EuclideanSpace.single 0 1) +
        (x 1 - p 1) * f (EuclideanSpace.single 1 1) := by
      rw [hv, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    rw [map_sub] at h1
    have e2 : -f (EuclideanSpace.single 0 1) * (x 0 - p 0) +
        -f (EuclideanSpace.single 1 1) * (x 1 - p 1) = -(f x - f p) := by linear_combination h1
    rw [e2]; linarith

/-- The first convex layer: the extreme points of `X`. -/
noncomputable def L1 (X : Finset Pt) : Finset Pt := by
  classical exact X.filter (IsExt X)

/-- The second convex layer: the extreme points of `X \ L₁`. -/
noncomputable def L2 (X : Finset Pt) : Finset Pt := by
  classical exact (X \ L1 X).filter (IsExt (X \ L1 X))

/-- `p ∈ L1 X ↔ IsExt X p`. -/
theorem mem_L1 {X : Finset Pt} {p : Pt} : p ∈ L1 X ↔ IsExt X p := by
  classical
  unfold L1; rw [mem_filter]; exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- `p ∈ L2 X ↔ IsExt (X \ L1 X) p`. -/
theorem mem_L2 {X : Finset Pt} {p : Pt} : p ∈ L2 X ↔ IsExt (X \ L1 X) p := by
  classical
  unfold L2; rw [mem_filter]; exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- `L1 X ⊆ X`. -/
theorem L1_subset (X : Finset Pt) : L1 X ⊆ X := by
  exact fun p hp => (mem_L1.1 hp).1

/-- `L2 X ⊆ X`. -/
theorem L2_subset (X : Finset Pt) : L2 X ⊆ X := by
  exact fun p hp => (mem_sdiff.1 (mem_L2.1 hp).1).1

/-- `L1 X` and `L2 X` are disjoint. -/
theorem disjoint_L1_L2 (X : Finset Pt) : Disjoint (L1 X) (L2 X) := by
  exact disjoint_left.2 fun p h1 h2 => (mem_sdiff.1 (mem_L2.1 h2).1).2 h1

/-- A point of `S` on the boundary of a disc containing `S` is extreme. -/
theorem isExt_of_disk {S : Finset Pt} {c q : Pt} {R : ℝ} (hq : q ∈ S)
    (hS : ∀ x ∈ S, sqd c x ≤ R) (hR : sqd c q = R) : IsExt S q := by
  refine ⟨hq, q 0 - c 0, q 1 - c 1, fun x hx hxq => ?_⟩
  have h1 := hS x hx
  have h2 := sqd_pos_of_ne hxq
  simp only [sqd] at h1 h2 hR
  nlinarith

/-- A non-extreme point has another point of `S` in every closed half-plane at it. -/
theorem exists_of_not_isExt {S : Finset Pt} {q : Pt} (hq : q ∈ S) (h : ¬ IsExt S q) (a b : ℝ) :
    ∃ x ∈ S, x ≠ q ∧ 0 ≤ a * (x 0 - q 0) + b * (x 1 - q 1) := by
  by_contra hcon
  push Not at hcon
  exact h ⟨hq, a, b, fun x hx hxq => hcon x hx hxq⟩

/-! ## Location of `Δ`- and `Δ₂`-pairs (Lemma "location", obs. (1)–(2)) -/

/-- Both endpoints of a `Δ`-pair are extreme (obs. (1)/(i)). -/
theorem isExt_of_dist_max {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) {p q : Pt}
    (hp : p ∈ X) (hq : q ∈ X) (h : dist p q = Δ) : IsExt X p := by
  refine isExt_of_disk hp (c := q) (R := Δ ^ 2) (fun x hx => hT.sqd_le hq hx) ?_
  rw [sqd_comm]; exact (dist_eq_iff_sqd (hT.pos.trans hT.snd_lt).le).1 h

/-- A non-extreme point has no `Δ`-partner. -/
theorem dist_le_snd_of_not_isExt {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) {q x : Pt}
    (hq : q ∈ X) (hqe : ¬ IsExt X q) (hx : x ∈ X) : dist q x ≤ Δ₂ := by
  rcases hT.dist_gap hq hx with h | h
  · exact h
  · exact absurd (isExt_of_dist_max hT hq hx h) hqe

/-- Every `Δ₂`-pair has an endpoint in `L₁` (obs. (2), first half). -/
theorem mem_L1_or_of_dist_snd {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) {p q : Pt}
    (hp : p ∈ X) (hq : q ∈ X) (h : dist p q = Δ₂) : p ∈ L1 X ∨ q ∈ L1 X := by
  by_contra hcon
  push Not at hcon
  have hpe : ¬ IsExt X p := fun h => hcon.1 (mem_L1.2 h)
  refine hcon.2 (mem_L1.2 (isExt_of_disk hq (c := p) (R := Δ₂ ^ 2) (fun x hx => ?_) ?_))
  · exact (dist_le_iff_sqd hT.pos.le).1 (dist_le_snd_of_not_isExt hT hp hpe hx)
  · exact (dist_eq_iff_sqd hT.pos.le).1 h

/-- Every endpoint of a `Δ₂`-pair lies in `L₁ ∪ L₂` (obs. (2), second half). -/
theorem mem_L12_of_dist_snd {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) {p q : Pt}
    (hp : p ∈ X) (hq : q ∈ X) (h : dist p q = Δ₂) : p ∈ L1 X ∪ L2 X := by
  by_cases hp1 : p ∈ L1 X
  · exact mem_union_left _ hp1
  refine mem_union_right _ (mem_L2.2 (isExt_of_disk (mem_sdiff.2 ⟨hp, hp1⟩) (c := q)
    (R := Δ₂ ^ 2) (fun x hx => ?_) ?_))
  · obtain ⟨hxX, hx1⟩ := mem_sdiff.1 hx
    rcases hT.sqd_gap hq hxX with h' | h'
    · exact h'
    · refine absurd (mem_L1.2 (isExt_of_dist_max hT hxX hq ?_)) hx1
      rw [dist_eq_iff_sqd (hT.pos.trans hT.snd_lt).le, sqd_comm]; exact h'
  · rw [sqd_comm]; exact (dist_eq_iff_sqd hT.pos.le).1 h

/-! ## Graphs, degrees and the 2-core -/

/-- The `d`-neighbours of `v` inside `V`. -/
noncomputable def nbr (V : Finset Pt) (d : ℝ) (v : Pt) : Finset Pt := by
  classical exact V.filter (fun x => dist v x = d)

/-- Twice the number of `d`-edges inside `V`: the degree sum. -/
noncomputable def esum (V : Finset Pt) (d : ℝ) : ℕ := ∑ v ∈ V, (nbr V d v).card

/-- Every vertex of `V` has at least two `d`-neighbours inside `V`. -/
def MinDeg2 (V : Finset Pt) (d : ℝ) : Prop := ∀ v ∈ V, 2 ≤ (nbr V d v).card

/-- The 2-core of the `d`-graph on `V`: the union of all subsets of minimum degree `≥ 2`. -/
noncomputable def core (V : Finset Pt) (d : ℝ) : Finset Pt := by
  classical exact (V.powerset.filter (fun S => MinDeg2 S d)).sup id

/-- Membership in `nbr`. -/
theorem mem_nbr {V : Finset Pt} {d : ℝ} {v x : Pt} : x ∈ nbr V d v ↔ x ∈ V ∧ dist v x = d := by
  unfold nbr; exact mem_filter

/-- `nbr` is monotone in the vertex set. -/
theorem nbr_mono {V V' : Finset Pt} (h : V ⊆ V') (d : ℝ) (v : Pt) : nbr V d v ⊆ nbr V' d v := by
  intro x hx
  rw [mem_nbr] at hx ⊢
  exact ⟨h hx.1, hx.2⟩

/-- `core V d ⊆ V`. -/
theorem core_subset (V : Finset Pt) (d : ℝ) : core V d ⊆ V := by
  classical
  unfold core
  exact Finset.sup_le fun S hS => mem_powerset.1 (mem_filter.1 hS).1

/-- Every min-degree-2 subset of `V` lies in the core. -/
theorem subset_core {V S : Finset Pt} {d : ℝ} (hS : S ⊆ V) (h : MinDeg2 S d) :
    S ⊆ core V d := by
  classical
  unfold core
  exact le_sup (f := id) (mem_filter.2 ⟨mem_powerset.2 hS, h⟩)

/-- The core itself has minimum degree `≥ 2`. -/
theorem minDeg2_core (V : Finset Pt) (d : ℝ) : MinDeg2 (core V d) d := by
  classical
  intro v hv
  have hv' := hv
  unfold core at hv'
  obtain ⟨S, hS, hvS⟩ := mem_sup.1 hv'
  obtain ⟨hSV, hS2⟩ := mem_filter.1 hS
  have hSc : S ⊆ core V d := subset_core (mem_powerset.1 hSV) hS2
  exact (hS2 v hvS).trans (card_le_card (nbr_mono hSc d v))

/-- Adding a vertex adds twice its degree to `esum`. -/
theorem esum_insert {V : Finset Pt} {d : ℝ} (hd : d ≠ 0) {v : Pt} (hv : v ∉ V) :
    esum (insert v V) d = esum V d + 2 * (nbr (insert v V) d v).card := by
  have key : ∀ (W : Finset Pt) (u : Pt),
      (nbr W d u).card = ∑ x ∈ W, if dist u x = d then 1 else 0 := by
    intro W u; unfold nbr; rw [card_filter]
  have h0 : (0 : ℝ) ≠ d := Ne.symm hd
  simp only [esum, key, sum_insert hv, dist_self, h0, ite_false, zero_add, sum_add_distrib]
  have hsym : ∑ u ∈ V, (if dist u v = d then 1 else 0 : ℕ) =
      ∑ x ∈ V, if dist v x = d then 1 else 0 :=
    sum_congr rfl fun u _ => by rw [dist_comm]
  rw [hsym]; ring

/-- Pruning to the 2-core loses at most one edge (two degree units) per deleted vertex. -/
theorem esum_le_core {d : ℝ} (hd : d ≠ 0) (V : Finset Pt) :
    esum V d ≤ esum (core V d) d + 2 * (V \ core V d).card := by
  induction V using Finset.strongInduction with
  | H V ih =>
  by_cases hV : V ⊆ core V d
  · have : core V d = V := (core_subset V d).antisymm hV
    rw [this]; simp
  · have hex : ∃ v ∈ V, v ∉ core V d ∧ (nbr V d v).card ≤ 1 := by
      by_contra hcon
      push Not at hcon
      apply hV
      refine subset_core subset_rfl fun v hv => ?_
      by_cases hvc : v ∈ core V d
      · exact (minDeg2_core V d v hvc).trans (card_le_card (nbr_mono (core_subset V d) d v))
      · exact hcon v hv hvc
    obtain ⟨v, hv, hvc, hdeg⟩ := hex
    have hcore : core (V.erase v) d = core V d := by
      apply le_antisymm
      · exact subset_core ((core_subset _ d).trans (erase_subset v V)) (minDeg2_core _ d)
      · refine subset_core (fun x hx => ?_) (minDeg2_core V d)
        exact mem_erase.2 ⟨fun h => hvc (h ▸ hx), core_subset V d hx⟩
    have h1 := esum_insert hd (notMem_erase v V)
    rw [insert_erase hv] at h1
    have h2 := ih (V.erase v) (erase_ssubset hv)
    rw [hcore, erase_sdiff_comm, card_erase_of_mem (mem_sdiff.2 ⟨hv, hvc⟩)] at h2
    have h3 : 0 < (V \ core V d).card := card_pos.2 ⟨v, mem_sdiff.2 ⟨hv, hvc⟩⟩
    omega

/-- Handshake lemma: `2 μ(d) = esum X d`. -/
theorem two_mul_multS {d : ℝ} (hd : 0 < d) (X : Finset Pt) : 2 * multS X d = esum X d := by
  classical
  set O := (X ×ˢ X).filter (fun e : Pt × Pt => dist e.1 e.2 = d) with hO
  have hE : esum X d = O.card := by
    rw [hO, card_filter, sum_product]
    unfold esum
    refine sum_congr rfl fun u _ => ?_
    unfold nbr; rw [card_filter]
  set T := (pairsS X).filter (fun z => pairDist z = d) with hT
  have hM : multS X d = T.card := by unfold multS; rfl
  have hmaps : Set.MapsTo (fun e : Pt × Pt => s(e.1, e.2)) O T := by
    intro e he
    obtain ⟨he1, he2⟩ := mem_filter.1 he
    obtain ⟨hx, hy⟩ := mem_product.1 he1
    have hne : e.1 ≠ e.2 := by intro h; rw [h, dist_self] at he2; linarith
    refine mem_filter.2 ⟨?_, by simpa [pairDist] using he2⟩
    unfold pairsS
    exact mem_filter.2 ⟨mk_mem_sym2_iff.2 ⟨hx, hy⟩, by simpa using hne⟩
  have hfib : ∀ z ∈ T, (O.filter (fun e => s(e.1, e.2) = z)).card = 2 := by
    intro z hz
    induction z using Sym2.ind with
    | h a b =>
    obtain ⟨hz1, hz2⟩ := mem_filter.1 hz
    unfold pairsS at hz1
    obtain ⟨hz1, hdiag⟩ := mem_filter.1 hz1
    have hab : a ≠ b := by simpa using hdiag
    obtain ⟨ha, hb⟩ := mk_mem_sym2_iff.1 hz1
    have hdab : dist a b = d := by simpa [pairDist] using hz2
    have : O.filter (fun e => s(e.1, e.2) = s(a, b)) = {(a, b), (b, a)} := by
      ext ⟨x, y⟩
      simp only [hO, mem_filter, mem_product, Sym2.eq_iff, mem_insert, mem_singleton,
        Prod.mk.injEq]
      constructor
      · rintro ⟨_, h⟩; exact h
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨⟨⟨ha, hb⟩, hdab⟩, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨⟨⟨hb, ha⟩, by rw [dist_comm]; exact hdab⟩, Or.inr ⟨rfl, rfl⟩⟩
    rw [this, card_pair]; simp [hab]
  rw [hE, hM, card_eq_sum_card_fiberwise hmaps, sum_congr rfl hfib, sum_const, smul_eq_mul,
    mul_comm]

/-- The `Δ₂`-graph on `L₁ ∪ L₂` contains every `Δ₂`-pair. -/
theorem esum_eq_esum_L12 {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) :
    esum X Δ₂ = esum (L1 X ∪ L2 X) Δ₂ := by
  have hW : L1 X ∪ L2 X ⊆ X := union_subset (L1_subset X) (L2_subset X)
  unfold esum
  rw [← sum_sdiff hW]
  have h0 : ∑ v ∈ X \ (L1 X ∪ L2 X), (nbr X Δ₂ v).card = 0 := by
    refine sum_eq_zero fun v hv => ?_
    obtain ⟨hvX, hvW⟩ := mem_sdiff.1 hv
    rw [card_eq_zero, eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨hxX, hd⟩ := mem_nbr.1 hx
    exact hvW (mem_L12_of_dist_snd hT hvX hxX hd)
  rw [h0, zero_add]
  refine sum_congr rfl fun v hv => ?_
  congr 1
  ext x
  simp only [mem_nbr]
  constructor
  · rintro ⟨hxX, hd⟩
    exact ⟨mem_L12_of_dist_snd hT hxX (hW hv) (by rw [dist_comm]; exact hd), hd⟩
  · rintro ⟨hxW, hd⟩; exact ⟨hW hxW, hd⟩

/-! ## Planar lemmas in normalised coordinates -/

/-- Two distinct circles (centres `0` and `t ≠ 0`) meet in at most two points. -/
theorem circle3_real {x₁ y₁ x₂ y₂ x₃ y₃ tx ty D : ℝ} (ht : 0 < tx ^ 2 + ty ^ 2)
    (h₁ : x₁ ^ 2 + y₁ ^ 2 = 1) (h₂ : x₂ ^ 2 + y₂ ^ 2 = 1) (h₃ : x₃ ^ 2 + y₃ ^ 2 = 1)
    (d₁ : (x₁ - tx) ^ 2 + (y₁ - ty) ^ 2 = D) (d₂ : (x₂ - tx) ^ 2 + (y₂ - ty) ^ 2 = D)
    (d₃ : (x₃ - tx) ^ 2 + (y₃ - ty) ^ 2 = D) :
    (x₁ = x₂ ∧ y₁ = y₂) ∨ (x₁ = x₃ ∧ y₁ = y₃) ∨ (x₂ = x₃ ∧ y₂ = y₃) := by
  have eqpt : ∀ {a b c e : ℝ}, a * tx + b * ty = c * tx + e * ty →
      tx * b - ty * a = tx * e - ty * c → a = c ∧ b = e := by
    intro a b c e hk hl
    have hx : (tx ^ 2 + ty ^ 2) * (a - c) = 0 := by linear_combination tx * hk - ty * hl
    have hy : (tx ^ 2 + ty ^ 2) * (b - e) = 0 := by linear_combination ty * hk + tx * hl
    exact ⟨by linarith [(mul_eq_zero.1 hx).resolve_left ht.ne'],
      by linarith [(mul_eq_zero.1 hy).resolve_left ht.ne']⟩
  have k12 : x₁ * tx + y₁ * ty = x₂ * tx + y₂ * ty := by
    linear_combination (-1/2 : ℝ) * d₁ + (1/2 : ℝ) * h₁ + (1/2 : ℝ) * d₂ - (1/2 : ℝ) * h₂
  have k13 : x₁ * tx + y₁ * ty = x₃ * tx + y₃ * ty := by
    linear_combination (-1/2 : ℝ) * d₁ + (1/2 : ℝ) * h₁ + (1/2 : ℝ) * d₃ - (1/2 : ℝ) * h₃
  have l12 : (tx * y₁ - ty * x₁) ^ 2 = (tx * y₂ - ty * x₂) ^ 2 := by
    linear_combination (tx ^ 2 + ty ^ 2) * h₁ - (tx ^ 2 + ty ^ 2) * h₂ -
      (x₁ * tx + y₁ * ty + x₂ * tx + y₂ * ty) * k12
  have l13 : (tx * y₁ - ty * x₁) ^ 2 = (tx * y₃ - ty * x₃) ^ 2 := by
    linear_combination (tx ^ 2 + ty ^ 2) * h₁ - (tx ^ 2 + ty ^ 2) * h₃ -
      (x₁ * tx + y₁ * ty + x₃ * tx + y₃ * ty) * k13
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 l12 with e12 | e12
  · exact Or.inl (eqpt k12 e12)
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 l13 with e13 | e13
  · exact Or.inr (Or.inl (eqpt k13 e13))
  · exact Or.inr (Or.inr (eqpt (k12.symm.trans k13) (by linarith)))

/-- **Lemma M** (opposite-side lemma) with `p = 0`, `b = (1, 0)`, `|pa| = |br| = 1`: if `a` is
strictly below the axis and `r ≠ p` is not, then `|ar| > 1`. -/
theorem lemmaM_real {xa ya xr yr : ℝ} (ha : xa ^ 2 + ya ^ 2 = 1) (hya : ya < 0)
    (hr : (xr - 1) ^ 2 + yr ^ 2 = 1) (hyr : 0 ≤ yr) (hr0 : 0 < xr ^ 2 + yr ^ 2) :
    1 < (xr - xa) ^ 2 + (yr - ya) ^ 2 := by
  have hxr : 0 < xr := by nlinarith
  have hxa : xa < 1 := by nlinarith
  nlinarith [mul_pos hxr (sub_pos.2 hxa), mul_nonneg hyr (neg_nonneg.2 hya.le)]

/-- Chord monotonicity: if `W` and then `B` follow `A` counter-clockwise within a half-turn, then
`A·B < A·W`, i.e. `|AB| > |AW|`.  Uses `(A·W − A·B)(1 + W·B) = (W×B)(A×W + A×B)` (no condition
on `|A|` needed). -/
theorem chord_real {a0 a1 w0 w1 b0 b1 : ℝ} (_ha : a0 ^ 2 + a1 ^ 2 = 1) (hw : w0 ^ 2 + w1 ^ 2 = 1)
    (hb : b0 ^ 2 + b1 ^ 2 = 1) (haw : 0 < a0 * w1 - a1 * w0) (hab : 0 < a0 * b1 - a1 * b0)
    (hwb : 0 < w0 * b1 - w1 * b0) : a0 * b0 + a1 * b1 < a0 * w0 + a1 * w1 := by
  have key : (a0 * w0 + a1 * w1 - (a0 * b0 + a1 * b1)) * (1 + (w0 * b0 + w1 * b1)) =
      (w0 * b1 - w1 * b0) * ((a0 * w1 - a1 * w0) + (a0 * b1 - a1 * b0)) := by
    linear_combination (a0 * b0 + a1 * b1) * hw - (a0 * w0 + a1 * w1) * hb
  have hlag : (w0 * b0 + w1 * b1) ^ 2 + (w0 * b1 - w1 * b0) ^ 2 = 1 := by
    linear_combination (b0 ^ 2 + b1 ^ 2) * hw + hb
  have h1 : 0 < 1 + (w0 * b0 + w1 * b1) := by nlinarith
  have hpos : 0 < (a0 * w0 + a1 * w1 - (a0 * b0 + a1 * b1)) * (1 + (w0 * b0 + w1 * b1)) := by
    rw [key]; exact mul_pos hwb (add_pos haw hab)
  have := (pos_iff_pos_of_mul_pos hpos).2 h1
  linarith

/-- `x ≥ 1/2 → x² ≥ 1/4`. -/
theorem sq_ge_quarter {x : ℝ} (h : 1 / 2 ≤ x) : 1 / 4 ≤ x ^ 2 := by nlinarith

/-- A unit vector within distance `1` of `(1, 0)` has first coordinate `≥ 1/2`. -/
theorem half_le_of_close {x y : ℝ} (h : x ^ 2 + y ^ 2 = 1) (h' : (x - 1) ^ 2 + y ^ 2 ≤ 1) :
    1 / 2 ≤ x := by
  have : (x - 1) ^ 2 + y ^ 2 = 2 - 2 * x := by linear_combination h
  linarith

/-- `x, y ≥ 1/2 → xy ≥ 1/4`. -/
theorem quarter_le_mul {x y : ℝ} (hx : 1 / 2 ≤ x) (hy : 1 / 2 ≤ y) : 1 / 4 ≤ x * y := by
  have h := mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hy)
  have e : (x - 1 / 2) * (y - 1 / 2) = x * y - x / 2 - y / 2 + 1 / 4 := by ring
  linarith

/-- VERIFY_A1b **Case 3** core computation (`b = (1,0)` the middle neighbour, `t` in the closed
half-plane `x ≤ 0` with `y_t ≥ 0`): `|tb|² = |tc|² = D`, then `t ∥ −(b + c)` and `a·b + a·c ≥ 0`
give `|ta|² = D`, and three points on two distinct circles is impossible. -/
theorem case3_real {xa ya xc yc xt yt D : ℝ} (_hD : 1 < D)
    (ha : xa ^ 2 + ya ^ 2 = 1) (hc : xc ^ 2 + yc ^ 2 = 1)
    (hab : (xa - 1) ^ 2 + ya ^ 2 ≤ 1) (hcb : (xc - 1) ^ 2 + yc ^ 2 ≤ 1)
    (hya : 0 < ya) (hyc : yc < 0) (hxt : xt ≤ 0) (ht0 : 0 < xt ^ 2 + yt ^ 2) (hyt : 0 ≤ yt)
    (ga : (xt - xa) ^ 2 + (yt - ya) ^ 2 ≤ 1 ∨ (xt - xa) ^ 2 + (yt - ya) ^ 2 = D)
    (gb : (xt - 1) ^ 2 + yt ^ 2 ≤ 1 ∨ (xt - 1) ^ 2 + yt ^ 2 = D)
    (gc : (xt - xc) ^ 2 + (yt - yc) ^ 2 ≤ 1 ∨ (xt - xc) ^ 2 + (yt - yc) ^ 2 = D) : False := by
  have hxa := half_le_of_close ha hab
  have hxc := half_le_of_close hc hcb
  have sc : (xt - xc) ^ 2 + (yt - yc) ^ 2 = xt ^ 2 + yt ^ 2 - 2 * (xt * xc + yt * yc) + 1 := by
    linear_combination hc
  have sa : (xt - xa) ^ 2 + (yt - ya) ^ 2 = xt ^ 2 + yt ^ 2 - 2 * (xt * xa + yt * ya) + 1 := by
    linear_combination ha
  have sb : (xt - 1) ^ 2 + yt ^ 2 = xt ^ 2 + yt ^ 2 - 2 * xt + 1 := by ring
  have p1 : xt * xc ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hxt (by linarith)
  have p2 : yt * yc ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hyt hyc.le
  have ec : (xt - xc) ^ 2 + (yt - yc) ^ 2 = D := gc.resolve_left (by linarith)
  have eb : (xt - 1) ^ 2 + yt ^ 2 = D := gb.resolve_left (by linarith)
  have hbc : (1 - xc) * xt = yt * yc := by linarith
  have hu := quarter_le_mul hxa hxc
  have hya2 : ya ^ 2 ≤ 3 / 4 := by linarith [sq_ge_quarter hxa]
  have hyc2 : yc ^ 2 ≤ 3 / 4 := by linarith [sq_ge_quarter hxc]
  have hyy : -(3 / 4) ≤ ya * yc := by
    have := sq_nonneg (ya + yc)
    have e : (ya + yc) ^ 2 = ya ^ 2 + 2 * (ya * yc) + yc ^ 2 := by ring
    linarith
  have hsum : 0 ≤ xa + xa * xc + ya * yc := by linarith
  have key : (1 - xc ^ 2) * (xt * xa + yt * ya) = yt * yc * (xa + xa * xc + ya * yc) := by
    linear_combination xa * (1 + xc) * hbc - ya * yt * hc
  have hpos : 0 < 1 - xc ^ 2 := by
    have : 0 < yc ^ 2 := by rw [sq]; exact mul_pos_of_neg_of_neg hyc hyc
    linarith
  have hta : xt * xa + yt * ya ≤ 0 := by
    have hR : yt * yc * (xa + xa * xc + ya * yc) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg p2 hsum
    by_contra hh
    push Not at hh
    have := mul_pos hpos hh
    linarith
  have ea : (xt - xa) ^ 2 + (yt - ya) ^ 2 = D := ga.resolve_left (by linarith)
  rcases circle3_real (x₁ := xa) (y₁ := ya) (x₂ := 1) (y₂ := 0) (x₃ := xc) (y₃ := yc)
    (tx := xt) (ty := yt) (D := D) ht0 ha (by norm_num) hc (by linear_combination ea)
    (by linear_combination eb) (by linear_combination ec) with h | h | h
  · linarith [h.2]
  · linarith [h.2]
  · linarith [h.2]

/-- Case 3 with `a, c` on opposite sides of the axis and no sign condition on `y_t` (reflections of
`case3_real`). -/
theorem case3_real' {xa ya xc yc xt yt D : ℝ} (hD : 1 < D)
    (ha : xa ^ 2 + ya ^ 2 = 1) (hc : xc ^ 2 + yc ^ 2 = 1)
    (hab : (xa - 1) ^ 2 + ya ^ 2 ≤ 1) (hcb : (xc - 1) ^ 2 + yc ^ 2 ≤ 1)
    (hopp : ya * yc < 0) (hxt : xt ≤ 0) (ht0 : 0 < xt ^ 2 + yt ^ 2)
    (ga : (xt - xa) ^ 2 + (yt - ya) ^ 2 ≤ 1 ∨ (xt - xa) ^ 2 + (yt - ya) ^ 2 = D)
    (gb : (xt - 1) ^ 2 + yt ^ 2 ≤ 1 ∨ (xt - 1) ^ 2 + yt ^ 2 = D)
    (gc : (xt - xc) ^ 2 + (yt - yc) ^ 2 ≤ 1 ∨ (xt - xc) ^ 2 + (yt - yc) ^ 2 = D) : False := by
  have rf : ∀ u v : ℝ, (-u - -v) ^ 2 = (u - v) ^ 2 := fun u v => by ring
  have rf0 : ∀ u : ℝ, (-u) ^ 2 = u ^ 2 := fun u => by ring
  rcases lt_or_gt_of_ne (show ya ≠ 0 by rintro rfl; simp at hopp) with hya | hya
  · have hyc : 0 < yc := by
      by_contra hh; push Not at hh
      linarith [mul_nonneg_of_nonpos_of_nonpos hya.le hh]
    rcases le_or_gt 0 yt with hyt | hyt
    · exact case3_real hD hc ha hcb hab hyc hya hxt ht0 hyt gc gb ga
    · refine case3_real (xa := xa) (ya := -ya) (xc := xc) (yc := -yc) (yt := -yt) hD
        (by rw [rf0]; exact ha) (by rw [rf0]; exact hc) (by rw [rf0]; exact hab)
        (by rw [rf0]; exact hcb) (by linarith) (by linarith) hxt (by rw [rf0]; exact ht0)
        (by linarith) (by rw [rf]; exact ga) (by rw [rf0]; exact gb) (by rw [rf]; exact gc)
  · have hyc : yc < 0 := by
      by_contra hh; push Not at hh
      linarith [mul_nonneg hya.le hh]
    rcases le_or_gt 0 yt with hyt | hyt
    · exact case3_real hD ha hc hab hcb hya hyc hxt ht0 hyt ga gb gc
    · refine case3_real (xa := xc) (ya := -yc) (xc := xa) (yc := -ya) (yt := -yt) hD
        (by rw [rf0]; exact hc) (by rw [rf0]; exact ha) (by rw [rf0]; exact hcb)
        (by rw [rf0]; exact hab) (by linarith) (by linarith) hxt (by rw [rf0]; exact ht0)
        (by linarith) (by rw [rf]; exact gc) (by rw [rf0]; exact gb) (by rw [rf]; exact ga)

/-- If `a, c` lie on the same side of the axis within `60°` of `(1,0)` and `|y_a| < |y_c|`, then `a`
separates `(1,0)` from `c`. -/
theorem middle_real {xa ya xc yc : ℝ} (ha : xa ^ 2 + ya ^ 2 = 1) (hc : xc ^ 2 + yc ^ 2 = 1)
    (hxa : 1 / 2 ≤ xa) (hxc : 1 / 2 ≤ xc) (hsame : 0 < ya * yc) (h : ya ^ 2 < yc ^ 2) :
    (-ya) * (xa * yc - ya * xc) < 0 := by
  have hx : xc < xa := by
    by_contra hh; push Not at hh
    have := mul_self_le_mul_self (by linarith) hh
    rw [← sq, ← sq] at this
    linarith
  have hya0 : ya ≠ 0 := by rintro rfl; simp at hsame
  have hy0 : 0 < ya ^ 2 := by positivity
  have hyy : ya ^ 2 ≤ ya * yc := by
    by_contra hh; push Not at hh
    have h1 : (ya * yc) ^ 2 < (ya ^ 2) ^ 2 := pow_lt_pow_left₀ hh hsame.le (by norm_num)
    have h2 : ya ^ 2 * ya ^ 2 < ya ^ 2 * yc ^ 2 := mul_lt_mul_of_pos_left h hy0
    have e1 : (ya * yc) ^ 2 = ya ^ 2 * yc ^ 2 := by ring
    have e2 : (ya ^ 2) ^ 2 = ya ^ 2 * ya ^ 2 := by ring
    linarith
  have M1 := mul_pos (sub_pos.2 hx) hsame
  have M2 := mul_nonneg (by linarith : (0:ℝ) ≤ xc) (sub_nonneg.2 hyy)
  have e : (-ya) * (xa * yc - ya * xc) = -((xa - xc) * (ya * yc) + xc * (ya * yc - ya ^ 2)) := by
    ring
  linarith

/-- If both non-middle neighbours lie on the same side, they are within distance `1` of each other
and one of them separates the other two. -/
theorem case3_select_real {xa ya xc yc : ℝ}
    (ha : xa ^ 2 + ya ^ 2 = 1) (hc : xc ^ 2 + yc ^ 2 = 1)
    (hab : (xa - 1) ^ 2 + ya ^ 2 ≤ 1) (hcb : (xc - 1) ^ 2 + yc ^ 2 ≤ 1)
    (hsame : 0 < ya * yc) (hne : ¬ (xa = xc ∧ ya = yc)) :
    (xa - xc) ^ 2 + (ya - yc) ^ 2 ≤ 1 ∧
      ((-ya) * (xa * yc - ya * xc) < 0 ∨ (-yc) * (xc * ya - yc * xa) < 0) := by
  have hxa := half_le_of_close ha hab
  have hxc := half_le_of_close hc hcb
  have hu := sq_ge_quarter hxa
  have hv := sq_ge_quarter hxc
  have hu1 : xa ^ 2 ≤ 1 := by linarith [sq_nonneg ya]
  have hv1 : xc ^ 2 ≤ 1 := by linarith [sq_nonneg yc]
  have hxy : 0 < xa * xc * (ya * yc) := mul_pos (by positivity) hsame
  have e : (xa * yc - ya * xc) ^ 2 = xa ^ 2 + xc ^ 2 - 2 * (xa ^ 2 * xc ^ 2) -
      2 * (xa * xc * (ya * yc)) := by linear_combination xa ^ 2 * hc + xc ^ 2 * ha
  have hcr : (xa * yc - ya * xc) ^ 2 ≤ 3 / 4 := by
    have A := mul_nonneg (sub_nonneg.2 hu) (sub_nonneg.2 hv)
    have B := mul_nonneg (sub_nonneg.2 hu1) (sub_nonneg.2 hv1)
    have eA : (xa ^ 2 - 1 / 4) * (xc ^ 2 - 1 / 4) =
        xa ^ 2 * xc ^ 2 - xa ^ 2 / 4 - xc ^ 2 / 4 + 1 / 16 := by ring
    have eB : (1 - xa ^ 2) * (1 - xc ^ 2) = 1 - xa ^ 2 - xc ^ 2 + xa ^ 2 * xc ^ 2 := by ring
    linarith
  have hxx := quarter_le_mul hxa hxc
  set s := xa * xc + ya * yc with hs
  have hlag : s ^ 2 + (xa * yc - ya * xc) ^ 2 = 1 := by
    rw [hs]; linear_combination (xc ^ 2 + yc ^ 2) * ha + hc
  have hdot : 0 < s := by rw [hs]; linarith
  have hdot' : 1 / 2 ≤ s := by
    by_contra hh; push Not at hh
    have := mul_pos (sub_pos.2 hh) (by linarith : (0:ℝ) < 1 / 2 + s)
    have e' : (1 / 2 - s) * (1 / 2 + s) = 1 / 4 - s ^ 2 := by ring
    linarith
  have sac : (xa - xc) ^ 2 + (ya - yc) ^ 2 = 2 - 2 * s := by
    rw [hs]; linear_combination ha + hc
  refine ⟨by linarith, ?_⟩
  rcases lt_trichotomy (ya ^ 2) (yc ^ 2) with h | h | h
  · exact Or.inl (middle_real ha hc hxa hxc hsame h)
  · exfalso
    have hy : ya = yc := by
      have : (ya - yc) * (ya + yc) = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with h' | h'
      · linarith
      · have hyc' : yc = -ya := by linarith
        rw [hyc'] at hsame
        have : ya * -ya = -(ya ^ 2) := by ring
        linarith [sq_nonneg ya]
    have hx : xa = xc := by
      have : (xa - xc) * (xa + xc) = 0 := by rw [hy] at ha; linear_combination ha - hc
      rcases mul_eq_zero.1 this with h' | h'
      · linarith
      · linarith
    exact hne ⟨hx, hy⟩
  · exact Or.inr (middle_real hc ha hxc hxa (by linarith [mul_comm ya yc]) h)

/-- Case 2 key computation: if the apex is `(1, 0)`, `v₂ = (x₂, y₂)` with `4y₂² ≤ 1`, and `r` (a
second `Δ₂`-neighbour of the apex, inside the unit disc) has `|r v₂|² = D`, then `ρ = |r|² = 1`,
`4x₂² = 3`, and `|r v₃|² = 2` for the mirror image `v₃ = (x₂, −y₂)`. -/
theorem case2_aux_real {x₂ y₂ xr yr D : ℝ} (hD : 1 < D) (h₂ : x₂ ^ 2 + y₂ ^ 2 = 1)
    (h12 : (1 - x₂) ^ 2 + y₂ ^ 2 = D) (hy : 4 * y₂ ^ 2 ≤ 1)
    (hr1 : (xr - 1) ^ 2 + yr ^ 2 = 1) (hrn : xr ^ 2 + yr ^ 2 ≤ 1)
    (E : (xr - x₂) ^ 2 + (yr - y₂) ^ 2 = D) :
    (xr - x₂) ^ 2 + (yr + y₂) ^ 2 = 2 ∧ x₂ ≠ 0 := by
  have hL : 2 * x₂ * xr - 2 * x₂ - 2 * xr + 2 * y₂ * yr + 1 = 0 := by
    linear_combination -E + hr1 + h12
  have hG : 2 * (1 - x₂) * (1 - 2 * xr) * (2 - 2 * xr) + 4 * x₂ ^ 2 - 3 = 0 := by
    linear_combination (2 * x₂ * xr - 2 * x₂ - 2 * xr + 1 - 2 * y₂ * yr) * hL +
      4 * yr ^ 2 * h₂ + 4 * (1 - x₂ ^ 2) * hr1
  have hDx : D = 2 - 2 * x₂ := by linear_combination -h12 + h₂
  have hx2 : x₂ < 1 / 2 := by linarith
  have hxr : 2 * xr ≤ 1 := by
    have : (xr - 1) ^ 2 + yr ^ 2 = xr ^ 2 + yr ^ 2 - 2 * xr + 1 := by ring
    linarith
  have hq : 3 ≤ 4 * x₂ ^ 2 := by linarith
  have T1 : 0 ≤ 2 * (1 - x₂) * (1 - 2 * xr) * (2 - 2 * xr) := by
    have := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 * (1 - x₂))
      (by linarith : (0:ℝ) ≤ 1 - 2 * xr)) (by linarith : (0:ℝ) ≤ 2 - 2 * xr)
    linarith
  have hT : 2 * (1 - x₂) * (1 - 2 * xr) * (2 - 2 * xr) = 0 := by linarith
  have hxr' : xr = 1 / 2 := by
    rcases mul_eq_zero.1 hT with h | h
    · rcases mul_eq_zero.1 h with h' | h'
      · linarith
      · linarith
    · linarith
  have hx0 : x₂ ≠ 0 := by
    rintro rfl; norm_num at hq
  refine ⟨?_, hx0⟩
  linear_combination hr1 + h₂ + hL + (4 - 4 * x₂) * hxr'

/-- VERIFY_A1b **Case 2** core computation (apex `v₁ = (1, 0)`): the apex has no second
`Δ₂`-neighbour `r` inside the unit disc.  By symmetry `v₃ = (x₂, −y₂)`; if `|r v₂|² = D` (or `|r
v₃|² = D`) then `case2_aux_real` puts the other distance at `2 ∈ (1, D)`; if both are `≤ 1` then
`ρ(1 − x₂) ≤ 0`. -/
theorem case2_real {x₂ y₂ x₃ y₃ xr yr D : ℝ} (hD : 1 < D)
    (h₂ : x₂ ^ 2 + y₂ ^ 2 = 1) (h₃ : x₃ ^ 2 + y₃ ^ 2 = 1)
    (h12 : (1 - x₂) ^ 2 + y₂ ^ 2 = D) (h13 : (1 - x₃) ^ 2 + y₃ ^ 2 = D)
    (h23 : (x₂ - x₃) ^ 2 + (y₂ - y₃) ^ 2 ≤ 1) (hne : ¬ (x₂ = x₃ ∧ y₂ = y₃))
    (hr1 : (xr - 1) ^ 2 + yr ^ 2 = 1) (hrn : xr ^ 2 + yr ^ 2 ≤ 1) (hr0 : 0 < xr ^ 2 + yr ^ 2)
    (g2 : (xr - x₂) ^ 2 + (yr - y₂) ^ 2 ≤ 1 ∨ (xr - x₂) ^ 2 + (yr - y₂) ^ 2 = D)
    (g3 : (xr - x₃) ^ 2 + (yr - y₃) ^ 2 ≤ 1 ∨ (xr - x₃) ^ 2 + (yr - y₃) ^ 2 = D) : False := by
  have hx : x₃ = x₂ := by linear_combination (1/2 : ℝ) * h12 - (1/2 : ℝ) * h13 -
    (1/2 : ℝ) * h₂ + (1/2 : ℝ) * h₃
  have hy : y₃ = -y₂ := by
    have : (y₃ - y₂) * (y₃ + y₂) = 0 := by rw [hx] at h₃; linear_combination h₃ - h₂
    rcases mul_eq_zero.1 this with h | h
    · exact absurd ⟨hx.symm, by linarith⟩ hne
    · linarith
  subst x₃ y₃
  have hy4 : 4 * y₂ ^ 2 ≤ 1 := by nlinarith
  rcases g2 with g2 | g2
  · rcases g3 with g3 | g3
    · have hDx : D = 2 - 2 * x₂ := by linear_combination -h12 + h₂
      have e2 : (xr - x₂) ^ 2 + (yr - y₂) ^ 2 =
          xr ^ 2 + yr ^ 2 - 2 * xr * x₂ - 2 * yr * y₂ + 1 := by
        linear_combination h₂
      have e3 : (xr - x₂) ^ 2 + (yr - -y₂) ^ 2 =
          xr ^ 2 + yr ^ 2 - 2 * xr * x₂ + 2 * yr * y₂ + 1 := by
        linear_combination h₂
      have hρ : xr ^ 2 + yr ^ 2 = 2 * xr := by linear_combination hr1
      have hxr : 0 < xr := by linarith
      have : xr * (1 - x₂) ≤ 0 := by nlinarith
      have := mul_pos hxr (by linarith : (0:ℝ) < 1 - x₂)
      linarith
    · obtain ⟨h, hx0⟩ := case2_aux_real (y₂ := -y₂) hD (by linear_combination h₂)
        (by linear_combination h12) (by nlinarith) hr1 hrn g3
      have : (yr + -y₂) = yr - y₂ := by ring
      rw [this] at h
      linarith
  · obtain ⟨h, hx0⟩ := case2_aux_real hD h₂ h12 hy4 hr1 hrn g2
    have : (yr - -y₂) = yr + y₂ := by ring
    rw [this] at g3
    rcases g3 with g3 | g3
    · linarith
    · have hDx : D = 2 - 2 * x₂ := by linear_combination -h12 + h₂
      exact hx0 (by linarith)

/-- The two candidates of VERIFY_A1b Case 1: if `A, C` are unit vectors at `120°` and `|rA|² = 1`,
`|rC|² = 3`, then `r = (ρ − 2/3)A + (ρ − 4/3)C` with `ρ = |r|²` and `ρ² − 3ρ + 4/3 = 0`. -/
theorem cand_real {a0 a1 c0 c1 r0 r1 : ℝ} (ha : a0 ^ 2 + a1 ^ 2 = 1) (hc : c0 ^ 2 + c1 ^ 2 = 1)
    (hac : a0 * c0 + a1 * c1 = -1 / 2)
    (hra : (r0 - a0) ^ 2 + (r1 - a1) ^ 2 = 1) (hrc : (r0 - c0) ^ 2 + (r1 - c1) ^ 2 = 3) :
    r0 = (r0 ^ 2 + r1 ^ 2 - 2 / 3) * a0 + (r0 ^ 2 + r1 ^ 2 - 4 / 3) * c0 ∧
    r1 = (r0 ^ 2 + r1 ^ 2 - 2 / 3) * a1 + (r0 ^ 2 + r1 ^ 2 - 4 / 3) * c1 ∧
    (r0 ^ 2 + r1 ^ 2) ^ 2 - 3 * (r0 ^ 2 + r1 ^ 2) + 4 / 3 = 0 := by
  set ρ := r0 ^ 2 + r1 ^ 2 with hρ
  have hA : r0 * a0 + r1 * a1 = ρ / 2 := by linear_combination (-1/2 : ℝ) * hra + (1/2 : ℝ) * ha
  have hC : r0 * c0 + r1 * c1 = ρ / 2 - 1 := by
    linear_combination (-1/2 : ℝ) * hrc + (1/2 : ℝ) * hc
  have hcr : (a0 * c1 - a1 * c0) ^ 2 = 3 / 4 := by
    linear_combination (c0 ^ 2 + c1 ^ 2) * ha + hc - (a0 * c0 + a1 * c1 - 1 / 2) * hac
  have hne : a0 * c1 - a1 * c0 ≠ 0 := by
    intro h; rw [h] at hcr; norm_num at hcr
  have hw0 : (a0 * c1 - a1 * c0) * (r0 - ((ρ - 2 / 3) * a0 + (ρ - 4 / 3) * c0)) = 0 := by
    linear_combination c1 * hA - c1 * (ρ - 2 / 3) * ha - c1 * (ρ - 4 / 3) * hac - a1 * hC +
      a1 * (ρ - 2 / 3) * hac + a1 * (ρ - 4 / 3) * hc
  have hw1 : (a0 * c1 - a1 * c0) * (r1 - ((ρ - 2 / 3) * a1 + (ρ - 4 / 3) * c1)) = 0 := by
    linear_combination a0 * hC - a0 * (ρ - 2 / 3) * hac - a0 * (ρ - 4 / 3) * hc - c0 * hA +
      c0 * (ρ - 2 / 3) * ha + c0 * (ρ - 4 / 3) * hac
  have e0 : r0 = (ρ - 2 / 3) * a0 + (ρ - 4 / 3) * c0 := by
    linarith [(mul_eq_zero.1 hw0).resolve_left hne]
  have e1 : r1 = (ρ - 2 / 3) * a1 + (ρ - 4 / 3) * c1 := by
    linarith [(mul_eq_zero.1 hw1).resolve_left hne]
  refine ⟨e0, e1, ?_⟩
  have hq : ρ = r0 ^ 2 + r1 ^ 2 := hρ
  linear_combination hq - (r0 + ((ρ - 2 / 3) * a0 + (ρ - 4 / 3) * c0)) * e0 -
    (r1 + ((ρ - 2 / 3) * a1 + (ρ - 4 / 3) * c1)) * e1 - (ρ - 2 / 3) ^ 2 * ha -
    (ρ - 4 / 3) ^ 2 * hc - 2 * (ρ - 2 / 3) * (ρ - 4 / 3) * hac

/-- Case 1 incompatibility: a candidate `r` of `A` pointing to `C` and a candidate `s` of `C`
(pointing to `A` or to the third vertex `−A − C`) are at squared distance `4/3` or `3ρ`, both in
`(1, 3)`. -/
theorem case1_pair_real {a0 a1 c0 c1 r0 r1 s0 s1 : ℝ} (ha : a0 ^ 2 + a1 ^ 2 = 1)
    (hc : c0 ^ 2 + c1 ^ 2 = 1) (hac : a0 * c0 + a1 * c1 = -1 / 2)
    (hra : (r0 - a0) ^ 2 + (r1 - a1) ^ 2 = 1) (hrc : (r0 - c0) ^ 2 + (r1 - c1) ^ 2 = 3)
    (hrn : r0 ^ 2 + r1 ^ 2 ≤ 1)
    (hsc : (s0 - c0) ^ 2 + (s1 - c1) ^ 2 = 1) (hsn : s0 ^ 2 + s1 ^ 2 ≤ 1)
    (hsx : (s0 - a0) ^ 2 + (s1 - a1) ^ 2 = 3 ∨
      (s0 - (-a0 - c0)) ^ 2 + (s1 - (-a1 - c1)) ^ 2 = 3) :
    1 < (r0 - s0) ^ 2 + (r1 - s1) ^ 2 ∧ (r0 - s0) ^ 2 + (r1 - s1) ^ 2 < 3 := by
  obtain ⟨e0, e1, q⟩ := cand_real ha hc hac hra hrc
  set ρ := r0 ^ 2 + r1 ^ 2 with hρ
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hne1 : ρ ≠ 1 := by intro h; rw [h] at q; norm_num at q
  have hlt : ρ < 1 := lt_of_le_of_ne hrn hne1
  have hgt : 1 / 3 < ρ := by
    by_contra h; push Not at h
    have : ρ * (3 - ρ) ≤ 1 := by nlinarith
    have e : ρ * (3 - ρ) = 4 / 3 := by linear_combination -q
    linarith
  have hK : (-a0 - c0) ^ 2 + (-a1 - c1) ^ 2 = 1 := by linear_combination ha + hc + 2 * hac
  have hCK : c0 * (-a0 - c0) + c1 * (-a1 - c1) = -1 / 2 := by linear_combination -hac - hc
  have hca : c0 * a0 + c1 * a1 = -1 / 2 := by linear_combination hac
  have same : ∀ σ : ℝ, σ ^ 2 - 3 * σ + 4 / 3 = 0 → σ ≤ 1 → σ = ρ := by
    intro σ hσ hσ1
    have : (σ - ρ) * (σ + ρ - 3) = 0 := by linear_combination hσ - q
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  rcases hsx with hsx | hsx
  · obtain ⟨f0, f1, q'⟩ := cand_real hc ha hca hsc hsx
    have hσ := same _ q' hsn
    rw [hσ] at f0 f1
    have hv : (r0 - s0) ^ 2 + (r1 - s1) ^ 2 = 4 / 3 := by
      rw [e0, e1, f0, f1]
      linear_combination (4 / 9 : ℝ) * ha + (4 / 9 : ℝ) * hc - (8 / 9 : ℝ) * hac
    constructor <;> linarith
  · obtain ⟨f0, f1, q'⟩ := cand_real hc hK hCK hsc hsx
    have hσ := same _ q' hsn
    rw [hσ] at f0 f1
    have hv : (r0 - s0) ^ 2 + (r1 - s1) ^ 2 = 3 * ρ := by
      rw [e0, e1, f0, f1]
      linear_combination (2 * ρ - 2) ^ 2 * ha + (ρ - 2) ^ 2 * hc +
        2 * (2 * ρ - 2) * (ρ - 2) * hac + 3 * q
    constructor <;> linarith

/-- For three unit vectors with `u + v + w = 0` and `r ≠ 0` with `|ru| = 1`: `r` is at squared
distance `> 1` from `v` or from `w` (the sum of the two is `3|r|² + 2`). -/
theorem far_real {u0 u1 v0 v1 w0 w1 p q : ℝ} (hu : u0 ^ 2 + u1 ^ 2 = 1)
    (hv : v0 ^ 2 + v1 ^ 2 = 1) (hw : w0 ^ 2 + w1 ^ 2 = 1)
    (hs0 : u0 + v0 + w0 = 0) (hs1 : u1 + v1 + w1 = 0)
    (hr : (p - u0) ^ 2 + (q - u1) ^ 2 = 1) (hr0 : 0 < p ^ 2 + q ^ 2) :
    1 < (p - v0) ^ 2 + (q - v1) ^ 2 ∨ 1 < (p - w0) ^ 2 + (q - w1) ^ 2 := by
  have e : (p - v0) ^ 2 + (q - v1) ^ 2 + ((p - w0) ^ 2 + (q - w1) ^ 2) =
      3 * (p ^ 2 + q ^ 2) + 2 := by
    linear_combination hv + hw - hr + hu - 2 * p * hs0 - 2 * q * hs1
  by_contra h; push Not at h
  linarith [h.1, h.2]

/-- VERIFY_A1b **Case 1** core computation (`v₁ = (1,0)`): `D = 3`, `v₂ = (−1/2, y₂)`, `v₃ = (−1/2,
−y₂)`; each extra neighbour `rᵢ` is at squared distance `3` from another vertex (`far_real`),
and `case1_pair_real` puts `|r₁ r₂|²` or `|r₁ r₃|²` in the gap `(1, 3)`. -/
theorem case1_real {x₂ y₂ x₃ y₃ p₁ q₁ p₂ q₂ p₃ q₃ D : ℝ} (hD : 1 < D)
    (h₂ : x₂ ^ 2 + y₂ ^ 2 = 1) (h₃ : x₃ ^ 2 + y₃ ^ 2 = 1)
    (h12 : (1 - x₂) ^ 2 + y₂ ^ 2 = D) (h13 : (1 - x₃) ^ 2 + y₃ ^ 2 = D)
    (h23 : (x₂ - x₃) ^ 2 + (y₂ - y₃) ^ 2 = D)
    (hr₁ : (p₁ - 1) ^ 2 + q₁ ^ 2 = 1) (hr₂ : (p₂ - x₂) ^ 2 + (q₂ - y₂) ^ 2 = 1)
    (hr₃ : (p₃ - x₃) ^ 2 + (q₃ - y₃) ^ 2 = 1)
    (n₁ : p₁ ^ 2 + q₁ ^ 2 ≤ 1) (n₂ : p₂ ^ 2 + q₂ ^ 2 ≤ 1) (n₃ : p₃ ^ 2 + q₃ ^ 2 ≤ 1)
    (z₁ : 0 < p₁ ^ 2 + q₁ ^ 2) (z₂ : 0 < p₂ ^ 2 + q₂ ^ 2) (z₃ : 0 < p₃ ^ 2 + q₃ ^ 2)
    (g12 : (p₁ - x₂) ^ 2 + (q₁ - y₂) ^ 2 ≤ 1 ∨ (p₁ - x₂) ^ 2 + (q₁ - y₂) ^ 2 = D)
    (g13 : (p₁ - x₃) ^ 2 + (q₁ - y₃) ^ 2 ≤ 1 ∨ (p₁ - x₃) ^ 2 + (q₁ - y₃) ^ 2 = D)
    (g21 : (p₂ - 1) ^ 2 + q₂ ^ 2 ≤ 1 ∨ (p₂ - 1) ^ 2 + q₂ ^ 2 = D)
    (g23 : (p₂ - x₃) ^ 2 + (q₂ - y₃) ^ 2 ≤ 1 ∨ (p₂ - x₃) ^ 2 + (q₂ - y₃) ^ 2 = D)
    (g31 : (p₃ - 1) ^ 2 + q₃ ^ 2 ≤ 1 ∨ (p₃ - 1) ^ 2 + q₃ ^ 2 = D)
    (g32 : (p₃ - x₂) ^ 2 + (q₃ - y₂) ^ 2 ≤ 1 ∨ (p₃ - x₂) ^ 2 + (q₃ - y₂) ^ 2 = D)
    (gr12 : (p₁ - p₂) ^ 2 + (q₁ - q₂) ^ 2 ≤ 1 ∨ (p₁ - p₂) ^ 2 + (q₁ - q₂) ^ 2 = D)
    (gr13 : (p₁ - p₃) ^ 2 + (q₁ - q₃) ^ 2 ≤ 1 ∨ (p₁ - p₃) ^ 2 + (q₁ - q₃) ^ 2 = D) : False := by
  have hx : x₃ = x₂ := by linear_combination (1/2 : ℝ) * h12 - (1/2 : ℝ) * h13 -
    (1/2 : ℝ) * h₂ + (1/2 : ℝ) * h₃
  have hy : y₃ = -y₂ := by
    have : (y₃ - y₂) * (y₃ + y₂) = 0 := by rw [hx] at h₃; linear_combination h₃ - h₂
    rcases mul_eq_zero.1 this with h | h
    · exfalso
      have hy' : y₃ = y₂ := by linarith
      rw [hx, hy'] at h23
      nlinarith
    · linarith
  subst x₃ y₃
  have hDx : D = 2 - 2 * x₂ := by linear_combination -h12 + h₂
  have h4 : 4 * y₂ ^ 2 = D := by linear_combination h23
  have hx2 : x₂ = -1 / 2 := by
    have : (2 * x₂ + 1) * (x₂ - 1) = 0 := by
      linear_combination (-1/2 : ℝ) * h4 - (1/2 : ℝ) * hDx + 2 * h₂
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exfalso; linarith
  subst x₂
  have hD3 : D = 3 := by linarith
  subst hD3
  have hy2 : y₂ ^ 2 = 3 / 4 := by linarith
  have u2 : (-1 / 2 : ℝ) ^ 2 + y₂ ^ 2 = 1 := h₂
  have u3 : (-1 / 2 : ℝ) ^ 2 + (-y₂) ^ 2 = 1 := by linear_combination h₂
  have u1 : (1 : ℝ) ^ 2 + 0 ^ 2 = 1 := by norm_num
  -- which vertex is `r₁` far from
  have F1 := far_real (u0 := 1) (u1 := 0) (v0 := -1/2) (v1 := y₂) (w0 := -1/2) (w1 := -y₂)
    (p := p₁) (q := q₁) u1 u2 u3 (by norm_num) (by ring) (by linear_combination hr₁) z₁
  have F2 := far_real (u0 := -1/2) (u1 := y₂) (v0 := 1) (v1 := 0) (w0 := -1/2) (w1 := -y₂)
    (p := p₂) (q := q₂) u2 u1 u3 (by norm_num) (by ring) hr₂ z₂
  have F3 := far_real (u0 := -1/2) (u1 := -y₂) (v0 := 1) (v1 := 0) (w0 := -1/2) (w1 := y₂)
    (p := p₃) (q := q₃) u3 u1 u2 (by norm_num) (by ring) hr₃ z₃
  have hac2 : (1 : ℝ) * (-1 / 2) + 0 * y₂ = -1 / 2 := by ring
  have hac3 : (1 : ℝ) * (-1 / 2) + 0 * (-y₂) = -1 / 2 := by ring
  rcases F1 with F1 | F1
  · -- `r₁` points to `v₂`; compare with `r₂`
    have e12 : (p₁ - -1 / 2) ^ 2 + (q₁ - y₂) ^ 2 = 3 := g12.resolve_left (by linarith)
    have hsx : (p₂ - 1) ^ 2 + (q₂ - 0) ^ 2 = 3 ∨
        (p₂ - (-1 - -1 / 2)) ^ 2 + (q₂ - (-0 - y₂)) ^ 2 = 3 := by
      rcases F2 with F2 | F2
      · left; have := g21.resolve_left (by linarith [F2]); linear_combination this
      · right; have := g23.resolve_left (by linarith [F2]); linear_combination this
    have P := case1_pair_real (a0 := 1) (a1 := 0) (c0 := -1/2) (c1 := y₂) (r0 := p₁) (r1 := q₁)
      (s0 := p₂) (s1 := q₂) u1 u2 hac2 (by linear_combination hr₁) e12 n₁ hr₂ n₂ hsx
    rcases gr12 with h | h <;> linarith [P.1, P.2]
  · have e13 : (p₁ - -1 / 2) ^ 2 + (q₁ - -y₂) ^ 2 = 3 := g13.resolve_left (by linarith)
    have hsx : (p₃ - 1) ^ 2 + (q₃ - 0) ^ 2 = 3 ∨
        (p₃ - (-1 - -1 / 2)) ^ 2 + (q₃ - (-0 - -y₂)) ^ 2 = 3 := by
      rcases F3 with F3 | F3
      · left; have := g31.resolve_left (by linarith [F3]); linear_combination this
      · right; have := g32.resolve_left (by linarith [F3]); linear_combination this
    have P := case1_pair_real (a0 := 1) (a1 := 0) (c0 := -1/2) (c1 := -y₂) (r0 := p₁)
      (r1 := q₁) (s0 := p₃) (s1 := q₃) u1 u3 hac3 (by linear_combination hr₁) e13 n₁ hr₃ n₃ hsx
    rcases gr13 with h | h <;> linarith [P.1, P.2]

/-- End of Lemma F: a neighbour `a` of `p = 0` with `a·w < 0` (`w = (1,0)`) is at distance `Δ` from
`w`, hence (chord monotonicity) farther than `Δ` from a neighbour `b` on the other side of `w`. -/
theorem lemmaF_end_real {xa ya xb yb D : ℝ} (ha : xa ^ 2 + ya ^ 2 = 1)
    (hb : xb ^ 2 + yb ^ 2 = 1) (hxa : xa < 0) (hya : ya < 0) (hyb : 0 < yb)
    (hab : 0 < xa * yb - ya * xb)
    (gw : (xa - 1) ^ 2 + ya ^ 2 ≤ 1 ∨ (xa - 1) ^ 2 + ya ^ 2 = D)
    (m : (xa - xb) ^ 2 + (ya - yb) ^ 2 ≤ D) : False := by
  have sw : (xa - 1) ^ 2 + ya ^ 2 = 2 - 2 * xa := by linear_combination ha
  have ew : (xa - 1) ^ 2 + ya ^ 2 = D := gw.resolve_left (by linarith)
  have hch := chord_real (a0 := xa) (a1 := ya) (w0 := 1) (w1 := 0) (b0 := xb) (b1 := yb) ha
    (by norm_num) hb (by ring_nf; linarith) hab (by ring_nf; linarith)
  have sb : (xa - xb) ^ 2 + (ya - yb) ^ 2 = 2 - 2 * (xa * xb + ya * yb) := by
    linear_combination ha + hb
  ring_nf at hch
  linarith

/-- **Lemma F** core computation (`p = 0`, `w = (1,0)`, `r` not below the axis): Lemma M gives `|r
a₁|² = |r a₂|² = D`, so `r ∥ a₁ + a₂`, which forces `x₁ + x₂ < 0`; conclude with
`lemmaF_end_real`. -/
theorem lemmaF_real {x₁ y₁ x₂ y₂ xb yb xr yr D : ℝ} (_hD : 1 < D)
    (h₁ : x₁ ^ 2 + y₁ ^ 2 = 1) (h₂ : x₂ ^ 2 + y₂ ^ 2 = 1) (hb : xb ^ 2 + yb ^ 2 = 1)
    (hy₁ : y₁ < 0) (hy₂ : y₂ < 0) (hyb : 0 < yb) (hne : ¬ (x₁ = x₂ ∧ y₁ = y₂))
    (hc₁ : 0 < x₁ * yb - y₁ * xb) (hc₂ : 0 < x₂ * yb - y₂ * xb)
    (hr : (xr - 1) ^ 2 + yr ^ 2 = 1) (hr0 : 0 < xr ^ 2 + yr ^ 2) (hyr : 0 ≤ yr)
    (g₁ : (xr - x₁) ^ 2 + (yr - y₁) ^ 2 ≤ 1 ∨ (xr - x₁) ^ 2 + (yr - y₁) ^ 2 = D)
    (g₂ : (xr - x₂) ^ 2 + (yr - y₂) ^ 2 ≤ 1 ∨ (xr - x₂) ^ 2 + (yr - y₂) ^ 2 = D)
    (gw₁ : (x₁ - 1) ^ 2 + y₁ ^ 2 ≤ 1 ∨ (x₁ - 1) ^ 2 + y₁ ^ 2 = D)
    (gw₂ : (x₂ - 1) ^ 2 + y₂ ^ 2 ≤ 1 ∨ (x₂ - 1) ^ 2 + y₂ ^ 2 = D)
    (m₁ : (x₁ - xb) ^ 2 + (y₁ - yb) ^ 2 ≤ D) (m₂ : (x₂ - xb) ^ 2 + (y₂ - yb) ^ 2 ≤ D) :
    False := by
  have M1 := lemmaM_real h₁ hy₁ hr hyr hr0
  have M2 := lemmaM_real h₂ hy₂ hr hyr hr0
  have e1 := g₁.resolve_left (by linarith)
  have e2 := g₂.resolve_left (by linarith)
  have hdot : xr * x₁ + yr * y₁ = xr * x₂ + yr * y₂ := by
    linear_combination (-1/2 : ℝ) * e1 + (1/2 : ℝ) * e2 + (1/2 : ℝ) * h₁ - (1/2 : ℝ) * h₂
  have hd : 0 < (x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2 := by
    by_contra h; push Not at h
    have a := sq_nonneg (x₁ - x₂)
    have b := sq_nonneg (y₁ - y₂)
    have ha : (x₁ - x₂) ^ 2 = 0 := by linarith
    have hb : (y₁ - y₂) ^ 2 = 0 := by linarith
    exact hne ⟨by linarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.1 ha],
      by linarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.1 hb]⟩
  have hcr : ((x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2) * (xr * (y₁ + y₂) - yr * (x₁ + x₂)) = 0 := by
    linear_combination ((x₁ - x₂) * (y₁ + y₂) - (y₁ - y₂) * (x₁ + x₂)) * hdot +
      ((y₁ - y₂) * xr - (x₁ - x₂) * yr) * (h₁ - h₂)
  have hcross : xr * (y₁ + y₂) - yr * (x₁ + x₂) = 0 := (mul_eq_zero.1 hcr).resolve_left hd.ne'
  have hxr : 0 < xr := by
    have : (xr - 1) ^ 2 + yr ^ 2 = xr ^ 2 + yr ^ 2 - 2 * xr + 1 := by ring
    linarith
  have hsx : x₁ + x₂ < 0 := by
    by_contra h; push Not at h
    have k1 : xr * (y₁ + y₂) < 0 := mul_neg_of_pos_of_neg hxr (by linarith)
    have k2 : 0 ≤ yr * (x₁ + x₂) := mul_nonneg hyr h
    linarith
  rcases lt_or_ge x₁ 0 with hx | hx
  · exact lemmaF_end_real h₁ hb hx hy₁ hyb hc₁ gw₁ m₁
  · exact lemmaF_end_real h₂ hb (by linarith) hy₂ hyb hc₂ gw₂ m₂

/-! ## Prop 3: core vertices of `L₂` have core degree `2` -/

/-- `frame_sqd` with the scale `sqd q v` named. -/
theorem frame_nsq {q v : Pt} {s : ℝ} (h : q ≠ v) (hs : sqd q v = s) (P Q : Pt) :
    (fx q v P - fx q v Q) ^ 2 + (fy q v P - fy q v Q) ^ 2 = sqd P Q / s := by
  rw [frame_sqd h, hs]

/-- Squared frame norm of `P` is `sqd q P / sqd q v`. -/
theorem frame_norm' {q v : Pt} {s : ℝ} (h : q ≠ v) (hs : sqd q v = s) (P : Pt) :
    fx q v P ^ 2 + fy q v P ^ 2 = sqd q P / s := by
  have := frame_nsq h hs P q
  rw [(frame_base q v).1, (frame_base q v).2, sub_zero, sub_zero, sqd_comm] at this
  exact this

/-- Normalised gap: `sqd P Q / Δ₂² ≤ 1` or `= Δ² / Δ₂²`. -/
theorem TwoLargest.ngap {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) {P Q : Pt}
    (hP : P ∈ X) (hQ : Q ∈ X) : sqd P Q / Δ₂ ^ 2 ≤ 1 ∨ sqd P Q / Δ₂ ^ 2 = Δ ^ 2 / Δ₂ ^ 2 := by
  have hs : 0 < Δ₂ ^ 2 := by have := hT.pos; positivity
  rcases hT.sqd_gap hP hQ with h | h
  · exact Or.inl (div_le_one_of_le₀ h hs.le)
  · exact Or.inr (by rw [h])

/-- Normalised maximality: `sqd P Q / Δ₂² ≤ Δ² / Δ₂²`. -/
theorem TwoLargest.nle {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) {P Q : Pt}
    (hP : P ∈ X) (hQ : Q ∈ X) : sqd P Q / Δ₂ ^ 2 ≤ Δ ^ 2 / Δ₂ ^ 2 := by
  have hs : 0 < Δ₂ ^ 2 := by have := hT.pos; positivity
  exact div_le_div_of_nonneg_right (hT.sqd_le hP hQ) hs.le

/-- `1 < Δ² / Δ₂²`. -/
theorem TwoLargest.one_lt {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) :
    1 < Δ ^ 2 / Δ₂ ^ 2 := by
  have hs : 0 < Δ₂ ^ 2 := by have := hT.pos; positivity
  exact (one_lt_div hs).2 (pow_lt_pow_left₀ hT.snd_lt hT.pos.le two_ne_zero)

/-- Points at distance `Δ₂ > 0` are distinct. -/
theorem ne_of_dist_snd {Δ₂ : ℝ} (hpos : 0 < Δ₂) {q v : Pt} (h : dist q v = Δ₂) : q ≠ v := by
  rintro rfl; rw [dist_self] at h; linarith

/-- Case 3 when the middle neighbour `m` separates `a` and `c` (frame at `q` with axis `m`; the
witness `t` comes from `q` not being extreme). -/
theorem prop3_case3_core {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) {q m a c : Pt}
    (hq : q ∈ X) (hqe : ¬ IsExt X q) (hm : m ∈ X) (ha : a ∈ X) (hc : c ∈ X)
    (hqm : dist q m = Δ₂) (hqa : dist q a = Δ₂) (hqc : dist q c = Δ₂)
    (hma : sqd m a ≤ Δ₂ ^ 2) (hmc : sqd m c ≤ Δ₂ ^ 2)
    (hopp : orient q m a * orient q m c < 0) : False := by
  have hpos := hT.pos
  have hs0 : 0 < Δ₂ ^ 2 := by positivity
  have hne := ne_of_dist_snd hpos hqm
  have hs : sqd q m = Δ₂ ^ 2 := (dist_eq_iff_sqd hpos.le).1 hqm
  obtain ⟨m0, m1⟩ := frame_axis hne
  have N := frame_nsq hne hs
  have Nn := frame_norm' hne hs
  obtain ⟨t, htX, htq, ht⟩ := exists_of_not_isExt hq hqe (q 0 - m 0) (q 1 - m 1)
  have hxt : fx q m t ≤ 0 := by
    unfold fx
    refine div_nonpos_of_nonpos_of_nonneg ?_ (sqd_pos_of_ne hne).le
    have e : dotp q m t = -((q 0 - m 0) * (t 0 - q 0) + (q 1 - m 1) * (t 1 - q 1)) := by
      simp only [dotp]; ring
    linarith
  have ht0 : 0 < fx q m t ^ 2 + fy q m t ^ 2 := by
    rw [Nn]; exact div_pos (sqd_pos_of_ne (Ne.symm htq)) hs0
  have unit : ∀ P, dist q P = Δ₂ → fx q m P ^ 2 + fy q m P ^ 2 = 1 := fun P hP => by
    rw [Nn, (dist_eq_iff_sqd hpos.le).1 hP, div_self hs0.ne']
  have close : ∀ P, sqd m P ≤ Δ₂ ^ 2 → (fx q m P - 1) ^ 2 + fy q m P ^ 2 ≤ 1 := fun P hP => by
    have := N P m
    rw [m0, m1, sub_zero, sqd_comm] at this
    rw [this]; exact div_le_one_of_le₀ hP hs0.le
  have gap : ∀ P ∈ X, ∀ Q ∈ X, (fx q m P - fx q m Q) ^ 2 + (fy q m P - fy q m Q) ^ 2 ≤ 1 ∨
      (fx q m P - fx q m Q) ^ 2 + (fy q m P - fy q m Q) ^ 2 = Δ ^ 2 / Δ₂ ^ 2 :=
    fun P hP Q hQ => by rw [N]; exact hT.ngap hP hQ
  have gb := gap t htX m hm
  rw [m0, m1, sub_zero] at gb
  have hopp' : fy q m a * fy q m c < 0 := by
    unfold fy; rw [div_mul_div_comm]
    exact div_neg_of_neg_of_pos hopp (by have := sqd_pos_of_ne hne; positivity)
  exact case3_real' hT.one_lt (unit a hqa) (unit c hqc) (close a hma) (close c hmc) hopp' hxt ht0
    (gap t htX a ha) gb (gap t htX c hc)

/-- **Case 3** (at most one `Δ`-pair, labelled so that `v₂` is within `Δ₂` of both others): in the
frame at `q` with axis `v₂`, either `v₂` separates `v₁, v₃`, or `case3_select_real` makes `v₁`
or `v₃` the separating middle neighbour. -/
theorem prop3_case3 {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) {q v₁ v₂ v₃ : Pt}
    (hq : q ∈ X) (hqe : ¬ IsExt X q) (h₁ : v₁ ∈ X) (h₂ : v₂ ∈ X) (h₃ : v₃ ∈ X)
    (h12 : v₁ ≠ v₂) (h13 : v₁ ≠ v₃) (h23 : v₂ ≠ v₃)
    (d₁ : dist q v₁ = Δ₂) (d₂ : dist q v₂ = Δ₂) (d₃ : dist q v₃ = Δ₂)
    (s12 : sqd v₁ v₂ ≤ Δ₂ ^ 2) (s23 : sqd v₂ v₃ ≤ Δ₂ ^ 2) : False := by
  have hpos := hT.pos
  have hs0 : 0 < Δ₂ ^ 2 := by positivity
  have hne := ne_of_dist_snd hpos d₂
  have hs : sqd q v₂ = Δ₂ ^ 2 := (dist_eq_iff_sqd hpos.le).1 d₂
  obtain ⟨m0, m1⟩ := frame_axis hne
  have N := frame_nsq hne hs
  have Nn := frame_norm' hne hs
  have unit : ∀ P, dist q P = Δ₂ → fx q v₂ P ^ 2 + fy q v₂ P ^ 2 = 1 := fun P hP => by
    rw [Nn, (dist_eq_iff_sqd hpos.le).1 hP, div_self hs0.ne']
  have close : ∀ P, sqd P v₂ ≤ Δ₂ ^ 2 → (fx q v₂ P - 1) ^ 2 + fy q v₂ P ^ 2 ≤ 1 := fun P hP => by
    have := N P v₂
    rw [m0, m1, sub_zero] at this
    rw [this]; exact div_le_one_of_le₀ hP hs0.le
  have ha := unit v₁ d₁
  have hc := unit v₃ d₃
  have hab := close v₁ s12
  have hcb := close v₃ (by rw [sqd_comm]; exact s23)
  -- neither `v₁` nor `v₃` lies on the axis
  have ynz : ∀ P, P ≠ v₂ → fx q v₂ P ^ 2 + fy q v₂ P ^ 2 = 1 →
      (fx q v₂ P - 1) ^ 2 + fy q v₂ P ^ 2 ≤ 1 → fy q v₂ P ≠ 0 := by
    intro P hP hu hcl hy
    rw [hy] at hu
    have hx : fx q v₂ P = 1 := by nlinarith
    have := N P v₂
    rw [m0, m1, hx, hy, sub_self, sub_self] at this
    have h0 : sqd P v₂ = 0 := by
      have := (div_eq_zero_iff.1 (by rw [← this]; norm_num)).resolve_right hs0.ne'
      exact this
    exact (sqd_pos_of_ne hP).ne' h0
  have ya := ynz v₁ h12 ha hab
  have yc := ynz v₃ (Ne.symm h23) hc hcb
  -- orientation in the frame
  have O : ∀ P Q, orient q P Q = (fx q v₂ P * fy q v₂ Q - fy q v₂ P * fx q v₂ Q) * Δ₂ ^ 2 :=
    fun P Q => by rw [frame_cross hne, hs, div_mul_cancel₀ _ hs0.ne']
  rcases lt_trichotomy (fy q v₂ v₁ * fy q v₂ v₃) 0 with hopp | h0 | hsame
  · refine prop3_case3_core hT hq hqe h₂ h₁ h₃ d₂ d₁ d₃ (by rw [sqd_comm]; exact s12) s23 ?_
    rw [O, O, m0, m1]
    have := mul_pos hs0 hs0
    have e : (1 * fy q v₂ v₁ - 0 * fx q v₂ v₁) * Δ₂ ^ 2 * ((1 * fy q v₂ v₃ - 0 * fx q v₂ v₃) *
        Δ₂ ^ 2) = (fy q v₂ v₁ * fy q v₂ v₃) * (Δ₂ ^ 2 * Δ₂ ^ 2) := by ring
    rw [e]; exact mul_neg_of_neg_of_pos hopp this
  · exact (mul_ne_zero ya yc) h0
  · have hne13 : ¬ (fx q v₂ v₁ = fx q v₂ v₃ ∧ fy q v₂ v₁ = fy q v₂ v₃) := by
      rintro ⟨hx, hy⟩
      have := N v₁ v₃
      rw [hx, hy, sub_self, sub_self] at this
      have h0 : sqd v₁ v₃ = 0 :=
        (div_eq_zero_iff.1 (by rw [← this]; norm_num)).resolve_right hs0.ne'
      exact (sqd_pos_of_ne h13).ne' h0
    obtain ⟨hac, hmid⟩ := case3_select_real ha hc hab hcb hsame hne13
    have s13 : sqd v₁ v₃ ≤ Δ₂ ^ 2 := by
      rw [N] at hac
      exact (div_le_one hs0).1 hac
    have := mul_pos hs0 hs0
    rcases hmid with hmid | hmid
    · -- `v₁` is the middle neighbour
      refine prop3_case3_core hT hq hqe h₁ h₂ h₃ d₁ d₂ d₃ s12 s13 ?_
      rw [O, O, m0, m1]
      have e : (fx q v₂ v₁ * 0 - fy q v₂ v₁ * 1) * Δ₂ ^ 2 * ((fx q v₂ v₁ * fy q v₂ v₃ -
          fy q v₂ v₁ * fx q v₂ v₃) * Δ₂ ^ 2) = ((-fy q v₂ v₁) * (fx q v₂ v₁ * fy q v₂ v₃ -
          fy q v₂ v₁ * fx q v₂ v₃)) * (Δ₂ ^ 2 * Δ₂ ^ 2) := by ring
      rw [e]; exact mul_neg_of_neg_of_pos hmid this
    · -- `v₃` is the middle neighbour
      refine prop3_case3_core hT hq hqe h₃ h₂ h₁ d₃ d₂ d₁ ?_ ?_ ?_
      · rw [sqd_comm]; exact s23
      · rw [sqd_comm]; exact s13
      · rw [O, O, m0, m1]
        have e : (fx q v₂ v₃ * 0 - fy q v₂ v₃ * 1) * Δ₂ ^ 2 * ((fx q v₂ v₃ * fy q v₂ v₁ -
            fy q v₂ v₃ * fx q v₂ v₁) * Δ₂ ^ 2) = ((-fy q v₂ v₃) * (fx q v₂ v₃ * fy q v₂ v₁ -
            fy q v₂ v₃ * fx q v₂ v₁)) * (Δ₂ ^ 2 * Δ₂ ^ 2) := by ring
        rw [e]; exact mul_neg_of_neg_of_pos hmid this

/-- Distinct points have distinct frame coordinates. -/
theorem frame_inj {q v : Pt} (h : q ≠ v) {P Q : Pt} (hPQ : P ≠ Q) :
    ¬ (fx q v P = fx q v Q ∧ fy q v P = fy q v Q) := by
  rintro ⟨hx, hy⟩
  have := frame_sqd h P Q
  rw [hx, hy, sub_self, sub_self] at this
  have h0 : sqd P Q = 0 :=
    (div_eq_zero_iff.1 (by rw [← this]; norm_num)).resolve_right (sqd_pos_of_ne h).ne'
  exact (sqd_pos_of_ne hPQ).ne' h0

/-- **Case 2** (exactly two `Δ`-pairs, apex `v₁`): in the frame at `q` with axis `v₁`, `case2_real`
shows that `v₁` has no `Δ₂`-neighbour besides `q`. -/
theorem prop3_case2 {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) {q v₁ v₂ v₃ r : Pt}
    (hq : q ∈ X) (hqe : ¬ IsExt X q) (_h₁ : v₁ ∈ X) (h₂ : v₂ ∈ X) (h₃ : v₃ ∈ X)
    (h23 : v₂ ≠ v₃) (d₁ : dist q v₁ = Δ₂) (d₂ : dist q v₂ = Δ₂) (d₃ : dist q v₃ = Δ₂)
    (s12 : sqd v₁ v₂ = Δ ^ 2) (s13 : sqd v₁ v₃ = Δ ^ 2) (s23 : sqd v₂ v₃ ≤ Δ₂ ^ 2)
    (hr : r ∈ X) (hrq : r ≠ q) (hr₁ : dist v₁ r = Δ₂) : False := by
  have hpos := hT.pos
  have hs0 : 0 < Δ₂ ^ 2 := by positivity
  have hne := ne_of_dist_snd hpos d₁
  have hs : sqd q v₁ = Δ₂ ^ 2 := (dist_eq_iff_sqd hpos.le).1 d₁
  obtain ⟨m0, m1⟩ := frame_axis hne
  have N := frame_nsq hne hs
  have Nn := frame_norm' hne hs
  have unit : ∀ P, dist q P = Δ₂ → fx q v₁ P ^ 2 + fy q v₁ P ^ 2 = 1 := fun P hP => by
    rw [Nn, (dist_eq_iff_sqd hpos.le).1 hP, div_self hs0.ne']
  have gap : ∀ P ∈ X, ∀ Q ∈ X, (fx q v₁ P - fx q v₁ Q) ^ 2 + (fy q v₁ P - fy q v₁ Q) ^ 2 ≤ 1 ∨
      (fx q v₁ P - fx q v₁ Q) ^ 2 + (fy q v₁ P - fy q v₁ Q) ^ 2 = Δ ^ 2 / Δ₂ ^ 2 :=
    fun P hP Q hQ => by rw [N]; exact hT.ngap hP hQ
  have h12' : (1 - fx q v₁ v₂) ^ 2 + fy q v₁ v₂ ^ 2 = Δ ^ 2 / Δ₂ ^ 2 := by
    have := N v₁ v₂; rw [m0, m1, s12] at this; linear_combination this
  have h13' : (1 - fx q v₁ v₃) ^ 2 + fy q v₁ v₃ ^ 2 = Δ ^ 2 / Δ₂ ^ 2 := by
    have := N v₁ v₃; rw [m0, m1, s13] at this; linear_combination this
  have h23' : (fx q v₁ v₂ - fx q v₁ v₃) ^ 2 + (fy q v₁ v₂ - fy q v₁ v₃) ^ 2 ≤ 1 := by
    rw [N]; exact div_le_one_of_le₀ s23 hs0.le
  have hr1 : (fx q v₁ r - 1) ^ 2 + fy q v₁ r ^ 2 = 1 := by
    have := N r v₁
    rw [m0, m1, sub_zero, sqd_comm, (dist_eq_iff_sqd hpos.le).1 hr₁, div_self hs0.ne'] at this
    exact this
  have hrn : fx q v₁ r ^ 2 + fy q v₁ r ^ 2 ≤ 1 := by
    rw [Nn]
    exact div_le_one_of_le₀ ((dist_le_iff_sqd hpos.le).1 (dist_le_snd_of_not_isExt hT hq hqe hr))
      hs0.le
  have hr0 : 0 < fx q v₁ r ^ 2 + fy q v₁ r ^ 2 := by
    rw [Nn]; exact div_pos (sqd_pos_of_ne (Ne.symm hrq)) hs0
  exact case2_real hT.one_lt (unit v₂ d₂) (unit v₃ d₃) h12' h13' h23' (frame_inj hne h23) hr1 hrn
    hr0 (gap r hr v₂ h₂) (gap r hr v₃ h₃)

/-- **Case 1** (all three pairs at `Δ`): in the frame at `q` with axis `v₁`, `case1_real` shows that
the three second neighbours `rᵢ` cannot coexist. -/
theorem prop3_case1 {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) {q v₁ v₂ v₃ r₁ r₂ r₃ : Pt}
    (hq : q ∈ X) (hqe : ¬ IsExt X q) (h₁ : v₁ ∈ X) (h₂ : v₂ ∈ X) (h₃ : v₃ ∈ X)
    (d₁ : dist q v₁ = Δ₂) (d₂ : dist q v₂ = Δ₂) (d₃ : dist q v₃ = Δ₂)
    (s12 : sqd v₁ v₂ = Δ ^ 2) (s13 : sqd v₁ v₃ = Δ ^ 2) (s23 : sqd v₂ v₃ = Δ ^ 2)
    (hr₁ : r₁ ∈ X) (hr₂ : r₂ ∈ X) (hr₃ : r₃ ∈ X) (hrq₁ : r₁ ≠ q) (hrq₂ : r₂ ≠ q) (hrq₃ : r₃ ≠ q)
    (e₁ : dist v₁ r₁ = Δ₂) (e₂ : dist v₂ r₂ = Δ₂) (e₃ : dist v₃ r₃ = Δ₂) : False := by
  have hpos := hT.pos
  have hs0 : 0 < Δ₂ ^ 2 := by positivity
  have hne := ne_of_dist_snd hpos d₁
  have hs : sqd q v₁ = Δ₂ ^ 2 := (dist_eq_iff_sqd hpos.le).1 d₁
  obtain ⟨m0, m1⟩ := frame_axis hne
  have N := frame_nsq hne hs
  have Nn := frame_norm' hne hs
  have unit : ∀ P, dist q P = Δ₂ → fx q v₁ P ^ 2 + fy q v₁ P ^ 2 = 1 := fun P hP => by
    rw [Nn, (dist_eq_iff_sqd hpos.le).1 hP, div_self hs0.ne']
  have inn : ∀ P ∈ X, fx q v₁ P ^ 2 + fy q v₁ P ^ 2 ≤ 1 := fun P hP => by
    rw [Nn]
    exact div_le_one_of_le₀ ((dist_le_iff_sqd hpos.le).1 (dist_le_snd_of_not_isExt hT hq hqe hP))
      hs0.le
  have pos : ∀ P, P ≠ q → 0 < fx q v₁ P ^ 2 + fy q v₁ P ^ 2 := fun P hP => by
    rw [Nn]; exact div_pos (sqd_pos_of_ne (Ne.symm hP)) hs0
  have one : ∀ P Q, dist Q P = Δ₂ →
      (fx q v₁ P - fx q v₁ Q) ^ 2 + (fy q v₁ P - fy q v₁ Q) ^ 2 = 1 := fun P Q h => by
    rw [N, sqd_comm, (dist_eq_iff_sqd hpos.le).1 h, div_self hs0.ne']
  have far : ∀ P Q, sqd P Q = Δ ^ 2 →
      (fx q v₁ P - fx q v₁ Q) ^ 2 + (fy q v₁ P - fy q v₁ Q) ^ 2 = Δ ^ 2 / Δ₂ ^ 2 := fun P Q h => by
    rw [N, h]
  have gap : ∀ P ∈ X, ∀ Q ∈ X, (fx q v₁ P - fx q v₁ Q) ^ 2 + (fy q v₁ P - fy q v₁ Q) ^ 2 ≤ 1 ∨
      (fx q v₁ P - fx q v₁ Q) ^ 2 + (fy q v₁ P - fy q v₁ Q) ^ 2 = Δ ^ 2 / Δ₂ ^ 2 :=
    fun P hP Q hQ => by rw [N]; exact hT.ngap hP hQ
  have h12' : (1 - fx q v₁ v₂) ^ 2 + fy q v₁ v₂ ^ 2 = Δ ^ 2 / Δ₂ ^ 2 := by
    have := far v₁ v₂ s12; rw [m0, m1] at this; linear_combination this
  have h13' : (1 - fx q v₁ v₃) ^ 2 + fy q v₁ v₃ ^ 2 = Δ ^ 2 / Δ₂ ^ 2 := by
    have := far v₁ v₃ s13; rw [m0, m1] at this; linear_combination this
  have hr1 : (fx q v₁ r₁ - 1) ^ 2 + fy q v₁ r₁ ^ 2 = 1 := by
    have := one r₁ v₁ e₁; rw [m0, m1, sub_zero] at this; exact this
  have g21 := gap r₂ hr₂ v₁ h₁
  rw [m0, m1, sub_zero] at g21
  have g31 := gap r₃ hr₃ v₁ h₁
  rw [m0, m1, sub_zero] at g31
  exact case1_real hT.one_lt (unit v₂ d₂) (unit v₃ d₃) h12' h13' (far v₂ v₃ s23) hr1
    (one r₂ v₂ e₂) (one r₃ v₃ e₃) (inn r₁ hr₁) (inn r₂ hr₂) (inn r₃ hr₃) (pos r₁ hrq₁)
    (pos r₂ hrq₂) (pos r₃ hrq₃) (gap r₁ hr₁ v₂ h₂) (gap r₁ hr₁ v₃ h₃) g21 (gap r₂ hr₂ v₃ h₃) g31
    (gap r₃ hr₃ v₂ h₂) (gap r₁ hr₁ r₂ hr₂) (gap r₁ hr₁ r₃ hr₃)

/-- A non-extreme point cannot have three `Δ₂`-neighbours that each have a further `Δ₂`-neighbour:
split on which of the three pairs are at distance `Δ` and relabel. -/
theorem prop3_three {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) {q v₁ v₂ v₃ r₁ r₂ r₃ : Pt}
    (hq : q ∈ X) (hqe : ¬ IsExt X q) (h₁ : v₁ ∈ X) (h₂ : v₂ ∈ X) (h₃ : v₃ ∈ X)
    (h12 : v₁ ≠ v₂) (h13 : v₁ ≠ v₃) (h23 : v₂ ≠ v₃)
    (d₁ : dist q v₁ = Δ₂) (d₂ : dist q v₂ = Δ₂) (d₃ : dist q v₃ = Δ₂)
    (hr₁ : r₁ ∈ X) (hr₂ : r₂ ∈ X) (hr₃ : r₃ ∈ X) (hrq₁ : r₁ ≠ q) (hrq₂ : r₂ ≠ q) (hrq₃ : r₃ ≠ q)
    (e₁ : dist v₁ r₁ = Δ₂) (e₂ : dist v₂ r₂ = Δ₂) (e₃ : dist v₃ r₃ = Δ₂) : False := by
  have c := sqd_comm
  rcases hT.sqd_gap h₁ h₂ with p12 | p12 <;> rcases hT.sqd_gap h₁ h₃ with p13 | p13 <;>
    rcases hT.sqd_gap h₂ h₃ with p23 | p23
  · exact prop3_case3 hT hq hqe h₁ h₂ h₃ h12 h13 h23 d₁ d₂ d₃ p12 p23
  · -- only `v₂ v₃` far: middle `v₁`
    exact prop3_case3 hT hq hqe h₂ h₁ h₃ (Ne.symm h12) h23 h13 d₂ d₁ d₃ (by rw [c]; exact p12) p13
  · -- only `v₁ v₃` far: middle `v₂`
    exact prop3_case3 hT hq hqe h₁ h₂ h₃ h12 h13 h23 d₁ d₂ d₃ p12 p23
  · -- `v₁ v₃`, `v₂ v₃` far: apex `v₃`
    exact prop3_case2 hT hq hqe h₃ h₁ h₂ h12 d₃ d₁ d₂ (by rw [c]; exact p13) (by rw [c]; exact p23)
      p12 hr₃ hrq₃ e₃
  · -- only `v₁ v₂` far: middle `v₃`
    exact prop3_case3 hT hq hqe h₁ h₃ h₂ h13 h12 (Ne.symm h23) d₁ d₃ d₂ p13
      (by rw [c]; exact p23)
  · -- `v₁ v₂`, `v₂ v₃` far: apex `v₂`
    exact prop3_case2 hT hq hqe h₂ h₁ h₃ h13 d₂ d₁ d₃ (by rw [c]; exact p12) p23 p13 hr₂ hrq₂ e₂
  · -- `v₁ v₂`, `v₁ v₃` far: apex `v₁`
    exact prop3_case2 hT hq hqe h₁ h₂ h₃ h23 d₁ d₂ d₃ p12 p13 p23 hr₁ hrq₁ e₁
  · exact prop3_case1 hT hq hqe h₁ h₂ h₃ d₁ d₂ d₃ p12 p13 p23 hr₁ hr₂ hr₃ hrq₁ hrq₂ hrq₃ e₁ e₂ e₃

/-- **Prop 3**: every `q ∈ L₂ ∩ V(G′)` has `deg_{G′} q = 2`. -/
theorem deg_core_L2 {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) {q : Pt}
    (hq : q ∈ L2 X) (hK : q ∈ core (L1 X ∪ L2 X) Δ₂) :
    (nbr (core (L1 X ∪ L2 X) Δ₂) Δ₂ q).card = 2 := by
  set K := core (L1 X ∪ L2 X) Δ₂ with hKdef
  have hKX : K ⊆ X := (core_subset _ _).trans (union_subset (L1_subset X) (L2_subset X))
  have hqX : q ∈ X := L2_subset X hq
  have hqe : ¬ IsExt X q := fun h => disjoint_left.1 (disjoint_L1_L2 X) (mem_L1.2 h) hq
  have h2 : 2 ≤ (nbr K Δ₂ q).card := minDeg2_core _ _ q hK
  by_contra hne
  have h3 : 2 < (nbr K Δ₂ q).card := by omega
  obtain ⟨v₁, hv₁, v₂, hv₂, v₃, hv₃, h12, h13, h23⟩ := two_lt_card.1 h3
  have extra : ∀ v ∈ nbr K Δ₂ q, v ∈ X ∧ dist q v = Δ₂ ∧ ∃ r ∈ X, r ≠ q ∧ dist v r = Δ₂ := by
    intro v hv
    obtain ⟨hvK, hvd⟩ := mem_nbr.1 hv
    have hv2 : 2 ≤ (nbr K Δ₂ v).card := minDeg2_core _ _ v hvK
    obtain ⟨r, hr, hrq⟩ := exists_mem_ne (by omega : 1 < (nbr K Δ₂ v).card) q
    obtain ⟨hrK, hrd⟩ := mem_nbr.1 hr
    exact ⟨hKX hvK, hvd, r, hKX hrK, hrq, hrd⟩
  obtain ⟨x₁, d₁, r₁, hr₁, hrq₁, e₁⟩ := extra v₁ hv₁
  obtain ⟨x₂, d₂, r₂, hr₂, hrq₂, e₂⟩ := extra v₂ hv₂
  obtain ⟨x₃, d₃, r₃, hr₃, hrq₃, e₃⟩ := extra v₃ hv₃
  exact prop3_three hT hqX hqe x₁ x₂ x₃ h12 h13 h23 d₁ d₂ d₃ hr₁ hr₂ hr₃ hrq₁ hrq₂ hrq₃ e₁ e₂ e₃

/-! ## Degree at most 4 on `L₁′` (Lemma M, Lemma F) -/

/-- **Lemma F**: a `Δ₂`-neighbour `w` of an extreme point `p` with two further neighbours of `p`
strictly on each side of the line `pw` has `p` as its only `Δ₂`-neighbour.  Frame at `p` with
axis `w`; if `r` lies strictly on the `a`-side, reflect. -/
theorem lemmaF {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) {p w a₁ a₂ b₁ b₂ : Pt}
    (_hp : p ∈ X) (hw : w ∈ X) (ha₁ : a₁ ∈ X) (ha₂ : a₂ ∈ X) (hb₁ : b₁ ∈ X) (hb₂ : b₂ ∈ X)
    (dw : dist p w = Δ₂) (da₁ : dist p a₁ = Δ₂) (da₂ : dist p a₂ = Δ₂)
    (db₁ : dist p b₁ = Δ₂) (db₂ : dist p b₂ = Δ₂) (hna : a₁ ≠ a₂) (hnb : b₁ ≠ b₂)
    (oa₁ : orient p w a₁ < 0) (oa₂ : orient p w a₂ < 0)
    (ob₁ : 0 < orient p w b₁) (ob₂ : 0 < orient p w b₂)
    (o11 : 0 < orient p a₁ b₁) (o21 : 0 < orient p a₂ b₁)
    (o12 : 0 < orient p a₁ b₂) (_o22 : 0 < orient p a₂ b₂)
    {r : Pt} (hr : r ∈ X) (hwr : dist w r = Δ₂) : r = p := by
  by_contra hrp
  have hpos := hT.pos
  have hs0 : 0 < Δ₂ ^ 2 := by positivity
  have hne := ne_of_dist_snd hpos dw
  have hs : sqd p w = Δ₂ ^ 2 := (dist_eq_iff_sqd hpos.le).1 dw
  have hsp := sqd_pos_of_ne hne
  obtain ⟨m0, m1⟩ := frame_axis hne
  have N := frame_nsq hne hs
  have Nn := frame_norm' hne hs
  have unit : ∀ P, dist p P = Δ₂ → fx p w P ^ 2 + fy p w P ^ 2 = 1 := fun P hP => by
    rw [Nn, (dist_eq_iff_sqd hpos.le).1 hP, div_self hs0.ne']
  have gap : ∀ P ∈ X, ∀ Q ∈ X, (fx p w P - fx p w Q) ^ 2 + (fy p w P - fy p w Q) ^ 2 ≤ 1 ∨
      (fx p w P - fx p w Q) ^ 2 + (fy p w P - fy p w Q) ^ 2 = Δ ^ 2 / Δ₂ ^ 2 :=
    fun P hP Q hQ => by rw [N]; exact hT.ngap hP hQ
  have mx : ∀ P ∈ X, ∀ Q ∈ X,
      (fx p w P - fx p w Q) ^ 2 + (fy p w P - fy p w Q) ^ 2 ≤ Δ ^ 2 / Δ₂ ^ 2 :=
    fun P hP Q hQ => by rw [N]; exact hT.nle hP hQ
  have gw : ∀ P ∈ X, (fx p w P - 1) ^ 2 + fy p w P ^ 2 ≤ 1 ∨
      (fx p w P - 1) ^ 2 + fy p w P ^ 2 = Δ ^ 2 / Δ₂ ^ 2 := fun P hP => by
    have := gap P hP w hw; rw [m0, m1, sub_zero] at this; exact this
  have fyneg : ∀ P, orient p w P < 0 → fy p w P < 0 := fun P h => div_neg_of_neg_of_pos h hsp
  have fypos : ∀ P, 0 < orient p w P → 0 < fy p w P := fun P h => div_pos h hsp
  have crpos : ∀ P Q, 0 < orient p P Q → 0 < fx p w P * fy p w Q - fy p w P * fx p w Q :=
    fun P Q h => by rw [frame_cross hne]; exact div_pos h hsp
  have hr1 : (fx p w r - 1) ^ 2 + fy p w r ^ 2 = 1 := by
    have := N r w
    rw [m0, m1, sub_zero, sqd_comm, (dist_eq_iff_sqd hpos.le).1 hwr, div_self hs0.ne'] at this
    exact this
  have hr0 : 0 < fx p w r ^ 2 + fy p w r ^ 2 := by
    rw [Nn]; exact div_pos (sqd_pos_of_ne (Ne.symm hrp)) hs0
  have rf : ∀ u v : ℝ, (-u - -v) ^ 2 = (u - v) ^ 2 := fun u v => by ring
  rcases le_or_gt 0 (fy p w r) with hyr | hyr
  · exact lemmaF_real hT.one_lt (unit a₁ da₁) (unit a₂ da₂) (unit b₁ db₁) (fyneg a₁ oa₁)
      (fyneg a₂ oa₂) (fypos b₁ ob₁) (frame_inj hne hna) (crpos a₁ b₁ o11) (crpos a₂ b₁ o21) hr1
      hr0 hyr (gap r hr a₁ ha₁) (gap r hr a₂ ha₂) (gw a₁ ha₁) (gw a₂ ha₂) (mx a₁ ha₁ b₁ hb₁)
      (mx a₂ ha₂ b₁ hb₁)
  · -- reflect `y ↦ −y` and swap the roles of the two sides
    have cr : ∀ P Q, 0 < orient p P Q →
        0 < fx p w Q * -fy p w P - -fy p w Q * fx p w P := fun P Q h => by
      have := crpos P Q h
      have e : fx p w Q * -fy p w P - -fy p w Q * fx p w P =
          fx p w P * fy p w Q - fy p w P * fx p w Q := by ring
      rw [e]; exact this
    refine lemmaF_real (x₁ := fx p w b₁) (y₁ := -fy p w b₁) (x₂ := fx p w b₂)
      (y₂ := -fy p w b₂) (xb := fx p w a₁) (yb := -fy p w a₁) (xr := fx p w r) (yr := -fy p w r)
      hT.one_lt (by rw [neg_sq]; exact unit b₁ db₁) (by rw [neg_sq]; exact unit b₂ db₂)
      (by rw [neg_sq]; exact unit a₁ da₁) (by linarith [fypos b₁ ob₁])
      (by linarith [fypos b₂ ob₂]) (by linarith [fyneg a₁ oa₁])
      (fun h => frame_inj hne hnb ⟨h.1, neg_inj.1 h.2⟩) (cr a₁ b₁ o11) (cr a₁ b₂ o12)
      (by rw [neg_sq]; exact hr1) (by rw [neg_sq]; exact hr0) (by linarith)
      (by rw [rf]; exact gap r hr b₁ hb₁) (by rw [rf]; exact gap r hr b₂ hb₂)
      (by rw [neg_sq]; exact gw b₁ hb₁) (by rw [neg_sq]; exact gw b₂ hb₂)
      (by rw [rf]; exact mx b₁ hb₁ a₁ ha₁) (by rw [rf]; exact mx b₂ hb₂ a₁ ha₁)

/-- Real-number core of `eq_of_orient_zero`: equal lengths, zero cross product and the same open
half-plane force equal vectors. -/
theorem same_dir_real {u0 u1 w0 w1 α β : ℝ} (hd : u0 ^ 2 + u1 ^ 2 = w0 ^ 2 + w1 ^ 2)
    (ho : u0 * w1 - u1 * w0 = 0) (hx : 0 < -(α * u0 + β * u1)) (hy : 0 < -(α * w0 + β * w1)) :
    u0 = w0 ∧ u1 = w1 := by
  have hlag : (u0 * w0 + u1 * w1) ^ 2 = (u0 ^ 2 + u1 ^ 2) ^ 2 := by
    linear_combination (-(u0 * w1 - u1 * w0)) * ho - (u0 ^ 2 + u1 ^ 2) * hd
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hlag with h | h
  · have hz : (u0 - w0) ^ 2 + (u1 - w1) ^ 2 = 0 := by linear_combination -hd - 2 * h
    have h0 : u0 - w0 = 0 := by nlinarith [sq_nonneg (u0 - w0), sq_nonneg (u1 - w1)]
    have h1 : u1 - w1 = 0 := by nlinarith [sq_nonneg (u0 - w0), sq_nonneg (u1 - w1)]
    exact ⟨by linarith, by linarith⟩
  · have hz : (u0 + w0) ^ 2 + (u1 + w1) ^ 2 = 0 := by linear_combination -hd + 2 * h
    have h0 : u0 + w0 = 0 := by nlinarith [sq_nonneg (u0 + w0), sq_nonneg (u1 + w1)]
    have h1 : u1 + w1 = 0 := by nlinarith [sq_nonneg (u0 + w0), sq_nonneg (u1 + w1)]
    have : -(α * w0 + β * w1) = α * u0 + β * u1 := by linear_combination (-α) * h0 + (-β) * h1
    linarith

/-- Two points at equal distance from `p`, collinear with `p` and in the same open half-plane at
`p`, coincide. -/
theorem eq_of_orient_zero {p x y : Pt} {α β : ℝ} (hd : sqd p x = sqd p y) (ho : orient p x y = 0)
    (hx : 0 < -(α * (x 0 - p 0) + β * (x 1 - p 1)))
    (hy : 0 < -(α * (y 0 - p 0) + β * (y 1 - p 1))) : x = y := by
  simp only [sqd, orient] at hd ho
  obtain ⟨h0, h1⟩ := same_dir_real (u0 := x 0 - p 0) (u1 := x 1 - p 1) (w0 := y 0 - p 0)
    (w1 := y 1 - p 1) (by linear_combination hd) ho hx hy
  ext i; fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]; linarith
  · simp only [Fin.mk_one, Fin.isValue]; linarith

/-- Among five `Δ₂`-neighbours of an extreme point, the angular median has two of them strictly on
each side.  The slope `g x = (n × (x−p)) / (n·(x−p))` (`n` the inner normal of the supporting
half-plane) orders the neighbours by angle and is injective on them; sort five values with
`orderEmbOfFin`. -/
theorem exists_median {X : Finset Pt} {Δ₂ : ℝ} {p : Pt} (hp : IsExt X p) {S : Finset Pt}
    (hSX : S ⊆ X) (hS : ∀ x ∈ S, dist p x = Δ₂) (hpos : 0 < Δ₂) (h5 : 5 ≤ S.card) :
    ∃ w ∈ S, ∃ a₁ ∈ S, ∃ a₂ ∈ S, ∃ b₁ ∈ S, ∃ b₂ ∈ S, a₁ ≠ a₂ ∧ b₁ ≠ b₂ ∧
      orient p w a₁ < 0 ∧ orient p w a₂ < 0 ∧ 0 < orient p w b₁ ∧ 0 < orient p w b₂ ∧
      0 < orient p a₁ b₁ ∧ 0 < orient p a₂ b₁ ∧ 0 < orient p a₁ b₂ ∧ 0 < orient p a₂ b₂ := by
  classical
  obtain ⟨S', hS'S, hS'5⟩ := exists_subset_card_eq h5
  obtain ⟨-, α, β, hαβ⟩ := hp
  have hSp : ∀ x ∈ S', x ≠ p := fun x hx h => by
    have := hS x (hS'S hx); rw [h, dist_self] at this; linarith
  have hN : ∀ x ∈ S', 0 < -(α * (x 0 - p 0) + β * (x 1 - p 1)) := fun x hx => by
    linarith [hαβ x (hSX (hS'S hx)) (hSp x hx)]
  set g : Pt → ℝ := fun x =>
    (-α * (x 1 - p 1) + β * (x 0 - p 0)) / -(α * (x 0 - p 0) + β * (x 1 - p 1)) with hg
  have hn : 0 < α ^ 2 + β ^ 2 := by
    obtain ⟨x, hx⟩ : S'.Nonempty := card_pos.1 (by omega)
    by_contra h; push Not at h
    have ha : α = 0 := by nlinarith [sq_nonneg α, sq_nonneg β]
    have hb : β = 0 := by nlinarith [sq_nonneg α, sq_nonneg β]
    have := hN x hx; rw [ha, hb] at this; simp at this
  have anti : ∀ x y, orient p y x = -orient p x y := fun x y => by simp only [orient]; ring
  have key : ∀ x ∈ S', ∀ y ∈ S', (0 < orient p x y ↔ g x < g y) := by
    intro x hx y hy
    have hx' := hN x hx
    have hy' := hN y hy
    have e : g y - g x = orient p x y * (α ^ 2 + β ^ 2) /
        ((-(α * (x 0 - p 0) + β * (x 1 - p 1))) * (-(α * (y 0 - p 0) + β * (y 1 - p 1)))) := by
      simp only [hg]
      rw [div_sub_div _ _ hy'.ne' hx'.ne', div_eq_div_iff (mul_ne_zero hy'.ne' hx'.ne')
        (mul_ne_zero hx'.ne' hy'.ne')]
      simp only [orient]; ring
    rw [← sub_pos (a := g y) (b := g x), e]
    constructor
    · intro h; exact div_pos (mul_pos h hn) (mul_pos hx' hy')
    · intro h
      exact (mul_pos_iff_of_pos_right hn).1 ((div_pos_iff_of_pos_right (mul_pos hx' hy')).1 h)
  have inj : Set.InjOn g S' := by
    intro x hx y hy hxy
    have ho : orient p x y = 0 := by
      rcases lt_trichotomy (orient p x y) 0 with h | h | h
      · have h' : 0 < orient p y x := by rw [anti]; linarith
        have := (key y hy x hx).1 h'; rw [hxy] at this; exact absurd this (lt_irrefl _)
      · exact h
      · have := (key x hx y hy).1 h; rw [hxy] at this; exact absurd this (lt_irrefl _)
    have hd : sqd p x = sqd p y := by
      rw [(dist_eq_iff_sqd hpos.le).1 (hS x (hS'S hx)),
        (dist_eq_iff_sqd hpos.le).1 (hS y (hS'S hy))]
    exact eq_of_orient_zero hd ho (hN x hx) (hN y hy)
  set T := S'.image g with hT
  have hT5 : T.card = 5 := by rw [hT, card_image_of_injOn inj, hS'5]
  set emb := T.orderEmbOfFin hT5 with hemb
  have pre : ∀ i : Fin 5, ∃ x ∈ S', g x = emb i := fun i => mem_image.1 (orderEmbOfFin_mem T hT5 i)
  choose f hfS hfg using pre
  have ord : ∀ i j : Fin 5, i < j → 0 < orient p (f i) (f j) := fun i j hij =>
    (key _ (hfS i) _ (hfS j)).2 (by rw [hfg, hfg]; exact emb.strictMono hij)
  have fne : ∀ i j : Fin 5, i ≠ j → f i ≠ f j := fun i j hij h => by
    have := congrArg g h; rw [hfg, hfg] at this; exact hij (emb.injective this)
  have neg : ∀ i j : Fin 5, i < j → orient p (f j) (f i) < 0 := fun i j hij => by
    rw [anti]; linarith [ord i j hij]
  refine ⟨f 2, hS'S (hfS 2), f 0, hS'S (hfS 0), f 1, hS'S (hfS 1), f 3, hS'S (hfS 3), f 4,
    hS'S (hfS 4), fne 0 1 (by decide), fne 3 4 (by decide), neg 0 2 (by decide),
    neg 1 2 (by decide), ord 2 3 (by decide), ord 2 4 (by decide), ord 0 3 (by decide),
    ord 1 3 (by decide), ord 0 4 (by decide), ord 1 4 (by decide)⟩

/-- **Degree ≤ 4**: every `p ∈ L₁ ∩ V(G′)` has `deg_{G′} p ≤ 4`. -/
theorem deg_core_L1_le_four {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) {p : Pt}
    (hp : p ∈ L1 X) (_hK : p ∈ core (L1 X ∪ L2 X) Δ₂) :
    (nbr (core (L1 X ∪ L2 X) Δ₂) Δ₂ p).card ≤ 4 := by
  set K := core (L1 X ∪ L2 X) Δ₂ with hKdef
  have hKX : K ⊆ X := (core_subset _ _).trans (union_subset (L1_subset X) (L2_subset X))
  have hpE : IsExt X p := mem_L1.1 hp
  have hpX : p ∈ X := hpE.1
  by_contra h
  push Not at h
  have hsub : nbr K Δ₂ p ⊆ X := fun x hx => hKX (mem_nbr.1 hx).1
  obtain ⟨w, hw, a₁, ha₁, a₂, ha₂, b₁, hb₁, b₂, hb₂, hna, hnb, oa₁, oa₂, ob₁, ob₂, o11, o21, o12,
    o22⟩ := exists_median hpE hsub (fun x hx => (mem_nbr.1 hx).2) hT.pos (by omega)
  have hwK := (mem_nbr.1 hw).1
  have hall : ∀ r ∈ nbr K Δ₂ w, r = p := fun r hr =>
    lemmaF hT hpX (hsub hw) (hsub ha₁) (hsub ha₂) (hsub hb₁) (hsub hb₂) (mem_nbr.1 hw).2
      (mem_nbr.1 ha₁).2 (mem_nbr.1 ha₂).2 (mem_nbr.1 hb₁).2 (mem_nbr.1 hb₂).2 hna hnb oa₁ oa₂ ob₁
      ob₂ o11 o21 o12 o22 (hKX (mem_nbr.1 hr).1) (mem_nbr.1 hr).2
  have h1 : (nbr K Δ₂ w).card ≤ 1 :=
    card_le_one.2 fun a ha b hb => (hall a ha).trans (hall b hb).symm
  have h2 : 2 ≤ (nbr K Δ₂ w).card := minDeg2_core _ _ w hwK
  omega

/-! ## Theorem A and Corollary A1 -/

/-- **Theorem A** (doubled): `2μ(Δ₂) ≤ 2|L₁| + 2|L₂| + Σ_{p ∈ L₁′} (deg′ p − 2)`.
Here `L₁′ = L₁ ∩ V(G′)` and `deg′ p ≥ 2` on `V(G′)`, so the truncated subtraction is exact. -/
theorem theoremA {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) :
    2 * multS X Δ₂ ≤ 2 * (L1 X).card + 2 * (L2 X).card +
      ∑ p ∈ L1 X ∩ core (L1 X ∪ L2 X) Δ₂, ((nbr (core (L1 X ∪ L2 X) Δ₂) Δ₂ p).card - 2) := by
  set W := L1 X ∪ L2 X with hW
  set K := core W Δ₂ with hK
  have hd : Δ₂ ≠ 0 := hT.pos.ne'
  have hKW : K ⊆ W := core_subset W Δ₂
  have e1 : 2 * multS X Δ₂ = esum W Δ₂ := by rw [two_mul_multS hT.pos, esum_eq_esum_L12 hT]
  have e2 : esum W Δ₂ ≤ esum K Δ₂ + 2 * (W \ K).card := esum_le_core hd W
  have hsplit : K.filter (· ∈ L1 X) = L1 X ∩ K := by rw [filter_mem_eq_inter, inter_comm]
  have e3 : esum K Δ₂ = ∑ p ∈ L1 X ∩ K, (nbr K Δ₂ p).card +
      2 * (K.filter (· ∉ L1 X)).card := by
    unfold esum
    rw [← sum_filter_add_sum_filter_not K (· ∈ L1 X), hsplit]
    congr 1
    rw [sum_const_nat (m := 2) (fun v hv => ?_), mul_comm]
    obtain ⟨hvK, hv1⟩ := mem_filter.1 hv
    have hv2 : v ∈ L2 X := by
      rcases mem_union.1 (hKW hvK) with h | h
      · exact absurd h hv1
      · exact h
    exact deg_core_L2 hT hv2 hvK
  have e4 : ∑ p ∈ L1 X ∩ K, (nbr K Δ₂ p).card =
      ∑ p ∈ L1 X ∩ K, ((nbr K Δ₂ p).card - 2) + 2 * (L1 X ∩ K).card := by
    rw [mul_comm, ← smul_eq_mul, ← sum_const, ← sum_add_distrib]
    refine sum_congr rfl fun p hp => ?_
    have : 2 ≤ (nbr K Δ₂ p).card := minDeg2_core W Δ₂ p (mem_inter.1 hp).2
    omega
  have e5 : (W \ K).card + K.card = (L1 X).card + (L2 X).card := by
    rw [card_sdiff_add_card_eq_card hKW, hW, card_union_of_disjoint (disjoint_L1_L2 X)]
  have e6 : (L1 X ∩ K).card + (K.filter (· ∉ L1 X)).card = K.card := by
    rw [← hsplit]; exact card_filter_add_card_filter_not _
  omega

/-- **Corollary A1**: under (H3) (no point of `L₁` has `≥ 4` points at distance `Δ₂`),
`2μ(Δ₂) ≤ 3|L₁| + 2|L₂|`. -/
theorem corA1 {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂)
    (hH3 : ∀ p ∈ L1 X, (nbr X Δ₂ p).card ≤ 3) :
    2 * multS X Δ₂ ≤ 3 * (L1 X).card + 2 * (L2 X).card := by
  have hA := theoremA hT
  have hKX : core (L1 X ∪ L2 X) Δ₂ ⊆ X :=
    (core_subset _ _).trans (union_subset (L1_subset X) (L2_subset X))
  have hs : ∑ p ∈ L1 X ∩ core (L1 X ∪ L2 X) Δ₂,
      ((nbr (core (L1 X ∪ L2 X) Δ₂) Δ₂ p).card - 2) ≤ (L1 X).card := by
    calc _ ≤ ∑ p ∈ L1 X ∩ core (L1 X ∪ L2 X) Δ₂, 1 := sum_le_sum fun p hp => by
            have h1 := card_le_card (nbr_mono hKX Δ₂ p)
            have h2 := hH3 p (mem_inter.1 hp).1
            omega
      _ = (L1 X ∩ core (L1 X ∪ L2 X) Δ₂).card := by rw [card_eq_sum_ones]
      _ ≤ (L1 X).card := card_le_card inter_subset_left
  omega

/-- **Unconditional form**: `2μ(Δ₂) ≤ 2|L₁| + 2|L₂| + Σ_{p ∈ L₁} (min(h p, 4) − 2)`, where
`h p = #{x ∈ X : |px| = Δ₂}` and the truncated subtraction is `(·)⁺`. -/
theorem corA1_uncond {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) :
    2 * multS X Δ₂ ≤ 2 * (L1 X).card + 2 * (L2 X).card +
      ∑ p ∈ L1 X, (min (nbr X Δ₂ p).card 4 - 2) := by
  have hA := theoremA hT
  have hKX : core (L1 X ∪ L2 X) Δ₂ ⊆ X :=
    (core_subset _ _).trans (union_subset (L1_subset X) (L2_subset X))
  have hs : ∑ p ∈ L1 X ∩ core (L1 X ∪ L2 X) Δ₂,
      ((nbr (core (L1 X ∪ L2 X) Δ₂) Δ₂ p).card - 2) ≤
      ∑ p ∈ L1 X, (min (nbr X Δ₂ p).card 4 - 2) := by
    calc _ ≤ ∑ p ∈ L1 X ∩ core (L1 X ∪ L2 X) Δ₂, (min (nbr X Δ₂ p).card 4 - 2) :=
          sum_le_sum fun p hp => by
            have h1 := card_le_card (nbr_mono hKX Δ₂ p)
            have h2 := deg_core_L1_le_four hT (mem_inter.1 hp).1 (mem_inter.1 hp).2
            omega
      _ ≤ _ := sum_le_sum_of_subset inter_subset_left
  omega

/-- CDL's layer bound `μ(Δ₂) ≤ 2|L₁| + |L₂|` (CDL Theorem 1.3, first bound). -/
theorem cdl_layer_bound {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) :
    multS X Δ₂ ≤ 2 * (L1 X).card + (L2 X).card := by
  have h := corA1_uncond hT
  have hs : ∑ p ∈ L1 X, (min (nbr X Δ₂ p).card 4 - 2) ≤ 2 * (L1 X).card := by
    calc _ ≤ ∑ p ∈ L1 X, 2 := sum_le_sum fun p _ => by omega
      _ = 2 * (L1 X).card := by rw [sum_const, smul_eq_mul, mul_comm]
  omega

/-- Under (H3), `|L₁| ≤ 2 m₃` (with `m₃ = |X| − |L₁| − |L₂|`) implies `μ(Δ₂) ≤ |X|`. -/
theorem corA1_le_card {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂)
    (hH3 : ∀ p ∈ L1 X, (nbr X Δ₂ p).card ≤ 3)
    (h : (L1 X).card ≤ 2 * (X.card - (L1 X).card - (L2 X).card)) : multS X Δ₂ ≤ X.card := by
  have h1 := corA1 hT hH3
  have h2 : (L1 X).card + (L2 X).card ≤ X.card := by
    rw [← card_union_of_disjoint (disjoint_L1_L2 X)]
    exact card_le_card (union_subset (L1_subset X) (L2_subset X))
  omega

/-! ## Axiom check -/

#print axioms theoremA
#print axioms corA1
#print axioms corA1_uncond
#print axioms cdl_layer_bound
#print axioms corA1_le_card
#print axioms deg_core_L2
#print axioms deg_core_L1_le_four
#print axioms isExt_iff_notMem_convexHull
#print axioms exists_twoLargest

end Erdos132Layer
