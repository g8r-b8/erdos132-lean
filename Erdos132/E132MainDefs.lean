import Erdos132.E132ConvexFinset
import Erdos132.E132Ve87
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Erdős Problem 132, the `54/37` theorem — definitions and the counting reductions (§§1–4)

Skeleton of the Lean formalisation of `problems/132/WRITEUP_A2.md` (paper §§2–7):

> there is an absolute `C₀` such that every finite `X ⊆ ℝ²` satisfies
> `min {μ(Δ₂), μ(δ)} ≤ (54/37)·|X| + C₀`.

Files:
* `E132MainDefs.lean`    — distances, `S / R / D`, `K`, the direction field, edge classes,
  turning measure; cited results [Ve87], [HP]; reductions (VS), (E); LP Lemmas 4.1, 4.2;
  normalisation `δ = 1`; small cases; numeric constants.
* `E132MainLocal.lean`   — §3 (Lemmas 3.1–3.4, rung identity, T-edge/rung dichotomy, T1, T2)
  and §5 (lens lemma, bad-edge counts KK, DD, c1, c2).
* `E132MainRegions.lean` — §6 Region I, §7 Regions II/III (Lemma 7.1, R1, R2, R2-sym, R3,
  ownership/pairing, corner lemma).
* `E132MainDegen.lean`   — §8 degenerate regime `Δ > 1.94 Δ₂ ⇒ μ(Δ₂) ≤ n + 1`.
* `E132Main.lean`        — §9 assembly: `erdos132_main` (proved from the lemma statements).

Conventions (finite sets, unordered pairs of distinct points, as in `E132ConvexFinset`):
* `diam X` = largest distance, `dist2 X` = largest distance `< diam X`, `minDist X` = smallest
  distance; each is `0` when it does not exist, and `mult X 0 = 0`, so degenerate small sets
  need no side conditions.
* `mult X d` = number of unordered pairs of `X` at distance `d`.

Every lemma carries a docstring `TODO / What's missing / Acceptance / Depends on`.
Plan and difficulty estimates: `problems/132/lean/MAIN_PLAN.md`.
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS orient)
open scoped Classical
open Erdos132Layer (sqd dist_eq_iff_sqd dist_sq_eq_sqd dist_mem_distSetS pos_of_mem_distSetS)

namespace Erdos132Main

noncomputable section

/-! ## Distances of a finite set -/

/-- Number of unordered pairs of distinct points of `X` at distance `d` (`μ(d)`). -/
abbrev mult (X : Finset Pt) (d : ℝ) : ℕ := multS X d

/-- Diameter `Δ` (largest distance; `0` if `X` has no pair). -/
def diam (X : Finset Pt) : ℝ :=
  if h : (distSetS X).Nonempty then (distSetS X).max' h else 0

/-- Second-largest distance `Δ₂` (largest distance `< Δ`; `0` if there is none). -/
def dist2 (X : Finset Pt) : ℝ :=
  if h : ((distSetS X).erase (diam X)).Nonempty then ((distSetS X).erase (diam X)).max' h else 0

/-- Minimum distance `δ` (`0` if `X` has no pair). -/
def minDist (X : Finset Pt) : ℝ :=
  if h : (distSetS X).Nonempty then (distSetS X).min' h else 0

/-- The points of `X` other than `p` at distance `d` from `p`. -/
def partners (X : Finset Pt) (d : ℝ) (p : Pt) : Finset Pt :=
  X.filter (fun q => q ≠ p ∧ dist p q = d)

/-- `S`: points of `X` with a `Δ₂`-partner. -/
def Sset (X : Finset Pt) : Finset Pt := X.filter (fun p => (partners X (dist2 X) p).Nonempty)

/-- `R := X ∖ S`. -/
def Rset (X : Finset Pt) : Finset Pt := X \ Sset X

/-- `D`: endpoints of diametral pairs. -/
def Dset (X : Finset Pt) : Finset Pt := X.filter (fun p => (partners X (diam X) p).Nonempty)

/-- `Δ₂`-degree of `p`. -/
def deg2 (X : Finset Pt) (p : Pt) : ℕ := (partners X (dist2 X) p).card

/-- `e(S)`: number of `δ`-pairs inside `S`. -/
def eS (X : Finset Pt) : ℕ := mult (Sset X) (minDist X)

/-- The `δ`-pairs inside `S` (as unordered pairs). `(edges X).card = eS X`. -/
def edges (X : Finset Pt) : Finset (Sym2 Pt) :=
  (pairsS (Sset X)).filter (fun z => pairDist z = minDist X)

/-! ## Parameters and constants (δ normalised to 1) -/

/-- `β = 1/100`. -/
def beta : ℝ := 1 / 100

/-- `t := Δ − Δ₂`. -/
def tgap (X : Finset Pt) : ℝ := diam X - dist2 X

/-- `τ := t − (1 − t²)/(2Δ₂)`. -/
def tau (X : Finset Pt) : ℝ := tgap X - (1 - tgap X ^ 2) / (2 * dist2 X)

/-- Rung offset length `s := √(1 − τ²)`. -/
def sOff (X : Finset Pt) : ℝ := √(1 - tau X ^ 2)

/-- Packing threshold `N₀ = 1.51·10⁹` for the small cases. -/
def N₀ : ℝ := 151 * 10 ^ 7

/-- Uniform bound on the number of bad edges (paper: `< 1.83·10⁷`). -/
def cBad : ℝ := 2 * 10 ^ 7

/-- The additive constant of the main theorem: `C₀ ≥ 3N₀ + cBad + 100`. -/
def C₀ : ℝ := 5 * 10 ^ 9

/-- The **nondegenerate, normalised, large** regime of §§4–7: `δ = 1`, `Δ ≤ 1.94Δ₂`,
`Δ₂ ≥ 10⁴`, `n ≥ 4`. -/
structure Normal (X : Finset Pt) : Prop where
  four_le : 4 ≤ X.card
  minDist_eq : minDist X = 1
  nondeg : diam X ≤ 1.94 * dist2 X
  large : 10 ^ 4 ≤ dist2 X

/-! ## Geometry: ball polygon, direction field, normal cones, turning -/

/-- The ball polygon `K := ⋂_{w ∈ X} D(w, Δ₂)`. -/
def KBall (X : Finset Pt) : Set Pt := ⋂ w ∈ (X : Set Pt), Metric.closedBall w (dist2 X)

/-- `det(a, b)`: positive iff `b` is to the left of `a`. -/
def det2 (a b : Pt) : ℝ := a 0 * b 1 - a 1 * b 0

/-- Rotation by `+90°`. -/
def perp (a : Pt) : Pt := !₂[-a 1, a 0]

/-- Unoriented angle between two vectors. -/
def ang (a b : Pt) : ℝ := InnerProductGeometry.angle a b

/-- Unit vector of direction `θ`. -/
def dirVec (θ : ℝ) : Pt := !₂[Real.cos θ, Real.sin θ]

/-- Outward normal cone of `K` at `x`. -/
def normalCone (K : Set Pt) (x : Pt) : Set Pt := {ν | ∀ y ∈ K, inner ℝ (y - x) ν ≤ 0}

/-- **Turning** of a set `γ` of boundary points: the measure of the set of directions lying in the
normal cone at some point of `γ` (full cones at the endpoints included, §3). -/
def turning (K γ : Set Pt) : ℝ :=
  (MeasureTheory.volume
    {θ : ℝ | θ ∈ Set.Ico 0 (2 * π) ∧ ∃ x ∈ γ, dirVec θ ∈ normalCone K x}).toReal

/-- A **direction field** (§3): a chosen partner for each `p ∈ S` — a `Δ₂`-partner if `p ∉ D`,
a diametral partner if `p ∈ D`.  The inward normal is `u p := (partner p − p)/|partner p − p|`. -/
structure DirField (X : Finset Pt) where
  partner : Pt → Pt
  partner_mem : ∀ p ∈ Sset X, partner p ∈ X
  partner_K : ∀ p ∈ Sset X, p ∉ Dset X → dist p (partner p) = dist2 X
  partner_D : ∀ p ∈ Sset X, p ∈ Dset X → dist p (partner p) = diam X

/-- The unit inward normal `u_p`. -/
def DirField.u {X : Finset Pt} (F : DirField X) (p : Pt) : Pt :=
  (dist p (F.partner p))⁻¹ • (F.partner p - p)

/-! ## Edge classes -/

variable {X : Finset Pt}

/-- A `δ`-edge is **good** if `∠(u_p, u_q) ≤ β`. -/
def IsGood (F : DirField X) (z : Sym2 Pt) : Prop :=
  ∀ p q, z = s(p, q) → ang (F.u p) (F.u q) ≤ beta

/-- Good `δ`-edges inside `S`. -/
def good (X : Finset Pt) (F : DirField X) : Finset (Sym2 Pt) := (edges X).filter (IsGood F)

/-- Bad `δ`-edges inside `S`. -/
def bad (X : Finset Pt) (F : DirField X) : Finset (Sym2 Pt) :=
  (edges X).filter (fun z => ¬ IsGood F z)

/-- **T-edge**: `a = (q−p)·u_p ∈ (0, β)` and `b = (p−q)·u_q ∈ (0, β)`. -/
def IsTEdge (F : DirField X) (p q : Pt) : Prop :=
  0 < inner ℝ (q - p) (F.u p) ∧ inner ℝ (q - p) (F.u p) < beta ∧
  0 < inner ℝ (p - q) (F.u q) ∧ inner ℝ (p - q) (F.u q) < beta

/-- **Rung** `(v, z)`: `v ∈ S ∖ D`, `z ∈ S ∩ D`, `|vz| = 1`, and `z` is an exception for `v`
(`|z w_v| = Δ`). -/
def IsRung (F : DirField X) (v z : Pt) : Prop :=
  v ∈ Sset X ∧ v ∉ Dset X ∧ z ∈ Sset X ∧ z ∈ Dset X ∧ dist v z = 1 ∧
    dist z (F.partner v) = diam X

/-- `q` is the **right** (`σ = -1`) / **left** (`σ = 1`) T-neighbour of `p`. -/
def IsSideT (F : DirField X) (σ : ℝ) (p q : Pt) : Prop :=
  p ∈ Sset X ∧ q ∈ Sset X ∧ dist p q = 1 ∧ ang (F.u p) (F.u q) ≤ beta ∧ IsTEdge F p q ∧
    0 < σ * det2 (F.u p) (q - p)

/-- Good T-edges. -/
def tEdges (X : Finset Pt) (F : DirField X) : Finset (Sym2 Pt) :=
  (good X F).filter (fun z => ∀ p q, z = s(p, q) → IsTEdge F p q)

/-- Good rungs. -/
def rungs (X : Finset Pt) (F : DirField X) : Finset (Sym2 Pt) :=
  (good X F).filter (fun z => ∃ v w, z = s(v, w) ∧ IsRung F v w)

/-- Mixed T-edges (one end in `D`, one not). -/
def mixedT (X : Finset Pt) (F : DirField X) : Finset (Sym2 Pt) :=
  (tEdges X F).filter (fun z => ∃ v w, z = s(v, w) ∧ v ∉ Dset X ∧ w ∈ Dset X)

/-- Good edges that are not mixed T-edges (pure T-edges and rungs). -/
def goodPure (X : Finset Pt) (F : DirField X) : Finset (Sym2 Pt) := good X F \ mixedT X F

/-! ## Helper lemmas: pairs at a given distance

Helpers live in the sub-namespace `Erdos132Main.Defs` (opened below) so that they cannot clash
with helpers of the same name in the downstream files. -/

namespace Defs

/-- Membership of an unordered pair in `pairsS`. -/
theorem mk_mem_pairsS {Y : Finset Pt} {a b : Pt} :
    s(a, b) ∈ pairsS Y ↔ a ∈ Y ∧ b ∈ Y ∧ a ≠ b := by
  unfold pairsS
  rw [mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff, and_assoc]

/-- `pairDist` of an explicit pair. -/
theorem pairDist_mk (a b : Pt) : pairDist s(a, b) = dist a b := rfl

/-- `mult` as the card of an explicit filter. -/
theorem mult_eq_card (Y : Finset Pt) (d : ℝ) :
    mult Y d = ((pairsS Y).filter (fun z => pairDist z = d)).card := by
  unfold mult multS; convert rfl

/-- Membership in the pairs at distance `d`. -/
theorem mem_pairsAt {Y : Finset Pt} {d : ℝ} {a b : Pt} :
    s(a, b) ∈ (pairsS Y).filter (fun z => pairDist z = d) ↔
      a ∈ Y ∧ b ∈ Y ∧ a ≠ b ∧ dist a b = d := by
  rw [mem_filter, mk_mem_pairsS, pairDist_mk, and_assoc, and_assoc]

/-- `mult` is monotone in the set. -/
theorem mult_mono {Y Z : Finset Pt} (h : Y ⊆ Z) (d : ℝ) : mult Y d ≤ mult Z d := by
  rw [mult_eq_card, mult_eq_card]
  refine card_le_card fun z hz => ?_
  induction z using Sym2.ind with
  | h a b =>
    obtain ⟨ha, hb, hab, hd⟩ := mem_pairsAt.1 hz
    exact mem_pairsAt.2 ⟨h ha, h hb, hab, hd⟩

/-- Membership in `partners`. -/
theorem mem_partners {Y : Finset Pt} {d : ℝ} {p q : Pt} :
    q ∈ partners Y d p ↔ q ∈ Y ∧ q ≠ p ∧ dist p q = d := by
  unfold partners; rw [mem_filter]

/-- Pairs of `Z` at distance `d` are those inside `Y` plus those meeting `Z \ Y`. -/
theorem mult_le_add_sum (Y Z : Finset Pt) (d : ℝ) :
    mult Z d ≤ mult Y d + ∑ x ∈ Z \ Y, (partners Z d x).card := by
  rw [mult_eq_card, mult_eq_card]
  have hsub : (pairsS Z).filter (fun z => pairDist z = d) ⊆
      (pairsS Y).filter (fun z => pairDist z = d) ∪
        (Z \ Y).biUnion (fun x => (partners Z d x).image (fun q => s(x, q))) := by
    intro z hz
    induction z using Sym2.ind with
    | h a b =>
      obtain ⟨ha, hb, hab, hd⟩ := mem_pairsAt.1 hz
      rw [mem_union, mem_biUnion]
      by_cases haY : a ∈ Y
      · by_cases hbY : b ∈ Y
        · exact Or.inl (mem_pairsAt.2 ⟨haY, hbY, hab, hd⟩)
        · refine Or.inr ⟨b, mem_sdiff.2 ⟨hb, hbY⟩, mem_image.2 ⟨a, ?_, Sym2.eq_swap⟩⟩
          exact mem_partners.2 ⟨ha, hab, by rw [dist_comm]; exact hd⟩
      · refine Or.inr ⟨a, mem_sdiff.2 ⟨ha, haY⟩, mem_image.2 ⟨b, ?_, rfl⟩⟩
        exact mem_partners.2 ⟨hb, Ne.symm hab, hd⟩
  refine (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_left ?_ _))
  exact card_biUnion_le.trans (sum_le_sum fun x _ => card_image_le)

/-- `δ ≤` every distance of distinct points. -/
theorem minDist_le_dist {X : Finset Pt} {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) :
    minDist X ≤ dist x y := by
  have hm := dist_mem_distSetS hx hy hxy
  have hne : (distSetS X).Nonempty := ⟨_, hm⟩
  rw [minDist, dite_eq_left hne]
  exact min'_le _ _ hm

/-- Two points on a circle of radius `δ` whose angles differ by less than `π/3` are at distance
`< δ`. -/
theorem sqd_lt_of_arg {δ a b : ℝ} (hδ : 0 < δ) (hab : |a - b| < π / 3) :
    (δ * cos a - δ * cos b) ^ 2 + (δ * sin a - δ * sin b) ^ 2 < δ ^ 2 := by
  have hc : 1 / 2 < cos (a - b) := by
    rw [← Real.cos_abs, ← Real.cos_pi_div_three]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hab
  have e : (δ * cos a - δ * cos b) ^ 2 + (δ * sin a - δ * sin b) ^ 2 =
      δ ^ 2 * (2 - 2 * cos (a - b)) := by
    rw [Real.cos_sub]
    linear_combination δ ^ 2 * (Real.sin_sq_add_cos_sq a) + δ ^ 2 * (Real.sin_sq_add_cos_sq b)
  rw [e]
  have : 0 < δ ^ 2 := by positivity
  nlinarith

/-- No pair of distinct points is at distance `0`. -/
theorem mult_zero (Y : Finset Pt) : mult Y 0 = 0 := by
  rw [mult_eq_card, card_eq_zero, filter_eq_empty_iff]
  intro z hz h0
  induction z using Sym2.ind with
  | h a b =>
    obtain ⟨-, -, hab⟩ := mk_mem_pairsS.1 hz
    rw [pairDist_mk] at h0
    exact hab (dist_eq_zero.1 h0)

/-- `δ ≥ 0`. -/
theorem minDist_nonneg (X : Finset Pt) : 0 ≤ minDist X := by
  unfold minDist
  split_ifs with h
  · exact (pos_of_mem_distSetS (min'_mem _ h)).le
  · exact le_rfl

open Erdos132Layer in
/-- Hopf–Pannwitz core step (frame at `q`, axis the middle neighbour `m`): if `x, y` are
`D`-neighbours of `q` on opposite sides of the line `qm`, then no `r ≠ q` with `|rm| = D` lies
within `D` of `q`, `x` and `y`. -/
theorem hp_core {q m x y r : Pt} {D : ℝ} (hD : 0 < D)
    (hm : sqd q m = D ^ 2) (hx : sqd q x = D ^ 2) (hy : sqd q y = D ^ 2)
    (hopp : orient q m x * orient q m y < 0)
    (hrm : sqd r m = D ^ 2) (hrx : sqd r x ≤ D ^ 2) (hry : sqd r y ≤ D ^ 2) (hr : r ≠ q) :
    False := by
  have hs0 : 0 < D ^ 2 := by positivity
  have hne : q ≠ m := by
    rintro rfl; have : sqd q q = 0 := by simp [sqd]
    rw [this] at hm; linarith
  obtain ⟨m0, m1⟩ := frame_axis hne
  have N := frame_nsq hne hm
  have Nn := frame_norm' hne hm
  have ux : fx q m x ^ 2 + fy q m x ^ 2 = 1 := by rw [Nn, hx, div_self hs0.ne']
  have uy : fx q m y ^ 2 + fy q m y ^ 2 = 1 := by rw [Nn, hy, div_self hs0.ne']
  have ur : (fx q m r - 1) ^ 2 + fy q m r ^ 2 = 1 := by
    have := N r m; rw [m0, m1, sub_zero] at this; rw [this, hrm, div_self hs0.ne']
  have r0 : 0 < fx q m r ^ 2 + fy q m r ^ 2 := by
    rw [Nn]; exact div_pos (sqd_pos_of_ne (Ne.symm hr)) hs0
  have cx : (fx q m r - fx q m x) ^ 2 + (fy q m r - fy q m x) ^ 2 ≤ 1 := by
    rw [N]; exact div_le_one_of_le₀ hrx hs0.le
  have cy : (fx q m r - fx q m y) ^ 2 + (fy q m r - fy q m y) ^ 2 ≤ 1 := by
    rw [N]; exact div_le_one_of_le₀ hry hs0.le
  have hopp' : fy q m x * fy q m y < 0 := by
    unfold fy; rw [div_mul_div_comm]
    exact div_neg_of_neg_of_pos hopp (by have := sqd_pos_of_ne hne; positivity)
  have rf : ∀ u v : ℝ, (-u - -v) ^ 2 = (u - v) ^ 2 := fun u v => by ring
  have rf0 : ∀ u : ℝ, (-u) ^ 2 = u ^ 2 := fun u => by ring
  -- `M a` : lemma M for a point `a` below the axis and `r` not below
  have M : ∀ {xa ya xr yr : ℝ}, xa ^ 2 + ya ^ 2 = 1 → ya < 0 → (xr - 1) ^ 2 + yr ^ 2 = 1 →
      0 ≤ yr → 0 < xr ^ 2 + yr ^ 2 → (xr - xa) ^ 2 + (yr - ya) ^ 2 ≤ 1 → False :=
    fun ha hya hr hyr hr0 hc => by linarith [lemmaM_real ha hya hr hyr hr0]
  rcases lt_or_gt_of_ne (show fy q m x ≠ 0 by rintro h; rw [h, zero_mul] at hopp'; linarith)
    with hxn | hxp
  · have hyp : 0 < fy q m y := by
      by_contra hh; push Not at hh; linarith [mul_nonneg_of_nonpos_of_nonpos hxn.le hh]
    rcases le_or_gt 0 (fy q m r) with hr' | hr'
    · exact M ux hxn ur hr' r0 cx
    · refine M (xa := fx q m y) (ya := -fy q m y) (xr := fx q m r) (yr := -fy q m r) (by rw [rf0]; exact uy) (by linarith)
        (by rw [rf0]; exact ur) (by linarith) (by rw [rf0]; exact r0) (by rw [rf]; exact cy)
  · have hyn : fy q m y < 0 := by
      by_contra hh; push Not at hh; linarith [mul_nonneg hxp.le hh]
    rcases le_or_gt 0 (fy q m r) with hr' | hr'
    · exact M uy hyn ur hr' r0 cy
    · refine M (xa := fx q m x) (ya := -fy q m x) (xr := fx q m r) (yr := -fy q m r) (by rw [rf0]; exact ux) (by linarith)
        (by rw [rf0]; exact ur) (by linarith) (by rw [rf0]; exact r0) (by rw [rf]; exact cx)

open Erdos132Layer in
/-- Among three distinct points at distance `D` from `q`, pairwise within `D`, one separates the
other two (as seen from `q`). -/
theorem select_middle {q v₁ v₂ v₃ : Pt} {D : ℝ} (hD : 0 < D)
    (h12 : v₁ ≠ v₂) (h13 : v₁ ≠ v₃) (h23 : v₂ ≠ v₃)
    (d₁ : sqd q v₁ = D ^ 2) (d₂ : sqd q v₂ = D ^ 2) (d₃ : sqd q v₃ = D ^ 2)
    (s12 : sqd v₁ v₂ ≤ D ^ 2) (s23 : sqd v₂ v₃ ≤ D ^ 2) :
    orient q v₂ v₁ * orient q v₂ v₃ < 0 ∨ orient q v₁ v₂ * orient q v₁ v₃ < 0 ∨
      orient q v₃ v₂ * orient q v₃ v₁ < 0 := by
  have hs0 : 0 < D ^ 2 := by positivity
  have hne : q ≠ v₂ := by
    rintro rfl; have : sqd q q = 0 := by simp [sqd]
    rw [this] at d₂; linarith
  obtain ⟨m0, m1⟩ := frame_axis hne
  have N := frame_nsq hne d₂
  have Nn := frame_norm' hne d₂
  have unit : ∀ P, sqd q P = D ^ 2 → fx q v₂ P ^ 2 + fy q v₂ P ^ 2 = 1 := fun P hP => by
    rw [Nn, hP, div_self hs0.ne']
  have close : ∀ P, sqd P v₂ ≤ D ^ 2 → (fx q v₂ P - 1) ^ 2 + fy q v₂ P ^ 2 ≤ 1 := fun P hP => by
    have := N P v₂
    rw [m0, m1, sub_zero] at this
    rw [this]; exact div_le_one_of_le₀ hP hs0.le
  have ha := unit v₁ d₁
  have hc := unit v₃ d₃
  have hab := close v₁ s12
  have hcb := close v₃ (by rw [sqd_comm]; exact s23)
  have ynz : ∀ P, P ≠ v₂ → fx q v₂ P ^ 2 + fy q v₂ P ^ 2 = 1 →
      (fx q v₂ P - 1) ^ 2 + fy q v₂ P ^ 2 ≤ 1 → fy q v₂ P ≠ 0 := by
    intro P hP hu hcl hy
    rw [hy] at hu
    have hx : fx q v₂ P = 1 := by nlinarith
    have := N P v₂
    rw [m0, m1, hx, hy, sub_self, sub_self] at this
    have h0 : sqd P v₂ = 0 :=
      (div_eq_zero_iff.1 (by rw [← this]; norm_num)).resolve_right hs0.ne'
    exact (sqd_pos_of_ne hP).ne' h0
  have ya := ynz v₁ h12 ha hab
  have yc := ynz v₃ (Ne.symm h23) hc hcb
  have O : ∀ P Q, orient q P Q = (fx q v₂ P * fy q v₂ Q - fy q v₂ P * fx q v₂ Q) * D ^ 2 :=
    fun P Q => by rw [frame_cross hne, d₂, div_mul_cancel₀ _ hs0.ne']
  have hpos := mul_pos hs0 hs0
  rcases lt_trichotomy (fy q v₂ v₁ * fy q v₂ v₃) 0 with hopp | h0 | hsame
  · left
    rw [O, O, m0, m1]
    have e : (1 * fy q v₂ v₁ - 0 * fx q v₂ v₁) * D ^ 2 * ((1 * fy q v₂ v₃ - 0 * fx q v₂ v₃) *
        D ^ 2) = (fy q v₂ v₁ * fy q v₂ v₃) * (D ^ 2 * D ^ 2) := by ring
    rw [e]; exact mul_neg_of_neg_of_pos hopp hpos
  · exact absurd h0 (mul_ne_zero ya yc)
  · have hne13 : ¬ (fx q v₂ v₁ = fx q v₂ v₃ ∧ fy q v₂ v₁ = fy q v₂ v₃) := by
      rintro ⟨hx, hy⟩
      have := N v₁ v₃
      rw [hx, hy, sub_self, sub_self] at this
      have h0 : sqd v₁ v₃ = 0 :=
        (div_eq_zero_iff.1 (by rw [← this]; norm_num)).resolve_right hs0.ne'
      exact (sqd_pos_of_ne h13).ne' h0
    obtain ⟨-, hmid⟩ := case3_select_real ha hc hab hcb hsame hne13
    rcases hmid with hmid | hmid
    · right; left
      rw [O, O, m0, m1]
      have e : (fx q v₂ v₁ * 0 - fy q v₂ v₁ * 1) * D ^ 2 * ((fx q v₂ v₁ * fy q v₂ v₃ -
          fy q v₂ v₁ * fx q v₂ v₃) * D ^ 2) = ((-fy q v₂ v₁) * (fx q v₂ v₁ * fy q v₂ v₃ -
          fy q v₂ v₁ * fx q v₂ v₃)) * (D ^ 2 * D ^ 2) := by ring
      rw [e]; exact mul_neg_of_neg_of_pos hmid hpos
    · right; right
      rw [O, O, m0, m1]
      have e : (fx q v₂ v₃ * 0 - fy q v₂ v₃ * 1) * D ^ 2 * ((fx q v₂ v₃ * fy q v₂ v₁ -
          fy q v₂ v₃ * fx q v₂ v₁) * D ^ 2) = ((-fy q v₂ v₃) * (fx q v₂ v₃ * fy q v₂ v₁ -
          fy q v₂ v₃ * fx q v₂ v₁)) * (D ^ 2 * D ^ 2) := by ring
      rw [e]; exact mul_neg_of_neg_of_pos hmid hpos

/-- `Δ ≥ 0`. -/
theorem diam_nonneg (Y : Finset Pt) : 0 ≤ diam Y := by
  unfold diam
  split_ifs with h
  · exact (pos_of_mem_distSetS (max'_mem _ h)).le
  · exact le_rfl

/-- Every distance is `≤ Δ`. -/
theorem le_diam {Y : Finset Pt} {d : ℝ} (hd : d ∈ distSetS Y) : d ≤ diam Y := by
  have hne : (distSetS Y).Nonempty := ⟨_, hd⟩
  rw [diam, dite_eq_left hne]; exact le_max' _ _ hd

/-- Distances of points of `Y` are `≤ Δ`. -/
theorem dist_le_diam {Y : Finset Pt} {x y : Pt} (hx : x ∈ Y) (hy : y ∈ Y) : dist x y ≤ diam Y := by
  by_cases h : x = y
  · rw [h, dist_self]; exact diam_nonneg Y
  · exact le_diam (dist_mem_distSetS hx hy h)

/-- Squared version of `dist_le_diam`. -/
theorem sqd_le_diam {Y : Finset Pt} {x y : Pt} (hx : x ∈ Y) (hy : y ∈ Y) :
    sqd x y ≤ diam Y ^ 2 := by
  rw [← dist_sq_eq_sqd]; exact pow_le_pow_left₀ dist_nonneg (dist_le_diam hx hy) 2

open Erdos132Layer in
/-- In the 2-core of the diameter graph every vertex has degree `≤ 2`. -/
theorem core_deg_le_two {Y : Finset Pt} (hD : 0 < diam Y) {v : Pt}
    (hv : v ∈ core Y (diam Y)) : (nbr (core Y (diam Y)) (diam Y) v).card ≤ 2 := by
  set D := diam Y
  set C := core Y D
  have hCY : C ⊆ Y := core_subset Y D
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := two_lt_card.1 hcon
  have hmem : ∀ x ∈ nbr C D v, x ∈ Y ∧ sqd v x = D ^ 2 := fun x hx => by
    obtain ⟨hxC, hd⟩ := mem_nbr.1 hx
    exact ⟨hCY hxC, (dist_eq_iff_sqd hD.le).1 hd⟩
  obtain ⟨haY, da⟩ := hmem a ha
  obtain ⟨hbY, db⟩ := hmem b hb
  obtain ⟨hcY, dc⟩ := hmem c hc
  have hvY : v ∈ Y := hCY hv
  -- the middle neighbour `m` has a second core neighbour `r ≠ v`
  have finish : ∀ m x y, m ∈ nbr C D v → x ∈ Y → y ∈ Y → sqd v m = D ^ 2 → sqd v x = D ^ 2 →
      sqd v y = D ^ 2 → orient v m x * orient v m y < 0 → False := by
    intro m x y hm hx hy dm dx dy hopp
    have hmC : m ∈ C := (mem_nbr.1 hm).1
    have h2 : 2 ≤ (nbr C D m).card := minDeg2_core Y D m hmC
    obtain ⟨r, hr, hrv⟩ := exists_mem_ne (by omega : 1 < (nbr C D m).card) v
    obtain ⟨hrC, hdr⟩ := mem_nbr.1 hr
    have hrY := hCY hrC
    have hrm : sqd r m = D ^ 2 := by
      rw [sqd_comm]; exact (dist_eq_iff_sqd hD.le).1 hdr
    exact hp_core hD dm dx dy hopp hrm (sqd_le_diam hrY hx) (sqd_le_diam hrY hy) hrv
  rcases select_middle hD hab hac hbc da db dc (sqd_le_diam haY hbY) (sqd_le_diam hbY hcY)
    with h | h | h
  · exact finish b a c hb haY hcY db da dc h
  · exact finish a b c ha hbY hcY da db dc h
  · exact finish c b a hc hbY haY dc db da h

/-- Elements of `distSetS` are distances of distinct points. -/
theorem mem_distSetS {Y : Finset Pt} {d : ℝ} (hd : d ∈ distSetS Y) :
    ∃ x ∈ Y, ∃ y ∈ Y, x ≠ y ∧ dist x y = d := by
  unfold distSetS at hd
  obtain ⟨z, hz, rfl⟩ := mem_image.1 hd
  induction z using Sym2.ind with
  | h a b =>
    obtain ⟨ha, hb, hab⟩ := mk_mem_pairsS.1 hz
    exact ⟨a, ha, b, hb, hab, rfl⟩

/-- `distSetS` is monotone. -/
theorem distSetS_mono {Y Z : Finset Pt} (h : Y ⊆ Z) {d : ℝ} (hd : d ∈ distSetS Y) :
    d ∈ distSetS Z := by
  obtain ⟨x, hx, y, hy, hxy, rfl⟩ := mem_distSetS hd
  exact dist_mem_distSetS (h hx) (h hy) hxy

/-- Scaling multiplies distances. -/
theorem dist_smul_pos {c : ℝ} (hc : 0 < c) (x y : Pt) : dist (c • x) (c • y) = c * dist x y := by
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hc]

/-- Distances of a dilate. -/
theorem distSetS_smul {c : ℝ} (hc : 0 < c) (X : Finset Pt) :
    distSetS (X.image (c • ·)) = (distSetS X).image (c * ·) := by
  ext d
  rw [mem_image]
  constructor
  · intro hd
    obtain ⟨x', hx', y', hy', hxy, rfl⟩ := mem_distSetS hd
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hx'
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hy'
    refine ⟨dist x y, dist_mem_distSetS hx hy fun h => hxy (by rw [h]), ?_⟩
    rw [dist_smul_pos hc]
  · rintro ⟨e, he, rfl⟩
    obtain ⟨x, hx, y, hy, hxy, rfl⟩ := mem_distSetS he
    rw [← dist_smul_pos hc]
    refine dist_mem_distSetS (mem_image_of_mem _ hx) (mem_image_of_mem _ hy) fun h => hxy ?_
    exact smul_right_injective Pt hc.ne' h

/-- Multiplicities of a dilate. -/
theorem mult_smul {c : ℝ} (hc : 0 < c) (X : Finset Pt) (d : ℝ) :
    mult (X.image (c • ·)) (c * d) = mult X d := by
  have hinj : Function.Injective (fun x : Pt => c • x) := smul_right_injective Pt hc.ne'
  rw [mult_eq_card, mult_eq_card]
  have e : (pairsS (X.image (c • ·))).filter (fun z => pairDist z = c * d) =
      ((pairsS X).filter (fun z => pairDist z = d)).image (Sym2.map (c • ·)) := by
    ext z
    rw [mem_image]
    constructor
    · intro hz
      induction z using Sym2.ind with
      | h a' b' =>
        obtain ⟨ha', hb', hab, hd⟩ := mem_pairsAt.1 hz
        obtain ⟨a, ha, rfl⟩ := mem_image.1 ha'
        obtain ⟨b, hb, rfl⟩ := mem_image.1 hb'
        refine ⟨s(a, b), mem_pairsAt.2 ⟨ha, hb, fun h => hab (by rw [h]), ?_⟩, rfl⟩
        rw [dist_smul_pos hc] at hd
        exact mul_left_cancel₀ hc.ne' hd
    · rintro ⟨w, hw, rfl⟩
      induction w using Sym2.ind with
      | h a b =>
        obtain ⟨ha, hb, hab, hd⟩ := mem_pairsAt.1 hw
        rw [Sym2.map_mk]
        refine mem_pairsAt.2 ⟨mem_image_of_mem _ ha, mem_image_of_mem _ hb,
          fun h => hab (hinj h), ?_⟩
        rw [dist_smul_pos hc, hd]
  rw [e, card_image_of_injective _ (Sym2.map.injective hinj)]

/-- `Δ` of a dilate. -/
theorem diam_smul {c : ℝ} (hc : 0 < c) (X : Finset Pt) :
    diam (X.image (c • ·)) = c * diam X := by
  have hmono : Monotone (fun t : ℝ => c * t) := fun a b h => mul_le_mul_of_nonneg_left h hc.le
  unfold diam
  rw [distSetS_smul hc]
  by_cases h : (distSetS X).Nonempty
  · rw [dite_eq_left (h.image _), dite_eq_left h, max'_image hmono]
  · rw [dite_eq_right (by rwa [image_nonempty]), dite_eq_right h, mul_zero]

/-- `Δ₂` of a dilate. -/
theorem dist2_smul {c : ℝ} (hc : 0 < c) (X : Finset Pt) :
    dist2 (X.image (c • ·)) = c * dist2 X := by
  have hmono : Monotone (fun t : ℝ => c * t) := fun a b h => mul_le_mul_of_nonneg_left h hc.le
  have hinj : Function.Injective (fun t : ℝ => c * t) := fun a b h => mul_left_cancel₀ hc.ne' h
  unfold dist2
  rw [diam_smul hc, distSetS_smul hc]
  have e : ((distSetS X).image (c * ·)).erase (c * diam X) =
      ((distSetS X).erase (diam X)).image (c * ·) := (image_erase hinj _ _).symm
  rw [e]
  by_cases h : ((distSetS X).erase (diam X)).Nonempty
  · rw [dite_eq_left (h.image _), dite_eq_left h, max'_image hmono]
  · rw [dite_eq_right (by rwa [image_nonempty]), dite_eq_right h, mul_zero]

/-- `δ` of a dilate. -/
theorem minDist_smul {c : ℝ} (hc : 0 < c) (X : Finset Pt) :
    minDist (X.image (c • ·)) = c * minDist X := by
  have hmono : Monotone (fun t : ℝ => c * t) := fun a b h => mul_le_mul_of_nonneg_left h hc.le
  unfold minDist
  rw [distSetS_smul hc]
  by_cases h : (distSetS X).Nonempty
  · rw [dite_eq_left (h.image _), dite_eq_left h, min'_image hmono]
  · rw [dite_eq_right (by rwa [image_nonempty]), dite_eq_right h, mul_zero]

/-- Coordinate differences are bounded by the distance (squared form). -/
theorem coord_sq_le (x y : Pt) :
    (x 0 - y 0) ^ 2 ≤ dist x y ^ 2 ∧ (x 1 - y 1) ^ 2 ≤ dist x y ^ 2 := by
  rw [dist_sq_eq_sqd, sqd]
  exact ⟨by nlinarith [sq_nonneg (x 1 - y 1)], by nlinarith [sq_nonneg (x 0 - y 0)]⟩

/-- Grid-cell index of a coordinate value (cells of side `7/10`). -/
theorem floor_cell_lt {t D : ℝ} (ht : 0 ≤ t) (htD : t ≤ D) (hD : D < 19400) :
    ⌊t / (7 / 10)⌋₊ < 27715 := by
  rw [Nat.floor_lt (by positivity)]
  rw [div_lt_iff₀ (by norm_num)]; push_cast; linarith

/-- Two values in the same grid cell differ by less than `7/10`. -/
theorem close_of_floor_eq {t t' : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t')
    (h : ⌊t / (7 / 10)⌋₊ = ⌊t' / (7 / 10)⌋₊) : (t - t') ^ 2 < (7 / 10) ^ 2 := by
  have a1 := Nat.floor_le (show 0 ≤ t / (7 / 10) by positivity)
  have a2 := Nat.lt_floor_add_one (t / (7 / 10))
  have b1 := Nat.floor_le (show 0 ≤ t' / (7 / 10) by positivity)
  have b2 := Nat.lt_floor_add_one (t' / (7 / 10))
  have h' : (⌊t / (7 / 10)⌋₊ : ℝ) = ⌊t' / (7 / 10)⌋₊ := by exact_mod_cast h
  have h1 : t / (7 / 10) - t' / (7 / 10) < 1 := by linarith
  have h2 : t' / (7 / 10) - t / (7 / 10) < 1 := by linarith
  have e : t - t' = (7 / 10) * (t / (7 / 10) - t' / (7 / 10)) := by field_simp
  rw [e, mul_pow]
  have : (t / (7 / 10) - t' / (7 / 10)) ^ 2 < 1 := by nlinarith
  nlinarith

end Defs

open Defs

/-! ## Cited results -/

/-- **[Ve87]** Vesztergombi, *On large distances in planar sets*, Discrete Math. 67 (1987)
191–198: in every `m`-point planar set the second-largest distance occurs at most `3m/2` times.

Formerly a cited black box; now **proved** in `Erdos132.E132Ve87` (2-core argument on the
`Δ₂`-graph of `L₁ ∪ L₂`), whose `Erdos132Ve87.vesztergombi87` has this exact statement up to
unfolding its local copies of `diam`/`dist2`.
Acceptance: no `sorry` (done). -/
theorem vesztergombi87 (Y : Finset Pt) : (mult Y (dist2 Y) : ℝ) ≤ 3 / 2 * Y.card :=
  Erdos132Ve87.vesztergombi87 Y

open Erdos132Layer in
/-- **[HP]** Hopf–Pannwitz (1934): in every `m`-point planar set the diameter occurs at most
`m` times.

TODO: none — proved (Phase 2).
Proof: `2μ(Δ) = esum ≤ esum(2-core) + 2|Y ∖ core|` (`E132Layer.esum_le_core`); in the 2-core
every vertex has degree `≤ 2`: of three `Δ`-neighbours one is the middle one (`select_middle`),
and its second core neighbour would violate lemma M (`hp_core`).
Acceptance: no `sorry`.
Depends on: nothing (planar geometry only). Difficulty L. -/
theorem hopf_pannwitz (Y : Finset Pt) : mult Y (diam Y) ≤ Y.card := by
  rcases (diam_nonneg Y).eq_or_lt with h0 | hD
  · rw [← h0, mult_zero]; exact Nat.zero_le _
  set D := diam Y
  set C := core Y D
  have h2 := two_mul_multS hD Y
  have h3 : esum Y D ≤ esum C D + 2 * (Y \ C).card := esum_le_core hD.ne' Y
  have h4 : esum C D ≤ 2 * C.card := by
    unfold esum
    calc ∑ v ∈ C, (nbr C D v).card ≤ ∑ _v ∈ C, 2 := sum_le_sum fun v hv => core_deg_le_two hD hv
      _ = 2 * C.card := by rw [sum_const, smul_eq_mul, mul_comm]
  have h5 : (Y \ C).card + C.card = Y.card := card_sdiff_add_card_eq_card (core_subset Y D)
  have e : mult Y D = multS Y D := rfl
  omega

/-! ## Elementary counting -/

/-- `|S| + |R| = n`.

TODO: none — proved (Phase 2).
What's missing: nothing mathematical.
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem card_S_add_R (X : Finset Pt) : (Sset X).card + (Rset X).card = X.card := by
  rw [Rset, add_comm]; exact card_sdiff_add_card_eq_card (filter_subset _ _)

/-- `e(S)` is the number of `edges`.

TODO: none — proved (Phase 2).
What's missing: nothing.
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem card_edges (X : Finset Pt) : (edges X).card = eS X := by
  rfl

/-- **Kissing bound**: a point has at most 6 points of `X` at distance `δ`.

TODO: none — proved (Phase 2).
Proof: two `δ`-neighbours of `p` subtend `≥ 60°` at `p` (else closer than `δ`),
so at most 6 fit around `p`.
Acceptance: no `sorry`.
Depends on: angle facts in `ℝ²`. Difficulty M. -/
theorem card_partners_minDist_le (X : Finset Pt) (p : Pt) :
    (partners X (minDist X) p).card ≤ 6 := by
  set δ := minDist X with hδdef
  by_contra hcon
  push Not at hcon
  obtain ⟨q₀, hq₀⟩ := card_pos.1 (by omega : 0 < (partners X δ p).card)
  obtain ⟨-, hq₀p, hq₀d⟩ := Defs.mem_partners.1 hq₀
  have hδ : 0 < δ := by rw [← hq₀d]; exact dist_pos.2 (Ne.symm hq₀p)
  let z : Pt → ℂ := fun q => ⟨q 0 - p 0, q 1 - p 1⟩
  have hz : ∀ q ∈ partners X δ p, ‖z q‖ = δ := by
    intro q hq
    obtain ⟨-, -, hd⟩ := Defs.mem_partners.1 hq
    have h1 := (dist_eq_iff_sqd hδ.le).1 hd
    have h2 : ‖z q‖ ^ 2 = δ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_mk, ← h1, sqd]; ring
    exact (pow_left_inj₀ (norm_nonneg _) hδ.le two_ne_zero).1 h2
  have hre : ∀ q ∈ partners X δ p, q 0 - p 0 = δ * cos (Complex.arg (z q)) := by
    intro q hq
    have hz0 : z q ≠ 0 := by
      intro h; have := hz q hq; rw [h, norm_zero] at this; linarith
    rw [Complex.cos_arg hz0, hz q hq, mul_div_cancel₀ _ hδ.ne']
  have him : ∀ q ∈ partners X δ p, q 1 - p 1 = δ * sin (Complex.arg (z q)) := by
    intro q hq
    rw [Complex.sin_arg, hz q hq, mul_div_cancel₀ _ hδ.ne']
  let f : Pt → ℕ := fun q => ⌈(Complex.arg (z q) + π) / (π / 3)⌉₊
  have hmaps : ∀ q ∈ partners X δ p, f q ∈ Icc 1 6 := by
    intro q _
    have h1 := Complex.neg_pi_lt_arg (z q)
    have h2 := Complex.arg_le_pi (z q)
    have hp3 : 0 < π / 3 := by positivity
    rw [mem_Icc]
    constructor
    · exact Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (Nat.ceil_pos.2 (div_pos (by linarith) hp3)))
    · refine Nat.ceil_le.2 ?_
      rw [div_le_iff₀ hp3]; push_cast; linarith
  have hcard : (Icc 1 6 : Finset ℕ).card < (partners X δ p).card := by simpa using hcon
  obtain ⟨q, hq, q', hq', hqq', hf⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  have hclose : |Complex.arg (z q) - Complex.arg (z q')| < π / 3 := by
    have hp3 : 0 < π / 3 := by positivity
    have h1 := Complex.neg_pi_lt_arg (z q)
    have h1' := Complex.neg_pi_lt_arg (z q')
    set x := (Complex.arg (z q) + π) / (π / 3)
    set y := (Complex.arg (z q') + π) / (π / 3)
    have hx0 : 0 ≤ x := div_nonneg (by linarith) hp3.le
    have hy0 : 0 ≤ y := div_nonneg (by linarith) hp3.le
    have a1 := Nat.le_ceil x
    have a2 := Nat.ceil_lt_add_one hx0
    have b1 := Nat.le_ceil y
    have b2 := Nat.ceil_lt_add_one hy0
    have hf' : (⌈x⌉₊ : ℝ) = ⌈y⌉₊ := by exact_mod_cast hf
    have hxy : |x - y| < 1 := by rw [abs_lt]; constructor <;> linarith
    have e : Complex.arg (z q) - Complex.arg (z q') = (x - y) * (π / 3) := by
      simp only [x, y]; field_simp; ring
    rw [e, abs_mul, abs_of_pos hp3]
    nlinarith [abs_nonneg (x - y)]
  obtain ⟨hqX, -, -⟩ := Defs.mem_partners.1 hq
  obtain ⟨hq'X, -, -⟩ := Defs.mem_partners.1 hq'
  have hge := minDist_le_dist hqX hq'X hqq'
  have hsq : δ ^ 2 ≤ sqd q q' := by
    rw [← dist_sq_eq_sqd]; exact pow_le_pow_left₀ hδ.le hge 2
  have hlt := sqd_lt_of_arg hδ hclose
  have e : sqd q q' = (δ * cos (Complex.arg (z q)) - δ * cos (Complex.arg (z q'))) ^ 2 +
      (δ * sin (Complex.arg (z q)) - δ * sin (Complex.arg (z q'))) ^ 2 := by
    rw [← hre q hq, ← hre q' hq', ← him q hq, ← him q' hq', sqd]; ring
  linarith

/-- **Handshake with degree ≤ k**: `2|E| ≤ k|V|` for a loopless edge set on `V` whose vertices
have degree `≤ k`.

TODO: none — proved (Phase 2).
Proof: the double counting over `Sym2`.
Acceptance: no `sorry`.
Depends on: nothing. Difficulty M. -/
theorem two_mul_card_le_of_deg_le {V : Finset Pt} {E : Finset (Sym2 Pt)} {k : ℕ}
    (hE : ∀ z ∈ E, ¬ z.IsDiag ∧ ∀ p ∈ z, p ∈ V)
    (hdeg : ∀ p ∈ V, (E.filter (fun z => p ∈ z)).card ≤ k) :
    2 * E.card ≤ k * V.card := by
  have h2 : ∀ z ∈ E, (V.filter (fun p => p ∈ z)).card = 2 := by
    intro z hz
    induction z using Sym2.ind with
    | h a b =>
      obtain ⟨hd, hV⟩ := hE _ hz
      have hab : a ≠ b := by simpa using hd
      have : V.filter (fun p => p ∈ s(a, b)) = {a, b} := by
        ext x
        simp only [mem_filter, Sym2.mem_iff, mem_insert, mem_singleton]
        constructor
        · exact fun h => h.2
        · rintro (rfl | rfl)
          · exact ⟨hV _ (Sym2.mem_mk_left _ _), Or.inl rfl⟩
          · exact ⟨hV _ (Sym2.mem_mk_right _ _), Or.inr rfl⟩
      rw [this, card_pair hab]
  have hdc : ∑ z ∈ E, (V.filter (fun p => p ∈ z)).card =
      ∑ p ∈ V, (E.filter (fun z => p ∈ z)).card := by
    simp only [card_filter]; exact sum_comm
  calc 2 * E.card = ∑ z ∈ E, (V.filter (fun p => p ∈ z)).card := by
        rw [sum_congr rfl h2, sum_const, smul_eq_mul, mul_comm]
    _ = ∑ p ∈ V, (E.filter (fun z => p ∈ z)).card := hdc
    _ ≤ ∑ _p ∈ V, k := sum_le_sum hdeg
    _ = k * V.card := by rw [sum_const, smul_eq_mul, mul_comm]

/-- `μ(δ) ≤ 3n` (from the kissing bound).

TODO: none — proved (Phase 2).
Proof: handshake applied to the `δ`-graph.
Acceptance: no `sorry`.
Depends on: `card_partners_minDist_le`, `two_mul_card_le_of_deg_le`. Difficulty S–M. -/
theorem mult_minDist_le (X : Finset Pt) : (mult X (minDist X) : ℝ) ≤ 3 * X.card := by
  rcases (minDist_nonneg X).eq_or_lt with h0 | hpos
  · rw [← h0, mult_zero]; simp
  · have h2 := Erdos132Layer.two_mul_multS hpos X
    have hle : Erdos132Layer.esum X (minDist X) ≤ 6 * X.card := by
      unfold Erdos132Layer.esum
      calc ∑ v ∈ X, (Erdos132Layer.nbr X (minDist X) v).card ≤ ∑ _v ∈ X, 6 := by
            refine sum_le_sum fun v _ => le_trans (card_le_card fun x hx => ?_)
              (card_partners_minDist_le X v)
            obtain ⟨hxX, hd⟩ := Erdos132Layer.mem_nbr.1 hx
            refine Defs.mem_partners.2 ⟨hxX, fun h => ?_, hd⟩
            rw [h, dist_self] at hd; linarith
        _ = 6 * X.card := by rw [sum_const, smul_eq_mul, mul_comm]
    have : 2 * mult X (minDist X) ≤ 6 * X.card := by
      have e : mult X (minDist X) = multS X (minDist X) := rfl
      omega
    have : (2 * mult X (minDist X) : ℝ) ≤ 6 * X.card := by exact_mod_cast this
    linarith

/-! ## (VS) and (E) -/

/-- **(VS), general form**: for `Y ⊆ X`, the `Δ₂(X)`-pairs inside `Y` number `≤ (3/2)|Y|`.

TODO: none — proved (Phase 2).
Proof: case split: if `diam Y = diam X` then `dist2 Y = dist2 X` (no distances of `X`
in `(Δ₂, Δ)`) and apply [Ve87] to `Y`; otherwise `diam Y ≤ Δ₂` and [HP] applies (or the count
is `0`).
Acceptance: no `sorry`.
Depends on: `vesztergombi87`, `hopf_pannwitz`. Difficulty M. -/
theorem mult_dist2_subset_le {Y : Finset Pt} (hY : Y ⊆ X) :
    (mult Y (dist2 X) : ℝ) ≤ 3 / 2 * Y.card := by
  by_cases h0 : mult Y (dist2 X) = 0
  · rw [h0]; simp only [Nat.cast_zero]; positivity
  obtain ⟨z, hz⟩ := card_pos.1 (Nat.pos_of_ne_zero (by rwa [mult_eq_card] at h0))
  induction z using Sym2.ind with
  | h a b =>
  obtain ⟨ha, hb, hab, hd⟩ := mem_pairsAt.1 hz
  have hD2Y : dist2 X ∈ distSetS Y := hd ▸ dist_mem_distSetS ha hb hab
  have hD2X : dist2 X ∈ distSetS X := distSetS_mono hY hD2Y
  have hpos : 0 < dist2 X := pos_of_mem_distSetS hD2X
  have hne : ((distSetS X).erase (diam X)).Nonempty := by
    by_contra hh
    have : dist2 X = 0 := by rw [dist2, dite_eq_right hh]
    linarith
  have hd2 : dist2 X = ((distSetS X).erase (diam X)).max' hne := by rw [dist2, dite_eq_left hne]
  have hmem : dist2 X ∈ (distSetS X).erase (diam X) := by rw [hd2]; exact max'_mem _ _
  have hD2ne : dist2 X ≠ diam X := ne_of_mem_erase hmem
  have hle : ∀ d ∈ distSetS X, d ≠ diam X → d ≤ dist2 X := fun d hd hdne => by
    rw [hd2]; exact le_max' _ _ (mem_erase.2 ⟨hdne, hd⟩)
  by_cases hdiam : diam Y = diam X
  · have hneY : ((distSetS Y).erase (diam Y)).Nonempty :=
      ⟨dist2 X, mem_erase.2 ⟨by rw [hdiam]; exact hD2ne, hD2Y⟩⟩
    have e : dist2 Y = dist2 X := by
      rw [dist2, dite_eq_left hneY]
      refine le_antisymm (max'_le _ _ _ fun d hd => ?_) (le_max' _ _ (mem_erase.2
        ⟨by rw [hdiam]; exact hD2ne, hD2Y⟩))
      obtain ⟨hdne, hdY⟩ := mem_erase.1 hd
      exact hle d (distSetS_mono hY hdY) (by rw [← hdiam]; exact hdne)
    have := vesztergombi87 Y
    rwa [e] at this
  · have hneY : (distSetS Y).Nonempty := ⟨_, hD2Y⟩
    have hdY : diam Y ∈ distSetS Y := by rw [diam, dite_eq_left hneY]; exact max'_mem _ _
    have e : dist2 X = diam Y :=
      le_antisymm (le_diam hD2Y) (hle _ (distSetS_mono hY hdY) hdiam)
    rw [e]
    have := hopf_pannwitz Y
    have : (mult Y (diam Y) : ℝ) ≤ Y.card := by exact_mod_cast this
    have : (0 : ℝ) ≤ Y.card := Nat.cast_nonneg _
    linarith

/-- Every `Δ₂`-pair lies inside `S`.

TODO: none — proved (Phase 2).
Proof: both ends of a `Δ₂`-pair have a `Δ₂`-partner, so are in `S`.
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem mult_dist2_eq_S (X : Finset Pt) : mult X (dist2 X) = mult (Sset X) (dist2 X) := by
  refine le_antisymm ?_ (mult_mono (filter_subset _ _) _)
  refine (mult_le_add_sum (Sset X) _ _).trans (le_of_eq ?_)
  rw [sum_eq_zero, add_zero]
  intro x hx
  obtain ⟨hxX, hxS⟩ := mem_sdiff.1 hx
  rw [card_eq_zero, ← not_nonempty_iff_eq_empty]
  intro hne
  exact hxS (mem_filter.2 ⟨hxX, hne⟩)

/-- **(VS)** `μ(Δ₂) ≤ (3/2)|S|`.

TODO: none (proved from the two lemmas above).
Acceptance: no `sorry` (inherits theirs).
Depends on: `mult_dist2_eq_S`, `mult_dist2_subset_le`. -/
theorem VS (X : Finset Pt) : (mult X (dist2 X) : ℝ) ≤ 3 / 2 * (Sset X).card := by
  rw [mult_dist2_eq_S]
  exact mult_dist2_subset_le (filter_subset _ _)

/-- **(E)** `μ(δ) ≤ e(S) + 6r`: every `δ`-pair not inside `S` has an endpoint in `R`.

TODO: none — proved (Phase 2).
Proof: split the `δ`-pairs of `X` into those inside `S` and those meeting `R`;
bound the latter by `Σ_{x ∈ R} deg_δ x ≤ 6r`.
Acceptance: no `sorry`.
Depends on: `card_partners_minDist_le`. Difficulty M. -/
theorem E_bound (X : Finset Pt) :
    (mult X (minDist X) : ℝ) ≤ eS X + 6 * (Rset X).card := by
  have h := mult_le_add_sum (Sset X) X (minDist X)
  have hs : ∑ x ∈ X \ Sset X, (partners X (minDist X) x).card ≤ 6 * (Rset X).card := by
    calc ∑ x ∈ X \ Sset X, (partners X (minDist X) x).card ≤ ∑ _x ∈ X \ Sset X, 6 :=
          sum_le_sum fun x _ => card_partners_minDist_le X x
      _ = 6 * (Rset X).card := by rw [sum_const, smul_eq_mul, mul_comm, Rset]
  have : mult X (minDist X) ≤ eS X + 6 * (Rset X).card := by
    rw [eS]; omega
  exact_mod_cast this

/-- **Weighted (VS)** (Lemma 4.2, first bullet): if every point of `P₁ ⊆ S` has `Δ₂`-degree 1
then `μ(Δ₂) ≤ |P₁| + (3/2)|S ∖ P₁|`.

TODO: none — proved (Phase 2).
Proof: pairs touching `P₁` number `≤ |P₁|`; the rest lie in `S ∖ P₁`, apply
`mult_dist2_subset_le`.
Acceptance: no `sorry`.
Depends on: `mult_dist2_eq_S`, `mult_dist2_subset_le`. Difficulty M. -/
theorem VS_weighted {P₁ : Finset Pt} (hP : P₁ ⊆ Sset X) (hdeg : ∀ v ∈ P₁, deg2 X v = 1) :
    (mult X (dist2 X) : ℝ) ≤ P₁.card + 3 / 2 * (Sset X \ P₁).card := by
  have h := mult_le_add_sum (Sset X \ P₁) X (dist2 X)
  have hSX : Sset X ⊆ X := filter_subset _ _
  have hsum : ∑ x ∈ X \ (Sset X \ P₁), (partners X (dist2 X) x).card = P₁.card := by
    rw [← sum_subset (s₁ := P₁) (fun x hx => mem_sdiff.2 ⟨hSX (hP hx),
      fun h' => (mem_sdiff.1 h').2 hx⟩)]
    · rw [card_eq_sum_ones]
      exact sum_congr rfl fun v hv => by have := hdeg v hv; rwa [deg2] at this
    · intro x hx hxP
      obtain ⟨hxX, hxS⟩ := mem_sdiff.1 hx
      have hxS' : x ∉ Sset X := fun h' => hxS (mem_sdiff.2 ⟨h', hxP⟩)
      rw [card_eq_zero, ← not_nonempty_iff_eq_empty]
      exact fun hne => hxS' (mem_filter.2 ⟨hxX, hne⟩)
  rw [hsum] at h
  have h2 := mult_dist2_subset_le (X := X) (Y := Sset X \ P₁) (sdiff_subset.trans hSX)
  have : (mult X (dist2 X) : ℝ) ≤ mult (Sset X \ P₁) (dist2 X) + P₁.card := by exact_mod_cast h
  linarith

/-! ## The linear programmes (Lemmas 4.1, 4.2) — pure algebra -/

/-- **Lemma 4.1** (LP certificate): with `λ = (6 − k)/(7.5 − k)`,
`min{μ₂, μ_δ} ≤ 9(s + r)/(7.5 − k) + C`.

TODO: none — proved (Phase 2).
What's missing: nothing — algebra.
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem lp_mix {μ₂ μδ s r e k C : ℝ} (_hk0 : 0 ≤ k) (hk : k ≤ 3 / 2) (_hs : 0 ≤ s) (_hr : 0 ≤ r)
    (hC : 0 ≤ C) (h₂ : μ₂ ≤ 3 / 2 * s) (hδ : μδ ≤ e + 6 * r) (he : e ≤ k * s + C) :
    min μ₂ μδ ≤ 9 * (s + r) / (15 / 2 - k) + C := by
  have hpos : 0 < 15 / 2 - k := by linarith
  have h1 := min_le_left μ₂ μδ
  have h2 := min_le_right μ₂ μδ
  set m := min μ₂ μδ
  have key : (15 / 2 - k) * m ≤ 9 * (s + r) + 3 / 2 * C := by
    have a : (6 - k) * m ≤ (6 - k) * (3 / 2 * s) :=
      mul_le_mul_of_nonneg_left (h1.trans h₂) (by linarith)
    have b : 3 / 2 * m ≤ 3 / 2 * (k * s + C + 6 * r) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num); linarith
    nlinarith
  have hCle : 3 / 2 * C ≤ (15 / 2 - k) * C := mul_le_mul_of_nonneg_right (by linarith) hC
  rw [div_add' _ _ _ hpos.ne', le_div_iff₀ hpos]
  nlinarith

/-- **Lemma 4.2** (weighted LP, weights `4/5, 1/5`): `min{μ₂, μ_δ} ≤ (7/5)(s + r) + C`.

TODO: none — proved (Phase 2).
What's missing: nothing — algebra.
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem lp_weighted {μ₂ μδ s r e p C : ℝ} (_hp : 0 ≤ p) (_hps : p ≤ s) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (h₂ : μ₂ ≤ p + 3 / 2 * (s - p)) (hδ : μδ ≤ e + 6 * r) (he : e ≤ s + 2 * p + C) :
    min μ₂ μδ ≤ 7 / 5 * (s + r) + C := by
  have h1 := min_le_left μ₂ μδ
  have h2 := min_le_right μ₂ μδ
  linarith

/-- `9n/(7.5 − k) ≤ (54/37) n` for `0 ≤ k ≤ 4/3`.

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem lp_value_le {k n : ℝ} (_hk0 : 0 ≤ k) (hk : k ≤ 4 / 3) (hn : 0 ≤ n) :
    9 * n / (15 / 2 - k) ≤ 54 / 37 * n := by
  have hpos : 0 < 15 / 2 - k := by linarith
  rw [div_le_iff₀ hpos]
  nlinarith

/-- **[C1]** values of the certificate: `k = 1, 5/4, 4/3 ↦ 18/13, 36/25, 54/37`, and
`7/5 ≤ 54/37`.

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem lp_values :
    (9 : ℝ) / (15 / 2 - 1) = 18 / 13 ∧ (9 : ℝ) / (15 / 2 - 5 / 4) = 36 / 25 ∧
      (9 : ℝ) / (15 / 2 - 4 / 3) = 54 / 37 ∧ (7 : ℝ) / 5 ≤ 54 / 37 := by
  norm_num

/-! ## Normalisation and small cases -/

/-- **Scaling**: every `X` with `≥ 2` points has a copy `Y` (a dilate) with `δ(Y) = 1` and the
same `n`, `μ(Δ₂)`, `μ(δ)`.

TODO: none — proved (Phase 2).
Proof: `Y := δ⁻¹ • X`; distances scale by `δ⁻¹`, so `diam`, `dist2`, `minDist`,
`mult` transform accordingly (`δ > 0` since the points are distinct).
Acceptance: no `sorry`.
Depends on: definitions. Difficulty M. -/
theorem exists_normalize (hX : 2 ≤ X.card) :
    ∃ Y : Finset Pt, Y.card = X.card ∧ minDist Y = 1 ∧
      mult Y (dist2 Y) = mult X (dist2 X) ∧ mult Y (minDist Y) = mult X (minDist X) := by
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.1 (by omega : 1 < X.card)
  have hne : (distSetS X).Nonempty := ⟨_, dist_mem_distSetS ha hb hab⟩
  have hδ : 0 < minDist X := by
    rw [minDist, dite_eq_left hne]; exact pos_of_mem_distSetS (min'_mem _ _)
  set c := (minDist X)⁻¹
  have hc : 0 < c := inv_pos.2 hδ
  refine ⟨X.image (c • ·), card_image_of_injective _ (smul_right_injective Pt hc.ne'), ?_, ?_, ?_⟩
  · rw [minDist_smul hc, inv_mul_cancel₀ hδ.ne']
  · rw [dist2_smul hc, mult_smul hc]
  · rw [minDist_smul hc, mult_smul hc]

/-- **[C11]** `(2 · 1.94·10⁴ + 1)² < N₀`.

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem N0_check : (2 * (1.94 * 10 ^ 4) + 1 : ℝ) ^ 2 < N₀ := by
  norm_num [N₀]

/-- **Small cases** (§4): nondegenerate with `δ = 1`, `Δ₂ < 10⁴` ⇒ `n < N₀` (packing:
`n ≤ (2Δ + 1)²`).

TODO: none — proved (Phase 2).
Proof: grid pigeonhole — `X` lies in an axis-parallel square of side `Δ < 19400`; cells of
side `7/10` have diameter `< 1 = δ`, so each holds `≤ 1` point: `n ≤ 27715² < N₀`.
Acceptance: no `sorry`.
Depends on: `N0_check`. Difficulty M–L. -/
theorem card_lt_N0 (h1 : minDist X = 1) (hnd : diam X ≤ 1.94 * dist2 X)
    (hsmall : dist2 X < 10 ^ 4) : (X.card : ℝ) < N₀ := by
  rcases X.eq_empty_or_nonempty with rfl | hne
  · simp [N₀]
  have hD : diam X < 19400 := by linarith
  have hD0 := diam_nonneg X
  set m0 := X.inf' hne (fun x : Pt => x 0)
  set m1 := X.inf' hne (fun x : Pt => x 1)
  obtain ⟨a, ha, hma⟩ := exists_mem_eq_inf' hne (fun x : Pt => x 0)
  obtain ⟨b, hb, hmb⟩ := exists_mem_eq_inf' hne (fun x : Pt => x 1)
  have lo0 : ∀ x ∈ X, 0 ≤ x 0 - m0 := fun x hx => sub_nonneg.2 (inf'_le _ hx)
  have lo1 : ∀ x ∈ X, 0 ≤ x 1 - m1 := fun x hx => sub_nonneg.2 (inf'_le _ hx)
  have hi0 : ∀ x ∈ X, x 0 - m0 ≤ diam X := fun x hx => by
    have h := (coord_sq_le x a).1
    have hd := dist_le_diam hx ha
    have := lo0 x hx
    have hm : m0 = a 0 := hma
    rw [hm] at this ⊢
    nlinarith [dist_nonneg (x := x) (y := a)]
  have hi1 : ∀ x ∈ X, x 1 - m1 ≤ diam X := fun x hx => by
    have h := (coord_sq_le x b).2
    have hd := dist_le_diam hx hb
    have := lo1 x hx
    have hm : m1 = b 1 := hmb
    rw [hm] at this ⊢
    nlinarith [dist_nonneg (x := x) (y := b)]
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = 27715 := ⟨_, rfl⟩
  let f : Pt → ℕ × ℕ := fun x => (⌊(x 0 - m0) / (7 / 10)⌋₊, ⌊(x 1 - m1) / (7 / 10)⌋₊)
  have hmaps : ∀ x ∈ X, f x ∈ range K ×ˢ range K := fun x hx => by
    rw [mem_product, mem_range, mem_range, hK]
    exact ⟨floor_cell_lt (lo0 x hx) (hi0 x hx) hD, floor_cell_lt (lo1 x hx) (hi1 x hx) hD⟩
  have hinj : Set.InjOn f X := by
    intro x hx y hy hxy
    by_contra hne'
    have e := Prod.mk.inj hxy
    have c0 := close_of_floor_eq (lo0 x hx) (lo0 y hy) e.1
    have c1 := close_of_floor_eq (lo1 x hx) (lo1 y hy) e.2
    have hge := minDist_le_dist hx hy hne'
    rw [h1] at hge
    have hsq : 1 ≤ sqd x y := by
      rw [← dist_sq_eq_sqd]; nlinarith
    have e0 : x 0 - m0 - (y 0 - m0) = x 0 - y 0 := by ring
    have e1 : x 1 - m1 - (y 1 - m1) = x 1 - y 1 := by ring
    rw [e0] at c0; rw [e1] at c1
    rw [sqd] at hsq
    norm_num at c0 c1
    linarith
  have hcard := card_le_card_of_injOn f hmaps hinj
  rw [card_product, card_range] at hcard
  rw [hK] at hcard
  have h' : (X.card : ℝ) ≤ 768121225 := by exact_mod_cast hcard.trans (by norm_num)
  rw [N₀]; linarith

end

end Erdos132Main
