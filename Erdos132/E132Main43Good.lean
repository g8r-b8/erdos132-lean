import Erdos132.E132Main43Defs

/-!
# Erdős Problem 132, `4/3` theorem — good points: exceptions and the local frame

Paper: `angle_R6.md` §1.1–1.2.  Euclidean-local form (as for Theorem N1 in
`E132Main15N1`, see `MAIN15_PLAN.md` "Deviations"): no arc length, no graph function.

* **Exceptions** (`card_E43_le`): at most `cE43 = 10¹⁵` heavy points are not good.  A heavy
  point `y` is in `R ∖ D`, interior to `K`, and (not good) has two boundary points
  `b₁, b₂ ∈ B̄(y, Λ)` with unit normals `‖ν₁ − ν₂‖ > ε₀`.  Either the normals are nearly
  antipodal (`ν₁·ν₂ ≤ −(1 − 10⁻⁴)`: **thin**, Lemma T at scale `Λ`, `|X ∖ D| ≤ cThin43`), or
  every direction between them is the normal of a support point within `150Λ = 69600` of `y`
  (**big turning**, `turning(∂K ∩ B̄(y, 69600)) ≥ ε₀`, counted by `turning_sum_le`).
* **Frame** (`frame_of_good`): a good heavy point has a `Frame43`: nearest boundary point
  `p₀ = y + h n`, `h ∈ (0, 1]`, normals near `n` within distance `6`, and far points of `K` at
  abscissa `±463` (from goodness at radius `Λ`: the support point in a direction just outside
  the `ε₀`-cone is farther than `Λ`).
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-- The boundary piece `∂K ∩ B̄(y, 150Λ)` whose turning is measured (`150·464 = 69600`). -/
def bdryNear43 (X : Finset Pt) (y : Pt) : Set Pt :=
  frontier (KBall X) ∩ Metric.closedBall y 69600

/-! ## Heavy points -/

/-- Heavy points are not diametral.

TODO: none — proved.
Acceptance: no `sorry` (inherits `degδ_le_three_of_D`).
Depends on: `vR_le_six_of_D`. Difficulty S. -/
theorem heavy_not_D (hX : Normal X) {y : Pt} (hy : y ∈ heavy X) : y ∉ Dset X := fun hD => by
  have := vR_le_six_of_D hX hD
  have := (mem_filter.1 hy).2
  omega

/-- Heavy points are interior to `K`.

TODO: none — proved.
Acceptance: no `sorry` (inherits).
Depends on: `Rset_interior`, `heavy_not_D`. Difficulty S. -/
theorem heavy_interior (hX : Normal X) {y : Pt} (hy : y ∈ heavy X) : y ∈ interior (KBall X) :=
  Rset_interior hX (mem_filter.1 hy).1 (heavy_not_D hX hy)

/-- Heavy points have depth `≤ 1` (they have an `S`-neighbour, `m_y ≥ 3`).

TODO: none — proved.
Acceptance: no `sorry` (inherits).
Depends on: `exists_near_normal`, `degδ_le_six`. Difficulty S. -/
theorem heavy_depth_le (hX : Normal X) {y : Pt} (hy : y ∈ heavy X) : depth X y ≤ 1 := by
  have hm : 0 < mS X y := by
    have h9 := (mem_filter.1 hy).2
    unfold vR at h9
    have := degδ_le_six X y
    omega
  obtain ⟨b, hb, hd, -⟩ := exists_near_normal hX (heavy_interior hX hy) hm
  exact (Metric.infDist_le_dist_of_mem hb).trans hd

/-! ## The frame at a good point -/

/-- **Nearest boundary point.**  For `y` interior to `K`, `h = depth X y > 0` is attained at
`p₀ = y + h n` for a unit `n`, and `n` is an outer normal of `K` at `p₀`.

TODO: none — proved.
What's missing: `frontier K` is compact (closed subset of the compact `K`) and nonempty (`K` is
bounded, `≠ univ`), so `IsCompact.exists_infDist_eq_dist` gives `p₀` with `dist y p₀ = h`;
`h > 0` since `y ∉ frontier K` (interior) and the frontier is closed
(`Metric.infDist_pos_iff_not_mem_closure` or similar).  Put `n = h⁻¹ (p₀ − y)`.  Normal: the
open ball `B(y, h)` lies in `K` (a point of it outside `K` gives, by `exists_frontier_seg`, a
frontier point closer than `h`), so for a unit normal `ν` at `p₀` (`exists_unit_normal`)
`⟨y + h ν − p₀, ν⟩ ≤ 0` (limit of points of the ball), i.e. `⟨p₀ − y, ν⟩ ≥ h = ‖p₀ − y‖`,
and equality in Cauchy–Schwarz forces `ν = n`.
Acceptance: no `sorry`.
Depends on: `KBall_isCompact`, `KBall_convex`, `exists_unit_normal`, `exists_frontier_seg`.
Difficulty M. -/
theorem exists_foot (hX : Normal X) {y : Pt} (hy : y ∈ interior (KBall X)) :
    ∃ n : Pt, ‖n‖ = 1 ∧ 0 < depth X y ∧ y + depth X y • n ∈ frontier (KBall X) ∧
      n ∈ normalCone (KBall X) (y + depth X y • n) := by
  have hne : X.Nonempty := card_pos.1 (by have := hX.four_le; omega)
  have hKc := KBall_isCompact hne
  have hyK : y ∈ KBall X := interior_subset hy
  have hFc : IsCompact (frontier (KBall X)) :=
    hKc.of_isClosed_subset isClosed_frontier
      (frontier_subset_closure.trans (KBall_isClosed X).closure_eq.subset)
  obtain ⟨x, hxK, hxmax⟩ := hKc.exists_isMaxOn ⟨y, hyK⟩
    (continuous_id.inner continuous_const :
      Continuous fun z : Pt => inner ℝ z (dirVec 0)).continuousOn
  have hxF : x ∈ frontier (KBall X) :=
    mem_frontier_of_max hxK (norm_dirVec 0) (fun z hz => hxmax hz)
  obtain ⟨p, hpF, hpd⟩ := hFc.exists_infDist_eq_dist ⟨x, hxF⟩ y
  have hdep : depth X y = dist y p := hpd
  have hyp : y ≠ p := by rintro rfl; exact hpF.2 hy
  have hpos : 0 < depth X y := by rw [hdep]; exact dist_pos.2 hyp
  set h := depth X y with hh
  set n : Pt := h⁻¹ • (p - y) with hndef
  have hpy : ‖p - y‖ = h := by rw [← dist_eq_norm, dist_comm, ← hdep]
  have hn : ‖n‖ = 1 := by
    rw [hndef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hpos, hpy,
      inv_mul_cancel₀ hpos.ne']
  have hp : y + h • n = p := by
    rw [hndef, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul, add_sub_cancel]
  refine ⟨n, hn, hpos, ?_⟩
  rw [hp]
  refine ⟨hpF, ?_⟩
  -- the open ball `B(y, h)` lies in `K`
  have hball : ∀ z, dist z y < h → z ∈ KBall X := by
    intro z hz
    by_contra hzK
    have hzI : z ∉ interior (KBall X) := fun hi => hzK (interior_subset hi)
    obtain ⟨l, hl0, hl1, hb⟩ := exists_frontier_seg (KBall_isClosed X) hy hzI
    have h1 : h ≤ dist y (y + l • (z - y)) := by
      rw [hh]; exact Metric.infDist_le_dist_of_mem hb
    have h2 : dist y (y + l • (z - y)) = l * dist z y := by
      rw [dist_eq_norm, show y - (y + l • (z - y)) = -(l • (z - y)) by abel, norm_neg,
        norm_smul, Real.norm_eq_abs, abs_of_pos hl0, dist_eq_norm]
    have : l * dist z y ≤ dist z y := by nlinarith [dist_nonneg (x := z) (y := y)]
    linarith
  obtain ⟨ν, hν1, hν⟩ := exists_unit_normal (KBall_convex X) ⟨y, hy⟩ hpF
  have hge : h ≤ inner ℝ (p - y) ν := by
    by_contra hlt
    push Not at hlt
    have hcs : -h ≤ inner ℝ (p - y) ν := by
      have := neg_abs_le (inner ℝ (p - y) ν)
      have := abs_real_inner_le_norm (p - y) ν
      rw [hpy, hν1, mul_one] at this
      linarith
    set a := inner ℝ (p - y) ν with ha
    set t := (a / h + 1) / 2 with htdef
    have has : a = a / h * h := by field_simp
    have hs1 : a / h < 1 := by rw [div_lt_one hpos]; exact hlt
    have hsm : -1 ≤ a / h := by rw [le_div_iff₀ hpos]; linarith
    have hz : y + (t * h) • ν ∈ KBall X := hball _ (by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hν1, mul_one, Real.norm_eq_abs,
        abs_lt]
      constructor <;> nlinarith)
    have := hν _ hz
    have e : y + (t * h) • ν - p = (t * h) • ν - (p - y) := by abel
    rw [e, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hν1, ← ha] at this
    nlinarith
  have hnν : 1 ≤ inner ℝ n ν := by
    rw [hndef, real_inner_smul_left, le_inv_mul_iff₀ hpos, mul_one]; exact hge
  have hsq := norm_sub_sq_real n ν
  rw [hn, hν1] at hsq
  have h0 : ‖n - ν‖ = 0 := by
    have : ‖n - ν‖ ^ 2 ≤ 0 := by linarith
    exact pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm this (sq_nonneg _))
  rw [norm_eq_zero, sub_eq_zero] at h0
  rw [h0]; exact hν

/-- Goodness gives the frame's normal control (radius `6`) around a boundary point `b₀` within
distance `1` carrying the unit normal `n`.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `IsGood43`. Difficulty S. -/
theorem good_normals {y b₀ n : Pt} (hg : IsGood43 X y) (hb₀ : b₀ ∈ frontier (KBall X))
    (hd₀ : dist y b₀ ≤ 1) (hn : n ∈ normalCone (KBall X) b₀) (hn1 : ‖n‖ = 1) :
    ∀ b ∈ frontier (KBall X), dist y b ≤ 6 → ∀ ν ∈ normalCone (KBall X) b, ‖ν‖ = 1 →
      ‖ν - n‖ ≤ ε₀43 := fun b hb hd ν hν hν1 =>
  hg b hb b₀ hb₀ (by unfold Lam43; linarith) (by unfold Lam43; linarith) ν hν n hn hν1 hn1

/-- **Far points** (input of Lemma DN): at a good `y ∈ K` with foot `p₀ = y + h n`
(`0 ≤ h ≤ 1`, `n` a unit normal at `p₀`), `K` contains points at abscissa `σ·463` and height
`≥ h − 9.31`, for `σ = ±1`.

TODO: none — proved.
What's missing (Euclidean replacement of the paper's graph points `g± = (±463, f(±463))`):
let `d = (n + σ κ perp n)/‖·‖` with `κ = 201/10000`, so `‖d − n‖ > 1/50`, and let `x` maximise
`⟨·, d⟩` on `K` (compact; `mem_frontier_of_max`), so `d ∈ normalCone K x`.  Goodness with
`b₁ = x`, `b₂ = p₀` (`dist y p₀ = h ≤ 1 ≤ Λ`, `n ∈ N(p₀)`) forces `dist y x > Λ = 464`.  With
`A = σ⟨x − y, perp n⟩`, `C = ⟨x − y, n⟩`: `⟨p₀ − x, d⟩ ≤ 0` gives `h − C ≤ κ A`; `C ≤ h`
(`Frame43.top`-style, from `n ∈ N(p₀)`) gives `A ≥ 0` and `|C| ≤ 1 + κ A`.  If `A ≤ 463` then
`A² + C² ≤ 463² + (1 + 463κ)² < 464²`, contradiction; so `A > 463`, and
`g = p₀ + (463/A)(x − p₀) ∈ K` (convexity) has abscissa `σ·463` and height
`h + (463/A)(C − h) ≥ h − 463κ ≥ h − 9.31`.
Acceptance: no `sorry`.
Depends on: `KBall_isCompact`, `KBall_convex`, `mem_frontier_of_max`, `IsGood43`,
`norm_perp`, `inner_pt`. Difficulty M–L. -/
theorem far_points (hX : Normal X) {y n : Pt} (hg : IsGood43 X y) (hyK : y ∈ KBall X)
    (hn : ‖n‖ = 1) (hh0 : 0 ≤ depth X y) (hh : depth X y ≤ 1)
    (hfoot : y + depth X y • n ∈ frontier (KBall X))
    (hnorm : n ∈ normalCone (KBall X) (y + depth X y • n)) :
    ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∃ g ∈ KBall X,
      inner ℝ (g - y) (perp n) = σ * 463 ∧ depth X y - 931 / 100 ≤ inner ℝ (g - y) n := by
  intro σ hσ
  have hne : X.Nonempty := card_pos.1 (by have := hX.four_le; omega)
  have hKc := KBall_isCompact hne
  set h := depth X y with hhdef
  set p₀ := y + h • n with hp₀
  have hp₀K : p₀ ∈ KBall X := (KBall_isClosed X).closure_eq ▸ hfoot.1
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hnn : inner ℝ n n = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have hnp : inner ℝ n (perp n) = 0 := by rw [inner_pt]; simp; ring
  have hpn : inner ℝ (perp n) n = 0 := by rw [real_inner_comm]; exact hnp
  have hpp : inner ℝ (perp n) (perp n) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_perp, hn]; norm_num
  set κ : ℝ := 201 / 10000 with hκ
  set d₀ : Pt := n + (σ * κ) • perp n with hd₀
  have hd₀n : inner ℝ d₀ n = 1 := by
    rw [hd₀, inner_add_left, real_inner_smul_left, hnn, hpn]; ring
  have hd₀p : inner ℝ d₀ (perp n) = σ * κ := by
    rw [hd₀, inner_add_left, real_inner_smul_left, hnp, hpp]; ring
  have hN2 : ‖d₀‖ ^ 2 = 1 + κ ^ 2 := by
    rw [n1_norm_sq_frame hn d₀, hd₀n, hd₀p]
    have : (σ * κ) ^ 2 = (σ * σ) * κ ^ 2 := by ring
    rw [this, hσ2]; ring
  set N := ‖d₀‖ with hNdef
  have hNpos : 0 < N := by
    by_contra hc
    push Not at hc
    have h0 : N = 0 := le_antisymm hc (norm_nonneg _)
    rw [h0] at hN2
    nlinarith [sq_nonneg κ]
  set d : Pt := N⁻¹ • d₀ with hddef
  have hd1 : ‖d‖ = 1 := by
    rw [hddef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hNpos, inv_mul_cancel₀ hNpos.ne']
  have hdn : inner ℝ d n = N⁻¹ := by rw [hddef, real_inner_smul_left, hd₀n, mul_one]
  have hu : N⁻¹ < 4999 / 5000 := by
    rw [inv_lt_comm₀ hNpos (by norm_num)]
    by_contra hc
    push Not at hc
    norm_num at hc
    have : N ^ 2 ≤ (5000 / 4999) ^ 2 := pow_le_pow_left₀ hNpos.le hc 2
    rw [hN2, hκ] at this
    norm_num at this
  have hfard : 1 / 50 < ‖d - n‖ := by
    have hs := norm_sub_sq_real d n
    rw [hd1, hn, hdn] at hs
    by_contra hc
    push Not at hc
    have : ‖d - n‖ ^ 2 ≤ (1 / 50) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hc 2
    nlinarith
  -- the support point in direction `d`
  obtain ⟨x, hxK, hxmax⟩ := hKc.exists_isMaxOn ⟨p₀, hp₀K⟩
    (continuous_id.inner continuous_const : Continuous fun z : Pt => inner ℝ z d).continuousOn
  have hmax : ∀ z ∈ KBall X, inner ℝ z d ≤ inner ℝ x d := fun z hz => hxmax hz
  have hxF : x ∈ frontier (KBall X) := mem_frontier_of_max hxK hd1 hmax
  have hxN : d ∈ normalCone (KBall X) x := fun z hz => by
    rw [inner_sub_left]; linarith [hmax z hz]
  have hdp₀ : dist y p₀ = h := by
    rw [hp₀, dist_eq_norm, show y - (y + h • n) = -(h • n) by abel, norm_neg, norm_smul, hn,
      mul_one, Real.norm_eq_abs, abs_of_nonneg hh0]
  have hfarx : 464 < dist y x := by
    by_contra hc
    push Not at hc
    have := hg x hxF p₀ hfoot (by unfold Lam43; exact hc) (by unfold Lam43; linarith)
      d hxN n hnorm hd1 hn
    unfold ε₀43 at this
    linarith
  -- coordinates of `x`
  set C := inner ℝ (x - y) n with hC
  set P := inner ℝ (x - y) (perp n) with hP
  have hxp : x - p₀ = (x - y) - h • n := by rw [hp₀]; abel
  have h1 : 0 ≤ C + κ * (σ * P) - h := by
    have hm := hmax p₀ hp₀K
    have e : inner ℝ x d - inner ℝ p₀ d = N⁻¹ * inner ℝ (x - p₀) d₀ := by
      rw [← inner_sub_left, hddef, inner_smul_right]
    have hge : 0 ≤ inner ℝ (x - p₀) d₀ := by
      have : 0 ≤ N⁻¹ * inner ℝ (x - p₀) d₀ := by linarith
      exact (mul_nonneg_iff_of_pos_left (inv_pos.2 hNpos)).1 this
    rw [hxp, hd₀, inner_sub_left, inner_add_right, inner_add_right, inner_smul_right,
      real_inner_smul_left, real_inner_smul_left, inner_smul_right, hnn, hnp, ← hC,
      ← hP] at hge
    linarith
  have h2 : C - h ≤ 0 := by
    have := hnorm x hxK
    rw [hxp, inner_sub_left, real_inner_smul_left, hnn, ← hC] at this
    linarith
  set A := σ * P with hA
  have hA0 : 0 ≤ A := by
    by_contra hc; push Not at hc
    have : κ * A < 0 := mul_neg_of_pos_of_neg (by norm_num [hκ]) hc
    linarith
  have hPA : P = σ * A := by rw [hA, ← mul_assoc, hσ2, one_mul]
  have hnx : ‖x - y‖ ^ 2 = C ^ 2 + A ^ 2 := by
    rw [n1_norm_sq_frame hn, ← hC, ← hP, hPA]
    have : (σ * A) ^ 2 = (σ * σ) * A ^ 2 := by ring
    rw [this, hσ2, one_mul]
  have hA463 : 463 < A := by
    by_contra hc
    push Not at hc
    have hCl : -(κ * 463) ≤ C := by
      have : κ * A ≤ κ * 463 := mul_le_mul_of_nonneg_left hc (by norm_num [hκ])
      linarith
    have hCu : C ≤ 1 := by linarith
    have hC2 : C ^ 2 ≤ 87 := by norm_num [hκ] at hCl; nlinarith
    have hA2 : A ^ 2 ≤ 463 ^ 2 := pow_le_pow_left₀ hA0 hc 2
    have hd2 : 464 ^ 2 < ‖x - y‖ ^ 2 := by
      rw [← dist_eq_norm, dist_comm]
      exact pow_lt_pow_left₀ hfarx (by norm_num) two_ne_zero
    linarith
  have hApos : 0 < A := by linarith
  set t := 463 / A with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hApos]; linarith
  have htA : t * A = 463 := by rw [ht]; field_simp
  refine ⟨p₀ + t • (x - p₀), (KBall_convex X).add_smul_sub_mem hp₀K hxK ⟨ht0, ht1⟩, ?_, ?_⟩
  · have e : p₀ + t • (x - p₀) - y = h • n + t • ((x - y) - h • n) := by rw [hxp, hp₀]; abel
    rw [e, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_sub_left,
      real_inner_smul_left, hnp, ← hP, hPA]
    have : t * (σ * A - h * 0) = σ * (t * A) := by ring
    rw [this, htA]; ring
  · have e : p₀ + t • (x - p₀) - y = h • n + t • ((x - y) - h • n) := by rw [hxp, hp₀]; abel
    rw [e, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_sub_left,
      real_inner_smul_left, hnn, ← hC]
    have hm := mul_le_mul_of_nonneg_left (by linarith : -(κ * A) ≤ C - h) ht0
    have hk : t * -(κ * A) = -(κ * (t * A)) := by ring
    rw [hk, htA, hκ] at hm
    linarith

/-- **The frame at a good heavy point** (§1.2).

TODO: none — proved from the statements (wiring).
Acceptance: no `sorry` (inherits).
Depends on: `heavy_interior`, `exists_foot`, `heavy_depth_le`, `good_normals`, `far_points`. -/
theorem frame_of_good (hX : Normal X) {y : Pt} (hy : y ∈ heavy X) (hg : IsGood43 X y) :
    ∃ n, Frame43 X y n := by
  have hint := heavy_interior hX hy
  obtain ⟨n, hn, hpos, hfoot, hnorm⟩ := exists_foot hX hint
  have hle := heavy_depth_le hX hy
  have hd : dist y (y + depth X y • n) ≤ 1 := by
    rw [dist_eq_norm, show y - (y + depth X y • n) = -(depth X y • n) by abel, norm_neg,
      norm_smul, hn, mul_one, Real.norm_eq_abs, abs_of_pos hpos]
    exact hle
  exact ⟨n, ⟨hn, hint, hpos, hle, hfoot, hnorm, good_normals hg hfoot hd hnorm hn,
    far_points hX hg (interior_subset hint) hn hpos.le hle hfoot hnorm⟩⟩

/-! ## Exceptions: thin case -/

/-- **Box packing**: points pairwise `≥ 1` apart in a box `[c₀, c₀ + L] × [c₁, c₁ + W]` of the
orthonormal frame `(e, perp e)` number at most `(2L + 1)(2W + 1)`.

TODO: none — proved.
What's missing: grid pigeonhole with cells of side `1/2` (diameter `√2/2 < 1`), as in
`card_sep_box_le`/`card_sep_ball_le`: `x ↦ (⌊2(⟨x,e⟩ − c₀)⌋, ⌊2(⟨x,perp e⟩ − c₁)⌋)` is
injective into `[0, ⌊2L⌋] × [0, ⌊2W⌋]`; `‖x − x'‖² = ⟨x−x',e⟩² + ⟨x−x',perp e⟩²`
(`n1_norm_sq_frame`).
Acceptance: no `sorry`.
Depends on: `n1_norm_sq_frame`, `card_le_card_of_injOn`. Difficulty M. -/
theorem card_sep_box_le43 {P : Finset Pt} (hsep : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → 1 ≤ dist a b)
    {e : Pt} (he : ‖e‖ = 1) {c₀ c₁ L W : ℝ} (hL : 0 ≤ L) (hW : 0 ≤ W)
    (hbox : ∀ x ∈ P, c₀ ≤ inner ℝ x e ∧ inner ℝ x e ≤ c₀ + L ∧
      c₁ ≤ inner ℝ x (perp e) ∧ inner ℝ x (perp e) ≤ c₁ + W) :
    (P.card : ℝ) ≤ (2 * L + 1) * (2 * W + 1) := by
  let f : Pt → ℕ × ℕ := fun a =>
    (⌊2 * (inner ℝ a e - c₀)⌋₊, ⌊2 * (inner ℝ a (perp e) - c₁)⌋₊)
  have hmaps : ∀ a ∈ P, f a ∈ (range (⌊2 * L⌋₊ + 1)) ×ˢ (range (⌊2 * W⌋₊ + 1)) := by
    intro a ha
    obtain ⟨h1, h2, h3, h4⟩ := hbox a ha
    simp only [f, mem_product, mem_range, Nat.lt_succ_iff]
    exact ⟨Nat.floor_mono (by linarith), Nat.floor_mono (by linarith)⟩
  have hclose : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → ⌊u⌋₊ = ⌊v⌋₊ → |u - v| < 1 := by
    intro u v hu hv huv
    have a1 := Nat.floor_le hu
    have a2 := Nat.lt_floor_add_one u
    have b1 := Nat.floor_le hv
    have b2 := Nat.lt_floor_add_one v
    rw [huv] at a1 a2
    rw [abs_lt]; constructor <;> linarith
  have := card_le_card_of_injOn f hmaps (fun a ha b hb hfe => by
    by_contra hab
    have h1 := hsep a ha b hb hab
    simp only [f, Prod.mk.injEq] at hfe
    obtain ⟨a1, -, a3, -⟩ := hbox a ha
    obtain ⟨b1, -, b3, -⟩ := hbox b hb
    have d0 := hclose _ _ (by linarith) (by linarith) hfe.1
    have d1 := hclose _ _ (by linarith) (by linarith) hfe.2
    have e0 : 2 * (inner ℝ a e - c₀) - 2 * (inner ℝ b e - c₀) = 2 * inner ℝ (a - b) e := by
      rw [inner_sub_left]; ring
    have e1 : 2 * (inner ℝ a (perp e) - c₁) - 2 * (inner ℝ b (perp e) - c₁) =
        2 * inner ℝ (a - b) (perp e) := by
      rw [inner_sub_left]; ring
    rw [e0, abs_mul, abs_two] at d0; rw [e1, abs_mul, abs_two] at d1
    have hn := n1_norm_sq_frame he (a - b)
    rw [← dist_eq_norm] at hn
    have := sq_abs (inner ℝ (a - b) e); have := sq_abs (inner ℝ (a - b) (perp e))
    have : dist a b ^ 2 < 1 := by
      rw [hn]
      nlinarith [abs_nonneg (inner ℝ (a - b) e), abs_nonneg (inner ℝ (a - b) (perp e))]
    nlinarith [dist_nonneg (x := a) (y := b)])
  rw [card_product, card_range, card_range] at this
  have hc : (P.card : ℝ) ≤ ((⌊2 * L⌋₊ : ℝ) + 1) * ((⌊2 * W⌋₊ : ℝ) + 1) := by
    exact_mod_cast this
  have fL := Nat.floor_le (by linarith : (0 : ℝ) ≤ 2 * L)
  have fW := Nat.floor_le (by linarith : (0 : ℝ) ≤ 2 * W)
  refine hc.trans (mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith))

/-- **Lemma T at scale `Λ`** (fatness step, §1.1 Lemma T* with `|b₁b₂| ≤ 2Λ`): if two boundary
points within `Λ = 464` of `y ∈ K` have nearly antipodal unit normals and `Δ₂ ≥ 10⁶`, then
`K` lies in a box of length `2·10⁵` and width `5000`.

TODO: none — proved.
What's missing: rerun the proof of `thin_box` with `1 ↦ Λ`.  Frame `e = −perp ν₁`
(`perp e = ν₁`), heights `H = ⟨·, ν₁⟩`, lengths `S = ⟨·, e⟩`, `L = max S − min S` on `K`.
`K ⊂ {H ≤ H(b₁)}`; `‖ν₁ + ν₂‖ ≤ √(2·10⁻⁴) < 1/70` and `⟨x − b₂, ν₂⟩ ≤ 0` give
`H(x) ≥ H(b₂) − |S(x) − S(b₂)|/69`; `H(b₁) − H(b₂) ≤ |b₁b₂| ≤ 2Λ`.  So the height range is
`W ≤ 928 + L/69`.  If `L ≥ 146400` then `W ≤ L/48`, and the middle-slice argument
(`n1_mid_interior`, `n1_slice_extreme`, `n1_circle_normal`, `n1_tilt`) gives circle centres
`w_top, w_bot ∈ X` with `|w_bot − w_top| ≥ 1.998Δ₂ − W`; since `L ≤ diam K ≤ 2Δ₂` and
`Δ₂ ≥ 10⁶`, `W ≤ 928 + 2Δ₂/69 < 0.058Δ₂`, so `|w_bot − w_top| > 1.94Δ₂ ≥ Δ`, contradiction.
Hence `L < 146400 ≤ 2·10⁵` and `W ≤ 928 + 146400/69 < 5000`.  (Why `Δ₂ ≥ 10⁶`: with only
`Δ₂ ≥ 10⁴` the width `W ≈ 4000` is not `≪ Δ₂`; the small-`Δ₂` case is handled by packing in
`thin_card_le43`.)
Acceptance: no `sorry`.
Depends on: `thin_box` (proof pattern), `n1_tilt`, `n1_slice_extreme`, `n1_circle_normal`,
`n1_mid_interior`, `frontier_on_circle`, `KBall_isCompact`. Difficulty L. -/
theorem thin_box43 (hX : Normal X) (hlarge : 10 ^ 6 ≤ dist2 X) {y b₁ b₂ ν₁ ν₂ : Pt}
    (hy : y ∈ KBall X) (hb₁ : b₁ ∈ frontier (KBall X)) (hb₂ : b₂ ∈ frontier (KBall X))
    (h₁ : dist y b₁ ≤ Lam43) (h₂ : dist y b₂ ≤ Lam43)
    (hν₁ : ν₁ ∈ normalCone (KBall X) b₁) (hν₂ : ν₂ ∈ normalCone (KBall X) b₂)
    (hn₁ : ‖ν₁‖ = 1) (hn₂ : ‖ν₂‖ = 1) (hthin : inner ℝ ν₁ ν₂ ≤ -(1 - 1 / 10 ^ 4)) :
    ∃ e : Pt, ‖e‖ = 1 ∧ ∃ c₀ c₁ : ℝ, ∀ x ∈ KBall X,
      c₀ ≤ inner ℝ x e ∧ inner ℝ x e ≤ c₀ + 2 * 10 ^ 5 ∧
        c₁ ≤ inner ℝ x (perp e) ∧ inner ℝ x (perp e) ≤ c₁ + 5000 := by
  have hne : X.Nonempty := card_pos.1 (by have := hX.four_le; omega)
  have hKc := KBall_isCompact hne
  have hD := hlarge
  unfold Lam43 at h₁ h₂
  have hΔ := hX.nondeg
  have hDpos : 0 < dist2 X := by linarith
  -- the frame `(e, ν₁)`
  set e : Pt := -perp ν₁ with hedef
  have hpe : perp e = ν₁ := by
    rw [hedef, perp_neg, pt_ext_iff]; simp [perp]
  have he : ‖e‖ = 1 := by rw [hedef, norm_neg, norm_perp, hn₁]
  have hframe : ∀ w₁ w₂ : Pt,
      inner ℝ w₁ w₂ = inner ℝ w₁ e * inner ℝ w₂ e + inner ℝ w₁ ν₁ * inner ℝ w₂ ν₁ := by
    intro w₁ w₂; rw [← hpe]; exact n1_inner_frame he w₁ w₂
  have hnsq : ∀ w : Pt, ‖w‖ ^ 2 = inner ℝ w e ^ 2 + inner ℝ w ν₁ ^ 2 := by
    intro w; rw [← hpe, norm_sq_frame he, det2_eq_inner_perp]
  have horth : inner ℝ ν₁ e = 0 := by
    have h := hnsq ν₁
    rw [hn₁, real_inner_self_eq_norm_sq, hn₁] at h
    have : inner ℝ ν₁ e ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  -- `ν₂ ≈ −ν₁`
  have hε : ‖ν₁ + ν₂‖ ≤ 3 / 200 := by
    have h := norm_add_sq_real ν₁ ν₂
    rw [hn₁, hn₂] at h
    nlinarith [norm_nonneg (ν₁ + ν₂)]
  have hb₁K : b₁ ∈ KBall X := (KBall_isClosed X).closure_eq ▸ hb₁.1
  have hb₂K : b₂ ∈ KBall X := (KBall_isClosed X).closure_eq ▸ hb₂.1
  have hsplit : ∀ (x b' ν : Pt), inner ℝ (x - y) ν = inner ℝ (x - b') ν + inner ℝ (b' - y) ν := by
    intro x b' ν; rw [← inner_add_left]; congr 1; abel
  have hbd : ∀ b' ν : Pt, dist y b' ≤ 464 → ‖ν‖ = 1 → inner ℝ (b' - y) ν ≤ 464 := by
    intro b' ν hb' hν
    refine (real_inner_le_norm _ _).trans ?_
    rw [hν, mul_one, ← dist_eq_norm, dist_comm]; exact hb'
  have up₁ : ∀ x ∈ KBall X, inner ℝ (x - y) ν₁ ≤ 464 := by
    intro x hx; rw [hsplit x b₁]; linarith [hν₁ x hx, hbd b₁ ν₁ h₁ hn₁]
  have up₂ : ∀ x ∈ KBall X, inner ℝ (x - y) ν₂ ≤ 464 := by
    intro x hx; rw [hsplit x b₂]; linarith [hν₂ x hx, hbd b₂ ν₂ h₂ hn₂]
  have lo₁ : ∀ x ∈ KBall X, -464 - 3 / 200 * ‖x - y‖ ≤ inner ℝ (x - y) ν₁ := by
    intro x hx
    have h2 := up₂ x hx
    have hs : inner ℝ (x - y) ν₂ = inner ℝ (x - y) (ν₁ + ν₂) - inner ℝ (x - y) ν₁ := by
      rw [inner_add_right]; ring
    have hcs := (abs_le.1 (abs_real_inner_le_norm (x - y) (ν₁ + ν₂))).1
    have : ‖x - y‖ * ‖ν₁ + ν₂‖ ≤ ‖x - y‖ * (3 / 200) :=
      mul_le_mul_of_nonneg_left hε (norm_nonneg _)
    linarith
  -- extreme levels along `e`
  have hcont : Continuous fun z : Pt => inner ℝ z e := continuous_id.inner continuous_const
  obtain ⟨xm, hxm, hmin⟩ := hKc.exists_isMinOn ⟨y, hy⟩ hcont.continuousOn
  obtain ⟨xp, hxp, hmax⟩ := hKc.exists_isMaxOn ⟨y, hy⟩ hcont.continuousOn
  have hsK : ∀ x ∈ KBall X, inner ℝ xm e ≤ inner ℝ x e ∧ inner ℝ x e ≤ inner ℝ xp e :=
    fun x hx => ⟨hmin hx, hmax hx⟩
  set L := inner ℝ xp e - inner ℝ xm e with hLdef
  have hL0 : 0 ≤ L := by have := hsK y hy; linarith
  have hnorm : ∀ x ∈ KBall X, 197 / 200 * ‖x - y‖ ≤ L + 464 := by
    intro x hx
    have h1 := hnsq (x - y)
    have hs : |inner ℝ (x - y) e| ≤ L := by
      rw [inner_sub_left, abs_le]
      have := hsK x hx; have := hsK y hy
      constructor <;> linarith
    have hh : |inner ℝ (x - y) ν₁| ≤ 464 + 3 / 200 * ‖x - y‖ :=
      abs_le.2 ⟨by linarith [lo₁ x hx], by linarith [up₁ x hx, norm_nonneg (x - y)]⟩
    have hsq : ‖x - y‖ ^ 2 ≤ (|inner ℝ (x - y) e| + |inner ℝ (x - y) ν₁|) ^ 2 := by
      rw [h1]
      nlinarith [abs_nonneg (inner ℝ (x - y) e), abs_nonneg (inner ℝ (x - y) ν₁),
        sq_abs (inner ℝ (x - y) e), sq_abs (inner ℝ (x - y) ν₁)]
    have := (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
    linarith
  have hlow : ∀ x ∈ KBall X, inner ℝ y ν₁ - 464 - (L + 464) / 64 ≤ inner ℝ x ν₁ := by
    intro x hx
    have h1 := lo₁ x hx
    have h2 := hnorm x hx
    rw [inner_sub_left] at h1
    nlinarith [norm_nonneg (x - y)]
  have hup : ∀ x ∈ KBall X, inner ℝ x ν₁ ≤ inner ℝ y ν₁ + 464 := by
    intro x hx; have := up₁ x hx; rw [inner_sub_left] at this; linarith
  -- **the fatness step**: `L ≤ 400`
  have hL : L ≤ 180000 := by
    by_contra hL
    push Not at hL
    set W := 928 + (L + 464) / 64 with hWdef
    have hW0 : 0 ≤ W := by positivity
    have hWL : W ≤ L / 48 := by rw [hWdef]; linarith
    have hwid : ∀ x ∈ KBall X, ∀ z ∈ KBall X, -W ≤ inner ℝ x ν₁ - inner ℝ z ν₁ := by
      intro x hx z hz; have := hlow x hx; have := hup z hz; rw [hWdef]; linarith
    have hne' : xm ≠ xp := by rintro h; rw [h] at hLdef; linarith
    set m : Pt := (1 / 2 : ℝ) • (xm + xp) with hmdef
    have hmI : m ∈ interior (KBall X) := n1_mid_interior hxm hxp hne'
    have hmK : m ∈ KBall X := interior_subset hmI
    have hms : inner ℝ m e = (inner ℝ xm e + inner ℝ xp e) / 2 := by
      rw [hmdef, inner_smul_left, inner_add_left]; simp; ring
    clear_value m
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hmI)
    have hshift : ∀ σ : ℝ, |σ| = 1 → m + (r / 2) • (σ • ν₁) ∈ KBall X := by
      intro σ hσ
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_smul, hn₁,
        Real.norm_eq_abs σ, hσ, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    have hshs : ∀ σ : ℝ, inner ℝ (m + (r / 2) • (σ • ν₁)) e = inner ℝ m e := by
      intro σ; rw [inner_add_left, inner_smul_left, inner_smul_left, horth]; simp
    have hshh : ∀ σ : ℝ, inner ℝ (m + (r / 2) • (σ • ν₁)) ν₁ = inner ℝ m ν₁ + r / 2 * σ := by
      intro σ
      rw [inner_add_left, inner_smul_left, inner_smul_left, real_inner_self_eq_norm_sq, hn₁]
      simp
    have hnν : ‖-ν₁‖ = 1 := by rw [norm_neg, hn₁]
    have hnorth : inner ℝ (-ν₁) e = 0 := by rw [inner_neg_left, horth, neg_zero]
    obtain ⟨pT, hpTF, hpTs, hpTmax⟩ := n1_slice_extreme hne hn₁ horth hmK
    obtain ⟨pB, hpBF, hpBs, hpBmax⟩ := n1_slice_extreme hne hnν hnorth hmK
    have hpTK : pT ∈ KBall X := (KBall_isClosed X).closure_eq ▸ hpTF.1
    have hpBK : pB ∈ KBall X := (KBall_isClosed X).closure_eq ▸ hpBF.1
    have hT : inner ℝ m ν₁ + r / 2 ≤ inner ℝ pT ν₁ := by
      have := hpTmax _ (hshift 1 (by simp)) (hshs 1)
      rw [hshh] at this; linarith
    have hB : inner ℝ pB ν₁ ≤ inner ℝ m ν₁ - r / 2 := by
      have := hpBmax _ (hshift (-1) (by simp)) (hshs (-1))
      rw [inner_neg_right, inner_neg_right, hshh] at this; linarith
    obtain ⟨wT, hwT, hdT, hnT⟩ := n1_circle_normal hX hpTF
    obtain ⟨wB, hwB, hdB, hnB⟩ := n1_circle_normal hX hpBF
    have hnormT : inner ℝ (pT - wT) e ^ 2 + inner ℝ (pT - wT) ν₁ ^ 2 = dist2 X ^ 2 := by
      rw [← hnsq, ← dist_eq_norm, hdT]
    have hnormB : (inner ℝ (pB - wB) e) ^ 2 + (-inner ℝ (pB - wB) ν₁) ^ 2 = dist2 X ^ 2 := by
      rw [neg_sq, ← hnsq, ← dist_eq_norm, hdB]
    have hexpT : ∀ z, inner ℝ (z - pT) (pT - wT) = (inner ℝ z e - inner ℝ pT e) *
        inner ℝ (pT - wT) e + (inner ℝ z ν₁ - inner ℝ pT ν₁) * inner ℝ (pT - wT) ν₁ := by
      intro z; rw [hframe (z - pT), inner_sub_left z pT e, inner_sub_left z pT ν₁]
    have hexpB : ∀ z, inner ℝ (z - pB) (pB - wB) = (inner ℝ z e - inner ℝ pB e) *
        inner ℝ (pB - wB) e + (inner ℝ z ν₁ - inner ℝ pB ν₁) * inner ℝ (pB - wB) ν₁ := by
      intro z; rw [hframe (z - pB), inner_sub_left z pB e, inner_sub_left z pB ν₁]
    have hLpos : 0 < L := by linarith
    -- top normal
    have sT : 0 ≤ inner ℝ (pT - wT) ν₁ := by
      have h := hnT pB hpBK
      rw [hexpT, hpBs, hpTs, sub_self, zero_mul, zero_add] at h
      by_contra hc; push Not at hc
      nlinarith
    have tT : 999 / 1000 * dist2 X ≤ inner ℝ (pT - wT) ν₁ := by
      have hp := hnT xp hxp
      have hm := hnT xm hxm
      rw [hexpT, hpTs, hms] at hp hm
      refine n1_tilt hLpos hW0 hWL hDpos hnormT sT (a := inner ℝ xp ν₁ - inner ℝ pT ν₁)
        (b := inner ℝ xm ν₁ - inner ℝ pT ν₁) ?_ ?_ (hwid xp hxp pT hpTK) (hwid xm hxm pT hpTK)
      · have : inner ℝ xp e - (inner ℝ xm e + inner ℝ xp e) / 2 = L / 2 := by rw [hLdef]; ring
        rw [this] at hp; exact hp
      · have : inner ℝ xm e - (inner ℝ xm e + inner ℝ xp e) / 2 = -(L / 2) := by rw [hLdef]; ring
        rw [this] at hm; exact hm
    -- bottom normal
    have sB : 0 ≤ -inner ℝ (pB - wB) ν₁ := by
      have h := hnB pT hpTK
      rw [hexpB, hpBs, hpTs, sub_self, zero_mul, zero_add] at h
      by_contra hc; push Not at hc
      nlinarith
    have tB : 999 / 1000 * dist2 X ≤ -inner ℝ (pB - wB) ν₁ := by
      have hp := hnB xp hxp
      have hm := hnB xm hxm
      rw [hexpB, hpBs, hms] at hp hm
      refine n1_tilt hLpos hW0 hWL hDpos hnormB sB (ns := inner ℝ (pB - wB) e)
        (a := inner ℝ pB ν₁ - inner ℝ xp ν₁)
        (b := inner ℝ pB ν₁ - inner ℝ xm ν₁) ?_ ?_ (hwid pB hpBK xp hxp) (hwid pB hpBK xm hxm)
      · have : inner ℝ xp e - (inner ℝ xm e + inner ℝ xp e) / 2 = L / 2 := by rw [hLdef]; ring
        rw [this] at hp
        have e2 : (inner ℝ pB ν₁ - inner ℝ xp ν₁) * -inner ℝ (pB - wB) ν₁ =
            (inner ℝ xp ν₁ - inner ℝ pB ν₁) * inner ℝ (pB - wB) ν₁ := by ring
        rw [e2]; exact hp
      · have : inner ℝ xm e - (inner ℝ xm e + inner ℝ xp e) / 2 = -(L / 2) := by rw [hLdef]; ring
        rw [this] at hm
        have e2 : (inner ℝ pB ν₁ - inner ℝ xm ν₁) * -inner ℝ (pB - wB) ν₁ =
            (inner ℝ xm ν₁ - inner ℝ pB ν₁) * inner ℝ (pB - wB) ν₁ := by ring
        rw [e2]; exact hm
    -- the two centres are too far apart
    have hcent : inner ℝ (wB - wT) ν₁ ≤ 1.94 * dist2 X := by
      refine (real_inner_le_norm _ _).trans ?_
      rw [hn₁, mul_one, ← dist_eq_norm]
      exact (dist_le_diam hwB hwT).trans hΔ
    have hcent' : inner ℝ (wB - wT) ν₁ =
        (inner ℝ pB ν₁ - inner ℝ pT ν₁) - inner ℝ (pB - wB) ν₁ + inner ℝ (pT - wT) ν₁ := by
      simp only [inner_sub_left]; ring
    have hLD : L ≤ 2 * dist2 X := by
      obtain ⟨w, hw⟩ := hne
      have h1 := (mem_KBall.1 hxp) w hw
      have h2 := (mem_KBall.1 hxm) w hw
      have h3 : inner ℝ (xp - xm) e ≤ ‖xp - xm‖ := by
        refine (real_inner_le_norm _ _).trans ?_; rw [he, mul_one]
      rw [← dist_eq_norm] at h3
      have h4 := dist_triangle xp w xm
      rw [dist_comm w xm] at h4
      rw [hLdef, ← inner_sub_left]; linarith
    have := hwid pB hpBK pT hpTK
    rw [hWdef] at this
    linarith
  refine ⟨e, he, inner ℝ xm e, inner ℝ y ν₁ - 464 - (L + 464) / 64, fun x hx => ?_⟩
  rw [hpe]
  refine ⟨(hsK x hx).1, by linarith [(hsK x hx).2], hlow x hx, ?_⟩
  linarith [hup x hx]

/-- Small `Δ₂`: `X ∖ D ⊂ K ⊂ B̄(w, Δ₂)` for any `w ∈ X`, so packing bounds `|X ∖ D|`.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `ball_polygon_a`, `card_sep_ball_le`, `one_le_dist`. Difficulty S. -/
theorem card_notD_le_of_small (hX : Normal X) (hs : dist2 X < 10 ^ 6) :
    ((X \ Dset X).card : ℝ) ≤ (4 * 10 ^ 6 + 1) ^ 2 := by
  have hne : X.Nonempty := card_pos.1 (by have := hX.four_le; omega)
  obtain ⟨w, hw⟩ := hne
  have h := card_sep_ball_le (P := X \ Dset X)
    (fun a ha b hb hab => one_le_dist hX.minDist_eq (mem_sdiff.1 ha).1 (mem_sdiff.1 hb).1 hab)
    w (10 ^ 6) (fun a ha => by
      have hK := ball_polygon_a (mem_sdiff.1 ha).1 (mem_sdiff.1 ha).2
      have := Set.mem_iInter₂.1 hK w (by simpa using hw)
      rw [Metric.mem_closedBall] at this
      push_cast; linarith)
  exact_mod_cast h

/-- **Thin case count**: nearly antipodal normals at two boundary points within `Λ` of
`y ∈ K` give `|X ∖ D| ≤ cThin43 = 10¹⁴`.

TODO: none — proved from the statements (wiring).
Acceptance: no `sorry` (inherits).
Depends on: `card_notD_le_of_small`, `thin_box43`, `card_sep_box_le43`, `ball_polygon_a`. -/
theorem thin_card_le43 (hX : Normal X) {y b₁ b₂ ν₁ ν₂ : Pt} (hy : y ∈ KBall X)
    (hb₁ : b₁ ∈ frontier (KBall X)) (hb₂ : b₂ ∈ frontier (KBall X))
    (h₁ : dist y b₁ ≤ Lam43) (h₂ : dist y b₂ ≤ Lam43)
    (hν₁ : ν₁ ∈ normalCone (KBall X) b₁) (hν₂ : ν₂ ∈ normalCone (KBall X) b₂)
    (hn₁ : ‖ν₁‖ = 1) (hn₂ : ‖ν₂‖ = 1) (hthin : inner ℝ ν₁ ν₂ ≤ -(1 - 1 / 10 ^ 4)) :
    ((X \ Dset X).card : ℝ) ≤ cThin43 := by
  by_cases hs : dist2 X < 10 ^ 6
  · have := card_notD_le_of_small hX hs
    norm_num [cThin43] at this ⊢
    linarith
  · push Not at hs
    obtain ⟨e, he, c₀, c₁, hbox⟩ :=
      thin_box43 hX hs hy hb₁ hb₂ h₁ h₂ hν₁ hν₂ hn₁ hn₂ hthin
    have hsep : ∀ a ∈ X \ Dset X, ∀ b ∈ X \ Dset X, a ≠ b → 1 ≤ dist a b :=
      fun a ha b hb hab =>
        one_le_dist hX.minDist_eq (mem_sdiff.1 ha).1 (mem_sdiff.1 hb).1 hab
    have := card_sep_box_le43 hsep he (by norm_num : (0 : ℝ) ≤ 2 * 10 ^ 5)
      (by norm_num : (0 : ℝ) ≤ 5000) (c₀ := c₀) (c₁ := c₁)
      (fun x hx => hbox x (ball_polygon_a (mem_sdiff.1 hx).1 (mem_sdiff.1 hx).2))
    norm_num [cThin43] at this ⊢
    linarith

/-! ## Exceptions: big turning -/

/-- Helper (Lemma BT at scale `Λ`, support points): adaptation of `n1_support_near` with
`1 ↦ Λ = 464`, `150 ↦ 150Λ = 69600`. -/
private theorem support_near43 (hX : Normal X) {y b₁ b₂ ν₁ ν₂ d : Pt} (hyK : y ∈ KBall X)
    (hb₁ : b₁ ∈ frontier (KBall X)) (hb₂ : b₂ ∈ frontier (KBall X))
    (h₁ : dist y b₁ ≤ Lam43) (h₂ : dist y b₂ ≤ Lam43)
    (hν₁ : ν₁ ∈ normalCone (KBall X) b₁) (hν₂ : ν₂ ∈ normalCone (KBall X) b₂)
    (hn₁ : ‖ν₁‖ = 1) (hn₂ : ‖ν₂‖ = 1) (hc : |inner ℝ ν₁ ν₂| ≤ 1 - 1 / 10 ^ 4)
    (hd : ‖d‖ = 1) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hdab : d = a • ν₁ + b • ν₂) :
    ∃ x ∈ bdryNear43 X y, d ∈ normalCone (KBall X) x := by
  have hne : X.Nonempty := card_pos.1 (by have := hX.four_le; omega)
  have hb₁K : b₁ ∈ KBall X := (KBall_isClosed X).closure_eq ▸ hb₁.1
  have hb₂K : b₂ ∈ KBall X := (KBall_isClosed X).closure_eq ▸ hb₂.1
  unfold Lam43 at h₁ h₂
  have hbd : ∀ b' ν : Pt, dist y b' ≤ 464 → ‖ν‖ = 1 → |inner ℝ (b' - y) ν| ≤ 464 := by
    intro b' ν hb' hν
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [hν, mul_one, ← dist_eq_norm, dist_comm]; exact hb'
  rcases ha.eq_or_lt with ha0 | ha0
  · subst ha0
    have hb1 : b = 1 := by
      rw [hdab, zero_smul, zero_add, norm_smul, hn₂, mul_one, Real.norm_eq_abs,
        abs_of_nonneg hb] at hd
      exact hd
    refine ⟨b₂, ⟨hb₂, ?_⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_comm]; linarith
    · rw [hdab, hb1, zero_smul, zero_add, one_smul]; exact hν₂
  rcases hb.eq_or_lt with hb0 | hb0
  · subst hb0
    have ha1 : a = 1 := by
      rw [hdab, zero_smul, add_zero, norm_smul, hn₁, mul_one, Real.norm_eq_abs,
        abs_of_nonneg ha] at hd
      exact hd
    refine ⟨b₁, ⟨hb₁, ?_⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_comm]; linarith
    · rw [hdab, ha1, zero_smul, add_zero, one_smul]; exact hν₁
  obtain ⟨x, hxK, hxmax⟩ := (KBall_isCompact hne).exists_isMaxOn ⟨y, hyK⟩
    (continuous_id.inner continuous_const : Continuous fun z : Pt => inner ℝ z d).continuousOn
  have hmax : ∀ z ∈ KBall X, inner ℝ z d ≤ inner ℝ x d := fun z hz => hxmax hz
  have hxF : x ∈ frontier (KBall X) := mem_frontier_of_max hxK hd hmax
  have hxN : d ∈ normalCone (KBall X) x := fun z hz => by
    rw [inner_sub_left]; linarith [hmax z hz]
  refine ⟨x, ⟨hxF, ?_⟩, hxN⟩
  have u₁ : inner ℝ (x - b₁) ν₁ ≤ 0 := hν₁ x hxK
  have u₂ : inner ℝ (x - b₂) ν₂ ≤ 0 := hν₂ x hxK
  have m₁ : 0 ≤ inner ℝ (x - b₁) d := by rw [inner_sub_left]; linarith [hmax b₁ hb₁K]
  have m₂ : 0 ≤ inner ℝ (x - b₂) d := by rw [inner_sub_left]; linarith [hmax b₂ hb₂K]
  rw [hdab, inner_add_right, inner_smul_right, inner_smul_right] at m₁ m₂
  have l₂ : 0 ≤ inner ℝ (x - b₁) ν₂ := by
    by_contra hneg; push Not at hneg
    have := mul_neg_of_pos_of_neg hb0 hneg
    nlinarith
  have l₁ : 0 ≤ inner ℝ (x - b₂) ν₁ := by
    by_contra hneg; push Not at hneg
    have := mul_neg_of_pos_of_neg ha0 hneg
    nlinarith
  have e : ∀ (b' ν : Pt), inner ℝ (x - y) ν = inner ℝ (x - b') ν + inner ℝ (b' - y) ν := by
    intro b' ν; rw [← inner_add_left]; congr 1; abel
  have s₁ : |inner ℝ (x - y) ν₁| ≤ 464 := by
    rw [abs_le]
    have := abs_le.1 (hbd b₁ ν₁ h₁ hn₁); have := abs_le.1 (hbd b₂ ν₁ h₂ hn₁)
    constructor
    · rw [e b₂ ν₁]; linarith
    · rw [e b₁ ν₁]; linarith
  have s₂ : |inner ℝ (x - y) ν₂| ≤ 464 := by
    rw [abs_le]
    have := abs_le.1 (hbd b₁ ν₂ h₁ hn₂); have := abs_le.1 (hbd b₂ ν₂ h₂ hn₂)
    constructor
    · rw [e b₁ ν₂]; linarith
    · rw [e b₂ ν₂]; linarith
  have hsc : ∀ ν : Pt, |inner ℝ (x - y) ν| ≤ 464 →
      |inner ℝ ((1 / 464 : ℝ) • (x - y)) ν| ≤ 1 := by
    intro ν hν
    rw [real_inner_smul_left, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 464)]
    linarith
  have hv := norm_le_of_inner_bounds hn₁ hn₂ hc (hsc ν₁ s₁) (hsc ν₂ s₂)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 464)] at hv
  rw [Metric.mem_closedBall, dist_eq_norm]
  linarith

/-- **Non-good, non-thin ⇒ big turning** (Lemma BT at scale `Λ`): if two boundary points within
`Λ` of `y ∈ K` carry unit normals with `‖ν₁ − ν₂‖ > ε₀` and `ν₁·ν₂ > −(1 − 10⁻⁴)`, then
`turning(K, ∂K ∩ B̄(y, 69600)) ≥ ε₀`.

TODO: none — proved.
What's missing: copy `turning_ge_of_nonflat` / `n1_support_near` with `1 ↦ Λ`:
`|ν₁·ν₂| ≤ 1 − 10⁻⁴` (upper side: `‖ν₁ − ν₂‖² > 1/2500` gives `ν₁·ν₂ < 1 − 1/5000`); a support
point `x` in a direction `d = aν₁ + bν₂` (`a, b ≥ 0`) has `|⟨x − y, ν_i⟩| ≤ Λ`, hence
`‖x − y‖ ≤ 150Λ = 69600` (`norm_le_of_inner_bounds` applied to `(x − y)/Λ`); the short arc
between `ν₁, ν₂` has length `∠(ν₁,ν₂) ≥ ‖ν₁ − ν₂‖ > ε₀` (`norm_sub_le_ang`);
`le_turning_of_Icc`.
Acceptance: no `sorry`.
Depends on: `norm_le_of_inner_bounds`, `n1_dirVec_arc`, `le_turning_of_Icc`,
`mem_frontier_of_max`, `exists_dirVec_pair`, `norm_sub_le_ang`, `KBall_isCompact`.
Difficulty M. -/
theorem turning_ge43 (hX : Normal X) {y b₁ b₂ ν₁ ν₂ : Pt} (hy : y ∈ KBall X)
    (hb₁ : b₁ ∈ frontier (KBall X)) (hb₂ : b₂ ∈ frontier (KBall X))
    (h₁ : dist y b₁ ≤ Lam43) (h₂ : dist y b₂ ≤ Lam43)
    (hν₁ : ν₁ ∈ normalCone (KBall X) b₁) (hν₂ : ν₂ ∈ normalCone (KBall X) b₂)
    (hn₁ : ‖ν₁‖ = 1) (hn₂ : ‖ν₂‖ = 1) (hfar : ε₀43 < ‖ν₁ - ν₂‖)
    (hnt : -(1 - 1 / 10 ^ 4) < inner ℝ ν₁ ν₂) :
    ε₀43 ≤ turning (KBall X) (bdryNear43 X y) := by
  unfold ε₀43 at hfar ⊢
  have hc_hi : inner ℝ ν₁ ν₂ < 1 - 1 / 5000 := by
    have := norm_sub_sq_real ν₁ ν₂
    rw [hn₁, hn₂] at this
    nlinarith [norm_nonneg (ν₁ - ν₂)]
  have hc : |inner ℝ ν₁ ν₂| ≤ 1 - 1 / 10 ^ 4 := abs_le.2 ⟨by linarith, by linarith⟩
  set α := ang ν₁ ν₂ with hαdef
  have hα1 : 1 / 50 < α := lt_of_lt_of_le hfar (norm_sub_le_ang hn₁ hn₂)
  have hαπ : α < π := by
    have hle : α ≤ π := InnerProductGeometry.angle_le_pi _ _
    refine lt_of_le_of_ne hle fun h => ?_
    have := cos_ang_unit hn₁ hn₂
    rw [← hαdef, h, Real.cos_pi] at this
    linarith
  have hα0 : 0 < α := by linarith
  have hsupp := fun (d : Pt) (hd : ‖d‖ = 1) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (hdab : d = a • ν₁ + b • ν₂) =>
    support_near43 hX hy hb₁ hb₂ h₁ h₂ hν₁ hν₂ hn₁ hn₂ hc hd ha hb hdab
  have key : ∀ c : ℝ, (dirVec c = ν₁ ∧ dirVec (c + α) = ν₂) ∨
      (dirVec c = ν₂ ∧ dirVec (c + α) = ν₁) → α ≤ turning (KBall X) (bdryNear43 X y) := by
    intro c hc'
    refine le_turning_of_Icc (c := c) hα0.le (by linarith) fun θ hθ => ?_
    obtain ⟨a, b, ha, hb, hab⟩ := n1_dirVec_arc (c := c) hα0 hαπ (t := θ - c)
      (by linarith [hθ.1]) (by linarith [hθ.2])
    rw [add_sub_cancel] at hab
    rcases hc' with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2] at hab
      exact hsupp _ (norm_dirVec θ) a b ha hb hab
    · rw [e1, e2, add_comm] at hab
      exact hsupp _ (norm_dirVec θ) b a hb ha hab
  obtain ⟨θ₁, σ, hσ, hd₁, hd₂⟩ := exists_dirVec_pair hn₁ hn₂
  rw [← hαdef] at hd₂
  rcases hσ with rfl | rfl
  · exact hα1.le.trans (key θ₁ (Or.inl ⟨hd₁, by simpa using hd₂⟩))
  · refine hα1.le.trans (key (θ₁ - α) (Or.inr ⟨?_, ?_⟩))
    · rw [← hd₂]; congr 1; ring
    · rw [← hd₁]; congr 1; ring

/-- **Lemma BT count at scale `Λ`**: at most `100π·278401²` points `y ∈ X` have
`turning(K, ∂K ∩ B̄(y, 69600)) ≥ ε₀` (`278401 = 4·69600 + 1`).

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `turning_sum_le`, `card_sep_ball_le`, `KBall_convex`, `KBall_isCompact`,
`one_le_dist`. Difficulty S. -/
theorem card_bigTurning_le43 (hX : Normal X) (Y : Finset Pt) (hY : Y ⊆ X)
    (hbig : ∀ y ∈ Y, ε₀43 ≤ turning (KBall X) (bdryNear43 X y)) :
    (Y.card : ℝ) ≤ 100 * π * 278401 ^ 2 := by
  have hne : X.Nonempty := card_pos.1 (by have := hX.four_le; omega)
  have hsep : ∀ a ∈ Y, ∀ b ∈ Y, a ≠ b → 1 ≤ dist a b := fun a ha b hb hab =>
    one_le_dist hX.minDist_eq (hY ha) (hY hb) hab
  have hsum := turning_sum_le (KBall_convex X) (KBall_isCompact hne) Y
    (fun y => bdryNear43 X y) (fun y _ => Set.inter_subset_left)
    (fun y _ => isClosed_frontier.inter Metric.isClosed_closedBall) (278401 ^ 2)
    (fun b => by
      have := card_sep_ball_le (P := Y.filter (fun y => b ∈ bdryNear43 X y))
        (fun a ha c hc hac => hsep a (mem_filter.1 ha).1 c (mem_filter.1 hc).1 hac) b 69600
        (fun a ha => by
          have h := (mem_filter.1 ha).2.2
          rw [Metric.mem_closedBall, dist_comm] at h
          push_cast; exact h)
      simpa using this)
  have hle : ∑ y ∈ Y, ε₀43 ≤ ∑ y ∈ Y, turning (KBall X) (bdryNear43 X y) :=
    sum_le_sum hbig
  rw [sum_const, nsmul_eq_mul] at hle
  push_cast at hsum
  unfold ε₀43 at hle
  linarith

/-- `100π·278401² + cThin43 ≤ cE43`.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem cE43_check : 100 * π * 278401 ^ 2 + cThin43 ≤ cE43 := by
  have := Real.pi_lt_d2
  norm_num [cThin43, cE43]
  nlinarith

/-- **Exceptions** (§1.1): at most `cE43` heavy points are not good.

TODO: none — proved from the statements (wiring, as `N1`).
Acceptance: no `sorry` (inherits).
Depends on: `heavy_not_D`, `heavy_interior`, `thin_card_le43`, `turning_ge43`,
`card_bigTurning_le43`, `cE43_check`. -/
theorem card_E43_le (hX : Normal X) : ((E43 X).card : ℝ) ≤ cE43 := by
  set E := E43 X with hE
  have hRX : Rset X ⊆ X := sdiff_subset
  have hEX : ∀ z ∈ E, z ∈ X := fun z hz => hRX (mem_filter.1 (mem_filter.1 hz).1).1
  have key : ∀ y ∈ E, y ∉ Dset X ∧ y ∈ interior (KBall X) ∧
      ∃ b₁ ∈ frontier (KBall X), ∃ b₂ ∈ frontier (KBall X), dist y b₁ ≤ Lam43 ∧
        dist y b₂ ≤ Lam43 ∧ ∃ ν₁ ∈ normalCone (KBall X) b₁, ∃ ν₂ ∈ normalCone (KBall X) b₂,
          ‖ν₁‖ = 1 ∧ ‖ν₂‖ = 1 ∧ ε₀43 < ‖ν₁ - ν₂‖ := by
    intro y hy
    obtain ⟨hyh, hg⟩ := mem_filter.1 hy
    refine ⟨heavy_not_D hX hyh, heavy_interior hX hyh, ?_⟩
    unfold IsGood43 at hg
    push Not at hg
    exact hg
  have hc := cE43_check
  have hπ := Real.pi_pos
  by_cases hthin : ∃ y ∈ E, ∃ b₁ ∈ frontier (KBall X), ∃ b₂ ∈ frontier (KBall X),
      dist y b₁ ≤ Lam43 ∧ dist y b₂ ≤ Lam43 ∧ ∃ ν₁ ∈ normalCone (KBall X) b₁,
        ∃ ν₂ ∈ normalCone (KBall X) b₂, ‖ν₁‖ = 1 ∧ ‖ν₂‖ = 1 ∧
          inner ℝ ν₁ ν₂ ≤ -(1 - 1 / 10 ^ 4)
  · obtain ⟨y, hy, b₁, hb₁, b₂, hb₂, hd₁, hd₂, ν₁, hν₁, ν₂, hν₂, hn₁, hn₂, hin⟩ := hthin
    have hyK := interior_subset (key y hy).2.1
    have h := thin_card_le43 hX hyK hb₁ hb₂ hd₁ hd₂ hν₁ hν₂ hn₁ hn₂ hin
    have hsub : E ⊆ X \ Dset X := fun z hz => mem_sdiff.2 ⟨hEX z hz, (key z hz).1⟩
    have : (E.card : ℝ) ≤ (X \ Dset X).card := by exact_mod_cast card_le_card hsub
    have : (0 : ℝ) ≤ 100 * π * 278401 ^ 2 := by positivity
    linarith
  · push Not at hthin
    have hbig : ∀ y ∈ E, ε₀43 ≤ turning (KBall X) (bdryNear43 X y) := by
      intro y hy
      obtain ⟨-, hint, b₁, hb₁, b₂, hb₂, hd₁, hd₂, ν₁, hν₁, ν₂, hν₂, hn₁, hn₂, hfar⟩ := key y hy
      have hnt := hthin y hy b₁ hb₁ b₂ hb₂ hd₁ hd₂ ν₁ hν₁ ν₂ hν₂ hn₁ hn₂
      exact turning_ge43 hX (interior_subset hint) hb₁ hb₂ hd₁ hd₂ hν₁ hν₂ hn₁ hn₂ hfar hnt
    have := card_bigTurning_le43 hX E (fun z hz => hEX z hz) hbig
    have : (0 : ℝ) ≤ cThin43 := by norm_num [cThin43]
    linarith

end

end Erdos132Main
