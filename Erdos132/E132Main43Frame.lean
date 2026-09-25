import Erdos132.E132Main43Defs

/-!
# Erdős Problem 132, `4/3` theorem — facts in the local frame (Lemma F′, Lemma DN)

Paper: `angle_R6.md` §1.2.  Everything is derived from the fields of `Frame43 X y n`
(`E132Main43Defs`); no arc length and no graph function `f` (see `MAIN43_PLAN.md`,
"Deviations").  Notation: `h = depth X y`, `Z q = ⟨q − y, n⟩` (height), `Xq = ⟨q − y, perp n⟩`
(abscissa), `t = tgap X`, `ε = ε43 = 1/49`.

| paper | here |
|---|---|
| (F′0) `K` below the support line at `p₀` | `Frame43.top` (Defs): `Z k ≤ h` |
| (F′1) `q ∉ int K` ⇒ `q_z ≥ f(q_x) ≥ −ε|q_x|` | `frame_outside`: `Z q ≥ h − ε|Xq|` |
| (F′0) `U′ ⊂ int K` | `frame_mem_interior` (contrapositive) |
| (F′3) D-points are `t` above the graph | `frame_D`: `Z z ≥ h + t − ε|Xz|` |
| (F′4) inward normals within `ε₀` of `−n₀` | `Frame43.normals` |
| Lemma DN (`τ₃ < 0.0267`, `τ* < 0.0224`) | `frame_dn` (`3/100`), `frame_dn1` (`9/400`) |
| Corollary D–D heights | `dd_heights` |

Plus the receiver facts used by `E132Main43Classify` and `E132Main43Charge`:
`Low_Z` (receivers have height `≤ −2/3`), `lower_mem_Low` (neighbours of height `≤ −4/5` are
receivers), `card_cone_le_two` (window packing).
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-! ## Neighbours and receivers: bookkeeping -/

/-- Membership in `nbδ`.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `mem_partners`. Difficulty S. -/
theorem mem_nbδ {y q : Pt} : q ∈ nbδ X y ↔ q ∈ X ∧ q ≠ y ∧ dist y q = minDist X :=
  mem_partners

/-- `δ`-neighbours are at distance `1` (normalised).

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `mem_nbδ`. Difficulty S. -/
theorem dist_of_mem_nbδ (hX : Normal X) {y q : Pt} (hq : q ∈ nbδ X y) : dist q y = 1 := by
  rw [dist_comm, (mem_nbδ.1 hq).2.2, hX.minDist_eq]

/-- Receivers are neighbours.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem Low_subset (X : Finset Pt) (y : Pt) : Low X y ⊆ nbδ X y := filter_subset _ _

/-- Receivers are interior to `K` (depth `≥ 2/3 > 0`).

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem Low_interior {y a : Pt} (ha : a ∈ Low X y) : a ∈ interior (KBall X) := by
  obtain ⟨-, haK, hd⟩ := mem_filter.1 ha
  have h0 : 0 ≤ depth X y := Metric.infDist_nonneg
  by_contra hint
  have hfr : a ∈ frontier (KBall X) := ⟨subset_closure haK, hint⟩
  have : depth X a = 0 := Metric.infDist_zero_of_mem hfr
  linarith

/-! ## Lemma F′ -/

/-- Helper: `⟨n, perp n⟩ = 0`. -/
private theorem inner_self_perp (n : Pt) : inner ℝ n (perp n) = 0 := by
  rw [← det2_eq_inner_perp]; unfold det2; ring

/-- Helper: a unit vector within `1/50` of the unit vector `n` has frame coefficients
`⟨ν, n⟩ ≥ 4999/5000` and `|⟨ν, perp n⟩| ≤ 1/50`. -/
private theorem near_coeffs {n ν : Pt} (hn : ‖n‖ = 1) (hν : ‖ν‖ = 1) (h : ‖ν - n‖ ≤ 1 / 50) :
    4999 / 5000 ≤ inner ℝ ν n ∧ |inner ℝ ν (perp n)| ≤ 1 / 50 := by
  have e := norm_sub_sq_real ν n
  rw [hν, hn] at e
  have h2 : ‖ν - n‖ ^ 2 ≤ (1 / 50) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  have hα : 4999 / 5000 ≤ inner ℝ ν n := by nlinarith
  have hf := n1_norm_sq_frame hn ν
  rw [hν] at hf
  have hα1 : inner ℝ ν n ≤ 1 := by nlinarith [sq_nonneg (inner ℝ ν (perp n))]
  refine ⟨hα, abs_le.2 ⟨?_, ?_⟩⟩ <;> nlinarith [sq_nonneg (inner ℝ ν (perp n))]

/-- **(F′1)** A point within `6` of `y` that is not interior to `K` is not below the frame's
tangent cone: `Z q ≥ h − ε|Xq|`.

TODO: none — proved.
What's missing: `exists_frontier_seg` (from `y ∈ int K` to `q`) gives `b = y + l(q − y)`,
`l ∈ (0, 1]`, on `∂K` with `dist y b ≤ 6`; a unit normal `ν` at `b` (`exists_unit_normal`) has
`‖ν − n‖ ≤ 1/50` (`hF.normals`).  `⟨q − b, ν⟩ = ((1−l)/l)⟨b − y, ν⟩ ≥ 0` (`y ∈ K`) and
`⟨b − p₀, ν⟩ ≥ 0` (`p₀ = y + h n ∈ K`), so `⟨q − p₀, ν⟩ ≥ 0`.  With `α = ⟨ν, n⟩ ≥ 1 − 1/5000`,
`|β| = |⟨ν, perp n⟩| ≤ 1/50` (from `‖ν − n‖ ≤ 1/50`; frame decomposition `n1_inner_frame`):
`α(Z q − h) + β Xq ≥ 0`, so `h − Z q ≤ |Xq|·(1/50)/(1 − 1/5000) ≤ |Xq|/49`.
Acceptance: no `sorry`.
Depends on: `exists_frontier_seg`, `exists_unit_normal`, `KBall_convex`, `KBall_isClosed`,
`Frame43` fields, `n1_inner_frame`, `norm_perp`. Difficulty M. -/
theorem frame_outside (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) {q : Pt}
    (hq : dist q y ≤ 6) (hqi : q ∉ interior (KBall X)) :
    depth X y - ε43 * |inner ℝ (q - y) (perp n)| ≤ inner ℝ (q - y) n := by
  obtain ⟨l, hl0, hl1, hb⟩ := exists_frontier_seg (KBall_isClosed X) hF.mem_int hqi
  obtain ⟨ν, hν1, hν⟩ := exists_unit_normal (KBall_convex X) ⟨y, hF.mem_int⟩ hb
  have hdb : dist y (y + l • (q - y)) ≤ 6 := by
    rw [dist_eq_norm, show y - (y + l • (q - y)) = -(l • (q - y)) by abel, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_of_pos hl0, ← dist_eq_norm]
    nlinarith [dist_nonneg (x := q) (y := y)]
  have hνn := hF.normals _ hb hdb ν hν hν1
  obtain ⟨hα, hβ⟩ := near_coeffs hF.unit hν1 hνn
  have hν0 : ν ≠ 0 := by rintro rfl; simp at hν1
  have hpos := inner_pos_of_seg hF.mem_int hl0 hν hν0
  have hp0 : y + depth X y • n ∈ KBall X := (KBall_isClosed X).closure_eq ▸ hF.foot_mem.1
  have h2 := hν _ hp0
  have e : y + depth X y • n - (y + l • (q - y)) = depth X y • n - l • (q - y) := by abel
  rw [e, inner_sub_left, real_inner_smul_left, real_inner_smul_left, real_inner_comm ν n] at h2
  have hfr := n1_inner_frame hF.unit (q - y) ν
  have hlI : l * inner ℝ (q - y) ν ≤ inner ℝ (q - y) ν := by nlinarith
  have hXb : inner ℝ (q - y) (perp n) * inner ℝ ν (perp n) ≤
      |inner ℝ (q - y) (perp n)| * (1 / 50) := by
    calc _ ≤ |inner ℝ (q - y) (perp n) * inner ℝ ν (perp n)| := le_abs_self _
      _ = |inner ℝ (q - y) (perp n)| * |inner ℝ ν (perp n)| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hβ (abs_nonneg _)
  have hh0 : 0 ≤ depth X y := hF.depth_pos.le
  unfold ε43
  by_contra hc
  push Not at hc
  have hA := abs_nonneg (inner ℝ (q - y) (perp n))
  have hD : 0 ≤ depth X y - inner ℝ (q - y) n := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hα hD]

/-- **(F′0, `U′ ⊂ int K`)** A point within `6` of `y` strictly below the tangent cone is
interior to `K`.

TODO: none — proved.
Acceptance: no `sorry` (inherits `frame_outside`).
Depends on: `frame_outside`. Difficulty S. -/
theorem frame_mem_interior (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) {q : Pt}
    (hq : dist q y ≤ 6)
    (hlt : inner ℝ (q - y) n < depth X y - ε43 * |inner ℝ (q - y) (perp n)|) :
    q ∈ interior (KBall X) := by
  by_contra h
  have := frame_outside hX hF hq h
  linarith

/-- **(F′3)** Diametral points near `y` are `t` above the tangent cone:
`Z z ≥ h + t − ε|Xz|`.

TODO: none — proved.
What's missing: `t ≤ dist z y ≤ 3` (`ball_polygon_c`, `y ∈ K`).  For `0 ≤ s < t` the point
`w = z − s n` has `dist w z = s < t ≤ dist(z, K)` (`ball_polygon_c`), so `w ∉ K`, and
`dist w y ≤ 3 + t ≤ 6`; `frame_outside` at `w` (same abscissa, height `Z z − s`) gives
`Z z ≥ h + s − ε|Xz|`; let `s → t` (or argue by contradiction with a suitable `s`).
Acceptance: no `sorry`.
Depends on: `frame_outside`, `ball_polygon_c`, `norm_perp`. Difficulty M. -/
theorem frame_D (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) {z : Pt} (hz : z ∈ Dset X)
    (hzy : dist z y ≤ 3) :
    depth X y + tgap X - ε43 * |inner ℝ (z - y) (perp n)| ≤ inner ℝ (z - y) n := by
  have hyK : y ∈ KBall X := interior_subset hF.mem_int
  have ht := ball_polygon_c hz hyK
  have ht0 : 0 < tgap X := by
    have hT := two_of_pos hX.dist2_pos
    unfold tgap; linarith [hT.lt]
  set s0 := inner ℝ (z - y) n - depth X y + ε43 * |inner ℝ (z - y) (perp n)| with hs0
  by_contra hc
  push Not at hc
  have hs0t : s0 < tgap X := by rw [hs0]; linarith
  set s := (max s0 0 + tgap X) / 2 with hs
  have hs1 : s0 < s := by rw [hs]; linarith [le_max_left s0 0, le_max_right s0 0]
  have hs2 : 0 ≤ s := by rw [hs]; linarith [le_max_right s0 0]
  have hs3 : s < tgap X := by rw [hs]; linarith [max_lt hs0t ht0]
  have hdw : dist (z - s • n) z = s := by
    rw [dist_eq_norm, show z - s • n - z = -(s • n) by abel, norm_neg, norm_smul, hF.unit,
      mul_one, Real.norm_eq_abs, abs_of_nonneg hs2]
  have hwK : z - s • n ∉ interior (KBall X) := by
    intro hw
    have := ball_polygon_c hz (interior_subset hw)
    rw [dist_comm, hdw] at this
    linarith
  have hwy : dist (z - s • n) y ≤ 6 := by
    have := dist_triangle (z - s • n) z y
    linarith
  have hfo := frame_outside hX hF hwy hwK
  have e : z - s • n - y = (z - y) - s • n := by abel
  have e1 : inner ℝ ((z - y) - s • n) (perp n) = inner ℝ (z - y) (perp n) := by
    rw [inner_sub_left, real_inner_smul_left, inner_self_perp, mul_zero, sub_zero]
  have e2 : inner ℝ ((z - y) - s • n) n = inner ℝ (z - y) n - s := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hF.unit]; ring
  rw [e, e1, e2] at hfo
  rw [hs0] at hs1
  linarith

/-- **Lemma 3.2(a), general form**: for a diametral pair `(z, w)` every `k ∈ X` has
`⟨k − z, w − z⟩ ≥ ‖k − z‖²/2` (as `|k − w| ≤ Δ = |z − w|`).

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `dist_le_diam`. Difficulty S. -/
theorem D_inner {z w k : Pt} (hw : w ∈ X) (hk : k ∈ X) (hzw : dist z w = diam X) :
    ‖k - z‖ ^ 2 / 2 ≤ inner ℝ (k - z) (w - z) := by
  have e := norm_sub_sq_real (k - z) (w - z)
  rw [show k - z - (w - z) = k - w by abel] at e
  have h1 : ‖k - w‖ ≤ diam X := by rw [← dist_eq_norm]; exact dist_le_diam hk hw
  have h2 : ‖w - z‖ = diam X := by rw [← dist_eq_norm, dist_comm]; exact hzw
  have h3 : ‖k - w‖ ^ 2 ≤ diam X ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [h2] at e
  linarith

/-! ## Lemma DN -/

/-- Helper: for a diametral pair `(z, w)`, every `k ∈ K` has `⟨k − z, w − z⟩ > 0`. -/
private theorem D_inner_pos (hX : Normal X) {z w k : Pt} (hw : w ∈ X) (hzw : dist z w = diam X)
    (hk : k ∈ KBall X) : 0 < inner ℝ (k - z) (w - z) := by
  have e := norm_sub_sq_real (k - z) (w - z)
  rw [show k - z - (w - z) = k - w by abel] at e
  have h1 : ‖k - w‖ ≤ dist2 X := by rw [← dist_eq_norm]; exact mem_KBall.1 hk w hw
  have h2 : ‖w - z‖ = diam X := by rw [← dist_eq_norm, dist_comm]; exact hzw
  have hT := two_of_pos hX.dist2_pos
  have h0 : 0 ≤ dist2 X := hX.dist2_pos.le
  have h3 : ‖k - w‖ ^ 2 ≤ dist2 X ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h4 : dist2 X ^ 2 < diam X ^ 2 := pow_lt_pow_left₀ hT.lt h0 two_ne_zero
  rw [h2] at e
  nlinarith [sq_nonneg ‖k - z‖]

/-- Helper: frame coordinates of a vector are bounded by its norm. -/
private theorem frame_coords_le {n v : Pt} (hn : ‖n‖ = 1) :
    |inner ℝ v n| ≤ ‖v‖ ∧ |inner ℝ v (perp n)| ≤ ‖v‖ := by
  have h1 := abs_real_inner_le_norm v n
  have h2 := abs_real_inner_le_norm v (perp n)
  rw [hn, mul_one] at h1
  rw [norm_perp, hn, mul_one] at h2
  exact ⟨h1, h2⟩

/-- Helper (common core of `frame_dn`, `frame_dn1`): for `z ∈ D` with `dist z y ≤ r ≤ 3` and a
diametral partner `w`, `⟨w − z, n⟩ < 0` and `(463 − r)|⟨w − z, perp n⟩| ≤ (9.31 + r)(−⟨w − z, n⟩)`. -/
private theorem dn_core (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) {z w : Pt}
    (hz : z ∈ Dset X) {r : ℝ} (hr : r ≤ 3) (hzy : dist z y ≤ r) (hw : w ∈ X)
    (hzw : dist z w = diam X) :
    inner ℝ (w - z) n < 0 ∧
      (463 - r) * |inner ℝ (w - z) (perp n)| ≤ (931 / 100 + r) * -inner ℝ (w - z) n := by
  have hzn : ‖z - y‖ ≤ r := by rw [← dist_eq_norm]; exact hzy
  obtain ⟨hZz, hXz⟩ := frame_coords_le (v := z - y) hF.unit
  have hZz' := abs_le.1 hZz
  have hXz' := abs_le.1 hXz
  have hh0 : 0 ≤ depth X y := hF.depth_pos.le
  have hh1 := hF.depth_le
  have hfD := frame_D hX hF hz (hzy.trans hr)
  have ht0 : 0 < tgap X := by
    have hT := two_of_pos hX.dist2_pos
    unfold tgap; linarith [hT.lt]
  -- (i) `⟨u, n⟩ < 0`
  set s := inner ℝ (z - y) n - depth X y + ε43 * |inner ℝ (z - y) (perp n)| + 1 / 100 with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  have e1 : inner ℝ ((z - y) - s • n) (perp n) = inner ℝ (z - y) (perp n) := by
    rw [inner_sub_left, real_inner_smul_left, inner_self_perp, mul_zero, sub_zero]
  have e2 : inner ℝ ((z - y) - s • n) n = inner ℝ (z - y) n - s := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hF.unit]; ring
  have eG : z - s • n - y = (z - y) - s • n := by abel
  have hε : ε43 * |inner ℝ (z - y) (perp n)| ≤ 3 / 49 := by
    unfold ε43; linarith
  have hε0 : 0 ≤ ε43 * |inner ℝ (z - y) (perp n)| := by unfold ε43; positivity
  have hGy : dist (z - s • n) y ≤ 6 := by
    rw [dist_eq_norm, eG]
    have hf := n1_norm_sq_frame hF.unit ((z - y) - s • n)
    rw [e1, e2] at hf
    have hf2 := n1_norm_sq_frame hF.unit (z - y)
    have hzn2 : ‖z - y‖ ^ 2 ≤ 9 := by nlinarith [norm_nonneg (z - y)]
    have hZG : inner ℝ (z - y) n - s = depth X y - ε43 * |inner ℝ (z - y) (perp n)| - 1 / 100 := by
      rw [hs]; ring
    rw [hZG] at hf
    nlinarith [norm_nonneg ((z - y) - s • n), sq_nonneg (inner ℝ (z - y) n)]
  have hGint : z - s • n ∈ interior (KBall X) := by
    refine frame_mem_interior hX hF hGy ?_
    rw [eG, e1, e2, hs]; linarith
  have hG := D_inner_pos hX hw hzw (interior_subset hGint)
  rw [show z - s • n - z = -(s • n) by abel, inner_neg_left, real_inner_smul_left,
    real_inner_comm] at hG
  have hc : inner ℝ (w - z) n < 0 := by
    by_contra hc; push Not at hc; nlinarith
  refine ⟨hc, ?_⟩
  -- (ii) the far points
  have far : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      -(931 / 100 + r) * -inner ℝ (w - z) n <
        (σ * 463 - inner ℝ (z - y) (perp n)) * inner ℝ (w - z) (perp n) := by
    intro σ hσ
    obtain ⟨g, hgK, hgX, hgZ⟩ := hF.far σ hσ
    have hp := D_inner_pos hX hw hzw hgK
    have eg : g - z = (g - y) - (z - y) := by abel
    have g1 : inner ℝ (g - z) n = inner ℝ (g - y) n - inner ℝ (z - y) n := by
      rw [eg, inner_sub_left]
    have g2 : inner ℝ (g - z) (perp n) = σ * 463 - inner ℝ (z - y) (perp n) := by
      rw [eg, inner_sub_left, hgX]
    rw [n1_inner_frame hF.unit, g1, g2] at hp
    have hZ : -(931 / 100 + r) ≤ inner ℝ (g - y) n - inner ℝ (z - y) n := by linarith
    have := mul_le_mul_of_nonneg_right hZ (by linarith : 0 ≤ -inner ℝ (w - z) n)
    nlinarith
  have f1 := far 1 (Or.inl rfl)
  have f2 := far (-1) (Or.inr rfl)
  rcases le_or_gt 0 (inner ℝ (w - z) (perp n)) with ha | ha
  · rw [abs_of_nonneg ha]
    nlinarith [mul_nonneg (by linarith : 0 ≤ inner ℝ (z - y) (perp n) + r) ha]
  · rw [abs_of_neg ha]
    nlinarith [mul_nonneg (by linarith : 0 ≤ r - inner ℝ (z - y) (perp n)) (neg_nonneg.2 ha.le)]

/-- **Lemma DN** (D-normals are nearly vertical): for `z ∈ D` within `3` of `y` and a diametral
partner `w`, `u = w − z` points downwards and `|⟨u, perp n⟩| ≤ (3/100)·(−⟨u, n⟩)`
(paper: `τ₃ = (463ε + 3)/460 < 0.0267`).

TODO: none — proved.
What's missing: every `k ∈ K` has `⟨k − z, u⟩ > 0` (`|k − w| ≤ Δ₂ < Δ`; `dist2 < diam`).
(i) `⟨u, n⟩ < 0`: the point `G = z − s n` with `s = Z z − h + ε|Xz| + 1/100 > 0` (`frame_D`)
has height `< h − ε|XG|` and `dist G y ≤ 6`, so `G ∈ int K` (`frame_mem_interior`) and
`0 < ⟨G − z, u⟩ = −s⟨u, n⟩`.  (ii) With `c = −⟨u,n⟩ > 0`, `a₁ = ⟨u, perp n⟩`, the far points
`g±` (`hF.far`, abscissa `±463`, height `≥ h − 9.31`) give
`(±463 − Xz) a₁ > (Z g± − Z z) c ≥ −(9.31 + 3) c` (`Z z ≤ 3`, `h ≥ 0`), so
`|a₁| ≤ 12.31 c/460 < 0.0268 c`.  Decompose with `n1_inner_frame`.
Acceptance: no `sorry`.
Depends on: `frame_D`, `frame_mem_interior`, `Frame43.far`, `Frame43.top`, `n1_inner_frame`,
`dist_le_dist2`. Difficulty M. -/
theorem frame_dn (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) {z w : Pt} (hz : z ∈ Dset X)
    (hzy : dist z y ≤ 3) (hw : w ∈ X) (hzw : dist z w = diam X) :
    inner ℝ (w - z) n < 0 ∧ |inner ℝ (w - z) (perp n)| ≤ 3 / 100 * -inner ℝ (w - z) n := by
  obtain ⟨hc, hb⟩ := dn_core hX hF hz le_rfl hzy hw hzw
  refine ⟨hc, ?_⟩
  linarith

/-- **Lemma DN for D-neighbours** (`dist z y ≤ 1`): `|⟨u, perp n⟩| ≤ (9/400)·(−⟨u, n⟩)`
(paper: `τ* = (463ε + 1)/462 < 0.0224`; here `(9.31 + 1)/462 < 0.02232 ≤ 9/400`).

TODO: none — proved.
What's missing: as `frame_dn` with `|Xz| ≤ 1`, `Z z ≤ 1`: `|a₁| ≤ 10.31 c/462`.
Acceptance: no `sorry`.
Depends on: as `frame_dn` (or share a helper). Difficulty M. -/
theorem frame_dn1 (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) {z w : Pt} (hz : z ∈ Dset X)
    (hzy : dist z y ≤ 1) (hw : w ∈ X) (hzw : dist z w = diam X) :
    inner ℝ (w - z) n < 0 ∧ |inner ℝ (w - z) (perp n)| ≤ 9 / 400 * -inner ℝ (w - z) n := by
  obtain ⟨hc, hb⟩ := dn_core hX hF hz (by norm_num : (1 : ℝ) ≤ 3) hzy hw hzw
  refine ⟨hc, ?_⟩
  linarith

/-- Helper (one side of `dd_heights`). -/
private theorem dd_side (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) {z₁ z₂ : Pt}
    (hz₁ : z₁ ∈ Dset X) (hz₂ : z₂ ∈ Dset X) (h₁ : dist z₁ y ≤ 1) :
    inner ℝ (z₂ - y) n - inner ℝ (z₁ - y) n ≤
      9 / 400 * |inner ℝ (z₁ - y) (perp n) - inner ℝ (z₂ - y) (perp n)| := by
  obtain ⟨w, hw⟩ := (mem_filter.1 hz₁).2
  obtain ⟨hwX, -, hd⟩ := mem_partners.1 hw
  obtain ⟨hc, hb⟩ := frame_dn1 hX hF hz₁ h₁ hwX hd
  have hDi := D_inner hwX (mem_filter.1 hz₂).1 hd
  have e : z₂ - z₁ = (z₂ - y) - (z₁ - y) := by abel
  have g1 : inner ℝ (z₂ - z₁) n = inner ℝ (z₂ - y) n - inner ℝ (z₁ - y) n := by
    rw [e, inner_sub_left]
  have g2 : inner ℝ (z₂ - z₁) (perp n) =
      -(inner ℝ (z₁ - y) (perp n) - inner ℝ (z₂ - y) (perp n)) := by
    rw [e, inner_sub_left]; ring
  rw [n1_inner_frame hF.unit, g1, g2] at hDi
  have h0 : 0 ≤ ‖z₂ - z₁‖ ^ 2 / 2 := by positivity
  have hab : -(inner ℝ (z₁ - y) (perp n) - inner ℝ (z₂ - y) (perp n)) *
      inner ℝ (w - z₁) (perp n) ≤
      |inner ℝ (z₁ - y) (perp n) - inner ℝ (z₂ - y) (perp n)| *
        (9 / 400 * -inner ℝ (w - z₁) n) := by
    calc _ ≤ |-(inner ℝ (z₁ - y) (perp n) - inner ℝ (z₂ - y) (perp n)) *
          inner ℝ (w - z₁) (perp n)| := le_abs_self _
      _ = |inner ℝ (z₁ - y) (perp n) - inner ℝ (z₂ - y) (perp n)| *
          |inner ℝ (w - z₁) (perp n)| := by rw [abs_mul, abs_neg]
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
  by_contra hcon
  push Not at hcon
  have := mul_lt_mul_of_pos_right hcon (neg_pos.2 hc)
  nlinarith

/-- **Corollary (D–D heights)**: two diametral points within `1` of `y` have
`|Z z₁ − Z z₂| ≤ (9/400)|Xz₁ − Xz₂|`.

TODO: none — proved.
What's missing: Lemma 3.2(a) both ways (`D_inner` with `k = z₂` and the partner `w₁` of `z₁`,
and vice versa): `⟨z₂ − z₁, w₁ − z₁⟩ ≥ 0` with `w₁ − z₁ = a₁ perp n − c₁ n`, `c₁ > 0`,
`|a₁| ≤ (9/400) c₁` (`frame_dn1`) gives `(Z z₂ − Z z₁) c₁ ≤ (Xz₂ − Xz₁) a₁`; symmetric.
Decompose with `n1_inner_frame`.
Acceptance: no `sorry`.
Depends on: `D_inner`, `frame_dn1`, `n1_inner_frame`. Difficulty M. -/
theorem dd_heights (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) {z₁ z₂ : Pt}
    (hz₁ : z₁ ∈ Dset X) (hz₂ : z₂ ∈ Dset X) (h₁ : dist z₁ y ≤ 1) (h₂ : dist z₂ y ≤ 1) :
    |inner ℝ (z₁ - y) n - inner ℝ (z₂ - y) n| ≤
      9 / 400 * |inner ℝ (z₁ - y) (perp n) - inner ℝ (z₂ - y) (perp n)| := by
  have a1 := dd_side hX hF hz₁ hz₂ h₁
  have a2 := dd_side hX hF hz₂ hz₁ h₂
  rw [abs_sub_comm (inner ℝ (z₂ - y) (perp n))] at a2
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-! ## Depth and receivers -/

/-- Depth is at most the vertical distance to the support line: `depth a ≤ h − Z a` for
`a ∈ K`.

TODO: none — proved.
What's missing: if `a ∈ ∂K` the depth is `0 ≤ h − Z a` (`Frame43.top`).  Otherwise the ray
`a + s n` leaves `K` for `s > h − Z a` (`Frame43.top`), so `exists_frontier_seg` from `a` to
`a + (h − Z a + η) n` gives a frontier point at distance `≤ h − Z a + η`; let `η → 0`
(`Metric.infDist_le_dist_of_mem`).
Acceptance: no `sorry`.
Depends on: `Frame43.top`, `exists_frontier_seg`, `KBall_isClosed`. Difficulty M. -/
theorem frame_depth_le (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) {a : Pt}
    (ha : a ∈ KBall X) : depth X a ≤ depth X y - inner ℝ (a - y) n := by
  have htop := hF.top ha
  by_cases hfr : a ∈ frontier (KBall X)
  · have : depth X a = 0 := Metric.infDist_zero_of_mem hfr
    linarith
  have hai : a ∈ interior (KBall X) := by
    by_contra hni
    exact hfr ⟨subset_closure ha, hni⟩
  refine le_of_forall_pos_le_add fun η hη => ?_
  set L := depth X y - inner ℝ (a - y) n + η with hL
  have hL0 : 0 < L := by rw [hL]; linarith
  have hq : a + L • n ∉ interior (KBall X) := by
    intro hq
    have := hF.top (interior_subset hq)
    rw [show a + L • n - y = (a - y) + L • n by abel, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hF.unit, hL] at this
    linarith
  obtain ⟨l, hl0, hl1, hb⟩ := exists_frontier_seg (KBall_isClosed X) hai hq
  have hd : dist a (a + l • (a + L • n - a)) ≤ L := by
    rw [dist_eq_norm, show a - (a + l • (a + L • n - a)) = -((l * L) • n) by
      rw [add_sub_cancel_left, smul_smul]; abel, norm_neg, norm_smul, hF.unit, mul_one,
      Real.norm_eq_abs, abs_of_pos (mul_pos hl0 hL0)]
    nlinarith
  have := Metric.infDist_le_dist_of_mem (x := a) hb
  unfold depth
  linarith

/-- Receivers have height `≤ −2/3`.

TODO: none — proved.
Acceptance: no `sorry` (inherits `frame_depth_le`).
Depends on: `frame_depth_le`. Difficulty S. -/
theorem Low_Z (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) {a : Pt} (ha : a ∈ Low X y) :
    inner ℝ (a - y) n ≤ -(2 / 3) := by
  obtain ⟨-, haK, hd⟩ := mem_filter.1 ha
  have := frame_depth_le hX hF haK
  linarith

/-- A neighbour of height `≤ −4/5` is a receiver.

TODO: none — proved.
What's missing: `a ∈ int K` by `frame_mem_interior` (`Z a ≤ −0.8 < h − |Xa|/49`, `h > 0`).
Depth: for `b ∈ ∂K`, either `dist a b > 2 ≥ h + 2/3` (`h ≤ 1`), or `dist b y ≤ 3`, `b ∉ int K`,
so `Z b ≥ h − 3/49` (`frame_outside`) and `dist a b ≥ Z b − Z a ≥ h + 0.8 − 0.0613 ≥ h + 2/3`;
`Metric.le_infDist` (frontier nonempty, e.g. the foot).
Acceptance: no `sorry`.
Depends on: `frame_outside`, `frame_mem_interior`, `dist_of_mem_nbδ`, `Frame43.foot_mem`,
`Metric.le_infDist`. Difficulty M. -/
theorem lower_mem_Low (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) {a : Pt}
    (ha : a ∈ nbδ X y) (hz : inner ℝ (a - y) n ≤ -(4 / 5)) : a ∈ Low X y := by
  have hay : dist a y = 1 := dist_of_mem_nbδ hX ha
  have hh0 := hF.depth_pos
  have hh1 := hF.depth_le
  have hXa := (frame_coords_le (v := a - y) hF.unit).2
  rw [← dist_eq_norm, hay] at hXa
  have hai : a ∈ interior (KBall X) := by
    refine frame_mem_interior hX hF (by linarith) ?_
    unfold ε43; linarith
  refine mem_filter.2 ⟨ha, interior_subset hai, ?_⟩
  show depth X y + 2 / 3 ≤ Metric.infDist a (frontier (KBall X))
  refine (Metric.le_infDist ⟨_, hF.foot_mem⟩).2 fun b hb => ?_
  by_cases hby : dist b y ≤ 3
  · have hfo := frame_outside hX hF (by linarith) hb.2
    have hXb := (frame_coords_le (v := b - y) hF.unit).2
    rw [← dist_eq_norm] at hXb
    have hZab := (abs_le.1 (frame_coords_le (v := b - a) hF.unit).1).2
    have e : inner ℝ (b - a) n = inner ℝ (b - y) n - inner ℝ (a - y) n := by
      rw [show b - a = (b - y) - (a - y) by abel, inner_sub_left]
    rw [e, ← dist_eq_norm, dist_comm] at hZab
    have : ε43 * |inner ℝ (b - y) (perp n)| ≤ 3 / 49 := by unfold ε43; linarith
    linarith
  · push Not at hby
    have := dist_triangle b a y
    rw [dist_comm b a] at this
    linarith

/-- **Window packing**: unit vectors `q − a`, pairwise `≥ 1` apart (i.e. `≥ 60°`), all strictly
within `60°` of `n` (`⟨q − a, n⟩ > 1/2`), number at most `2`.

TODO: none — proved.
What's missing: as `card_sep_arc_le_four` with the cone `1/2 < ⟨·, n⟩` (open arc of length
`2π/3`): three points pairwise `≥ π/3` apart span `≥ 2π/3`.  Or directly: angles `ψ_i ∈
(−π/3, π/3)`, sorted, `ψ₃ − ψ₁ ≥ 2π/3` impossible.
Acceptance: no `sorry`.
Depends on: `exists_angle`, `card_le_of_sep_real` (as in `card_sep_arc_le_four`).
Difficulty M. -/
theorem card_cone_le_two {a n : Pt} (hn : ‖n‖ = 1) (P : Finset Pt)
    (h1 : ∀ q ∈ P, dist q a = 1) (hsep : ∀ q ∈ P, ∀ q' ∈ P, q ≠ q' → 1 ≤ dist q q')
    (hcone : ∀ q ∈ P, 1 / 2 < inner ℝ (q - a) n) : P.card ≤ 2 := by
  have hπ := Real.pi_pos
  obtain ⟨θn, hθn⟩ := exists_dirVec hn
  have hu : ∀ q ∈ P, ‖q - a‖ = 1 := fun q hq => by rw [← dist_eq_norm, h1 q hq]
  have hp : (0 : ℝ) < 2 * π := by linarith
  have hang : ∀ q ∈ P, ∃ ψ : ℝ, ψ ∈ Set.Ioc (-π) π ∧ dirVec (θn + ψ) = q - a := by
    intro q hq
    obtain ⟨φ, -, hφ⟩ := exists_angle (hu q hq)
    refine ⟨toIocMod hp (-π) (φ - θn), ?_, ?_⟩
    · have := toIocMod_mem_Ioc hp (-π) (φ - θn)
      refine ⟨this.1, ?_⟩
      linarith [this.2]
    · have e := toIocMod_add_toIocDiv_zsmul hp (-π) (φ - θn)
      rw [← hφ]
      have : θn + toIocMod hp (-π) (φ - θn) =
          φ + ((-(toIocDiv hp (-π) (φ - θn)) : ℤ) : ℝ) * (2 * π) := by
        rw [zsmul_eq_mul] at e; push_cast; linarith
      rw [this, dirVec_add_int]
  choose! ψ hψ hψd using hang
  have hbound : ∀ q ∈ P, |ψ q| < π / 3 := by
    intro q hq
    have hc : Real.cos (ψ q) = inner ℝ (q - a) n := by
      rw [← hψd q hq, ← hθn, Curve.inner_dirVec]; congr 1; ring
    have hcos : 1 / 2 < Real.cos |ψ q| := by rw [Real.cos_abs, hc]; exact hcone q hq
    have hm1 : |ψ q| ≤ π := abs_le.2 ⟨by linarith [(hψ q hq).1], (hψ q hq).2⟩
    by_contra h
    push Not at h
    have h2 := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hm1 h
    rw [Real.cos_pi_div_three] at h2
    linarith
  have hsep' : ∀ q ∈ P, ∀ q' ∈ P, q ≠ q' → π / 3 ≤ |ψ q - ψ q'| := by
    intro q hq q' hq' hne
    by_contra hlt
    push Not at hlt
    have hlt' := Defs.sqd_lt_of_arg one_pos (a := θn + ψ q) (b := θn + ψ q')
      (by rwa [add_sub_add_left_eq_sub])
    have hd := hsep q hq q' hq' hne
    have e : dist q q' ^ 2 = (1 * Real.cos (θn + ψ q) - 1 * Real.cos (θn + ψ q')) ^ 2 +
        (1 * Real.sin (θn + ψ q) - 1 * Real.sin (θn + ψ q')) ^ 2 := by
      have e0 : dist q q' = dist (q - a) (q' - a) := by
        rw [dist_eq_norm, dist_eq_norm, sub_sub_sub_cancel_right]
      rw [e0, dist_sq_pt, ← hψd q hq, ← hψd q' hq']
      simp only [dirVec_apply0, dirVec_apply1, one_mul]
    nlinarith [dist_nonneg (x := q) (y := q')]
  by_contra hc
  push Not at hc
  obtain ⟨q₁, q₂, q₃, hq₁, hq₂, hq₃, h12, h13, h23⟩ := Finset.two_lt_card_iff.1 hc
  have b1 := abs_lt.1 (hbound q₁ hq₁)
  have b2 := abs_lt.1 (hbound q₂ hq₂)
  have b3 := abs_lt.1 (hbound q₃ hq₃)
  rcases le_abs'.1 (hsep' q₁ hq₁ q₂ hq₂ h12) with s12 | s12 <;>
  rcases le_abs'.1 (hsep' q₁ hq₁ q₃ hq₃ h13) with s13 | s13 <;>
  rcases le_abs'.1 (hsep' q₂ hq₂ q₃ hq₃ h23) with s23 | s23 <;>
  linarith

end

end Erdos132Main
