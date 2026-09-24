import Erdos132.E132Main15Defs

/-!
# Erdős Problem 132, `15/11` theorem — Region III at the exact value `τ = √3/2`

`angle_R4.md` §3.3.  At `τ = √3/2` (`s = 1/2`, `θ₀ = 30°`) a two-rung vertex `v` with rung ends
`a, b` spans an equilateral **triangle** `v a b` of side 1 whose base `ab` is a D–D `δ`-edge.
Goal: `q₂ ≤ #breaks + cBad` (`exact_breaks`), where a **break** is a point of `S` without a
pure right T-neighbour.  Combined with `#T + #breaks ≤ |S| + #mixed` this gives the slot bound
`#T + q₂ ≤ |S| + C` used in `regionIII_key`.

The rigidity chain:
* **Base determines apex** (`base_apex_unique`); bad bases are `≤ cBad` (`card_badBase_le`).
* **(R)** rows are cyclic orders (`rowR_cap_K`) — the cap cut off by a pure K–K T-edge contains no
  other row point.  *Not on the critical path* of the slot formulation (kept for fidelity).
* **(B′)** the pure right/left D-walks from a good base stay on `C(w_v, Δ)`, stepping by the
  rotation `rot α₁` (`Bprime_walk_right`, `Bprime_walk_left`, `Bprime_rot`, `Bprime_span`).
* **(W)** one centre per D-walk (`W_center`); the apex position (`apex_eq`).
* **(Arc)** the short arc of `C(w, Δ₂)` between consecutive apexes lies in `K`, hence in `∂K`
  (`arc_sub_K`), and has single-ray normal cones in its relative interior (`normal_fact`).
* **(Rigid)** the pure right K-walk from an apex moves along that arc in steps of `α₂`
  (`rigid_step`).
* **(Arith)** `jα₂ ≠ kα₁` whenever `kα₁ < π/3` (`arith_no_land`, with `tgap_bounds_exact`), so
  the K-walk breaks strictly before the next apex.
* **(Count)** arcs of different triangles are disjoint (`arc_centre_unique` for different
  centres), giving an injection `triangles → breaks` (`exact_breaks`).

Orientation convention: with inward normal `u ≈ −(p − w)/|p − w|`, "right" (`σ = −1`,
`det2 u (q − p) < 0`) is the **counterclockwise** sense about `w` in both rows.
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-- A **triangle** at `τ = √3/2`: `v` has good rungs to `a` and `b`, and the base `ab` is a good
pure D-row T-edge with `b` the right neighbour of `a`. -/
def IsTri (F : DirField X) (v a b : Pt) : Prop :=
  IsRung F v a ∧ IsRung F v b ∧ s(v, a) ∈ rungs X F ∧ s(v, b) ∈ rungs X F ∧ RowR F a b ∧
    s(a, b) ∈ good X F

/-! ## Constants at `τ = √3/2` -/

/-- At `τ = √3/2`: `√3/2 < t < √3/2 + 1/(2Δ₂)` (`t < 1`, since `t ≥ 1` forces `τ ≥ t ≥ 1`).

TODO: none — proved.
What's missing: (was) `tau_sub_tgap` (`τ − t = (t² − 1)/(2Δ₂)`); if `t ≥ 1` then `τ ≥ 1`; so
`t < 1` and `0 < (1 − t²)/(2Δ₂) < 1/(2Δ₂)`.
Acceptance: no `sorry`.
Depends on: `tau_sub_tgap`, `Normal.dist2_pos`, `tgap > 0`. Difficulty S. -/
theorem tgap_bounds_exact (hX : Normal X) (hτ : tau X = √3 / 2) :
    √3 / 2 < tgap X ∧ tgap X < √3 / 2 + 1 / (2 * dist2 X) := by
  have hpos := hX.dist2_pos
  have ht0 : 0 < tgap X := by have := (two_of_pos hpos).lt; unfold tgap; linarith
  have e := tau_sub_tgap X
  rw [hτ] at e
  have h3 : √3 < 1.7321 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have ht1 : tgap X < 1 := by
    by_contra h; push Not at h
    have : 0 ≤ (tgap X ^ 2 - 1) / (2 * dist2 X) := div_nonneg (by nlinarith) (by positivity)
    linarith
  have hd : 0 < 2 * dist2 X := by positivity
  have e' : tgap X - √3 / 2 = (1 - tgap X ^ 2) / (2 * dist2 X) := by
    have : (tgap X ^ 2 - 1) / (2 * dist2 X) = -((1 - tgap X ^ 2) / (2 * dist2 X)) := by
      rw [← neg_div, neg_sub]
    linarith
  constructor
  · have : 0 < (1 - tgap X ^ 2) / (2 * dist2 X) := div_pos (by nlinarith) hd
    linarith
  · have : (1 - tgap X ^ 2) / (2 * dist2 X) < 1 / (2 * dist2 X) :=
      div_lt_div_of_pos_right (by nlinarith) hd
    linarith

/-- `x ≤ arcsin x ≤ x + x³` for `0 < x ≤ 1/2`. -/
private theorem arcsin_bounds {x : ℝ} (h0 : 0 < x) (h1 : x ≤ 1 / 2) :
    x ≤ Real.arcsin x ∧ Real.arcsin x ≤ x + x ^ 3 := by
  have hπ := Real.pi_gt_three
  constructor
  · have hs := Real.sin_arcsin (x := x) (by linarith) (by linarith)
    have := Real.sin_le (Real.arcsin_nonneg.2 h0.le)
    linarith
  · have hx3 : x ^ 3 ≤ 1 / 8 := by
      calc x ^ 3 ≤ (1 / 2) ^ 3 := by gcongr
        _ = 1 / 8 := by norm_num
    rw [Real.arcsin_le_iff_le_sin ⟨by linarith, by linarith⟩
      ⟨by nlinarith [pow_pos h0 3], by linarith⟩]
    have := Real.sin_gt_sub_cube (x := x + x ^ 3) (by positivity)
    have hx2 : x ^ 2 ≤ 1 / 4 := by nlinarith
    have : (x + x ^ 3) ^ 3 ≤ 6 * x ^ 3 := by
      have e : (x + x ^ 3) ^ 3 = x ^ 3 * (1 + x ^ 2) ^ 3 := by ring
      rw [e]
      have : (1 + x ^ 2) ^ 3 ≤ 6 := by
        have : 1 + x ^ 2 ≤ 5 / 4 := by linarith
        calc (1 + x ^ 2) ^ 3 ≤ (5 / 4) ^ 3 := by gcongr
          _ ≤ 6 := by norm_num
      have : 0 < x ^ 3 := by positivity
      nlinarith
    linarith

/-- **(Arith)** For `R ≥ 10⁴`, `Δ = R + t` with `√3/2 < t < √3/2 + 1/(2R)`, `α₁ = 2 arcsin(1/(2Δ))`,
`α₂ = 2 arcsin(1/(2R))`: no `j ≥ 1`, `k` with `kα₁ < π/3` have `jα₂ = kα₁`.
(`jα₂ = kα₁ ⇒ k > j ⇒ kα₁ ≥ α₁α₂/(α₂ − α₁) ≥ 1/(t + 1/(23R)) > 1/0.8662 > π/3`.)

TODO: none — proved (with `x ≤ arcsin x ≤ x + x³`: `1/α₁ ≤ R + t`, `1/α₂ ≥ R − 1/(4R)`).
What's missing: (was) bounds on `f(ρ) = 1/α_ρ`: from `sin(α/2) = 1/(2ρ)` and
`x − x³/6 ≤ sin x ≤ x`: `ρ − 1/(23ρ) ≤ f(ρ) ≤ ρ`; then `1/α₁ − 1/α₂ ≤ t + 1/(23R)`,
`t + 1/(23R) < 0.8662 < 3/π` (`Real.pi_lt_d2`).
Acceptance: no `sorry`.
Depends on: `Real.sin_arcsin`, `Real.sin_le`, `Real.sin_gt_sub_cube`-type bounds. Difficulty M. -/
theorem arith_no_land {R t : ℝ} (hR : 10 ^ 4 ≤ R) (ht₁ : √3 / 2 < t) (ht₂ : t < √3 / 2 + 1 / (2 * R))
    {j k : ℕ} (hj : 1 ≤ j) (hk : (k : ℝ) * (2 * Real.arcsin (1 / (2 * (R + t)))) < π / 3) :
    (j : ℝ) * (2 * Real.arcsin (1 / (2 * R))) ≠ k * (2 * Real.arcsin (1 / (2 * (R + t)))) := by
  intro hjk
  have h3 : √3 < 1.7321 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h3' : (1.732 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hR0 : 0 < R := by linarith
  have ht0 : 0 < t := by linarith
  set x₁ := 1 / (2 * (R + t)) with hx₁
  set x₂ := 1 / (2 * R) with hx₂
  set A := 2 * Real.arcsin x₁
  set B := 2 * Real.arcsin x₂
  have hx₁0 : 0 < x₁ := by positivity
  have hx₂0 : 0 < x₂ := by positivity
  have hx₂s : x₂ ≤ 1 / 20000 := by
    rw [hx₂, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hx₁s : x₁ ≤ 1 / 2 := by
    rw [hx₁, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  obtain ⟨a1, -⟩ := arcsin_bounds hx₁0 hx₁s
  obtain ⟨-, b2⟩ := arcsin_bounds hx₂0 (by linarith)
  have hA0 : 0 < A := by simp only [A]; linarith
  -- `1/A ≤ R + t`
  have hA : 1 / A ≤ R + t := by
    rw [div_le_iff₀ hA0]
    have : (R + t) * (2 * x₁) = 1 := by rw [hx₁]; field_simp
    simp only [A]; nlinarith
  -- `R − 1/(4R) ≤ 1/B`
  have hB0 : 0 < B := by
    have := arcsin_bounds hx₂0 (by linarith); simp only [B]; linarith [this.1]
  have hR' : 0 < R - 1 / (4 * R) := by
    have : 1 / (4 * R) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  have hB : R - 1 / (4 * R) ≤ 1 / B := by
    rw [le_div_iff₀ hB0]
    have e : 2 * (x₂ + x₂ ^ 3) * (R - 1 / (4 * R)) = 1 - x₂ ^ 4 := by
      rw [hx₂]; field_simp; ring
    have : B ≤ 2 * (x₂ + x₂ ^ 3) := by simp only [B]; linarith
    have := mul_le_mul_of_nonneg_right this hR'.le
    nlinarith [pow_pos hx₂0 4]
  -- `1/A − 1/B ≤ c := t + 1/(4R) < 0.8662`
  set c := t + 1 / (4 * R)
  have hc : c < 0.8662 := by
    have h1 : 1 / (2 * R) ≤ 1 / 20000 := hx₂s
    have h2 : 1 / (4 * R) ≤ 1 / 40000 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    simp only [c]; linarith
  have hkey : B - A ≤ c * (A * B) := by
    have h : 1 / A - 1 / B ≤ c := by simp only [c]; linarith
    have : B - A = (1 / A - 1 / B) * (A * B) := by field_simp
    rw [this]; exact mul_le_mul_of_nonneg_right h (by positivity)
  -- integrality: `j (B − A) ≥ A`
  have hAB : A < B := by
    have : x₁ < x₂ := by
      rw [hx₁, hx₂]; exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
    have := Real.arcsin_lt_arcsin (by linarith) this (by linarith)
    simp only [A, B]; linarith
  have hkj : (j : ℝ) + 1 ≤ k := by
    have : j < k := by
      by_contra hle; push Not at hle
      have h1 : (k : ℝ) ≤ j := by exact_mod_cast hle
      have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
      have : (k : ℝ) * A < j * B := by nlinarith
      linarith
    exact_mod_cast this
  have hjBA : A ≤ j * (B - A) := by
    have : 0 ≤ ((k : ℝ) - j - 1) * A := mul_nonneg (by linarith) hA0.le
    nlinarith
  -- `j B c ≥ 1`, but `j B = k A < π/3` and `c < 3/π`
  have hj0 : (0 : ℝ) ≤ j := by positivity
  have h1 : 1 ≤ j * B * c := by
    have h2 := mul_le_mul_of_nonneg_left hkey hj0
    have : A * 1 ≤ A * (j * B * c) := by
      have : (j : ℝ) * (c * (A * B)) = A * (j * B * c) := by ring
      linarith
    exact le_of_mul_le_mul_left this hA0
  have hπ := Real.pi_lt_d2
  have hkA : (k : ℝ) * A < π / 3 := hk
  have hjB : (j : ℝ) * B < π / 3 := by linarith
  have hjB0 : 0 ≤ (j : ℝ) * B := by positivity
  have e1 : (j : ℝ) * B * c ≤ (j * B) * 0.8662 := mul_le_mul_of_nonneg_left hc.le hjB0
  have e2 : (j : ℝ) * B * 0.8662 ≤ π / 3 * 0.8662 := by linarith
  linarith

/-! ## Private helpers (rung pairs) -/

/-- `det(a, c b) = c det(a, b)`. -/
private theorem det2_smul_right' (a b : Pt) (c : ℝ) : det2 a (c • b) = c * det2 a b := by
  simp only [det2_pt, PiLp.smul_apply, smul_eq_mul]; ring

/-- `det(a, b^⊥) = a·b`. -/
private theorem det2_perp_right' (a b : Pt) : det2 a (perp b) = inner ℝ a b := by
  rw [det2_pt, inner_pt]; simp

/-- Two rungs `z ≠ z′` of `v`: `z − z′ = 2sκ u_v^⊥` and `z′ − v = −τu_v − κs u_v^⊥`, `κ = ±1`. -/
private theorem rung_pair_kappa (F : DirField X) {v z z' : Pt} (hr : IsRung F v z)
    (hr' : IsRung F v z') (hne : z ≠ z') :
    ∃ κ : ℝ, (κ = 1 ∨ κ = -1) ∧ z - z' = (2 * sOff X * κ) • perp (F.u v) ∧
      z' - v = (-tau X) • F.u v + (-κ * sOff X) • perp (F.u v) := by
  obtain ⟨σ₁, hσ₁, e₁⟩ := rung_offset F hr
  obtain ⟨σ₂, hσ₂, e₂⟩ := rung_offset F hr'
  have hne12 : σ₁ ≠ σ₂ := by
    rintro rfl; apply hne
    have : z - v = z' - v := by rw [e₁, e₂]
    exact sub_left_injective this
  have hz : z - z' = (z - v) - (z' - v) := by abel
  rcases hσ₁ with rfl | rfl <;> rcases hσ₂ with rfl | rfl
  · exact absurd rfl hne12
  · refine ⟨1, Or.inl rfl, ?_, ?_⟩
    · rw [hz, e₁, e₂, show 2 * sOff X * 1 = 1 * sOff X - (-1) * sOff X by ring, sub_smul]; abel
    · rw [e₂]; try ring_nf
  · refine ⟨-1, Or.inr rfl, ?_, ?_⟩
    · rw [hz, e₁, e₂, show 2 * sOff X * (-1) = (-1) * sOff X - 1 * sOff X by ring, sub_smul]; abel
    · rw [e₂]; try ring_nf
  · exact absurd rfl hne12

/-- The side of `2sκ u^⊥` seen from `u′ ≈ u` has the sign of `κ`. -/
private theorem side_sign {u u' : Pt} (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1) (huu : ‖u - u'‖ ≤ 1 / 100)
    {s κ σ : ℝ} (hs : 0 < s) (h : 0 < σ * det2 u' ((2 * s * κ) • perp u)) : 0 < σ * κ := by
  have huu' : 0 < inner ℝ u' u := by
    have e := @norm_sub_sq_real _ _ _ u u'
    rw [hu, hu', real_inner_comm] at e
    nlinarith [norm_nonneg (u - u')]
  rw [det2_smul_right', det2_perp_right'] at h
  by_contra h'; push Not at h'
  have : σ * (2 * s * κ * inner ℝ u' u) = (σ * κ) * (2 * s * inner ℝ u' u) := by ring
  have h2 : 0 ≤ 2 * s * inner ℝ u' u := by positivity
  nlinarith [mul_nonpos_of_nonpos_of_nonneg h' h2]

/-- `u·u' > 0` for unit vectors with `|u − u'| ≤ 1/100`. -/
private theorem inner_pos_of_close {u u' : Pt} (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1)
    (huu : ‖u - u'‖ ≤ 1 / 100) : 0 < inner ℝ u' u := by
  have e := @norm_sub_sq_real _ _ _ u u'
  rw [hu, hu', real_inner_comm] at e
  nlinarith [norm_nonneg (u - u')]

/-- Two K-vertices whose rungs to a common end `b` have the same offset coefficient (in their own
frames) and nearly equal normals coincide. -/
private theorem eq_of_same_offset (hX : Normal X) (F : DirField X) {v v' b : Pt}
    (hv : IsRung F v b) (hv' : IsRung F v' b) (huu : ‖F.u v' - F.u v‖ ≤ 2 / 100) {c : ℝ}
    (hc : |c| ≤ 1) (hτ : |tau X| ≤ 1)
    (h : b - v = (-tau X) • F.u v + c • perp (F.u v))
    (h' : b - v' = (-tau X) • F.u v' + c • perp (F.u v')) : v = v' := by
  refine eq_of_dist_lt_one hX.minDist_eq hv.memX.1 hv'.memX.1 ?_
  have e : v - v' = (b - v') - (b - v) := by abel
  rw [dist_eq_norm, e, h, h']
  have : ((-tau X) • F.u v' + c • perp (F.u v')) - ((-tau X) • F.u v + c • perp (F.u v)) =
      (-tau X) • (F.u v' - F.u v) + c • perp (F.u v' - F.u v) := by
    rw [perp_sub, smul_sub, smul_sub]; abel
  rw [this]
  refine (norm_add_le _ _).trans_lt ?_
  rw [norm_smul, norm_smul, norm_perp, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
  nlinarith [norm_nonneg (F.u v' - F.u v), abs_nonneg c, abs_nonneg (tau X)]

/-- At `τ = √3/2`, `s = 1/2`. -/
private theorem sOff_exact (hτ : tau X = √3 / 2) : sOff X = 1 / 2 := by
  unfold sOff
  rw [hτ, div_pow, Real.sq_sqrt (by norm_num)]
  rw [show (1 : ℝ) - 3 / 2 ^ 2 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-! ## Triangles and bases -/

/-- At `τ = √3/2` every two-rung vertex spans a triangle over a unit D–D base, which is bad or
(in one orientation) a good pure right T-edge.

TODO: none — proved.
What's missing: (was) `rung_offset` with `sOff = 1/2` gives `z − z′ = ±perp u_v` (`‖·‖ = 1`), so
`s(z, z′) ∈ edges`; if good, `good_dichotomy` (both ends in `D`, so no rung) makes it a T-edge,
and `tstep_flip`/`T2` orient it as `RowR`.
Acceptance: no `sorry`.
Depends on: `rung_offset`, `good_dichotomy`, `tstep_flip`, `T2`, `tgap_bounds_exact`.
Difficulty M. -/
theorem tri_of_twoRung (hX : Normal X) (F : DirField X) (hτ : tau X = √3 / 2) {v : Pt}
    (hv : v ∈ twoRungVerts X F) :
    ∃ a b, IsRung F v a ∧ IsRung F v b ∧ s(v, a) ∈ rungs X F ∧ s(v, b) ∈ rungs X F ∧ a ≠ b ∧
      s(a, b) ∈ edges X ∧ (s(a, b) ∈ bad X F ∨ IsTri F v a b) := by
  obtain ⟨z, z', hne, h1, h2, g1, g2⟩ := (mem_filter.1 hv).2
  obtain ⟨κ, hκ, hd, -⟩ := rung_pair_kappa F h1 h2 hne
  have hs := sOff_exact hτ
  have hdist : dist z z' = 1 := by
    rw [dist_eq_norm, hd, norm_smul, norm_perp, F.norm_u h1.1, hs]
    rcases hκ with rfl | rfl <;> norm_num
  have hz := h1.2.2.1
  have hz' := h2.2.2.1
  have hzD := h1.2.2.2.1
  have hz'D := h2.2.2.2.1
  have hedge : s(z, z') ∈ edges X := by
    refine mem_filter.2 ⟨?_, ?_⟩
    · simp only [pairsS, mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff]
      exact ⟨⟨hz, hz'⟩, hne⟩
    · show dist z z' = minDist X
      rw [hX.minDist_eq, hdist]
  by_cases hgood : s(z, z') ∈ good X F
  · have hg : ang (F.u z) (F.u z') ≤ beta := (mem_filter.1 hgood).2 z z' rfl
    have hτ' : 2 * beta < tau X := by
      rw [hτ]
      have : (1.7 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
      unfold beta; linarith
    have hT : IsTEdge F z z' := by
      rcases good_dichotomy hX F hτ' hz hz' hdist hg with h | h | h
      · exact h
      · exact absurd hzD h.2.1
      · exact absurd hz'D h.2.1
    have hl := lagrange (z' - z) (F.u z)
    rw [F.norm_u' hz, ← dist_eq_norm, dist_comm z' z, hdist] at hl
    have ha := hT.2.1
    have hβ : beta = 1 / 100 := rfl
    rw [hβ] at ha
    have hDD : (z ∈ Dset X ↔ z' ∈ Dset X) := ⟨fun _ => hz'D, fun _ => hzD⟩
    rcases lt_or_gt_of_ne (show det2 (F.u z) (z' - z) ≠ 0 by
      intro h0; rw [h0] at hl; nlinarith [hT.1]) with hb | hb
    · exact ⟨z, z', h1, h2, g1, g2, hne, hedge, Or.inr ⟨h1, h2, g1, g2,
        ⟨⟨hz, hz', hdist, hg, hT, by linarith⟩, hDD⟩, hgood⟩⟩
    · have := tstep_flip hz hz' hdist hg hT.1 hT.2.1
      have hb' : det2 (F.u z') (z - z') < 0 := by nlinarith
      have hg' : ang (F.u z') (F.u z) ≤ beta := by
        rw [ang, InnerProductGeometry.angle_comm]; exact hg
      have hd' : dist z' z = 1 := by rw [dist_comm]; exact hdist
      have hR : RowR F z' z := ⟨⟨hz', hz, hd', hg', hT.symm, by linarith⟩, hDD.symm⟩
      have he' : s(z', z) ∈ edges X := Sym2.eq_swap ▸ hedge
      have hgood' : s(z', z) ∈ good X F := Sym2.eq_swap ▸ hgood
      exact ⟨z', z, h2, h1, g2, g1, hne.symm, he', Or.inr ⟨h2, h1, g2, g1, hR, hgood'⟩⟩
  · exact ⟨z, z', h1, h2, g1, g2, hne, hedge,
      Or.inl (mem_filter.2 ⟨hedge, fun h => hgood (mem_filter.2 ⟨hedge, h⟩)⟩)⟩

/-- **Base determines apex**: the other point `v̄ = z′ − τu + ½u^⊥` of `C(z,1) ∩ C(z′,1)` violates
Lemma 3.2(a) (`(v̄ − z′)·u_{z′} ≤ −τ cos β + ½ sin β < 0`), so two vertices with good rungs to
the same two ends coincide.

TODO: none — proved (no mirror argument: goodness at `a` gives `|u_v − u_{v′}| ≤ 2β`, hence the
same side `κ = κ′` of `a − b`, and then `|v − v′| ≤ 2β(τ + s) < 1`).
What's missing: (was) two circles of radius 1 meet in `≤ 2` points; the mirror apex contradicts
`exact_identity_a` at `z′` (`u_{z′}` within `β` of `u_v`).
Acceptance: no `sorry`.
Depends on: `rung_offset`, `exact_identity_a`, `RungM.ang`. Difficulty M. -/
theorem base_apex_unique (hX : Normal X) (F : DirField X) (hτ : tau X = √3 / 2) {v v' a b : Pt}
    (hab : a ≠ b) (h₁ : IsRung F v a) (h₂ : IsRung F v b) (h₃ : IsRung F v' a)
    (h₄ : IsRung F v' b) (g₁ : s(v, a) ∈ rungs X F) (g₂ : s(v, b) ∈ rungs X F)
    (g₃ : s(v', a) ∈ rungs X F) (g₄ : s(v', b) ∈ rungs X F) : v = v' := by
  obtain ⟨κ, hκ, hd, ho⟩ := rung_pair_kappa F h₁ h₂ hab
  obtain ⟨κ', hκ', hd', ho'⟩ := rung_pair_kappa F h₃ h₄ hab
  have hs := sOff_exact hτ
  have hga : ang (F.u v) (F.u a) ≤ beta := (mem_filter.1 (mem_filter.1 g₁).1).2 v a rfl
  have hga' : ang (F.u v') (F.u a) ≤ beta := (mem_filter.1 (mem_filter.1 g₃).1).2 v' a rfl
  have hu := F.norm_u h₁.1
  have hu' := F.norm_u h₃.1
  have hua := F.norm_u h₁.2.2.1
  have hb : beta = 1 / 100 := rfl
  have h1 : ‖F.u v - F.u a‖ ≤ 1 / 100 := hb ▸ (norm_sub_le_angR hu hua).trans hga
  have h2 : ‖F.u v' - F.u a‖ ≤ 1 / 100 := hb ▸ (norm_sub_le_angR hu' hua).trans hga'
  have hs0 : (0 : ℝ) < sOff X := by rw [hs]; norm_num
  -- the sign of `det(u_a, a − b)` is `κ` and `κ′`
  have e2 : 0 < κ' * det2 (F.u a) ((2 * sOff X * κ') • perp (F.u v')) := by
    rw [det2_smul_right', det2_perp_right']
    have := inner_pos_of_close hu' hua h2
    have hk : κ' * (2 * sOff X * κ' * inner ℝ (F.u a) (F.u v')) =
        (κ' * κ') * (2 * sOff X * inner ℝ (F.u a) (F.u v')) := by ring
    rw [hk, show κ' * κ' = 1 by rcases hκ' with rfl | rfl <;> norm_num, one_mul]
    positivity
  rw [← hd', hd] at e2
  have e1 := side_sign hu hua h1 hs0 e2
  have hκκ : κ = κ' := by
    rcases hκ with rfl | rfl <;> rcases hκ' with rfl | rfl <;> first | rfl | nlinarith
  subst hκκ
  have hw : ‖F.u v' - F.u v‖ ≤ 2 / 100 := by
    have := norm_sub_le (F.u v' - F.u a) (F.u v - F.u a)
    rw [sub_sub_sub_cancel_right] at this
    linarith
  have h3 : √3 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  refine eq_of_same_offset hX F h₂ h₄ hw (c := -κ * sOff X) ?_ ?_ ho ho'
  · rw [hs]; rcases hκ with rfl | rfl <;> norm_num
  · rw [hτ, abs_le]; constructor <;> nlinarith [Real.sqrt_nonneg 3]

/-- Pure real core in the frame `(e, perp e)`. -/
private theorem cap_real {x₀ y A B b b' : ℝ} (hy : y ≤ 0) (hA : 0 < A) (hA' : A < 1 / 100)
    (hB : 0 < B) (hB' : B < 1 / 100) (hb : 0 < b) (hb2 : b ^ 2 = 1 - A ^ 2) (hb' : 0 < b')
    (hb2' : b' ^ 2 = 1 - B ^ 2) (h1 : 0 ≤ x₀ * A + y * b) (h2 : 0 ≤ (1 - x₀) * B + y * b') :
    x₀ ^ 2 + y ^ 2 < 1 ∨ (x₀ - 1) ^ 2 + y ^ 2 < 1 := by
  have hb99 : 99 / 100 ≤ b := by nlinarith
  have hb99' : 99 / 100 ≤ b' := by nlinarith
  have hny : 0 ≤ -y := by linarith
  have k1 : -y * (99 / 100) ≤ -y * b := mul_le_mul_of_nonneg_left hb99 hny
  have k2 : -y * (99 / 100) ≤ -y * b' := mul_le_mul_of_nonneg_left hb99' hny
  have hx0 : 0 ≤ x₀ := by
    by_contra hc; push Not at hc; nlinarith [mul_neg_of_neg_of_pos hc hA]
  have hx1 : x₀ ≤ 1 := by
    by_contra hc; push Not at hc
    have : 1 - x₀ < 0 := by linarith
    nlinarith [mul_neg_of_neg_of_pos this hB]
  have hy1 : -y * (99 / 100) ≤ x₀ / 100 := by
    nlinarith [mul_le_mul_of_nonneg_left hA'.le hx0]
  have hy2 : -y * (99 / 100) ≤ (1 - x₀) / 100 := by
    have : 0 ≤ 1 - x₀ := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hB'.le this]
  rcases le_total x₀ (1 / 2) with hx | hx
  · left
    have : -y ≤ 1 / 100 := by linarith
    nlinarith
  · right
    have : -y ≤ 1 / 100 := by linarith
    nlinarith

/-- Coordinate form, with `e = q − p`, `v = x − p`. -/
private theorem cap_coord {e0 e1 v0 v1 a0 a1 c0 c1 n0 n1 : ℝ}
    (he : e0 ^ 2 + e1 ^ 2 = 1) (ha : a0 ^ 2 + a1 ^ 2 = 1)
    (hc : c0 ^ 2 + c1 ^ 2 = 1)
    (hA : 0 < e0 * a0 + e1 * a1) (hA' : e0 * a0 + e1 * a1 < 1 / 100)
    (hB : 0 < -(e0 * c0 + e1 * c1)) (hB' : -(e0 * c0 + e1 * c1) < 1 / 100)
    (hdet : a0 * e1 - a1 * e0 < 0) (hdet2 : 0 < e0 * c1 - e1 * c0)
    (hn : n0 ^ 2 + n1 ^ 2 = 1)
    (hnq : n0 * e0 + n1 * e1 = 0) (hnu : 0 < n0 * a0 + n1 * a1)
    (k1 : 0 ≤ v0 * a0 + v1 * a1) (k2 : 0 ≤ (v0 - e0) * c0 + (v1 - e1) * c1)
    (hcap : v0 * n0 + v1 * n1 ≤ 0) :
    v0 ^ 2 + v1 ^ 2 < 1 ∨ (v0 - e0) ^ 2 + (v1 - e1) ^ 2 < 1 := by
  have hn0 : n0 = -(e0 * n1 - e1 * n0) * e1 := by linear_combination (-n0) * he + e0 * hnq
  have hn1 : n1 = (e0 * n1 - e1 * n0) * e0 := by linear_combination (-n1) * he + e1 * hnq
  obtain ⟨s, hs⟩ : ∃ s, s = e0 * n1 - e1 * n0 := ⟨_, rfl⟩
  rw [← hs] at hn0 hn1
  have hs2 : s ^ 2 = 1 := by
    have : n0 ^ 2 + n1 ^ 2 = s ^ 2 * (e0 ^ 2 + e1 ^ 2) := by rw [hn0, hn1]; ring
    rw [he, hn] at this; linarith
  have hbpos : 0 < e0 * a1 - e1 * a0 := by linarith
  have hsb : 0 < s * (e0 * a1 - e1 * a0) := by
    have : n0 * a0 + n1 * a1 = s * (e0 * a1 - e1 * a0) := by rw [hn0, hn1]; ring
    linarith
  have hspos : 0 < s := by
    by_contra hc; push Not at hc
    have := mul_nonpos_of_nonpos_of_nonneg hc hbpos.le
    linarith
  have hs1 : s = 1 := by
    have : (s - 1) * (s + 1) = 0 := by linear_combination hs2
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hy : e0 * v1 - e1 * v0 ≤ 0 := by
    have : v0 * n0 + v1 * n1 = s * (e0 * v1 - e1 * v0) := by rw [hn0, hn1]; ring
    rw [hs1] at this; linarith
  have r := cap_real (x₀ := e0 * v0 + e1 * v1) (y := e0 * v1 - e1 * v0) (A := e0 * a0 + e1 * a1)
    (B := -(e0 * c0 + e1 * c1)) (b := e0 * a1 - e1 * a0) (b' := e0 * c1 - e1 * c0) hy hA hA'
    hB hB' hbpos (by linear_combination (a0 ^ 2 + a1 ^ 2) * he + ha) hdet2
    (by linear_combination (c0 ^ 2 + c1 ^ 2) * he + hc)
    (by
      have : (e0 * v0 + e1 * v1) * (e0 * a0 + e1 * a1) + (e0 * v1 - e1 * v0) * (e0 * a1 - e1 * a0)
          = v0 * a0 + v1 * a1 := by linear_combination (v0 * a0 + v1 * a1) * he
      linarith)
    (by
      have : (1 - (e0 * v0 + e1 * v1)) * -(e0 * c0 + e1 * c1) +
          (e0 * v1 - e1 * v0) * (e0 * c1 - e1 * c0) = (v0 - e0) * c0 + (v1 - e1) * c1 := by
        linear_combination (v0 * c0 + v1 * c1) * he
      linarith)
  rcases r with r | r
  · left
    have : (e0 * v0 + e1 * v1) ^ 2 + (e0 * v1 - e1 * v0) ^ 2 = v0 ^ 2 + v1 ^ 2 := by
      linear_combination (v0 ^ 2 + v1 ^ 2) * he
    linarith
  · right
    have : (e0 * v0 + e1 * v1 - 1) ^ 2 + (e0 * v1 - e1 * v0) ^ 2 =
        (v0 - e0) ^ 2 + (v1 - e1) ^ 2 := by
      linear_combination (v0 ^ 2 + v1 ^ 2 - 1) * he
    linarith

/-- **(R)** rows are cyclic orders (K-row): the cap of `K` cut off by the line of a pure K–K
T-edge `pq` (on the side away from `u_p`) lies within distance `< 1` of `p` or `q`.  Hence it
contains no other point of `X`.  *Not used by the slot formulation.*

TODO: none — proved (`cap_real`, `cap_coord`; `ang(u_p, u_q) ≤ β` unused).
What's missing: (was) coordinates `p = (0,0)`, `q = (1,0)`, `u_p = (sin ε, cos ε)`,
`u_q = (−sin ε′, cos ε′)` with `ε, ε′ ∈ (0, arcsin β)`; the cap lies in the triangle
`{y ≤ 0, y ≥ −x tan ε, y ≥ (x − 1) tan ε′}`, every point of which is within
`√(1/4 + tan²(arcsin β)) < 1` of `p` or `q`.
Acceptance: no `sorry`.
Depends on: `neg_mem_normalCone`, `T2`. Difficulty M. -/
theorem rowR_cap_K (hX : Normal X) (F : DirField X) {p q n : Pt} (h : RowR F p q)
    (hpD : p ∉ Dset X) (hn : ‖n‖ = 1) (hnq : inner ℝ n (q - p) = 0)
    (hnu : 0 < inner ℝ n (F.u p)) {x : Pt} (hx : x ∈ KBall X) (hcap : inner ℝ (x - p) n ≤ 0) :
    dist x p < 1 ∨ dist x q < 1 := by
  have hp : p ∈ Sset X := h.1.1
  have hq : q ∈ Sset X := h.1.2.1
  have hqD : q ∉ Dset X := fun hq' => hpD (h.2.2 hq')
  obtain ⟨hstep, hA, hA', hdet⟩ := h.1.step
  obtain ⟨-, -, -, -, ⟨hB, hB', -, -⟩, hs2⟩ := T2 hX F h.1
  have hpK := ball_polygon_a (Finset.mem_filter.1 hp).1 hpD
  have hqK := ball_polygon_a (Finset.mem_filter.1 hq).1 hqD
  have k1 : 0 ≤ inner ℝ (x - p) (F.u p) := by
    have := neg_mem_normalCone hpK (F.partner_mem p hp) (F.partner_K p hp hpD)
      (dist p (F.partner p))⁻¹ (inv_nonneg.2 dist_nonneg) x hx
    rw [inner_neg_right] at this
    have e : F.u p = (dist p (F.partner p))⁻¹ • (F.partner p - p) := rfl
    rw [e]; linarith
  have k2 : 0 ≤ inner ℝ (x - q) (F.u q) := by
    have := neg_mem_normalCone hqK (F.partner_mem q hq) (F.partner_K q hq hqD)
      (dist q (F.partner q))⁻¹ (inv_nonneg.2 dist_nonneg) x hx
    rw [inner_neg_right] at this
    have e : F.u q = (dist q (F.partner q))⁻¹ • (F.partner q - q) := rfl
    rw [e]; linarith
  have hup := unit_sq (F.norm_u hp)
  have huq := unit_sq (F.norm_u hq)
  have hn' := unit_sq hn
  have he : ‖q - p‖ ^ 2 = 1 := by rw [hstep]; norm_num
  rw [norm_sq_pt] at he
  have hβ : beta = 1 / 100 := rfl
  rw [hβ] at hA' hB'
  have d1 := dist_sq_pt x p
  have d2 := dist_sq_pt x q
  simp only [inner_pt, det2_pt, PiLp.sub_apply, one_mul] at hA hA' hB hB' hdet hs2
  simp only [inner_pt, PiLp.sub_apply] at hnq hnu k1 k2 hcap he
  have r := cap_coord (e0 := q 0 - p 0) (e1 := q 1 - p 1) (v0 := x 0 - p 0) (v1 := x 1 - p 1)
    he hup huq hA hA' (by linarith) (by linarith) hdet (by linarith) hn' (by linarith)
    hnu k1 (by linarith) hcap
  rcases r with r | r
  · left; nlinarith [dist_nonneg (x := x) (y := p)]
  · right; nlinarith [dist_nonneg (x := x) (y := q)]

/-! ## (B′), (W) -/

/-- Real core of the (B′) step: two unit vectors `(aᵢ, cᵢ)` with elevations in `(0, 1/100)` on
opposite sides, a unit `(x, y)` making a nonnegative product with the second: the product with
the first is `≤ 1/40`. -/
private theorem eta_real {a₁ c₁ a₂ c₂ x y : ℝ} (n1 : a₁ ^ 2 + c₁ ^ 2 = 1) (n2 : a₂ ^ 2 + c₂ ^ 2 = 1)
    (nw : x ^ 2 + y ^ 2 = 1) (h1 : 0 < a₁) (h1' : a₁ < 1 / 100) (h2 : 0 < a₂)
    (h2' : a₂ < 1 / 100) (hs : c₁ * c₂ < 0) (hζ : 0 ≤ a₂ * x + c₂ * y) :
    a₁ * x + c₁ * y ≤ 1 / 40 := by
  have hx : |x| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith [sq_nonneg y]
  have hc₁ : |c₁| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith [sq_nonneg a₁]
  have hc₂' : |c₂| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith [sq_nonneg a₂]
  have hc₂ : c₂ ≠ 0 := by rintro rfl; simp at hs
  have ha2 : a₂ ^ 2 < 1 / 10000 := by nlinarith
  have hsq : 0.9999 ≤ c₂ ^ 2 := by linarith
  rw [abs_le] at hx hc₁ hc₂'
  -- `κ c₂ ≥ 0.99` and `κ c₁ > 0` for the sign `κ` of `c₂`
  obtain ⟨κ, hκ, hκc₂, hκc₁⟩ : ∃ κ : ℝ, (κ = 1 ∨ κ = -1) ∧ 0.99 ≤ κ * c₂ ∧ κ * c₁ < 0 := by
    rcases lt_or_gt_of_ne hc₂ with hc | hc
    · refine ⟨-1, Or.inr rfl, by nlinarith, ?_⟩
      by_contra h; push Not at h
      have : c₁ ≤ 0 := by linarith
      nlinarith [mul_nonneg_of_nonpos_of_nonpos this hc.le]
    · refine ⟨1, Or.inl rfl, by nlinarith, ?_⟩
      by_contra h; push Not at h
      have : 0 ≤ c₁ := by linarith
      nlinarith [mul_nonneg this hc.le]
  have k1 : (κ * c₁) * (c₂ * y) ≤ (κ * c₁) * (-(a₂ * x)) :=
    mul_le_mul_of_nonpos_left (by linarith) hκc₁.le
  have hS1 : |κ * c₂ * a₁ - κ * c₁ * a₂| ≤ 2 / 100 := by
    have e1 : |κ * c₂| ≤ 1 := by
      rcases hκ with rfl | rfl <;> rw [abs_le] <;> constructor <;> linarith
    have e2 : |κ * c₁| ≤ 1 := by
      rcases hκ with rfl | rfl <;> rw [abs_le] <;> constructor <;> linarith
    have := abs_sub (κ * c₂ * a₁) (κ * c₁ * a₂)
    rw [abs_mul (κ * c₂), abs_mul (κ * c₁), abs_of_pos h1, abs_of_pos h2] at this
    have := mul_le_mul_of_nonneg_right e1 h1.le
    have := mul_le_mul_of_nonneg_right e2 h2.le
    linarith
  have k2 : x * (κ * c₂ * a₁ - κ * c₁ * a₂) ≤ 2 / 100 := by
    have := abs_mul x (κ * c₂ * a₁ - κ * c₁ * a₂)
    have hx' : |x| ≤ 1 := abs_le.2 hx
    have := mul_le_mul hx' hS1 (abs_nonneg _) zero_le_one
    have := le_abs_self (x * (κ * c₂ * a₁ - κ * c₁ * a₂))
    linarith
  have k3 : (κ * c₂) * (a₁ * x + c₁ * y) ≤ 2 / 100 := by
    have e : (κ * c₂) * (a₁ * x + c₁ * y) = x * (κ * c₂ * a₁) + (κ * c₁) * (c₂ * y) := by ring
    have e' : (κ * c₁) * (-(a₂ * x)) = -(x * (κ * c₁ * a₂)) := by ring
    have e'' : x * (κ * c₂ * a₁ - κ * c₁ * a₂) = x * (κ * c₂ * a₁) - x * (κ * c₁ * a₂) := by ring
    linarith
  by_contra hη; push Not at hη
  have : 0.99 * (1 / 40) ≤ (κ * c₂) * (a₁ * x + c₁ * y) :=
    mul_le_mul hκc₂ hη.le (by norm_num) (by linarith)
  linarith

/-- Vector form of `eta_real` in the frame of `u`. -/
private theorem eta_small {u ŵ e₁ e₂ : Pt} (hu : ‖u‖ = 1) (hŵ : ‖ŵ‖ = 1) (he₁ : ‖e₁‖ = 1)
    (he₂ : ‖e₂‖ = 1) (a₁ : 0 < inner ℝ e₁ u) (a₁' : inner ℝ e₁ u < beta)
    (a₂ : 0 < inner ℝ e₂ u) (a₂' : inner ℝ e₂ u < beta) (hs : det2 u e₁ * det2 u e₂ < 0)
    (hζ : 0 ≤ inner ℝ e₂ ŵ) : inner ℝ e₁ ŵ ≤ 1 / 40 := by
  have f1 := inner_mul_add_det_mul u e₁ ŵ
  have f2 := inner_mul_add_det_mul u e₂ ŵ
  have n1 := inner_sq_add_det_sq (e := e₁) hu
  have n2 := inner_sq_add_det_sq (e := e₂) hu
  have nw := inner_sq_add_det_sq (e := ŵ) hu
  rw [hu, one_pow, one_mul] at f1 f2
  rw [he₁] at n1; rw [he₂] at n2; rw [hŵ] at nw
  rw [real_inner_comm e₁ u, real_inner_comm ŵ u] at f1
  rw [real_inner_comm e₂ u, real_inner_comm ŵ u] at f2
  have hb : beta = 1 / 100 := rfl
  rw [hb] at a₁' a₂'
  rw [← f1]; rw [← f2] at hζ
  exact eta_real (by linarith) (by linarith) (by linarith) a₁ a₁' a₂ a₂' hs hζ

/-- **(B′) step**: `z` on `C(w, Δ)` with T-neighbours `q` (the one we step to) and `p` on the
two sides; then `q` is on `C(w, Δ)` too (at `τ = √3/2`, `t > 0.866`). -/
private theorem step_on_circle (hX : Normal X) (F : DirField X) (hτ : tau X = √3 / 2)
    {w z q p : Pt} (hw : w ∈ X) (hz : z ∈ Sset X) (hq : q ∈ Sset X) (hp : p ∈ Sset X)
    (hzq : dist z q = 1) (hzp : dist z p = 1) (a₁ : 0 < inner ℝ (q - z) (F.u z))
    (a₁' : inner ℝ (q - z) (F.u z) < beta) (a₂ : 0 < inner ℝ (p - z) (F.u z))
    (a₂' : inner ℝ (p - z) (F.u z) < beta)
    (hs : det2 (F.u z) (q - z) * det2 (F.u z) (p - z) < 0) (hd : dist z w = diam X) :
    dist q w = diam X := by
  have hpos := hX.dist2_pos
  have hT := two_of_pos hpos
  have hΔ : 0 < diam X := hpos.trans hT.lt
  have hzX := Sset_sub hz
  have hqX := Sset_sub hq
  have hpX := Sset_sub hp
  set ŵ := (diam X)⁻¹ • (w - z)
  have hŵ : ‖ŵ‖ = 1 := by
    rw [norm_smul, ← dist_eq_norm, dist_comm, hd, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hΔ),
      inv_mul_cancel₀ hΔ.ne']
  have he₁ : ‖q - z‖ = 1 := by rw [← dist_eq_norm, dist_comm, hzq]
  have he₂ : ‖p - z‖ = 1 := by rw [← dist_eq_norm, dist_comm, hzp]
  have hζ : 0 ≤ inner ℝ (p - z) ŵ := by
    rw [real_inner_smul_right]
    have := two_inner_sub p z w
    have hpw := hT.le_diam p hpX w hw
    rw [dist_comm p z, hzp, dist_comm w z, hd] at this
    have : 0 ≤ inner ℝ (p - z) (w - z) := by nlinarith [dist_nonneg (x := p) (y := w)]
    positivity
  have hη := eta_small (F.norm_u hz) hŵ he₁ he₂ a₁ a₁' a₂ a₂' hs hζ
  rw [real_inner_smul_right] at hη
  have hcos := two_inner_sub q z w
  rw [dist_comm q z, hzq, dist_comm w z, hd] at hcos
  have hη' : inner ℝ (q - z) (w - z) ≤ diam X / 40 := by
    rw [inv_mul_le_iff₀ hΔ] at hη; linarith
  obtain ⟨ht1, -⟩ := tgap_bounds_exact hX hτ
  have h3 : (1.732 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hgap : diam X - dist2 X = tgap X := rfl
  have hfar : dist2 X < dist q w := by
    by_contra hle; push Not at hle
    have : dist q w ^ 2 ≤ dist2 X ^ 2 := pow_le_pow_left₀ dist_nonneg hle 2
    nlinarith
  rcases hT.gap q hqX w hw with h | h
  · exact absurd h (not_le.2 hfar)
  · exact h

/-- **(B′)** the pure right D-walk from the right base end `b` of a triangle stays on
`C(w_v, Δ)`.

TODO: none — proved (`step_on_circle`: with `ŵ = (w − z)/Δ`, the left neighbour gives
`(p − z)·ŵ ≥ 0`, hence `η = (q − z)·ŵ ≤ 1/40` (`eta_real`) and `|qw|² ≥ 1 + Δ² − Δ/20 > Δ₂²`).
What's missing: (was) induction on `k`; interior walk vertices have normal cones of `conv X` in the
cap of radius `arcsin β` around `u` (inwardness against both neighbours); the diametral
direction `ŵ_k = (w − z_k)/Δ` is such a normal, so `η = (z_{k+1} − z_k)·ŵ_k < sin(2 arcsin β)`
`< t`; `lemmaB`-type identity `|z_{k+1}w|² = 1 + Δ² − 2Δη > Δ₂²` forces `|z_{k+1}w| = Δ`.
Acceptance: no `sorry`.
Depends on: `exact_identity_a`, `dist_le_dist2`, `tgap_bounds_exact`. Difficulty L. -/
theorem Bprime_walk_right (hX : Normal X) (F : DirField X) (hτ : tau X = √3 / 2) {v a b : Pt}
    (ht : IsTri F v a b) (z : ℕ → Pt) (N : ℕ) (hz0 : z 0 = b)
    (hstep : ∀ k < N, RowR F (z k) (z (k + 1))) :
    ∀ k ≤ N, dist (z k) (F.partner v) = diam X := by
  obtain ⟨hva, hvb, -, -, hab, -⟩ := ht
  have hwX : F.partner v ∈ X := F.partner_mem v hva.1
  have hleft : ∀ k < N, ∃ p, RowR F p (z k) := by
    intro k hk
    cases k with
    | zero => exact ⟨a, hz0 ▸ hab⟩
    | succ k => exact ⟨z k, hstep k (by omega)⟩
  intro k hk
  induction k with
  | zero => rw [hz0]; exact hvb.2.2.2.2.2
  | succ k ih =>
    have hk' : k < N := by omega
    obtain ⟨p, hp⟩ := hleft k hk'
    have hq := hstep k hk'
    obtain ⟨-, -, hd1, -, ⟨a₁, a₁', -, -⟩, s₁⟩ := hq.1
    have hp' := T2 hX F hp.1
    obtain ⟨-, -, hd2, -, ⟨a₂, a₂', -, -⟩, s₂⟩ := hp'
    exact step_on_circle hX F hτ hwX hq.1.1 hq.1.2.1 hp.1.1 hd1 hd2 a₁ a₁' a₂ a₂'
      (by nlinarith) (ih (by omega))

/-- **(B′)** the pure left D-walk from the left base end `a` stays on `C(w_v, Δ)`.

TODO: none — proved (mirror image, via `step_on_circle`).
What's missing: (was) mirror image of `Bprime_walk_right`.
Acceptance: no `sorry`.
Depends on: as `Bprime_walk_right`. Difficulty L. -/
theorem Bprime_walk_left (hX : Normal X) (F : DirField X) (hτ : tau X = √3 / 2) {v a b : Pt}
    (ht : IsTri F v a b) (z : ℕ → Pt) (N : ℕ) (hz0 : z 0 = a)
    (hstep : ∀ k < N, RowR F (z (k + 1)) (z k)) :
    ∀ k ≤ N, dist (z k) (F.partner v) = diam X := by
  obtain ⟨hva, hvb, -, -, hab, -⟩ := ht
  have hwX : F.partner v ∈ X := F.partner_mem v hva.1
  have hright : ∀ k < N, ∃ p, RowR F (z k) p := by
    intro k hk
    cases k with
    | zero => exact ⟨b, hz0 ▸ hab⟩
    | succ k => exact ⟨z k, hstep k (by omega)⟩
  intro k hk
  induction k with
  | zero => rw [hz0]; exact hva.2.2.2.2.2
  | succ k ih =>
    have hk' : k < N := by omega
    obtain ⟨p, hp⟩ := hright k hk'
    have hq := T2 hX F (hstep k hk').1
    obtain ⟨-, -, hd1, -, ⟨a₁, a₁', -, -⟩, s₁⟩ := hq
    obtain ⟨-, -, hd2, -, ⟨a₂, a₂', -, -⟩, s₂⟩ := hp.1
    exact step_on_circle hX F hτ hwX hp.1.1 (hstep k hk').1.1 hp.1.2.1 hd1 hd2 a₁ a₁' a₂ a₂'
      (by nlinarith) (ih (by omega))

private theorem rot_apply0 (θ : ℝ) (x : Pt) :
    rot θ x 0 = Real.cos θ * x 0 - Real.sin θ * x 1 := by simp [rot]

private theorem rot_apply1 (θ : ℝ) (x : Pt) :
    rot θ x 1 = Real.sin θ * x 0 + Real.cos θ * x 1 := by simp [rot]

/-- `|u|² det(w, e) = (w·u) det(u, e) − det(u, w) (e·u)`. -/
private theorem det_frame (u w e : Pt) :
    ‖u‖ ^ 2 * det2 w e = inner ℝ w u * det2 u e - det2 u w * inner ℝ e u := by
  rw [norm_sq_pt, det2_pt, det2_pt, det2_pt, inner_pt, inner_pt]; ring

/-- Two points of `C(w, Δ)` at distance `1`, the second counterclockwise from the first
(`det(r₀, r₁) > 0`): `r₁ = rot α₁ r₀`. -/
private theorem rot_of_det {r₀ r₁ : Pt} {Δ : ℝ} (hΔ : 1 ≤ Δ) (h₀ : ‖r₀‖ = Δ) (h₁ : ‖r₁‖ = Δ)
    (h01 : ‖r₁ - r₀‖ = 1) (hdet : 0 < det2 r₀ r₁) :
    r₁ = rot (2 * Real.arcsin (1 / (2 * Δ))) r₀ := by
  set sα := 1 / (2 * Δ)
  have hs0 : 0 < sα := by positivity
  have hs1 : sα ≤ 1 / 2 := by
    simp only [sα]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  set C := Real.cos (2 * Real.arcsin sα)
  set S := Real.sin (2 * Real.arcsin sα)
  have hC : C = 1 - 2 * sα ^ 2 := by
    simp only [C]
    rw [Real.cos_two_mul', Real.cos_sq', Real.sin_arcsin (by linarith) (by linarith)]; ring
  have hS0 : 0 ≤ S := by
    have := Real.arcsin_nonneg.2 hs0.le
    have := Real.arcsin_le_pi_div_two sα
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hCS : C ^ 2 + S ^ 2 = 1 := by rw [add_comm]; exact Real.sin_sq_add_cos_sq _
  have n0 := norm_sq_pt r₀
  have n1 := norm_sq_pt r₁
  have n01 := norm_sq_pt (r₁ - r₀)
  rw [h₀] at n0; rw [h₁] at n1; rw [h01] at n01
  simp only [PiLp.sub_apply] at n01
  rw [det2_pt] at hdet
  set P := r₀ 0 * r₁ 0 + r₀ 1 * r₁ 1
  set D := r₀ 0 * r₁ 1 - r₀ 1 * r₁ 0
  have hP : P = C * Δ ^ 2 := by
    rw [hC]; simp only [sα]; field_simp; simp only [P]; nlinarith
  have hPD : P ^ 2 + D ^ 2 = Δ ^ 4 := by
    have : P ^ 2 + D ^ 2 = (r₀ 0 ^ 2 + r₀ 1 ^ 2) * (r₁ 0 ^ 2 + r₁ 1 ^ 2) := by ring
    rw [this, ← n0, ← n1]; ring
  have hD : D = S * Δ ^ 2 := by
    have h2 : D ^ 2 = (S * Δ ^ 2) ^ 2 := by
      rw [hP] at hPD
      have : S ^ 2 = 1 - C ^ 2 := by linarith
      nlinarith
    have : 0 ≤ S * Δ ^ 2 := by positivity
    nlinarith [sq_nonneg (D - S * Δ ^ 2), sq_nonneg (D + S * Δ ^ 2)]
  have hΔ2 : 0 < Δ ^ 2 := by positivity
  rw [pt_ext_iff, rot_apply0, rot_apply1]
  constructor
  · have e : r₁ 0 * Δ ^ 2 = P * r₀ 0 - D * r₀ 1 := by
      rw [n0]; simp only [P, D]; ring
    rw [hP, hD] at e
    have : (r₁ 0 - (C * r₀ 0 - S * r₀ 1)) * Δ ^ 2 = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_right hΔ2.ne'
    linarith
  · have e : r₁ 1 * Δ ^ 2 = P * r₀ 1 + D * r₀ 0 := by
      rw [n0]; simp only [P, D]; ring
    rw [hP, hD] at e
    have : (r₁ 1 - (S * r₀ 0 + C * r₀ 1)) * Δ ^ 2 = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_right hΔ2.ne'
    linarith

/-- Orientation from two neighbours: with `ŵ = x u + y u^⊥` making nonnegative products with a
right step `e₁` and a left step `e₂`, `det(ŵ, e₁) < 0`. -/
private theorem det_real {a₁ c₁ a₂ c₂ x y : ℝ} (n1 : a₁ ^ 2 + c₁ ^ 2 = 1)
    (n2 : a₂ ^ 2 + c₂ ^ 2 = 1) (nw : x ^ 2 + y ^ 2 = 1) (h1 : 0 < a₁) (h1' : a₁ < 1 / 100)
    (h2 : 0 < a₂) (h2' : a₂ < 1 / 100) (hc1 : c₁ < 0) (hc2 : 0 < c₂)
    (hη : 0 ≤ a₁ * x + c₁ * y) (hζ : 0 ≤ a₂ * x + c₂ * y) : x * c₁ - y * a₁ < 0 := by
  have hc1' : c₁ ≤ -0.99 := by nlinarith
  have hc2' : 0.99 ≤ c₂ := by nlinarith
  have hx : 0 < x := by
    by_contra h; push Not at h
    have hy1 : 0 ≤ y := by
      by_contra hy; push Not at hy
      nlinarith [mul_nonpos_of_nonneg_of_nonpos h2.le h, mul_neg_of_pos_of_neg hc2 hy]
    have hy2 : y ≤ 0 := by
      by_contra hy; push Not at hy
      nlinarith [mul_nonpos_of_nonneg_of_nonpos h1.le h, mul_neg_of_neg_of_pos hc1 hy]
    have hy : y = 0 := le_antisymm hy2 hy1
    subst hy
    have : x = -1 := by nlinarith
    subst this; nlinarith
  -- `c₂ y ≥ −a₂ x`, so `−y a₁ ≤ a₁ a₂ x / c₂`
  have k : -(y * a₁) * c₂ ≤ a₁ * a₂ * x := by nlinarith
  have ha12 : a₁ * a₂ ≤ 1 / 10000 := by nlinarith
  have k2 : a₁ * a₂ * x ≤ 1 / 10000 * x := mul_le_mul_of_nonneg_right ha12 hx.le
  have hxc : x * c₁ ≤ -0.99 * x := by nlinarith
  rcases le_or_gt (-(y * a₁)) 0 with k' | k'
  · linarith
  · have : -(y * a₁) * 0.99 ≤ -(y * a₁) * c₂ := mul_le_mul_of_nonneg_left hc2' k'.le
    linarith

/-- Orientation from closeness: `|ŵ − u| ≤ 0.011`, `e` a left step of `u`: `det(ŵ, e) > 0`. -/
private theorem det_pos_of_close {u ŵ e : Pt} (hu : ‖u‖ = 1) (hŵ : ‖ŵ‖ = 1) (he : ‖e‖ = 1)
    (hclose : ‖ŵ - u‖ ≤ 0.011) (ha : 0 < inner ℝ e u) (ha' : inner ℝ e u < 1 / 100)
    (hc : 0 < det2 u e) : 0 < det2 ŵ e := by
  have hf := det_frame u ŵ e
  rw [hu, one_pow, one_mul] at hf
  rw [hf]
  have ne := inner_sq_add_det_sq (e := e) hu
  rw [he] at ne
  have hx : 0.9999 ≤ inner ℝ ŵ u := by
    have e := @norm_sub_sq_real _ _ _ ŵ u
    rw [hŵ, hu] at e
    nlinarith [norm_nonneg (ŵ - u)]
  have hy : |det2 u ŵ| ≤ 0.011 := by
    have : det2 u ŵ = det2 u (ŵ - u) := by rw [det2_pt, det2_pt]; simp; ring
    rw [this]
    refine (abs_det2_leR u (ŵ - u)).trans ?_
    rw [hu, one_mul]; exact hclose
  have hc' : 0.99 ≤ det2 u e := by nlinarith
  rw [abs_le] at hy
  nlinarith

/-- Vector form of `det_real`. -/
private theorem det_neg_two_nbrs {u ŵ e₁ e₂ : Pt} (hu : ‖u‖ = 1) (hŵ : ‖ŵ‖ = 1)
    (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1) (a₁ : 0 < inner ℝ e₁ u) (a₁' : inner ℝ e₁ u < beta)
    (a₂ : 0 < inner ℝ e₂ u) (a₂' : inner ℝ e₂ u < beta) (hc1 : det2 u e₁ < 0)
    (hc2 : 0 < det2 u e₂) (hη : 0 ≤ inner ℝ e₁ ŵ) (hζ : 0 ≤ inner ℝ e₂ ŵ) : det2 ŵ e₁ < 0 := by
  have f1 := inner_mul_add_det_mul u e₁ ŵ
  have f2 := inner_mul_add_det_mul u e₂ ŵ
  have n1 := inner_sq_add_det_sq (e := e₁) hu
  have n2 := inner_sq_add_det_sq (e := e₂) hu
  have nw := inner_sq_add_det_sq (e := ŵ) hu
  have hf := det_frame u ŵ e₁
  rw [hu, one_pow, one_mul] at f1 f2 hf
  rw [he₁] at n1; rw [he₂] at n2; rw [hŵ] at nw
  rw [real_inner_comm e₁ u, real_inner_comm ŵ u] at f1
  rw [real_inner_comm e₂ u, real_inner_comm ŵ u] at f2
  have hb : beta = 1 / 100 := rfl
  rw [hb] at a₁' a₂'
  rw [← f1] at hη; rw [← f2] at hζ
  rw [hf]
  have := det_real (a₁ := inner ℝ e₁ u) (c₁ := det2 u e₁) (a₂ := inner ℝ e₂ u)
    (c₂ := det2 u e₂) (x := inner ℝ ŵ u) (y := det2 u ŵ) (by linarith) (by linarith)
    (by linarith) a₁ a₁' a₂ a₂' hc1 hc2 hη hζ
  linarith

/-- For `y ∈ X` at distance `1` from `z ∈ C(w, Δ)`: `(y − z)·(w − z) ≥ 1/2`. -/
private theorem inner_nonneg_of_diam (hX : Normal X) {w z y : Pt} (hw : w ∈ X) (hy : y ∈ X)
    (hzy : dist z y = 1) (hd : dist z w = diam X) : 1 / 2 ≤ inner ℝ (y - z) (w - z) := by
  have hT := two_of_pos hX.dist2_pos
  have := two_inner_sub y z w
  have hyw := hT.le_diam y hy w hw
  rw [dist_comm y z, hzy, dist_comm w z, hd] at this
  nlinarith [dist_nonneg (x := y) (y := w)]

private theorem det2_smul_left' (c : ℝ) (a b : Pt) : det2 (c • a) b = c * det2 a b := by
  simp only [det2_pt, PiLp.smul_apply, smul_eq_mul]; ring

/-- **(B′)** consecutive walk vertices differ by the rotation `rot α₁` about `w = w_v`
(counterclockwise = right), starting with the base itself.

TODO: none — proved (`rot_of_det`; orientation from the two neighbours (`det_real`) for walk
steps and from `ŵ_b ≈ u_v ≈ u_b` (`det_pos_of_close`) for the base).
What's missing: (was) two points of `C(w,Δ) ∩ C(z_k, 1)` are `w + rot (±α₁) (z_k − w)`; the right
T-neighbour is the counterclockwise one because `ŵ_k` is within `arcsin β` of `u_{z_k}`.
Acceptance: no `sorry`.
Depends on: `Bprime_walk_right`, `rot`, `alpha1`. Difficulty L. -/
theorem Bprime_rot (hX : Normal X) (F : DirField X) (hτ : tau X = √3 / 2) {v a b : Pt}
    (ht : IsTri F v a b) (z : ℕ → Pt) (N : ℕ) (hz0 : z 0 = b)
    (hstep : ∀ k < N, RowR F (z k) (z (k + 1))) :
    b - F.partner v = rot (alpha1 X) (a - F.partner v) ∧
      ∀ k < N, z (k + 1) - F.partner v = rot (alpha1 X) (z k - F.partner v) := by
  have hwalk := Bprime_walk_right hX F hτ ht z N hz0 hstep
  obtain ⟨hva, hvb, gva, gvb, hab, -⟩ := ht
  set w := F.partner v
  have hwX : w ∈ X := F.partner_mem v hva.1
  have hpos := hX.dist2_pos
  have hT := two_of_pos hpos
  have hΔ : 0 < diam X := hpos.trans hT.lt
  have hΔ1 : 1 ≤ diam X := by have := hX.large; linarith [hT.lt]
  -- generic rotation step from an orientation
  have hrot : ∀ z q : Pt, dist z w = diam X → dist q w = diam X → dist z q = 1 →
      0 < det2 (z - w) (q - w) → q - w = rot (alpha1 X) (z - w) := by
    intro z q hz hq hzq hdet
    unfold alpha1
    refine rot_of_det hΔ1 (by rw [← dist_eq_norm, hz]) (by rw [← dist_eq_norm, hq]) ?_ hdet
    rw [show q - w - (z - w) = q - z by abel, ← dist_eq_norm, dist_comm, hzq]
  have hdetE : ∀ z q : Pt, det2 (z - w) (q - w) =
      -(diam X) * det2 ((diam X)⁻¹ • (w - z)) (q - z) := by
    intro z q
    rw [det2_smul_left', det2_pt, det2_pt]
    simp only [PiLp.sub_apply]
    field_simp; ring
  have hŵ : ∀ z, dist z w = diam X → ‖(diam X)⁻¹ • (w - z)‖ = 1 := by
    intro z hz
    rw [norm_smul, ← dist_eq_norm, dist_comm, hz, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hΔ),
      inv_mul_cancel₀ hΔ.ne']
  refine ⟨?_, fun k hk => ?_⟩
  · -- the base: orientation from `ŵ_b ≈ u_v ≈ u_b`
    have haw : dist a w = diam X := hva.2.2.2.2.2
    have hbw : dist b w = diam X := hvb.2.2.2.2.2
    have hab1 : dist a b = 1 := hab.1.2.2.1
    have hba := T2 hX F hab.1
    obtain ⟨hbS, haS, -, -, ⟨ea, ea', -, -⟩, ec⟩ := hba
    have hvw : dist v w = dist2 X := F.partner_K v hva.1 hva.2.1
    have huv : F.u v = (dist2 X)⁻¹ • (w - v) := by
      unfold DirField.u; rw [hvw]
    have hgood : ang (F.u v) (F.u b) ≤ beta := (mem_filter.1 (mem_filter.1 gvb).1).2 v b rfl
    have hvb1 : dist v b = 1 := hvb.2.2.2.2.1
    have hclose1 : ‖(diam X)⁻¹ • (w - b) - F.u v‖ ≤ 0.0002 := by
      rw [huv]
      have e : (diam X)⁻¹ • (w - b) - (dist2 X)⁻¹ • (w - v) =
          ((diam X)⁻¹ - (dist2 X)⁻¹) • (w - b) + (dist2 X)⁻¹ • (v - b) := by
        module
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, ← dist_eq_norm w b,
        ← dist_eq_norm v b, dist_comm w b, hbw, hvb1, abs_of_pos (inv_pos.2 hpos), mul_one]
      have hlt := hT.lt
      obtain ⟨-, ht2⟩ := tgap_bounds_exact hX hτ
      have h3 : √3 < 1.7321 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
      have hL := hX.large
      have hinv : (dist2 X)⁻¹ ≤ 1 / 10000 := by
        rw [inv_eq_one_div, div_le_div_iff₀ hpos (by norm_num)]; linarith
      have e2 : |(diam X)⁻¹ - (dist2 X)⁻¹| * diam X = (diam X - dist2 X) * (dist2 X)⁻¹ := by
        rw [abs_of_nonpos (by rw [sub_nonpos]; exact inv_anti₀ hpos hlt.le)]
        field_simp; ring
      rw [e2]
      have htg : diam X - dist2 X < 1 := by
        have : 1 / (2 * dist2 X) ≤ 1 / 20000 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        unfold tgap at ht2; linarith
      have := mul_le_mul_of_nonneg_right htg.le (inv_nonneg.2 hpos.le)
      nlinarith
    have hclose2 : ‖F.u v - F.u b‖ ≤ 1 / 100 :=
      (norm_sub_le_angR (F.norm_u hva.1) (F.norm_u hbS)).trans hgood
    have hclose : ‖(diam X)⁻¹ • (w - b) - F.u b‖ ≤ 0.011 := by
      have := norm_sub_le ((diam X)⁻¹ • (w - b) - F.u v) (F.u b - F.u v)
      rw [sub_sub_sub_cancel_right] at this
      rw [norm_sub_rev (F.u b)] at this
      linarith
    have hpos' := det_pos_of_close (F.norm_u hbS) (hŵ b hbw)
      (by rw [← dist_eq_norm, hab1]) hclose ea ea' (by linarith)
    have hd : 0 < det2 (a - w) (b - w) := by
      have e : det2 (a - w) (b - w) = -det2 (b - w) (a - w) := by
        rw [det2_pt, det2_pt]; ring
      rw [e, hdetE b a]; nlinarith
    exact hrot a b haw hbw hab1 hd
  · -- a walk step, orientation from the two neighbours of `z k`
    have hzk := hwalk k hk.le
    have hzk1 := hwalk (k + 1) hk
    have hq := hstep k hk
    obtain ⟨p, hp⟩ : ∃ p, RowR F p (z k) := by
      cases k with
      | zero => exact ⟨a, hz0 ▸ hab⟩
      | succ k => exact ⟨z k, hstep k (by omega)⟩
    obtain ⟨hzS, hqS, hd1, -, ⟨a₁, a₁', -, -⟩, s₁⟩ := hq.1
    obtain ⟨-, hpS, hd2, -, ⟨a₂, a₂', -, -⟩, s₂⟩ := T2 hX F hp.1
    have hη := inner_nonneg_of_diam hX hwX (Sset_sub hqS) hd1 hzk
    have hζ := inner_nonneg_of_diam hX hwX (Sset_sub hpS) hd2 hzk
    have hneg := det_neg_two_nbrs (F.norm_u hzS) (hŵ _ hzk)
      (by rw [← dist_eq_norm, dist_comm, hd1]) (by rw [← dist_eq_norm, dist_comm, hd2])
      a₁ a₁' a₂ a₂' (by linarith) (by linarith)
      (by rw [real_inner_smul_right]; positivity) (by rw [real_inner_smul_right]; positivity)
    refine hrot _ _ hzk hzk1 hd1 ?_
    rw [hdetE]; nlinarith

private theorem rot_rot (θ φ : ℝ) (x : Pt) : rot θ (rot φ x) = rot (θ + φ) x := by
  rw [pt_ext_iff]
  simp only [rot_apply0, rot_apply1, Real.cos_add, Real.sin_add]
  constructor <;> ring

private theorem norm_rot_sub_sq (ψ : ℝ) (r : Pt) :
    ‖rot ψ r - r‖ ^ 2 = 2 * (1 - Real.cos ψ) * ‖r‖ ^ 2 := by
  rw [norm_sq_pt, norm_sq_pt]
  simp only [PiLp.sub_apply, rot_apply0, rot_apply1]
  have := Real.sin_sq_add_cos_sq ψ
  linear_combination (r 0 ^ 2 + r 1 ^ 2) * this

/-- **(B′)** span: a walk of `N` right steps from the base satisfies `(N + 1)·α₁ ≤ π/3`
(points of `X` are `≤ Δ` apart; chord `2Δ sin(θ/2) ≤ Δ`), so D-walks are paths.

TODO: none — proved (induction on `N`, using `(N+1)α₁ ≤ π/3 + α₁ < π`).
What's missing: (was) `Bprime_rot` iterated: `z_N − w = rot((N+1)α₁)(a − w)`; `|z_N − a| ≤ Δ`.
Acceptance: no `sorry`.
Depends on: `Bprime_rot`, `dist_le_diam`. Difficulty M. -/
theorem Bprime_span (hX : Normal X) (F : DirField X) (hτ : tau X = √3 / 2) {v a b : Pt}
    (ht : IsTri F v a b) (z : ℕ → Pt) (N : ℕ) (hz0 : z 0 = b)
    (hstep : ∀ k < N, RowR F (z k) (z (k + 1))) : ((N : ℝ) + 1) * alpha1 X ≤ π / 3 := by
  obtain ⟨hbase, hsteps⟩ := Bprime_rot hX F hτ ht z N hz0 hstep
  obtain ⟨hva, hvb, -, -, -, -⟩ := ht
  set w := F.partner v
  set α := alpha1 X
  have hpos := hX.dist2_pos
  have hT := two_of_pos hpos
  have hΔ : 0 < diam X := hpos.trans hT.lt
  have hL := hX.large
  have hπ := Real.pi_gt_three
  -- `0 ≤ α ≤ 0.001`
  have hα0 : 0 ≤ α := by
    have : 0 ≤ Real.arcsin (1 / (2 * diam X)) := Real.arcsin_nonneg.2 (by positivity)
    simp only [α, alpha1]; linarith
  have hα1 : α ≤ 1 / 1000 := by
    have hx0 : 0 < 1 / (2 * diam X) := by positivity
    have hx1 : 1 / (2 * diam X) ≤ 1 / 20000 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith [hT.lt]
    obtain ⟨-, h⟩ := arcsin_bounds hx0 (by linarith)
    have : (1 / (2 * diam X)) ^ 3 ≤ 1 / 20000 := by
      calc (1 / (2 * diam X)) ^ 3 ≤ (1 / 20000) ^ 3 := by gcongr
        _ ≤ 1 / 20000 := by norm_num
    simp only [α, alpha1]; linarith
  -- positions on the circle
  have hzk : ∀ k ≤ N, z k - w = rot (((k : ℝ) + 1) * α) (a - w) := by
    intro k hk
    induction k with
    | zero => rw [hz0, hbase]; simp
    | succ k ih =>
      rw [hsteps k (by omega), ih (by omega), rot_rot]
      congr 1; push_cast; ring
  have hzX : ∀ k ≤ N, z k ∈ X := by
    intro k hk
    cases k with
    | zero => rw [hz0]; exact Sset_sub hvb.2.2.1
    | succ k => exact Sset_sub (hstep k (by omega)).1.2.1
  have haw : ‖a - w‖ = diam X := by rw [← dist_eq_norm]; exact hva.2.2.2.2.2
  have hcos : ∀ k ≤ N, 1 / 2 ≤ Real.cos (((k : ℝ) + 1) * α) := by
    intro k hk
    have hd := hT.le_diam (z k) (hzX k hk) a (Sset_sub hva.2.2.1)
    rw [dist_eq_norm, show z k - a = (z k - w) - (a - w) by abel, hzk k hk] at hd
    have h2 := norm_rot_sub_sq (((k : ℝ) + 1) * α) (a - w)
    rw [haw] at h2
    have : ‖rot (((k : ℝ) + 1) * α) (a - w) - (a - w)‖ ^ 2 ≤ diam X ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hd 2
    have hΔ2 : 0 < diam X ^ 2 := by positivity
    by_contra hlt; push Not at hlt
    have : 0 < (2 * (1 - Real.cos (((k : ℝ) + 1) * α)) - 1) * diam X ^ 2 :=
      mul_pos (by linarith) hΔ2
    nlinarith
  have key : ∀ k ≤ N, ((k : ℝ) + 1) * α ≤ π / 3 := by
    intro k
    induction k with
    | zero => intro _; simp; linarith
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have hc := hcos (k + 1) hk
      by_contra h; push Not at h
      have hle : ((((k + 1 : ℕ) : ℝ)) + 1) * α ≤ π := by push_cast at h1 ⊢; nlinarith
      have := Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) hle h
      rw [Real.cos_pi_div_three] at this
      linarith
  exact key N le_rfl

/-- **(W)** one centre per D-walk: if the base of a second triangle `A′` lies on the right walk
from the base of `A`, the two apexes have the same `Δ₂`-partner.

TODO: none — proved (walk extended by `b′`; frame `e = a′ − b′` at `b′`: the centres are
`b′ + ½e ± β e^⊥`, and the mirror case gives `(w − b′)·(w′ − b′) = ½ − Δ² < Δ²/2`).
What's missing: (was) both centres are at distance `Δ` from `a′, b′`; distinct centres are mirror
images in the line `a′b′`, and `a·e = ±1/(2Δ)` (second referee) gives `a·a* < 0`, contradicting
`exact_identity_a` at `b′`.
Acceptance: no `sorry`.
Depends on: `Bprime_walk_right`, `exact_identity_a`. Difficulty M–L. -/
theorem W_center (hX : Normal X) (F : DirField X) (hτ : tau X = √3 / 2) {v a b v' a' b' : Pt}
    (ht : IsTri F v a b) (ht' : IsTri F v' a' b') (z : ℕ → Pt) (N : ℕ) (hz0 : z 0 = b)
    (hstep : ∀ k < N, RowR F (z k) (z (k + 1))) (hk : ∃ k ≤ N, z k = a') :
    F.partner v = F.partner v' := by
  obtain ⟨k, hkN, hka⟩ := hk
  have hR' : RowR F a' b' := ht'.2.2.2.2.1
  set w := F.partner v
  set w' := F.partner v'
  -- the walk extended by `b′`
  let z' : ℕ → Pt := fun j => if j ≤ k then z j else b'
  have hz'0 : z' 0 = b := by simp [z', hz0]
  have hstep' : ∀ j < k + 1, RowR F (z' j) (z' (j + 1)) := by
    intro j hj
    rcases Nat.lt_or_ge j k with h | h
    · simp only [z', if_pos h.le, if_pos (show j + 1 ≤ k by omega)]
      exact hstep j (by omega)
    · have : j = k := by omega
      subst this
      simp only [z', if_pos le_rfl, if_neg (show ¬ j + 1 ≤ j by omega)]
      rw [hka]; exact hR'
  have hw1 := Bprime_walk_right hX F hτ ht z' (k + 1) hz'0 hstep'
  have haw : dist a' w = diam X := by
    have := hw1 k (by omega); simp only [z', if_pos le_rfl] at this; rwa [hka] at this
  have hbw : dist b' w = diam X := by
    have := hw1 (k + 1) le_rfl
    simp only [z', if_neg (show ¬ k + 1 ≤ k by omega)] at this; exact this
  have haw' : dist a' w' = diam X := ht'.1.2.2.2.2.2
  have hbw' : dist b' w' = diam X := ht'.2.1.2.2.2.2.2
  have hab' : dist a' b' = 1 := hR'.1.2.2.1
  have hwX : w ∈ X := F.partner_mem v ht.1.1
  have hw'X : w' ∈ X := F.partner_mem v' ht'.1.1
  have hT := two_of_pos hX.dist2_pos
  have hL := hX.large
  have hΔ : dist2 X ≤ diam X := dist2_le_diam X
  -- frame at `b′` with `e = a′ − b′`
  set e := a' - b'
  have he : ‖e‖ = 1 := by rw [← dist_eq_norm, hab']
  have hin : ∀ x, dist x a' = diam X → dist x b' = diam X → inner ℝ (x - b') e = 1 / 2 := by
    intro x hxa hxb
    have := two_inner_sub x b' a'
    rw [hxa, hxb, dist_comm a' b'] at this
    rw [dist_comm b' a', hab'] at this
    linarith
  have h1 := hin w (by rw [dist_comm, haw]) (by rw [dist_comm, hbw])
  have h2 := hin w' (by rw [dist_comm, haw']) (by rw [dist_comm, hbw'])
  have n1 := inner_sq_add_det_sq (e := w - b') he
  have n2 := inner_sq_add_det_sq (e := w' - b') he
  rw [h1, ← dist_eq_norm, dist_comm, hbw] at n1
  rw [h2, ← dist_eq_norm, dist_comm, hbw'] at n2
  have d1 := decompR he (w - b')
  have d2 := decompR he (w' - b')
  rw [h1] at d1; rw [h2] at d2
  have hL2 := inner_mul_add_det_mul e (w - b') (w' - b')
  rw [real_inner_comm (w - b') e, real_inner_comm (w' - b') e, h1, h2, he] at hL2
  set β₁ := det2 e (w - b')
  set β₂ := det2 e (w' - b')
  by_cases hβ : β₁ = β₂
  · have : w - b' = w' - b' := by rw [d1, d2, hβ]
    exact sub_left_injective this
  · exfalso
    have hβ' : β₂ = -β₁ := by
      have : (β₂ - β₁) * (β₂ + β₁) = 0 := by linear_combination n2 - n1
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (sub_eq_zero.1 h).symm hβ
      · linarith
    rw [hβ'] at hL2
    have hlow := two_inner_sub w b' w'
    rw [dist_comm w b', hbw, dist_comm w' b', hbw'] at hlow
    have hww := hT.le_diam w hwX w' hw'X
    have : dist w w' ^ 2 ≤ diam X ^ 2 := pow_le_pow_left₀ dist_nonneg hww 2
    nlinarith

/-- A point equidistant from `a, b` (`|ab| = 1`) lies on the bisector:
`x − m = c·(b − a)^⊥` with `c² = |xa|² − 1/4`. -/
private theorem bisector {x a b : Pt} (hab : dist a b = 1) (h : dist x a = dist x b) :
    x - midpoint ℝ a b = det2 (b - a) (x - midpoint ℝ a b) • perp (b - a) ∧
      det2 (b - a) (x - midpoint ℝ a b) ^ 2 = dist x a ^ 2 - 1 / 4 := by
  have hm : midpoint ℝ a b = (1 / 2 : ℝ) • (a + b) := by rw [midpoint_eq_smul_add]; norm_num
  have hu := dist_sq_pt a b
  rw [hab] at hu
  have hsq : dist x a ^ 2 = dist x b ^ 2 := by rw [h]
  rw [dist_sq_pt, dist_sq_pt] at hsq
  have hxa := dist_sq_pt x a
  rw [hm]
  constructor
  · rw [pt_ext_iff]
    simp only [PiLp.sub_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, det2_pt,
      perp_apply0, perp_apply1]
    constructor
    · linear_combination ((b 0 - a 0) / 2) * hsq + (x 0 - (a 0 + b 0) / 2) * hu
    · linear_combination ((b 1 - a 1) / 2) * hsq + (x 1 - (a 1 + b 1) / 2) * hu
  · simp only [PiLp.sub_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, det2_pt]
    rw [hxa]
    linear_combination (-((x 0 - (a 0 + b 0) / 2) ^ 2 + (x 1 - (a 1 + b 1) / 2) ^ 2 - 1 / 4)) * hu
      - (((b 0 - a 0) * (x 0 - (a 0 + b 0) / 2) + (b 1 - a 1) * (x 1 - (a 1 + b 1) / 2) + 1) / 2) * hsq

/-- The apex of a triangle sits on `C(w, Δ₂)` on the bisector of its base:
`v = w + (Δ₂/|m − w|)(m − w)` with `m` the base midpoint.

TODO: none — proved (bisector coefficients `α, β` with `2αβ = Δ² − Δ₂² + 1/2 > 0`, `|β| > |α|`).
What's missing: (was) `|va| = |vb| = 1`, `|aw| = |bw| = Δ`: `v, w` both on the perpendicular
bisector of `ab`; `|vw| = Δ₂ < |mw|` and `v` on the segment side (`exact_identity_c`).
Acceptance: no `sorry`.
Depends on: `rung_offset`, `IsRung`. Difficulty M. -/
theorem apex_eq (hX : Normal X) (F : DirField X) (hτ : tau X = √3 / 2) {v a b : Pt}
    (ht : IsTri F v a b) :
    v = F.partner v + (dist2 X / ‖midpoint ℝ a b - F.partner v‖) •
      (midpoint ℝ a b - F.partner v) := by
  obtain ⟨hva, hvb, -, -, hR, -⟩ := ht
  set w := F.partner v
  have hvw : dist v w = dist2 X := F.partner_K v hva.1 hva.2.1
  have haw : dist a w = diam X := hva.2.2.2.2.2
  have hbw : dist b w = diam X := hvb.2.2.2.2.2
  have hab : dist a b = 1 := hR.1.2.2.1
  obtain ⟨ev, cv⟩ := bisector hab (x := v)
    (by rw [hva.2.2.2.2.1, hvb.2.2.2.2.1])
  obtain ⟨ew, cw⟩ := bisector hab (x := w) (by rw [dist_comm w a, dist_comm w b, haw, hbw])
  set m := midpoint ℝ a b
  set n := perp (b - a)
  set α := det2 (b - a) (v - m)
  set β := det2 (b - a) (w - m)
  have hn : ‖n‖ = 1 := by rw [norm_perp, ← dist_eq_norm, dist_comm, hab]
  rw [hva.2.2.2.2.1] at cv
  rw [dist_comm w a, haw] at cw
  have hvw' : v - w = (α - β) • n := by
    rw [sub_smul, ← ev, ← ew]; abel
  have hαβ : (α - β) ^ 2 = dist2 X ^ 2 := by
    rw [← hvw, dist_eq_norm, hvw', norm_smul, hn, mul_one, Real.norm_eq_abs, sq_abs]
  have hΔ := dist2_le_diam X
  have hΔ₂ := hX.large
  have hR0 := hX.dist2_pos
  have hmw : m - w = (-β) • n := by rw [neg_smul, ← ew]; abel
  rw [hmw, norm_smul, hn, mul_one, Real.norm_eq_abs, abs_neg]
  have e : v = w + (α - β) • n := by rw [← hvw']; abel
  have h2 : 2 * α * β = diam X ^ 2 - dist2 X ^ 2 + 1 / 2 := by nlinarith
  have hβα : α ^ 2 < β ^ 2 := by nlinarith
  have hβ0 : β ≠ 0 := by intro h0; rw [h0] at hβα; nlinarith
  rcases lt_or_gt_of_ne hβ0 with hβ | hβ
  · have hα : α < 0 := by nlinarith
    have hlt : β < α := by nlinarith
    have : α - β = dist2 X :=
      (pow_left_inj₀ (by linarith) hR0.le two_ne_zero).1 hαβ
    rw [abs_of_neg hβ, e, this, smul_smul, div_mul_cancel₀ _ (by linarith)]
  · have hα : 0 < α := by nlinarith
    have hlt : α < β := by nlinarith
    have : β - α = dist2 X :=
      (pow_left_inj₀ (by linarith) hR0.le two_ne_zero).1 (by rw [← hαβ]; ring)
    rw [abs_of_pos hβ, e, smul_smul, show α - β = -dist2 X by linarith]
    congr 2
    field_simp

/-! ## (Arc), (Rigid) -/

/-- Interpolation for sinusoids: `g ≥ m ≥ 0` at the ends of an interval of length `< π` gives
`g ≥ m` on it (`g(θ) sin(θ₂ − θ₁) = g(θ₁) sin(θ₂ − θ) + g(θ₂) sin(θ − θ₁)`). -/
private theorem sinusoid_interp {a b m θ₁ θ θ₂ : ℝ} (hm : 0 ≤ m) (h1 : θ₁ ≤ θ) (h2 : θ ≤ θ₂)
    (hπ : θ₂ - θ₁ < π) (g1 : m ≤ a * Real.cos θ₁ + b * Real.sin θ₁)
    (g2 : m ≤ a * Real.cos θ₂ + b * Real.sin θ₂) : m ≤ a * Real.cos θ + b * Real.sin θ := by
  rcases h1.eq_or_lt with rfl | h1'
  · exact g1
  have hsΔ : 0 < Real.sin (θ₂ - θ₁) := Real.sin_pos_of_pos_of_lt_pi (by linarith) hπ
  have hsα : 0 ≤ Real.sin (θ₂ - θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hsβ : 0 ≤ Real.sin (θ - θ₁) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hid : (a * Real.cos θ + b * Real.sin θ) * Real.sin (θ₂ - θ₁) =
      (a * Real.cos θ₁ + b * Real.sin θ₁) * Real.sin (θ₂ - θ) +
        (a * Real.cos θ₂ + b * Real.sin θ₂) * Real.sin (θ - θ₁) := by
    rw [Real.sin_sub, Real.sin_sub, Real.sin_sub]; ring
  have hsum : Real.sin (θ₂ - θ₁) ≤ Real.sin (θ₂ - θ) + Real.sin (θ - θ₁) := by
    have e : θ₂ - θ₁ = (θ₂ - θ) + (θ - θ₁) := by ring
    rw [e, Real.sin_add]
    have := Real.cos_le_one (θ - θ₁)
    have := Real.cos_le_one (θ₂ - θ)
    nlinarith
  have : m * Real.sin (θ₂ - θ₁) ≤ (a * Real.cos θ + b * Real.sin θ) * Real.sin (θ₂ - θ₁) := by
    rw [hid]
    nlinarith [mul_le_mul_of_nonneg_right g1 hsα, mul_le_mul_of_nonneg_right g2 hsβ,
      mul_le_mul_of_nonneg_left hsum hm]
  exact le_of_mul_le_mul_right this hsΔ

/-- `|w + R·dirVec φ − x|² = |x − w|² − 2R((x−w)·dirVec φ) + R²`, in coordinates. -/
private theorem dist_arc_sq (w x : Pt) (R φ : ℝ) :
    dist (w + R • dirVec φ) x ^ 2 = ((x 0 - w 0) ^ 2 + (x 1 - w 1) ^ 2) -
      2 * R * ((x 0 - w 0) * Real.cos φ + (x 1 - w 1) * Real.sin φ) + R ^ 2 := by
  rw [dist_sq_pt]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, dirVec_apply0, dirVec_apply1]
  have := Real.sin_sq_add_cos_sq φ
  linear_combination R ^ 2 * this

/-- `C(w, R)` membership in `K` along an arc, pointwise criterion. -/
private theorem arc_mem_iff {w x : Pt} {R φ : ℝ} (hR : 0 < R) :
    dist (w + R • dirVec φ) x ≤ R ↔
      ((x 0 - w 0) ^ 2 + (x 1 - w 1) ^ 2) / (2 * R) ≤
        (x 0 - w 0) * Real.cos φ + (x 1 - w 1) * Real.sin φ := by
  rw [div_le_iff₀ (by positivity), ← sq_le_sq₀ dist_nonneg hR.le, dist_arc_sq]
  constructor <;> intro h <;> nlinarith

/-- **(Arc)** spindle convexity: if two points of `C(w, Δ₂)` (`w ∈ X`) at angles `θ₁ ≤ θ₂`,
`θ₂ − θ₁ < π`, lie in `K`, the whole short arc between them lies in `K`, hence in `∂K`.

TODO: none — proved (sinusoid interpolation `sinusoid_interp`; frontier via the outward normal
`dirVec θ`).
What's missing: (was) for `x ∈ X`, `D(x,Δ₂) ∩ C(w,Δ₂) = {θ : cos(θ − θ_x) ≥ |wx|/(2Δ₂)}` is an arc
of width `≤ π` (or everything if `x = w`) containing `θ₁, θ₂`, so containing `[θ₁, θ₂]`; frontier
since `w ∈ X` and the point is on `C(w,Δ₂)`.
Acceptance: no `sorry`.
Depends on: `mem_KBall`, `dirVec`, `Real.cos` monotonicity. Difficulty M. -/
theorem arc_sub_K (hX : Normal X) {w : Pt} (hw : w ∈ X) {θ₁ θ₂ : ℝ} (hθ : θ₁ ≤ θ₂)
    (hθπ : θ₂ - θ₁ < π) (h₁ : w + dist2 X • dirVec θ₁ ∈ KBall X)
    (h₂ : w + dist2 X • dirVec θ₂ ∈ KBall X) :
    ∀ θ ∈ Set.Icc θ₁ θ₂, w + dist2 X • dirVec θ ∈ KBall X ∩ frontier (KBall X) := by
  intro θ hθ
  have hR := hX.dist2_pos
  have hK : w + dist2 X • dirVec θ ∈ KBall X := by
    rw [mem_KBall]
    intro x hx
    rw [arc_mem_iff hR]
    have g1 := (arc_mem_iff (x := x) (φ := θ₁) hR).1 ((mem_KBall.1 h₁) x hx)
    have g2 := (arc_mem_iff (x := x) (φ := θ₂) hR).1 ((mem_KBall.1 h₂) x hx)
    exact sinusoid_interp (by positivity) hθ.1 hθ.2 hθπ g1 g2
  refine ⟨hK, mem_frontier_of_normal hK (n := dirVec θ) ?_ ?_⟩
  · intro h0; have := norm_dirVec θ; rw [h0, norm_zero] at this; norm_num at this
  · have hd : dist (w + dist2 X • dirVec θ) w = dist2 X := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, norm_dirVec, mul_one, Real.norm_eq_abs,
        abs_of_pos hR]
    have := neg_mem_normalCone hK hw hd (dist2 X)⁻¹ (inv_nonneg.2 hR.le)
    have e : -((dist2 X)⁻¹ • (w - (w + dist2 X • dirVec θ))) = dirVec θ := by
      rw [sub_add_cancel_left, smul_neg, neg_neg, smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
    rwa [e] at this

/-- If `a(cos h − 1) + b sin h ≤ 0` for all `|h| ≤ δ`, then `a ≥ 0` and `b = 0`. -/
private theorem normal_core {a b δ : ℝ} (hδ : 0 < δ)
    (h : ∀ x ∈ Set.Icc (-δ) δ, a * (Real.cos x - 1) + b * Real.sin x ≤ 0) : 0 ≤ a ∧ b = 0 := by
  have hπ := Real.pi_gt_three
  -- two-sided bound `|b| sin x ≤ a (1 − cos x)` for `0 < x ≤ min δ 1`
  have two : ∀ x, 0 < x → x ≤ δ → x ≤ 1 → |b| * Real.sin x ≤ a * (1 - Real.cos x) := by
    intro x hx hxδ _
    have h1 := h x ⟨by linarith, hxδ⟩
    have h2 := h (-x) ⟨by linarith, by linarith⟩
    rw [Real.cos_neg, Real.sin_neg] at h2
    rcases abs_cases b with ⟨hb, -⟩ | ⟨hb, -⟩ <;> rw [hb] <;> nlinarith
  set x₀ := min δ 1
  have hx₀ : 0 < x₀ := lt_min hδ one_pos
  have hx₀δ : x₀ ≤ δ := min_le_left _ _
  have hx₀1 : x₀ ≤ 1 := min_le_right _ _
  have hcos : Real.cos x₀ < 1 := by
    rw [← Real.cos_zero]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi_div_two le_rfl (by linarith) hx₀
  have hsin0 : 0 ≤ Real.sin x₀ := Real.sin_nonneg_of_nonneg_of_le_pi hx₀.le (by linarith)
  have ha : 0 ≤ a := by
    have := two x₀ hx₀ hx₀δ hx₀1
    have : 0 ≤ a * (1 - Real.cos x₀) := le_trans (by positivity) this
    by_contra ha; push Not at ha
    have : a * (1 - Real.cos x₀) < 0 := mul_neg_of_neg_of_pos ha (by linarith)
    linarith
  refine ⟨ha, ?_⟩
  by_contra hb
  have hbpos : 0 < |b| := abs_pos.2 hb
  set x := min x₀ (|b| / (2 * (a + 1)))
  have hx : 0 < x := lt_min hx₀ (by positivity)
  have hxx₀ : x ≤ x₀ := min_le_left _ _
  have hxb : x ≤ |b| / (2 * (a + 1)) := min_le_right _ _
  have h2 := two x hx (hxx₀.trans hx₀δ) (hxx₀.trans hx₀1)
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hs := Real.sin_gt_sub_cube (x := x) hx
  have hx1 : x ≤ 1 := hxx₀.trans hx₀1
  have hx3 : x ^ 3 ≤ x := by nlinarith
  -- `|b| x/2 ≤ |b| sin x ≤ a x²/2`, so `|b| ≤ a x`
  have e1 : |b| * (x / 2) ≤ a * (x ^ 2 / 2) := by
    have : x / 2 ≤ Real.sin x := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this hbpos.le, mul_le_mul_of_nonneg_left
      (show 1 - Real.cos x ≤ x ^ 2 / 2 by linarith) ha]
  have e2 : |b| ≤ a * x := by nlinarith
  have e3 : a * x ≤ a * (|b| / (2 * (a + 1))) := mul_le_mul_of_nonneg_left hxb ha
  have e4 : a * (|b| / (2 * (a + 1))) < |b| := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  linarith

/-- **(Rigid), normal fact**: at a relative-interior point of an arc of `C(w, Δ₂)` contained in
`K`, the outer normal cone is the single ray through `dirVec θ`.

TODO: none — proved (`normal_core`: `a(cos h − 1) + b sin h ≤ 0` for `|h| ≤ δ` forces `b = 0`).
What's missing: (was) `ν` normal ⇒ `(y − p)·ν ≤ 0` for `y` on the arc on both sides of `p`; divide by
the arc parameter and let it tend to `0` (or use the two chords): `ν ⊥ tangent`, and
`(w − p)·ν ≤ 0` fixes the sign.
Acceptance: no `sorry`.
Depends on: `normalCone`, `dirVec`. Difficulty M. -/
theorem normal_fact (hX : Normal X) {w : Pt} {θ₁ θ θ₂ : ℝ} (h₁ : θ₁ < θ) (h₂ : θ < θ₂)
    (harc : ∀ φ ∈ Set.Icc θ₁ θ₂, w + dist2 X • dirVec φ ∈ KBall X) {ν : Pt}
    (hν : ν ∈ normalCone (KBall X) (w + dist2 X • dirVec θ)) :
    ∃ c : ℝ, 0 ≤ c ∧ ν = c • dirVec θ := by
  have hR := hX.dist2_pos
  set R := dist2 X
  set d := dirVec θ
  have hd : ‖d‖ = 1 := norm_dirVec θ
  set a := inner ℝ ν d
  set b := det2 d ν
  have hdec : ν = a • d + b • perp d := decompR hd ν
  set δ := min (θ - θ₁) (θ₂ - θ)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have key : ∀ x ∈ Set.Icc (-δ) δ, a * (Real.cos x - 1) + b * Real.sin x ≤ 0 := by
    intro x hx
    have hφ : θ + x ∈ Set.Icc θ₁ θ₂ :=
      ⟨by linarith [min_le_left (θ - θ₁) (θ₂ - θ), hx.1],
        by linarith [min_le_right (θ - θ₁) (θ₂ - θ), hx.2]⟩
    have h := hν _ (harc _ hφ)
    have e0 : w + R • dirVec (θ + x) - (w + R • d) = R • (dirVec (θ + x) - d) := by
      rw [smul_sub]; abel
    rw [e0, real_inner_smul_left, dirVec_addR] at h
    have e : inner ℝ (Real.cos x • d + Real.sin x • perp d - d) ν =
        a * (Real.cos x - 1) + b * Real.sin x := by
      rw [inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_comm ν d, ← det2_eq_inner_perpR]
      ring
    rw [e] at h
    by_contra hc; push Not at hc
    have := mul_pos hR hc
    linarith
  obtain ⟨ha, hb⟩ := normal_core hδ key
  exact ⟨a, ha, by rw [hdec, hb, zero_smul, add_zero]⟩

/-- Inner product in the frame `(d, d^⊥)` of a unit `d`. -/
private theorem frame_inner {d : Pt} (hd : ‖d‖ = 1) (x y x' y' : ℝ) :
    inner ℝ (x • d + y • perp d) (x' • d + y' • perp d) = x * x' + y * y' := by
  have h := unit_sq hd
  rw [inner_pt]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, perp_apply0, perp_apply1]
  linear_combination (x * x' + y * y') * h

private theorem frame_norm_sq {d : Pt} (hd : ‖d‖ = 1) (x y : ℝ) :
    ‖x • d + y • perp d‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, frame_inner hd]; ring

/-- The arithmetic core of `rigid_step`. -/
private theorem rigid_arith {A B N1 N2 X1 Y1 R : ℝ} (hR : 0 < R) (hAB : A ^ 2 + B ^ 2 = 1)
    (hB : 0 < B) (h1 : 1 + 2 * A * R ≤ 0) (hN1 : N1 < 0) (hX1 : 2 * R * X1 = -1) (hY : 0 ≤ Y1)
    (hXY : X1 ^ 2 + Y1 ^ 2 = 1) (hP : 0 ≤ -A * N1 + -B * N2)
    (hV : 0 ≤ (X1 - A) * N1 + (Y1 - B) * N2) : A = X1 ∧ B = Y1 := by
  have hR2 : 0 < 2 * R := by linarith
  have hAle : A ≤ X1 := by
    by_contra h; push Not at h
    have := mul_lt_mul_of_pos_left h hR2
    linarith
  have hX1n : X1 < 0 := by
    by_contra h; push Not at h
    have := mul_nonneg hR2.le h
    linarith
  have hAeq : A = X1 := by
    by_contra hne
    have hlt : A < X1 := lt_of_le_of_ne hAle hne
    have hA : A < 0 := by linarith
    have hAN : 0 < A * N1 := mul_pos_of_neg_of_neg hA hN1
    have hN2 : N2 < 0 := by
      by_contra h; push Not at h
      have := mul_nonneg hB.le h
      linarith
    have hpos : 0 < (A - X1) * N1 := mul_pos_of_neg_of_neg (by linarith) hN1
    have hYB : Y1 < B := by
      by_contra h; push Not at h
      have := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ Y1 - B by linarith) hN2.le
      linarith
    have e1 : Y1 ^ 2 < B ^ 2 := pow_lt_pow_left₀ hYB hY two_ne_zero
    have e2 : X1 ^ 2 < A ^ 2 := by nlinarith
    linarith
  refine ⟨hAeq, ?_⟩
  subst hAeq
  have h : (B - Y1) * (B + Y1) = 0 := by linear_combination hAB - hXY
  rcases mul_eq_zero.1 h with h | h
  · linarith
  · linarith

/-- **(Rigid), step**: on an arc `[θ, θ₂]` of `C(w, Δ₂)` inside `K`, with `u = −dirVec θ` at the
current K-row point and room for one step (`θ + α₂ ≤ θ₂`), the pure right K T-neighbour is the
next arc point `w + Δ₂ dirVec(θ + α₂)`.

TODO: none — proved (frame `(d, d^⊥)`, `d = dirVec θ`; testing the inward
normal `u_q` at `y = p` and `y = v*` pins `q − p = v* − p`, `rigid_arith`).
What's missing: (was) coordinates `(r, u)`; `v_{i+1} − v_i = (cos ψ, sin ψ)` with `ψ < arcsin β`;
`v_{i+1} ∈ D(w,Δ₂)` forces `ψ ≥ ψ* = arcsin(1/(2Δ₂))`; if `ψ > ψ*`, the normal `n = u_{v_{i+1}}`
(`|φ| ≤ β`) violates `v_i ∈ K` or `v* ∈ K` (both terms negative).  Float check B2.
Acceptance: no `sorry`.
Depends on: `arc_sub_K`, `neg_mem_normalCone`, `IsSideT`. Difficulty L. -/
theorem rigid_step (hX : Normal X) (F : DirField X) (hτ : tau X = √3 / 2) {w : Pt} (hw : w ∈ X)
    {θ θ₂ : ℝ} (harc : ∀ φ ∈ Set.Icc θ θ₂, w + dist2 X • dirVec φ ∈ KBall X)
    (hroom : θ + alpha2 X ≤ θ₂) (hv : w + dist2 X • dirVec θ ∈ Sset X)
    (hvD : w + dist2 X • dirVec θ ∉ Dset X) (hu : F.u (w + dist2 X • dirVec θ) = -dirVec θ)
    {q : Pt} (hq : RowR F (w + dist2 X • dirVec θ) q) :
    q = w + dist2 X • dirVec (θ + alpha2 X) := by
  have hR := hX.dist2_pos
  have hRbig := hX.large
  set R := dist2 X with hRdef
  set α := alpha2 X with hαdef
  set d := dirVec θ with hddef
  set p := w + R • d with hpdef
  have hd : ‖d‖ = 1 := norm_dirVec θ
  obtain ⟨hpS, hqS, -, hang, -, -⟩ := hq.1
  have hqD : q ∉ Dset X := fun h => hvD (hq.2.2 h)
  obtain ⟨hn, -, -, hdet⟩ := hq.1.step
  rw [hu] at hdet
  set e := q - p with hedef
  set A := inner ℝ e d
  set B := det2 d e
  have hdec : e = A • d + B • perp d := decompR hd e
  have hAB : A ^ 2 + B ^ 2 = 1 := by rw [inner_sq_add_det_sq hd, hn, one_pow]
  have hB : 0 < B := by
    have : det2 (-d) e = -B := by simp only [B, det2_pt, PiLp.neg_apply]; ring
    linarith
  -- `q ∈ K ⊆ D(w, Δ₂)`
  have hqK : q ∈ KBall X := ball_polygon_a (Sset_sub hqS) hqD
  have hqw : dist q w ≤ R := mem_KBall.1 hqK w hw
  have hqw' : q - w = (A + R) • d + B • perp d := by
    rw [show q - w = e + R • d by simp only [e, p]; abel, hdec, add_smul]; abel
  have h1 : 1 + 2 * A * R ≤ 0 := by
    have h := frame_norm_sq hd (A + R) B
    rw [← hqw', ← dist_eq_norm] at h
    have h2 : dist q w ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ dist_nonneg hqw 2
    nlinarith
  -- inward normal at `q`
  have hnq : ‖F.u q‖ = 1 := F.norm_u hqS
  have hnc : ∀ y ∈ KBall X, 0 ≤ inner ℝ (y - q) (F.u q) := by
    intro y hy
    have := neg_mem_normalCone hqK (F.partner_mem q hqS) (F.partner_K q hqS hqD)
      (dist q (F.partner q))⁻¹ (inv_nonneg.2 dist_nonneg) y hy
    rw [inner_neg_right] at this
    unfold DirField.u
    linarith
  set N1 := inner ℝ (F.u q) d
  set N2 := det2 d (F.u q)
  have hndec : F.u q = N1 • d + N2 • perp d := decompR hd _
  have hN1 : N1 < 0 := by
    have hc := cos_le_inner_of_ang_le (F.norm_u hpS) hnq
      (by unfold beta; linarith [Real.pi_gt_three]) hang
    rw [hu, inner_neg_left, real_inner_comm] at hc
    have : 0 < Real.cos beta :=
      Real.cos_pos_of_mem_Ioo ⟨by unfold beta; linarith [Real.pi_gt_three],
        by unfold beta; linarith [Real.pi_gt_three]⟩
    linarith
  -- `α₂` facts
  set s := 1 / (2 * R) with hsdef
  have hs0 : 0 < s := by positivity
  have hs1 : s ≤ 1 := by
    rw [hsdef, div_le_one (by positivity)]; linarith
  have hsin : Real.sin (Real.arcsin s) = s := Real.sin_arcsin (by linarith) hs1
  set C := Real.cos (Real.arcsin s)
  have hC0 : 0 ≤ C := Real.cos_arcsin_nonneg _
  have hC2 : s ^ 2 + C ^ 2 = 1 := by rw [← hsin]; exact Real.sin_sq_add_cos_sq _
  have hα0 : 0 ≤ α := by
    rw [hαdef, alpha2]; have := Real.arcsin_nonneg.2 hs0.le; linarith
  have hRs : 2 * R * s = 1 := by rw [hsdef]; field_simp
  set X1 := R * (Real.cos α - 1)
  set Y1 := R * Real.sin α
  have hX1 : 2 * R * X1 = -1 := by
    have : Real.cos α = 2 * C ^ 2 - 1 := by rw [hαdef, alpha2, Real.cos_two_mul]
    simp only [X1]; rw [this]; linear_combination 4 * R ^ 2 * hC2 - (2 * R * s + 1) * hRs
  have hY1 : Y1 = C := by
    have : Real.sin α = 2 * s * C := by rw [hαdef, alpha2, Real.sin_two_mul, hsin]
    simp only [Y1]; rw [this]; linear_combination C * hRs
  have hXY : X1 ^ 2 + Y1 ^ 2 = 1 := by
    have : X1 = -s := by
      have h' : (2 * R) * (X1 + s) = 0 := by linarith
      rcases mul_eq_zero.1 h' with h | h
      · linarith
      · linarith
    rw [this, hY1]; nlinarith
  -- the candidate point
  set vs := w + R • dirVec (θ + α) with hvsdef
  have hvsp : vs - p = X1 • d + Y1 • perp d := by
    simp only [vs, p, X1, Y1]
    rw [dirVec_addR, pt_ext_iff]
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    constructor <;> ring
  -- test `y = p`
  have hP := hnc p (harc θ ⟨le_rfl, by linarith⟩)
  rw [show p - q = (-A) • d + (-B) • perp d by rw [← neg_sub, hedef.symm, hdec]; simp; abel,
    hndec, frame_inner hd] at hP
  -- test `y = v*`
  have hV := hnc vs (harc (θ + α) ⟨by linarith, hroom⟩)
  rw [show vs - q = (X1 - A) • d + (Y1 - B) • perp d by
      rw [show vs - q = (vs - p) - e by simp only [e]; abel, hvsp, hdec, sub_smul, sub_smul]; abel,
    hndec, frame_inner hd] at hV
  -- conclude `A = X1`, `B = Y1`
  obtain ⟨hAeq, hBeq⟩ := rigid_arith hR hAB hB h1 hN1 hX1 (hY1 ▸ hC0) hXY
    (by linarith [hP]) (by linarith [hV])
  have : q = p + (vs - p) := by
    rw [hvsp, ← hAeq, ← hBeq, ← hdec, hedef]; abel
  rw [this, add_sub_cancel]

/-- **(Count), different centres**: a point in the relative interior of an arc of `C(w, Δ₂)`
inside `K` cannot be an endpoint of a nondegenerate arc of `C(w′, Δ₂)` inside `K` unless
`w = w′` (near such a point `∂K` is the arc of `C(w,Δ₂)`, and two circles share `≤ 2` points).

TODO: none — proved (`p − w′` is an outward normal at `p`, so by
`normal_fact` it is `c·dirVec θ`, and `c = Δ₂` by norms; `hw`, `hφ`, `harc'` are unused).
What's missing: (was) points of the `w′`-arc near `p` are in `∂K` (`w′ ∈ X`); near `p` every boundary
point of `K` lies on `C(w, Δ₂)` (inside `D(w,Δ₂)` near `p` is interior to the circular segment
`conv(arc) ⊆ K`); infinitely many common points of two circles force `w = w′`.
Acceptance: no `sorry`.
Depends on: `arc_sub_K`, `KBall_convex`. Difficulty M–L. -/
theorem arc_centre_unique (hX : Normal X) {w w' : Pt} (hw : w ∈ X) (hw' : w' ∈ X)
    {θ₁ θ θ₂ φ₁ φ₂ : ℝ} (h₁ : θ₁ < θ) (h₂ : θ < θ₂)
    (harc : ∀ ψ ∈ Set.Icc θ₁ θ₂, w + dist2 X • dirVec ψ ∈ KBall X) (hφ : φ₁ < φ₂)
    (harc' : ∀ ψ ∈ Set.Icc φ₁ φ₂, w' + dist2 X • dirVec ψ ∈ KBall X)
    (hp : w + dist2 X • dirVec θ = w' + dist2 X • dirVec φ₁ ∨
      w + dist2 X • dirVec θ = w' + dist2 X • dirVec φ₂) : w = w' := by
  have hR := hX.dist2_pos
  set R := dist2 X
  set d := dirVec θ
  set p := w + R • d with hpdef
  have hK : p ∈ KBall X := harc θ ⟨h₁.le, h₂.le⟩
  have hd : dist p w' = R := by
    rcases hp with h | h <;>
    · rw [h, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_dirVec, mul_one, Real.norm_eq_abs,
        abs_of_pos hR]
  have hn := neg_mem_normalCone hK hw' hd 1 zero_le_one
  obtain ⟨c, hc, e⟩ := normal_fact hX h₁ h₂ harc hn
  have hc' : c = R := by
    have := congrArg norm e
    rw [norm_neg, one_smul, norm_smul, norm_dirVec, mul_one, Real.norm_eq_abs, abs_of_nonneg hc,
      ← dist_eq_norm, dist_comm, hd] at this
    exact this.symm
  have e2 : w' = p - c • d := by rw [← e]; simp
  rw [e2, hc', hpdef, add_sub_cancel_right]

/-! ## (Count) -/

/-- Triangles over **bad** bases number at most `cBad` (base determines apex).

TODO: none — proved.
What's missing: (was) the map `v ↦ base` into `bad X F` is injective by `base_apex_unique`.
Acceptance: no `sorry`.
Depends on: `tri_of_twoRung`, `base_apex_unique`, `card_bad_le`. Difficulty M. -/
theorem card_badBase_le (hX : Normal X) (F : DirField X) (hτ : tau X = √3 / 2) :
    (((twoRungVerts X F).filter (fun v => ¬ ∃ a b, IsTri F v a b)).card : ℝ) ≤ cBad := by
  classical
  set V := (twoRungVerts X F).filter (fun v => ¬ ∃ a b, IsTri F v a b)
  let Q : Pt → Pt × Pt → Prop := fun v ab => IsRung F v ab.1 ∧ IsRung F v ab.2 ∧
    s(v, ab.1) ∈ rungs X F ∧ s(v, ab.2) ∈ rungs X F ∧ ab.1 ≠ ab.2 ∧ s(ab.1, ab.2) ∈ bad X F
  have hQ : ∀ v ∈ V, ∃ ab, Q v ab := by
    intro v hv
    obtain ⟨hv2, hnt⟩ := mem_filter.1 hv
    obtain ⟨a, b, h1, h2, g1, g2, hab, -, hbt⟩ := tri_of_twoRung hX F hτ hv2
    rcases hbt with hb | ht
    · exact ⟨(a, b), h1, h2, g1, g2, hab, hb⟩
    · exact absurd ⟨a, b, ht⟩ hnt
  let f : Pt → Sym2 Pt := fun v => if h : ∃ ab, Q v ab then s(h.choose.1, h.choose.2) else s(0, 0)
  have hf : ∀ v ∈ V, ∃ ab, Q v ab ∧ f v = s(ab.1, ab.2) := by
    intro v hv
    have h := hQ v hv
    exact ⟨h.choose, h.choose_spec, dif_pos h⟩
  have hmaps : ∀ v ∈ V, f v ∈ bad X F := by
    intro v hv
    obtain ⟨ab, hq, he⟩ := hf v hv
    rw [he]; exact hq.2.2.2.2.2
  have hinj : Set.InjOn f ↑V := by
    intro v hv v' hv' e
    obtain ⟨⟨a, b⟩, ⟨h1, h2, g1, g2, hab, -⟩, he⟩ := hf v hv
    obtain ⟨⟨a', b'⟩, ⟨h1', h2', g1', g2', -, -⟩, he'⟩ := hf v' hv'
    rw [he, he'] at e
    rcases Sym2.eq_iff.1 e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact base_apex_unique hX F hτ hab h1 h2 h1' h2' g1 g2 g1' g2'
    · exact base_apex_unique hX F hτ hab h1 h2 h2' h1' g1 g2 g2' g1'
  have h1 := card_le_card_of_injOn f hmaps hinj
  have h2 := card_bad_le hX F
  have : (V.card : ℝ) ≤ (bad X F).card := by exact_mod_cast h1
  linarith

/-! ### Walks, angles and the charging of triangles (skeleton for `exact_breaks`) -/

/-- The pure right successor of `p` (or `p` itself if there is none). -/
private noncomputable def nxt (F : DirField X) (p : Pt) : Pt :=
  if h : ∃ q, RowR F p q then h.choose else p

/-- The pure right walk from `p`. -/
private noncomputable def walk (F : DirField X) (p : Pt) (k : ℕ) : Pt := (nxt F)^[k] p

/-- The walk from `p` makes (at least) `N` genuine right steps. -/
private def Runs (F : DirField X) (p : Pt) (N : ℕ) : Prop :=
  ∀ k < N, RowR F (walk F p k) (walk F p (k + 1))

/-- `p` is the left base end of some triangle. -/
private def TriAt (F : DirField X) (p : Pt) : Prop := ∃ v' a' b', IsTri F v' a' b' ∧ a' = p

/-- TODO: none — proved.
What's missing: `rowR_fun` and `Classical.choose_spec`.
Acceptance: no `sorry`. Depends on: `rowR_fun`. Difficulty S. -/
private theorem nxt_eq (hX : Normal X) {F : DirField X} {p q : Pt} (h : RowR F p q) :
    nxt F p = q := by
  have hc : ∃ q, RowR F p q := ⟨q, h⟩
  unfold nxt
  rw [dif_pos hc]
  exact rowR_fun hX hc.choose_spec h

private theorem walk_zero (F : DirField X) (p : Pt) : walk F p 0 = p := rfl

private theorem walk_succ (F : DirField X) (p : Pt) (k : ℕ) :
    walk F p (k + 1) = nxt F (walk F p k) := Function.iterate_succ_apply' _ _ _

/-- TODO: none — proved. What's missing: restriction. Acceptance: no `sorry`. Difficulty S. -/
private theorem runs_mono {F : DirField X} {p : Pt} {N M : ℕ} (h : Runs F p N) (hM : M ≤ N) :
    Runs F p M := by
  exact fun k hk => h k (lt_of_lt_of_le hk hM)

/-- TODO: none — proved. What's missing: `nxt_eq`, `walk_succ`. Acceptance: no `sorry`. Difficulty S. -/
private theorem runs_succ (hX : Normal X) {F : DirField X} {p q : Pt} {N : ℕ} (h : Runs F p N)
    (hq : RowR F (walk F p N) q) : Runs F p (N + 1) := by
  intro k hk
  rcases (Nat.lt_succ_iff.1 hk).lt_or_eq with h1 | rfl
  · exact h k h1
  · rw [walk_succ, nxt_eq hX hq]; exact hq

/-- TODO: none — proved. What's missing: induction; `RowR` targets lie in `S`. Difficulty S. -/
private theorem walk_mem_S {F : DirField X} {p : Pt} {N : ℕ} (h : Runs F p N) (hp : p ∈ Sset X) :
    ∀ k ≤ N, walk F p k ∈ Sset X := by
  intro k hk
  cases k with
  | zero => exact hp
  | succ k => exact (h k (by omega)).1.2.1

/-- TODO: none — proved. What's missing: induction; `RowR` preserves `D`-membership. Difficulty S. -/
private theorem walk_D_iff {F : DirField X} {p : Pt} {N : ℕ} (h : Runs F p N) :
    ∀ k ≤ N, (walk F p k ∈ Dset X ↔ p ∈ Dset X) := by
  intro k hk
  induction k with
  | zero => exact Iff.rfl
  | succ k ih => exact (h k (by omega)).2.symm.trans (ih (by omega))

/-- Suffix property of walks (predecessors are unique, `rowR_inj`).
TODO: none — proved. What's missing: induction on `i'` generalising `i`. Difficulty S–M. -/
private theorem walk_suffix (hX : Normal X) {F : DirField X} {p p' : Pt} {i i' : ℕ}
    (h : Runs F p i) (h' : Runs F p' i') (he : walk F p i = walk F p' i') (hle : i' ≤ i) :
    walk F p (i - i') = p' := by
  induction i' generalizing i with
  | zero => rw [walk_zero] at he; simpa using he
  | succ i' ih =>
    have h1 := h' i' (by omega)
    have h2 := h (i - 1) (by omega)
    rw [show i - 1 + 1 = i by omega, he] at h2
    have e := rowR_inj hX h2 h1
    have := ih (i := i - 1) (runs_mono h (by omega)) (runs_mono h' (by omega)) e (by omega)
    rwa [show i - 1 - i' = i - (i' + 1) by omega] at this

/-- TODO: none — proved. What's missing: `pt_ext_iff`, `rot`, `cos_add`/`sin_add`. Difficulty S. -/
private theorem rot_dirVec (ψ φ c : ℝ) : rot ψ (c • dirVec φ) = c • dirVec (φ + ψ) := by
  rw [pt_ext_iff, rot_apply0, rot_apply1]
  simp only [PiLp.smul_apply, smul_eq_mul, dirVec_apply0, dirVec_apply1, Real.cos_add,
    Real.sin_add]
  constructor <;> ring

/-- TODO: none — proved. What's missing: sum-to-product in coordinates. Difficulty S. -/
private theorem dirVec_add_half (φ α : ℝ) :
    dirVec φ + dirVec (φ + α) = (2 * Real.cos (α / 2)) • dirVec (φ + α / 2) := by
  have gen : ∀ x y : ℝ, dirVec (x - y) + dirVec (x + y) = (2 * Real.cos y) • dirVec x := by
    intro x y
    rw [pt_ext_iff]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, dirVec_apply0, dirVec_apply1,
      Real.cos_sub, Real.cos_add, Real.sin_sub, Real.sin_add]
    constructor <;> ring
  have := gen (φ + α / 2) (α / 2)
  rwa [show φ + α / 2 - α / 2 = φ by ring, show φ + α / 2 + α / 2 = φ + α by ring] at this

/-- Two points of `C(w, R) ∩ X` at angular distance in `(0, 2 arcsin(1/(2R)))` would be `< 1`
apart and distinct.
TODO: none — proved. What's missing: chord `|dirVec x − dirVec y| = 2|sin((x−y)/2)|`. Difficulty M. -/
private theorem arc_sep (hX : Normal X) {w : Pt} {R x y : ℝ} (hR : 1 ≤ R)
    (hx : w + R • dirVec x ∈ X) (hy : w + R • dirVec y ∈ X) (h0 : 0 < x - y)
    (h1 : x - y < 2 * Real.arcsin (1 / (2 * R))) : False := by
  have hR0 : 0 < R := by linarith
  set d := (x - y) / 2
  have hd0 : 0 < d := by simp only [d]; linarith
  have hs0 : 0 < 1 / (2 * R) := by positivity
  have hs1 : 1 / (2 * R) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hA := Real.arcsin_le_pi_div_two (1 / (2 * R))
  have hπ := Real.pi_gt_three
  have hdA : d < Real.arcsin (1 / (2 * R)) := by simp only [d]; linarith
  have hsin_pos : 0 < Real.sin d := Real.sin_pos_of_pos_of_lt_pi hd0 (by linarith)
  have hsin_lt : Real.sin d < 1 / (2 * R) := by
    have := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) hA hdA
    rwa [Real.sin_arcsin (by linarith) (by linarith)] at this
  -- the chord
  have hch : ‖dirVec x - dirVec y‖ ^ 2 = 4 * Real.sin d ^ 2 := by
    rw [norm_sq_pt]
    simp only [PiLp.sub_apply, dirVec_apply0, dirVec_apply1]
    have e : x - y = 2 * d := by simp only [d]; ring
    have hc : Real.cos x * Real.cos y + Real.sin x * Real.sin y = Real.cos (x - y) := by
      rw [Real.cos_sub]
    have hc2 : Real.cos (x - y) = 1 - 2 * Real.sin d ^ 2 := by
      rw [e, Real.cos_two_mul', Real.cos_sq']; ring
    have := Real.sin_sq_add_cos_sq x
    have := Real.sin_sq_add_cos_sq y
    nlinarith
  have hn : ‖dirVec x - dirVec y‖ = 2 * Real.sin d := by
    rw [← Real.sqrt_sq (norm_nonneg _), hch, show 4 * Real.sin d ^ 2 = (2 * Real.sin d) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  have hdist : dist (w + R • dirVec x) (w + R • dirVec y) = R * (2 * Real.sin d) := by
    rw [dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos hR0, hn]
  have hlt : dist (w + R • dirVec x) (w + R • dirVec y) < 1 := by
    rw [hdist]
    have := mul_lt_mul_of_pos_left hsin_lt (show (0 : ℝ) < 2 * R by positivity)
    rw [show 2 * R * (1 / (2 * R)) = 1 by field_simp] at this
    linarith
  have heq := eq_of_dist_lt_one hX.minDist_eq hx hy hlt
  rw [heq, dist_self] at hdist
  have : 0 < R * (2 * Real.sin d) := by positivity
  linarith

/-- TODO: none — proved. What's missing: `arcsin` positivity. Difficulty S. -/
private theorem alpha_pos (hX : Normal X) : 0 < alpha1 X ∧ 0 < alpha2 X := by
  have hpos := hX.dist2_pos
  have hΔ : 0 < diam X := hpos.trans_le (dist2_le_diam X)
  constructor
  · unfold alpha1
    have := Real.arcsin_pos.2 (show 0 < 1 / (2 * diam X) by positivity)
    linarith
  · unfold alpha2
    have := Real.arcsin_pos.2 (show 0 < 1 / (2 * dist2 X) by positivity)
    linarith

/-- The apex angle: if `a − w = Δ dirVec φ` then `v = w + Δ₂ dirVec(φ + α₁/2)`.
TODO: none — proved. What's missing: `Bprime_rot` (with `N = 0`), `rot_dirVec`, `dirVec_add_half`,
`apex_eq`. Difficulty M. -/
private theorem apex_angle (hX : Normal X) (F : DirField X) (hτ : tau X = √3 / 2) {v a b : Pt}
    (ht : IsTri F v a b) {φ : ℝ} (hφ : a - F.partner v = diam X • dirVec φ) :
    v = F.partner v + dist2 X • dirVec (φ + alpha1 X / 2) := by
  obtain ⟨hbase, -⟩ := Bprime_rot hX F hτ ht (fun _ => b) 0 rfl
    (fun k hk => absurd hk (Nat.not_lt_zero k))
  set w := F.partner v
  set α := alpha1 X
  have hb : b - w = diam X • dirVec (φ + α) := by rw [hbase, hφ, rot_dirVec]
  have ha' : a = w + diam X • dirVec φ := by rw [← hφ]; abel
  have hb' : b = w + diam X • dirVec (φ + α) := by rw [← hb]; abel
  have hm : midpoint ℝ a b - w = (diam X / 2) • (dirVec φ + dirVec (φ + α)) := by
    rw [midpoint_eq_smul_add, invOf_eq_inv, ha', hb']; module
  rw [dirVec_add_half, smul_smul] at hm
  have hpos := hX.dist2_pos
  have hΔ : 0 < diam X := hpos.trans_le (dist2_le_diam X)
  have hc : 0 < Real.cos (α / 2) := by
    have e : α / 2 = Real.arcsin (1 / (2 * diam X)) := by simp only [α, alpha1]; ring
    rw [e, Real.cos_arcsin]
    have : 1 / (2 * diam X) < 1 := by
      rw [div_lt_one (by positivity)]; have := hX.large; linarith [dist2_le_diam X]
    apply Real.sqrt_pos.2
    have : (1 / (2 * diam X)) ^ 2 < 1 := by
      have h0 : 0 < 1 / (2 * diam X) := by positivity
      nlinarith
    linarith
  have hn : ‖midpoint ℝ a b - w‖ = diam X * Real.cos (α / 2) := by
    rw [hm, norm_smul, norm_dirVec, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]
    ring
  rw [apex_eq hX F hτ ht, hn, hm, smul_smul]
  congr 2
  field_simp

/-- D-walk positions: `walk b k − w = Δ dirVec(φ + (k+1)α₁)`.
TODO: none — proved. What's missing: `Bprime_rot` with `z = walk F b`, `rot_dirVec`. Difficulty S–M. -/
private theorem dwalk_angle (hX : Normal X) (F : DirField X) (hτ : tau X = √3 / 2) {v a b : Pt}
    (ht : IsTri F v a b) {φ : ℝ} (hφ : a - F.partner v = diam X • dirVec φ) {N : ℕ}
    (hN : Runs F b N) :
    ∀ k ≤ N, walk F b k - F.partner v = diam X • dirVec (φ + ((k : ℝ) + 1) * alpha1 X) := by
  obtain ⟨hbase, hsteps⟩ := Bprime_rot hX F hτ ht (walk F b) N rfl hN
  intro k hk
  induction k with
  | zero =>
    rw [walk_zero, hbase, hφ, rot_dirVec]; congr 2; push_cast; ring
  | succ k ih =>
    rw [hsteps k (by omega), ih (by omega), rot_dirVec]; congr 2; push_cast; ring

/-- D-walks terminate.
TODO: none — proved. What's missing: otherwise `Runs F b N` for all `N` (`runs_succ`), contradicting
`Bprime_span` and `α₁ > 0`. Difficulty M. -/
private theorem dwalk_stops (hX : Normal X) (F : DirField X) (hτ : tau X = √3 / 2) {v a b : Pt}
    (ht : IsTri F v a b) : ∃ N, Runs F b N ∧ ¬ ∃ q, RowR F (walk F b N) q := by
  by_contra h
  push Not at h
  have hall : ∀ N, Runs F b N := by
    intro N
    induction N with
    | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
    | succ N ih =>
      obtain ⟨q, hq⟩ := h N ih
      exact runs_succ hX ih hq
  have hα := (alpha_pos hX).1
  obtain ⟨N, hN⟩ := exists_nat_gt (π / 3 / alpha1 X)
  have := Bprime_span hX F hτ ht (walk F b) N rfl (hall N)
  rw [div_lt_iff₀ hα] at hN
  nlinarith

/-- A point in the relative interior of an arc of `C(w, Δ₂)` inside `K`, at distance `Δ₂` from
`w′ ∈ X`: `w = w′` (the proof of `arc_centre_unique`, without the unused hypotheses).
TODO: none — proved. What's missing: copy of the `arc_centre_unique` proof. Difficulty S. -/
private theorem centre_eq (hX : Normal X) {w w' : Pt} (hw' : w' ∈ X) {θ₁ θ θ₂ : ℝ}
    (h₁ : θ₁ < θ) (h₂ : θ < θ₂)
    (harc : ∀ ψ ∈ Set.Icc θ₁ θ₂, w + dist2 X • dirVec ψ ∈ KBall X)
    (hd : dist (w + dist2 X • dirVec θ) w' = dist2 X) : w = w' := by
  have hR := hX.dist2_pos
  set R := dist2 X
  set d := dirVec θ
  set p := w + R • d with hpdef
  have hK : p ∈ KBall X := harc θ ⟨h₁.le, h₂.le⟩
  have hn := neg_mem_normalCone hK hw' hd 1 zero_le_one
  obtain ⟨c, hc, e⟩ := normal_fact hX h₁ h₂ harc hn
  have hc' : c = R := by
    have := congrArg norm e
    rw [norm_neg, one_smul, norm_smul, norm_dirVec, mul_one, Real.norm_eq_abs, abs_of_nonneg hc,
      ← dist_eq_norm, dist_comm, hd] at this
    exact this.symm
  have e2 : w' = p - c • d := by rw [← e]; simp
  rw [e2, hc', hpdef, add_sub_cancel_right]

/-- **K-walk on the arc**: with `A = (v, a, b)`, `a − w = Δ dirVec φ`, and a triangle `B` whose
left base end is `walk b j` (`j < N`), the pure right walk from `v` stays on `C(w, Δ₂)` in steps
`α₂`, strictly before the apex of `B` (at angle `φ + α₁/2 + (j+1)α₁`).
TODO: none — proved. What's missing: induction on `i`: room (`arc_sep`), `arc_sub_K`, `normal_fact`
(`u = −dirVec θ_i`), `rigid_step`, `arith_no_land` + `Bprime_span`; `W_center`, `apex_angle`,
`dwalk_angle` for the apex of `B`. Difficulty L. -/
private theorem kwalk_arc (hX : Normal X) (F : DirField X) (hτ : tau X = √3 / 2) {v a b : Pt}
    (ht : IsTri F v a b) {φ : ℝ} (hφ : a - F.partner v = diam X • dirVec φ) {N : ℕ}
    (hN : Runs F b N) {j : ℕ} (hj : j < N) {v' b' : Pt} (ht' : IsTri F v' (walk F b j) b') :
    ∀ i, Runs F v i → walk F v i = F.partner v +
        dist2 X • dirVec (φ + alpha1 X / 2 + (i : ℝ) * alpha2 X) ∧
      (i : ℝ) * alpha2 X < ((j : ℝ) + 1) * alpha1 X := by
  obtain ⟨hα₁, hα₂⟩ := alpha_pos hX
  have hR2 := hX.dist2_pos
  have hΔ2 : dist2 X ≤ diam X := dist2_le_diam X
  have hL := hX.large
  have hwX : F.partner v ∈ X := F.partner_mem v ht.1.1
  have hD := dwalk_angle hX F hτ ht hφ hN
  have hspan := Bprime_span hX F hτ ht (walk F b) N (walk_zero F b) hN
  have hjN : ((j:ℝ) + 1) ≤ N := by exact_mod_cast hj
  have hjα : 0 < ((j:ℝ) + 1) * alpha1 X := by positivity
  have hmul := mul_le_mul_of_nonneg_right hjN hα₁.le
  have hkπ : ((j:ℝ) + 1) * alpha1 X < π / 3 := by nlinarith
  -- the apexes of `A` and `B`
  have hvpos := apex_angle hX F hτ ht hφ
  have hwv' : F.partner v = F.partner v' :=
    W_center hX F hτ ht ht' (walk F b) N (walk_zero F b) hN ⟨j, hj.le, rfl⟩
  have hφ' : walk F b j - F.partner v' = diam X • dirVec (φ + ((j:ℝ) + 1) * alpha1 X) := by
    rw [← hwv']; exact hD j hj.le
  have hv'pos : v' = F.partner v + dist2 X • dirVec (φ + alpha1 X / 2 + ((j:ℝ) + 1) * alpha1 X) := by
    have e := apex_angle hX F hτ ht' hφ'
    rw [← hwv'] at e
    rw [e]; congr 3; ring
  have hvK : F.partner v + dist2 X • dirVec (φ + alpha1 X / 2) ∈ KBall X := by
    rw [← hvpos]; exact ball_polygon_a (Sset_sub ht.1.1) ht.1.2.1
  have hv'K : F.partner v + dist2 X • dirVec (φ + alpha1 X / 2 + ((j:ℝ) + 1) * alpha1 X)
      ∈ KBall X := by
    rw [← hv'pos]; exact ball_polygon_a (Sset_sub ht'.1.1) ht'.1.2.1
  have harc : ∀ ψ ∈ Set.Icc (φ + alpha1 X / 2) (φ + alpha1 X / 2 + ((j:ℝ) + 1) * alpha1 X),
      F.partner v + dist2 X • dirVec ψ ∈ KBall X := fun ψ hψ =>
    (arc_sub_K hX hwX (by linarith) (by linarith [Real.pi_pos]) hvK hv'K ψ hψ).1
  have hv'X : F.partner v + dist2 X • dirVec (φ + alpha1 X / 2 + ((j:ℝ) + 1) * alpha1 X) ∈ X := by
    rw [← hv'pos]; exact Sset_sub ht'.1.1
  obtain ⟨ht1, ht2⟩ := tgap_bounds_exact hX hτ
  have hdt : dist2 X + tgap X = diam X := by unfold tgap; ring
  intro i
  induction i with
  | zero =>
    intro _
    simp only [Nat.cast_zero, zero_mul, add_zero, walk_zero]
    exact ⟨hvpos, hjα⟩
  | succ i ih =>
    intro hr
    obtain ⟨hpos_i, hlt_i⟩ := ih (runs_mono hr (by omega))
    have hRi : RowR F (walk F v i) (walk F v (i + 1)) := hr i (by omega)
    have hyS : walk F v i ∈ Sset X := hRi.1.1
    have hyD : walk F v i ∉ Dset X := fun h => ht.1.2.1 ((walk_D_iff hr i (by omega)).1 h)
    set θi := φ + alpha1 X / 2 + (i : ℝ) * alpha2 X with hθi
    set θB := φ + alpha1 X / 2 + ((j:ℝ) + 1) * alpha1 X with hθB
    rw [hpos_i] at hRi hyS hyD
    have hyX : F.partner v + dist2 X • dirVec θi ∈ X := Sset_sub hyS
    have hθ1 : φ + alpha1 X / 2 ≤ θi := by
      have : 0 ≤ (i : ℝ) * alpha2 X := by positivity
      linarith
    -- room for one more step
    have hroom : θi + alpha2 X ≤ θB := by
      by_contra h; push Not at h
      exact arc_sep hX (by linarith) hv'X hyX (by linarith)
        (by simp only [alpha2] at h; linarith)
    -- the inward normal at `y_i`
    have hu : F.u (F.partner v + dist2 X • dirVec θi) = -dirVec θi := by
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · have e0 : θi = φ + alpha1 X / 2 := by rw [hθi, h0]; simp
        rw [e0, ← hvpos]
        unfold DirField.u
        rw [F.partner_K v ht.1.1 ht.1.2.1]
        have e1 : v - F.partner v = dist2 X • dirVec (φ + alpha1 X / 2) :=
          sub_eq_iff_eq_add'.2 hvpos
        rw [← neg_sub, e1, smul_neg, smul_smul, inv_mul_cancel₀ hR2.ne', one_smul]
      · have hlo : φ + alpha1 X / 2 < θi := by
          have : 0 < (i : ℝ) * alpha2 X := mul_pos (by exact_mod_cast hpos) hα₂
          linarith
        have hn := neg_mem_normalCone (harc θi ⟨hθ1, by linarith⟩)
          (F.partner_mem _ hyS) (F.partner_K _ hyS hyD)
          (dist (F.partner v + dist2 X • dirVec θi) (F.partner (F.partner v + dist2 X • dirVec θi)))⁻¹
          (inv_nonneg.2 dist_nonneg)
        obtain ⟨c, hc, e⟩ := normal_fact hX hlo (by linarith) harc hn
        set y := F.partner v + dist2 X • dirVec θi
        have hFu : F.u y = (dist y (F.partner y))⁻¹ • (F.partner y - y) := rfl
        rw [← hFu] at e
        have hc1 : c = 1 := by
          have := congrArg norm e
          rw [norm_neg, F.norm_u hyS, norm_smul, norm_dirVec, mul_one, Real.norm_eq_abs,
            abs_of_nonneg hc] at this
          exact this.symm
        rw [hc1, one_smul] at e
        rw [← e, neg_neg]
    -- the rigid step
    have hq := rigid_step hX F hτ hwX (θ := θi) (θ₂ := θB)
      (fun ψ hψ => harc ψ ⟨hθ1.trans hψ.1, hψ.2⟩) hroom hyS hyD hu hRi
    have hnext : (((i + 1 : ℕ) : ℝ)) * alpha2 X = (i : ℝ) * alpha2 X + alpha2 X := by
      push_cast; ring
    refine ⟨?_, ?_⟩
    · rw [hq, hθi, hnext, add_assoc]
    · have hle : (((i + 1 : ℕ) : ℝ)) * alpha2 X ≤ ((j : ℝ) + 1) * alpha1 X := by
        rw [hnext]; linarith
      rcases hle.lt_or_eq with h | h
      · exact h
      · exfalso
        refine arith_no_land (R := dist2 X) (t := tgap X) hL ht1 ht2 (j := i + 1) (k := j + 1)
          (by omega) ?_ ?_
        · rw [hdt]; push_cast; exact hkπ
        · rw [hdt]
          have e2 : alpha2 X = 2 * Real.arcsin (1 / (2 * dist2 X)) := rfl
          have e1 : alpha1 X = 2 * Real.arcsin (1 / (2 * diam X)) := rfl
          rw [← e1, ← e2]; push_cast at h ⊢; exact h

/-- K-walks from an apex with a successor terminate.
TODO: none — proved. What's missing: `kwalk_arc`, `alpha_pos`, Archimedes. Difficulty S–M. -/
private theorem kwalk_stops (hX : Normal X) (F : DirField X) (hτ : tau X = √3 / 2) {v a b : Pt}
    (ht : IsTri F v a b) {N : ℕ} (hN : Runs F b N) {j : ℕ} (hj : j < N) {v' b' : Pt}
    (ht' : IsTri F v' (walk F b j) b') : ∃ i, Runs F v i ∧ ¬ ∃ q, RowR F (walk F v i) q := by
  have hΔ : 0 < diam X := hX.dist2_pos.trans_le (dist2_le_diam X)
  have haw : ‖(diam X)⁻¹ • (a - F.partner v)‖ = 1 := by
    rw [norm_smul, ← dist_eq_norm, ht.1.2.2.2.2.2, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hΔ),
      inv_mul_cancel₀ hΔ.ne']
  obtain ⟨φ, -, hφ'⟩ := exists_angle haw
  have hφ : a - F.partner v = diam X • dirVec φ := by
    rw [hφ', smul_smul, mul_inv_cancel₀ hΔ.ne', one_smul]
  by_contra h
  push Not at h
  have hall : ∀ i, Runs F v i := by
    intro i
    induction i with
    | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
    | succ i ih =>
      obtain ⟨q, hq⟩ := h i ih
      exact runs_succ hX ih hq
  have hα := alpha_pos hX
  obtain ⟨i, hi⟩ := exists_nat_gt (((j : ℝ) + 1) * alpha1 X / alpha2 X)
  have := (kwalk_arc hX F hτ ht hφ hN hj ht' i (hall i)).2
  rw [div_lt_iff₀ hα.2] at hi
  linarith

/-- A point at distance `R > 0` from `w` is `w + R • dirVec φ` for some angle `φ`. -/
private theorem angle_of_dist {p w : Pt} {R : ℝ} (hR : 0 < R) (h : dist p w = R) :
    ∃ φ : ℝ, p - w = R • dirVec φ := by
  have hn : ‖R⁻¹ • (p - w)‖ = 1 := by
    rw [norm_smul, ← dist_eq_norm, h, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR),
      inv_mul_cancel₀ hR.ne']
  obtain ⟨φ, -, hφ⟩ := exists_angle hn
  exact ⟨φ, by rw [hφ, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]⟩

private theorem dirVec_shift {x y : ℝ} (h : dirVec x = dirVec y) (c : ℝ) :
    dirVec (x + c) = dirVec (y + c) := by
  rw [dirVec_addR, dirVec_addR, h]

/-- **No apex strictly inside** the arc `(θ_A, θ_B)` when `B` is the first successor of `A`.
TODO: none — proved. -/
private theorem no_apex_inside (hX : Normal X) (F : DirField X) (hτ : tau X = √3 / 2)
    {v a b : Pt} (ht : IsTri F v a b) {N : ℕ} (hN : Runs F b N) {j : ℕ} (hj : j < N)
    {v' b' : Pt} (ht' : IsTri F v' (walk F b j) b')
    (hmin : ∀ j' < j, ¬ TriAt F (walk F b j')) {i : ℕ} (hi : 1 ≤ i) (hr : Runs F v i)
    {v'' a'' b'' : Pt} (ht'' : IsTri F v'' a'' b'') (hv'' : v'' = walk F v i) : False := by
  obtain ⟨hα₁, hα₂⟩ := alpha_pos hX
  have hR2 := hX.dist2_pos
  have hΔ2 : dist2 X ≤ diam X := dist2_le_diam X
  have hL := hX.large
  have hΔ1 : 1 ≤ diam X := by linarith
  have hΔ : 0 < diam X := by linarith
  have hwX : F.partner v ∈ X := F.partner_mem v ht.1.1
  obtain ⟨φ, hφ⟩ := angle_of_dist hΔ ht.1.2.2.2.2.2
  obtain ⟨hv''pos, hlt⟩ := kwalk_arc hX F hτ ht hφ hN hj ht' i hr
  have hD := dwalk_angle hX F hτ ht hφ hN
  have hspan := Bprime_span hX F hτ ht (walk F b) N (walk_zero F b) hN
  have hbS : b ∈ Sset X := ht.2.1.2.2.1
  have hwalkX : ∀ m ≤ N, walk F b m ∈ X := fun m hm => Sset_sub (walk_mem_S hN hbS m hm)
  have hiα : (0:ℝ) < (i:ℝ) * alpha2 X := mul_pos (by exact_mod_cast hi) hα₂
  have hjN : ((j:ℝ) + 1) ≤ N := by exact_mod_cast hj
  have hjα : 0 < ((j:ℝ) + 1) * alpha1 X := by positivity
  have hmul := mul_le_mul_of_nonneg_right hjN hα₁.le
  -- the two end points of the arc lie in `K`
  have hvK : F.partner v + dist2 X • dirVec (φ + alpha1 X / 2) ∈ KBall X := by
    rw [← apex_angle hX F hτ ht hφ]
    exact ball_polygon_a (Sset_sub ht.1.1) ht.1.2.1
  have hwv' : F.partner v = F.partner v' :=
    W_center hX F hτ ht ht' (walk F b) N (walk_zero F b) hN ⟨j, hj.le, rfl⟩
  have hφ' : walk F b j - F.partner v' = diam X • dirVec (φ + ((j:ℝ) + 1) * alpha1 X) := by
    rw [← hwv']; exact hD j hj.le
  have hv'K : F.partner v + dist2 X • dirVec (φ + alpha1 X / 2 + ((j:ℝ) + 1) * alpha1 X)
      ∈ KBall X := by
    have e := apex_angle hX F hτ ht' hφ'
    rw [← hwv'] at e
    rw [show φ + alpha1 X / 2 + ((j:ℝ) + 1) * alpha1 X
        = φ + ((j:ℝ) + 1) * alpha1 X + alpha1 X / 2 by ring, ← e]
    exact ball_polygon_a (Sset_sub ht'.1.1) ht'.1.2.1
  have harc : ∀ ψ ∈ Set.Icc (φ + alpha1 X / 2) (φ + alpha1 X / 2 + ((j:ℝ) + 1) * alpha1 X),
      F.partner v + dist2 X • dirVec ψ ∈ KBall X := fun ψ hψ =>
    (arc_sub_K hX hwX (by linarith) (by linarith [Real.pi_pos]) hvK hv'K ψ hψ).1
  -- the centre of `A''` is `w`
  have hθ1 : φ + alpha1 X / 2 < φ + alpha1 X / 2 + (i:ℝ) * alpha2 X := by linarith
  have hθ2 : φ + alpha1 X / 2 + (i:ℝ) * alpha2 X
      < φ + alpha1 X / 2 + ((j:ℝ) + 1) * alpha1 X := by linarith
  have hv''S := ht''.1.1
  have hdw'' : dist (F.partner v + dist2 X • dirVec (φ + alpha1 X / 2 + (i:ℝ) * alpha2 X))
      (F.partner v'') = dist2 X := by
    rw [← hv''pos, ← hv'']; exact F.partner_K v'' hv''S ht''.1.2.1
  have hww'' : F.partner v = F.partner v'' :=
    centre_eq hX (F.partner_mem v'' hv''S) hθ1 hθ2 harc hdw''
  -- the base end `a''` sits at angle `ψ = φ + i α₂` on `C(w, Δ)`
  obtain ⟨φ'', hφ''⟩ := angle_of_dist hΔ ht''.1.2.2.2.2.2
  have e'' := apex_angle hX F hτ ht'' hφ''
  rw [← hww''] at e'' hφ''
  have hdir : dirVec (φ'' + alpha1 X / 2) = dirVec (φ + alpha1 X / 2 + (i:ℝ) * alpha2 X) := by
    have := e''.symm.trans (hv''.trans hv''pos)
    exact smul_right_injective _ hR2.ne' (add_left_cancel this)
  have hdir' : dirVec φ'' = dirVec (φ + (i:ℝ) * alpha2 X) := by
    have := dirVec_shift hdir (-(alpha1 X / 2))
    rwa [show φ'' + alpha1 X / 2 + -(alpha1 X / 2) = φ'' by ring,
      show φ + alpha1 X / 2 + (i:ℝ) * alpha2 X + -(alpha1 X / 2) = φ + (i:ℝ) * alpha2 X by ring]
      at this
  rw [hdir'] at hφ''
  have ha''X : F.partner v + diam X • dirVec (φ + (i:ℝ) * alpha2 X) ∈ X := by
    rw [← sub_eq_iff_eq_add'.1 hφ'']; exact Sset_sub ht''.1.2.2.1
  have hsep : ∀ y : ℝ, F.partner v + diam X • dirVec y ∈ X → y < φ + (i:ℝ) * alpha2 X →
      φ + (i:ℝ) * alpha2 X - y < alpha1 X → False :=
    fun y hy h0 h1 => arc_sep hX hΔ1 ha''X hy (by linarith) h1
  -- `k = ⌊i α₂ / α₁⌋`
  have hA : (0:ℝ) ≤ (i:ℝ) * alpha2 X / alpha1 X := by positivity
  have hk1 := Nat.floor_le hA
  have hk2 := Nat.lt_floor_add_one ((i:ℝ) * alpha2 X / alpha1 X)
  generalize ⌊(i:ℝ) * alpha2 X / alpha1 X⌋₊ = k at hk1 hk2
  rw [le_div_iff₀ hα₁] at hk1
  rw [div_lt_iff₀ hα₁] at hk2
  have hkj : k ≤ j := by
    have : (k:ℝ) < (j:ℝ) + 1 := by
      by_contra hc
      push_neg at hc
      nlinarith [mul_le_mul_of_nonneg_right hc hα₁.le]
    have : k < j + 1 := by exact_mod_cast this
    omega
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0
    simp only [Nat.cast_zero, zero_add, one_mul] at hk2
    refine hsep φ ?_ (by linarith) (by linarith)
    rw [← sub_eq_iff_eq_add'.1 hφ]; exact Sset_sub ht.1.2.2.1
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    push_cast at hk1 hk2
    have hmN : m ≤ N := by omega
    have hwm := hD m hmN
    have hwmX : F.partner v + diam X • dirVec (φ + ((m:ℝ) + 1) * alpha1 X) ∈ X := by
      rw [← sub_eq_iff_eq_add'.1 hwm]; exact hwalkX m hmN
    rcases lt_or_eq_of_le hk1 with hlt' | heq
    · exact hsep _ hwmX (by linarith) (by linarith)
    · refine hmin m (by omega) ⟨v'', a'', b'', ht'', ?_⟩
      rw [sub_eq_iff_eq_add'.1 hφ'', sub_eq_iff_eq_add'.1 hwm, heq]

/-- **(Count)** at `τ = √3/2`: `q₂ ≤ #breaks + cBad`.
Each good-base triangle `A` is charged to a break: the K-break `b_{AB} ∈ [v_A, v_B)` if `A` has a
successor `B` on its D-walk ((W), (Arc), (Rigid), (Arith)), else the right end of its D-walk (a
D-break, (B′)).  K-breaks of different triangles lie on disjoint half-open arcs
(`arc_centre_unique`, one triangle per apex); D-breaks of different walks are distinct
(`rowR_inj`); K- and D-breaks differ (`∉ D` vs `∈ D`).

TODO: none — proved (charging relation `Ch`: successor-free triangles are charged to the end
of their D-walk, the others to the first break of their K-walk (`kwalk_arc`); injectivity via
`walk_suffix`, `base_apex_unique`, `no_apex_inside`, and `D`-membership).
What's missing: (was) the injection and its well-definedness (walk iteration via `rowR_fun`, a
`Nat.find` for the first break), assembling the chain lemmas above.
Acceptance: no `sorry`.
Depends on: `card_badBase_le`, `tri_of_twoRung`, `Bprime_walk_right`, `Bprime_rot`,
`Bprime_span`, `W_center`, `apex_eq`, `arc_sub_K`, `normal_fact`, `rigid_step`,
`arith_no_land`, `tgap_bounds_exact`, `arc_centre_unique`, `rowR_fun`, `rowR_inj`.
Difficulty XL. -/
theorem exact_breaks (hX : Normal X) (F : DirField X) (hτ : tau X = √3 / 2) :
    ((twoRungVerts X F).card : ℝ) ≤ (breaks X F).card + cBad := by
  classical
  set V := twoRungVerts X F
  set Vb := V.filter (fun v => ¬ ∃ a b, IsTri F v a b)
  set Vg := V.filter (fun v => ∃ a b, IsTri F v a b)
  have hsplit : Vg.card + Vb.card = V.card := card_filter_add_card_filter_not _
  have hbad := card_badBase_le hX F hτ
  -- the charging relation
  let DC : Pt → Pt → Prop := fun b p => ∃ N, Runs F b N ∧ (¬ ∃ q, RowR F (walk F b N) q) ∧
    p = walk F b N ∧ ∀ j < N, ¬ TriAt F (walk F b j)
  let KC : Pt → Pt → Pt → Prop := fun v b p => ∃ N j, Runs F b N ∧ j < N ∧
    TriAt F (walk F b j) ∧ (∀ j' < j, ¬ TriAt F (walk F b j')) ∧
    ∃ i, Runs F v i ∧ (¬ ∃ q, RowR F (walk F v i) q) ∧ p = walk F v i
  let Ch : Pt → Pt → Prop := fun v p => ∃ a b, IsTri F v a b ∧ (DC b p ∨ KC v b p)
  have hex : ∀ v ∈ Vg, ∃ p ∈ breaks X F, Ch v p := by
    intro v hv
    obtain ⟨a, b, ht⟩ := (mem_filter.1 hv).2
    obtain ⟨N, hN, hs⟩ := dwalk_stops hX F hτ ht
    have hbS : b ∈ Sset X := ht.2.1.2.2.1
    have hvS : v ∈ Sset X := ht.1.1
    by_cases hsucc : ∃ j, j < N ∧ TriAt F (walk F b j)
    · let j := Nat.find hsucc
      have hj : j < N ∧ TriAt F (walk F b j) := Nat.find_spec hsucc
      have hmin : ∀ j' < j, ¬ TriAt F (walk F b j') := fun j' hj' h =>
        Nat.find_min hsucc hj' ⟨hj'.trans hj.1, h⟩
      obtain ⟨v', a', b', ht', ha'⟩ := hj.2
      rw [ha'] at ht'
      obtain ⟨i, hi, his⟩ := kwalk_stops hX F hτ ht hN hj.1 ht'
      refine ⟨walk F v i, mem_filter.2 ⟨walk_mem_S hi hvS i le_rfl, his⟩, a, b, ht,
        Or.inr ⟨N, j, hN, hj.1, hj.2, hmin, i, hi, his, rfl⟩⟩
    · push Not at hsucc
      refine ⟨walk F b N, mem_filter.2 ⟨walk_mem_S hN hbS N le_rfl, hs⟩, a, b, ht,
        Or.inl ⟨N, hN, hs, rfl, fun j hj => hsucc j hj⟩⟩
  -- the charging relation is injective
  have hDD : ∀ {v a b v' a' b' p}, IsTri F v a b → IsTri F v' a' b' → DC b p → DC b' p →
      v = v' := by
    intro v a b v' a' b' p ht ht' hd hd'
    -- wlog `N' ≤ N`
    have key : ∀ {v a b v' a' b' : Pt} {N N' : ℕ}, IsTri F v a b → IsTri F v' a' b' →
        Runs F b N → Runs F b' N' → walk F b N = walk F b' N' → N' ≤ N →
        (∀ j < N, ¬ TriAt F (walk F b j)) → v = v' := by
      intro v a b v' a' b' N N' ht ht' hN hN' he hle hfree
      have hsuf := walk_suffix hX hN hN' he hle
      rcases Nat.lt_or_ge N' N with hlt | hge
      · exfalso
        set d := N - N'
        have hd1 : 1 ≤ d := by omega
        have hR := hN (d - 1) (by omega)
        rw [show d - 1 + 1 = d by omega, hsuf] at hR
        have := rowR_inj hX hR ht'.2.2.2.2.1
        exact hfree (d - 1) (by omega) ⟨v', a', b', ht', this.symm⟩
      · have hNN : N = N' := le_antisymm hge hle
        rw [hNN, Nat.sub_self, walk_zero] at hsuf
        subst hsuf
        have haa := rowR_inj hX ht.2.2.2.2.1 ht'.2.2.2.2.1
        subst haa
        have hab : a ≠ b := by
          intro e; have := ht.2.2.2.2.1.1.2.2.1; rw [e, dist_self] at this; norm_num at this
        exact base_apex_unique hX F hτ hab ht.1 ht.2.1 ht'.1 ht'.2.1 ht.2.2.1 ht.2.2.2.1
          ht'.2.2.1 ht'.2.2.2.1
    obtain ⟨N, hN, -, hp, hfree⟩ := hd
    obtain ⟨N', hN', -, hp', hfree'⟩ := hd'
    rcases le_total N' N with hle | hle
    · exact key ht ht' hN hN' (hp.symm.trans hp') hle hfree
    · exact (key ht' ht hN' hN (hp'.symm.trans hp) hle hfree').symm
  have hKK : ∀ {v a b v' a' b' p}, IsTri F v a b → IsTri F v' a' b' → KC v b p → KC v' b' p →
      v = v' := by
    intro v a b v' a' b' p ht ht' hk hk'
    have key : ∀ {v a b v' a' b' : Pt} {i i' : ℕ}, IsTri F v a b → IsTri F v' a' b' →
        KC v b (walk F v i) → Runs F v i → Runs F v' i' → walk F v i = walk F v' i' →
        i' ≤ i → v = v' := by
      intro v a b v' a' b' i i' ht ht' hk hi hi' he hle
      have hsuf := walk_suffix hX hi hi' he hle
      rcases Nat.lt_or_ge i' i with hlt | hge
      · exfalso
        obtain ⟨N, j, hN, hj, ⟨v₁, a₁, b₁, ht₁, ha₁⟩, hmin, -⟩ := hk
        rw [ha₁] at ht₁
        exact no_apex_inside hX F hτ ht hN hj ht₁ hmin (i := i - i') (by omega)
          (runs_mono hi (by omega)) ht' hsuf.symm
      · have : i = i' := le_antisymm hge hle
        rw [this, Nat.sub_self, walk_zero] at hsuf
        exact hsuf
    obtain ⟨N, j, hN, hj, htj, hmin, i, hi, his, hp⟩ := hk
    obtain ⟨N', j', hN', hj', htj', hmin', i', hi', his', hp'⟩ := hk'
    subst hp
    rcases le_total i' i with hle | hle
    · exact key ht ht' ⟨N, j, hN, hj, htj, hmin, i, hi, his, rfl⟩ hi hi' hp' hle
    · exact (key ht' ht ⟨N', j', hN', hj', htj', hmin', i', hi', his', rfl⟩ hi' hi
        hp'.symm hle).symm
  have hDK : ∀ {v a b v' a' b' p}, IsTri F v a b → IsTri F v' a' b' → DC b p → KC v' b' p →
      False := by
    intro v a b v' a' b' p ht ht' hd hk
    obtain ⟨N, hN, -, hp, -⟩ := hd
    obtain ⟨-, -, -, -, -, -, i, hi, -, hp'⟩ := hk
    have h1 := (walk_D_iff hN N le_rfl).2 ht.2.1.2.2.2.1
    have h2 := (walk_D_iff hi i le_rfl).1
    rw [← hp, hp'] at h1
    exact ht'.1.2.1 (h2 h1)
  have huniq : ∀ {v v' p}, Ch v p → Ch v' p → v = v' := by
    intro v v' p ⟨a, b, ht, h⟩ ⟨a', b', ht', h'⟩
    rcases h with hd | hk <;> rcases h' with hd' | hk'
    · exact hDD ht ht' hd hd'
    · exact (hDK ht ht' hd hk').elim
    · exact (hDK ht' ht hd' hk).elim
    · exact hKK ht ht' hk hk'
  -- the injection
  let g : Pt → Pt := fun v => if h : v ∈ Vg then (hex v h).choose else 0
  have hg : ∀ v ∈ Vg, g v ∈ breaks X F ∧ Ch v (g v) := by
    intro v hv
    have : g v = (hex v hv).choose := dif_pos hv
    rw [this]; exact (hex v hv).choose_spec
  have hinj : Set.InjOn g ↑Vg := fun v hv v' hv' e =>
    huniq (hg v hv).2 (e ▸ (hg v' hv').2)
  have hcard := card_le_card_of_injOn g (fun v hv => (hg v hv).1) hinj
  have : (Vg.card : ℝ) ≤ (breaks X F).card := by exact_mod_cast hcard
  have hs : (V.card : ℝ) = Vg.card + Vb.card := by exact_mod_cast hsplit.symm
  rw [hs]
  linarith

end

end Erdos132Main
