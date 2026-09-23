import Erdos132.E132MainDefs

/-!
# Erdős Problem 132, `54/37` theorem — direction-measure counting for outward normals

Infrastructure for the bad-edge counts KK, DD and (c2) of §5.2 (`E132MainLocal.lean`).

The paper counts bad edges with arc length along `∂K` (Lemma 5.2, the walk of (c2)).  Here we
avoid convex-curve arc length altogether and work with a finite set `V` of points carrying unit
*outward normals* `nrm v` with the strict chord inequalities `(w − v)·nrm v < 0` (a
`NormalConfig`).  For such a configuration:

* two points whose normals lie in a common half-plane `{n · g ≥ c}` are separated along `g^⊥`:
  `c·|w − v| ≤ |det(g, w − v)|` (`NormalConfig.sep_det2`, via `wedge_sep`);
* hence the points whose normals lie in the *cap* between the normals of a unit edge `pq`
  number at most `2/|n_p + n_q| + 1` (`NormalConfig.card_cap_le`), and a direction lies in the
  caps of at most `D·N` oriented edges (`D` = degree bound);
* integrating over directions (`sum_dirMeasure_le`), with each cap of measure `∠(n_p, n_q)`
  (`ang_le_dirMeasure_cap`): `#E · β₀ ≤ 2π·D·N` (`NormalConfig.card_mul_le_of_edges`) —
  this gives KK and DD;
* for (c2), windows of half-width `1/800` around the normals, and the discrete "walk":
  a point `v` at depth `≤ 1` in a disc `D(x, R) ⊇ V` whose normal is not nearly parallel to
  `x − v` has all window-neighbours on one side within distance `412`
  (`NormalConfig.card_walk_mul_le`).
-/

open Finset Real
open Erdos132Convex (Pt)
open scoped Classical

namespace Erdos132Main

namespace Curve

noncomputable section

/-! ## Planar coordinates -/

theorem inner_coord (x y : Pt) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

theorem norm_sq_coord (x : Pt) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_coord]; ring

theorem det2_eq_inner_perp (u e : Pt) : det2 u e = inner ℝ e (perp u) := by
  simp [det2, perp, inner_coord]; ring

theorem det2_sub_right (u x y : Pt) : det2 u (x - y) = det2 u x - det2 u y := by
  simp only [det2, PiLp.sub_apply]; ring

theorem det2_swap (a b : Pt) : det2 b a = - det2 a b := by
  simp only [det2]; ring

theorem lagrange (e u : Pt) : inner ℝ e u ^ 2 + det2 u e ^ 2 = ‖e‖ ^ 2 * ‖u‖ ^ 2 := by
  rw [norm_sq_coord, norm_sq_coord, inner_coord, det2]; ring

theorem abs_det2_le (w e : Pt) : |det2 w e| ≤ ‖e‖ * ‖w‖ := by
  have h := lagrange e w
  have h2 : det2 w e ^ 2 ≤ (‖e‖ * ‖w‖) ^ 2 := by nlinarith [sq_nonneg (inner ℝ e w)]
  have := sq_le_sq.1 h2
  rwa [abs_of_nonneg (by positivity : 0 ≤ ‖e‖ * ‖w‖)] at this

/-- Inner product in an orthonormal frame `(e, e^⊥)`. -/
theorem inner_frame {e : Pt} (he : ‖e‖ = 1) (w₁ w₂ : Pt) :
    inner ℝ w₁ w₂ = inner ℝ w₁ e * inner ℝ w₂ e + det2 e w₁ * det2 e w₂ := by
  have h := norm_sq_coord e
  rw [he] at h
  rw [inner_coord, inner_coord, inner_coord]
  simp only [det2]
  linear_combination (w₁ 0 * w₂ 0 + w₁ 1 * w₂ 1) * h

/-- Unit vectors with `a · b ≥ 1` coincide. -/
theorem eq_of_one_le_inner {a b : Pt} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (h : 1 ≤ inner ℝ a b) :
    a = b := by
  have h2 := norm_sub_sq_real a b
  rw [ha, hb] at h2
  have : ‖a - b‖ ^ 2 ≤ 0 := by linarith
  have : ‖a - b‖ = 0 := by nlinarith [norm_nonneg (a - b)]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

/-- Unit vectors with `det(a, b) = 0` are equal or opposite. -/
theorem eq_or_eq_neg_of_det2_eq_zero {a b : Pt} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (h : det2 a b = 0) : a = b ∨ a = -b := by
  have hl := lagrange b a
  rw [h, ha, hb] at hl
  have h1 : inner ℝ b a = 1 ∨ inner ℝ b a = -1 := by
    have : (inner ℝ b a - 1) * (inner ℝ b a + 1) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  rcases h1 with h1 | h1
  · left; exact eq_of_one_le_inner ha hb (by rw [real_inner_comm]; linarith)
  · right
    have hn : ‖-b‖ = 1 := by rw [norm_neg, hb]
    exact eq_of_one_le_inner ha hn (by rw [inner_neg_right, real_inner_comm]; linarith)

theorem det2_sub_left (u v e : Pt) : det2 (u - v) e = det2 u e - det2 v e := by
  simp only [det2, PiLp.sub_apply]; ring

/-- Grassmann–Plücker relation in the plane. -/
theorem plucker (w u n h : Pt) :
    det2 w n * det2 u h = det2 w u * det2 n h + det2 w h * det2 u n := by
  simp only [det2]; ring

/-! ## Directions -/

theorem continuous_dirVec : Continuous dirVec := by
  unfold dirVec; fun_prop

theorem norm_dirVec (θ : ℝ) : ‖dirVec θ‖ = 1 := by
  have h := norm_sq_coord (dirVec θ)
  have h2 : (dirVec θ) 0 ^ 2 + (dirVec θ) 1 ^ 2 = 1 := by simp [dirVec]
  rw [h2] at h
  nlinarith [norm_nonneg (dirVec θ)]

theorem dirVec_add_int_mul (θ : ℝ) (k : ℤ) : dirVec (θ + k * (2 * π)) = dirVec θ := by
  simp [dirVec, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

theorem exists_dirVec {n : Pt} (hn : ‖n‖ = 1) : ∃ θ : ℝ, dirVec θ = n := by
  set z : ℂ := ⟨n 0, n 1⟩
  have hsq := norm_sq_coord n
  rw [hn] at hsq
  have hz : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp only [z]
    rw [show n 0 * n 0 + n 1 * n 1 = 1 by nlinarith, Real.sqrt_one]
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; norm_num at hz
  refine ⟨Complex.arg z, ?_⟩
  ext i; fin_cases i
  · simp [dirVec, Complex.cos_arg hz0, hz, z]
  · simp [dirVec, Complex.sin_arg, hz, z]

theorem inner_dirVec (θ φ : ℝ) : inner ℝ (dirVec θ) (dirVec φ) = Real.cos (θ - φ) := by
  rw [inner_coord, Real.cos_sub]; simp [dirVec]

/-- `dirVec` is `1`-Lipschitz (chord `≤` arc). -/
theorem norm_dirVec_sub_le (θ φ : ℝ) : ‖dirVec θ - dirVec φ‖ ≤ |θ - φ| := by
  have h := norm_sub_sq_real (dirVec θ) (dirVec φ)
  rw [norm_dirVec, norm_dirVec, inner_dirVec] at h
  have hc := Real.one_sub_sq_div_two_le_cos (x := θ - φ)
  have hsq : ‖dirVec θ - dirVec φ‖ ^ 2 ≤ |θ - φ| ^ 2 := by rw [sq_abs]; nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (abs_nonneg _)).1 hsq

/-! ## Measure of sets of directions -/

/-- The measure of the set of directions `θ ∈ [0, 2π)` with `dirVec θ ∈ Q`. -/
def dirMeasure (Q : Set Pt) : ℝ :=
  (MeasureTheory.volume {θ : ℝ | θ ∈ Set.Ico 0 (2 * π) ∧ dirVec θ ∈ Q}).toReal

/-- A closed arc of directions of length `α ≤ 2π` inside `Q` gives `dirMeasure Q ≥ α`. -/
theorem le_dirMeasure_of_Icc {Q : Set Pt} {c α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 2 * π)
    (h : ∀ θ ∈ Set.Icc c (c + α), dirVec θ ∈ Q) : α ≤ dirMeasure Q := by
  have hpi := Real.pi_pos
  set k : ℤ := ⌊c / (2 * π)⌋
  set c' := c - k * (2 * π)
  have hk1 : (k : ℝ) ≤ c / (2 * π) := Int.floor_le _
  have hk2 : c / (2 * π) < k + 1 := Int.lt_floor_add_one _
  have hc0 : 0 ≤ c' := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * π)).1 hk1; simp only [c']; linarith
  have hc1 : c' < 2 * π := by
    have := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * π)).1 hk2; simp only [c']; linarith
  have h' : ∀ θ ∈ Set.Icc c' (c' + α), dirVec θ ∈ Q := by
    intro θ hθ
    rw [← dirVec_add_int_mul θ k]
    exact h _ ⟨by simp only [c'] at hθ; linarith [hθ.1], by simp only [c'] at hθ; linarith [hθ.2]⟩
  set T : Set ℝ := {θ | θ ∈ Set.Ico 0 (2 * π) ∧ dirVec θ ∈ Q}
  have hT1 : Set.Ico c' (min (c' + α) (2 * π)) ⊆ T := fun θ hθ =>
    ⟨⟨by linarith [hθ.1], lt_of_lt_of_le hθ.2 (min_le_right _ _)⟩,
      h' θ ⟨hθ.1, (lt_of_lt_of_le hθ.2 (min_le_left _ _)).le⟩⟩
  have hT2 : Set.Ico 0 (c' + α - 2 * π) ⊆ T := fun θ hθ => by
    refine ⟨⟨hθ.1, by linarith [hθ.2]⟩, ?_⟩
    rw [← dirVec_add_int_mul θ 1]
    exact h' _ ⟨by push_cast; linarith [hθ.1], by push_cast; linarith [hθ.2]⟩
  have hdisj : Disjoint (Set.Ico c' (min (c' + α) (2 * π))) (Set.Ico 0 (c' + α - 2 * π)) := by
    rw [Set.disjoint_left]; intro θ h1 h2; linarith [h1.1, h2.2]
  have hvol : MeasureTheory.volume (Set.Ico c' (min (c' + α) (2 * π)) ∪
      Set.Ico 0 (c' + α - 2 * π)) = ENNReal.ofReal α := by
    rw [MeasureTheory.measure_union hdisj measurableSet_Ico, Real.volume_Ico, Real.volume_Ico]
    rcases le_or_gt (c' + α) (2 * π) with hle | hlt
    · rw [min_eq_left hle, sub_zero,
        ENNReal.ofReal_of_nonpos (show c' + α - 2 * π ≤ 0 by linarith), add_zero,
        add_sub_cancel_left]
    · rw [min_eq_right hlt.le, sub_zero, ← ENNReal.ofReal_add (by linarith) (by linarith)]
      congr 1; ring
  have hTfin : MeasureTheory.volume T ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
      (MeasureTheory.measure_mono (fun θ h => h.1))
  have hle := MeasureTheory.measure_mono (μ := MeasureTheory.volume) (Set.union_subset hT1 hT2)
  rw [hvol] at hle
  have := ENNReal.toReal_mono hTfin hle
  rwa [ENNReal.toReal_ofReal hα] at this

/-- Multiplicity bound: if every direction lies in at most `M` of the closed sets `Q i`, the
direction measures sum to at most `2πM`. -/
theorem sum_dirMeasure_le {ι : Type*} (A : Finset ι) (Q : ι → Set Pt)
    (hQ : ∀ i ∈ A, IsClosed (Q i)) (M : ℕ)
    (hM : ∀ θ : ℝ, (A.filter (fun i => dirVec θ ∈ Q i)).card ≤ M) :
    ∑ i ∈ A, dirMeasure (Q i) ≤ 2 * π * M := by
  classical
  set I : Set ℝ := Set.Ico 0 (2 * π)
  let C : ι → Set ℝ := fun i => {θ | θ ∈ I ∧ dirVec θ ∈ Q i}
  have hCm : ∀ i ∈ A, MeasurableSet (C i) := fun i hi =>
    measurableSet_Ico.inter ((hQ i hi).preimage continuous_dirVec).measurableSet
  have hpt : ∀ θ, ∑ i ∈ A, (C i).indicator (fun _ => (1 : ENNReal)) θ ≤
      I.indicator (fun _ => (M : ENNReal)) θ := by
    intro θ
    by_cases hI : θ ∈ I
    · rw [Set.indicator_of_mem hI]
      simp only [Set.indicator_apply]
      rw [Finset.sum_boole]
      have : (A.filter (fun i => θ ∈ C i)).card ≤ M := by
        refine le_trans (Finset.card_le_card ?_) (hM θ)
        intro i hi
        simp only [Finset.mem_filter] at hi ⊢
        exact ⟨hi.1, hi.2.2⟩
      exact_mod_cast this
    · rw [Set.indicator_of_notMem hI]
      have : ∀ i ∈ A, (C i).indicator (fun _ => (1 : ENNReal)) θ = 0 := fun i _ =>
        Set.indicator_of_notMem (fun h => hI h.1) _
      rw [Finset.sum_eq_zero this]
  have hsum : ∑ i ∈ A, MeasureTheory.volume (C i) ≤ M * ENNReal.ofReal (2 * π) := by
    calc ∑ i ∈ A, MeasureTheory.volume (C i)
        = ∑ i ∈ A, ∫⁻ θ, (C i).indicator (fun _ => (1 : ENNReal)) θ := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [MeasureTheory.lintegral_indicator_const (hCm i hi), one_mul]
      _ = ∫⁻ θ, ∑ i ∈ A, (C i).indicator (fun _ => (1 : ENNReal)) θ := by
          rw [MeasureTheory.lintegral_finsetSum]
          exact fun i hi => measurable_const.indicator (hCm i hi)
      _ ≤ ∫⁻ θ, I.indicator (fun _ => (M : ENNReal)) θ := MeasureTheory.lintegral_mono hpt
      _ = M * ENNReal.ofReal (2 * π) := by
          rw [MeasureTheory.lintegral_indicator_const measurableSet_Ico, Real.volume_Ico,
            sub_zero]
  have hfin : ∀ i ∈ A, MeasureTheory.volume (C i) ≠ ⊤ := fun i _ =>
    ne_top_of_le_ne_top (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
      (MeasureTheory.measure_mono (fun θ h => h.1))
  have h1 : ∑ i ∈ A, dirMeasure (Q i) = (∑ i ∈ A, MeasureTheory.volume (C i)).toReal := by
    rw [ENNReal.toReal_sum hfin]; rfl
  rw [h1]
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top M)
    ENNReal.ofReal_ne_top) hsum
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity)] at h2
  linarith

theorem card_mul_le_of_dirMeasure {ι : Type*} (A : Finset ι) (Q : ι → Set Pt)
    (hQ : ∀ i ∈ A, IsClosed (Q i)) (M : ℕ)
    (hM : ∀ θ : ℝ, (A.filter (fun i => dirVec θ ∈ Q i)).card ≤ M) {α : ℝ}
    (hα : ∀ i ∈ A, α ≤ dirMeasure (Q i)) : (A.card : ℝ) * α ≤ 2 * π * M := by
  have h := sum_dirMeasure_le A Q hQ M hM
  have h2 : ∑ _i ∈ A, α ≤ ∑ i ∈ A, dirMeasure (Q i) := Finset.sum_le_sum hα
  rw [Finset.sum_const, nsmul_eq_mul] at h2
  linarith

/-! ## Caps and windows of directions -/

/-- The *cap* of unit vectors on the short arc between `a` and `b`. -/
def cap (a b : Pt) : Set Pt := {m | 1 + inner ℝ a b ≤ inner ℝ m (a + b)}

/-- The *window* of half-width `ε` (chordal) around `a`. -/
def window (a : Pt) (ε : ℝ) : Set Pt := {m | ‖m - a‖ ≤ ε}

theorem isClosed_cap (a b : Pt) : IsClosed (cap a b) := by
  exact isClosed_le continuous_const (by fun_prop)

theorem isClosed_window (a : Pt) (ε : ℝ) : IsClosed (window a ε) := by
  exact isClosed_le (by fun_prop) continuous_const

/-- The cap between two non-antipodal unit vectors has direction measure `≥ ∠(a, b)`. -/
theorem ang_le_dirMeasure_cap {a b : Pt} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : 0 < 1 + inner ℝ a b) : ang a b ≤ dirMeasure (cap a b) := by
  set g := a + b with hg_def
  set A := ang a b with hA_def
  have hk : inner ℝ a b = Real.cos A := by
    have := InnerProductGeometry.cos_angle_mul_norm_mul_norm a b
    rw [ha, hb, mul_one, mul_one] at this; exact this.symm
  have hA0 : 0 ≤ A := InnerProductGeometry.angle_nonneg a b
  have hAπ : A ≤ π := InnerProductGeometry.angle_le_pi a b
  have hpi := Real.pi_pos
  have hg2 : ‖g‖ ^ 2 = 2 + 2 * inner ℝ a b := by rw [hg_def, norm_add_sq_real, ha, hb]; ring
  have hc2 : 0 ≤ Real.cos (A / 2) := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hhalf : Real.cos (A / 2) ^ 2 = 1 / 2 + Real.cos A / 2 := by
    rw [Real.cos_sq, show 2 * (A / 2) = A by ring]
  have hgc : ‖g‖ = 2 * Real.cos (A / 2) := by
    have : ‖g‖ ^ 2 = (2 * Real.cos (A / 2)) ^ 2 := by rw [hg2, mul_pow, hhalf, hk]; ring
    exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 this
  have hgpos : 0 < ‖g‖ := by
    have : 0 < ‖g‖ ^ 2 := by rw [hg2]; linarith
    exact lt_of_le_of_ne (norm_nonneg _) (fun h => by rw [← h] at this; norm_num at this)
  have hu : ‖‖g‖⁻¹ • g‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hgpos.ne']
  obtain ⟨θb, hθb⟩ := exists_dirVec hu
  have hgθ : g = ‖g‖ • dirVec θb := by rw [hθb, smul_smul, mul_inv_cancel₀ hgpos.ne', one_smul]
  refine le_dirMeasure_of_Icc hA0 (by linarith) (c := θb - A / 2) fun θ hθ => ?_
  show 1 + inner ℝ a b ≤ inner ℝ (dirVec θ) (a + b)
  rw [← hg_def, hgθ, real_inner_smul_right, inner_dirVec]
  have habs : |θ - θb| ≤ A / 2 := abs_le.2 ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hcos : Real.cos (A / 2) ≤ Real.cos (θ - θb) := by
    rw [← Real.cos_abs (θ - θb)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) habs
  rw [hgc, hk]
  nlinarith

theorem two_mul_le_dirMeasure_window {a : Pt} (ha : ‖a‖ = 1) {ε : ℝ} (hε : 0 ≤ ε)
    (hε' : ε ≤ π) : 2 * ε ≤ dirMeasure (window a ε) := by
  obtain ⟨θa, rfl⟩ := exists_dirVec ha
  refine le_dirMeasure_of_Icc (by linarith) (by linarith) (c := θa - ε) fun θ hθ => ?_
  show ‖dirVec θ - dirVec θa‖ ≤ ε
  refine (norm_dirVec_sub_le θ θa).trans ?_
  exact abs_le.2 ⟨by linarith [hθ.1], by linarith [hθ.2]⟩

/-! ## Planar lemmas on caps and wedges -/

/-- A unit vector in the cap of `(a, b)` (`det(a, b) > 0`) is between them. -/
theorem det2_nonneg_of_mem_cap {a b m : Pt} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hm : ‖m‖ = 1)
    (hab : 0 < det2 a b) (h : m ∈ cap a b) : 0 ≤ det2 a m ∧ 0 ≤ det2 m b := by
  have ha2 : a 0 ^ 2 + a 1 ^ 2 = 1 := by rw [← norm_sq_coord, ha]; norm_num
  have hb2 : b 0 ^ 2 + b 1 ^ 2 = 1 := by rw [← norm_sq_coord, hb]; norm_num
  have hm2 : m 0 ^ 2 + m 1 ^ 2 = 1 := by rw [← norm_sq_coord, hm]; norm_num
  set D := det2 a b
  set x := det2 m b
  set y := det2 a m
  set k := inner ℝ a b
  have hcap : 1 + k ≤ inner ℝ m (a + b) := h
  have E1 : D * inner ℝ m (a + b) = (x + y) * (1 + k) := by
    simp only [D, x, y, k, det2, inner_coord, PiLp.add_apply]
    linear_combination (m 0 * b 1 - m 1 * b 0) * ha2 + (a 0 * m 1 - a 1 * m 0) * hb2
  have E2 : D ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y * k := by
    simp only [D, x, y, k, det2, inner_coord]
    linear_combination (-(a 0 * b 1 - a 1 * b 0) ^ 2) * hm2 +
      (m 0 * b 1 - m 1 * b 0) ^ 2 * ha2 + (a 0 * m 1 - a 1 * m 0) ^ 2 * hb2
  have hl := lagrange b a
  rw [ha, hb] at hl
  have hk1 : k ^ 2 < 1 := by
    have : inner ℝ b a = k := real_inner_comm a b
    rw [this] at hl; nlinarith
  have hk0 : 0 < 1 + k := by nlinarith
  have hk2 : k < 1 := by nlinarith
  have hxy : D ≤ x + y := by
    have : D * (1 + k) ≤ (x + y) * (1 + k) := by rw [← E1]; exact mul_le_mul_of_nonneg_left hcap hab.le
    exact le_of_mul_le_mul_right this hk0
  have hxy2 : 0 ≤ x * y := by nlinarith
  constructor
  · show 0 ≤ y
    by_contra hy; push Not at hy; nlinarith
  · show 0 ≤ x
    by_contra hx; push Not at hx; nlinarith

/-- A unit vector between `a` and `b` (`det(a, b) > 0`) is in their cap. -/
theorem mem_cap_of_det2 {a b m : Pt} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hm : ‖m‖ = 1)
    (hab : 0 < det2 a b) (h1 : 0 ≤ det2 a m) (h2 : 0 ≤ det2 m b) : m ∈ cap a b := by
  have ha2 : a 0 ^ 2 + a 1 ^ 2 = 1 := by rw [← norm_sq_coord, ha]; norm_num
  have hb2 : b 0 ^ 2 + b 1 ^ 2 = 1 := by rw [← norm_sq_coord, hb]; norm_num
  have hm2 : m 0 ^ 2 + m 1 ^ 2 = 1 := by rw [← norm_sq_coord, hm]; norm_num
  set D := det2 a b
  set x := det2 m b
  set y := det2 a m
  set k := inner ℝ a b
  have E1 : D * inner ℝ m (a + b) = (x + y) * (1 + k) := by
    simp only [D, x, y, k, det2, inner_coord, PiLp.add_apply]
    linear_combination (m 0 * b 1 - m 1 * b 0) * ha2 + (a 0 * m 1 - a 1 * m 0) * hb2
  have E2 : D ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y * k := by
    simp only [D, x, y, k, det2, inner_coord]
    linear_combination (-(a 0 * b 1 - a 1 * b 0) ^ 2) * hm2 +
      (m 0 * b 1 - m 1 * b 0) ^ 2 * ha2 + (a 0 * m 1 - a 1 * m 0) ^ 2 * hb2
  have hk : k ≤ 1 := by
    have := real_inner_le_norm a b; rw [ha, hb] at this; linarith
  have hl := lagrange b a
  rw [ha, hb] at hl
  have hk0 : 0 ≤ 1 + k := by
    have : inner ℝ b a = k := real_inner_comm a b
    rw [this] at hl; nlinarith
  have hxy2 : D ^ 2 ≤ (x + y) ^ 2 := by nlinarith [mul_nonneg h2 h1]
  have hxy : D ≤ x + y := (sq_le_sq₀ hab.le (by linarith)).1 hxy2
  show 1 + k ≤ inner ℝ m (a + b)
  have : D * (1 + k) ≤ D * inner ℝ m (a + b) := by rw [E1]; nlinarith
  exact le_of_mul_le_mul_left this hab

/-- Two unit vectors `u, w` on the clockwise side of `n`, with `u` closer to `n`: `u` is
counter-clockwise from `w`. -/
theorem det2_tail {u w n : Pt} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (hn : ‖n‖ = 1)
    (hun : 0 ≤ det2 u n) (hwn : 0 ≤ det2 w n) (huw : inner ℝ w n ≤ inner ℝ u n) :
    0 ≤ det2 w u := by
  have hl := lagrange u n
  have hl' := lagrange w n
  rw [hu, hn, det2_swap u n] at hl; rw [hw, hn, det2_swap w n] at hl'
  set a1 := inner ℝ u n
  set b1 := inner ℝ w n
  set s := det2 u n
  set t := det2 w n
  have key : det2 w u = t * a1 - s * b1 := by
    have hn2 : n 0 ^ 2 + n 1 ^ 2 = 1 := by rw [← norm_sq_coord, hn]; norm_num
    simp only [a1, b1, s, t, det2, inner_coord]
    linear_combination (-(w 0 * u 1 - w 1 * u 0)) * hn2
  rw [key]
  have hs1 : s ^ 2 = 1 - a1 ^ 2 := by linarith
  have ht1 : t ^ 2 = 1 - b1 ^ 2 := by linarith
  rcases le_or_gt 0 b1 with hb | hb
  · have hst : s ≤ t := (sq_le_sq₀ hun hwn).1 (by nlinarith)
    nlinarith
  · rcases le_or_gt 0 a1 with ha' | ha'
    · nlinarith
    · have hst : t ≤ s := (sq_le_sq₀ hwn hun).1 (by nlinarith)
      nlinarith

/-- **Wedge separation.**  If `d · a ≤ 0 ≤ d · b` with `det(a, b) > 0` and both unit normals in
the half-plane `{n · g ≥ c}`, then `d` makes a small angle with `g^⊥`: `c|d| ≤ det(g, d)`. -/
theorem wedge_sep {a b g d : Pt} {c : ℝ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : 0 ≤ c)
    (hag : c ≤ inner ℝ a g) (hbg : c ≤ inner ℝ b g) (hab : 0 < det2 a b)
    (hda : inner ℝ d a ≤ 0) (hdb : 0 ≤ inner ℝ d b) : c * ‖d‖ ≤ det2 g d := by
  have ha2 : a 0 ^ 2 + a 1 ^ 2 = 1 := by rw [← norm_sq_coord, ha]; norm_num
  have hb2 : b 0 ^ 2 + b 1 ^ 2 = 1 := by rw [← norm_sq_coord, hb]; norm_num
  have hd2 := norm_sq_coord d
  set D := det2 a b
  have I1 : D * det2 g d = inner ℝ d b * inner ℝ a g - inner ℝ d a * inner ℝ b g := by
    simp only [D, det2, inner_coord]; ring
  have I2 : (inner ℝ d b - inner ℝ d a) ^ 2 - ‖d‖ ^ 2 * D ^ 2 =
      -2 * (inner ℝ d a * inner ℝ d b) * (1 - inner ℝ a b) := by
    rw [hd2]
    simp only [D, det2, inner_coord]
    linear_combination (-(d 0 * a 0 + d 1 * a 1) ^ 2) * hb2 + (-(d 0 * b 0 + d 1 * b 1) ^ 2) * ha2
  have hk : inner ℝ a b ≤ 1 := by
    have := real_inner_le_norm a b; rw [ha, hb] at this; linarith
  have hprod : inner ℝ d a * inner ℝ d b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hda hdb
  have hsq : (‖d‖ * D) ^ 2 ≤ (inner ℝ d b - inner ℝ d a) ^ 2 := by nlinarith
  have hnd : ‖d‖ * D ≤ inner ℝ d b - inner ℝ d a :=
    (sq_le_sq₀ (by positivity) (by linarith)).1 hsq
  have h3 : c * (inner ℝ d b - inner ℝ d a) ≤ D * det2 g d := by
    rw [I1]; nlinarith
  have h4 : D * (c * ‖d‖) ≤ D * det2 g d := by nlinarith
  exact le_of_mul_le_mul_left h4 hab

/-! ## Separated reals -/

/-- `c`-separated reals in `[a, b]` number at most `(b − a)/c + 1`. -/
theorem card_le_of_sep {c a : ℝ} (hc : 0 < c) (T : Finset ℝ) : ∀ b : ℝ, a ≤ b + c →
    (∀ x ∈ T, a ≤ x ∧ x ≤ b) → (∀ x ∈ T, ∀ y ∈ T, x ≠ y → c ≤ |x - y|) →
    (T.card : ℝ) ≤ (b - a) / c + 1 := by
  induction T using Finset.induction_on_max with
  | empty =>
    intro b hb _ _
    have : -1 ≤ (b - a) / c := by rw [le_div_iff₀ hc]; linarith
    simp; linarith
  | insert m T hlt ih =>
    intro b hb hmem hsep
    have hmT : m ∉ T := fun h => lt_irrefl _ (hlt m h)
    have hm := hmem m (mem_insert_self _ _)
    have hT : ∀ x ∈ T, a ≤ x ∧ x ≤ m - c := by
      intro x hx
      refine ⟨(hmem x (mem_insert_of_mem hx)).1, ?_⟩
      have := hsep x (mem_insert_of_mem hx) m (mem_insert_self _ _) (hlt x hx).ne
      rw [abs_of_neg (by linarith [hlt x hx])] at this; linarith
    have h1 := ih (m - c) (by linarith [hm.1]) hT
      (fun x hx y hy hxy => hsep x (mem_insert_of_mem hx) y (mem_insert_of_mem hy) hxy)
    rw [card_insert_of_notMem hmT]; push_cast
    have : (m - c - a) / c + 1 + 1 ≤ (b - a) / c + 1 := by
      rw [div_add_one hc.ne', div_add_one hc.ne', div_add_one hc.ne', div_le_div_iff_of_pos_right hc]
      linarith [hm.2]
    linarith

/-- One-sided count: `c`-separated values `s` on `G`, any two within `ℓ` when ordered. -/
theorem card_le_of_oneSided {G : Finset Pt} (s : Pt → ℝ) {c ℓ : ℝ} (hc : 0 < c) (hℓ : 0 ≤ ℓ)
    (hsep : ∀ v ∈ G, ∀ w ∈ G, v ≠ w → c ≤ |s v - s w|)
    (hside : ∀ v ∈ G, ∀ w ∈ G, s v < s w → s w - s v ≤ ℓ) :
    (G.card : ℝ) ≤ ℓ / c + 1 := by
  rcases G.eq_empty_or_nonempty with rfl | hne
  · simp; positivity
  obtain ⟨v₀, hv₀, hmin⟩ := G.exists_min_image s hne
  have hinj : Set.InjOn s G := by
    intro v hv w hw h
    by_contra hvw
    have := hsep v hv w hw hvw
    rw [h, sub_self, abs_zero] at this; linarith
  rw [← card_image_of_injOn hinj]
  have := card_le_of_sep (a := s v₀) hc (G.image s) (s v₀ + ℓ) (by linarith) ?_ ?_
  · rwa [show s v₀ + ℓ - s v₀ = ℓ by ring] at this
  · intro x hx
    obtain ⟨w, hw, rfl⟩ := mem_image.1 hx
    refine ⟨hmin w hw, ?_⟩
    rcases (hmin w hw).lt_or_eq with h | h
    · linarith [hside v₀ hv₀ w hw h]
    · rw [← h]; linarith
  · intro x hx y hy hxy
    obtain ⟨v, hv, rfl⟩ := mem_image.1 hx
    obtain ⟨w, hw, rfl⟩ := mem_image.1 hy
    exact hsep v hv w hw (fun h => hxy (h ▸ rfl))

/-! ## Configurations of points with outward normals -/

/-- A finite set `V` with unit outward normals: `1`-separated, strict chord inequalities. -/
structure NormalConfig (V : Finset Pt) (nrm : Pt → Pt) : Prop where
  unit : ∀ v ∈ V, ‖nrm v‖ = 1
  sep : ∀ v ∈ V, ∀ w ∈ V, v ≠ w → 1 ≤ dist v w
  chord : ∀ v ∈ V, ∀ w ∈ V, v ≠ w → inner ℝ (w - v) (nrm v) < 0

variable {V : Finset Pt} {nrm : Pt → Pt}

/-- Distinct points with normals in a common open half-plane have non-parallel normals. -/
theorem NormalConfig.det2_ne (hV : NormalConfig V nrm) {v w g : Pt} {c : ℝ} (hc : 0 < c)
    (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w) (hvg : c ≤ inner ℝ (nrm v) g)
    (hwg : c ≤ inner ℝ (nrm w) g) : det2 (nrm v) (nrm w) ≠ 0 := by
  intro h0
  rcases eq_or_eq_neg_of_det2_eq_zero (hV.unit v hv) (hV.unit w hw) h0 with h | h
  · have h1 := hV.chord v hv w hw hvw
    have h2 := hV.chord w hw v hv (Ne.symm hvw)
    rw [h] at h1
    have : inner ℝ (v - w) (nrm w) = - inner ℝ (w - v) (nrm w) := by
      rw [← inner_neg_left, neg_sub]
    linarith
  · rw [h, inner_neg_left] at hvg
    linarith

/-- Oriented separation along `g^⊥`. -/
theorem NormalConfig.sep_det2 (hV : NormalConfig V nrm) {v w g : Pt} {c : ℝ} (hc : 0 ≤ c)
    (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w) (hvg : c ≤ inner ℝ (nrm v) g)
    (hwg : c ≤ inner ℝ (nrm w) g) (hdet : 0 < det2 (nrm v) (nrm w)) :
    c * dist w v ≤ det2 g (w - v) := by
  have h1 := hV.chord v hv w hw hvw
  have h2 := hV.chord w hw v hv (Ne.symm hvw)
  have h2' : 0 ≤ inner ℝ (w - v) (nrm w) := by
    have : inner ℝ (v - w) (nrm w) = - inner ℝ (w - v) (nrm w) := by
      rw [← inner_neg_left, neg_sub]
    linarith
  have := wedge_sep (hV.unit v hv) (hV.unit w hw) hc hvg hwg hdet h1.le h2'
  rwa [← dist_eq_norm] at this

/-- Unoriented separation along `g^⊥`. -/
theorem NormalConfig.sep_abs (hV : NormalConfig V nrm) {v w g : Pt} {c : ℝ} (hc : 0 < c)
    (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w) (hvg : c ≤ inner ℝ (nrm v) g)
    (hwg : c ≤ inner ℝ (nrm w) g) : c * dist w v ≤ |det2 g (w - v)| := by
  rcases lt_or_gt_of_ne (hV.det2_ne hc hv hw hvw hvg hwg) with h | h
  · have hd : 0 < det2 (nrm w) (nrm v) := by rw [det2_swap]; linarith
    have := hV.sep_det2 hc.le hw hv (Ne.symm hvw) hwg hvg hd
    have e : det2 g (v - w) = - det2 g (w - v) := by rw [det2_sub_right, det2_sub_right]; ring
    rw [e, dist_comm] at this
    exact this.trans (neg_le_abs _)
  · exact (hV.sep_det2 hc.le hv hw hvw hvg hwg h).trans (le_abs_self _)

/-- The points whose normals lie in the cap of a unit edge `pq` number at most `N`
(`N > 2/|n_p + n_q|`). -/
theorem NormalConfig.card_cap_le (hV : NormalConfig V nrm) {p q : Pt} (hp : p ∈ V) (hq : q ∈ V)
    (hpq : dist p q = 1) (hdet : 0 < det2 (nrm p) (nrm q)) {κ : ℝ} (hκ : 0 < κ)
    (hκp : κ ≤ ‖nrm p + nrm q‖) {N : ℕ} (hN : 2 / κ < N) :
    (V.filter (fun v => nrm v ∈ cap (nrm p) (nrm q))).card ≤ N := by
  set a := nrm p with ha_def
  set b := nrm q with hb_def
  have ha : ‖a‖ = 1 := hV.unit p hp
  have hb : ‖b‖ = 1 := hV.unit q hq
  set g := a + b with hg_def
  set c := 1 + inner ℝ a b with hc_def
  have hg2 : ‖g‖ ^ 2 = 2 * c := by rw [hg_def, norm_add_sq_real, ha, hb]; ring
  have hgpos : 0 < ‖g‖ := lt_of_lt_of_le hκ hκp
  have hc : 0 < c := by nlinarith
  set C := V.filter (fun v => nrm v ∈ cap a b) with hC_def
  have hCV : ∀ v ∈ C, v ∈ V := fun v hv => (mem_filter.1 hv).1
  have hCg : ∀ v ∈ C, c ≤ inner ℝ (nrm v) g := fun v hv => (mem_filter.1 hv).2
  have hpC : p ∈ C := by
    refine mem_filter.2 ⟨hp, ?_⟩
    show 1 + inner ℝ a b ≤ inner ℝ a (a + b)
    rw [inner_add_right, real_inner_self_eq_norm_sq, ha]; norm_num
  have hqC : q ∈ C := by
    refine mem_filter.2 ⟨hq, ?_⟩
    show 1 + inner ℝ a b ≤ inner ℝ b (a + b)
    rw [inner_add_right, real_inner_self_eq_norm_sq, hb, real_inner_comm]; norm_num; linarith
  have hlo : ∀ v ∈ C, det2 g p ≤ det2 g v := by
    intro v hv
    by_cases hvp : v = p
    · rw [hvp]
    have hvV := hCV v hv
    have hd := (det2_nonneg_of_mem_cap ha hb (hV.unit v hvV) hdet (mem_filter.1 hv).2).1
    have hne := hV.det2_ne hc hp hvV (Ne.symm hvp) (hCg p hpC) (hCg v hv)
    have := hV.sep_det2 hc.le hp hvV (Ne.symm hvp) (hCg p hpC) (hCg v hv)
      (lt_of_le_of_ne hd (Ne.symm hne))
    rw [det2_sub_right] at this
    have : 0 ≤ c * dist v p := by positivity
    linarith
  have hhi : ∀ v ∈ C, det2 g v ≤ det2 g q := by
    intro v hv
    by_cases hvq : v = q
    · rw [hvq]
    have hvV := hCV v hv
    have hd := (det2_nonneg_of_mem_cap ha hb (hV.unit v hvV) hdet (mem_filter.1 hv).2).2
    have hne := hV.det2_ne hc hvV hq hvq (hCg v hv) (hCg q hqC)
    have := hV.sep_det2 hc.le hvV hq hvq (hCg v hv) (hCg q hqC) (lt_of_le_of_ne hd (Ne.symm hne))
    rw [det2_sub_right] at this
    have : 0 ≤ c * dist q v := by positivity
    linarith
  have hext : det2 g q - det2 g p ≤ ‖g‖ := by
    rw [← det2_sub_right]
    have := abs_det2_le g (q - p)
    rw [← dist_eq_norm, dist_comm, hpq, one_mul] at this
    exact (le_abs_self _).trans this
  have hsep : ∀ v ∈ C, ∀ w ∈ C, v ≠ w → c ≤ |det2 g v - det2 g w| := by
    intro v hv w hw hvw
    have := hV.sep_abs hc (hCV v hv) (hCV w hw) hvw (hCg v hv) (hCg w hw)
    rw [det2_sub_right, abs_sub_comm] at this
    have h1 := hV.sep w (hCV w hw) v (hCV v hv) (Ne.symm hvw)
    nlinarith
  have hinj : Set.InjOn (fun v => det2 g v) C := by
    intro v hv w hw h
    by_contra hvw
    have := hsep v hv w hw hvw
    simp only at h
    rw [h, sub_self, abs_zero] at this; linarith
  have hcard := card_le_of_sep (a := det2 g p) hc (C.image (fun v => det2 g v)) (det2 g q)
    (by linarith [hlo q hqC]) (by
      intro x hx
      obtain ⟨w, hw, rfl⟩ := mem_image.1 hx
      exact ⟨hlo w hw, hhi w hw⟩) (by
      intro x hx y hy hxy
      obtain ⟨v, hv, rfl⟩ := mem_image.1 hx
      obtain ⟨w, hw, rfl⟩ := mem_image.1 hy
      exact hsep v hv w hw (fun h => hxy (h ▸ rfl)))
  rw [card_image_of_injOn hinj] at hcard
  have h1 : (det2 g q - det2 g p) / c ≤ 2 / κ := by
    rw [div_le_div_iff₀ hc hκ]
    have : ‖g‖ * κ ≤ 2 * c := by rw [← hg2]; nlinarith
    nlinarith
  have h2 : (C.card : ℝ) < N + 1 := by linarith
  exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast h2)

/-- **Edge count** (KK / DD): unit edges with normals at angle `> β₀` and `|n_p + n_q| ≥ κ`,
degree `≤ D`, satisfy `#E · β₀ ≤ 2π·D·N` for any `N > 2/κ`. -/
theorem NormalConfig.card_mul_le_of_edges (hV : NormalConfig V nrm) {E : Finset (Sym2 Pt)}
    {β₀ κ : ℝ} {D N : ℕ}
    (hE : ∀ p q, s(p, q) ∈ E → p ∈ V ∧ q ∈ V ∧ dist p q = 1 ∧ β₀ < ang (nrm p) (nrm q) ∧
      κ ≤ ‖nrm p + nrm q‖)
    (hdeg : ∀ p, (E.filter (fun e => p ∈ e)).card ≤ D) (hβ₀ : 0 ≤ β₀) (hκ : 0 < κ)
    (hN : 2 / κ < N) : (E.card : ℝ) * β₀ ≤ 2 * π * (D * N) := by
  set P := (V ×ˢ V).filter
    (fun pq : Pt × Pt => s(pq.1, pq.2) ∈ E ∧ 0 < det2 (nrm pq.1) (nrm pq.2)) with hP_def
  have hPmem : ∀ pq ∈ P, pq.1 ∈ V ∧ pq.2 ∈ V ∧ s(pq.1, pq.2) ∈ E ∧
      0 < det2 (nrm pq.1) (nrm pq.2) := by
    intro pq h
    simp only [P, mem_filter, mem_product] at h
    exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩
  -- every edge has exactly one positive orientation
  have hEP : E ⊆ P.image (fun pq => s(pq.1, pq.2)) := by
    intro e he
    induction e using Sym2.ind with
    | _ p q =>
    obtain ⟨hp, hq, -, hang, hκp⟩ := hE p q he
    have hne : det2 (nrm p) (nrm q) ≠ 0 := by
      intro h0
      rcases eq_or_eq_neg_of_det2_eq_zero (hV.unit p hp) (hV.unit q hq) h0 with h | h
      · have hq0 : nrm q ≠ 0 := by
          intro h'; have := hV.unit q hq; rw [h', norm_zero] at this; norm_num at this
        rw [h, ang, InnerProductGeometry.angle_self hq0] at hang; linarith
      · rw [h, neg_add_cancel, norm_zero] at hκp; linarith
    rw [mem_image]
    rcases lt_or_gt_of_ne hne with h | h
    · refine ⟨(q, p), ?_, Sym2.eq_swap⟩
      simp only [P, mem_filter, mem_product]
      exact ⟨⟨hq, hp⟩, by rw [Sym2.eq_swap]; exact he, by rw [det2_swap]; linarith⟩
    · exact ⟨(p, q), by simp only [P, mem_filter, mem_product]; exact ⟨⟨hp, hq⟩, he, h⟩, rfl⟩
  have hcardE : (E.card : ℝ) ≤ P.card := by
    exact_mod_cast (card_le_card hEP).trans card_image_le
  -- each oriented edge owns a cap of measure `> β₀`
  have hα : ∀ pq ∈ P, β₀ ≤ dirMeasure (cap (nrm pq.1) (nrm pq.2)) := by
    intro pq hpq
    obtain ⟨hp, hq, he, -⟩ := hPmem pq hpq
    obtain ⟨-, -, -, hang, hκp⟩ := hE pq.1 pq.2 he
    have ha := hV.unit pq.1 hp
    have hb := hV.unit pq.2 hq
    have h2 : ‖nrm pq.1 + nrm pq.2‖ ^ 2 = 2 + 2 * inner ℝ (nrm pq.1) (nrm pq.2) := by
      rw [norm_add_sq_real, ha, hb]; ring
    have : 0 < 1 + inner ℝ (nrm pq.1) (nrm pq.2) := by nlinarith
    exact hang.le.trans (ang_le_dirMeasure_cap ha hb this)
  -- multiplicity
  have hM : ∀ θ : ℝ, (P.filter (fun pq => dirVec θ ∈ cap (nrm pq.1) (nrm pq.2))).card ≤
      D * N := by
    intro θ
    have hm : ‖dirVec θ‖ = 1 := norm_dirVec θ
    set m := dirVec θ
    set F := P.filter (fun pq => m ∈ cap (nrm pq.1) (nrm pq.2)) with hF_def
    have hfib : ∀ t ∈ F.image Prod.fst, (F.filter (fun pq => pq.1 = t)).card ≤ D := by
      intro t _
      refine le_trans ?_ (hdeg t)
      refine card_le_card_of_injOn (fun pq => s(pq.1, pq.2)) (fun pq hpq => ?_) ?_
      · obtain ⟨hpqF, rfl⟩ := mem_filter.1 hpq
        refine mem_filter.2 ⟨(hPmem pq (mem_filter.1 hpqF).1).2.2.1, Sym2.mem_mk_left _ _⟩
      · intro x hx y hy hxy
        have hx1 := (mem_filter.1 hx).2
        have hy1 := (mem_filter.1 hy).2
        simp only at hxy
        rcases Sym2.eq_iff.1 hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Prod.ext h1 h2
        · exact Prod.ext (by rw [hx1, hy1]) (by rw [← h1, hx1, h2, hy1])
    have hT : (F.image Prod.fst).card ≤ N := by
      rcases F.eq_empty_or_nonempty with hF | hF
      · rw [hF]; simp
      obtain ⟨⟨p0, q0⟩, h0F, hmin⟩ := F.exists_min_image (fun pq => inner ℝ (nrm pq.1) m) hF
      obtain ⟨h0P, h0m⟩ := mem_filter.1 h0F
      obtain ⟨hp0, hq0, he0, hdet0⟩ := hPmem _ h0P
      obtain ⟨-, -, hd0, -, hκ0⟩ := hE p0 q0 he0
      refine le_trans (card_le_card ?_) (hV.card_cap_le hp0 hq0 hd0 hdet0 hκ hκ0 hN)
      intro t ht
      obtain ⟨⟨t', h⟩, htF, rfl⟩ := mem_image.1 ht
      obtain ⟨htP, htm⟩ := mem_filter.1 htF
      obtain ⟨htV, hhV, -, hdett⟩ := hPmem _ htP
      simp only at htV hhV hdett htm ⊢
      refine mem_filter.2 ⟨htV, ?_⟩
      have hu := hV.unit t' htV
      have hw := hV.unit p0 hp0
      have hh1 := hV.unit q0 hq0
      obtain ⟨ht1, -⟩ := det2_nonneg_of_mem_cap hu (hV.unit h hhV) hm hdett htm
      obtain ⟨h01, h02⟩ := det2_nonneg_of_mem_cap hw hh1 hm hdet0 h0m
      have hle : inner ℝ (nrm p0) m ≤ inner ℝ (nrm t') m := hmin (t', h) htF
      have hwu : 0 ≤ det2 (nrm p0) (nrm t') := det2_tail hu hw hm ht1 h01 hle
      have huh : 0 ≤ det2 (nrm t') (nrm q0) := by
        rcases h01.lt_or_eq with hpos | hzero
        · have hpl := plucker (nrm p0) (nrm t') m (nrm q0)
          have : 0 ≤ det2 (nrm p0) m * det2 (nrm t') (nrm q0) := by
            rw [hpl]; exact add_nonneg (mul_nonneg hwu h02) (mul_nonneg hdet0.le ht1)
          exact (mul_nonneg_iff_of_pos_left hpos).1 this
        · rcases eq_or_eq_neg_of_det2_eq_zero hw hm hzero.symm with hwm | hwm
          · have h1 : 1 ≤ inner ℝ (nrm t') m := by
              rw [hwm, real_inner_self_eq_norm_sq, hm] at hle; linarith
            rw [eq_of_one_le_inner hu hm h1, ← hwm]; exact hdet0.le
          · exfalso
            have : det2 (nrm p0) (nrm q0) = - det2 m (nrm q0) := by
              rw [hwm]; simp only [det2, PiLp.neg_apply]; ring
            linarith
      exact mem_cap_of_det2 hw hh1 hu hdet0 hwu huh
    calc F.card ≤ D * (F.image Prod.fst).card := card_le_mul_card_image F D hfib
      _ ≤ D * N := Nat.mul_le_mul_left D hT
  have h := card_mul_le_of_dirMeasure P (fun pq => cap (nrm pq.1) (nrm pq.2))
    (fun _ _ => isClosed_cap _ _) (D * N) hM hα
  push_cast at h
  calc (E.card : ℝ) * β₀ ≤ P.card * β₀ := mul_le_mul_of_nonneg_right hcardE hβ₀
    _ ≤ 2 * π * (D * N) := h

/-- The discrete walk: a window-neighbour `y` of `v` on the side away from `x` is within `412`
of `v`. -/
theorem walk_close {v x y m nv ny : Pt} {R : ℝ} (hR : 10 ^ 4 ≤ R) (hm : ‖m‖ = 1)
    (hnv : ‖nv - m‖ ≤ 1 / 800) (hny : ‖ny - m‖ ≤ 1 / 800) (hxv : dist v x ≤ R)
    (hR1 : R - 1 ≤ dist v x) (hs : dist v x / 201 ≤ |det2 nv (x - v)|) (hyx : dist y x ≤ R)
    (hcv : inner ℝ (y - v) nv < 0) (hcy : 0 < inner ℝ (y - v) ny)
    (hsep : 99 / 100 * ‖y - v‖ ≤ |det2 m (y - v)|)
    (hside : det2 m (y - v) * det2 m (x - v) < 0) : ‖y - v‖ ≤ 412 := by
  set d := y - v with hd_def
  set e := x - v with he_def
  set ρ := dist v x with hρ_def
  set nd := ‖d‖ with hnd_def
  have hρ0 : 9999 ≤ ρ := by linarith
  have he : ‖e‖ = ρ := by rw [he_def, ← dist_eq_norm, dist_comm]
  have hnd0 : 0 ≤ nd := norm_nonneg _
  -- `d` is nearly orthogonal to `m`
  have hdm : |inner ℝ d m| ≤ nd / 800 := by
    have a1 : inner ℝ d m = inner ℝ d nv + inner ℝ d (m - nv) := by rw [inner_sub_right]; ring
    have a2 : inner ℝ d m = inner ℝ d ny + inner ℝ d (m - ny) := by rw [inner_sub_right]; ring
    have b1 := abs_real_inner_le_norm d (m - nv)
    have b2 := abs_real_inner_le_norm d (m - ny)
    rw [norm_sub_rev m nv] at b1
    rw [norm_sub_rev m ny] at b2
    have c1 : nd * ‖nv - m‖ ≤ nd * (1 / 800) := mul_le_mul_of_nonneg_left hnv hnd0
    have c2 : nd * ‖ny - m‖ ≤ nd * (1 / 800) := mul_le_mul_of_nonneg_left hny hnd0
    rw [abs_le] at b1 b2 ⊢
    constructor <;> linarith
  -- `x − v` is far from parallel to `m`
  have hme : ρ * (1 / 201 - 1 / 800) ≤ |det2 m e| := by
    have e1 : det2 m e = det2 nv e - det2 (nv - m) e := by rw [det2_sub_left]; ring
    have e2 := abs_det2_le (nv - m) e
    rw [he] at e2
    have e3 : ρ * ‖nv - m‖ ≤ ρ * (1 / 800) := mul_le_mul_of_nonneg_left hnv (by linarith)
    have e4 := abs_sub_abs_le_abs_sub (det2 nv e) (det2 (nv - m) e)
    rw [← e1] at e4
    linarith
  -- the frame decomposition of `d · e`
  have hframe := inner_frame hm d e
  have hem : |inner ℝ e m| ≤ ρ := by
    have := abs_real_inner_le_norm e m; rw [he, hm, mul_one] at this; exact this
  have t1 : inner ℝ d m * inner ℝ e m ≤ nd / 800 * ρ := by
    have := abs_mul (inner ℝ d m) (inner ℝ e m)
    have h2 : |inner ℝ d m| * |inner ℝ e m| ≤ nd / 800 * ρ :=
      mul_le_mul hdm hem (abs_nonneg _) (by positivity)
    linarith [le_abs_self (inner ℝ d m * inner ℝ e m)]
  have t2 : det2 m d * det2 m e ≤ -(99 / 100 * nd * (ρ * (1 / 201 - 1 / 800))) := by
    have h1 : |det2 m d * det2 m e| = -(det2 m d * det2 m e) := abs_of_neg hside
    rw [abs_mul] at h1
    have h2 : 99 / 100 * nd * (ρ * (1 / 201 - 1 / 800)) ≤ |det2 m d| * |det2 m e| :=
      mul_le_mul hsep hme (by nlinarith) (abs_nonneg _)
    linarith
  have hde : inner ℝ d e ≤ -(ρ * nd / 411) := by
    rw [hframe]; nlinarith
  -- `y` would leave the disc `D(x, R)`
  have hyx2 : ‖d - e‖ ^ 2 ≤ R ^ 2 := by
    have : d - e = y - x := by rw [hd_def, he_def]; abel
    rw [this, ← dist_eq_norm]; exact pow_le_pow_left₀ dist_nonneg hyx 2
  have hexp : ‖d - e‖ ^ 2 = nd ^ 2 - 2 * inner ℝ d e + ρ ^ 2 := by
    rw [norm_sub_sq_real, he]
  have hkey : 2 * ρ * nd / 411 ≤ 2 * ρ + 1 := by nlinarith
  by_contra hcon
  push Not at hcon
  nlinarith

/-- The side of the walk is well defined: `det(m, x − v) ≠ 0`. -/
theorem walk_side_ne {v x m nv : Pt} {R : ℝ} (hR : 10 ^ 4 ≤ R)
    (hnv : ‖nv - m‖ ≤ 1 / 800) (hR1 : R - 1 ≤ dist v x)
    (hs : dist v x / 201 ≤ |det2 nv (x - v)|) : det2 m (x - v) ≠ 0 := by
  have hρ : 0 < dist v x := by linarith
  have e1 : det2 m (x - v) = det2 nv (x - v) - det2 (nv - m) (x - v) := by
    rw [det2_sub_left]; ring
  have e2 := abs_det2_le (nv - m) (x - v)
  rw [← dist_eq_norm, dist_comm] at e2
  have e3 : dist v x * ‖nv - m‖ ≤ dist v x * (1 / 800) := mul_le_mul_of_nonneg_left hnv hρ.le
  intro h0
  rw [h0] at e1
  have : |det2 nv (x - v)| = |det2 (nv - m) (x - v)| := by rw [show det2 nv (x - v) =
    det2 (nv - m) (x - v) by linarith]
  linarith

/-- **Walk count** ((c2)): points `v ∈ W ⊆ V` at depth `≤ 1` in a disc `D(x_v, R) ⊇ V` with
`|det(n_v, x_v − v)| ≥ |x_v − v|/201` satisfy `#W/400 ≤ 2π·834`. -/
theorem NormalConfig.card_walk_mul_le (hV : NormalConfig V nrm) {W : Finset Pt} (hW : W ⊆ V)
    {R : ℝ} (hR : 10 ^ 4 ≤ R)
    (hx : ∀ v ∈ W, ∃ x : Pt, (∀ y ∈ V, dist y x ≤ R) ∧ R - 1 ≤ dist v x ∧
      dist v x / 201 ≤ |det2 (nrm v) (x - v)|) :
    (W.card : ℝ) * (1 / 400) ≤ 2 * π * 834 := by
  have hmeas : ∀ v ∈ W, 1 / 400 ≤ dirMeasure (window (nrm v) (1 / 800)) := fun v hv => by
    have := two_mul_le_dirMeasure_window (hV.unit v (hW hv)) (ε := 1 / 800) (by norm_num)
      (by linarith [Real.pi_gt_three])
    linarith
  have hM : ∀ θ : ℝ, (W.filter (fun v => dirVec θ ∈ window (nrm v) (1 / 800))).card ≤ 834 := by
    intro θ
    have hm : ‖dirVec θ‖ = 1 := norm_dirVec θ
    set m := dirVec θ
    set A := W.filter (fun v => m ∈ window (nrm v) (1 / 800)) with hA_def
    have hAV : ∀ v ∈ A, v ∈ V := fun v hv => hW (mem_filter.1 hv).1
    have hAw : ∀ v ∈ A, ‖nrm v - m‖ ≤ 1 / 800 := fun v hv => by
      have := (mem_filter.1 hv).2; rw [norm_sub_rev]; exact this
    have hAc : ∀ v ∈ A, 99 / 100 ≤ inner ℝ (nrm v) m := by
      intro v hv
      have h1 := hAw v hv
      have h2 := norm_sub_sq_real (nrm v) m
      rw [hV.unit v (hAV v hv), hm] at h2
      have : ‖nrm v - m‖ ^ 2 ≤ (1 / 800) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith
    have hsepA : ∀ v ∈ A, ∀ w ∈ A, v ≠ w → 99 / 100 * dist w v ≤ |det2 m (w - v)| :=
      fun v hv w hw hvw => hV.sep_abs (by norm_num) (hAV v hv) (hAV w hw) hvw (hAc v hv) (hAc w hw)
    -- the walk: each `v ∈ A` has a short side
    have hwalk : ∀ v ∈ A, ∀ y ∈ A, ∀ x : Pt, (∀ y ∈ V, dist y x ≤ R) → R - 1 ≤ dist v x →
        dist v x / 201 ≤ |det2 (nrm v) (x - v)| →
        det2 m (y - v) * det2 m (x - v) < 0 → dist y v ≤ 412 := by
      intro v hv y hy x hxV hR1 hs hside
      have hyv : y ≠ v := by
        rintro rfl; rw [sub_self] at hside; simp [det2] at hside
      rw [dist_eq_norm]
      refine walk_close hR hm (hAw v hv) (hAw y hy) (hxV v (hAV v hv)) hR1 hs (hxV y (hAV y hy))
        (hV.chord v (hAV v hv) y (hAV y hy) hyv.symm) ?_ ?_ hside
      · have := hV.chord y (hAV y hy) v (hAV v hv) hyv
        have e : inner ℝ (v - y) (nrm y) = - inner ℝ (y - v) (nrm y) := by
          rw [← inner_neg_left, neg_sub]
        linarith
      · have := hsepA v hv y hy hyv.symm
        rwa [dist_eq_norm] at this
    set Gp := A.filter (fun v => ∀ y ∈ A, 0 < det2 m (y - v) → dist y v ≤ 412)
    set Gm := A.filter (fun v => ∀ y ∈ A, det2 m (y - v) < 0 → dist y v ≤ 412)
    have hcover : A ⊆ Gp ∪ Gm := by
      intro v hv
      obtain ⟨x, hxV, hR1, hs⟩ := hx v (mem_filter.1 hv).1
      have hne := walk_side_ne hR (hAw v hv) hR1 hs
      rcases lt_or_gt_of_ne hne with h | h
      · refine mem_union_left _ (mem_filter.2 ⟨hv, fun y hy hpos => ?_⟩)
        exact hwalk v hv y hy x hxV hR1 hs (mul_neg_of_pos_of_neg hpos h)
      · refine mem_union_right _ (mem_filter.2 ⟨hv, fun y hy hneg => ?_⟩)
        exact hwalk v hv y hy x hxV hR1 hs (mul_neg_of_neg_of_pos hneg h)
    have hdet_le : ∀ v w : Pt, |det2 m (w - v)| ≤ dist w v := by
      intro v w
      have := abs_det2_le m (w - v); rwa [hm, mul_one, ← dist_eq_norm] at this
    have hGp : (Gp.card : ℝ) ≤ 412 / (99 / 100) + 1 := by
      refine card_le_of_oneSided (fun y => det2 m y) (by norm_num) (by norm_num) ?_ ?_
      · intro v hv w hw hvw
        have hv' := (mem_filter.1 hv).1
        have hw' := (mem_filter.1 hw).1
        have h1 := hsepA v hv' w hw' hvw
        have h2 := hV.sep w (hAV w hw') v (hAV v hv') (Ne.symm hvw)
        rw [det2_sub_right, abs_sub_comm] at h1
        nlinarith
      · intro v hv w hw hlt
        have hpos : 0 < det2 m (w - v) := by rw [det2_sub_right]; linarith
        have h1 := (mem_filter.1 hv).2 w (mem_filter.1 hw).1 hpos
        have h2 := hdet_le v w
        rw [det2_sub_right] at h2
        linarith [le_abs_self (det2 m w - det2 m v)]
    have hGm : (Gm.card : ℝ) ≤ 412 / (99 / 100) + 1 := by
      refine card_le_of_oneSided (fun y => - det2 m y) (by norm_num) (by norm_num) ?_ ?_
      · intro v hv w hw hvw
        have hv' := (mem_filter.1 hv).1
        have hw' := (mem_filter.1 hw).1
        have h1 := hsepA v hv' w hw' hvw
        have h2 := hV.sep w (hAV w hw') v (hAV v hv') (Ne.symm hvw)
        rw [det2_sub_right] at h1
        have : |-det2 m v - -det2 m w| = |det2 m w - det2 m v| := by congr 1; ring
        rw [this]
        nlinarith
      · intro v hv w hw hlt
        have hneg : det2 m (w - v) < 0 := by rw [det2_sub_right]; linarith
        have h1 := (mem_filter.1 hv).2 w (mem_filter.1 hw).1 hneg
        have h2 := hdet_le v w
        rw [det2_sub_right] at h2
        linarith [neg_abs_le (det2 m w - det2 m v)]
    have hA : (A.card : ℝ) ≤ Gp.card + Gm.card := by
      exact_mod_cast (card_le_card hcover).trans (card_union_le _ _)
    have : (A.card : ℝ) < 835 := by linarith
    exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
  have := card_mul_le_of_dirMeasure W (fun v => window (nrm v) (1 / 800))
    (fun _ _ => isClosed_window _ _) 834 hM hmeas
  push_cast at this
  exact this

end

end Curve

end Erdos132Main
