import Erdos132.E132Main43Frame

/-!
# Erdős Problem 132, `4/3` theorem — receivers and owner uniqueness (§1.4)

Paper: `angle_R6.md` §1.4.  Every heavy good point `y` passes its excess `v(y) − 8` to its
receivers `Low X y` (neighbours at least `2/3` deeper than `y`).

* **Receivers** (`low_receiver`): a receiver `a` is interior to `K` (so `a ∈ R`), has height
  `≤ −2/3` (`Low_Z`), and every `S`-neighbour `q` of `a` has height `≥ h − 2/49`; so `q − a`
  and `y − a` are unit vectors within `60°` of `n`, and at most two such are `≥ 60°` apart
  (`card_cone_le_two`): `m_a ≤ 1`, `v(a) ≤ 7`.
* **Owner uniqueness** (`low_disjoint`): fans and caps never coexist (Lemma Pin, `t` global);
  two caps sharing `b` would both sit within `1/20` above `b` (`frame_normal_close`); two fans
  `y ≠ y′` sharing `a` sit at `≈ ±30°` above `a`, so `y′` is `y`'s neighbour in a `±90°` slot
  (`fan_common_low_slot`), which is not in `S`, so `y` is HF2 — and symmetrically `y′`; then
  `y`'s D at `σ·30°` and `y′`'s D at `−σ·30°` coincide in a point `z ∈ D` with four
  `δ`-neighbours, contradicting `degδ_le_three_of_D`.
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-! ## Receivers -/

/-- A receiver has at most one `S`-neighbour.

TODO: none — proved.
What's missing (paper §1.4, "fan receiver"): `Z a ≤ −2/3` (`Low_Z`).  An `S`-neighbour `q` of
`a` has `dist q y ≤ 2`, `q ∉ int K` (`Sset_not_interior`), so `Z q ≥ h − 2/49`
(`frame_outside`, `|Xq| ≤ 2`) and `⟨q − a, n⟩ ≥ 2/3 − 2/49 > 1/2`; also
`⟨y − a, n⟩ = −Z a ≥ 2/3 > 1/2` and `y ∉ S` (`y ∈ R`), `y ∈ X`.  Apply `card_cone_le_two` to
`insert y (S-neighbours of a)` (unit distances `dist_of_mem_nbδ`, separation `one_le_dist`):
`1 + m_a ≤ 2`.
Acceptance: no `sorry`.
Depends on: `Low_Z`, `frame_outside`, `Sset_not_interior`, `card_cone_le_two`,
`dist_of_mem_nbδ`, `one_le_dist`, `Low_subset`. Difficulty M. -/
theorem mS_le_one_of_Low (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) (hy : y ∈ Rset X)
    {a : Pt} (ha : a ∈ Low X y) : mS X a ≤ 1 := by
  have hZa := Low_Z hX hF ha
  have hay : a ∈ nbδ X y := Low_subset X y ha
  have hdya : dist a y = 1 := dist_of_mem_nbδ hX hay
  have hyX : y ∈ X := (mem_sdiff.1 hy).1
  have hyS : y ∉ Sset X := (mem_sdiff.1 hy).2
  have hdep := hF.depth_pos
  set Q := (nbδ X a).filter (· ∈ Sset X) with hQ
  have hmS : mS X a = Q.card := rfl
  have hyQ : y ∉ Q := fun h => hyS (mem_filter.1 h).2
  have hcard := card_cone_le_two (a := a) hF.unit (insert y Q) ?_ ?_ ?_
  · rw [card_insert_of_notMem hyQ] at hcard
    omega
  · intro q hq
    rcases mem_insert.1 hq with rfl | hq
    · rw [dist_comm]; exact hdya
    · exact dist_of_mem_nbδ hX (mem_filter.1 hq).1
  · intro q hq q' hq' hne
    have hmem : ∀ r ∈ insert y Q, r ∈ X := by
      intro r hr
      rcases mem_insert.1 hr with rfl | hr
      · exact hyX
      · exact (mem_nbδ.1 (mem_filter.1 hr).1).1
    exact one_le_dist hX.minDist_eq (hmem q hq) (hmem q' hq') hne
  · intro q hq
    rcases mem_insert.1 hq with rfl | hq
    · have e : inner ℝ (q - a) n = -inner ℝ (a - q) n := by
        rw [← inner_neg_left, neg_sub]
      rw [e]; linarith
    · obtain ⟨hqa, hqS⟩ := mem_filter.1 hq
      have hdqa := dist_of_mem_nbδ hX hqa
      have hdqy : dist q y ≤ 2 := by
        have := dist_triangle q a y
        linarith
      have hout := frame_outside hX hF (by linarith) (Sset_not_interior hX hqS)
      have hper : |inner ℝ (q - y) (perp n)| ≤ 2 := by
        have := abs_real_inner_le_norm (q - y) (perp n)
        rw [norm_perp, hF.unit, mul_one, ← dist_eq_norm] at this
        linarith
      have e : inner ℝ (q - a) n = inner ℝ (q - y) n - inner ℝ (a - y) n := by
        rw [← inner_sub_left]; congr 1; abel
      rw [e]
      unfold ε43 at hout
      nlinarith [abs_nonneg (inner ℝ (q - y) (perp n))]

/-- **Receivers are in `R` and have weight `≤ 7`.**

TODO: none — proved from the statements.
Acceptance: no `sorry` (inherits).
Depends on: `Low_interior`, `Sset_not_interior`, `degδ_le_six`, `mS_le_one_of_Low`. -/
theorem low_receiver (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) (hy : y ∈ Rset X)
    {a : Pt} (ha : a ∈ Low X y) : a ∈ Rset X ∧ vR X a ≤ 7 := by
  have haX : a ∈ X := (mem_nbδ.1 (Low_subset X y ha)).1
  have hint := Low_interior ha
  have haS : a ∉ Sset X := fun h => Sset_not_interior hX h hint
  refine ⟨mem_sdiff.2 ⟨haX, haS⟩, ?_⟩
  unfold vR
  have := degδ_le_six X a
  have := mS_le_one_of_Low hX hF hy ha
  omega

/-! ## Private frame helpers -/

private theorem ch_np (n : Pt) : inner ℝ n (perp n) = 0 := by
  rw [← det2_eq_inner_perp]; unfold det2; ring

private theorem ch_pn (n : Pt) : inner ℝ (perp n) n = 0 := by
  rw [real_inner_comm]; exact ch_np n

private theorem ch_sq {n : Pt} (hn : ‖n‖ = 1) (v : Pt) :
    ‖v‖ ^ 2 = inner ℝ v n ^ 2 + inner ℝ v (perp n) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, n1_inner_frame hn v v]; ring

private theorem ch_dirF_n {n : Pt} (hn : ‖n‖ = 1) (ψ : ℝ) :
    inner ℝ (dirF n ψ) n = Real.cos ψ := by
  unfold dirF
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, ch_pn,
    real_inner_self_eq_norm_sq, hn]; ring

private theorem ch_dirF_p {n : Pt} (hn : ‖n‖ = 1) (ψ : ℝ) :
    inner ℝ (dirF n ψ) (perp n) = Real.sin ψ := by
  unfold dirF
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, ch_np,
    real_inner_self_eq_norm_sq, norm_perp, hn]; ring

private theorem ch_abs {u : Pt} (hu : ‖u‖ = 1) (v : Pt) : |inner ℝ v u| ≤ ‖v‖ := by
  have := abs_real_inner_le_norm v u
  rwa [hu, mul_one] at this

private theorem ch_dirF_sub (n n' : Pt) (ψ : ℝ) :
    ‖dirF n' ψ - dirF n ψ‖ ≤ 2 * ‖n' - n‖ := by
  have e : dirF n' ψ - dirF n ψ = Real.sin ψ • perp (n' - n) + Real.cos ψ • (n' - n) := by
    unfold dirF; rw [perp_sub, smul_sub, smul_sub]; abel
  rw [e]
  calc ‖Real.sin ψ • perp (n' - n) + Real.cos ψ • (n' - n)‖
      ≤ ‖Real.sin ψ • perp (n' - n)‖ + ‖Real.cos ψ • (n' - n)‖ := norm_add_le _ _
    _ = |Real.sin ψ| * ‖n' - n‖ + |Real.cos ψ| * ‖n' - n‖ := by
        rw [norm_smul, norm_smul, norm_perp, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 1 * ‖n' - n‖ + 1 * ‖n' - n‖ := by
        gcongr
        · exact Real.abs_sin_le_one ψ
        · exact Real.abs_cos_le_one ψ
    _ = 2 * ‖n' - n‖ := by ring

/-- Abscissa (w.r.t. `n`) of a point in a slot of a (possibly different) frame `n'`. -/
private theorem ch_slotX {y q n n' : Pt} (hn : ‖n‖ = 1) {ψ η : ℝ} (h : Slot y n' ψ η q) :
    |inner ℝ (q - y) (perp n) - Real.sin ψ| ≤ η + 2 * ‖n' - n‖ := by
  have hp : ‖perp n‖ = 1 := by rw [norm_perp, hn]
  have e : inner ℝ (q - y) (perp n) - Real.sin ψ =
      inner ℝ (q - y - dirF n' ψ) (perp n) + inner ℝ (dirF n' ψ - dirF n ψ) (perp n) := by
    rw [inner_sub_left (q - y), inner_sub_left (dirF n' ψ), ch_dirF_p hn]; ring
  rw [e]
  have h1 := ch_abs hp (q - y - dirF n' ψ)
  have h2 := ch_abs hp (dirF n' ψ - dirF n ψ)
  have h3 := ch_dirF_sub n n' ψ
  unfold Slot at h
  calc _ ≤ |inner ℝ (q - y - dirF n' ψ) (perp n)| + |inner ℝ (dirF n' ψ - dirF n ψ) (perp n)| :=
        abs_add_le _ _
    _ ≤ _ := by linarith

private theorem ch_sin2 {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : Real.sin (σ * (π / 2)) = σ := by
  rcases hσ with rfl | rfl <;> simp [neg_mul, Real.sin_neg]

private theorem ch_cos2 {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : Real.cos (σ * (π / 2)) = 0 := by
  rcases hσ with rfl | rfl <;> simp [neg_mul, Real.cos_neg]

private theorem ch_sin6 {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : Real.sin (σ * (π / 6)) = σ / 2 := by
  rcases hσ with rfl | rfl <;> norm_num [neg_mul, Real.sin_neg, Real.sin_pi_div_six]

/-- Hexagon identity: `dirF(σ·30°) = dirF(σ·90°) + dirF(−σ·30°)`. -/
private theorem ch_hex (n : Pt) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    dirF n (σ * (π / 6)) = dirF n (σ * (π / 2)) + dirF n (-(σ * (π / 6))) := by
  unfold dirF
  rw [Real.sin_neg, Real.cos_neg, ch_sin6 hσ, ch_sin2 hσ, ch_cos2 hσ]
  module

/-- The slot argument of owner uniqueness: if `y′ ∈ R` lies within `7/20` of `y`'s `σ′·90°`
direction, then `y′` is `y`'s slot neighbour `q` and `y` is of type HF2. -/
private theorem ch_fan_hf2 (hX : Normal X) {y y' n : Pt} (hy' : y' ∈ Rset X)
    (hs : FanSlots X y n) {σ' : ℝ} (hσ' : σ' = 1 ∨ σ' = -1)
    (h' : ‖y' - y - dirF n (σ' * (π / 2))‖ ≤ 7 / 20) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ Slot y n (σ * (π / 2)) (1 / 20) y' ∧
      ∃ z₁ ∈ nbδ X y, z₁ ∈ Dset X ∧ Slot y n (σ * (π / 6)) (1 / 20) z₁ ∧
      ∃ z₂ ∈ nbδ X y, z₂ ∈ Dset X ∧ Slot y n (-(σ * (π / 6))) (1 / 20) z₂ ∧
        dist z₁ z₂ = minDist X := by
  obtain ⟨σ, hσ, p, hp, q, hq, z₁, hz₁, hpS, -, hz₁D, hpsl, hqsl, hz₁sl, hrest⟩ := hs
  have hy'X : y' ∈ X := (mem_sdiff.1 hy').1
  have hy'S : y' ∉ Sset X := (mem_sdiff.1 hy').2
  have close : ∀ r ∈ nbδ X y, ‖r - y - dirF n (σ' * (π / 2))‖ ≤ 1 / 20 → r = y' := by
    intro r hr hrs
    by_contra hne
    have h1 := one_le_dist hX.minDist_eq (mem_nbδ.1 hr).1 hy'X hne
    have e : r - y' = (r - y - dirF n (σ' * (π / 2))) - (y' - y - dirF n (σ' * (π / 2))) := by
      abel
    rw [dist_eq_norm, e] at h1
    have := norm_sub_le (r - y - dirF n (σ' * (π / 2))) (y' - y - dirF n (σ' * (π / 2)))
    linarith
  have hcase : σ' = σ ∨ σ' = -σ := by
    rcases hσ with rfl | rfl <;> rcases hσ' with rfl | rfl <;> norm_num
  rcases hcase with rfl | rfl
  · have hqy := close q hq hqsl
    subst hqy
    rcases hrest with hqS | ⟨z₂, hz₂, hz₂D, hz₂sl, hd⟩
    · exact absurd hqS hy'S
    · exact ⟨_, hσ', hqsl, z₁, hz₁, hz₁D, hz₁sl, z₂, hz₂, hz₂D, hz₂sl, hd⟩
  · exfalso
    have hpy := close p hp (by unfold Slot at hpsl; rw [neg_mul]; exact hpsl)
    exact hy'S (hpy ▸ hpS)

private theorem ch_num_d {d e : ℝ} (hd0 : 0 ≤ d) (hdd : 1 - 121 / 2500 ≤ d ^ 2)
    (hd2 : d ≤ 123 / 100) (he : e ^ 2 ≤ 121 / 2500) : e ^ 2 + (d - 1) ^ 2 ≤ (7 / 20) ^ 2 := by
  have l1 : 97 / 100 ≤ d := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 l1) (sub_nonneg.2 hd2)]

/-- Numerics of `fan_common_low_slot` (worst case `≈ 0.2267 ≤ 7/20`). -/
private theorem ch_num {c c' x x' : ℝ} (hc : 4 / 5 ≤ c) (hc' : 4 / 5 - 1 / 50 ≤ c')
    (s1 : (1 : ℝ) ^ 2 = c ^ 2 + x ^ 2) (s2 : (1 : ℝ) ^ 2 = c' ^ 2 + x' ^ 2)
    (hsq : 1 ≤ (c' - c) ^ 2 + (x' - x) ^ 2) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ (c' - c) ^ 2 + (x' - x - σ) ^ 2 ≤ (7 / 20) ^ 2 := by
  have cle : c ≤ 1 := by nlinarith
  have c'le : c' ≤ 1 := by nlinarith
  have hcc : (c' - c) ^ 2 ≤ 121 / 2500 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ c' - c + 11 / 50)
      (by linarith : (0 : ℝ) ≤ 11 / 50 - (c' - c))]
  have hx1 : x ≤ 3 / 5 := by nlinarith
  have hx2 : -(3 / 5) ≤ x := by nlinarith
  have hx3 : x' ≤ 63 / 100 := by nlinarith
  have hx4 : -(63 / 100) ≤ x' := by nlinarith
  have hdd : 1 - 121 / 2500 ≤ (x' - x) ^ 2 := by linarith
  rcases le_total 0 (x' - x) with h0 | h0
  · refine ⟨1, Or.inl rfl, ?_⟩
    exact ch_num_d h0 hdd (by linarith) hcc
  · refine ⟨-1, Or.inr rfl, ?_⟩
    have := ch_num_d (d := -(x' - x)) (by linarith) (by rw [neg_sq]; exact hdd) (by linarith) hcc
    have e : (x' - x - -1) ^ 2 = (-(x' - x) - 1) ^ 2 := by ring
    rw [e]; exact this

/-! ## Owner uniqueness -/

/-- **Two fans sharing a receiver are horizontal neighbours**: `y′ − y` is within `7/20` of
`±perp n`.

TODO: none — proved.
What's missing (paper §1.4, "fan"): `e = y − a`, `e′ = y′ − a` are unit (`Low_subset`,
`dist_of_mem_nbδ`), `‖e − e′‖ = dist y y′ ≥ 1` (`one_le_dist`), `⟨e, n⟩ ≥ 4/5` (`IsFan43`),
`⟨e′, n′⟩ ≥ 4/5` and `‖n′ − n‖ ≤ 1/50` (`frame_normal_close`, `dist y y′ ≤ 2`), so
`⟨e′, n⟩ ≥ 0.78`.  In angles from `n`: `|α| ≤ 36.9°`, `|α′| ≤ 38.8°`, `|α − α′| ≥ 60°`, so
`y′ − y = e′ − e` has length `∈ [1, 1.226]` and direction within `8.8°` of `±perp n`; hence
`‖y′ − y − dirF n (±π/2)‖ ≤ 0.282 < 7/20`.  (A coordinate proof: with `x = ⟨·, perp n⟩`,
`c = ⟨·, n⟩`, bound `|c′ − c|` and `|x′ − x| − 1`.)
Acceptance: no `sorry`.
Depends on: `frame_normal_close`, `one_le_dist`, `dist_of_mem_nbδ`, `n1_inner_frame`,
`norm_perp`. Difficulty M–L. -/
theorem fan_common_low_slot (hX : Normal X) {y y' n n' : Pt} (hF : Frame43 X y n)
    (hF' : Frame43 X y' n') (hy : y ∈ Rset X) (hy' : y' ∈ Rset X) (hf : IsFan43 X y n)
    (hf' : IsFan43 X y' n') {a : Pt} (ha : a ∈ Low X y) (ha' : a ∈ Low X y')
    (hne : y ≠ y') :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ‖y' - y - dirF n (σ * (π / 2))‖ ≤ 7 / 20 := by
  have hn := hF.unit
  have d1 : dist a y = 1 := dist_of_mem_nbδ hX (Low_subset X y ha)
  have d2 : dist a y' = 1 := dist_of_mem_nbδ hX (Low_subset X y' ha')
  have hyX : y ∈ X := (mem_sdiff.1 hy).1
  have hy'X : y' ∈ X := (mem_sdiff.1 hy').1
  have hd : dist y y' ≤ 2 := by
    have := dist_triangle y a y'
    have := dist_comm y a
    linarith
  have hnn := frame_normal_close hF hF' hd
  unfold ε₀43 at hnn
  have hsep := one_le_dist hX.minDist_eq hyX hy'X hne
  have n1 : ‖y - a‖ = 1 := by rw [← dist_eq_norm, dist_comm]; exact d1
  have n2 : ‖y' - a‖ = 1 := by rw [← dist_eq_norm, dist_comm]; exact d2
  have hc := hf.2.1 a ha
  have hc'' := hf'.2.1 a ha'
  have hc' : 4 / 5 - 1 / 50 ≤ inner ℝ (y' - a) n := by
    have e : inner ℝ (y' - a) n = inner ℝ (y' - a) n' - inner ℝ (y' - a) (n' - n) := by
      rw [inner_sub_right]; ring
    have hb : |inner ℝ (y' - a) (n' - n)| ≤ 1 / 50 := by
      calc _ ≤ ‖y' - a‖ * ‖n' - n‖ := abs_real_inner_le_norm _ _
        _ ≤ 1 / 50 := by rw [n2, one_mul]; exact hnn
    rw [e]; linarith [(abs_le.1 hb).2]
  have s1 := ch_sq hn (y - a)
  have s2 := ch_sq hn (y' - a)
  have s3 := ch_sq hn (y' - y)
  rw [n1] at s1
  rw [n2] at s2
  have ey : y' - y = (y' - a) - (y - a) := by abel
  have i1 : inner ℝ (y' - y) n = inner ℝ (y' - a) n - inner ℝ (y - a) n := by
    rw [ey, inner_sub_left]
  have i2 : inner ℝ (y' - y) (perp n) =
      inner ℝ (y' - a) (perp n) - inner ℝ (y - a) (perp n) := by
    rw [ey, inner_sub_left]
  have hsep' : 1 ≤ ‖y' - y‖ := by rw [← dist_eq_norm, dist_comm]; exact hsep
  rw [i1, i2] at s3
  have hsq : 1 ≤ (inner ℝ (y' - a) n - inner ℝ (y - a) n) ^ 2 +
      (inner ℝ (y' - a) (perp n) - inner ℝ (y - a) (perp n)) ^ 2 := by
    rw [← s3]; nlinarith
  have key : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      (inner ℝ (y' - a) n - inner ℝ (y - a) n) ^ 2 +
        (inner ℝ (y' - a) (perp n) - inner ℝ (y - a) (perp n) - σ) ^ 2 ≤ (7 / 20) ^ 2 →
      ‖y' - y - dirF n (σ * (π / 2))‖ ≤ 7 / 20 := by
    intro σ hσ h
    have s := ch_sq hn (y' - y - dirF n (σ * (π / 2)))
    have e1 : inner ℝ (y' - y - dirF n (σ * (π / 2))) n =
        inner ℝ (y' - a) n - inner ℝ (y - a) n := by
      rw [inner_sub_left (y' - y), ch_dirF_n hn, ch_cos2 hσ, i1]; ring
    have e2 : inner ℝ (y' - y - dirF n (σ * (π / 2))) (perp n) =
        inner ℝ (y' - a) (perp n) - inner ℝ (y - a) (perp n) - σ := by
      rw [inner_sub_left (y' - y), ch_dirF_p hn, ch_sin2 hσ, i2]
    rw [e1, e2] at s
    nlinarith [norm_nonneg (y' - y - dirF n (σ * (π / 2)))]
  obtain ⟨σ, hσ, h⟩ := ch_num hc hc' s1 s2 hsq
  exact ⟨σ, hσ, key σ hσ h⟩

/-- **Fans have private receivers.**

TODO: none — proved.
What's missing (paper §1.4, "fan", with the HF2–HF2 argument): suppose `a ∈ Low y ∩ Low y′`.
`fan_common_low_slot` gives `σ′`; the slot neighbour of `y` at `σ′·90°` (from `FanSlots`: `p` at
`−σ·90°` or `q` at `σ·90°`, within `1/20`) is within `7/20 + 1/20 < 1` of `y′`, hence equals
`y′` (`one_le_dist`).  It is not `p` (`p ∈ S`, `y′ ∈ R`), so `σ′ = σ`, `y′ = q ∉ S`, and the
HF2 branch gives `z₁` (slot `σ·30°`), `z₂` (slot `−σ·30°`), `dist z₁ z₂ = 1`.  Symmetrically
(roles swapped, `frame_normal_close`) `y = q′` is `y′`'s slot-`σ₁·90°` neighbour with HF2 data
`z₁′, z₂′`, and `σ₁ = −σ` (`y − y′ ≈ −σ perp n`, `‖n − n′‖ ≤ 1/50`).  Then
`‖z₁ − z₁′‖ ≤ 3/20 + 1/50 < 1` (`dirF n (σπ/2) + dirF n (−σπ/6) = dirF n (σπ/6)`, and
`‖dirF n ψ − dirF n′ ψ‖ = ‖n − n′‖`), so `z := z₁ = z₁′ ∈ D`.  Its `δ`-neighbours include `y`,
`y′`, `z₂`, `z₂′` (distances `= minDist`), pairwise `≥ 0.8` apart by their positions
`0, dirF(σπ/2), dirF(−σπ/6), dirF(σπ/2) + dirF(σπ/6)` relative to `y` (errors `≤ 0.2`), so
`degδ X z ≥ 4`, contradicting `degδ_le_three_of_D`.
Acceptance: no `sorry`.
Depends on: `fan_common_low_slot`, `frame_normal_close`, `degδ_le_three_of_D`, `one_le_dist`,
`mem_nbδ`, `dist_of_mem_nbδ`. Difficulty L. -/
theorem fan_disjoint (hX : Normal X) {y y' n n' : Pt} (hF : Frame43 X y n)
    (hF' : Frame43 X y' n') (hy : y ∈ Rset X) (hy' : y' ∈ Rset X) (hf : IsFan43 X y n)
    (hf' : IsFan43 X y' n') (hne : y ≠ y') : Disjoint (Low X y) (Low X y') := by
  rw [Finset.disjoint_left]
  intro a ha ha'
  have hyX : y ∈ X := (mem_sdiff.1 hy).1
  have hy'X : y' ∈ X := (mem_sdiff.1 hy').1
  have d1 : dist a y = 1 := dist_of_mem_nbδ hX (Low_subset X y ha)
  have d2 : dist a y' = 1 := dist_of_mem_nbδ hX (Low_subset X y' ha')
  have hd : dist y y' ≤ 2 := by
    have := dist_triangle y a y'
    have := dist_comm y a
    linarith
  have hnn := frame_normal_close hF hF' hd
  unfold ε₀43 at hnn
  have hn := hF.unit
  obtain ⟨σ', hσ', h'⟩ := fan_common_low_slot hX hF hF' hy hy' hf hf' ha ha' hne
  obtain ⟨σ, hσ, hy'sl, z₁, hz₁, hz₁D, hz₁sl, z₂, hz₂, hz₂D, hz₂sl, hd₁₂⟩ :=
    ch_fan_hf2 hX hy' hf.2.2 hσ' h'
  obtain ⟨σ₁, hσ₁, h₁⟩ := fan_common_low_slot hX hF' hF hy' hy hf' hf ha' ha (Ne.symm hne)
  obtain ⟨τ, hτ, hysl, w₁, hw₁, hw₁D, hw₁sl, w₂, hw₂, hw₂D, hw₂sl, hdw⟩ :=
    ch_fan_hf2 hX hy hf'.2.2 hσ₁ h₁
  -- abscissae w.r.t. `(y, n)`
  have Xy' := ch_slotX hn hy'sl
  rw [sub_self, norm_zero, ch_sin2 hσ] at Xy'
  have Xy := ch_slotX hn hysl
  rw [ch_sin2 hτ] at Xy
  have eyy : inner ℝ (y - y') (perp n) = -inner ℝ (y' - y) (perp n) := by
    rw [← inner_neg_left, neg_sub]
  rw [abs_le] at Xy Xy'
  have hτσ : τ = -σ := by
    rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl
    all_goals first | (exfalso; linarith) | norm_num
  subst hτσ
  rw [neg_mul] at hw₁sl
  rw [neg_mul, neg_neg] at hw₂sl
  -- `y`'s and `y′`'s D-points at `σ·30°`, `−σ·30°` coincide
  have hzw : z₁ = w₁ := by
    by_contra hne'
    have h1 := one_le_dist hX.minDist_eq (mem_nbδ.1 hz₁).1 (mem_nbδ.1 hw₁).1 hne'
    rw [dist_eq_norm] at h1
    have e : z₁ - w₁ = (z₁ - y - dirF n (σ * (π / 6))) - (w₁ - y' - dirF n' (-(σ * (π / 6))))
        - (y' - y - dirF n (σ * (π / 2)))
        + (dirF n (-(σ * (π / 6))) - dirF n' (-(σ * (π / 6)))) := by
      rw [ch_hex n hσ]; abel
    rw [e] at h1
    have b1 := norm_add_le ((z₁ - y - dirF n (σ * (π / 6))) -
      (w₁ - y' - dirF n' (-(σ * (π / 6)))) - (y' - y - dirF n (σ * (π / 2))))
      (dirF n (-(σ * (π / 6))) - dirF n' (-(σ * (π / 6))))
    have b2 := norm_sub_le ((z₁ - y - dirF n (σ * (π / 6))) -
      (w₁ - y' - dirF n' (-(σ * (π / 6))))) (y' - y - dirF n (σ * (π / 2)))
    have b3 := norm_sub_le (z₁ - y - dirF n (σ * (π / 6))) (w₁ - y' - dirF n' (-(σ * (π / 6))))
    have b4 := ch_dirF_sub n' n (-(σ * (π / 6)))
    rw [norm_sub_rev n n'] at b4
    unfold Slot at hz₁sl hw₁sl hy'sl
    linarith
  subst hzw
  -- four `δ`-neighbours of `z₁`
  have hz₁' := mem_nbδ.1 hz₁
  have hw₁' := mem_nbδ.1 hw₁
  have hyN : y ∈ nbδ X z₁ :=
    mem_nbδ.2 ⟨hyX, hz₁'.2.1.symm, by rw [dist_comm]; exact hz₁'.2.2⟩
  have hy'N : y' ∈ nbδ X z₁ :=
    mem_nbδ.2 ⟨hy'X, hw₁'.2.1.symm, by rw [dist_comm]; exact hw₁'.2.2⟩
  have hz₂N : z₂ ∈ nbδ X z₁ := by
    refine mem_nbδ.2 ⟨(mem_nbδ.1 hz₂).1, fun h => ?_, hd₁₂⟩
    rw [h, dist_self, hX.minDist_eq] at hd₁₂; norm_num at hd₁₂
  have hw₂N : w₂ ∈ nbδ X z₁ := by
    refine mem_nbδ.2 ⟨(mem_nbδ.1 hw₂).1, fun h => ?_, hdw⟩
    rw [h, dist_self, hX.minDist_eq] at hdw; norm_num at hdw
  -- their abscissae: `0`, `σ`, `−σ/2`, `3σ/2`
  have Xz₂ := ch_slotX hn hz₂sl
  rw [Real.sin_neg, ch_sin6 hσ, sub_self, norm_zero] at Xz₂
  have Xw₂ := ch_slotX hn hw₂sl
  rw [ch_sin6 hσ] at Xw₂
  rw [abs_le] at Xz₂ Xw₂
  have ew : inner ℝ (w₂ - y) (perp n) =
      inner ℝ (w₂ - y') (perp n) + inner ℝ (y' - y) (perp n) := by
    rw [← inner_add_left]; congr 1; abel
  have X0 : inner ℝ (y - y) (perp n) = 0 := by rw [sub_self, inner_zero_left]
  have sep : ∀ r r' : Pt, r = r' → inner ℝ (r - y) (perp n) = inner ℝ (r' - y) (perp n) :=
    fun r r' h => by rw [h]
  have hsub : ({y, y', z₂, w₂} : Finset Pt) ⊆ nbδ X z₁ := by
    intro r hr
    simp only [mem_insert, mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  have hcard : ({y, y', z₂, w₂} : Finset Pt).card = 4 := by
    rw [card_insert_of_notMem, card_insert_of_notMem, card_pair]
    · intro h; have := sep _ _ h
      rcases hσ with rfl | rfl <;> linarith
    · simp only [mem_insert, mem_singleton, not_or]
      refine ⟨fun h => ?_, fun h => ?_⟩ <;> have := sep _ _ h <;>
        rcases hσ with rfl | rfl <;> linarith
    · simp only [mem_insert, mem_singleton, not_or]
      refine ⟨hne, fun h => ?_, fun h => ?_⟩ <;> have := sep _ _ h <;>
        rcases hσ with rfl | rfl <;> linarith
  have h4 := card_le_card hsub
  rw [hcard] at h4
  have h3 : (nbδ X z₁).card ≤ 3 := degδ_le_three_of_D hX hz₁D
  omega

/-- **Caps have private receivers**: two caps sharing a receiver `b` satisfy
`‖y − y′‖ ≤ 1/20 + 1/20 + 1/50 < 1`.

TODO: none — proved.
What's missing: `‖b − y + n‖ ≤ 1/20`, `‖b − y′ + n′‖ ≤ 1/20` (`IsCap43`), `dist y y′ ≤ 2`
(both at distance `1` from `b`), `‖n′ − n‖ ≤ 1/50` (`frame_normal_close`); then
`dist y y′ < 1` contradicts `one_le_dist`.
Acceptance: no `sorry`.
Depends on: `frame_normal_close`, `one_le_dist`, `dist_of_mem_nbδ`, `Low_subset`.
Difficulty S–M. -/
theorem cap_disjoint (hX : Normal X) {y y' n n' : Pt} (hF : Frame43 X y n)
    (hF' : Frame43 X y' n') (hy : y ∈ Rset X) (hy' : y' ∈ Rset X) (hc : IsCap43 X y n)
    (hc' : IsCap43 X y' n') (hne : y ≠ y') : Disjoint (Low X y) (Low X y') := by
  rw [Finset.disjoint_left]
  intro b hb hb'
  have h1 := hc.2 b hb
  have h2 := hc'.2 b hb'
  have hyX : y ∈ X := (mem_sdiff.1 hy).1
  have hy'X : y' ∈ X := (mem_sdiff.1 hy').1
  have d1 := dist_of_mem_nbδ hX (Low_subset X y hb)
  have d2 := dist_of_mem_nbδ hX (Low_subset X y' hb')
  have hd : dist y y' ≤ 2 := by
    have := dist_triangle y b y'
    have := dist_comm y b
    have := dist_comm b y'
    linarith
  have hn := frame_normal_close hF hF' hd
  have hsep := one_le_dist hX.minDist_eq hyX hy'X hne
  have e : y' - y = (b - y + n) - (b - y' + n') + (n' - n) := by abel
  have h3 : ‖y' - y‖ ≤ 1 / 20 + 1 / 20 + ε₀43 := by
    rw [e]
    calc ‖(b - y + n) - (b - y' + n') + (n' - n)‖
        ≤ ‖(b - y + n) - (b - y' + n')‖ + ‖n' - n‖ := norm_add_le _ _
      _ ≤ ‖b - y + n‖ + ‖b - y' + n'‖ + ‖n' - n‖ := by
          gcongr; exact norm_sub_le _ _
      _ ≤ _ := by linarith
  rw [dist_comm, dist_eq_norm] at hsep
  norm_num [ε₀43] at h3
  linarith

/-- **Owner uniqueness** (§1.4): distinct heavy good points have disjoint receiver sets.
Fans and caps never coexist (`t ≥ 0.7` vs `t ≤ 0.6`).

TODO: none — proved from the statements.
Acceptance: no `sorry` (inherits).
Depends on: `fan_disjoint`, `cap_disjoint`. -/
theorem low_disjoint (hX : Normal X) {y y' n n' : Pt} (hF : Frame43 X y n)
    (hF' : Frame43 X y' n') (hy : y ∈ Rset X) (hy' : y' ∈ Rset X)
    (ht : IsFan43 X y n ∨ IsCap43 X y n) (ht' : IsFan43 X y' n' ∨ IsCap43 X y' n')
    (hne : y ≠ y') : Disjoint (Low X y) (Low X y') := by
  rcases ht with hf | hc <;> rcases ht' with hf' | hc'
  · exact fan_disjoint hX hF hF' hy hy' hf hf' hne
  · exfalso; linarith [hf.1, hc'.1]
  · exfalso; linarith [hc.1, hf'.1]
  · exact cap_disjoint hX hF hF' hy hy' hc hc' hne

end

end Erdos132Main
