import Erdos132.E132Main43Frame

/-!
# Erdős Problem 132, `4/3` theorem — classification of heavy points (Lemmas P, M, H, Pin)

Paper: `angle_R6.md` §1.3.  Let `y ∈ R` have a frame `(n, h)` (`Frame43`) and `v(y) ≥ 9`.
Neighbours are unit vectors pairwise `≥ 60°` apart.  *Kinds*: K-row (`S ∖ D`, height
`∈ [h − ε|X|, h]`), D (height `≥ h + t − ε|X|`), interior (`< h`).

* `mS_le_four_of_frame`: `S`-neighbours have height `> −1/4`, so `m_y ≤ 4`; hence
  `(deg, m) ∈ {(5,4), (6,4), (6,3)}`.
* **Lemma P** (`pair_sym`, `pair_K`, `pair_D`): two neighbours of the same kind are
  mirror-symmetric (`|X₁ + X₂|` small); three of one kind are impossible.
* **Lemma M** (`lemmaM`): `m = 4` ⇒ K at `±90°`, D at `±30°` (within `1.2°`).
* **Lemma H** (`lemmaH`): `deg = 6`, `m = 3` ⇒ the hexagon (`hexagon_exact`) is HF1, HF2 or a
  cap.
* **Lemma Pin** (`pin_fan`, `pin_cap`): fans force `t ≥ 0.7`, caps force `t ≤ 0.6`.
* Outputs: `heavy_type : IsFan43 ∨ IsCap43` (consumed by `E132Main43Charge`) and
  `heavy_low : v(y) ≤ 8 + |Low X y|` (both proved from the statements).

Shapes (`FanShape`, `CapShape`) record, besides the slots, the two facts used downstream:
every neighbour of height `≤ −2/3` has height `≤ −4/5` (fan) resp. is within `1/20` of
`y − n` (cap), and `v(y) ≤ 8 + #{neighbours of height ≤ −4/5}`.
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-! ## Shapes -/

/-- **Fan shape** (F6, F5, HF1, HF2): the fan slots, lower neighbours are well below
(`height ≤ −2/3 ⇒ height ≤ −4/5`), and `v ≤ 8 + #{neighbours of height ≤ −4/5}`
(F6: `10 ≤ 8 + 2`; F5, HF: `9 ≤ 8 + 1`). -/
def FanShape (X : Finset Pt) (y n : Pt) : Prop :=
  FanSlots X y n ∧
    (∀ a ∈ nbδ X y, inner ℝ (a - y) n ≤ -(2 / 3) → inner ℝ (a - y) n ≤ -(4 / 5)) ∧
    vR X y ≤ 8 + ((nbδ X y).filter (fun a => inner ℝ (a - y) n ≤ -(4 / 5))).card

/-- **Cap shape**: a K-row neighbour at `σ·60°`, a D-neighbour at `0°`; the only neighbour of
height `≤ −2/3` is `b ≈ y − n` (the points at `±120°` have height `≈ −1/2`); `v = 9 ≤ 8 + 1`. -/
def CapShape (X : Finset Pt) (y n : Pt) : Prop :=
  (∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∃ p ∈ nbδ X y, ∃ z ∈ nbδ X y,
      p ∈ Sset X ∧ p ∉ Dset X ∧ z ∈ Dset X ∧
      Slot y n (σ * (π / 3)) (1 / 20) p ∧ Slot y n 0 (1 / 20) z) ∧
    (∀ a ∈ nbδ X y, inner ℝ (a - y) n ≤ -(2 / 3) → ‖a - y + n‖ ≤ 1 / 20) ∧
    vR X y ≤ 8 + ((nbδ X y).filter (fun a => inner ℝ (a - y) n ≤ -(4 / 5))).card

/-! ## Frame toolkit (private helpers) -/

private theorem c43_np (n : Pt) : inner ℝ n (perp n) = 0 := by
  rw [← det2_eq_inner_perp]; unfold det2; ring

private theorem c43_pn (n : Pt) : inner ℝ (perp n) n = 0 := by
  rw [real_inner_comm]; exact c43_np n

/-- Squared norm in the frame `(n, perp n)`. -/
private theorem c43_sq {n : Pt} (hn : ‖n‖ = 1) (v : Pt) :
    ‖v‖ ^ 2 = inner ℝ v n ^ 2 + inner ℝ v (perp n) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, n1_inner_frame hn v v]; ring

private theorem c43_dirF_n {n : Pt} (hn : ‖n‖ = 1) (ψ : ℝ) :
    inner ℝ (dirF n ψ) n = Real.cos ψ := by
  unfold dirF
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, c43_pn,
    real_inner_self_eq_norm_sq, hn]; ring

private theorem c43_dirF_p {n : Pt} (hn : ‖n‖ = 1) (ψ : ℝ) :
    inner ℝ (dirF n ψ) (perp n) = Real.sin ψ := by
  unfold dirF
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, c43_np,
    real_inner_self_eq_norm_sq, norm_perp, hn]; ring

private theorem c43_abs_n {n : Pt} (hn : ‖n‖ = 1) (v : Pt) : |inner ℝ v n| ≤ ‖v‖ := by
  have := abs_real_inner_le_norm v n; rwa [hn, mul_one] at this

private theorem c43_abs_p {n : Pt} (hn : ‖n‖ = 1) (v : Pt) : |inner ℝ v (perp n)| ≤ ‖v‖ := by
  have := abs_real_inner_le_norm v (perp n); rwa [norm_perp, hn, mul_one] at this

/-- A slot gives both coordinates within `η`. -/
private theorem c43_slot_coords {y n q : Pt} (hn : ‖n‖ = 1) {ψ η : ℝ} (h : Slot y n ψ η q) :
    |inner ℝ (q - y) n - Real.cos ψ| ≤ η ∧
      |inner ℝ (q - y) (perp n) - Real.sin ψ| ≤ η := by
  unfold Slot at h
  constructor
  · have := c43_abs_n hn (q - y - dirF n ψ)
    rw [inner_sub_left, c43_dirF_n hn] at this; linarith
  · have := c43_abs_p hn (q - y - dirF n ψ)
    rw [inner_sub_left, c43_dirF_p hn] at this; linarith

/-- A slot from the coordinates. -/
private theorem c43_slot_of {y n q : Pt} (hn : ‖n‖ = 1) {ψ η : ℝ} (hη : 0 ≤ η)
    (h : (inner ℝ (q - y) n - Real.cos ψ) ^ 2 + (inner ℝ (q - y) (perp n) - Real.sin ψ) ^ 2 ≤
      η ^ 2) : Slot y n ψ η q := by
  unfold Slot
  have e := c43_sq hn (q - y - dirF n ψ)
  rw [inner_sub_left (q - y) (dirF n ψ), inner_sub_left (q - y) (dirF n ψ) (perp n),
    c43_dirF_n hn, c43_dirF_p hn] at e
  nlinarith [norm_nonneg (q - y - dirF n ψ)]

private theorem c43_slot_mono {y n q : Pt} {ψ η η' : ℝ} (h : Slot y n ψ η q) (hle : η ≤ η') :
    Slot y n ψ η' q := le_trans h hle

/-- Neighbours are unit vectors: `Z² + X² = 1`. -/
private theorem c43_unit (hX : Normal X) {y n q : Pt} (hn : ‖n‖ = 1) (hq : q ∈ nbδ X y) :
    inner ℝ (q - y) n ^ 2 + inner ℝ (q - y) (perp n) ^ 2 = 1 := by
  rw [← c43_sq hn, ← dist_eq_norm, dist_of_mem_nbδ hX hq]; norm_num

/-- Distinct neighbours are `≥ 1` apart, in coordinates. -/
private theorem c43_sep (hX : Normal X) {y n q q' : Pt} (hn : ‖n‖ = 1) (hq : q ∈ nbδ X y)
    (hq' : q' ∈ nbδ X y) (hne : q ≠ q') :
    1 ≤ (inner ℝ (q - y) n - inner ℝ (q' - y) n) ^ 2 +
      (inner ℝ (q - y) (perp n) - inner ℝ (q' - y) (perp n)) ^ 2 := by
  have h1 := one_le_dist hX.minDist_eq (mem_nbδ.1 hq).1 (mem_nbδ.1 hq').1 hne
  have e := c43_sq hn ((q - y) - (q' - y))
  rw [inner_sub_left (q - y) (q' - y), inner_sub_left (q - y) (q' - y) (perp n),
    sub_sub_sub_cancel_right] at e
  rw [dist_eq_norm] at h1
  nlinarith

private theorem c43_abs_le_one {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) : |b| ≤ 1 := by
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg a, sq_nonneg (b - 1), sq_nonneg (b + 1)]

private theorem c43_r_lo : (1732 / 1000 : ℝ) < √3 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  nlinarith [Real.sqrt_nonneg 3]

private theorem c43_r_hi : √3 < (17321 / 10000 : ℝ) := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  nlinarith [Real.sqrt_nonneg 3]

private theorem c43_r_sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

/-- Height lower bound for `S`-neighbours (`frame_outside`). -/
private theorem c43_S_low (hX : Normal X) {y n q : Pt} (hF : Frame43 X y n) (hq : q ∈ nbδ X y)
    (hS : q ∈ Sset X) :
    depth X y - 1 / 49 * |inner ℝ (q - y) (perp n)| ≤ inner ℝ (q - y) n := by
  have := frame_outside hX hF (by rw [dist_of_mem_nbδ hX hq]; norm_num) (Sset_not_interior hX hS)
  unfold ε43 at this; exact this

/-- Height upper bound for K-row neighbours (`Frame43.top`). -/
private theorem c43_K_top {y n q : Pt} (hF : Frame43 X y n) (hq : q ∈ nbδ X y)
    (hD : q ∉ Dset X) : inner ℝ (q - y) n ≤ depth X y :=
  hF.top (ball_polygon_a (mem_nbδ.1 hq).1 hD)

/-- Height lower bound for D-neighbours (`frame_D`). -/
private theorem c43_D_low (hX : Normal X) {y n q : Pt} (hF : Frame43 X y n) (hq : q ∈ nbδ X y)
    (hD : q ∈ Dset X) :
    depth X y + tgap X - 1 / 49 * |inner ℝ (q - y) (perp n)| ≤ inner ℝ (q - y) n := by
  have := frame_D hX hF hD (by rw [dist_of_mem_nbδ hX hq]; norm_num)
  unfold ε43 at this; exact this

private theorem c43_tgap_pos (hX : Normal X) : 0 < tgap X := by
  have hT := two_of_pos hX.dist2_pos
  unfold tgap; linarith [hT.lt]

/-! ## Counting `S`-neighbours -/

/-- At a framed point `m_y ≤ 4`: `S`-neighbours are not interior, so their height is
`≥ h − 1/49 > −1/4` (`frame_outside`), and an open arc of length `< 240°` holds at most four
points `60°` apart.

TODO: none — proved.
What's missing: `card_sep_arc_le_four` with `n`; cone from `frame_outside`
(`|Xq| ≤ ‖q − y‖ = 1`, `h > 0`) and `Sset_not_interior`; separation `one_le_dist`.
Acceptance: no `sorry`.
Depends on: `card_sep_arc_le_four`, `frame_outside`, `Sset_not_interior`, `one_le_dist`,
`norm_perp`. Difficulty S–M. -/
theorem mS_le_four_of_frame (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) : mS X y ≤ 4 := by
  have hn := hF.unit
  unfold mS
  apply card_sep_arc_le_four (y := y) hn
  · intro q hq; exact dist_of_mem_nbδ hX (mem_filter.1 hq).1
  · intro q hq q' hq' hne
    exact one_le_dist hX.minDist_eq (mem_nbδ.1 (mem_filter.1 hq).1).1
      (mem_nbδ.1 (mem_filter.1 hq').1).1 hne
  · intro q hq
    have h1 := mem_filter.1 hq
    have hlow := c43_S_low hX hF h1.1 h1.2
    have hu := c43_abs_le_one (c43_unit hX hn h1.1)
    have := hF.depth_pos
    nlinarith

/-! ## Lemma P (pairs) -/

/-- **Lemma P, core identity**: two unit vectors at distance `≥ 1` (angle `≥ 60°`) satisfy
`|X₁ + X₂| ≤ √3·|Z₁ − Z₂|` in any orthonormal frame `(perp n, n)`.
(With `e_i = (sin ψ_i, cos ψ_i)`: `(X₁+X₂)²‖e₁−e₂‖² = (Z₁−Z₂)²‖e₁+e₂‖²`, and
`‖e₁+e₂‖² = 4 − ‖e₁−e₂‖² ≤ 3 ≤ 3‖e₁−e₂‖²`.)  Together with `|Z₁ − Z₂|` this is the paper's
Lemma P: the distance from `e₂` to the mirror image `(−X₁, Z₁)` of `e₁` is
`√((X₁+X₂)² + (Z₁−Z₂)²) = 2|sin((ψ₁+ψ₂)/2)| ≤ 2|Z₁ − Z₂|`.  (For a pair at `≈ ±90°`,
`X₁ + X₂ ≈ 0` automatically and the mirror error is all in `Z₁ − Z₂`.)

TODO: none — proved.
What's missing: coordinates (`n1_inner_frame`/`inner_pt`, `unit_sq`); the identity above is a
polynomial identity under `X_i² + Z_i² = 1`; then `nlinarith`/`sq_le_sq'`.
Acceptance: no `sorry`.
Depends on: `n1_inner_frame`, `norm_perp`, `inner_pt`. Difficulty M. -/
theorem pair_sym {n e₁ e₂ : Pt} (hn : ‖n‖ = 1) (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (hsep : 1 ≤ ‖e₁ - e₂‖) :
    |inner ℝ e₁ (perp n) + inner ℝ e₂ (perp n)| ≤ √3 * |inner ℝ e₁ n - inner ℝ e₂ n| := by
  have e1 := c43_sq hn e₁
  have e2 := c43_sq hn e₂
  have e3 := c43_sq hn (e₁ - e₂)
  rw [h₁] at e1
  rw [h₂] at e2
  rw [inner_sub_left, inner_sub_left] at e3
  set X1 := inner ℝ e₁ (perp n)
  set X2 := inner ℝ e₂ (perp n)
  set Z1 := inner ℝ e₁ n
  set Z2 := inner ℝ e₂ n
  have hs : 1 ≤ ‖e₁ - e₂‖ ^ 2 := by nlinarith [norm_nonneg (e₁ - e₂)]
  have hid : (X1 + X2) ^ 2 * ((X1 - X2) ^ 2 + (Z1 - Z2) ^ 2) =
      (Z1 - Z2) ^ 2 * ((X1 + X2) ^ 2 + (Z1 + Z2) ^ 2) := by
    have hab : (X1 + X2) * (X1 - X2) + (Z1 - Z2) * (Z1 + Z2) = 0 := by nlinarith
    linear_combination ((X1 + X2) * (X1 - X2) - (Z1 - Z2) * (Z1 + Z2)) * hab
  have hsum : (X1 + X2) ^ 2 + (Z1 + Z2) ^ 2 ≤ 3 := by nlinarith
  have hB : 1 ≤ (X1 - X2) ^ 2 + (Z1 - Z2) ^ 2 := by nlinarith
  have key : (X1 + X2) ^ 2 ≤ 3 * (Z1 - Z2) ^ 2 := by
    by_contra hc
    push Not at hc
    have h1 : (Z1 - Z2) ^ 2 * ((X1 + X2) ^ 2 + (Z1 + Z2) ^ 2) ≤ 3 * (Z1 - Z2) ^ 2 :=
      by nlinarith [sq_nonneg (Z1 - Z2)]
    have h2 : 3 * (Z1 - Z2) ^ 2 * ((X1 - X2) ^ 2 + (Z1 - Z2) ^ 2) <
        (X1 + X2) ^ 2 * ((X1 - X2) ^ 2 + (Z1 - Z2) ^ 2) :=
      mul_lt_mul_of_pos_right hc (by linarith)
    nlinarith [sq_nonneg (Z1 - Z2)]
  have h3 : |X1 + X2| ≤ |√3 * (Z1 - Z2)| := by
    rw [← sq_le_sq, mul_pow, c43_r_sq]; exact key
  rwa [abs_mul, abs_of_pos (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3))] at h3

/-- **Lemma P (K)**: two distinct K-row neighbours are mirror-symmetric: heights within
`1/49` (both in `[h − 1/49, h]`) and `|X₁ + X₂| ≤ √3/49 < 1/25`.

TODO: none — proved.
What's missing: heights from `Frame43.top` (`ball_polygon_a`) and `frame_outside`
(`Sset_not_interior`), `|X_i| ≤ 1`; `pair_sym` with `e_i = q_i − y`
(`dist_of_mem_nbδ`, `one_le_dist`).
Acceptance: no `sorry`.
Depends on: `pair_sym`, `frame_outside`, `Frame43.top`, `ball_polygon_a`, `Sset_not_interior`.
Difficulty M. -/
theorem pair_K (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) {q₁ q₂ : Pt}
    (h₁ : q₁ ∈ nbδ X y) (h₂ : q₂ ∈ nbδ X y) (hne : q₁ ≠ q₂)
    (hS₁ : q₁ ∈ Sset X) (hD₁ : q₁ ∉ Dset X) (hS₂ : q₂ ∈ Sset X) (hD₂ : q₂ ∉ Dset X) :
    |inner ℝ (q₁ - y) n - inner ℝ (q₂ - y) n| ≤ 1 / 49 ∧
      |inner ℝ (q₁ - y) (perp n) + inner ℝ (q₂ - y) (perp n)| ≤ 1 / 25 := by
  have hn := hF.unit
  have l1 := c43_S_low hX hF h₁ hS₁
  have l2 := c43_S_low hX hF h₂ hS₂
  have t1 := c43_K_top hF h₁ hD₁
  have t2 := c43_K_top hF h₂ hD₂
  have a1 := c43_abs_le_one (c43_unit hX hn h₁)
  have a2 := c43_abs_le_one (c43_unit hX hn h₂)
  have hZ : |inner ℝ (q₁ - y) n - inner ℝ (q₂ - y) n| ≤ 1 / 49 := by
    rw [abs_le]; constructor <;> nlinarith
  refine ⟨hZ, ?_⟩
  have hu1 : ‖q₁ - y‖ = 1 := by rw [← dist_eq_norm, dist_of_mem_nbδ hX h₁]
  have hu2 : ‖q₂ - y‖ = 1 := by rw [← dist_eq_norm, dist_of_mem_nbδ hX h₂]
  have hsep : 1 ≤ ‖(q₁ - y) - (q₂ - y)‖ := by
    rw [sub_sub_sub_cancel_right, ← dist_eq_norm]
    exact one_le_dist hX.minDist_eq (mem_nbδ.1 h₁).1 (mem_nbδ.1 h₂).1 hne
  have hs := pair_sym hn hu1 hu2 hsep
  have := c43_r_hi
  nlinarith [abs_nonneg (inner ℝ (q₁ - y) n - inner ℝ (q₂ - y) n)]

/-- **Lemma P (D)**: two distinct D-neighbours are mirror-symmetric: heights differ by
`≤ (9/400)|X₁ − X₂| ≤ 9/200` and `|X₁ + X₂| ≤ √3·(9/200) < 2/25`.

TODO: none — proved.
What's missing: `dd_heights`, `|X₁ − X₂| ≤ 2`, `pair_sym`.
Acceptance: no `sorry`.
Depends on: `dd_heights`, `pair_sym`, `dist_of_mem_nbδ`, `one_le_dist`. Difficulty M. -/
theorem pair_D (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) {q₁ q₂ : Pt}
    (h₁ : q₁ ∈ nbδ X y) (h₂ : q₂ ∈ nbδ X y) (hne : q₁ ≠ q₂)
    (hD₁ : q₁ ∈ Dset X) (hD₂ : q₂ ∈ Dset X) :
    |inner ℝ (q₁ - y) n - inner ℝ (q₂ - y) n| ≤ 9 / 200 ∧
      |inner ℝ (q₁ - y) (perp n) + inner ℝ (q₂ - y) (perp n)| ≤ 2 / 25 := by
  have hn := hF.unit
  have hdd := dd_heights hX hF hD₁ hD₂ (dist_of_mem_nbδ hX h₁).le (dist_of_mem_nbδ hX h₂).le
  have a1 := c43_abs_le_one (c43_unit hX hn h₁)
  have a2 := c43_abs_le_one (c43_unit hX hn h₂)
  have hd2 : |inner ℝ (q₁ - y) (perp n) - inner ℝ (q₂ - y) (perp n)| ≤ 2 := by
    have := abs_sub (inner ℝ (q₁ - y) (perp n)) (inner ℝ (q₂ - y) (perp n)); linarith
  have hZ : |inner ℝ (q₁ - y) n - inner ℝ (q₂ - y) n| ≤ 9 / 200 := by nlinarith
  refine ⟨hZ, ?_⟩
  have hu1 : ‖q₁ - y‖ = 1 := by rw [← dist_eq_norm, dist_of_mem_nbδ hX h₁]
  have hu2 : ‖q₂ - y‖ = 1 := by rw [← dist_eq_norm, dist_of_mem_nbδ hX h₂]
  have hsep : 1 ≤ ‖(q₁ - y) - (q₂ - y)‖ := by
    rw [sub_sub_sub_cancel_right, ← dist_eq_norm]
    exact one_le_dist hX.minDist_eq (mem_nbδ.1 h₁).1 (mem_nbδ.1 h₂).1 hne
  have hs := pair_sym hn hu1 hu2 hsep
  have := c43_r_hi
  nlinarith [abs_nonneg (inner ℝ (q₁ - y) n - inner ℝ (q₂ - y) n)]

/-! ## Angles in the frame (private helpers) -/

private theorem c43_angle {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    ∃ ψ : ℝ, -π < ψ ∧ ψ ≤ π ∧ Real.cos ψ = a ∧ Real.sin ψ = b := by
  set z : ℂ := ⟨a, b⟩ with hzdef
  have hz : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp only [z]
    rw [show a * a + b * b = 1 by nlinarith, Real.sqrt_one]
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; norm_num at hz
  refine ⟨Complex.arg z, Complex.neg_pi_lt_arg z, Complex.arg_le_pi z, ?_, ?_⟩
  · rw [Complex.cos_arg hz0, hz, div_one]
  · rw [Complex.sin_arg, hz, div_one]

private theorem c43_cos_gt_half {d : ℝ} (h : |d| < π / 3) : 1 / 2 < Real.cos d := by
  rw [← Real.cos_abs, ← Real.cos_pi_div_three]
  exact Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg d) (by linarith [Real.pi_pos]) h

private theorem c43_chord (a b : ℝ) :
    (Real.cos a - Real.cos b) ^ 2 + (Real.sin a - Real.sin b) ^ 2 = 2 - 2 * Real.cos (a - b) := by
  rw [Real.cos_sub]
  linear_combination Real.sin_sq_add_cos_sq a + Real.sin_sq_add_cos_sq b

/-- A neighbour `q` distinct from a neighbour `q'` in the slot `ψ` (within `η`) satisfies
`⟨q − y, dirF n ψ⟩ ≤ 1/2 + η`. -/
private theorem c43_dot_slot (hX : Normal X) {y n q q' : Pt} (hq : q ∈ nbδ X y)
    (hq' : q' ∈ nbδ X y) (hne : q ≠ q') {s η : ℝ} (hs : Slot y n s η q') :
    inner ℝ (q - y) n * Real.cos s + inner ℝ (q - y) (perp n) * Real.sin s ≤ 1 / 2 + η := by
  have hu : ‖q - y‖ = 1 := by rw [← dist_eq_norm, dist_of_mem_nbδ hX hq]
  have hu' : ‖q' - y‖ = 1 := by rw [← dist_eq_norm, dist_of_mem_nbδ hX hq']
  have hsep : 1 ≤ ‖(q - y) - (q' - y)‖ := by
    rw [sub_sub_sub_cancel_right, ← dist_eq_norm]
    exact one_le_dist hX.minDist_eq (mem_nbδ.1 hq).1 (mem_nbδ.1 hq').1 hne
  have e := norm_sub_sq_real (q - y) (q' - y)
  rw [hu, hu'] at e
  have hi : inner ℝ (q - y) (q' - y) ≤ 1 / 2 := by
    nlinarith [norm_nonneg ((q - y) - (q' - y))]
  have h2 : -η ≤ inner ℝ (q - y) (q' - y - dirF n s) := by
    have := abs_real_inner_le_norm (q - y) (q' - y - dirF n s)
    rw [hu, one_mul] at this
    unfold Slot at hs
    linarith [(abs_le.1 this).1]
  have h3 : inner ℝ (q - y) (dirF n s) =
      inner ℝ (q - y) n * Real.cos s + inner ℝ (q - y) (perp n) * Real.sin s := by
    unfold dirF; rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]; ring
  have h4 : inner ℝ (q - y) (dirF n s) =
      inner ℝ (q - y) (q' - y) - inner ℝ (q - y) (q' - y - dirF n s) := by
    rw [inner_sub_right (q - y) (q' - y) (dirF n s)]; ring
  linarith

/-- Slot from an angle: `|ψ − s| ≤ η` gives `Slot y n s η q` when `q − y = dirF n ψ` in
coordinates. -/
private theorem c43_slot_of_angle {y n q : Pt} (hn : ‖n‖ = 1) {ψ s η : ℝ} (hη : 0 ≤ η)
    (hc : Real.cos ψ = inner ℝ (q - y) n) (hs : Real.sin ψ = inner ℝ (q - y) (perp n))
    (h : |ψ - s| ≤ η) : Slot y n s η q := by
  refine c43_slot_of hn hη ?_
  rw [← hc, ← hs, c43_chord]
  have h2 := Real.one_sub_sq_div_two_le_cos (x := ψ - s)
  have h3 : (ψ - s) ^ 2 ≤ η ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  linarith

/-- Reals `c`-separated in `[lo, hi]` number at most `(hi − lo)/c + 1`. -/
private theorem c43_count {ι : Type*} (T : Finset ι) (f : ι → ℝ) {c lo hi : ℝ} (hc : 0 < c)
    (hlh : lo ≤ hi) (hsep : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → c ≤ |f a - f b|)
    (hT : ∀ a ∈ T, lo ≤ f a ∧ f a ≤ hi) : (T.card : ℝ) * c ≤ hi - lo + c := by
  have hinj : Set.InjOn (fun a => f a / c) T := by
    intro a ha b hb h
    by_contra hne
    have h3 := hsep a ha b hb hne
    simp only at h
    have : f a = f b := by
      have := congrArg (· * c) h
      simpa [div_mul_cancel₀ _ hc.ne'] using this
    rw [this, sub_self, abs_zero] at h3
    linarith
  have hcard := card_le_of_sep_real (a := lo / c) (T.image fun a => f a / c)
    (hi / c) (by have := div_le_div_of_nonneg_right hlh hc.le; linarith)
    (by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hx
      exact ⟨div_le_div_of_nonneg_right (hT a ha).1 hc.le,
        div_le_div_of_nonneg_right (hT a ha).2 hc.le⟩)
    (by
      intro x hx x' hx' hne
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hx
      obtain ⟨b, hb, rfl⟩ := mem_image.1 hx'
      have hab : a ≠ b := by rintro rfl; exact hne rfl
      have h3 := hsep a ha b hb hab
      rw [← sub_div, abs_div, abs_of_pos hc, le_div_iff₀ hc, one_mul]
      exact h3)
  rw [card_image_of_injOn hinj] at hcard
  have e : (hi / c - lo / c + 1) * c = hi - lo + c := by
    rw [add_mul, sub_mul, div_mul_cancel₀ _ hc.ne', div_mul_cancel₀ _ hc.ne', one_mul]
  calc (T.card : ℝ) * c ≤ (hi / c - lo / c + 1) * c := mul_le_mul_of_nonneg_right hcard hc.le
    _ = hi - lo + c := e

private theorem c43_rot_eq (θ : ℝ) (x : Pt) : rot θ x = dirF x θ := by
  rw [pt_ext_iff]; refine ⟨?_, ?_⟩ <;> simp [rot, dirF, perp] <;> ring

/-- Two vectors with the same coordinates in a frame are equal. -/
private theorem c43_eq_of_coords {n v w : Pt} (hn : ‖n‖ = 1) (h1 : inner ℝ v n = inner ℝ w n)
    (h2 : inner ℝ v (perp n) = inner ℝ w (perp n)) : v = w := by
  have e := c43_sq hn (v - w)
  rw [inner_sub_left, inner_sub_left, h1, h2, sub_self, sub_self] at e
  have h0 : ‖v - w‖ ^ 2 = 0 := by rw [e]; ring
  exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0))

/-- **Four points on the upper arc**: four unit vectors pairwise `≥ 60°` apart with height
`> −1/49` sit within `0.021` (in angle) of the slots `−90°, −30°, 30°, 90°`. -/
private theorem c43_arc4 {y n : Pt} (hn : ‖n‖ = 1) (P : Finset Pt) (hcard : P.card = 4)
    (hu : ∀ q ∈ P, inner ℝ (q - y) n ^ 2 + inner ℝ (q - y) (perp n) ^ 2 = 1)
    (hsep : ∀ q ∈ P, ∀ q' ∈ P, q ≠ q' →
      1 ≤ (inner ℝ (q - y) n - inner ℝ (q' - y) n) ^ 2 +
        (inner ℝ (q - y) (perp n) - inner ℝ (q' - y) (perp n)) ^ 2)
    (hcone : ∀ q ∈ P, -(1 / 49) < inner ℝ (q - y) n) :
    ∀ j : ℕ, j < 4 → ∃ q ∈ P, Slot y n (-(π / 2) + (j : ℝ) * (π / 3)) (21 / 1000) q := by
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have hang : ∀ q ∈ P, ∃ ψ : ℝ, -π < ψ ∧ ψ ≤ π ∧ Real.cos ψ = inner ℝ (q - y) n ∧
      Real.sin ψ = inner ℝ (q - y) (perp n) := fun q hq => c43_angle (hu q hq)
  choose! ψ hψ1 hψ2 hψc hψs using hang
  have hsin : (1 : ℝ) / 49 < Real.sin (21 / 1000) := by
    have := Real.sin_gt_sub_cube (x := 21 / 1000) (by norm_num)
    linarith [show (1 : ℝ) / 49 < 21 / 1000 - (21 / 1000) ^ 3 / 6 by norm_num]
  have hbound : ∀ q ∈ P, |ψ q| < π / 2 + 21 / 1000 := by
    intro q hq
    by_contra hc
    push Not at hc
    have habs : |ψ q| ≤ π := abs_le.2 ⟨by linarith [hψ1 q hq], hψ2 q hq⟩
    have h1 := Real.cos_le_cos_of_nonneg_of_le_pi
      (by positivity : (0 : ℝ) ≤ π / 2 + 21 / 1000) habs hc
    rw [Real.cos_abs, hψc q hq, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two] at h1
    have := hcone q hq
    linarith
  have hsepψ : ∀ q ∈ P, ∀ q' ∈ P, q ≠ q' → π / 3 ≤ |ψ q - ψ q'| := by
    intro q hq q' hq' hne
    by_contra hc
    push Not at hc
    have h1 := c43_cos_gt_half hc
    have h2 := hsep q hq q' hq' hne
    rw [← hψc q hq, ← hψc q' hq', ← hψs q hq, ← hψs q' hq', c43_chord] at h2
    linarith
  have hc3 : (0 : ℝ) < π / 3 := by positivity
  -- separated angles in an interval
  have hcount : ∀ (T : Finset Pt) (lo hi : ℝ), T ⊆ P → lo ≤ hi →
      (∀ q ∈ T, lo ≤ ψ q ∧ ψ q ≤ hi) → (T.card : ℝ) * (π / 3) ≤ hi - lo + π / 3 := by
    intro T lo hi hTP hlh hT
    have hinj : Set.InjOn (fun q => ψ q / (π / 3)) T := by
      intro q hq q' hq' h
      by_contra hne
      have h3 := hsepψ q (hTP hq) q' (hTP hq') hne
      simp only at h
      have : ψ q = ψ q' := by
        have := congrArg (· * (π / 3)) h
        simpa [div_mul_cancel₀ _ hc3.ne'] using this
      rw [this, sub_self, abs_zero] at h3
      linarith
    have hcard := card_le_of_sep_real (a := lo / (π / 3)) (T.image fun q => ψ q / (π / 3))
      (hi / (π / 3)) (by have := div_le_div_of_nonneg_right hlh hc3.le; linarith)
      (by
        intro x hx
        obtain ⟨q, hq, rfl⟩ := mem_image.1 hx
        exact ⟨div_le_div_of_nonneg_right (hT q hq).1 hc3.le,
          div_le_div_of_nonneg_right (hT q hq).2 hc3.le⟩)
      (by
        intro x hx x' hx' hne
        obtain ⟨q, hq, rfl⟩ := mem_image.1 hx
        obtain ⟨q', hq', rfl⟩ := mem_image.1 hx'
        have hqq : q ≠ q' := by rintro rfl; exact hne rfl
        have h3 := hsepψ q (hTP hq) q' (hTP hq') hqq
        rw [← sub_div, abs_div, abs_of_pos hc3, le_div_iff₀ hc3, one_mul]
        exact h3)
    rw [card_image_of_injOn hinj] at hcard
    have e : (hi / (π / 3) - lo / (π / 3) + 1) * (π / 3) = hi - lo + π / 3 := by
      rw [add_mul, sub_mul, div_mul_cancel₀ _ hc3.ne', div_mul_cancel₀ _ hc3.ne', one_mul]
    calc (T.card : ℝ) * (π / 3) ≤ (hi / (π / 3) - lo / (π / 3) + 1) * (π / 3) :=
          mul_le_mul_of_nonneg_right hcard hc3.le
      _ = hi - lo + π / 3 := e
  -- the rank of `q` among the angles
  obtain ⟨k, hk⟩ : ∃ k : Pt → ℕ, ∀ q, k q = (P.filter (fun q' => ψ q' < ψ q)).card :=
    ⟨_, fun q => rfl⟩
  have hB : ∀ q ∈ P, |ψ q - (-(π / 2) + (k q : ℝ) * (π / 3))| ≤ 21 / 1000 := by
    intro q hq
    have hb := abs_lt.1 (hbound q hq)
    have hLc : k q + 1 ≤ (P.filter (fun q' => ψ q' ≤ ψ q)).card := by
      have hsub : insert q (P.filter (fun q' => ψ q' < ψ q)) ⊆
          P.filter (fun q' => ψ q' ≤ ψ q) := by
        intro x hx
        rcases mem_insert.1 hx with rfl | hx
        · exact mem_filter.2 ⟨hq, le_refl _⟩
        · have := mem_filter.1 hx; exact mem_filter.2 ⟨this.1, this.2.le⟩
      have hnm : q ∉ P.filter (fun q' => ψ q' < ψ q) := fun h => lt_irrefl _ (mem_filter.1 h).2
      have := card_le_card hsub
      rwa [card_insert_of_notMem hnm, ← hk] at this
    have hL := hcount (P.filter (fun q' => ψ q' ≤ ψ q)) (-(π / 2 + 21 / 1000)) (ψ q)
      (filter_subset _ _) (by linarith)
      (fun x hx => ⟨(abs_lt.1 (hbound x (mem_filter.1 hx).1)).1.le, (mem_filter.1 hx).2⟩)
    have hHc : (P.filter (fun q' => ¬ ψ q' < ψ q)).card + k q = 4 := by
      have := card_filter_add_card_filter_not (s := P) (fun q' => ψ q' < ψ q)
      rw [hcard, ← hk] at this; omega
    have hH := hcount (P.filter (fun q' => ¬ ψ q' < ψ q)) (ψ q) (π / 2 + 21 / 1000)
      (filter_subset _ _) (by linarith)
      (fun x hx => ⟨not_lt.1 (mem_filter.1 hx).2,
        (abs_lt.1 (hbound x (mem_filter.1 hx).1)).2.le⟩)
    have h1 : ((k q : ℕ) : ℝ) + 1 ≤ ((P.filter (fun q' => ψ q' ≤ ψ q)).card : ℝ) := by
      exact_mod_cast hLc
    have h2 : ((P.filter (fun q' => ¬ ψ q' < ψ q)).card : ℝ) = 4 - k q := by
      have : (((P.filter (fun q' => ¬ ψ q' < ψ q)).card + k q : ℕ) : ℝ) = 4 := by
        exact_mod_cast hHc
      push_cast at this; linarith
    rw [h2] at hH
    have h3 := mul_le_mul_of_nonneg_right h1 hc3.le
    rw [abs_le]; constructor <;> nlinarith
  have hkP : ∀ q ∈ P, k q ∈ range 4 := by
    intro q hq
    rw [mem_range, hk]
    have : (P.filter (fun q' => ψ q' < ψ q)).card < P.card :=
      card_lt_card (filter_ssubset.2 ⟨q, hq, lt_irrefl _⟩)
    omega
  have hinj : Set.InjOn k P := by
    intro q hq q' hq' h
    by_contra hne
    obtain ⟨a1, a2⟩ := abs_le.1 (hB q hq)
    obtain ⟨b1, b2⟩ := abs_le.1 (hB q' hq')
    have h3 := hsepψ q hq q' hq' hne
    rw [h] at a1 a2
    have : |ψ q - ψ q'| ≤ 42 / 1000 := by rw [abs_le]; constructor <;> linarith
    linarith
  intro j hj
  obtain ⟨q, hq, hqj⟩ := Finset.surjOn_of_injOn_of_card_le k
    (fun q hq => mem_coe.2 (hkP q (mem_coe.1 hq))) hinj (by rw [card_range, hcard])
    (mem_coe.2 (mem_range.2 hj))
  have hq' : q ∈ P := mem_coe.1 hq
  have h1 := hB q hq'
  rw [hqj] at h1
  exact ⟨q, hq', c43_slot_of_angle hn (by norm_num) (hψc q hq') (hψs q hq') h1⟩

/-! ## The exact hexagon -/

/-- **Exact hexagon**: if `y` has six `δ`-neighbours, they form a regular hexagon: the set of
neighbours is invariant under rotation by `60°` about `y`.

TODO: none — proved.
What's missing: write `q − y = dirVec(θ_q)`; distinct neighbours are `≥ 1` apart, i.e. the
angles are pairwise `≥ π/3` apart on the circle; six such angles have all six consecutive gaps
`≥ π/3` summing to `2π`, so every gap equals `π/3`; hence `rot (π/3)` maps each neighbour to
the next one (`rot`, `dirVec_add`).
Acceptance: no `sorry`.
Depends on: `exists_angle`, `rot`, `one_le_dist`, `dist_of_mem_nbδ`. Difficulty M–L. -/
theorem hexagon_exact (hX : Normal X) {y : Pt} (h6 : degδ X y = 6) :
    ∀ q ∈ nbδ X y, y + rot (π / 3) (q - y) ∈ nbδ X y := by
  intro q hq
  have hπ := Real.pi_pos
  have hn : ‖q - y‖ = 1 := by rw [← dist_eq_norm, dist_of_mem_nbδ hX hq]
  set n := q - y with hndef
  set P := (nbδ X y).erase q with hP
  have hPc : P.card = 5 := by
    have : (nbδ X y).card = 6 := h6
    rw [hP, card_erase_of_mem hq, this]
  have hPm : ∀ a ∈ P, a ∈ nbδ X y ∧ a ≠ q := fun a ha => ⟨(mem_erase.1 ha).2, (mem_erase.1 ha).1⟩
  have hang : ∀ a ∈ P, ∃ φ : ℝ, 0 ≤ φ ∧ φ < 2 * π ∧ Real.cos φ = inner ℝ (a - y) n ∧
      Real.sin φ = inner ℝ (a - y) (perp n) := by
    intro a ha
    obtain ⟨ψ, h1, h2, hc, hs⟩ := c43_angle (c43_unit hX hn (hPm a ha).1)
    rcases le_or_gt 0 ψ with h | h
    · exact ⟨ψ, h, by linarith, hc, hs⟩
    · refine ⟨ψ + 2 * π, by linarith, by linarith, ?_, ?_⟩
      · rw [Real.cos_add_two_pi, hc]
      · rw [Real.sin_add_two_pi, hs]
  choose! φ hφ0 hφ1 hφc hφs using hang
  have hqZ : inner ℝ (q - y) n = 1 := by
    rw [← hndef, real_inner_self_eq_norm_sq, hn]; norm_num
  have hqX : inner ℝ (q - y) (perp n) = 0 := by rw [← hndef]; exact c43_np n
  -- every other neighbour is at angle in `[π/3, 5π/3]`
  have hrange : ∀ a ∈ P, π / 3 ≤ φ a ∧ φ a ≤ 5 * π / 3 := by
    intro a ha
    have h1 := c43_sep hX hn (hPm a ha).1 hq (hPm a ha).2
    have hu := c43_unit hX hn (hPm a ha).1
    rw [hqZ, hqX] at h1
    have hc : Real.cos (φ a) ≤ 1 / 2 := by rw [hφc a ha]; nlinarith
    constructor
    · by_contra h
      push Not at h
      have := c43_cos_gt_half (d := φ a) (by rw [abs_of_nonneg (hφ0 a ha)]; exact h)
      linarith
    · by_contra h
      push Not at h
      have := c43_cos_gt_half (d := φ a - 2 * π)
        (by rw [abs_lt]; constructor <;> linarith [hφ1 a ha])
      rw [Real.cos_sub_two_pi] at this
      linarith
  have hsepφ : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → π / 3 ≤ |φ a - φ b| := by
    intro a ha b hb hne
    by_contra hc
    push Not at hc
    have h1 := c43_cos_gt_half hc
    have h2 := c43_sep hX hn (hPm a ha).1 (hPm b hb).1 hne
    rw [← hφc a ha, ← hφc b hb, ← hφs a ha, ← hφs b hb, c43_chord] at h2
    linarith
  have hne : P.Nonempty := by rw [← card_pos, hPc]; norm_num
  obtain ⟨m, hm, hmin⟩ := P.exists_min_image φ hne
  have hcnt := c43_count P φ (c := π / 3) (lo := φ m) (hi := 5 * π / 3) (by positivity)
    (hrange m hm).2 hsepφ (fun a ha => ⟨hmin a ha, (hrange a ha).2⟩)
  rw [hPc] at hcnt
  have hφm : φ m = π / 3 := by
    have := (hrange m hm).1
    push_cast at hcnt
    linarith
  have hrot : rot (π / 3) n = m - y := by
    rw [c43_rot_eq]
    apply c43_eq_of_coords hn
    · rw [c43_dirF_n hn, ← hφc m hm, hφm]
    · rw [c43_dirF_p hn, ← hφs m hm, hφm]
  rw [hrot, show y + (m - y) = m by abel]
  exact (hPm m hm).1

/-! ## Hexagon toolkit (private helpers for Lemma H) -/

private theorem c43_sq_le {t c : ℝ} (h : |t| ≤ c) : t ^ 2 ≤ c ^ 2 := by
  rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg t) h 2

private theorem c43_rot_dirF (φ θ : ℝ) (n : Pt) : rot φ (dirF n θ) = dirF n (θ + φ) := by
  rw [pt_ext_iff]
  refine ⟨?_, ?_⟩ <;> simp [rot, dirF, perp, Real.cos_add, Real.sin_add] <;> ring

private theorem c43_rot_sub (φ : ℝ) (a b : Pt) : rot φ (a - b) = rot φ a - rot φ b := by
  rw [pt_ext_iff]; refine ⟨?_, ?_⟩ <;> simp [rot] <;> ring

private theorem c43_rot_rot (α β : ℝ) (x : Pt) : rot α (rot β x) = rot (α + β) x := by
  rw [pt_ext_iff]; refine ⟨?_, ?_⟩ <;> simp [rot, Real.cos_add, Real.sin_add] <;> ring

private theorem c43_rot_norm (φ : ℝ) (x : Pt) : ‖rot φ x‖ = ‖x‖ := by
  have h : ‖rot φ x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [norm_sq_coord, norm_sq_coord]
    have e0 : rot φ x 0 = Real.cos φ * x 0 - Real.sin φ * x 1 := by simp [rot]
    have e1 : rot φ x 1 = Real.sin φ * x 0 + Real.cos φ * x 1 := by simp [rot]
    rw [e0, e1]
    linear_combination (x 0 ^ 2 + x 1 ^ 2) * Real.sin_sq_add_cos_sq φ
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

private theorem c43_perp_inner (w n : Pt) :
    inner ℝ (perp w) n = -inner ℝ w (perp n) ∧ inner ℝ (perp w) (perp n) = inner ℝ w n := by
  constructor <;> simp [inner_pt, perp] <;> ring

/-- The rotation by `60°` about `y`. -/
private def c43g (y x : Pt) : Pt := y + rot (π / 3) (x - y)

private theorem c43g_mem (hX : Normal X) {y x : Pt} (h6 : degδ X y = 6) (hx : x ∈ nbδ X y) :
    c43g y x ∈ nbδ X y :=
  hexagon_exact hX h6 x hx

private theorem c43g_slot {y n x : Pt} {θ η : ℝ} (h : Slot y n θ η x) :
    Slot y n (θ + π / 3) η (c43g y x) := by
  unfold Slot at h ⊢
  have e : c43g y x - y - dirF n (θ + π / 3) = rot (π / 3) (x - y - dirF n θ) := by
    rw [c43_rot_sub (π / 3) (x - y) (dirF n θ), c43_rot_dirF]; unfold c43g; abel
  rw [e, c43_rot_norm]; exact h

private theorem c43g3 (y x : Pt) : c43g y (c43g y (c43g y x)) = y - (x - y) := by
  unfold c43g
  simp only [add_sub_cancel_left]
  rw [c43_rot_rot, c43_rot_rot, show π / 3 + π / 3 + π / 3 = π by ring]
  have : rot π (x - y) = -(x - y) := by
    rw [pt_ext_iff]; refine ⟨?_, ?_⟩ <;> simp [rot]
  rw [this, ← sub_eq_add_neg]

private theorem c43g_coords {n : Pt} (y x : Pt) :
    inner ℝ (c43g y x - y) n =
        1 / 2 * inner ℝ (x - y) n - √3 / 2 * inner ℝ (x - y) (perp n) ∧
      inner ℝ (c43g y x - y) (perp n) =
        √3 / 2 * inner ℝ (x - y) n + 1 / 2 * inner ℝ (x - y) (perp n) := by
  have e : c43g y x - y = Real.sin (π / 3) • perp (x - y) + Real.cos (π / 3) • (x - y) := by
    simp only [c43g, add_sub_cancel_left, c43_rot_eq, dirF]
  rw [e, Real.sin_pi_div_three, Real.cos_pi_div_three]
  obtain ⟨p1, p2⟩ := c43_perp_inner (x - y) n
  constructor
  · rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, p1]; ring
  · rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, p2]

private theorem c43g2_coords {n : Pt} (y x : Pt) :
    inner ℝ (c43g y (c43g y x) - y) n =
        -(1 / 2) * inner ℝ (x - y) n - √3 / 2 * inner ℝ (x - y) (perp n) ∧
      inner ℝ (c43g y (c43g y x) - y) (perp n) =
        √3 / 2 * inner ℝ (x - y) n - 1 / 2 * inner ℝ (x - y) (perp n) := by
  obtain ⟨a1, a2⟩ := c43g_coords (n := n) y x
  obtain ⟨b1, b2⟩ := c43g_coords (n := n) y (c43g y x)
  rw [b1, b2, a1, a2]
  constructor
  · linear_combination (-(inner ℝ (x - y) n) / 4) * c43_r_sq
  · linear_combination (-(inner ℝ (x - y) (perp n)) / 4) * c43_r_sq

/-- Adjacent hexagon vertices are at distance `1`. -/
private theorem c43g_dist (hX : Normal X) {y n x : Pt} (hn : ‖n‖ = 1) (hx : x ∈ nbδ X y) :
    dist x (c43g y x) = 1 := by
  obtain ⟨g1, g2⟩ := c43g_coords (n := n) y x
  have hu := c43_unit hX hn hx
  have e := c43_sq hn ((x - y) - (c43g y x - y))
  rw [inner_sub_left (x - y) (c43g y x - y) n,
    inner_sub_left (x - y) (c43g y x - y) (perp n), g1, g2] at e
  have h1 : ‖(x - y) - (c43g y x - y)‖ ^ 2 = 1 ^ 2 := by
    rw [e]
    linear_combination
      ((inner ℝ (x - y) n ^ 2 + inner ℝ (x - y) (perp n) ^ 2) / 4) * c43_r_sq + hu
  rw [sub_sub_sub_cancel_right] at h1
  rw [dist_eq_norm]
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 h1

private theorem c43_slot_congr {y n q : Pt} {θ θ' η : ℝ} (h : Slot y n θ η q)
    (hc : Real.cos θ = Real.cos θ') (hs : Real.sin θ = Real.sin θ') : Slot y n θ' η q := by
  unfold Slot dirF at *; rw [← hc, ← hs]; exact h

private theorem c43_slot_fix {y n q : Pt} {θ θ' η η' : ℝ} (h : Slot y n θ η q) (hθ : θ = θ')
    (hη : η ≤ η') : Slot y n θ' η' q := by
  subst hθ; exact le_trans h hη

private theorem c43_slot_pi {y n q : Pt} {η : ℝ} (h : Slot y n π η q) : ‖q - y + n‖ ≤ η := by
  unfold Slot dirF at h
  rwa [Real.sin_pi, Real.cos_pi, zero_smul, zero_add, neg_one_smul, sub_neg_eq_add] at h

/-- Slot at an angle `θ = θ' + 2πk`, with the coordinates. -/
private theorem c43_ZX {y n q : Pt} (hn : ‖n‖ = 1) {θ θ' η C S : ℝ} (k : ℤ)
    (h : Slot y n θ η q) (hθ : θ = θ' + k * (2 * π))
    (hcs : Real.cos θ' = C ∧ Real.sin θ' = S) :
    Slot y n θ' η q ∧ C - η ≤ inner ℝ (q - y) n ∧ inner ℝ (q - y) n ≤ C + η ∧
      S - η ≤ inner ℝ (q - y) (perp n) ∧ inner ℝ (q - y) (perp n) ≤ S + η := by
  have hs : Slot y n θ' η q := c43_slot_congr h (by rw [hθ, Real.cos_add_int_mul_two_pi])
    (by rw [hθ, Real.sin_add_int_mul_two_pi])
  obtain ⟨h1, h2⟩ := c43_slot_coords hn hs
  rw [hcs.1] at h1
  rw [hcs.2] at h2
  obtain ⟨a1, a2⟩ := abs_le.1 h1
  obtain ⟨b1, b2⟩ := abs_le.1 h2
  exact ⟨hs, by linarith, by linarith, by linarith, by linarith⟩

private theorem c43_cs_0 : Real.cos 0 = 1 ∧ Real.sin 0 = 0 := ⟨Real.cos_zero, Real.sin_zero⟩
private theorem c43_cs_p6 : Real.cos (π / 6) = √3 / 2 ∧ Real.sin (π / 6) = 1 / 2 :=
  ⟨Real.cos_pi_div_six, Real.sin_pi_div_six⟩
private theorem c43_cs_m6 : Real.cos (-(π / 6)) = √3 / 2 ∧ Real.sin (-(π / 6)) = -(1 / 2) :=
  ⟨by rw [Real.cos_neg, Real.cos_pi_div_six], by rw [Real.sin_neg, Real.sin_pi_div_six]⟩
private theorem c43_cs_p3 : Real.cos (π / 3) = 1 / 2 ∧ Real.sin (π / 3) = √3 / 2 :=
  ⟨Real.cos_pi_div_three, Real.sin_pi_div_three⟩
private theorem c43_cs_m3 : Real.cos (-(π / 3)) = 1 / 2 ∧ Real.sin (-(π / 3)) = -(√3 / 2) :=
  ⟨by rw [Real.cos_neg, Real.cos_pi_div_three], by rw [Real.sin_neg, Real.sin_pi_div_three]⟩
private theorem c43_cs_p2 : Real.cos (π / 2) = 0 ∧ Real.sin (π / 2) = 1 :=
  ⟨Real.cos_pi_div_two, Real.sin_pi_div_two⟩
private theorem c43_cs_m2 : Real.cos (-(π / 2)) = 0 ∧ Real.sin (-(π / 2)) = -1 :=
  ⟨by rw [Real.cos_neg, Real.cos_pi_div_two], by rw [Real.sin_neg, Real.sin_pi_div_two]⟩
private theorem c43_cs_p23 : Real.cos (π - π / 3) = -(1 / 2) ∧ Real.sin (π - π / 3) = √3 / 2 :=
  ⟨by rw [Real.cos_pi_sub, Real.cos_pi_div_three], by rw [Real.sin_pi_sub, Real.sin_pi_div_three]⟩
private theorem c43_cs_m23 :
    Real.cos (-(π - π / 3)) = -(1 / 2) ∧ Real.sin (-(π - π / 3)) = -(√3 / 2) :=
  ⟨by rw [Real.cos_neg, Real.cos_pi_sub, Real.cos_pi_div_three],
    by rw [Real.sin_neg, Real.sin_pi_sub, Real.sin_pi_div_three]⟩
private theorem c43_cs_p56 : Real.cos (π - π / 6) = -(√3 / 2) ∧ Real.sin (π - π / 6) = 1 / 2 :=
  ⟨by rw [Real.cos_pi_sub, Real.cos_pi_div_six], by rw [Real.sin_pi_sub, Real.sin_pi_div_six]⟩
private theorem c43_cs_m56 :
    Real.cos (-(π - π / 6)) = -(√3 / 2) ∧ Real.sin (-(π - π / 6)) = -(1 / 2) :=
  ⟨by rw [Real.cos_neg, Real.cos_pi_sub, Real.cos_pi_div_six],
    by rw [Real.sin_neg, Real.sin_pi_sub, Real.sin_pi_div_six]⟩
private theorem c43_cs_pi : Real.cos π = -1 ∧ Real.sin π = 0 := ⟨Real.cos_pi, Real.sin_pi⟩

/-- **Hexagon enumeration**: at a point of degree `6` the neighbours are the six rotations of
any one of them by multiples of `60°`. -/
private theorem c43_hex_enum (hX : Normal X) {y a : Pt} (h6 : degδ X y = 6)
    (ha : a ∈ nbδ X y) :
    ∀ x ∈ nbδ X y, x = a ∨ x = c43g y a ∨ x = c43g y (c43g y a) ∨
      x = c43g y (c43g y (c43g y a)) ∨ x = c43g y (c43g y (c43g y (c43g y a))) ∨
      x = c43g y (c43g y (c43g y (c43g y (c43g y a)))) := by
  intro x hx
  have hπ := Real.pi_pos
  have he : ‖a - y‖ = 1 := by rw [← dist_eq_norm, dist_of_mem_nbδ hX ha]
  have m1 := c43g_mem hX h6 ha
  have m2 := c43g_mem hX h6 m1
  have m3 := c43g_mem hX h6 m2
  have m4 := c43g_mem hX h6 m3
  have m5 := c43g_mem hX h6 m4
  have s0 : Slot y (a - y) 0 0 a := by
    unfold Slot dirF
    rw [Real.sin_zero, Real.cos_zero, zero_smul, one_smul, zero_add, sub_self, norm_zero]
  have s1 := c43g_slot s0
  have s2 := c43g_slot s1
  have s3 := c43g_slot s2
  have s4 := c43g_slot s3
  have s5 := c43g_slot s4
  obtain ⟨ψ, h1, h2, hc, hs⟩ := c43_angle (c43_unit hX he hx)
  have key : ∀ R ∈ nbδ X y, ∀ θ : ℝ, Slot y (a - y) θ 0 R → 1 / 2 < Real.cos (ψ - θ) →
      x = R := by
    intro R hR θ hsl hlt
    by_contra hne
    obtain ⟨c1, c2⟩ := c43_slot_coords he hsl
    have hZ : inner ℝ (R - y) (a - y) = Real.cos θ := by
      have := abs_nonpos_iff.1 c1; linarith
    have hX' : inner ℝ (R - y) (perp (a - y)) = Real.sin θ := by
      have := abs_nonpos_iff.1 c2; linarith
    have hsep := c43_sep hX he hx hR hne
    rw [hZ, hX', ← hc, ← hs, c43_chord] at hsep
    linarith
  have gt2 : ∀ d : ℝ, |d + 2 * π| < π / 3 → 1 / 2 < Real.cos d := by
    intro d h; rw [← Real.cos_add_two_pi]; exact c43_cos_gt_half h
  rcases lt_or_ge ψ (-(5 * π / 6)) with c | c
  · right; right; right; left
    exact key _ m3 _ s3 (gt2 _ (by rw [abs_lt]; constructor <;> linarith))
  rcases lt_or_ge ψ (-(π / 2)) with c' | c'
  · right; right; right; right; left
    exact key _ m4 _ s4 (gt2 _ (by rw [abs_lt]; constructor <;> linarith))
  rcases lt_or_ge ψ (-(π / 6)) with c'' | c''
  · right; right; right; right; right
    exact key _ m5 _ s5 (gt2 _ (by rw [abs_lt]; constructor <;> linarith))
  rcases lt_or_ge ψ (π / 6) with d | d
  · left
    exact key _ ha _ s0 (c43_cos_gt_half (by rw [abs_lt]; constructor <;> linarith))
  rcases lt_or_ge ψ (π / 2) with d' | d'
  · right; left
    exact key _ m1 _ s1 (c43_cos_gt_half (by rw [abs_lt]; constructor <;> linarith))
  rcases lt_or_ge ψ (5 * π / 6) with d'' | d''
  · right; right; left
    exact key _ m2 _ s2 (c43_cos_gt_half (by rw [abs_lt]; constructor <;> linarith))
  · right; right; right; left
    exact key _ m3 _ s3 (c43_cos_gt_half (by rw [abs_lt]; constructor <;> linarith))

/-- **Pinning** (algebra): if the component of the unit vector `(u, v)` orthogonal to the unit
vector `(c, s)` is `≤ δ`, then `(u, v)` is within `η` (`2δ² ≤ η²`) of `±(c, s)`. -/
private theorem c43_pin_alg {u v c s δ η : ℝ} (hu : u ^ 2 + v ^ 2 = 1) (hcs : s ^ 2 + c ^ 2 = 1)
    (hδ : 2 * δ ^ 2 ≤ η ^ 2) (hQ : |-s * u + c * v| ≤ δ) :
    (u - c) ^ 2 + (v - s) ^ 2 ≤ η ^ 2 ∨ (u + c) ^ 2 + (v + s) ^ 2 ≤ η ^ 2 := by
  have hPQ : (c * u + s * v) ^ 2 + (-s * u + c * v) ^ 2 = 1 := by
    linear_combination (u ^ 2 + v ^ 2) * hcs + hu
  have hQ2 := c43_sq_le hQ
  have hP1 : c * u + s * v ≤ 1 := by nlinarith [sq_nonneg (-s * u + c * v)]
  have hPm1 : -1 ≤ c * u + s * v := by nlinarith [sq_nonneg (-s * u + c * v)]
  rcases le_total 0 (c * u + s * v) with h0 | h0
  · left
    have e : (u - c) ^ 2 + (v - s) ^ 2 = 2 - 2 * (c * u + s * v) := by
      linear_combination hu + hcs
    rw [e]; nlinarith [mul_nonneg h0 (sub_nonneg.2 hP1)]
  · right
    have e : (u + c) ^ 2 + (v + s) ^ 2 = 2 + 2 * (c * u + s * v) := by
      linear_combination hu + hcs
    rw [e]; nlinarith [mul_nonneg (neg_nonneg.2 h0) (by linarith : (0 : ℝ) ≤ 1 + (c * u + s * v))]

/-- **Pinning**: a unit neighbour whose component orthogonal to the slot `θ` is `≤ δ` lies within
`η` (`2δ² ≤ η²`) of the slot `θ` or of the antipodal slot `θ + π`. -/
private theorem c43_pin {y n q : Pt} (hn : ‖n‖ = 1) {θ δ η : ℝ} (hη : 0 ≤ η)
    (hδ : 2 * δ ^ 2 ≤ η ^ 2)
    (hu : inner ℝ (q - y) n ^ 2 + inner ℝ (q - y) (perp n) ^ 2 = 1)
    (hQ : |-(Real.sin θ) * inner ℝ (q - y) n + Real.cos θ * inner ℝ (q - y) (perp n)| ≤ δ) :
    Slot y n θ η q ∨ Slot y n (θ + π) η q := by
  rcases c43_pin_alg hu (Real.sin_sq_add_cos_sq θ) hδ hQ with h | h
  · exact Or.inl (c43_slot_of hn hη h)
  · refine Or.inr (c43_slot_of hn hη ?_)
    rw [Real.cos_add_pi, Real.sin_add_pi, sub_neg_eq_add, sub_neg_eq_add]; exact h

private theorem c43_S_gt (hX : Normal X) {y n q : Pt} (hF : Frame43 X y n) (hq : q ∈ nbδ X y)
    (hS : q ∈ Sset X) : -(1 / 49) < inner ℝ (q - y) n := by
  have h1 := c43_S_low hX hF hq hS
  have h2 := c43_abs_le_one (c43_unit hX hF.unit hq)
  have := hF.depth_pos
  linarith

private theorem c43_KD (hX : Normal X) {y n p z : Pt} (hF : Frame43 X y n) (hp : p ∈ nbδ X y)
    (hpD : p ∉ Dset X) (hz : z ∈ nbδ X y) (hzD : z ∈ Dset X) :
    inner ℝ (p - y) n - 1 / 49 < inner ℝ (z - y) n := by
  have h1 := c43_K_top hF hp hpD
  have h2 := c43_D_low hX hF hz hzD
  have h3 := c43_abs_le_one (c43_unit hX hF.unit hz)
  have := c43_tgap_pos hX
  linarith

/-- Three K-row neighbours are impossible (Lemma P). -/
private theorem c43_three_K (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) {a b c : Pt}
    (ha : a ∈ nbδ X y) (hb : b ∈ nbδ X y) (hc : c ∈ nbδ X y) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hSa : a ∈ Sset X) (hDa : a ∉ Dset X) (hSb : b ∈ Sset X) (hDb : b ∉ Dset X)
    (hSc : c ∈ Sset X) (hDc : c ∉ Dset X) : False := by
  obtain ⟨z1, -⟩ := pair_K hX hF ha hb hab hSa hDa hSb hDb
  obtain ⟨-, x2⟩ := pair_K hX hF ha hc hac hSa hDa hSc hDc
  obtain ⟨-, x3⟩ := pair_K hX hF hb hc hbc hSb hDb hSc hDc
  have hs := c43_sep hX hF.unit ha hb hab
  obtain ⟨x2a, x2b⟩ := abs_le.1 x2
  obtain ⟨x3a, x3b⟩ := abs_le.1 x3
  have hx : |inner ℝ (a - y) (perp n) - inner ℝ (b - y) (perp n)| ≤ 2 / 25 := by
    rw [abs_le]; constructor <;> linarith
  have h1 := c43_sq_le z1
  have h2 := c43_sq_le hx
  linarith

/-- Three D-neighbours are impossible (Lemma P). -/
private theorem c43_three_D (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) {a b c : Pt}
    (ha : a ∈ nbδ X y) (hb : b ∈ nbδ X y) (hc : c ∈ nbδ X y) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hDa : a ∈ Dset X) (hDb : b ∈ Dset X) (hDc : c ∈ Dset X) : False := by
  obtain ⟨z1, -⟩ := pair_D hX hF ha hb hab hDa hDb
  obtain ⟨-, x2⟩ := pair_D hX hF ha hc hac hDa hDc
  obtain ⟨-, x3⟩ := pair_D hX hF hb hc hbc hDb hDc
  have hs := c43_sep hX hF.unit ha hb hab
  obtain ⟨x2a, x2b⟩ := abs_le.1 x2
  obtain ⟨x3a, x3b⟩ := abs_le.1 x3
  have hx : |inner ℝ (a - y) (perp n) - inner ℝ (b - y) (perp n)| ≤ 4 / 25 := by
    rw [abs_le]; constructor <;> linarith
  have h1 := c43_sq_le z1
  have h2 := c43_sq_le hx
  linarith

/-! ### Lemma H: the six pair cases

Notation: `a` and `b` are the two same-kind `S`-neighbours, `b` is the hexagon vertex `j` steps
(of `60°`) after `a` (`j ∈ {1, 2, 3}` after swapping `a, b`), `c` is the third `S`-neighbour.
The mirror estimate pins `a` (`c43_pin`), the hexagon (`c43g_slot`) pins all other vertices. -/

/-- K pair at `±30°` (`j = 1`): the D-point would need height `≈ 0.85`; impossible. -/
private theorem c43_coreK1 (hX : Normal X) {y n : Pt} (hF : Frame43 X y n)
    (hd : degδ X y = 6) (_hm : mS X y = 3) {a c : Pt} (ha : a ∈ nbδ X y) (hc : c ∈ nbδ X y)
    (hab : a ≠ c43g y a) (hac : a ≠ c) (hbc : c43g y a ≠ c) (hSa : a ∈ Sset X)
    (hDa : a ∉ Dset X) (hSb : c43g y a ∈ Sset X) (hDb : c43g y a ∉ Dset X)
    (_hSc : c ∈ Sset X) (hDc : c ∈ Dset X) : False := by
  have hn := hF.unit
  have hr := c43_r_lo
  have m1 := c43g_mem hX hd ha
  obtain ⟨g1, -⟩ := c43g_coords (n := n) y a
  obtain ⟨hPa, hPb⟩ := abs_le.1 (pair_K hX hF ha m1 hab hSa hDa hSb hDb).1
  have hQ : |-(Real.sin (-(π / 6))) * inner ℝ (a - y) n +
      Real.cos (-(π / 6)) * inner ℝ (a - y) (perp n)| ≤ 1 / 49 := by
    rw [c43_cs_m6.1, c43_cs_m6.2, abs_le]; constructor <;> linarith
  have hSa' := c43_S_gt hX hF ha hSa
  rcases Or.symm <| c43_pin (η := 3 / 100) hn (by norm_num) (by norm_num) (c43_unit hX hn ha) hQ
    with sa | sa
  · obtain ⟨-, -, za, -, -⟩ := c43_ZX hn 0 sa (θ' := π - π / 6) (by push_cast; ring) c43_cs_p56
    linarith
  obtain ⟨-, za, -, -, -⟩ := c43_ZX hn 0 sa (θ' := -(π / 6)) (by push_cast; ring) c43_cs_m6
  have s1 := c43g_slot sa
  have s2 := c43g_slot s1
  have s3 := c43g_slot s2
  have s4 := c43g_slot s3
  have s5 := c43g_slot s4
  have hKD := c43_KD hX hF ha hDa hc hDc
  rcases c43_hex_enum hX hd ha c hc with h | h | h | h | h | h
  · exact hac h.symm
  · exact hbc h.symm
  · subst h
    obtain ⟨-, -, z, -, -⟩ := c43_ZX hn 0 s2 (θ' := π / 2) (by push_cast; ring) c43_cs_p2
    linarith
  · subst h
    obtain ⟨-, -, z, -, -⟩ := c43_ZX hn 0 s3 (θ' := π - π / 6) (by push_cast; ring) c43_cs_p56
    linarith
  · subst h
    obtain ⟨-, -, z, -, -⟩ :=
      c43_ZX hn 1 s4 (θ' := -(π - π / 6)) (by push_cast; ring) c43_cs_m56
    linarith
  · subst h
    obtain ⟨-, -, z, -, -⟩ := c43_ZX hn 1 s5 (θ' := -(π / 2)) (by push_cast; ring) c43_cs_m2
    linarith

/-- K pair at `±60°` (`j = 2`): the D-point is at `0°`, a **cap**. -/
private theorem c43_coreK2 (hX : Normal X) {y n : Pt} (hF : Frame43 X y n)
    (hd : degδ X y = 6) (hm : mS X y = 3) {a c : Pt} (ha : a ∈ nbδ X y) (hc : c ∈ nbδ X y)
    (hab : a ≠ c43g y (c43g y a)) (hac : a ≠ c) (hbc : c43g y (c43g y a) ≠ c)
    (hSa : a ∈ Sset X) (hDa : a ∉ Dset X) (hSb : c43g y (c43g y a) ∈ Sset X)
    (hDb : c43g y (c43g y a) ∉ Dset X) (hSc : c ∈ Sset X) (hDc : c ∈ Dset X) :
    FanShape X y n ∨ CapShape X y n := by
  have hn := hF.unit
  have hr := c43_r_lo
  have m1 := c43g_mem hX hd ha
  have m2 := c43g_mem hX hd m1
  have m3 := c43g_mem hX hd m2
  have m4 := c43g_mem hX hd m3
  obtain ⟨g1, -⟩ := c43g2_coords (n := n) y a
  obtain ⟨hPa, hPb⟩ := abs_le.1 (pair_K hX hF ha m2 hab hSa hDa hSb hDb).1
  have e : inner ℝ (a - y) n - inner ℝ (c43g y (c43g y a) - y) n =
      √3 * (√3 / 2 * inner ℝ (a - y) n + 1 / 2 * inner ℝ (a - y) (perp n)) := by
    rw [g1]; linear_combination (-(inner ℝ (a - y) n) / 2) * c43_r_sq
  have hQ' : |√3 / 2 * inner ℝ (a - y) n + 1 / 2 * inner ℝ (a - y) (perp n)| ≤ 12 / 1000 := by
    have h1 : |√3 * (√3 / 2 * inner ℝ (a - y) n + 1 / 2 * inner ℝ (a - y) (perp n))| ≤
        1 / 49 := by
      rw [← e, abs_le]; exact ⟨hPa, hPb⟩
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < √3)] at h1
    nlinarith [mul_le_mul_of_nonneg_right hr.le
      (abs_nonneg (√3 / 2 * inner ℝ (a - y) n + 1 / 2 * inner ℝ (a - y) (perp n)))]
  have hQ : |-(Real.sin (-(π / 3))) * inner ℝ (a - y) n +
      Real.cos (-(π / 3)) * inner ℝ (a - y) (perp n)| ≤ 12 / 1000 := by
    rw [c43_cs_m3.1, c43_cs_m3.2, neg_neg]; exact hQ'
  have hSa' := c43_S_gt hX hF ha hSa
  have hSc' := c43_S_gt hX hF hc hSc
  rcases Or.symm <| c43_pin (η := 1 / 50) hn (by norm_num) (by norm_num) (c43_unit hX hn ha) hQ
    with sa | sa
  · obtain ⟨-, -, za, -, -⟩ := c43_ZX hn 0 sa (θ' := π - π / 3) (by push_cast; ring) c43_cs_p23
    linarith
  obtain ⟨sl0, za0, -, -, -⟩ := c43_ZX hn 0 sa (θ' := -(π / 3)) (by push_cast; ring) c43_cs_m3
  have s1 := c43g_slot sa
  obtain ⟨sl1, z10, -, -, -⟩ := c43_ZX hn 0 s1 (θ' := 0) (by push_cast; ring) c43_cs_0
  have s2 := c43g_slot s1
  obtain ⟨-, z20, -, -, -⟩ := c43_ZX hn 0 s2 (θ' := π / 3) (by push_cast; ring) c43_cs_p3
  have s3 := c43g_slot s2
  obtain ⟨-, z30, z31, -, -⟩ := c43_ZX hn 0 s3 (θ' := π - π / 3) (by push_cast; ring) c43_cs_p23
  have s4 := c43g_slot s3
  obtain ⟨sl4, -, z41, -, -⟩ := c43_ZX hn 0 s4 (θ' := π) (by push_cast; ring) c43_cs_pi
  have s5 := c43g_slot s4
  obtain ⟨-, z50, z51, -, -⟩ :=
    c43_ZX hn 1 s5 (θ' := -(π - π / 3)) (by push_cast; ring) c43_cs_m23
  rcases c43_hex_enum hX hd ha c hc with h | h | h | h | h | h
  · exact absurd h.symm hac
  · subst h
    refine Or.inr ⟨⟨-1, Or.inr rfl, a, ha, c43g y a, m1, hSa, hDa, hDc,
      c43_slot_fix sl0 (by ring) (by norm_num), c43_slot_fix sl1 rfl (by norm_num)⟩, ?_, ?_⟩
    · intro x hx hZ
      rcases c43_hex_enum hX hd ha x hx with h | h | h | h | h | h <;> subst h
      · exfalso; linarith
      · exfalso; linarith
      · exfalso; linarith
      · exfalso; linarith
      · exact c43_slot_pi (c43_slot_mono sl4 (by norm_num))
      · exfalso; linarith
    · have hmem : c43g y (c43g y (c43g y (c43g y a))) ∈
          (nbδ X y).filter (fun x => inner ℝ (x - y) n ≤ -(4 / 5)) :=
        mem_filter.2 ⟨m4, by linarith⟩
      have := card_pos.2 ⟨_, hmem⟩
      unfold vR; rw [hd, hm]; omega
  · exact absurd h.symm hbc
  · subst h; linarith
  · subst h; linarith
  · subst h; linarith

/-- K pair at `±90°` (`j = 3`): the D-point is at `±30°`, fan **HF1**. -/
private theorem c43_coreK3 (hX : Normal X) {y n : Pt} (hF : Frame43 X y n)
    (hd : degδ X y = 6) (hm : mS X y = 3) {a c : Pt} (ha : a ∈ nbδ X y) (hc : c ∈ nbδ X y)
    (hab : a ≠ c43g y (c43g y (c43g y a))) (hac : a ≠ c)
    (hbc : c43g y (c43g y (c43g y a)) ≠ c) (hSa : a ∈ Sset X) (hDa : a ∉ Dset X)
    (hSb : c43g y (c43g y (c43g y a)) ∈ Sset X) (hDb : c43g y (c43g y (c43g y a)) ∉ Dset X)
    (hSc : c ∈ Sset X) (hDc : c ∈ Dset X) : FanShape X y n ∨ CapShape X y n := by
  have hn := hF.unit
  have hr := c43_r_lo
  have m1 := c43g_mem hX hd ha
  have m2 := c43g_mem hX hd m1
  have m3 := c43g_mem hX hd m2
  have m4 := c43g_mem hX hd m3
  have m5 := c43g_mem hX hd m4
  have eb : c43g y (c43g y (c43g y a)) - y = -(a - y) := by rw [c43g3]; abel
  obtain ⟨hPa, hPb⟩ := abs_le.1 (pair_K hX hF ha m3 hab hSa hDa hSb hDb).1
  rw [eb, inner_neg_left] at hPa hPb
  have hQ : |-(Real.sin (π / 2)) * inner ℝ (a - y) n +
      Real.cos (π / 2) * inner ℝ (a - y) (perp n)| ≤ 1 / 98 := by
    rw [c43_cs_p2.1, c43_cs_p2.2, abs_le]; constructor <;> linarith
  have hSc' := c43_S_gt hX hF hc hSc
  rcases c43_pin (η := 1 / 50) hn (by norm_num) (by norm_num) (c43_unit hX hn ha) hQ
    with sa | sa
  · -- `a` at `90°`, `b` at `−90°`
    obtain ⟨sl0, za0, -, -, -⟩ := c43_ZX hn 0 sa (θ' := π / 2) (by push_cast; ring) c43_cs_p2
    have s1 := c43g_slot sa
    obtain ⟨-, -, z11, -, -⟩ :=
      c43_ZX hn 0 s1 (θ' := π - π / 6) (by push_cast; ring) c43_cs_p56
    have s2 := c43g_slot s1
    obtain ⟨-, -, z21, -, -⟩ :=
      c43_ZX hn 1 s2 (θ' := -(π - π / 6)) (by push_cast; ring) c43_cs_m56
    have s3 := c43g_slot s2
    obtain ⟨sl3, z30, -, -, -⟩ :=
      c43_ZX hn 1 s3 (θ' := -(π / 2)) (by push_cast; ring) c43_cs_m2
    have s4 := c43g_slot s3
    obtain ⟨sl4, z40, -, -, -⟩ :=
      c43_ZX hn 1 s4 (θ' := -(π / 6)) (by push_cast; ring) c43_cs_m6
    have s5 := c43g_slot s4
    obtain ⟨sl5, z50, -, -, -⟩ := c43_ZX hn 1 s5 (θ' := π / 6) (by push_cast; ring) c43_cs_p6
    have hlow : ∀ x ∈ nbδ X y, inner ℝ (x - y) n ≤ -(2 / 3) →
        inner ℝ (x - y) n ≤ -(4 / 5) := by
      intro x hx hZ
      rcases c43_hex_enum hX hd ha x hx with h | h | h | h | h | h <;> subst h <;> linarith
    have hcnt : vR X y ≤ 8 +
        ((nbδ X y).filter (fun x => inner ℝ (x - y) n ≤ -(4 / 5))).card := by
      have hmem : c43g y a ∈ (nbδ X y).filter (fun x => inner ℝ (x - y) n ≤ -(4 / 5)) :=
        mem_filter.2 ⟨m1, by linarith⟩
      have := card_pos.2 ⟨_, hmem⟩
      unfold vR; rw [hd, hm]; omega
    rcases c43_hex_enum hX hd ha c hc with h | h | h | h | h | h
    · exact absurd h.symm hac
    · subst h; linarith
    · subst h; linarith
    · exact absurd h.symm hbc
    · subst h
      exact Or.inl ⟨⟨-1, Or.inr rfl, a, ha, _, m3, _, m4, hSa, hDa, hDc,
        c43_slot_fix sl0 (by ring) (by norm_num), c43_slot_fix sl3 (by ring) (by norm_num),
        c43_slot_fix sl4 (by ring) (by norm_num), Or.inl hSb⟩, hlow, hcnt⟩
    · subst h
      exact Or.inl ⟨⟨1, Or.inl rfl, _, m3, a, ha, _, m5, hSb, hDb, hDc,
        c43_slot_fix sl3 (by ring) (by norm_num), c43_slot_fix sl0 (by ring) (by norm_num),
        c43_slot_fix sl5 (by ring) (by norm_num), Or.inl hSa⟩, hlow, hcnt⟩
  · -- `a` at `−90°`, `b` at `90°`
    obtain ⟨sl0, za0, -, -, -⟩ := c43_ZX hn 1 sa (θ' := -(π / 2)) (by push_cast; ring) c43_cs_m2
    have s1 := c43g_slot sa
    obtain ⟨sl1, z10, -, -, -⟩ :=
      c43_ZX hn 1 s1 (θ' := -(π / 6)) (by push_cast; ring) c43_cs_m6
    have s2 := c43g_slot s1
    obtain ⟨sl2, z20, -, -, -⟩ := c43_ZX hn 1 s2 (θ' := π / 6) (by push_cast; ring) c43_cs_p6
    have s3 := c43g_slot s2
    obtain ⟨sl3, z30, -, -, -⟩ := c43_ZX hn 1 s3 (θ' := π / 2) (by push_cast; ring) c43_cs_p2
    have s4 := c43g_slot s3
    obtain ⟨-, -, z41, -, -⟩ :=
      c43_ZX hn 1 s4 (θ' := π - π / 6) (by push_cast; ring) c43_cs_p56
    have s5 := c43g_slot s4
    obtain ⟨-, -, z51, -, -⟩ :=
      c43_ZX hn 2 s5 (θ' := -(π - π / 6)) (by push_cast; ring) c43_cs_m56
    have hlow : ∀ x ∈ nbδ X y, inner ℝ (x - y) n ≤ -(2 / 3) →
        inner ℝ (x - y) n ≤ -(4 / 5) := by
      intro x hx hZ
      rcases c43_hex_enum hX hd ha x hx with h | h | h | h | h | h <;> subst h <;> linarith
    have hcnt : vR X y ≤ 8 +
        ((nbδ X y).filter (fun x => inner ℝ (x - y) n ≤ -(4 / 5))).card := by
      have hmem : c43g y (c43g y (c43g y (c43g y a))) ∈
          (nbδ X y).filter (fun x => inner ℝ (x - y) n ≤ -(4 / 5)) :=
        mem_filter.2 ⟨m4, by linarith⟩
      have := card_pos.2 ⟨_, hmem⟩
      unfold vR; rw [hd, hm]; omega
    rcases c43_hex_enum hX hd ha c hc with h | h | h | h | h | h
    · exact absurd h.symm hac
    · subst h
      exact Or.inl ⟨⟨-1, Or.inr rfl, _, m3, a, ha, _, m1, hSb, hDb, hDc,
        c43_slot_fix sl3 (by ring) (by norm_num), c43_slot_fix sl0 (by ring) (by norm_num),
        c43_slot_fix sl1 (by ring) (by norm_num), Or.inl hSa⟩, hlow, hcnt⟩
    · subst h
      exact Or.inl ⟨⟨1, Or.inl rfl, a, ha, _, m3, _, m2, hSa, hDa, hDc,
        c43_slot_fix sl0 (by ring) (by norm_num), c43_slot_fix sl3 (by ring) (by norm_num),
        c43_slot_fix sl2 (by ring) (by norm_num), Or.inl hSb⟩, hlow, hcnt⟩
    · exact absurd h.symm hbc
    · subst h; linarith
    · subst h; linarith

/-- D pair at `±30°` (`j = 1`): the K-point is at `±90°`, fan **HF2**. -/
private theorem c43_coreD1 (hX : Normal X) {y n : Pt} (hF : Frame43 X y n)
    (hd : degδ X y = 6) (hm : mS X y = 3) {a c : Pt} (ha : a ∈ nbδ X y) (hc : c ∈ nbδ X y)
    (hab : a ≠ c43g y a) (hac : a ≠ c) (hbc : c43g y a ≠ c) (hSa : a ∈ Sset X)
    (hDa : a ∈ Dset X) (_hSb : c43g y a ∈ Sset X) (hDb : c43g y a ∈ Dset X)
    (hSc : c ∈ Sset X) (hDc : c ∉ Dset X) : FanShape X y n ∨ CapShape X y n := by
  have hn := hF.unit
  have hr := c43_r_lo
  have m1 := c43g_mem hX hd ha
  have m2 := c43g_mem hX hd m1
  have m3 := c43g_mem hX hd m2
  have m4 := c43g_mem hX hd m3
  have m5 := c43g_mem hX hd m4
  obtain ⟨g1, g2⟩ := c43g_coords (n := n) y a
  have hu := c43_unit hX hn ha
  have hdd := dd_heights hX hF hDa hDb (dist_of_mem_nbδ hX ha).le (dist_of_mem_nbδ hX m1).le
  rw [g1, g2] at hdd
  have ht : (inner ℝ (a - y) n - (1 / 2 * inner ℝ (a - y) n -
      √3 / 2 * inner ℝ (a - y) (perp n))) ^ 2 + (inner ℝ (a - y) (perp n) -
      (√3 / 2 * inner ℝ (a - y) n + 1 / 2 * inner ℝ (a - y) (perp n))) ^ 2 = 1 := by
    linear_combination
      ((inner ℝ (a - y) n ^ 2 + inner ℝ (a - y) (perp n) ^ 2) / 4) * c43_r_sq + hu
  have hXd : |inner ℝ (a - y) (perp n) -
      (√3 / 2 * inner ℝ (a - y) n + 1 / 2 * inner ℝ (a - y) (perp n))| ≤ 1 :=
    (sq_le_one_iff_abs_le_one _).1 (by nlinarith [sq_nonneg (inner ℝ (a - y) n -
      (1 / 2 * inner ℝ (a - y) n - √3 / 2 * inner ℝ (a - y) (perp n)))])
  have hQ : |-(Real.sin (-(π / 6))) * inner ℝ (a - y) n +
      Real.cos (-(π / 6)) * inner ℝ (a - y) (perp n)| ≤ 9 / 400 := by
    rw [c43_cs_m6.1, c43_cs_m6.2,
      show -(-(1 / 2 : ℝ)) * inner ℝ (a - y) n + √3 / 2 * inner ℝ (a - y) (perp n) =
        inner ℝ (a - y) n - (1 / 2 * inner ℝ (a - y) n - √3 / 2 * inner ℝ (a - y) (perp n))
        by ring]
    linarith
  have hSa' := c43_S_gt hX hF ha hSa
  have hSc' := c43_S_gt hX hF hc hSc
  rcases Or.symm <| c43_pin (η := 1 / 30) hn (by norm_num) (by norm_num) hu hQ with sa | sa
  · obtain ⟨-, -, za, -, -⟩ := c43_ZX hn 0 sa (θ' := π - π / 6) (by push_cast; ring) c43_cs_p56
    linarith
  obtain ⟨sl0, za0, -, -, -⟩ := c43_ZX hn 0 sa (θ' := -(π / 6)) (by push_cast; ring) c43_cs_m6
  have s1 := c43g_slot sa
  obtain ⟨sl1, z10, -, -, -⟩ := c43_ZX hn 0 s1 (θ' := π / 6) (by push_cast; ring) c43_cs_p6
  have s2 := c43g_slot s1
  obtain ⟨sl2, z20, -, -, -⟩ := c43_ZX hn 0 s2 (θ' := π / 2) (by push_cast; ring) c43_cs_p2
  have s3 := c43g_slot s2
  obtain ⟨-, -, z31, -, -⟩ := c43_ZX hn 0 s3 (θ' := π - π / 6) (by push_cast; ring) c43_cs_p56
  have s4 := c43g_slot s3
  obtain ⟨-, -, z41, -, -⟩ :=
    c43_ZX hn 1 s4 (θ' := -(π - π / 6)) (by push_cast; ring) c43_cs_m56
  have s5 := c43g_slot s4
  obtain ⟨sl5, z50, -, -, -⟩ := c43_ZX hn 1 s5 (θ' := -(π / 2)) (by push_cast; ring) c43_cs_m2
  have hlow : ∀ x ∈ nbδ X y, inner ℝ (x - y) n ≤ -(2 / 3) →
      inner ℝ (x - y) n ≤ -(4 / 5) := by
    intro x hx hZ
    rcases c43_hex_enum hX hd ha x hx with h | h | h | h | h | h <;> subst h <;> linarith
  have hcnt : vR X y ≤ 8 +
      ((nbδ X y).filter (fun x => inner ℝ (x - y) n ≤ -(4 / 5))).card := by
    have hmem : c43g y (c43g y (c43g y a)) ∈
        (nbδ X y).filter (fun x => inner ℝ (x - y) n ≤ -(4 / 5)) :=
      mem_filter.2 ⟨m3, by linarith⟩
    have := card_pos.2 ⟨_, hmem⟩
    unfold vR; rw [hd, hm]; omega
  have hdist : dist a (c43g y a) = minDist X := by
    rw [hX.minDist_eq]; exact c43g_dist hX hn ha
  rcases c43_hex_enum hX hd ha c hc with h | h | h | h | h | h
  · exact absurd h.symm hac
  · exact absurd h.symm hbc
  · subst h
    exact Or.inl ⟨⟨-1, Or.inr rfl, _, m2, _, m5, a, ha, hSc, hDc, hDa,
      c43_slot_fix sl2 (by ring) (by norm_num), c43_slot_fix sl5 (by ring) (by norm_num),
      c43_slot_fix sl0 (by ring) (by norm_num),
      Or.inr ⟨_, m1, hDb, c43_slot_fix sl1 (by ring) (by norm_num), hdist⟩⟩, hlow, hcnt⟩
  · subst h; linarith
  · subst h; linarith
  · subst h
    exact Or.inl ⟨⟨1, Or.inl rfl, _, m5, _, m2, _, m1, hSc, hDc, hDb,
      c43_slot_fix sl5 (by ring) (by norm_num), c43_slot_fix sl2 (by ring) (by norm_num),
      c43_slot_fix sl1 (by ring) (by norm_num),
      Or.inr ⟨a, ha, hDa, c43_slot_fix sl0 (by ring) (by norm_num),
        by rw [dist_comm]; exact hdist⟩⟩, hlow, hcnt⟩

/-- D pair at `±60°` (`j = 2`): the K-point would be at `0°`, above the D-points; impossible. -/
private theorem c43_coreD2 (hX : Normal X) {y n : Pt} (hF : Frame43 X y n)
    (hd : degδ X y = 6) (_hm : mS X y = 3) {a c : Pt} (ha : a ∈ nbδ X y) (hc : c ∈ nbδ X y)
    (hab : a ≠ c43g y (c43g y a)) (hac : a ≠ c) (hbc : c43g y (c43g y a) ≠ c)
    (hSa : a ∈ Sset X) (hDa : a ∈ Dset X) (_hSb : c43g y (c43g y a) ∈ Sset X)
    (hDb : c43g y (c43g y a) ∈ Dset X) (hSc : c ∈ Sset X) (hDc : c ∉ Dset X) : False := by
  have hn := hF.unit
  have hr := c43_r_lo
  have m1 := c43g_mem hX hd ha
  have m2 := c43g_mem hX hd m1
  obtain ⟨g1, -⟩ := c43g2_coords (n := n) y a
  obtain ⟨hPa, hPb⟩ := abs_le.1 (pair_D hX hF ha m2 hab hDa hDb).1
  have e : inner ℝ (a - y) n - inner ℝ (c43g y (c43g y a) - y) n =
      √3 * (√3 / 2 * inner ℝ (a - y) n + 1 / 2 * inner ℝ (a - y) (perp n)) := by
    rw [g1]; linear_combination (-(inner ℝ (a - y) n) / 2) * c43_r_sq
  have hQ' : |√3 / 2 * inner ℝ (a - y) n + 1 / 2 * inner ℝ (a - y) (perp n)| ≤ 26 / 1000 := by
    have h1 : |√3 * (√3 / 2 * inner ℝ (a - y) n + 1 / 2 * inner ℝ (a - y) (perp n))| ≤
        9 / 200 := by
      rw [← e, abs_le]; exact ⟨hPa, hPb⟩
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < √3)] at h1
    nlinarith [mul_le_mul_of_nonneg_right hr.le
      (abs_nonneg (√3 / 2 * inner ℝ (a - y) n + 1 / 2 * inner ℝ (a - y) (perp n)))]
  have hQ : |-(Real.sin (-(π / 3))) * inner ℝ (a - y) n +
      Real.cos (-(π / 3)) * inner ℝ (a - y) (perp n)| ≤ 26 / 1000 := by
    rw [c43_cs_m3.1, c43_cs_m3.2, neg_neg]; exact hQ'
  have hSa' := c43_S_gt hX hF ha hSa
  have hSc' := c43_S_gt hX hF hc hSc
  rcases Or.symm <| c43_pin (η := 37 / 1000) hn (by norm_num) (by norm_num) (c43_unit hX hn ha) hQ
    with sa | sa
  · obtain ⟨-, -, za, -, -⟩ := c43_ZX hn 0 sa (θ' := π - π / 3) (by push_cast; ring) c43_cs_p23
    linarith
  obtain ⟨-, -, za1, -, -⟩ := c43_ZX hn 0 sa (θ' := -(π / 3)) (by push_cast; ring) c43_cs_m3
  have s1 := c43g_slot sa
  have s2 := c43g_slot s1
  have s3 := c43g_slot s2
  have s4 := c43g_slot s3
  have s5 := c43g_slot s4
  rcases c43_hex_enum hX hd ha c hc with h | h | h | h | h | h
  · exact hac h.symm
  · subst h
    obtain ⟨-, z, -, -, -⟩ := c43_ZX hn 0 s1 (θ' := 0) (by push_cast; ring) c43_cs_0
    have := c43_KD hX hF hc hDc ha hDa
    linarith
  · exact hbc h.symm
  · subst h
    obtain ⟨-, -, z, -, -⟩ := c43_ZX hn 0 s3 (θ' := π - π / 3) (by push_cast; ring) c43_cs_p23
    linarith
  · subst h
    obtain ⟨-, -, z, -, -⟩ := c43_ZX hn 0 s4 (θ' := π) (by push_cast; ring) c43_cs_pi
    linarith
  · subst h
    obtain ⟨-, -, z, -, -⟩ :=
      c43_ZX hn 1 s5 (θ' := -(π - π / 3)) (by push_cast; ring) c43_cs_m23
    linarith

/-- D pair at `±90°` (`j = 3`): the K-point would be at `±30°`, above the D-points;
impossible. -/
private theorem c43_coreD3 (hX : Normal X) {y n : Pt} (hF : Frame43 X y n)
    (hd : degδ X y = 6) (_hm : mS X y = 3) {a c : Pt} (ha : a ∈ nbδ X y) (hc : c ∈ nbδ X y)
    (hab : a ≠ c43g y (c43g y (c43g y a))) (hac : a ≠ c)
    (hbc : c43g y (c43g y (c43g y a)) ≠ c) (_hSa : a ∈ Sset X) (hDa : a ∈ Dset X)
    (_hSb : c43g y (c43g y (c43g y a)) ∈ Sset X) (hDb : c43g y (c43g y (c43g y a)) ∈ Dset X)
    (hSc : c ∈ Sset X) (hDc : c ∉ Dset X) : False := by
  have hn := hF.unit
  have hr := c43_r_lo
  have m1 := c43g_mem hX hd ha
  have m2 := c43g_mem hX hd m1
  have m3 := c43g_mem hX hd m2
  have eb : c43g y (c43g y (c43g y a)) - y = -(a - y) := by rw [c43g3]; abel
  obtain ⟨hPa, hPb⟩ := abs_le.1 (pair_D hX hF ha m3 hab hDa hDb).1
  rw [eb, inner_neg_left] at hPa hPb
  have hQ : |-(Real.sin (π / 2)) * inner ℝ (a - y) n +
      Real.cos (π / 2) * inner ℝ (a - y) (perp n)| ≤ 9 / 400 := by
    rw [c43_cs_p2.1, c43_cs_p2.2, abs_le]; constructor <;> linarith
  have hSc' := c43_S_gt hX hF hc hSc
  have hKD := c43_KD hX hF hc hDc ha hDa
  rcases c43_pin (η := 1 / 30) hn (by norm_num) (by norm_num) (c43_unit hX hn ha) hQ
    with sa | sa
  · obtain ⟨-, -, za1, -, -⟩ := c43_ZX hn 0 sa (θ' := π / 2) (by push_cast; ring) c43_cs_p2
    have s1 := c43g_slot sa
    have s2 := c43g_slot s1
    have s3 := c43g_slot s2
    have s4 := c43g_slot s3
    have s5 := c43g_slot s4
    rcases c43_hex_enum hX hd ha c hc with h | h | h | h | h | h
    · exact hac h.symm
    · subst h
      obtain ⟨-, -, z, -, -⟩ :=
        c43_ZX hn 0 s1 (θ' := π - π / 6) (by push_cast; ring) c43_cs_p56
      linarith
    · subst h
      obtain ⟨-, -, z, -, -⟩ :=
        c43_ZX hn 1 s2 (θ' := -(π - π / 6)) (by push_cast; ring) c43_cs_m56
      linarith
    · exact hbc h.symm
    · subst h
      obtain ⟨-, z, -, -, -⟩ := c43_ZX hn 1 s4 (θ' := -(π / 6)) (by push_cast; ring) c43_cs_m6
      linarith
    · subst h
      obtain ⟨-, z, -, -, -⟩ := c43_ZX hn 1 s5 (θ' := π / 6) (by push_cast; ring) c43_cs_p6
      linarith
  · obtain ⟨-, -, za1, -, -⟩ := c43_ZX hn 1 sa (θ' := -(π / 2)) (by push_cast; ring) c43_cs_m2
    have s1 := c43g_slot sa
    have s2 := c43g_slot s1
    have s3 := c43g_slot s2
    have s4 := c43g_slot s3
    have s5 := c43g_slot s4
    rcases c43_hex_enum hX hd ha c hc with h | h | h | h | h | h
    · exact hac h.symm
    · subst h
      obtain ⟨-, z, -, -, -⟩ := c43_ZX hn 1 s1 (θ' := -(π / 6)) (by push_cast; ring) c43_cs_m6
      linarith
    · subst h
      obtain ⟨-, z, -, -, -⟩ := c43_ZX hn 1 s2 (θ' := π / 6) (by push_cast; ring) c43_cs_p6
      linarith
    · exact hbc h.symm
    · subst h
      obtain ⟨-, -, z, -, -⟩ :=
        c43_ZX hn 1 s4 (θ' := π - π / 6) (by push_cast; ring) c43_cs_p56
      linarith
    · subst h
      obtain ⟨-, -, z, -, -⟩ :=
        c43_ZX hn 2 s5 (θ' := -(π - π / 6)) (by push_cast; ring) c43_cs_m56
      linarith

/-- A K pair `a, b` and a D-point `c` among the `S`-neighbours. -/
private theorem c43_coreK (hX : Normal X) {y n : Pt} (hF : Frame43 X y n)
    (hd : degδ X y = 6) (hm : mS X y = 3) {a b c : Pt} (ha : a ∈ nbδ X y) (hb : b ∈ nbδ X y)
    (hc : c ∈ nbδ X y) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hSa : a ∈ Sset X)
    (hDa : a ∉ Dset X) (hSb : b ∈ Sset X) (hDb : b ∉ Dset X) (hSc : c ∈ Sset X)
    (hDc : c ∈ Dset X) : FanShape X y n ∨ CapShape X y n := by
  rcases c43_hex_enum hX hd ha b hb with h | h | h | h | h | h
  · exact absurd h.symm hab
  · subst h; exact (c43_coreK1 hX hF hd hm ha hc hab hac hbc hSa hDa hSb hDb hSc hDc).elim
  · subst h; exact c43_coreK2 hX hF hd hm ha hc hab hac hbc hSa hDa hSb hDb hSc hDc
  · subst h; exact c43_coreK3 hX hF hd hm ha hc hab hac hbc hSa hDa hSb hDb hSc hDc
  · have h' : a = c43g y (c43g y b) := by rw [h, c43g3, c43g3]; abel
    subst h'
    exact c43_coreK2 hX hF hd hm hb hc (Ne.symm hab) hbc hac hSb hDb hSa hDa hSc hDc
  · have h' : a = c43g y b := by rw [h, c43g3, c43g3]; abel
    subst h'
    exact (c43_coreK1 hX hF hd hm hb hc (Ne.symm hab) hbc hac hSb hDb hSa hDa hSc hDc).elim

/-- A D pair `a, b` and a K-point `c` among the `S`-neighbours. -/
private theorem c43_coreD (hX : Normal X) {y n : Pt} (hF : Frame43 X y n)
    (hd : degδ X y = 6) (hm : mS X y = 3) {a b c : Pt} (ha : a ∈ nbδ X y) (hb : b ∈ nbδ X y)
    (hc : c ∈ nbδ X y) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hSa : a ∈ Sset X)
    (hDa : a ∈ Dset X) (hSb : b ∈ Sset X) (hDb : b ∈ Dset X) (hSc : c ∈ Sset X)
    (hDc : c ∉ Dset X) : FanShape X y n ∨ CapShape X y n := by
  rcases c43_hex_enum hX hd ha b hb with h | h | h | h | h | h
  · exact absurd h.symm hab
  · subst h; exact c43_coreD1 hX hF hd hm ha hc hab hac hbc hSa hDa hSb hDb hSc hDc
  · subst h; exact (c43_coreD2 hX hF hd hm ha hc hab hac hbc hSa hDa hSb hDb hSc hDc).elim
  · subst h; exact (c43_coreD3 hX hF hd hm ha hc hab hac hbc hSa hDa hSb hDb hSc hDc).elim
  · have h' : a = c43g y (c43g y b) := by rw [h, c43g3, c43g3]; abel
    subst h'
    exact (c43_coreD2 hX hF hd hm hb hc (Ne.symm hab) hbc hac hSb hDb hSa hDa hSc hDc).elim
  · have h' : a = c43g y b := by rw [h, c43g3, c43g3]; abel
    subst h'
    exact c43_coreD1 hX hF hd hm hb hc (Ne.symm hab) hbc hac hSb hDb hSa hDa hSc hDc

/-! ## Lemma M and Lemma H -/

/-- **Lemma M** (`m_y = 4`): the four `S`-neighbours are K-row points within `1/40` of the
slots `±90°` and D-points (in `S`) within `1/40` of the slots `±30°`.

TODO: none — proved.
What's missing (paper §1.3): all four have angle in `[−91.17°, 91.17°]` (height
`≥ −1/49`) and are pairwise `≥ 60°` apart, so their angles are within `1.17°` of
`−90°, −30°, 30°, 90°` (chord `≤ 0.0204 < 1/40`).  By `pair_K`/`pair_D` at most two of each
kind and same-kind pairs are mirror pairs, so the kinds pair up as `{±90°}`, `{±30°}`.  K at
`±30°` would force `h ≥ cos 31.2° > 0.85` (`Frame43.top`) while D at `±90°` needs height
`≥ h + t − 1/49` (`frame_D`) but has height `≤ 0.021`: contradiction.
Acceptance: no `sorry`.
Depends on: `mS_le_four_of_frame`-style angle bounds, `pair_K`, `pair_D`, `frame_outside`,
`frame_D`, `Frame43.top`, `Sset_not_interior`, `exists_angle`. Difficulty L. -/
theorem lemmaM (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) (hy : y ∈ Rset X)
    (hm : mS X y = 4) :
    ∃ p₁ ∈ nbδ X y, ∃ p₂ ∈ nbδ X y, ∃ z₁ ∈ nbδ X y, ∃ z₂ ∈ nbδ X y,
      p₁ ∈ Sset X ∧ p₁ ∉ Dset X ∧ p₂ ∈ Sset X ∧ p₂ ∉ Dset X ∧
      z₁ ∈ Sset X ∧ z₁ ∈ Dset X ∧ z₂ ∈ Sset X ∧ z₂ ∈ Dset X ∧
      Slot y n (π / 2) (1 / 40) p₁ ∧ Slot y n (-(π / 2)) (1 / 40) p₂ ∧
      Slot y n (π / 6) (1 / 40) z₁ ∧ Slot y n (-(π / 6)) (1 / 40) z₂ := by
  have hn := hF.unit
  have hdp := hF.depth_pos
  have ht := c43_tgap_pos hX
  have hr := c43_r_lo
  set P := (nbδ X y).filter (· ∈ Sset X) with hP
  have hPc : P.card = 4 := hm
  have hPm : ∀ q ∈ P, q ∈ nbδ X y ∧ q ∈ Sset X := fun q hq => mem_filter.1 hq
  have harc := c43_arc4 hn P hPc (fun q hq => c43_unit hX hn (hPm q hq).1)
    (fun q hq q' hq' hne => c43_sep hX hn (hPm q hq).1 (hPm q' hq').1 hne)
    (fun q hq => by
      have h1 := hPm q hq
      have hlow := c43_S_low hX hF h1.1 h1.2
      have hu := c43_abs_le_one (c43_unit hX hn h1.1)
      linarith)
  obtain ⟨q0, hq0, hs0⟩ := harc 0 (by norm_num)
  obtain ⟨q1, hq1, hs1⟩ := harc 1 (by norm_num)
  obtain ⟨q2, hq2, hs2⟩ := harc 2 (by norm_num)
  obtain ⟨q3, hq3, hs3⟩ := harc 3 (by norm_num)
  rw [show -(π / 2) + ((0 : ℕ) : ℝ) * (π / 3) = -(π / 2) by push_cast; ring] at hs0
  rw [show -(π / 2) + ((1 : ℕ) : ℝ) * (π / 3) = -(π / 6) by push_cast; ring] at hs1
  rw [show -(π / 2) + ((2 : ℕ) : ℝ) * (π / 3) = π / 6 by push_cast; ring] at hs2
  rw [show -(π / 2) + ((3 : ℕ) : ℝ) * (π / 3) = π / 2 by push_cast; ring] at hs3
  obtain ⟨hn0, hS0⟩ := hPm q0 hq0
  obtain ⟨hn1, hS1⟩ := hPm q1 hq1
  obtain ⟨hn2, hS2⟩ := hPm q2 hq2
  obtain ⟨hn3, hS3⟩ := hPm q3 hq3
  obtain ⟨z0, x0⟩ := c43_slot_coords hn hs0
  obtain ⟨z1, x1⟩ := c43_slot_coords hn hs1
  obtain ⟨z2, x2⟩ := c43_slot_coords hn hs2
  obtain ⟨z3, x3⟩ := c43_slot_coords hn hs3
  simp only [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two,
    Real.cos_pi_div_six, Real.sin_pi_div_six, sub_zero] at z0 x0 z1 x1 z2 x2 z3 x3
  obtain ⟨z0a, z0b⟩ := abs_le.1 z0
  obtain ⟨z1a, z1b⟩ := abs_le.1 z1
  obtain ⟨z2a, z2b⟩ := abs_le.1 z2
  obtain ⟨z3a, z3b⟩ := abs_le.1 z3
  have u0 := c43_abs_le_one (c43_unit hX hn hn0)
  have u3 := c43_abs_le_one (c43_unit hX hn hn3)
  have ne01 : q0 ≠ q1 := by rintro rfl; linarith
  have ne32 : q3 ≠ q2 := by rintro rfl; linarith
  -- the points at `±90°` are K-row points
  have hD0 : q0 ∉ Dset X := by
    intro hD0
    have l0 := c43_D_low hX hF hn0 hD0
    by_cases hD1 : q1 ∈ Dset X
    · have := (abs_le.1 (pair_D hX hF hn0 hn1 ne01 hD0 hD1).1).1
      linarith
    · have := c43_K_top hF hn1 hD1
      linarith
  have hD3 : q3 ∉ Dset X := by
    intro hD3
    have l3 := c43_D_low hX hF hn3 hD3
    by_cases hD2 : q2 ∈ Dset X
    · have := (abs_le.1 (pair_D hX hF hn3 hn2 ne32 hD3 hD2).1).1
      linarith
    · have := c43_K_top hF hn2 hD2
      linarith
  -- the points at `±30°` are D-points
  have hD1 : q1 ∈ Dset X := by
    by_contra hD1
    have := (abs_le.1 (pair_K hX hF hn0 hn1 ne01 hS0 hD0 hS1 hD1).1).1
    linarith
  have hD2 : q2 ∈ Dset X := by
    by_contra hD2
    have := (abs_le.1 (pair_K hX hF hn3 hn2 ne32 hS3 hD3 hS2 hD2).1).1
    linarith
  exact ⟨q3, hn3, q0, hn0, q2, hn2, q1, hn1, hS3, hD3, hS0, hD0, hS2, hD2, hS1, hD1,
    c43_slot_mono hs3 (by norm_num), c43_slot_mono hs0 (by norm_num),
    c43_slot_mono hs2 (by norm_num), c43_slot_mono hs1 (by norm_num)⟩

/-- **F6 / F5** (`m = 4`, `deg ≥ 5`) have fan shape.

TODO: none — proved.
What's missing: `lemmaM`; slots with `σ = 1`, `p = p₂`, `q = p₁ ∈ S`, `z₁`.  Remaining
neighbours (one for F5, two for F6) are `≥ 60°` from the slots `±90°` (within `1.17°`), so
their angle is in `[148.8°, 211.2°]`: height `≤ −cos 31.2° < −0.85`; all other neighbours have
height `≥ −0.03`.  Count: `v = deg + 4 ≤ 8 + (deg − 4)`.
Acceptance: no `sorry`.
Depends on: `lemmaM`, `hexagon_exact` (F6), `dist_of_mem_nbδ`, `one_le_dist`.
Difficulty M. -/
theorem fanShape_of_m4 (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) (hy : y ∈ Rset X)
    (hm : mS X y = 4) (hd : 5 ≤ degδ X y) : FanShape X y n := by
  have hn := hF.unit
  have hr := c43_r_lo
  obtain ⟨p₁, hp₁, p₂, hp₂, z₁, hz₁, z₂, hz₂, hp₁S, hp₁D, hp₂S, hp₂D, hz₁S, hz₁D, hz₂S, hz₂D,
    hs₁, hs₂, hs₃, hs₄⟩ := lemmaM hX hF hy hm
  obtain ⟨a1, -⟩ := c43_slot_coords hn hs₁
  obtain ⟨a2, -⟩ := c43_slot_coords hn hs₂
  simp only [Real.cos_neg, Real.cos_pi_div_two, sub_zero] at a1 a2
  -- `|X a| ≤ 21/40` for the neighbours other than `p₁, p₂`
  have hXa : ∀ a ∈ nbδ X y, a ≠ p₁ → a ≠ p₂ →
      inner ℝ (a - y) (perp n) ^ 2 ≤ (21 / 40) ^ 2 := by
    intro a ha h1 h2
    have d1 := c43_dot_slot hX ha hp₁ h1 hs₁
    have d2 := c43_dot_slot hX ha hp₂ h2 hs₂
    simp only [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two] at d1 d2
    have : |inner ℝ (a - y) (perp n)| ≤ 21 / 40 := by
      rw [abs_le]; constructor <;> linarith
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
  -- non-`S` neighbours are low
  have hnonS : ∀ a ∈ nbδ X y, a ∉ Sset X → inner ℝ (a - y) n ≤ -(4 / 5) := by
    intro a ha haS
    have ne1 : a ≠ p₁ := fun h => haS (h ▸ hp₁S)
    have ne2 : a ≠ p₂ := fun h => haS (h ▸ hp₂S)
    have ne3 : a ≠ z₁ := fun h => haS (h ▸ hz₁S)
    have ne4 : a ≠ z₂ := fun h => haS (h ▸ hz₂S)
    have hx := hXa a ha ne1 ne2
    have hu := c43_unit hX hn ha
    have d3 := c43_dot_slot hX ha hz₁ ne3 hs₃
    have d4 := c43_dot_slot hX ha hz₂ ne4 hs₄
    simp only [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_six, Real.sin_pi_div_six] at d3 d4
    have hz : inner ℝ (a - y) n ≤ 61 / 100 := by
      by_contra hc
      push Not at hc
      nlinarith
    by_contra hc
    push Not at hc
    nlinarith
  refine ⟨⟨1, Or.inl rfl, p₂, hp₂, p₁, hp₁, z₁, hz₁, hp₂S, hp₂D, hz₁D, ?_, ?_, ?_,
    Or.inl hp₁S⟩, ?_, ?_⟩
  · rw [one_mul]; exact c43_slot_mono hs₂ (by norm_num)
  · rw [one_mul]; exact c43_slot_mono hs₁ (by norm_num)
  · rw [one_mul]; exact c43_slot_mono hs₃ (by norm_num)
  · intro a ha hZ
    have ne1 : a ≠ p₁ := by rintro rfl; linarith [(abs_le.1 a1).1]
    have ne2 : a ≠ p₂ := by rintro rfl; linarith [(abs_le.1 a2).1]
    have hx := hXa a ha ne1 ne2
    have hu := c43_unit hX hn ha
    by_contra hc
    push Not at hc
    nlinarith
  · have hsub : (nbδ X y).filter (fun a => a ∉ Sset X) ⊆
        (nbδ X y).filter (fun a => inner ℝ (a - y) n ≤ -(4 / 5)) := by
      intro a ha
      obtain ⟨ha1, ha2⟩ := mem_filter.1 ha
      exact mem_filter.2 ⟨ha1, hnonS a ha1 ha2⟩
    have hc := card_le_card hsub
    have hsplit := card_filter_add_card_filter_not (s := nbδ X y) (fun a => a ∈ Sset X)
    have hmS : ((nbδ X y).filter (fun a => a ∈ Sset X)).card = mS X y := rfl
    have hdeg : (nbδ X y).card = degδ X y := rfl
    unfold vR
    omega

/-- **Lemma H** (`deg = 6`, `m = 3`): the exact hexagon is within `1.3°` of
`{±30°, ±90°, ±150°}` (HF1: K pair at `±90°` + D at `±30°`; HF2: D pair at `±30°` + K at
`±90°`) or of `{0°, ±60°, ±120°, 180°}` (cap: K pair at `±60°` + D at `0°`).

TODO: none — proved.
What's missing (paper §1.3 enumeration): two of the three `S`-neighbours have the same kind
(`pair_K`/`pair_D`: mirror pair), which pins the hexagon offset (`hexagon_exact`) to `≈ 0°` or
`≈ 30°`; only slots with height `> −1/49` can hold `S`-points; excluded cases (K pair at
`±30°` + D at `±90°`; D pair at `±60°` + K at `0°`; D pair at `±90°` + K at `±30°`; three of
one kind) by `Frame43.top`, `frame_outside`, `frame_D` as in the paper.  Offsets from the
mirror error `≤ 2|Z₁ − Z₂|` (`pair_sym`): `≤ 1.2°` for a K pair (HF1 at `±90°`, cap at `±60°`),
`≤ 2.6°` for the D pair of HF2 (`≤ 1.3°` using `dd_heights` with `|X₁ − X₂| ≈ 1`); all
chords `≤ 0.046 < 1/20`.
Fan: slots with `σ` chosen so that the K-row point is at `−σ·90°` (HF2: `q` = hexagon vertex at
`σ·90°`, `z₂` at `−σ·30°`, `dist z₁ z₂ = 1` from `hexagon_exact`); lower points at `≈ ±150°`
(height `≤ −cos 32.6° < −0.84`).  Cap: the point at `180°` has height `≤ −0.99`, those at
`±120°` height `≥ −0.53 > −2/3`.
Acceptance: no `sorry`.
Depends on: `hexagon_exact`, `pair_K`, `pair_D`, `frame_outside`, `frame_D`, `Frame43.top`,
`Sset_not_interior`. Difficulty L. -/
theorem lemmaH (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) (hy : y ∈ Rset X)
    (hd : degδ X y = 6) (hm : mS X y = 3) : FanShape X y n ∨ CapShape X y n := by
  have hPc : ((nbδ X y).filter (· ∈ Sset X)).card = 3 := hm
  obtain ⟨p1, p2, p3, h12, h13, h23, hPeq⟩ := card_eq_three.1 hPc
  have hmem : ∀ p, p = p1 ∨ p = p2 ∨ p = p3 → p ∈ nbδ X y ∧ p ∈ Sset X := by
    intro p hp
    have : p ∈ (nbδ X y).filter (· ∈ Sset X) := by
      rw [hPeq]; rcases hp with rfl | rfl | rfl <;> simp
    exact mem_filter.1 this
  obtain ⟨hn1, hS1⟩ := hmem p1 (Or.inl rfl)
  obtain ⟨hn2, hS2⟩ := hmem p2 (Or.inr (Or.inl rfl))
  obtain ⟨hn3, hS3⟩ := hmem p3 (Or.inr (Or.inr rfl))
  by_cases d1 : p1 ∈ Dset X <;> by_cases d2 : p2 ∈ Dset X <;> by_cases d3 : p3 ∈ Dset X
  · exact (c43_three_D hX hF hn1 hn2 hn3 h12 h13 h23 d1 d2 d3).elim
  · exact c43_coreD hX hF hd hm hn1 hn2 hn3 h12 h13 h23 hS1 d1 hS2 d2 hS3 d3
  · exact c43_coreD hX hF hd hm hn1 hn3 hn2 h13 h12 (Ne.symm h23) hS1 d1 hS3 d3 hS2 d2
  · exact c43_coreK hX hF hd hm hn2 hn3 hn1 h23 (Ne.symm h12) (Ne.symm h13) hS2 d2 hS3 d3 hS1 d1
  · exact c43_coreD hX hF hd hm hn2 hn3 hn1 h23 (Ne.symm h12) (Ne.symm h13) hS2 d2 hS3 d3 hS1 d1
  · exact c43_coreK hX hF hd hm hn1 hn3 hn2 h13 h12 (Ne.symm h23) hS1 d1 hS3 d3 hS2 d2
  · exact c43_coreK hX hF hd hm hn1 hn2 hn3 h12 h13 h23 hS1 d1 hS2 d2 hS3 d3
  · exact (c43_three_K hX hF hn1 hn2 hn3 h12 h13 h23 hS1 d1 hS2 d2 hS3 d3).elim

/-! ## Lemma Pin -/

/-- **Lemma Pin (fan)**: fan slots force `t ≥ 0.7` (paper: `t ∈ [0.74, 0.99]`, referee exact
window `[0.751, 0.950]`).

TODO: none — proved.
What's missing: `p` (K-row, slot `−σ·90°`, height `≤ 1/20`) and `z₁` (D, slot `σ·30°`, height
`≥ √3/2 − 1/20`): `Δc ≥ 0.766`.  Take `w` from `n1_circle_normal` (`|p − w| = Δ₂`,
`ν = (p − w)/Δ₂` an outer unit normal at `p ∈ ∂K`, `ball_polygon_b`); `‖ν − n‖ ≤ 1/50`
(`Frame43.normals`), so `⟨z₁ − p, w − p⟩/Δ₂ ≤ −Δc + 2/50 < 0`: `z₁` is not normal for `p`,
hence `|z₁ − w| = Δ` (`dist_le_dist2`: otherwise `≤ Δ₂` and the inner product is
`≥ |z₁ − p|²/2 > 0`).  Law of cosines: `⟨z₁ − p, w − p⟩/Δ₂ = −t + (d² − t²)/(2Δ₂)`, `d ≤ 2`,
`t ≤ 1` (`ball_polygon_c`): `t ≥ 0.766 − 0.04 − 10⁻⁴ > 0.7`.
Acceptance: no `sorry`.
Depends on: `n1_circle_normal`, `ball_polygon_b`, `ball_polygon_c`, `dist_le_dist2`,
`Frame43.normals`, `n1_inner_frame`. Difficulty M. -/
theorem pin_fan (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) (hs : FanSlots X y n) :
    7 / 10 ≤ tgap X := by
  obtain ⟨σ, hσ, p, hp, -, -, z, hz, hpS, hpD, hzD, hsp, -, hsz, -⟩ := hs
  have hn := hF.unit
  have hpX := (mem_nbδ.1 hp).1
  have hzX := (mem_nbδ.1 hz).1
  have hpb : p ∈ frontier (KBall X) := ball_polygon_b hpS hpD
  obtain ⟨w, hw, hpw, hnorm⟩ := n1_circle_normal hX hpb
  have hΔ2 := hX.dist2_pos
  set ν : Pt := (dist2 X)⁻¹ • (p - w) with hνdef
  have hν1 : ‖ν‖ = 1 := by
    rw [hνdef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hΔ2), ← dist_eq_norm, hpw,
      inv_mul_cancel₀ hΔ2.ne']
  have hνc : ν ∈ normalCone (KBall X) p := by
    intro k hk
    rw [hνdef, inner_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hΔ2.le) (hnorm k hk)
  have hνn : ‖ν - n‖ ≤ 1 / 50 := hF.normals p hpb
    (by rw [dist_comm, dist_of_mem_nbδ hX hp]; norm_num) ν hνc hν1
  obtain ⟨hpZ, -⟩ := c43_slot_coords hn hsp
  obtain ⟨hzZ, -⟩ := c43_slot_coords hn hsz
  have hc1 : Real.cos (-(σ * (π / 2))) = 0 := by
    rw [Real.cos_neg]
    rcases hσ with rfl | rfl
    · rw [one_mul, Real.cos_pi_div_two]
    · rw [neg_one_mul, Real.cos_neg, Real.cos_pi_div_two]
  have hc2 : Real.cos (σ * (π / 6)) = √3 / 2 := by
    rcases hσ with rfl | rfl
    · rw [one_mul, Real.cos_pi_div_six]
    · rw [neg_one_mul, Real.cos_neg, Real.cos_pi_div_six]
  rw [hc1] at hpZ
  rw [hc2] at hzZ
  have hr := c43_r_lo
  -- `z − p` in the frame
  have hzp_eq : z - p = (z - y) - (p - y) := by abel
  have hzp2 : ‖z - p‖ ≤ 2 := by
    rw [hzp_eq]
    have := norm_sub_le (z - y) (p - y)
    rw [← dist_eq_norm z y, ← dist_eq_norm p y, dist_of_mem_nbδ hX hz,
      dist_of_mem_nbδ hX hp] at this
    linarith
  have hzpn : inner ℝ (z - p) n = inner ℝ (z - y) n - inner ℝ (p - y) n := by
    rw [hzp_eq, inner_sub_left]
  have hS : 363 / 500 ≤ inner ℝ (z - p) ν := by
    have e : inner ℝ (z - p) ν = inner ℝ (z - p) n + inner ℝ (z - p) (ν - n) := by
      rw [inner_sub_right]; ring
    have h1 := abs_real_inner_le_norm (z - p) (ν - n)
    have h2 : ‖z - p‖ * ‖ν - n‖ ≤ 2 * (1 / 50) :=
      mul_le_mul hzp2 hνn (norm_nonneg _) (by norm_num)
    have h3 := (abs_le.1 h1).1
    have h4 := (abs_le.1 hpZ).2
    have h5 := (abs_le.1 hzZ).1
    rw [e, hzpn]
    linarith
  -- `w − p = −Δ₂ ν`
  have hwp : w - p = -(dist2 X) • ν := by
    rw [hνdef, smul_smul, neg_mul, mul_inv_cancel₀ hΔ2.ne', neg_smul, one_smul, neg_sub]
  have hinner : inner ℝ (z - p) (w - p) = -(dist2 X) * inner ℝ (z - p) ν := by
    rw [hwp, inner_smul_right]
  have hwpn : ‖w - p‖ = dist2 X := by rw [← dist_eq_norm, dist_comm, hpw]
  have hcos : ‖z - w‖ ^ 2 = ‖z - p‖ ^ 2 - 2 * inner ℝ (z - p) (w - p) + ‖w - p‖ ^ 2 := by
    rw [← norm_sub_sq_real, sub_sub_sub_cancel_right]
  have hzw : dist z w = diam X := by
    by_contra hne
    have hle := dist_le_dist2 hzX hw hne
    rw [dist_eq_norm] at hle
    have : ‖z - w‖ ^ 2 ≤ dist2 X ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
    rw [hcos, hinner, hwpn] at this
    nlinarith [sq_nonneg ‖z - p‖, mul_pos hΔ2 (show (0 : ℝ) < inner ℝ (z - p) ν by linarith)]
  have hd1 : 1 ≤ ‖z - p‖ := by
    rw [← dist_eq_norm]
    exact one_le_dist hX.minDist_eq hzX hpX (fun h => hpD (h ▸ hzD))
  have ht0 := c43_tgap_pos hX
  rw [dist_eq_norm] at hzw
  have hdiam : diam X = dist2 X + tgap X := by unfold tgap; ring
  have hkey := hcos
  rw [hinner, hwpn, hzw, hdiam] at hkey
  by_contra hlt
  push Not at hlt
  have hd1' : 1 ≤ ‖z - p‖ ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hS hΔ2.le, mul_lt_mul_of_pos_left hlt hΔ2,
    mul_lt_mul_of_pos_left hlt ht0]

/-- **Lemma Pin (cap)**: cap shape forces `t ≤ 0.6` (paper: `[0.43, 0.57]`, referee
`[0.442, 0.558]`).

TODO: none — proved.
What's missing: `frame_D` at `z` (slot `0°`: height `≤ 1`, `|Xz| ≤ 1/20`) and `Frame43.top` at
`p` (slot `σ·60°`: height `≥ 1/2 − 1/20`): `t ≤ Z z − Z p + |Xz|/49 ≤ 0.551`.
Acceptance: no `sorry`.
Depends on: `frame_D`, `Frame43.top`, `ball_polygon_a`, `n1_inner_frame`. Difficulty S–M. -/
theorem pin_cap (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) (hc : CapShape X y n) :
    tgap X ≤ 3 / 5 := by
  obtain ⟨⟨σ, hσ, p, hp, z, hz, -, hpD, hzD, hsp, hsz⟩, -, -⟩ := hc
  have hn := hF.unit
  have htop := c43_K_top hF hp hpD
  have hfD := c43_D_low hX hF hz hzD
  obtain ⟨hpZ, -⟩ := c43_slot_coords hn hsp
  obtain ⟨-, hzX⟩ := c43_slot_coords hn hsz
  have hcos : Real.cos (σ * (π / 3)) = 1 / 2 := by
    rcases hσ with rfl | rfl
    · rw [one_mul, Real.cos_pi_div_three]
    · rw [neg_one_mul, Real.cos_neg, Real.cos_pi_div_three]
  rw [hcos] at hpZ
  rw [Real.sin_zero, sub_zero] at hzX
  have hz1 := c43_unit hX hn hz
  have hzZ : inner ℝ (z - y) n ≤ 1 := by nlinarith [sq_nonneg (inner ℝ (z - y) (perp n))]
  have h1 := (abs_le.1 hpZ).1
  nlinarith [abs_nonneg (inner ℝ (z - y) (perp n))]

/-! ## Outputs -/

/-- Heavy framed points have fan or cap shape.

TODO: none — proved from the statements.
Acceptance: no `sorry` (inherits).
Depends on: `mS_le_four_of_frame`, `degδ_le_six`, `fanShape_of_m4`, `lemmaH`. -/
theorem heavy_shape (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) (hy : y ∈ Rset X)
    (h9 : 9 ≤ vR X y) : FanShape X y n ∨ CapShape X y n := by
  have hm := mS_le_four_of_frame hX hF
  have hd := degδ_le_six X y
  unfold vR at h9
  by_cases h4 : mS X y = 4
  · exact Or.inl (fanShape_of_m4 hX hF hy h4 (by omega))
  · exact lemmaH hX hF hy (by omega) (by omega)

/-- **Classification output (types)**: a heavy framed point is of fan or cap type.

TODO: none — proved from the statements.
Acceptance: no `sorry` (inherits).
Depends on: `heavy_shape`, `pin_fan`, `pin_cap`, `Low_Z`, `Low_subset`. -/
theorem heavy_type (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) (hy : y ∈ Rset X)
    (h9 : 9 ≤ vR X y) : IsFan43 X y n ∨ IsCap43 X y n := by
  rcases heavy_shape hX hF hy h9 with ⟨hs, hlow, -⟩ | hc
  · refine Or.inl ⟨pin_fan hX hF hs, fun a ha => ?_, hs⟩
    have hZ := Low_Z hX hF ha
    have := hlow a (Low_subset X y ha) hZ
    rw [show y - a = -(a - y) by abel, inner_neg_left]
    linarith
  · exact Or.inr ⟨pin_cap hX hF hc, fun a ha => hc.2.1 a (Low_subset X y ha) (Low_Z hX hF ha)⟩

/-- **Classification output (excess)**: `v(y) ≤ 8 + |Low X y|` at a heavy framed point.

TODO: none — proved from the statements.
Acceptance: no `sorry` (inherits).
Depends on: `heavy_shape`, `lower_mem_Low`. -/
theorem heavy_low (hX : Normal X) {y n : Pt} (hF : Frame43 X y n) (hy : y ∈ Rset X)
    (h9 : 9 ≤ vR X y) : vR X y ≤ 8 + (Low X y).card := by
  have hsub : (nbδ X y).filter (fun a => inner ℝ (a - y) n ≤ -(4 / 5)) ⊆ Low X y :=
    fun a ha => lower_mem_Low hX hF (mem_filter.1 ha).1 (mem_filter.1 ha).2
  have hc := card_le_card hsub
  rcases heavy_shape hX hF hy h9 with ⟨-, -, hv⟩ | ⟨-, -, hv⟩ <;> omega

end

end Erdos132Main
