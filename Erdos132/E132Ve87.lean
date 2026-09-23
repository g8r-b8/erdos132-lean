import Erdos132.E132Layer

/-!
# Erdős Problem 132: Vesztergombi 1987 — the second-largest distance occurs at most `3n/2` times

K. Vesztergombi, *On large distances in planar sets*, Discrete Math. 67 (1987) 191–198:
for every finite `X ⊆ ℝ²`, `2 μ(Δ₂) ≤ 3 |X|`.

We do **not** follow Vesztergombi's deletion/induction proof (deleting points can change `Δ` and
`Δ₂`).  Instead we work in the 2-core `G′` of the `Δ₂`-graph on `L₁ ∪ L₂`, reusing
`Erdos132.E132Layer` (location of `Δ₂`-pairs, Prop 3, `deg′ ≤ 4` on `L₁′`, `esum_le_core`):

* (**middle lemma**, new; Ve87's "it is easy to see" in Prop 7) if `p` is extreme and `w` is a
  `Δ₂`-neighbour of `p` with one neighbour `b` of `p` strictly on one side of the line `pw` and two
  neighbours `a₁, a₂` strictly on the other side (in angular order), then `w` has at most one
  `Δ₂`-neighbour besides `p`.  (Lemma F puts every such neighbour `r` strictly on the `a`-side,
  Lemma M gives `|rb| = Δ`, and two such `r ≠ r'` are mirror images in the line `wb`, which is
  incompatible with `|pr|, |pr'| ∈ (0, Δ₂] ∪ {Δ}`.)
* hence every `p ∈ L₁′` of core degree `4` has two core neighbours (its middle neighbours) of core
  degree `2`;
* core degrees lie in `[2, 4]` (Prop 3 and `deg′ ≤ 4`), so a double count of the edges between
  degree-4 and degree-2 vertices gives `#{deg′ = 4} ≤ #{deg′ = 2}`, hence `Σ deg′ ≤ 3 |V(G′)|`;
* `2 μ(Δ₂) = esum(L₁ ∪ L₂) ≤ esum(G′) + 2 |(L₁ ∪ L₂) \ V(G′)| ≤ 3 |L₁ ∪ L₂| ≤ 3 |X|`.

The final statement `vesztergombi87` has the shape of `Erdos132Main.vesztergombi87`
(`E132MainDefs.lean`), with local copies `diam`, `dist2` of the definitions there.
-/

open Finset
open Erdos132Convex

namespace Erdos132Ve87

open Erdos132Layer

/-! ## The middle lemma -/

/-- Mixed case of the middle lemma: `|r|² = D`, `|s|² ≤ 1`.  With `S = U + V ∥ 1 − B`
(complex notation, `U = u`, `V = v`, `B = b`), `UV · S̄ = S` and `(−B) · (1 − B)‾ = 1 − B` give
`UV = −B`; then `|s − b|² = D` reads `b₀ = v₀ + 1/2 ≤ 0`, which forces `u₀ < 0`, contradicting
`u₀ + v₀ > 0`. -/
theorem mid_mixed_real {u0 u1 v0 v1 b0 b1 : ℝ}
    (hu : u0 ^ 2 + u1 ^ 2 = 1) (hv : v0 ^ 2 + v1 ^ 2 = 1) (hb : b0 ^ 2 + b1 ^ 2 = 1)
    (hu1 : u1 < 0) (hv1 : v1 < 0) (hb1 : 0 < b1) (hb0 : b0 < 1)
    (hX : (u0 + v0) * b1 + (u1 + v1) * (1 - b0) = 0) (hs0 : 0 < u0 + v0)
    (es : (1 + v0 - b0) ^ 2 + (v1 - b1) ^ 2 = 2 + 2 * u0) (hv0 : 2 + 2 * v0 ≤ 1) : False := by
  have R : (u0 * v0 - u1 * v1) * (u0 + v0) + (u0 * v1 + u1 * v0) * (u1 + v1) = u0 + v0 := by
    linear_combination v0 * hu + u0 * hv
  have I : (u0 * v1 + u1 * v0) * (u0 + v0) - (u0 * v0 - u1 * v1) * (u1 + v1) = u1 + v1 := by
    linear_combination v1 * hu + u1 * hv
  have E1 : (u0 + v0) * ((u0 * v0 - u1 * v1) * (1 - b0) - (u0 * v1 + u1 * v0) * b1 - (1 - b0))
      = 0 := by
    linear_combination (1 - b0) * R - (u0 * v1 + u1 * v0) * hX
  have E2 : (u0 + v0) * ((u0 * v1 + u1 * v0) * (1 - b0) + (u0 * v0 - u1 * v1) * b1 + b1)
      = 0 := by
    linear_combination (1 - b0) * I + (u0 * v0 - u1 * v1 + 1) * hX
  have e1 := (mul_eq_zero.1 E1).resolve_left hs0.ne'
  have e2 := (mul_eq_zero.1 E2).resolve_left hs0.ne'
  have hc : 0 < (1 - b0) ^ 2 + b1 ^ 2 := by have := pow_pos hb1 2; positivity
  have F0 : (u0 * v0 - u1 * v1 + b0) * ((1 - b0) ^ 2 + b1 ^ 2) = 0 := by
    linear_combination (1 - b0) * e1 + b1 * e2 - (1 - b0) * hb
  have F1 : (u0 * v1 + u1 * v0 + b1) * ((1 - b0) ^ 2 + b1 ^ 2) = 0 := by
    linear_combination (1 - b0) * e2 - b1 * e1 + b1 * hb
  have f0 := (mul_eq_zero.1 F0).resolve_right hc.ne'
  have f1 := (mul_eq_zero.1 F1).resolve_right hc.ne'
  have hbv : b0 = v0 + 1 / 2 := by
    linear_combination (-1/2 : ℝ) * es + (1/2 : ℝ) * hv + (1/2 : ℝ) * hb +
      - v0 * f0 - v1 * f1 + u0 * hv
  have huv : 0 < u1 * v1 := mul_pos_of_neg_of_neg hu1 hv1
  have : 0 < u0 * v0 := by linarith
  have hu0 : u0 < 0 := by
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos this with h | h
    · linarith [h.2]
    · exact h.1
  linarith

/-- **Middle lemma, real core.**  Frame: `p = 0`, `w = (1, 0)`, `b` a unit vector strictly above
the axis.  `r = w + u` and `s = w + v` (`u, v` unit, strictly below the axis) are both at squared
distance `D` from `b`, and each of `|r|², |s|²` is `≤ 1` or `= D`.  Then `r = s`.

Proof: `r ≠ s` ⇒ `(u + v) × (w − b) = 0` ⇒ `u₀ + v₀ > 0`; so not both `|r|², |s|² ≤ 1`; both `= D`
gives `r = s`; the mixed case is `mid_mixed_real`. -/
theorem mid_pair_real {u0 u1 v0 v1 b0 b1 D : ℝ} (_hD : 1 < D)
    (hu : u0 ^ 2 + u1 ^ 2 = 1) (hv : v0 ^ 2 + v1 ^ 2 = 1) (hb : b0 ^ 2 + b1 ^ 2 = 1)
    (hu1 : u1 < 0) (hv1 : v1 < 0) (hb1 : 0 < b1)
    (er : (1 + u0 - b0) ^ 2 + (u1 - b1) ^ 2 = D) (es : (1 + v0 - b0) ^ 2 + (v1 - b1) ^ 2 = D)
    (gr : (1 + u0) ^ 2 + u1 ^ 2 ≤ 1 ∨ (1 + u0) ^ 2 + u1 ^ 2 = D)
    (gs : (1 + v0) ^ 2 + v1 ^ 2 ≤ 1 ∨ (1 + v0) ^ 2 + v1 ^ 2 = D) :
    u0 = v0 ∧ u1 = v1 := by
  by_contra hne
  have hd : 0 < (u0 - v0) ^ 2 + (u1 - v1) ^ 2 := by
    by_contra h; push Not at h
    have a := sq_nonneg (u0 - v0)
    have b := sq_nonneg (u1 - v1)
    have ha : (u0 - v0) ^ 2 = 0 := by linarith
    have hb' : (u1 - v1) ^ 2 = 0 := by linarith
    exact hne ⟨by linarith [pow_eq_zero_iff (n := 2) two_ne_zero |>.1 ha],
      by linarith [pow_eq_zero_iff (n := 2) two_ne_zero |>.1 hb']⟩
  have ha : (u0 - v0) * (1 - b0) - (u1 - v1) * b1 = 0 := by
    linear_combination (1/2 : ℝ) * er - (1/2 : ℝ) * es - (1/2 : ℝ) * hu + (1/2 : ℝ) * hv
  have hX' : ((u0 - v0) ^ 2 + (u1 - v1) ^ 2) * ((u0 + v0) * b1 + (u1 + v1) * (1 - b0)) = 0 := by
    linear_combination ((u0 - v0) * (u1 + v1) - (u1 - v1) * (u0 + v0)) * ha -
      ((u0 - v0) * (-b1) - (u1 - v1) * (1 - b0)) * (hu - hv)
  have hX : (u0 + v0) * b1 + (u1 + v1) * (1 - b0) = 0 :=
    (mul_eq_zero.1 hX').resolve_left hd.ne'
  have hb0 : b0 < 1 := by
    have h2 := pow_pos hb1 2
    have : b0 ^ 2 < 1 := by linarith
    exact (abs_lt.1 ((sq_lt_one_iff_abs_lt_one b0).1 this)).2
  have hs0 : 0 < u0 + v0 := by
    have : 0 < (u0 + v0) * b1 := by
      have : 0 < -(u1 + v1) * (1 - b0) := mul_pos (by linarith) (by linarith)
      linarith
    exact (pos_iff_pos_of_mul_pos this).2 hb1
  have nr : (1 + u0) ^ 2 + u1 ^ 2 = 2 + 2 * u0 := by linear_combination hu
  have ns : (1 + v0) ^ 2 + v1 ^ 2 = 2 + 2 * v0 := by linear_combination hv
  rcases gr with gr | gr <;> rcases gs with gs | gs
  · linarith
  · exact mid_mixed_real hv hu hb hv1 hu1 hb1 hb0 (by linear_combination hX) (by linarith)
      (by rw [← ns, gs]; exact er) (by linarith)
  · exact mid_mixed_real hu hv hb hu1 hv1 hb1 hb0 hX hs0 (by rw [← nr, gr]; exact es)
      (by linarith)
  · have h0 : u0 = v0 := by linarith
    have h1 : (u1 - v1) * (u1 + v1) = 0 := by linear_combination hu - hv - (u0 + v0) * h0
    have : u1 - v1 = 0 := (mul_eq_zero.1 h1).resolve_right (by linarith)
    exact hne ⟨h0, by linarith⟩

/-- **Middle lemma.**  Let `p` have `Δ₂`-neighbours `w, a₁, a₂, b` with (for a sign `σ = ±1`)
`a₁, a₂` strictly on one side of the line `pw`, `b` strictly on the other, and `b` after `a₁, a₂`
in angular order.  Then `w` has at most one `Δ₂`-neighbour other than `p`.

Proof: frame at `p` with axis `w` and second coordinate multiplied by `σ`; `lemmaF_real` puts
every other neighbour strictly on the `a`-side, `lemmaM_real` (reflected) gives distance `Δ` to
`b`, then `mid_pair_real`. -/
theorem mid_nbr_unique {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) {p w a₁ a₂ b : Pt} (hp : p ∈ X)
    (hw : w ∈ X) (ha₁ : a₁ ∈ X) (ha₂ : a₂ ∈ X) (hb : b ∈ X)
    (dw : dist p w = Δ₂) (da₁ : dist p a₁ = Δ₂) (da₂ : dist p a₂ = Δ₂) (db : dist p b = Δ₂)
    (hna : a₁ ≠ a₂)
    (oa₁ : σ * orient p w a₁ < 0) (oa₂ : σ * orient p w a₂ < 0) (ob : 0 < σ * orient p w b)
    (o₁ : 0 < σ * orient p a₁ b) (o₂ : 0 < σ * orient p a₂ b)
    {r s : Pt} (hr : r ∈ X) (hs : s ∈ X) (hrp : r ≠ p) (hsp : s ≠ p)
    (dr : dist w r = Δ₂) (ds : dist w s = Δ₂) : r = s := by
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hσ0 : σ ≠ 0 := by rintro rfl; norm_num at hσ2
  have hpos := hT.pos
  have hs0 : 0 < Δ₂ ^ 2 := by positivity
  have hne := ne_of_dist_snd hpos dw
  have hsq : sqd p w = Δ₂ ^ 2 := (dist_eq_iff_sqd hpos.le).1 dw
  have hwp := sqd_pos_of_ne hne
  set U : Pt → ℝ := fun P => fx p w P with hU
  set V : Pt → ℝ := fun P => σ * fy p w P with hV
  have N : ∀ P Q, (U P - U Q) ^ 2 + (V P - V Q) ^ 2 = sqd P Q / Δ₂ ^ 2 := fun P Q => by
    rw [← frame_nsq hne hsq P Q]; simp only [hU, hV]; linear_combination
      (fy p w P - fy p w Q) ^ 2 * hσ2
  have m0 : U w = 1 := (frame_axis hne).1
  have m1 : V w = 0 := by simp only [hV, (frame_axis hne).2, mul_zero]
  have z0 : U p = 0 := (frame_base p w).1
  have z1 : V p = 0 := by simp only [hV, (frame_base p w).2, mul_zero]
  have unit : ∀ P, dist p P = Δ₂ → U P ^ 2 + V P ^ 2 = 1 := fun P hP => by
    have := N P p
    rw [z0, z1, sub_zero, sub_zero, sqd_comm, (dist_eq_iff_sqd hpos.le).1 hP,
      div_self hs0.ne'] at this
    exact this
  have gap : ∀ P ∈ X, ∀ Q ∈ X, (U P - U Q) ^ 2 + (V P - V Q) ^ 2 ≤ 1 ∨
      (U P - U Q) ^ 2 + (V P - V Q) ^ 2 = Δ ^ 2 / Δ₂ ^ 2 :=
    fun P hP Q hQ => by rw [N]; exact hT.ngap hP hQ
  have mx : ∀ P ∈ X, ∀ Q ∈ X, (U P - U Q) ^ 2 + (V P - V Q) ^ 2 ≤ Δ ^ 2 / Δ₂ ^ 2 :=
    fun P hP Q hQ => by rw [N]; exact hT.nle hP hQ
  have gw : ∀ P ∈ X, (U P - 1) ^ 2 + V P ^ 2 ≤ 1 ∨ (U P - 1) ^ 2 + V P ^ 2 = Δ ^ 2 / Δ₂ ^ 2 :=
    fun P hP => by have := gap P hP w hw; rw [m0, m1, sub_zero] at this; exact this
  have side : ∀ P, V P = σ * orient p w P / sqd p w := fun P => by
    simp only [hV, fy]; ring
  have vneg : ∀ P, σ * orient p w P < 0 → V P < 0 := fun P h => by
    rw [side]; exact div_neg_of_neg_of_pos h hwp
  have vpos : ∀ P, 0 < σ * orient p w P → 0 < V P := fun P h => by
    rw [side]; exact div_pos h hwp
  have crpos : ∀ P Q, 0 < σ * orient p P Q → 0 < U P * V Q - V P * U Q := fun P Q h => by
    have e : U P * V Q - V P * U Q = σ * (fx p w P * fy p w Q - fy p w P * fx p w Q) := by
      simp only [hU, hV]; ring
    rw [e, frame_cross hne, ← mul_div_assoc]; exact div_pos h hwp
  -- every other neighbour of `w` is strictly on the `a`-side and at distance `Δ` from `b`
  have below : ∀ r ∈ X, r ≠ p → dist w r = Δ₂ →
      (U r - 1) ^ 2 + V r ^ 2 = 1 ∧ V r < 0 ∧
        (U r - U b) ^ 2 + (V r - V b) ^ 2 = Δ ^ 2 / Δ₂ ^ 2 := by
    intro r hr hrp dr
    have hr1 : (U r - 1) ^ 2 + V r ^ 2 = 1 := by
      have := N r w
      rw [m0, m1, sub_zero, sqd_comm, (dist_eq_iff_sqd hpos.le).1 dr, div_self hs0.ne'] at this
      exact this
    have hr0 : 0 < U r ^ 2 + V r ^ 2 := by
      have := N r p
      rw [z0, z1, sub_zero, sub_zero] at this
      rw [this]; exact div_pos (sqd_pos_of_ne hrp) hs0
    have hyr : V r < 0 := by
      by_contra hyr; push Not at hyr
      exact lemmaF_real hT.one_lt (unit a₁ da₁) (unit a₂ da₂) (unit b db) (vneg a₁ oa₁)
        (vneg a₂ oa₂) (vpos b ob)
        (fun h => hna (by
          refine by_contra fun hne' => frame_inj hne hne' ⟨h.1, ?_⟩
          exact mul_left_cancel₀ hσ0 h.2))
        (crpos a₁ b o₁) (crpos a₂ b o₂) hr1 hr0 hyr (gap r hr a₁ ha₁) (gap r hr a₂ ha₂)
        (gw a₁ ha₁) (gw a₂ ha₂) (mx a₁ ha₁ b hb) (mx a₂ ha₂ b hb)
    refine ⟨hr1, hyr, (gap r hr b hb).resolve_left fun hle => ?_⟩
    have := lemmaM_real (xa := U b) (ya := -V b) (xr := U r) (yr := -V r)
      (by rw [neg_sq]; exact unit b db) (by linarith [vpos b ob]) (by rw [neg_sq]; exact hr1)
      (by linarith) (by rw [neg_sq]; exact hr0)
    have e : (U r - U b) ^ 2 + (-V r - -V b) ^ 2 = (U r - U b) ^ 2 + (V r - V b) ^ 2 := by ring
    linarith
  obtain ⟨r1, rneg, rb⟩ := below r hr hrp dr
  obtain ⟨s1, sneg, sb⟩ := below s hs hsp ds
  have gp : ∀ P ∈ X, (1 + (U P - 1)) ^ 2 + V P ^ 2 ≤ 1 ∨
      (1 + (U P - 1)) ^ 2 + V P ^ 2 = Δ ^ 2 / Δ₂ ^ 2 := fun P hP => by
    have := gap P hP p hp
    rw [z0, z1, sub_zero, sub_zero] at this
    rw [show 1 + (U P - 1) = U P by ring]; exact this
  have e1 : ∀ P, (1 + (U P - 1) - U b) ^ 2 = (U P - U b) ^ 2 := fun P => by ring
  obtain ⟨h0, h1⟩ := mid_pair_real hT.one_lt r1 s1
    (unit b db) rneg sneg (vpos b ob) (by rw [e1]; exact rb) (by rw [e1]; exact sb)
    (gp r hr) (gp s hs)
  by_contra hrs
  exact frame_inj hne hrs ⟨by simp only [hU] at h0; linarith,
    mul_left_cancel₀ hσ0 h1⟩

/-! ## Angular order and core vertices of degree 4 -/

/-- The `Δ₂`-neighbours (in a set `S` of size `k`) of an extreme point can be listed in strict
angular order.

Proof: the slope-function sort of `Erdos132Layer.exists_median`, for general `k`. -/
theorem exists_sorted {X : Finset Pt} {Δ₂ : ℝ} {p : Pt} (hp : IsExt X p) {S : Finset Pt}
    (hSX : S ⊆ X) (hS : ∀ x ∈ S, dist p x = Δ₂) (hpos : 0 < Δ₂) {k : ℕ} (hk : S.card = k) :
    ∃ f : Fin k → Pt, (∀ i, f i ∈ S) ∧ Function.Injective f ∧
      ∀ i j, i < j → 0 < orient p (f i) (f j) := by
  classical
  obtain ⟨-, α, β, hαβ⟩ := hp
  have hSp : ∀ x ∈ S, x ≠ p := fun x hx h => by
    have := hS x hx; rw [h, dist_self] at this; linarith
  have hN : ∀ x ∈ S, 0 < -(α * (x 0 - p 0) + β * (x 1 - p 1)) := fun x hx => by
    linarith [hαβ x (hSX hx) (hSp x hx)]
  set g : Pt → ℝ := fun x =>
    (-α * (x 1 - p 1) + β * (x 0 - p 0)) / -(α * (x 0 - p 0) + β * (x 1 - p 1)) with hg
  have anti : ∀ x y, orient p y x = -orient p x y := fun x y => by simp only [orient]; ring
  by_cases hk0 : k = 0
  · subst hk0
    exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  have hn : 0 < α ^ 2 + β ^ 2 := by
    obtain ⟨x, hx⟩ : S.Nonempty := card_pos.1 (by omega)
    by_contra h; push Not at h
    have ha : α = 0 := by nlinarith [sq_nonneg α, sq_nonneg β]
    have hb : β = 0 := by nlinarith [sq_nonneg α, sq_nonneg β]
    have := hN x hx; rw [ha, hb] at this; simp at this
  have key : ∀ x ∈ S, ∀ y ∈ S, (0 < orient p x y ↔ g x < g y) := by
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
  have inj : Set.InjOn g S := by
    intro x hx y hy hxy
    have ho : orient p x y = 0 := by
      rcases lt_trichotomy (orient p x y) 0 with h | h | h
      · have h' : 0 < orient p y x := by rw [anti]; linarith
        have := (key y hy x hx).1 h'; rw [hxy] at this; exact absurd this (lt_irrefl _)
      · exact h
      · have := (key x hx y hy).1 h; rw [hxy] at this; exact absurd this (lt_irrefl _)
    have hd : sqd p x = sqd p y := by
      rw [(dist_eq_iff_sqd hpos.le).1 (hS x hx), (dist_eq_iff_sqd hpos.le).1 (hS y hy)]
    exact eq_of_orient_zero hd ho (hN x hx) (hN y hy)
  set T := S.image g with hT
  have hTk : T.card = k := by rw [hT, card_image_of_injOn inj, hk]
  set emb := T.orderEmbOfFin hTk with hemb
  have pre : ∀ i : Fin k, ∃ x ∈ S, g x = emb i := fun i =>
    mem_image.1 (orderEmbOfFin_mem T hTk i)
  choose f hfS hfg using pre
  refine ⟨f, hfS, fun i j h => ?_, fun i j hij =>
    (key _ (hfS i) _ (hfS j)).2 (by rw [hfg, hfg]; exact emb.strictMono hij)⟩
  have := congrArg g h; rw [hfg, hfg] at this; exact emb.injective this

/-- A core vertex `p ∈ L₁` of core degree `4` has at least two core neighbours of core degree
`2` (its two middle neighbours).

Proof: sort the four neighbours `f 0, …, f 3`; apply `mid_nbr_unique` to `f 1` (`σ = −1`) and
`f 2` (`σ = 1`); core degree `≥ 2` from `minDeg2_core`. -/
theorem two_le_mid {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) {p : Pt}
    (hp : p ∈ L1 X) (h4 : (nbr (core (L1 X ∪ L2 X) Δ₂) Δ₂ p).card = 4) :
    2 ≤ ((nbr (core (L1 X ∪ L2 X) Δ₂) Δ₂ p).filter
      (fun w => (nbr (core (L1 X ∪ L2 X) Δ₂) Δ₂ w).card = 2)).card := by
  set K := core (L1 X ∪ L2 X) Δ₂ with hKdef
  have hKX : K ⊆ X := (core_subset _ _).trans (union_subset (L1_subset X) (L2_subset X))
  have hpE : IsExt X p := mem_L1.1 hp
  have hpX : p ∈ X := hpE.1
  have hsub : nbr K Δ₂ p ⊆ X := fun x hx => hKX (mem_nbr.1 hx).1
  obtain ⟨f, hfS, hfi, ord⟩ :=
    exists_sorted hpE hsub (fun x hx => (mem_nbr.1 hx).2) hT.pos h4
  have anti : ∀ x y, orient p y x = -orient p x y := fun x y => by simp only [orient]; ring
  have fX : ∀ i, f i ∈ X := fun i => hsub (hfS i)
  have fd : ∀ i, dist p (f i) = Δ₂ := fun i => (mem_nbr.1 (hfS i)).2
  have fne : ∀ i j : Fin 4, i ≠ j → f i ≠ f j := fun i j h e => h (hfi e)
  -- a vertex `w ∈ K` all of whose `Δ₂`-neighbours other than `p` coincide has core degree `2`
  have deg2 : ∀ w ∈ nbr K Δ₂ p, (∀ r ∈ X, ∀ s ∈ X, r ≠ p → s ≠ p → dist w r = Δ₂ →
      dist w s = Δ₂ → r = s) → (nbr K Δ₂ w).card = 2 := by
    intro w hw huniq
    have hwK := (mem_nbr.1 hw).1
    have h2 : 2 ≤ (nbr K Δ₂ w).card := minDeg2_core _ _ w hwK
    have h1 : ((nbr K Δ₂ w).erase p).card ≤ 1 := by
      refine card_le_one.2 fun a ha b hb => ?_
      obtain ⟨hap, ha'⟩ := mem_erase.1 ha
      obtain ⟨hbp, hb'⟩ := mem_erase.1 hb
      exact huniq a (hKX (mem_nbr.1 ha').1) b (hKX (mem_nbr.1 hb').1) hap hbp
        (mem_nbr.1 ha').2 (mem_nbr.1 hb').2
    have := pred_card_le_card_erase (s := nbr K Δ₂ w) (a := p)
    omega
  have o : ∀ i j : Fin 4, i < j → 0 < orient p (f i) (f j) := ord
  have d2 : (nbr K Δ₂ (f 2)).card = 2 := deg2 _ (hfS 2) fun r hr s hs hrp hsp dr ds =>
    mid_nbr_unique hT (σ := 1) (Or.inl rfl) hpX (fX 2) (fX 0) (fX 1) (fX 3) (fd 2) (fd 0) (fd 1)
      (fd 3) (fne 0 1 (by decide))
      (by rw [one_mul, anti]; linarith [o 0 2 (by decide)])
      (by rw [one_mul, anti]; linarith [o 1 2 (by decide)])
      (by rw [one_mul]; exact o 2 3 (by decide))
      (by rw [one_mul]; exact o 0 3 (by decide))
      (by rw [one_mul]; exact o 1 3 (by decide)) hr hs hrp hsp dr ds
  have d1 : (nbr K Δ₂ (f 1)).card = 2 := deg2 _ (hfS 1) fun r hr s hs hrp hsp dr ds =>
    mid_nbr_unique hT (σ := -1) (Or.inr rfl) hpX (fX 1) (fX 2) (fX 3) (fX 0) (fd 1) (fd 2) (fd 3)
      (fd 0) (fne 2 3 (by decide))
      (by linarith [o 1 2 (by decide)])
      (by linarith [o 1 3 (by decide)])
      (by rw [anti]; linarith [o 0 1 (by decide)])
      (by rw [anti]; linarith [o 0 2 (by decide)])
      (by rw [anti]; linarith [o 0 3 (by decide)]) hr hs hrp hsp dr ds
  have hsub2 : ({f 1, f 2} : Finset Pt) ⊆ (nbr K Δ₂ p).filter (fun w => (nbr K Δ₂ w).card = 2) := by
    intro x hx
    rcases mem_insert.1 hx with rfl | hx
    · exact mem_filter.2 ⟨hfS 1, d1⟩
    · rw [mem_singleton.1 hx]; exact mem_filter.2 ⟨hfS 2, d2⟩
  have := card_le_card hsub2
  rwa [card_pair (fne 1 2 (by decide))] at this

/-! ## Counting -/

/-- **Double count.**  In a graph with all degrees in `[2, 4]` in which every vertex of degree
`4` has two neighbours of degree `2`, the degree sum is at most `3 |K|`.

Proof: count pairs (degree-4 vertex, adjacent degree-2 vertex) both ways:
`2 #{deg 4} ≤ … ≤ 2 #{deg 2}`; then `2 deg v + 2[deg v = 2] ≤ 6 + 2[deg v = 4]` pointwise. -/
theorem esum_le_three {K : Finset Pt} {d : ℝ}
    (hlo : ∀ v ∈ K, 2 ≤ (nbr K d v).card) (hhi : ∀ v ∈ K, (nbr K d v).card ≤ 4)
    (h4 : ∀ v ∈ K, (nbr K d v).card = 4 →
      2 ≤ ((nbr K d v).filter (fun w => (nbr K d w).card = 2)).card) :
    esum K d ≤ 3 * K.card := by
  classical
  let deg : Pt → ℕ := fun v => (nbr K d v).card
  set I : Pt → Pt → ℕ := fun v w => if dist v w = d ∧ deg v = 4 ∧ deg w = 2 then 1 else 0
    with hI
  have hlow : ∀ v ∈ K, (if deg v = 4 then 2 else 0) ≤ ∑ w ∈ K, I v w := by
    intro v hv
    split_ifs with h
    · have hc : ∑ w ∈ K, I v w =
          (K.filter (fun w => dist v w = d ∧ deg v = 4 ∧ deg w = 2)).card := by
        rw [card_filter]
      rw [hc]
      refine (h4 v hv h).trans (card_le_card fun w hw => ?_)
      obtain ⟨hw1, hw2⟩ := mem_filter.1 hw
      obtain ⟨hwK, hwd⟩ := mem_nbr.1 hw1
      exact mem_filter.2 ⟨hwK, hwd, h, hw2⟩
    · exact Nat.zero_le _
  have hup : ∀ w ∈ K, ∑ v ∈ K, I v w ≤ if deg w = 2 then 2 else 0 := by
    intro w _
    have hc : ∑ v ∈ K, I v w =
        (K.filter (fun v => dist v w = d ∧ deg v = 4 ∧ deg w = 2)).card := by
      rw [card_filter]
    rw [hc]
    split_ifs with h
    · refine (card_le_card fun v hv => ?_).trans (le_of_eq h)
      obtain ⟨hvK, hvd, -⟩ := mem_filter.1 hv
      exact mem_nbr.2 ⟨hvK, by rw [dist_comm]; exact hvd⟩
    · rw [Nat.le_zero, card_eq_zero, filter_eq_empty_iff]
      exact fun v _ hv => h hv.2.2
  have hA : ∑ v ∈ K, (if deg v = 4 then 2 else 0) ≤ ∑ w ∈ K, (if deg w = 2 then 2 else 0) :=
    calc _ ≤ ∑ v ∈ K, ∑ w ∈ K, I v w := sum_le_sum hlow
      _ = ∑ w ∈ K, ∑ v ∈ K, I v w := sum_comm
      _ ≤ _ := sum_le_sum hup
  have hpt : ∀ v ∈ K, 2 * deg v + (if deg v = 2 then 2 else 0) ≤
      6 + (if deg v = 4 then 2 else 0) := by
    intro v hv
    have := hlo v hv
    have := hhi v hv
    simp only [deg]
    split_ifs <;> omega
  have hsum := sum_le_sum hpt
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, sum_const, smul_eq_mul] at hsum
  have he : esum K d = ∑ v ∈ K, deg v := rfl
  omega

/-- **Vesztergombi 1987** (for the two largest distances `Δ > Δ₂`): `2 μ(Δ₂) ≤ 3 |X|`.

Proof: `two_mul_multS`, `esum_eq_esum_L12`, `esum_le_core`, and `esum_le_three` on the core
(degrees from `deg_core_L2`, `deg_core_L1_le_four`, `two_le_mid`). -/
theorem ve87 {X : Finset Pt} {Δ Δ₂ : ℝ} (hT : TwoLargest X Δ Δ₂) :
    2 * multS X Δ₂ ≤ 3 * X.card := by
  set W := L1 X ∪ L2 X with hW
  set K := core W Δ₂ with hK
  have hKW : K ⊆ W := core_subset W Δ₂
  have e1 : 2 * multS X Δ₂ = esum W Δ₂ := by rw [two_mul_multS hT.pos, esum_eq_esum_L12 hT]
  have e2 : esum W Δ₂ ≤ esum K Δ₂ + 2 * (W \ K).card := esum_le_core hT.pos.ne' W
  have hL2 : ∀ v ∈ K, v ∉ L1 X → (nbr K Δ₂ v).card = 2 := fun v hv h1 => by
    have hv2 : v ∈ L2 X := by
      rcases mem_union.1 (hKW hv) with h | h
      · exact absurd h h1
      · exact h
    exact deg_core_L2 hT hv2 hv
  have e3 : esum K Δ₂ ≤ 3 * K.card := by
    refine esum_le_three (minDeg2_core W Δ₂) (fun v hv => ?_) (fun v hv h4 => ?_)
    · by_cases h1 : v ∈ L1 X
      · exact deg_core_L1_le_four hT h1 hv
      · rw [hL2 v hv h1]; norm_num
    · by_cases h1 : v ∈ L1 X
      · exact two_le_mid hT h1 h4
      · rw [hL2 v hv h1] at h4; norm_num at h4
  have e4 : (W \ K).card + K.card = W.card := card_sdiff_add_card_eq_card hKW
  have e5 : W.card ≤ X.card := card_le_card (union_subset (L1_subset X) (L2_subset X))
  omega

/-! ## The statement in the shape of `Erdos132Main.vesztergombi87` -/

section MainShape

open scoped Classical

/-- Diameter (copy of `Erdos132Main.diam`). -/
noncomputable def diam (X : Finset Pt) : ℝ :=
  if h : (distSetS X).Nonempty then (distSetS X).max' h else 0

/-- Second-largest distance (copy of `Erdos132Main.dist2`). -/
noncomputable def dist2 (X : Finset Pt) : ℝ :=
  if h : ((distSetS X).erase (diam X)).Nonempty then ((distSetS X).erase (diam X)).max' h else 0

/-- **[Ve87]** in the shape of `Erdos132Main.vesztergombi87`:
`μ(Δ₂) ≤ (3/2)|Y|` for every finite planar `Y` (with `Δ₂ = 0`, `μ = 0` if `Y` determines fewer
than two distances).

Proof: if `distSetS Y` has `≥ 2` elements, `TwoLargest Y (diam Y) (dist2 Y)` and `ve87`;
otherwise `dist2 Y = 0` and `multS Y 0 = 0`. -/
theorem vesztergombi87 (Y : Finset Pt) : (multS Y (dist2 Y) : ℝ) ≤ 3 / 2 * Y.card := by
  have key : 2 * multS Y (dist2 Y) ≤ 3 * Y.card := by
    by_cases h : 2 ≤ (distSetS Y).card
    · have hne : (distSetS Y).Nonempty := card_pos.1 (by omega)
      have hd : diam Y = (distSetS Y).max' hne := by rw [diam, dite_eq_left hne]
      have hmem : diam Y ∈ distSetS Y := by rw [hd]; exact max'_mem _ _
      have hne' : ((distSetS Y).erase (diam Y)).Nonempty := by
        rw [← card_pos, card_erase_of_mem hmem]; omega
      have hd2 : dist2 Y = ((distSetS Y).erase (diam Y)).max' hne' := by rw [dist2, dite_eq_left hne']
      have h2 : dist2 Y ∈ (distSetS Y).erase (diam Y) := by rw [hd2]; exact max'_mem _ _
      have hT : TwoLargest Y (diam Y) (dist2 Y) :=
        ⟨hmem, mem_of_mem_erase h2,
          lt_of_le_of_ne (by rw [hd]; exact le_max' _ _ (mem_of_mem_erase h2)) (ne_of_mem_erase h2),
          fun d hd' => by rw [hd]; exact le_max' _ _ hd',
          fun d hd' hlt => by rw [hd2]; exact le_max' _ _ (mem_erase.2 ⟨hlt.ne, hd'⟩)⟩
      exact ve87 hT
    · have hemp : ¬ ((distSetS Y).erase (diam Y)).Nonempty := by
        rw [← card_pos]
        have := card_erase_le (s := distSetS Y) (a := diam Y)
        by_cases hne : (distSetS Y).Nonempty
        · have hmem : diam Y ∈ distSetS Y := by rw [diam, dite_eq_left hne]; exact max'_mem _ _
          rw [card_erase_of_mem hmem]; omega
        · rw [not_nonempty_iff_eq_empty.1 hne]; simp
      have h0 : dist2 Y = 0 := by rw [dist2, dite_eq_right hemp]
      have hm : multS Y 0 = 0 := by
        unfold multS
        rw [card_eq_zero, filter_eq_empty_iff]
        intro z hz hz0
        have := pos_of_mem_distSetS (X := Y) (d := pairDist z) (by
          unfold distSetS; exact mem_image_of_mem _ hz)
        linarith
      rw [h0, hm]; omega
  have : (2 * multS Y (dist2 Y) : ℝ) ≤ 3 * Y.card := by exact_mod_cast key
  linarith

end MainShape

/-! ## Axiom check -/

#print axioms ve87
#print axioms vesztergombi87

end Erdos132Ve87
