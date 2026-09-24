import Erdos132.E132Main15Exact

/-!
# Erdős Problem 132, `15/11` theorem — Region III: `e(S) ≤ |S| + |Q| + C`

`angle_R4.md` §3, for `√3/2 − 2β < τ < √3/2 + 3β`.  With `q₂ = #twoRungVerts`:
`#rungs ≤ #rungVerts + q₂`, `#rungVerts ≤ |P₁| + 6` (corner lemma), so it suffices that

  `#T + q₂ ≤ |S| + C`   (`regionIII_key`).

* `τ > √3/2`: the two rung positions are `2s < 1` apart, so `q₂ = 0` (`twoRung_eq_empty`).
* `τ < √3/2`: **slot killing** (Lemma III.1, `slot_kill_one`) with injectivity
  (`slot_kill_inj`) kills `2q₂` distinct T-slots; `card_tEdges_slots` counts slots.
* `τ = √3/2`: breaks (`E132Main15Exact.exact_breaks`) and `card_tEdges_add_breaks_le`, with
  Lemma 7.1 in Region III (`card_mixedT_le_III`).
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-! ## Rung and slot bookkeeping -/

/-- `#rungs ≤ #rungVerts + #twoRungVerts` (each K-end carries `≤ 2` good rungs, and `2` only on
`twoRungVerts`).

TODO: none — proved.
What's missing: (was) as `card_rungs_le`: map a rung to its K-end; fibres have size `≤ 2`, and size
`2` only over `twoRungVerts`; `card_le_card_biUnion`-style sum over fibres.
Acceptance: no `sorry`.
Depends on: `rung_offset`, proof of `card_rungs_le`. Difficulty M. -/
theorem card_rungs_le_add (hX : Normal X) (F : DirField X) :
    (rungs X F).card ≤ (rungVerts X F).card + (twoRungVerts X F).card := by
  classical
  let f : Sym2 Pt → Pt := fun e =>
    if h : ∃ v w, e = s(v, w) ∧ IsRung F v w then h.choose else 0
  have hf : ∀ e, (h : ∃ v w, e = s(v, w) ∧ IsRung F v w) →
      ∃ w, e = s(f e, w) ∧ IsRung F (f e) w := by
    intro e h
    have : f e = h.choose := dif_pos h
    rw [this]; exact h.choose_spec
  have hmap : ∀ e ∈ rungs X F, f e ∈ rungVerts X F := by
    intro e he
    obtain ⟨w, -, hr⟩ := hf e (mem_filter.1 he).2
    exact mem_filter.2 ⟨mem_sdiff.2 ⟨hr.1, hr.2.1⟩, w, hr⟩
  rw [card_eq_sum_card_fiberwise hmap]
  have hfib : ∀ v ∈ rungVerts X F, ((rungs X F).filter (fun e => f e = v)).card ≤
      1 + if v ∈ twoRungVerts X F then 1 else 0 := by
    intro v hv
    split_ifs with h2
    · let o : ℝ → Pt := fun σ => v + ((-tau X) • F.u v + (σ * sOff X) • perp (F.u v))
      have hsub : (rungs X F).filter (fun e => f e = v) ⊆ {s(v, o 1), s(v, o (-1))} := by
        intro e he
        obtain ⟨he, hfe⟩ := mem_filter.1 he
        obtain ⟨w, hew, hr⟩ := hf e (mem_filter.1 he).2
        rw [hfe] at hew hr
        obtain ⟨σ, hσ, ho⟩ := rung_offset F hr
        have hw : w = o σ := by simp only [o]; rw [← ho]; abel
        rw [hew, hw]
        rcases hσ with rfl | rfl <;> simp
      exact (card_le_card hsub).trans card_le_two
    · refine (card_le_one.2 fun e he e' he' => ?_).trans (by omega)
      by_contra hne
      apply h2
      obtain ⟨he, hfe⟩ := mem_filter.1 he
      obtain ⟨he', hfe'⟩ := mem_filter.1 he'
      obtain ⟨w, hew, hr⟩ := hf e (mem_filter.1 he).2
      obtain ⟨w', hew', hr'⟩ := hf e' (mem_filter.1 he').2
      rw [hfe] at hew hr
      rw [hfe'] at hew' hr'
      refine mem_filter.2 ⟨hv, w, w', ?_, hr, hr', hew ▸ he, hew' ▸ he'⟩
      rintro rfl
      exact hne (hew.trans hew'.symm)
  refine (sum_le_sum hfib).trans ?_
  rw [sum_add_distrib, sum_const, smul_eq_mul, mul_one, sum_boole]
  have : ((rungVerts X F).filter (fun v => v ∈ twoRungVerts X F)).card ≤
      (twoRungVerts X F).card := card_le_card fun v hv => (mem_filter.1 hv).2
  simp only [Nat.cast_id] at this ⊢
  omega

/-- For `τ > √3/2` no vertex carries two rungs: the positions `v + o_±` are `2s < 1` apart.

TODO: none — proved.
What's missing: (was) `rung_offset` for both rungs; `σ ≠ σ'` (else equal); `|z − z′| = 2 sOff < 1`
(`sOff² = 1 − τ² < 1/4`); `eq_of_dist_lt_one`.
Acceptance: no `sorry`.
Depends on: `rung_offset`, `eq_of_dist_lt_one`, `norm_perp`. Difficulty S–M. -/
theorem twoRung_eq_empty (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 < tau X)
    (hτ₂ : tau X < √3 / 2 + 3 * beta) : twoRungVerts X F = ∅ := by
  refine eq_empty_of_forall_notMem fun v hv => ?_
  obtain ⟨z, z', hne, h₁, h₂, -, -⟩ := (mem_filter.1 hv).2
  obtain ⟨σ₁, hσ₁, e₁⟩ := rung_offset F h₁
  obtain ⟨σ₂, hσ₂, e₂⟩ := rung_offset F h₂
  have hu := F.norm_u h₁.1
  have hs0 : 0 ≤ sOff X := Real.sqrt_nonneg _
  have hs : 2 * sOff X < 1 := by
    have h3 : (1.732 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
    have : sOff X < 1 / 2 := by
      have e3 : (√3 / 2) ^ 2 = 3 / 4 := by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
      have : (√3 / 2) ^ 2 < tau X ^ 2 := pow_lt_pow_left₀ hτ₁ (by positivity) (by norm_num)
      unfold sOff; rw [Real.sqrt_lt' (by norm_num)]; nlinarith
    linarith
  refine hne (eq_of_dist_lt_one hX.minDist_eq h₁.memX.2 h₂.memX.2 ?_)
  have e : z - z' = (z - v) - (z' - v) := by abel
  rw [dist_eq_norm, e, e₁, e₂]
  refine (norm_offset_sub hu hu hs0 hσ₁ hσ₂).trans_lt ?_
  simpa using hs

/-- **Slot counting**: each T-edge uses two slots (one at each end, by the sign of `det2`), each
slot is used at most once (T1); so `2#T + #(free slots) ≤ 2|S|`.

TODO: none — proved.
What's missing: (was) injection `tEdges × {end} → S × {±1}` (via `tstep_flip`: the two ends see each
other on opposite sides, and `tnbr_unique`), disjoint from `Kill`; slots live in
`S ×ˢ {1, -1}` of size `2|S|`.
Acceptance: no `sorry`.
Depends on: `tnbr_unique`, `tstep_flip`, definitions. Difficulty M. -/
theorem card_tEdges_slots (hX : Normal X) (F : DirField X) (Kill : Finset (Pt × ℝ))
    (hK : ∀ x ∈ Kill, x.1 ∈ Sset X ∧ (x.2 = 1 ∨ x.2 = -1) ∧ SlotFree F x.1 x.2) :
    2 * (tEdges X F).card + Kill.card ≤ 2 * (Sset X).card := by
  classical
  set S := Sset X
  set T := tEdges X F
  have hE : ∀ z ∈ T, ¬ z.IsDiag ∧ ∀ p ∈ z, p ∈ S := fun z hz =>
    mem_edges (mem_filter.1 (mem_filter.1 hz).1).1
  have tdata : ∀ {p q : Pt}, s(p, q) ∈ T → dist p q = 1 ∧ IsTEdge F p q := by
    intro p q h
    obtain ⟨hg, hTall⟩ := mem_filter.1 h
    obtain ⟨hee, -⟩ := mem_filter.1 hg
    have hd : pairDist s(p, q) = minDist X := (mem_filter.1 hee).2
    exact ⟨by rw [← hX.minDist_eq, ← hd]; rfl, hTall p q rfl⟩
  have h2 : ∀ z ∈ T, (S.filter (fun p => p ∈ z)).card = 2 := by
    intro z hz
    induction z using Sym2.ind with
    | h a b =>
      obtain ⟨hd, hV⟩ := hE _ hz
      have hab : a ≠ b := by simpa using hd
      have : S.filter (fun p => p ∈ s(a, b)) = {a, b} := by
        ext x
        simp only [mem_filter, Sym2.mem_iff, mem_insert, mem_singleton]
        constructor
        · exact fun h => h.2
        · rintro (rfl | rfl)
          · exact ⟨hV _ (Sym2.mem_mk_left _ _), Or.inl rfl⟩
          · exact ⟨hV _ (Sym2.mem_mk_right _ _), Or.inr rfl⟩
      rw [this, card_pair hab]
  have hdc : ∑ z ∈ T, (S.filter (fun p => p ∈ z)).card =
      ∑ p ∈ S, (T.filter (fun z => p ∈ z)).card := by
    simp only [card_filter]; exact sum_comm
  have hT2 : 2 * T.card = ∑ p ∈ S, (T.filter (fun z => p ∈ z)).card := by
    rw [← hdc, sum_congr rfl h2, sum_const, smul_eq_mul, mul_comm]
  have hK2 : Kill.card = ∑ p ∈ S, (Kill.filter (fun x => x.1 = p)).card :=
    card_eq_sum_card_fiberwise (fun x hx => (hK x hx).1)
  have hloc : ∀ p ∈ S, (T.filter (fun z => p ∈ z)).card +
      (Kill.filter (fun x => x.1 = p)).card ≤ 2 := by
    intro p hp
    let B : ℝ → Finset Pt := fun σ =>
      S.filter (fun q => s(p, q) ∈ T ∧ 0 < σ * det2 (F.u p) (q - p))
    let k : ℝ → ℕ := fun σ => if (p, σ) ∈ Kill then 1 else 0
    have hB : ∀ σ, (B σ).card + k σ ≤ 1 := by
      intro σ
      by_cases hk : (p, σ) ∈ Kill
      · have hfree := (hK _ hk).2.2
        have : B σ = ∅ := by
          refine eq_empty_of_forall_notMem fun q hq => ?_
          obtain ⟨-, hqT, hs⟩ := mem_filter.1 hq
          exact hfree q hqT hs
        simp [k, hk, this]
      · simp only [k, hk, if_false, add_zero]
        refine card_le_one.2 fun a ha b hb => ?_
        obtain ⟨haS, haT, has⟩ := mem_filter.1 ha
        obtain ⟨hbS, hbT, hbs⟩ := mem_filter.1 hb
        obtain ⟨da, ta⟩ := tdata haT
        obtain ⟨db, tb⟩ := tdata hbT
        exact tnbr_unique hX hp haS hbS da db ta tb has hbs
    have hsub : T.filter (fun z => p ∈ z) ⊆ (B 1 ∪ B (-1)).image (fun q => s(p, q)) := by
      intro z hz
      obtain ⟨hzT, hpz⟩ := mem_filter.1 hz
      obtain ⟨q, rfl⟩ := Sym2.mem_iff_exists.1 hpz
      obtain ⟨hd, hTe⟩ := tdata hzT
      have hq : q ∈ S := (hE _ hzT).2 q (Sym2.mem_mk_right _ _)
      rw [mem_image]
      refine ⟨q, ?_, rfl⟩
      have hl := lagrange (q - p) (F.u p)
      rw [F.norm_u' hp, ← dist_eq_norm, dist_comm q p, hd] at hl
      have ha := hTe.2.1
      have hβ : beta = 1 / 100 := rfl
      rw [hβ] at ha
      rcases lt_or_gt_of_ne (show det2 (F.u p) (q - p) ≠ 0 by
        intro h0; rw [h0] at hl; nlinarith [hTe.1]) with hb | hb
      · exact mem_union_right _ (mem_filter.2 ⟨hq, hzT, by linarith⟩)
      · exact mem_union_left _ (mem_filter.2 ⟨hq, hzT, by linarith⟩)
    have hKp : (Kill.filter (fun x => x.1 = p)).card ≤ k 1 + k (-1) := by
      have : Kill.filter (fun x => x.1 = p) ⊆
          (if (p, (1 : ℝ)) ∈ Kill then {(p, 1)} else ∅) ∪
            (if (p, (-1 : ℝ)) ∈ Kill then {(p, -1)} else ∅) := by
        intro x hx
        obtain ⟨hxK, hx1⟩ := mem_filter.1 hx
        obtain ⟨-, hσ, -⟩ := hK x hxK
        obtain ⟨a, σ⟩ := x
        simp only at hx1 hσ
        subst hx1
        rcases hσ with rfl | rfl
        · apply mem_union_left; rw [if_pos hxK]; exact mem_singleton_self _
        · apply mem_union_right; rw [if_pos hxK]; exact mem_singleton_self _
      refine (card_le_card this).trans ((card_union_le _ _).trans ?_)
      simp only [k]; split_ifs <;> simp
    have c1 := hB 1
    have c2 := hB (-1)
    have := (card_le_card hsub).trans (card_image_le.trans (card_union_le _ _))
    omega
  have := sum_le_sum hloc
  rw [sum_add_distrib, sum_const, smul_eq_mul, ← hT2, ← hK2] at this
  omega

/-- `det(a, c b) = c det(a, b)`. -/
private theorem det2_smul_right' (a b : Pt) (c : ℝ) : det2 a (c • b) = c * det2 a b := by
  simp only [det2_pt, PiLp.smul_apply, smul_eq_mul]; ring

/-- `det(a, b^⊥) = a·b`. -/
private theorem det2_perp_right' (a b : Pt) : det2 a (perp b) = inner ℝ a b := by
  rw [det2_pt, inner_pt]; simp

/-- Common data of the two rungs of a two-rung vertex at `τ < √3/2`: `z − z′ = 2sκ u_v^⊥`,
`κ = ±1`, and `1/2 < s < 0.6`. -/
private theorem two_rung_diff (F : DirField X) (hτ₁ : √3 / 2 - 2 * beta < tau X)
    (hτ₂ : tau X < √3 / 2) {v z z' : Pt} (hr : IsRung F v z) (hr' : IsRung F v z')
    (hne : z ≠ z') :
    1 / 2 < sOff X ∧ sOff X < 0.6 ∧ ∃ κ : ℝ, (κ = 1 ∨ κ = -1) ∧
      z - z' = (2 * sOff X * κ) • perp (F.u v) := by
  obtain ⟨σ₁, hσ₁, e₁⟩ := rung_offset F hr
  obtain ⟨σ₂, hσ₂, e₂⟩ := rung_offset F hr'
  have hb : beta = 1 / 100 := rfl
  have h3 : (1.732 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hτpos : 0.84 < tau X := by rw [hb] at hτ₁; linarith
  have hτ2 : tau X ^ 2 < 3 / 4 := by
    have e3 : (√3 / 2) ^ 2 = 3 / 4 := by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
    have := pow_lt_pow_left₀ hτ₂ (by linarith) (two_ne_zero)
    linarith
  have hs2 : sOff X ^ 2 = 1 - tau X ^ 2 := Real.sq_sqrt (by nlinarith)
  have hs0 : 0 ≤ sOff X := Real.sqrt_nonneg _
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  have hne12 : σ₁ ≠ σ₂ := by
    rintro rfl; apply hne
    have : z - v = z' - v := by rw [e₁, e₂]
    exact sub_left_injective this
  refine ⟨(σ₁ - σ₂) / 2, ?_, ?_⟩
  · rcases hσ₁ with rfl | rfl <;> rcases hσ₂ with rfl | rfl <;> (try norm_num at hne12) <;> norm_num
  · have : z - z' = (z - v) - (z' - v) := by abel
    rw [this, e₁, e₂, show 2 * sOff X * ((σ₁ - σ₂) / 2) = σ₁ * sOff X - σ₂ * sOff X by ring,
      sub_smul]
    abel

/-- **Lemma III.1** (`τ < √3/2`, `2s > 1`): if `v` has rungs `z ≠ z′` (the one to `z′` good),
then `z′` has no T-neighbour on the side of `z`.
(`o₊ − o₋ = 2s·u^⊥`; a T-neighbour `y` of `z′` on that side has `∠(y − z′, z − z′) ≤ β + arcsin β`,
so `|y − z|² ≤ (2s − 1)² + 4s(1 − cos γ) < 1`, and `y ≠ z` since `|zz′| = 2s ≠ 1`.)

TODO: none — proved (in the frame of `u_{z′}`: `κ det(u_v, q − z′) > 0.98`, so
`|q − z|² = 1 − 4sκ det + 4s² < 1`).
What's missing: (was) the vector computation above with `rung_offset`, `RungM.ang`/good rung,
`IsTEdge` bounds, `eq_of_dist_lt_one`; float worst case `|y − z| ≤ 0.069`.
Acceptance: no `sorry`.
Depends on: `rung_offset`, `norm_offset_sub`, `same_side_close`, `eq_of_dist_lt_one`.
Difficulty M–L. -/
theorem slot_kill_one (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 - 2 * beta < tau X)
    (hτ₂ : tau X < √3 / 2) {v z z' : Pt} (hr : IsRung F v z) (hr' : IsRung F v z')
    (hg' : s(v, z') ∈ rungs X F) (hne : z ≠ z') {σ : ℝ}
    (hσ : 0 < σ * det2 (F.u z') (z - z')) : SlotFree F z' σ := by
  intro q hq hqs
  obtain ⟨hgq, hTall⟩ := mem_filter.1 hq
  obtain ⟨hee, -⟩ := mem_filter.1 hgq
  have hd1 : dist z' q = 1 := by
    have hd : pairDist s(z', q) = minDist X := (mem_filter.1 hee).2
    rw [← hX.minDist_eq, ← hd]; rfl
  have hT := hTall z' q rfl
  have hqS : q ∈ Sset X := (mem_edges hee).2 q (Sym2.mem_mk_right _ _)
  have hgood : ang (F.u v) (F.u z') ≤ beta := (mem_filter.1 (mem_filter.1 hg').1).2 v z' rfl
  obtain ⟨hs1, hs2, κ, hκ, hd⟩ := two_rung_diff F hτ₁ hτ₂ hr hr' hne
  set u := F.u v
  set u' := F.u z'
  set s := sOff X
  have hu : ‖u‖ = 1 := F.norm_u hr.1
  have hu' : ‖u'‖ = 1 := F.norm_u hr'.2.2.1
  have huu : ‖u - u'‖ ≤ beta := (norm_sub_le_angR hu hu').trans hgood
  have hb : beta = 1 / 100 := rfl
  rw [hb] at huu
  have hκ2 : κ * κ = 1 := by rcases hκ with rfl | rfl <;> norm_num
  set y := q - z'
  have hy : ‖y‖ = 1 := by rw [← dist_eq_norm, dist_comm, hd1]
  have ha0 : 0 < inner ℝ y u' := hT.1
  have ha1 : inner ℝ y u' < 1 / 100 := hT.2.1
  -- `u·u' > 0`
  have huu' : 0 < inner ℝ u' u := by
    have e := @norm_sub_sq_real _ _ _ u u'
    rw [hu, hu', real_inner_comm] at e
    nlinarith [norm_nonneg (u - u')]
  -- the sign of the side: `σκ > 0`
  have hσκ : 0 < σ * κ := by
    rw [hd, det2_smul_right', det2_perp_right'] at hσ
    by_contra h; push Not at h
    have : σ * (2 * s * κ * inner ℝ u' u) = (σ * κ) * (2 * s * inner ℝ u' u) := by ring
    have h2 : 0 ≤ 2 * s * inner ℝ u' u := by positivity
    nlinarith [mul_nonpos_of_nonpos_of_nonneg h h2]
  have hκD : 0 < κ * det2 u' y := by
    by_contra h; push Not at h
    have : σ * κ * (σ * det2 u' y) = σ ^ 2 * (κ * det2 u' y) := by ring
    nlinarith [mul_pos hσκ hqs, mul_nonpos_of_nonneg_of_nonpos (sq_nonneg σ) h]
  have hD2 := inner_sq_add_det_sq (e := y) hu'
  rw [hy] at hD2
  have hκD' : 0.999 < κ * det2 u' y := by
    have : (κ * det2 u' y) ^ 2 = det2 u' y ^ 2 := by
      rw [mul_pow, show κ ^ 2 = κ * κ by ring, hκ2, one_mul]
    nlinarith
  have hW := abs_det2_leR (u - u') y
  rw [hy, mul_one, det2_sub_left] at hW
  have hκE : 0.98 < κ * det2 u y := by
    rw [abs_le] at hW
    rcases hκ with rfl | rfl <;> nlinarith
  -- `|q − z| < 1`
  have hqz : q - z = y - (z - z') := by simp only [y]; abel
  have hlt : dist q z < 1 := by
    rw [dist_eq_norm, hqz]
    have e := @norm_sub_sq_real _ _ _ y (z - z')
    have hin : inner ℝ y (z - z') = 2 * s * (κ * det2 u y) := by
      rw [hd, inner_smul_right, det2_eq_inner_perpR, real_inner_comm]; ring
    have hn : ‖z - z'‖ ^ 2 = 4 * s ^ 2 := by
      rw [hd, norm_smul, norm_perp, hu, mul_one, Real.norm_eq_abs, sq_abs]
      linear_combination (4 * s ^ 2) * hκ2
    rw [hin, hn, hy] at e
    have : ‖y - (z - z')‖ ^ 2 < 1 := by nlinarith
    nlinarith [norm_nonneg (y - (z - z'))]
  have hqz' := eq_of_dist_lt_one hX.minDist_eq (Sset_sub hqS) hr.memX.2 hlt
  rw [hqz', dist_eq_norm'] at hd1
  have : ‖z - z'‖ = 2 * s := by
    rw [hd, norm_smul, norm_perp, hu, mul_one, Real.norm_eq_abs, abs_mul, abs_of_pos
      (by linarith : (0 : ℝ) < 2 * s)]
    rcases hκ with rfl | rfl <;> norm_num
  linarith

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

/-- The side of `z − z′ = 2sκ u^⊥` seen from `u′ ≈ u` has the sign of `κ`. -/
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

/-- **Injectivity of killed slots** (`τ < √3/2`): two two-rung vertices `v, v̄` sharing a rung end
`z′` and killing the same slot of `z′` coincide.  (`|z̄ − z| ≤ 2s·2β < 1` gives `z̄ = z`; then `v̄`
is the mirror image of `v` in `zz′`, contradicting Lemma 3.2(a) at `z′`.)

TODO: none — proved (no mirror argument needed: the sign `σ` fixes `κ = κ′`, so `z′ − v` and
`z′ − v′` are the same offset in the frames `u_v, u_{v′}` with `|u_v − u_{v′}| ≤ 2β`, whence
`|v − v′| ≤ 2β(τ + s) < 1`).
What's missing: (was) `rung_offset` for the four rungs, goodness (`∠(u_v, u_{z′}), ∠(u_v̄, u_{z′}) ≤ β`),
`eq_of_dist_lt_one`, then the mirror argument with `exact_identity_a`.
Acceptance: no `sorry`.
Depends on: `rung_offset`, `exact_identity_a`, `eq_of_dist_lt_one`. Difficulty M–L. -/
theorem slot_kill_inj (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 - 2 * beta < tau X)
    (hτ₂ : tau X < √3 / 2) {v v' z z' z'' : Pt} (hr : IsRung F v z) (hr' : IsRung F v z')
    (hs' : IsRung F v' z') (hs'' : IsRung F v' z'') (g : s(v, z) ∈ rungs X F)
    (g' : s(v, z') ∈ rungs X F) (k' : s(v', z') ∈ rungs X F) (k'' : s(v', z'') ∈ rungs X F)
    (hne : z ≠ z') (hne' : z'' ≠ z') {σ : ℝ} (hσ : 0 < σ * det2 (F.u z') (z - z'))
    (hσ' : 0 < σ * det2 (F.u z') (z'' - z')) : v = v' := by
  have hgood' : ang (F.u v) (F.u z') ≤ beta := (mem_filter.1 (mem_filter.1 g').1).2 v z' rfl
  have hgood'' : ang (F.u v') (F.u z') ≤ beta := (mem_filter.1 (mem_filter.1 k').1).2 v' z' rfl
  obtain ⟨hs1, hs2, -⟩ := two_rung_diff F hτ₁ hτ₂ hr hr' hne
  obtain ⟨κ, hκ, hd, ho⟩ := rung_pair_kappa F hr hr' hne
  obtain ⟨κ', hκ', hd', ho'⟩ := rung_pair_kappa F hs'' hs' hne'
  set s := sOff X
  have hu := F.norm_u hr.1
  have hu' := F.norm_u hs'.1
  have huz := F.norm_u hr'.2.2.1
  have hb : beta = 1 / 100 := rfl
  have h1 : ‖F.u v - F.u z'‖ ≤ 1 / 100 := hb ▸ (norm_sub_le_angR hu huz).trans hgood'
  have h2 : ‖F.u v' - F.u z'‖ ≤ 1 / 100 := hb ▸ (norm_sub_le_angR hu' huz).trans hgood''
  have hs0 : 0 < s := by linarith
  have e1 := side_sign hu huz h1 hs0 (by rw [← hd]; exact hσ)
  have e2 := side_sign hu' huz h2 hs0 (by rw [← hd']; exact hσ')
  have hκκ : κ = κ' := by
    rcases hκ with rfl | rfl <;> rcases hκ' with rfl | rfl <;> first | rfl | nlinarith
  subst hκκ
  refine eq_of_dist_lt_one hX.minDist_eq hr.memX.1 hs'.memX.1 ?_
  have e : v - v' = (z' - v') - (z' - v) := by abel
  rw [dist_eq_norm, e, ho, ho']
  have : ((-tau X) • F.u v' + (-κ * s) • perp (F.u v')) -
      ((-tau X) • F.u v + (-κ * s) • perp (F.u v)) =
      (-tau X) • (F.u v' - F.u v) + (-κ * s) • perp (F.u v' - F.u v) := by
    rw [perp_sub, smul_sub, smul_sub]; abel
  rw [this]
  have hw : ‖F.u v' - F.u v‖ ≤ 2 / 100 := by
    have := norm_sub_le (F.u v' - F.u z') (F.u v - F.u z')
    rw [sub_sub_sub_cancel_right] at this
    linarith
  refine (norm_add_le _ _).trans_lt ?_
  have hks : |(-κ * s)| = s := by
    rcases hκ with rfl | rfl <;> simp [abs_of_pos hs0]
  have h3 : (1.732 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hτ0 : 0 < tau X := by rw [hb] at hτ₁; linarith
  rw [norm_smul, norm_smul, norm_perp, Real.norm_eq_abs, Real.norm_eq_abs, hks, abs_neg,
    abs_of_pos hτ0]
  have : tau X < 1 := by
    have : √3 < 1.7321 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    linarith
  nlinarith [norm_nonneg (F.u v' - F.u v)]

/-- **Slot bound for `τ < √3/2`**: `#T + q₂ ≤ |S|`.

TODO: none — proved.
What's missing: (was) `Kill := ⋃_{v ∈ twoRungVerts} {(z′, σ_v), (z, σ′_v)}` (the two killed slots of
`v`, chosen via `Classical.choose`); `slot_kill_one` gives `SlotFree`; `slot_kill_inj` and
`z ≠ z′` give `#Kill = 2q₂`; conclude with `card_tEdges_slots`.
Acceptance: no `sorry` (inherits).
Depends on: `card_tEdges_slots`, `slot_kill_one`, `slot_kill_inj`. Difficulty M. -/
theorem card_tEdges_add_twoRung_lt (hX : Normal X) (F : DirField X)
    (hτ₁ : √3 / 2 - 2 * beta < tau X) (hτ₂ : tau X < √3 / 2) :
    (tEdges X F).card + (twoRungVerts X F).card ≤ (Sset X).card := by
  classical
  set V := twoRungVerts X F
  have hpick : ∀ v ∈ V, ∃ zz : Pt × Pt, zz.1 ≠ zz.2 ∧ IsRung F v zz.1 ∧ IsRung F v zz.2 ∧
      s(v, zz.1) ∈ rungs X F ∧ s(v, zz.2) ∈ rungs X F := by
    intro v hv
    obtain ⟨z, z', hne, h1, h2, g1, g2⟩ := (mem_filter.1 hv).2
    exact ⟨(z, z'), hne, h1, h2, g1, g2⟩
  let P : Pt → Pt × Pt := fun v => if h : v ∈ V then (hpick v h).choose else (0, 0)
  have hP : ∀ v ∈ V, (P v).1 ≠ (P v).2 ∧ IsRung F v (P v).1 ∧ IsRung F v (P v).2 ∧
      s(v, (P v).1) ∈ rungs X F ∧ s(v, (P v).2) ∈ rungs X F := by
    intro v hv
    have : P v = (hpick v hv).choose := dif_pos hv
    rw [this]; exact (hpick v hv).choose_spec
  let sg : ℝ → ℝ := fun x => if 0 < x then 1 else -1
  -- the slot of `b` on the side of `a`
  have hsg : ∀ {v a b : Pt}, IsRung F v a → IsRung F v b → s(v, b) ∈ rungs X F → a ≠ b →
      0 < sg (det2 (F.u b) (a - b)) * det2 (F.u b) (a - b) ∧
        (sg (det2 (F.u b) (a - b)) = 1 ∨ sg (det2 (F.u b) (a - b)) = -1) := by
    intro v a b ha hb gb hab
    obtain ⟨hs1, -, -⟩ := two_rung_diff F hτ₁ hτ₂ ha hb hab
    obtain ⟨κ, hκ, hd, -⟩ := rung_pair_kappa F ha hb hab
    have hgood : ang (F.u v) (F.u b) ≤ beta := (mem_filter.1 (mem_filter.1 gb).1).2 v b rfl
    have hu := F.norm_u ha.1
    have hub := F.norm_u hb.2.2.1
    have huu : ‖F.u v - F.u b‖ ≤ beta := (norm_sub_le_angR hu hub).trans hgood
    have hb' : beta = 1 / 100 := rfl
    rw [hb'] at huu
    have hin : 0 < inner ℝ (F.u b) (F.u v) := by
      have e := @norm_sub_sq_real _ _ _ (F.u v) (F.u b)
      rw [hu, hub, real_inner_comm] at e
      nlinarith [norm_nonneg (F.u v - F.u b)]
    have hne0 : det2 (F.u b) (a - b) ≠ 0 := by
      rw [hd, det2_smul_right', det2_perp_right']
      have : 0 < sOff X := by linarith
      rcases hκ with rfl | rfl
      · have := mul_pos (mul_pos (by norm_num : (0:ℝ) < 2) this) hin; nlinarith
      · have := mul_pos (mul_pos (by norm_num : (0:ℝ) < 2) this) hin; nlinarith
    simp only [sg]
    split_ifs with h
    · exact ⟨by linarith, Or.inl rfl⟩
    · exact ⟨by have := lt_of_le_of_ne (not_lt.1 h) hne0; linarith, Or.inr rfl⟩
  let Sl : Pt → Finset (Pt × ℝ) := fun v =>
    {((P v).2, sg (det2 (F.u (P v).2) ((P v).1 - (P v).2))),
      ((P v).1, sg (det2 (F.u (P v).1) ((P v).2 - (P v).1)))}
  have hmem : ∀ v ∈ V, ∀ x ∈ Sl v, ∃ a, IsRung F v a ∧ IsRung F v x.1 ∧ s(v, a) ∈ rungs X F ∧
      s(v, x.1) ∈ rungs X F ∧ a ≠ x.1 ∧ 0 < x.2 * det2 (F.u x.1) (a - x.1) ∧
      (x.2 = 1 ∨ x.2 = -1) := by
    intro v hv x hx
    obtain ⟨hne, h1, h2, g1, g2⟩ := hP v hv
    rcases mem_insert.1 hx with rfl | hx
    · exact ⟨_, h1, h2, g1, g2, hne, hsg h1 h2 g2 hne⟩
    · rw [mem_singleton] at hx; subst hx
      exact ⟨_, h2, h1, g2, g1, hne.symm, hsg h2 h1 g1 hne.symm⟩
  set Kill := V.biUnion Sl
  have hK : ∀ x ∈ Kill, x.1 ∈ Sset X ∧ (x.2 = 1 ∨ x.2 = -1) ∧ SlotFree F x.1 x.2 := by
    intro x hx
    obtain ⟨v, hv, hx⟩ := mem_biUnion.1 hx
    obtain ⟨a, ha, hb, ga, gb, hab, hσ, hσ1⟩ := hmem v hv x hx
    exact ⟨hb.2.2.1, hσ1, slot_kill_one hX F hτ₁ hτ₂ ha hb gb hab hσ⟩
  have hcard : Kill.card = 2 * V.card := by
    rw [card_biUnion]
    · rw [sum_congr rfl (g := fun _ => 2), sum_const, smul_eq_mul, mul_comm]
      intro v hv
      refine card_pair fun e => (hP v hv).1 ?_
      exact (congrArg Prod.fst e).symm
    · intro v hv v' hv' hvv'
      refine Finset.disjoint_left.2 fun x hx hx' => hvv' ?_
      obtain ⟨a, ha, hb, ga, gb, hab, hσ, -⟩ := hmem v hv x hx
      obtain ⟨a', ha', hb', ga', gb', hab', hσ', -⟩ := hmem v' hv' x hx'
      exact slot_kill_inj hX F hτ₁ hτ₂ ha hb hb' ha' ga gb gb' ga' hab hab' hσ hσ'
  have := card_tEdges_slots hX F Kill hK
  omega

/-- **Breaks**: `#T + #breaks ≤ |S| + #mixed` (a pure T-edge is charged to its left end, which
has a pure right T-neighbour; each vertex has `≤ 1` right T-neighbour).

TODO: none — proved.
What's missing: (was) `tEdges = pure ⊔ mixedT`; the left-end map on pure T-edges is injective into
`S ∖ breaks` (`rowR_fun`; orientation from `tstep_flip`/`T2`).
Acceptance: no `sorry`.
Depends on: `rowR_fun`, `tstep_flip`, `T2`, `mixedT_data`. Difficulty M. -/
theorem card_tEdges_add_breaks_le (hX : Normal X) (F : DirField X) :
    (tEdges X F).card + (breaks X F).card ≤ (Sset X).card + (mixedT X F).card := by
  classical
  have tdata : ∀ {p q : Pt}, s(p, q) ∈ tEdges X F → dist p q = 1 ∧ IsTEdge F p q := by
    intro p q h
    obtain ⟨hg, hTall⟩ := mem_filter.1 h
    obtain ⟨hee, -⟩ := mem_filter.1 hg
    have hd : pairDist s(p, q) = minDist X := (mem_filter.1 hee).2
    exact ⟨by rw [← hX.minDist_eq, ← hd]; rfl, hTall p q rfl⟩
  have hleft : ∀ z ∈ tEdges X F \ mixedT X F, ∃ a b, z = s(a, b) ∧ RowR F a b := by
    intro z hz
    obtain ⟨hzT, hzM⟩ := mem_sdiff.1 hz
    induction z using Sym2.ind with
    | h p q =>
    obtain ⟨hd, hTe⟩ := tdata hzT
    have hS := (mem_edges (mem_filter.1 (mem_filter.1 hzT).1).1).2
    have hp := hS p (Sym2.mem_mk_left _ _)
    have hq := hS q (Sym2.mem_mk_right _ _)
    have hg : ang (F.u p) (F.u q) ≤ beta := (mem_filter.1 (mem_filter.1 hzT).1).2 p q rfl
    have hDD : (p ∈ Dset X ↔ q ∈ Dset X) := by
      constructor
      · intro hpD; by_contra hqD
        exact hzM (mem_filter.2 ⟨hzT, q, p, Sym2.eq_swap, hqD, hpD⟩)
      · intro hqD; by_contra hpD
        exact hzM (mem_filter.2 ⟨hzT, p, q, rfl, hpD, hqD⟩)
    have hl := lagrange (q - p) (F.u p)
    rw [F.norm_u' hp, ← dist_eq_norm, dist_comm q p, hd] at hl
    have ha := hTe.2.1
    have hβ : beta = 1 / 100 := rfl
    rw [hβ] at ha
    rcases lt_or_gt_of_ne (show det2 (F.u p) (q - p) ≠ 0 by
      intro h0; rw [h0] at hl; nlinarith [hTe.1]) with hb | hb
    · exact ⟨p, q, rfl, ⟨hp, hq, hd, hg, hTe, by linarith⟩, hDD⟩
    · have := tstep_flip hp hq hd hg hTe.1 hTe.2.1
      have hb' : det2 (F.u q) (p - q) < 0 := by nlinarith
      exact ⟨q, p, Sym2.eq_swap, ⟨hq, hp, by rw [dist_comm]; exact hd,
        by rw [ang, InnerProductGeometry.angle_comm]; exact hg, hTe.symm, by linarith⟩, hDD.symm⟩
  let g : Sym2 Pt → Pt := fun z =>
    if h : ∃ a b, z = s(a, b) ∧ RowR F a b then h.choose else 0
  have hg : ∀ z, (h : ∃ a b, z = s(a, b) ∧ RowR F a b) → ∃ b, z = s(g z, b) ∧ RowR F (g z) b := by
    intro z h
    have : g z = h.choose := dif_pos h
    rw [this]; exact h.choose_spec
  have hinj : Set.InjOn g ↑(tEdges X F \ mixedT X F) := by
    intro z hz z' hz' e
    obtain ⟨b, hzb, hr⟩ := hg z (hleft z hz)
    obtain ⟨b', hzb', hr'⟩ := hg z' (hleft z' hz')
    rw [e] at hzb hr
    rw [rowR_fun hX hr hr'] at hzb
    exact hzb.trans hzb'.symm
  have hmaps : ∀ z ∈ tEdges X F \ mixedT X F, g z ∈ Sset X \ breaks X F := by
    intro z hz
    obtain ⟨b, -, hr⟩ := hg z (hleft z hz)
    exact mem_sdiff.2 ⟨hr.1.1, fun hb => (mem_filter.1 hb).2 ⟨b, hr⟩⟩
  have h1 := card_le_card_of_injOn g hmaps hinj
  have h2 := card_sdiff_add_card_eq_card (show breaks X F ⊆ Sset X from filter_subset _ _)
  have h3 : (tEdges X F).card ≤ (tEdges X F \ mixedT X F).card + (mixedT X F).card :=
    card_le_card_sdiff_add_card
  omega

/-- Lemma 7.1 without the Region II hypothesis (the proof of `lemma71` never uses
`√3/2 + 3β ≤ τ`); copied verbatim from `E132MainRegions.lemma71`. -/
private theorem lemma71_III (hX : Normal X) (F : DirField X) {v z : Pt}
    (hv : v ∈ Sset X) (hvD : v ∉ Dset X) (hz : z ∈ Sset X) (hzD : z ∈ Dset X)
    (hvz : dist v z = 1) (hT : IsTEdge F v z) :
    ∃ Γ : Set Pt, Γ ⊆ frontier (KBall X) ∧ (∀ x ∈ Γ, dist v x ≤ 2) ∧
      tgap X - Real.arcsin beta ≤ turning (KBall X) Γ := by
  set K := KBall X
  refine ⟨frontier K ∩ Metric.closedBall v 2, Set.inter_subset_left,
    fun x hx => by rw [dist_comm]; exact hx.2, ?_⟩
  set Θ := tgap X - Real.arcsin beta
  have hvK : v ∈ K := ball_polygon_a (Sset_sub hv) hvD
  have ht1 : tgap X ≤ 1 := by
    have := ball_polygon_c hzD hvK; rwa [dist_comm, hvz] at this
  have hab0 : 0 ≤ Real.arcsin beta := Real.arcsin_nonneg.2 (by unfold beta; norm_num)
  rcases le_or_gt Θ 0 with hΘ | hΘ
  · exact hΘ.trans ENNReal.toReal_nonneg
  have hΘ1 : Θ ≤ 1 := by linarith
  have hπ := Real.pi_gt_three
  -- the frame `(u, e₀)` at `v`, `e₀` pointing to `z`'s side
  set u := F.u v
  have hu : ‖u‖ = 1 := F.norm_u hv
  set zh := z - v
  have hzn : ‖zh‖ = 1 := by rw [← dist_eq_norm, dist_comm, hvz]
  set a := inner ℝ zh u
  set c := det2 u zh
  have hac : a ^ 2 + c ^ 2 = 1 := by
    have := inner_sq_add_det_sq (e := zh) hu; rw [hzn] at this; linarith
  have ha0 : 0 < a := hT.1
  have ha1 : a < beta := hT.2.1
  have hbeta : beta = 1 / 100 := rfl
  have hc0 : c ≠ 0 := by intro h; rw [h] at hac; rw [hbeta] at ha1; nlinarith
  set ς : ℝ := if 0 < c then 1 else -1
  have hς2 : ς * ς = 1 := by simp only [ς]; split_ifs <;> norm_num
  have hςc : 0 < ς * c := by
    simp only [ς]; split_ifs with h
    · linarith
    · have : c < 0 := lt_of_le_of_ne (not_lt.1 h) hc0
      linarith
  set e₀ : Pt := ς • perp u
  have hie : ∀ x, inner ℝ x e₀ = ς * det2 u x := by
    intro x; rw [inner_smul_right, real_inner_comm, det2_eq_inner_perpR]
  have he₀ : ‖e₀‖ = 1 := by
    rw [norm_smul, norm_perp, hu, mul_one, Real.norm_eq_abs]
    simp only [ς]; split_ifs <;> norm_num
  have hue : inner ℝ u e₀ = 0 := by rw [hie, det2_pt]; ring
  -- `−u` is an outward normal at `v`
  have hn₀ : -u ∈ normalCone K v := by
    have := neg_mem_normalCone hvK (F.partner_mem v hv) (F.partner_K v hv hvD)
      (dist v (F.partner v))⁻¹ (inv_nonneg.2 dist_nonneg)
    exact this
  -- `e₀` is close to `zh`
  have hze : ‖e₀ - zh‖ ≤ Real.arcsin beta := by
    have hsc : ς * c = Real.cos (Real.arcsin a) := by
      rw [Real.cos_arcsin, eq_comm, Real.sqrt_eq_iff_mul_self_eq (by nlinarith) hςc.le]
      linear_combination (-1) * hac - c ^ 2 * hς2
    have hz2 : ‖e₀ - zh‖ ^ 2 = 2 - 2 * Real.cos (Real.arcsin a) := by
      rw [@norm_sub_sq_real, he₀, hzn, real_inner_comm, hie, ← hsc]; ring
    have hA0 : 0 ≤ Real.arcsin a := Real.arcsin_nonneg.2 ha0.le
    have hA1 : Real.arcsin a ≤ Real.arcsin beta := Real.monotone_arcsin ha1.le
    have hcos := Real.one_sub_sq_div_two_le_cos (x := Real.arcsin a)
    have : ‖e₀ - zh‖ ^ 2 ≤ Real.arcsin beta ^ 2 := by rw [hz2]; nlinarith
    exact (sq_le_sq₀ (norm_nonneg _) hab0).1 this
  obtain ⟨xa, hxa⟩ : X.Nonempty := card_pos.1 (by linarith [hX.four_le])
  have hKc := KBall_isCompact ⟨xa, hxa⟩
  -- support points in the directions `ν(φ) = cos φ (−u) + sin φ e₀`, `0 < φ < Θ`
  have hframe : ∀ x : Pt, inner ℝ x u ^ 2 + inner ℝ x e₀ ^ 2 = ‖x‖ ^ 2 := by
    intro x
    rw [hie, ← inner_sq_add_det_sq (e := x) hu]
    linear_combination (det2 u x) ^ 2 * hς2
  have key : ∀ φ ∈ Set.Ioo 0 Θ, ∃ y ∈ frontier K ∩ Metric.closedBall v 2,
      (Real.cos φ • (-u) + Real.sin φ • e₀) ∈ normalCone K y := by
    intro φ hφ
    have hνn := norm_rot hu he₀ hue φ
    obtain ⟨y, hyK, hmax⟩ := hKc.exists_isMaxOn ⟨v, hvK⟩
      (f := fun y => inner ℝ y (Real.cos φ • (-u) + Real.sin φ • e₀))
      (continuous_id.inner continuous_const).continuousOn
    have hmax' : ∀ y' ∈ K, inner ℝ y' (Real.cos φ • (-u) + Real.sin φ • e₀) ≤
        inner ℝ y (Real.cos φ • (-u) + Real.sin φ • e₀) := fun y' hy' => hmax hy'
    refine ⟨y, ⟨mem_frontier_of_max hyK hνn hmax', ?_⟩, fun y' hy' => ?_⟩
    · rw [Metric.mem_closedBall]
      exact support_point_close hzD hvK hyK hu he₀ hframe hn₀ (hmax' v hvK) hφ.1
        (by linarith [hφ.2]) (by linarith [hφ.2])
    · rw [inner_sub_left]; linarith [hmax' y' hy']
  -- the angle of `−u`, and the measure of the arc of directions
  obtain ⟨θ₀, -, hθ₀⟩ := exists_angle (show ‖-u‖ = 1 by rw [norm_neg, hu])
  unfold turning
  have hfin : MeasureTheory.volume {θ : ℝ | θ ∈ Set.Ico 0 (2 * π) ∧
      ∃ x ∈ frontier K ∩ Metric.closedBall v 2, dirVec θ ∈ normalCone K x} ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (MeasureTheory.measure_mono (fun θ hθ => hθ.1))
    rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top
  rw [← ENNReal.ofReal_le_iff_le_toReal hfin]
  have hς : ς = 1 ∨ ς = -1 := by simp only [ς]; split_ifs <;> simp
  have hdir : ∀ φ : ℝ, dirVec (θ₀ + (-ς * φ)) = Real.cos φ • (-u) + Real.sin φ • e₀ := by
    intro φ
    rw [dirVec_addR, hθ₀, perp_neg]
    simp only [e₀]
    rcases hς with h | h <;> rw [h] <;> simp [Real.cos_neg, Real.sin_neg] <;> module
  refine vol_arc_ge _ (a := if ς = 1 then θ₀ - Θ else θ₀) hΘ.le (by linarith) ?_
  intro θ k hθ
  set θ' := θ + k * (2 * π)
  have hφ : ς * (θ₀ - θ') ∈ Set.Ioo 0 Θ := by
    rcases hς with h | h <;>
      simp only [h, if_true, if_neg (show (-1 : ℝ) ≠ 1 by norm_num)] at hθ ⊢ <;>
      constructor <;> linarith [hθ.1, hθ.2]
  obtain ⟨y, hyΓ, hyν⟩ := key _ hφ
  refine ⟨y, hyΓ, ?_⟩
  have e1 : dirVec θ = dirVec θ' := (dirVec_add_int θ k).symm
  have e2 : θ' = θ₀ + (-ς * (ς * (θ₀ - θ'))) := by
    have : -ς * (ς * (θ₀ - θ')) = -(ς * ς) * (θ₀ - θ') := by ring
    rw [this, hς2]; ring
  rw [e1, e2, hdir]; exact hyν

/-- Region III version of `c5_tgap`: `t − arcsin β ≥ 0.835` (`t ≥ min(τ, 1) > 0.846`). -/
private theorem tgap_arcsin_III (hX : Normal X) (hτ : √3 / 2 - 2 * beta < tau X) :
    0.835 ≤ tgap X - Real.arcsin beta := by
  have hb : beta = 1 / 100 := rfl
  have h3' : (1.732 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hpos := hX.dist2_pos
  have ht : 0.846 ≤ tgap X := by
    by_cases h1 : tgap X ≤ 1
    · have e := tau_sub_tgap X
      have : (tgap X ^ 2 - 1) / (2 * dist2 X) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg _ (by linarith)
        have : 0 ≤ tgap X := by
          have := (two_of_pos hpos).lt; unfold tgap; linarith
        nlinarith
      rw [hb] at hτ; linarith
    · linarith
  have hy : Real.arcsin beta < 0.01002 := by
    rw [Real.arcsin_lt_iff_lt_sin ⟨by rw [hb]; norm_num, by rw [hb]; norm_num⟩
      ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩]
    have := Real.sin_gt_sub_cube (x := 0.01002) (by norm_num)
    rw [hb]; norm_num at this ⊢; linarith
  linarith

/-- **Lemma 7.1 in Region III** (F3): `#mixed T-edges ≤ 1500` for `√3/2 − 2β < τ < √3/2 + 3β`
(`t ≥ τ > 0.846`, so `t − arcsin β > 0.835`).

TODO: none — proved (via the private copy `lemma71_III` of `lemma71`, whose proof never used
the Region II hypothesis, and `tgap_arcsin_III`; the count is `2·2π·81/0.835 < 1220`).
What's missing: (was) re-run `lemma71` / `card_mixedT_le` with the Region III lower bound
`t − arcsin β ≥ 0.835` in place of `c5_tgap` (`0.886`); the count becomes
`2π·81/0.835·… ≤ 1500`.
Acceptance: no `sorry`.
Depends on: proofs of `lemma71`, `card_mixedT_le`, `c5_tgap`. Difficulty M–L. -/
theorem card_mixedT_le_III (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 - 2 * beta < tau X)
    (hτ₂ : tau X < √3 / 2 + 3 * beta) : ((mixedT X F).card : ℝ) ≤ 1500 := by
  classical
  have h1 := hX.minDist_eq
  let Dat : Sym2 Pt → Pt → Pt → Prop := fun e v w => e = s(v, w) ∧ v ∈ Sset X ∧ v ∉ Dset X ∧
    w ∈ Sset X ∧ w ∈ Dset X ∧ dist v w = 1 ∧ IsTEdge F v w ∧ ang (F.u v) (F.u w) ≤ beta
  let kend : Sym2 Pt → Pt := fun e => if h : ∃ v w, Dat e v w then h.choose else 0
  have hk : ∀ e ∈ mixedT X F, ∃ w, Dat e (kend e) w := by
    intro e he
    have h : ∃ v w, Dat e v w := mixedT_data he h1
    have : kend e = h.choose := dif_pos h
    rw [this]; exact h.choose_spec
  set A := (mixedT X F).image kend
  -- step 1: at most two mixed edges per K-end
  have hA : (mixedT X F).card ≤ 2 * A.card := by
    refine card_le_mul_card_image_of_maps_to (fun e he => mem_image_of_mem _ he) 2 ?_
    intro v _
    set G := (mixedT X F).filter (fun e => kend e = v)
    let P : ℝ → Sym2 Pt → Prop := fun σ e => ∃ w, Dat e v w ∧ 0 < σ * det2 (F.u v) (w - v)
    have hsplit : G ⊆ G.filter (P 1) ∪ G.filter (P (-1)) := by
      intro e he
      obtain ⟨he', hkv⟩ := mem_filter.1 he
      obtain ⟨w, hd⟩ := hk e he'
      rw [hkv] at hd
      obtain ⟨-, hv, -, -, -, hvw, hT, -⟩ := id hd
      have n := inner_sq_add_det_sq (e := w - v) (F.norm_u hv)
      rw [← dist_eq_norm, dist_comm, hvw] at n
      have hne : det2 (F.u v) (w - v) ≠ 0 := by
        intro h0; rw [h0] at n
        have := hT.2.1; unfold beta at this; nlinarith [hT.1]
      rcases hne.lt_or_gt with h | h
      · exact mem_union.2 (Or.inr (mem_filter.2 ⟨he, w, hd, by linarith⟩))
      · exact mem_union.2 (Or.inl (mem_filter.2 ⟨he, w, hd, by linarith⟩))
    have hside : ∀ σ, (G.filter (P σ)).card ≤ 1 := by
      intro σ
      refine card_le_one.2 fun e₁ he₁ e₂ he₂ => ?_
      obtain ⟨w₁, ⟨r₁, hv, -, hw₁, -, d₁, t₁, -⟩, s₁⟩ := (mem_filter.1 he₁).2
      obtain ⟨w₂, ⟨r₂, -, -, hw₂, -, d₂, t₂, -⟩, s₂⟩ := (mem_filter.1 he₂).2
      rw [r₁, r₂, tnbr_unique hX hv hw₁ hw₂ d₁ d₂ t₁ t₂ s₁ s₂]
    calc G.card ≤ (G.filter (P 1) ∪ G.filter (P (-1))).card := card_le_card hsplit
      _ ≤ (G.filter (P 1)).card + (G.filter (P (-1))).card := card_union_le _ _
      _ ≤ 2 := by linarith [hside 1, hside (-1)]
  -- step 2: the boundary sets of Lemma 7.1 and the multiplicity bound
  let Arc : Pt → Prop := fun v => ∃ Γ : Set Pt, Γ ⊆ frontier (KBall X) ∧ (∀ x ∈ Γ, dist v x ≤ 2) ∧
    tgap X - Real.arcsin beta ≤ turning (KBall X) Γ
  have hArc : ∀ v ∈ A, Arc v ∧ v ∈ Sset X := by
    intro v hv
    obtain ⟨e, he, rfl⟩ := mem_image.1 hv
    obtain ⟨w, -, hv, hvD, hw, hwD, hvw, hT, -⟩ := hk e he
    exact ⟨lemma71_III hX F hv hvD hw hwD hvw hT, hv⟩
  let Γ : Pt → Set Pt := fun v => if h : Arc v then h.choose else ∅
  have hΓ : ∀ v ∈ A, Γ v ⊆ frontier (KBall X) ∧ tgap X - Real.arcsin beta ≤ turning (KBall X) (Γ v)
      ∧ ∀ x ∈ Γ v, dist v x ≤ 2 := by
    intro v hv
    have h := (hArc v hv).1
    have e : Γ v = h.choose := dif_pos h
    obtain ⟨hsub, hd, htu⟩ := h.choose_spec
    rw [e]
    exact ⟨hsub, htu, hd⟩
  obtain ⟨a, ha⟩ : X.Nonempty := card_pos.1 (by linarith [hX.four_le])
  have hsum := turning_sum_le_closure (KBall_convex X) (KBall_isCompact ⟨a, ha⟩) A Γ
    (fun v hv => (hΓ v hv).1) 81 (fun x => by
      refine card_sep_le_81 (fun a ha b hb hab => ?_) x (fun a ha => ?_)
      · exact one_le_dist h1 (Sset_sub (hArc a (mem_filter.1 ha).1).2)
          (Sset_sub (hArc b (mem_filter.1 hb).1).2) hab
      · have hsub : Γ a ⊆ Metric.closedBall a 2 := fun y hy => by
          rw [Metric.mem_closedBall, dist_comm]; exact (hΓ a (mem_filter.1 ha).1).2.2 y hy
        have hx := closure_minimal hsub Metric.isClosed_closedBall (mem_filter.1 ha).2
        rw [Metric.mem_closedBall] at hx; rw [dist_comm]; exact hx)
  have hlow : ∑ v ∈ A, (0.835 : ℝ) ≤ ∑ v ∈ A, turning (KBall X) (Γ v) :=
    sum_le_sum fun v hv => (tgap_arcsin_III hX hτ₁).trans (hΓ v hv).2.1
  rw [sum_const, nsmul_eq_mul] at hlow
  have hπ := Real.pi_lt_d4
  have hAc : (A.card : ℝ) * 0.835 ≤ 2 * π * 81 := by push_cast at hsum; linarith
  have hA' : ((mixedT X F).card : ℝ) ≤ 2 * A.card := by exact_mod_cast hA
  nlinarith

/-! ## Region III -/

/-- **Key bound**: `#T + q₂ ≤ |S| + cBad + 1500` on all of Region III.

TODO: none — proved from the statements (wiring).
Acceptance: no `sorry` (inherits).
Depends on: `twoRung_eq_empty`, `card_tEdges_le`, `card_tEdges_add_twoRung_lt`,
`card_tEdges_add_breaks_le`, `exact_breaks`, `card_mixedT_le_III`. -/
theorem regionIII_key (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 - 2 * beta < tau X)
    (hτ₂ : tau X < √3 / 2 + 3 * beta) :
    ((tEdges X F).card : ℝ) + (twoRungVerts X F).card ≤ (Sset X).card + (cBad + 1500) := by
  have hc : (0 : ℝ) ≤ cBad := by norm_num [cBad]
  rcases lt_trichotomy (tau X) (√3 / 2) with h | h | h
  · have := card_tEdges_add_twoRung_lt hX F hτ₁ h
    have : ((tEdges X F).card : ℝ) + (twoRungVerts X F).card ≤ (Sset X).card := by
      exact_mod_cast this
    linarith
  · have h1 := card_tEdges_add_breaks_le hX F
    have h1' : ((tEdges X F).card : ℝ) + (breaks X F).card ≤ (Sset X).card + (mixedT X F).card := by
      exact_mod_cast h1
    have h2 := exact_breaks hX F h
    have h3 := card_mixedT_le_III hX F hτ₁ hτ₂
    linarith
  · rw [twoRung_eq_empty hX F h hτ₂, card_empty, Nat.cast_zero, add_zero]
    have : ((tEdges X F).card : ℝ) ≤ (Sset X).card := by exact_mod_cast card_tEdges_le hX F
    linarith

/-- **Region III** (`√3/2 − 2β < τ < √3/2 + 3β`): `e(S) ≤ |S| + |P₁| + cReg`.

TODO: none — proved from the statements (wiring).
Acceptance: no `sorry` (inherits).
Depends on: `good_subset_T_union_rungs`, `card_rungs_le_add`, `card_rungVerts`,
`card_cornerVerts_le`, `regionIII_key`, `card_good_add_bad`, `card_bad_le`, `two_beta_lt_of`. -/
theorem regionIII15 (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 - 2 * beta < tau X)
    (hτ₂ : tau X < √3 / 2 + 3 * beta) :
    (eS X : ℝ) ≤ (Sset X).card + (P1set X F).card + cReg := by
  have hsub := good_subset_T_union_rungs hX F (two_beta_lt_of hτ₁)
  have hg := (card_le_card hsub).trans (card_union_le _ _)
  have hR := card_rungs_le_add hX F
  have hV := card_rungVerts F
  have hC := card_cornerVerts_le hX F hτ₁ hτ₂
  have hgood : ((good X F).card : ℝ) ≤ (tEdges X F).card + (twoRungVerts X F).card +
      (P1set X F).card + 6 := by
    exact_mod_cast (show (good X F).card ≤ (tEdges X F).card + (twoRungVerts X F).card +
      (P1set X F).card + 6 by omega)
  have hkey := regionIII_key hX F hτ₁ hτ₂
  have h3 := card_bad_le hX F
  have : (eS X : ℝ) = (good X F).card + (bad X F).card := by
    exact_mod_cast (card_good_add_bad F).symm
  unfold cReg
  linarith

end

end Erdos132Main
