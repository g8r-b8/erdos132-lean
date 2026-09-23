import Erdos132.E132MainLocal

/-!
# Erdős Problem 132, `54/37` theorem — Regions I, II, III (§§6–7)

Every region lemma bounds `e(S)`; the top-level region statements (`regionI`, `regionII_high`,
`regionII_rest`, `regionII_res`, `regionIII`) are **proved** here from the finer lemmas, so the
statements are checked to fit together.  Region split on `τ` (with `β = 1/100`):

| region | `τ` range | `e(S) ≤` |
|---|---|---|
| I | `τ ≤ √3/2 − 2β` | `|S| + C` |
| III | `√3/2 − 2β < τ < √3/2 + 3β` | `|S| + 2|P₁| + C` |
| II-rest | `√3/2 + 3β ≤ τ < cos(β/2)` | `(5/4)|S| + C` |
| II-res | `cos(β/2) ≤ τ ≤ 1` | `(4/3)|S| + C` |
| II-high | `τ > 1` | `|S| + C` |
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-! ## Helpers (coordinates, separation, unit vectors, offsets, T-steps) -/

theorem inner_pt (x y : Pt) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_two, dotProduct]; ring

theorem norm_sq_pt (x : Pt) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_pt]; ring

theorem dist_sq_pt (x y : Pt) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [dist_eq_norm, norm_sq_pt]; simp

@[simp] theorem perp_apply0 (a : Pt) : perp a 0 = - a 1 := by simp [perp]
@[simp] theorem perp_apply1 (a : Pt) : perp a 1 = a 0 := by simp [perp]

theorem pt_ext_iff {a b : Pt} : a = b ↔ a 0 = b 0 ∧ a 1 = b 1 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩
    ext i; fin_cases i <;> simp [h0, h1]

theorem det2_pt (a b : Pt) : det2 a b = a 0 * b 1 - a 1 * b 0 := rfl

theorem norm_perp (a : Pt) : ‖perp a‖ = ‖a‖ := by
  have h : ‖perp a‖ ^ 2 = ‖a‖ ^ 2 := by rw [norm_sq_pt, norm_sq_pt]; simp; ring
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

theorem perp_sub (a b : Pt) : perp (a - b) = perp a - perp b := by
  rw [pt_ext_iff]; simp; ring

theorem unit_sq {a : Pt} (h : ‖a‖ = 1) : a 0 ^ 2 + a 1 ^ 2 = 1 := by
  rw [← norm_sq_pt, h, one_pow]

theorem inner_unit_le {a b : Pt} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) : |inner ℝ a b| ≤ 1 := by
  have := abs_real_inner_le_norm a b; rw [ha, hb] at this; simpa using this

theorem ang_unit {a b : Pt} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ang a b = Real.arccos (inner ℝ a b) := by
  unfold ang InnerProductGeometry.angle; rw [ha, hb]; simp

theorem cos_ang_unit {a b : Pt} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    Real.cos (ang a b) = inner ℝ a b := by
  unfold ang; rw [InnerProductGeometry.cos_angle, ha, hb]; simp

theorem ang_comm (a b : Pt) : ang a b = ang b a := InnerProductGeometry.angle_comm a b

/-- Chord `≤` arc for unit vectors. -/
theorem norm_sub_le_angR {a b : Pt} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) : ‖a - b‖ ≤ ang a b := by
  have h0 : 0 ≤ ang a b := InnerProductGeometry.angle_nonneg a b
  have hc := Real.one_sub_sq_div_two_le_cos (x := ang a b)
  rw [cos_ang_unit ha hb] at hc
  have hn : ‖a - b‖ ^ 2 = 2 - 2 * inner ℝ a b := by
    rw [@norm_sub_sq_real, ha, hb]; ring
  have : ‖a - b‖ ^ 2 ≤ ang a b ^ 2 := by rw [hn]; linarith
  exact (sq_le_sq₀ (norm_nonneg _) h0).1 this

/-- A lower bound on an angle from an upper bound on the inner product. -/
theorem lt_ang_of_inner_lt {a b : Pt} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) {θ : ℝ} (h0 : 0 ≤ θ)
    (hπ : θ ≤ π) (h : inner ℝ a b < Real.cos θ) : θ < ang a b := by
  rw [ang_unit ha hb]
  have h1 := inner_unit_le ha hb
  rw [abs_le] at h1
  calc θ = Real.arccos (Real.cos θ) := (Real.arccos_cos h0 hπ).symm
    _ < Real.arccos (inner ℝ a b) :=
        Real.arccos_lt_arccos h1.1 h (Real.cos_le_one θ)

theorem cos_le_inner_of_ang_le {a b : Pt} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) {θ : ℝ}
    (hπ : θ ≤ π) (h : ang a b ≤ θ) : Real.cos θ ≤ inner ℝ a b := by
  rw [← cos_ang_unit ha hb]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (InnerProductGeometry.angle_nonneg a b) hπ h

/-- Decomposition in the frame `(u, u^⊥)` of a unit `u`. -/
theorem decompR {u : Pt} (hu : ‖u‖ = 1) (e : Pt) :
    e = inner ℝ e u • u + det2 u e • perp u := by
  have h := unit_sq hu
  rw [pt_ext_iff, inner_pt, det2_pt]; simp
  constructor
  · linear_combination (-e 0) * h
  · linear_combination (-e 1) * h

theorem inner_sq_add_det_sq {u e : Pt} (hu : ‖u‖ = 1) :
    inner ℝ e u ^ 2 + det2 u e ^ 2 = ‖e‖ ^ 2 := by
  have h := unit_sq hu
  rw [inner_pt, det2_pt, norm_sq_pt]; linear_combination (e 0 ^ 2 + e 1 ^ 2) * h

/-- Lagrange-type identity: `(c·a)(c·b) + det(c,a) det(c,b) = |c|² (a·b)`. -/
theorem inner_mul_add_det_mul (c a b : Pt) :
    inner ℝ c a * inner ℝ c b + det2 c a * det2 c b = ‖c‖ ^ 2 * inner ℝ a b := by
  rw [inner_pt, inner_pt, inner_pt, det2_pt, det2_pt, norm_sq_pt]; ring

theorem norm_frame {a c : ℝ} (h : a ^ 2 + c ^ 2 = 1) (w : Pt) : ‖a • w + c • perp w‖ = ‖w‖ := by
  have : ‖a • w + c • perp w‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [norm_sq_pt, norm_sq_pt]; simp; linear_combination (w 0 ^ 2 + w 1 ^ 2) * h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

theorem norm_frame_le (a c : ℝ) {u : Pt} (hu : ‖u‖ = 1) : ‖a • u + c • perp u‖ ≤ |a| + |c| := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, norm_perp, hu, Real.norm_eq_abs, Real.norm_eq_abs]; simp

/-- Offsets `o_σ(u) = −τu + σ s u^⊥`: `|o_σ(u) − o_σ'(u')| ≤ |τ||u − u'| + 2s`. -/
theorem norm_offset_sub {u u' : Pt} (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1) {τ s σ σ' : ℝ}
    (hs : 0 ≤ s) (hσ : σ = 1 ∨ σ = -1) (hσ' : σ' = 1 ∨ σ' = -1) :
    ‖((-τ) • u + (σ * s) • perp u) - ((-τ) • u' + (σ' * s) • perp u')‖ ≤
      |τ| * ‖u - u'‖ + 2 * s := by
  have e : ((-τ) • u + (σ * s) • perp u) - ((-τ) • u' + (σ' * s) • perp u') =
      (-τ) • (u - u') + ((σ * s) • perp u - (σ' * s) • perp u') := by
    rw [smul_sub]; abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs, abs_neg]
  · refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, norm_smul, norm_perp, norm_perp, hu, hu', Real.norm_eq_abs, Real.norm_eq_abs,
      abs_mul, abs_mul]
    rcases hσ with rfl | rfl <;> rcases hσ' with rfl | rfl <;>
      simp [abs_of_nonneg hs] <;> linarith

/-- Two right T-steps from nearly parallel normals are close. -/
theorem norm_tstep_sub {u₁ u₂ e₁ e₂ : Pt} (hu₁ : ‖u₁‖ = 1) (hu₂ : ‖u₂‖ = 1) (he₁ : ‖e₁‖ = 1)
    (he₂ : ‖e₂‖ = 1) (ha₁ : 0 < inner ℝ e₁ u₁) (ha₁' : inner ℝ e₁ u₁ < beta)
    (ha₂ : 0 < inner ℝ e₂ u₂) (ha₂' : inner ℝ e₂ u₂ < beta) (hc₁ : det2 u₁ e₁ < 0)
    (hc₂ : det2 u₂ e₂ < 0) : ‖e₁ - e₂‖ ≤ ‖u₁ - u₂‖ + 2 * beta := by
  set a₁ := inner ℝ e₁ u₁
  set a₂ := inner ℝ e₂ u₂
  set c₁ := det2 u₁ e₁
  set c₂ := det2 u₂ e₂
  have n₁ := inner_sq_add_det_sq (e := e₁) hu₁
  have n₂ := inner_sq_add_det_sq (e := e₂) hu₂
  rw [he₁] at n₁; rw [he₂] at n₂
  have E : e₁ - e₂ = (a₁ • (u₁ - u₂) + c₁ • perp (u₁ - u₂)) +
      ((a₁ - a₂) • u₂ + (c₁ - c₂) • perp u₂) := by
    conv_lhs => rw [decompR hu₁ e₁, decompR hu₂ e₂]
    rw [perp_sub, smul_sub, smul_sub, sub_smul, sub_smul]; abel
  rw [E]
  refine (norm_add_le _ _).trans ?_
  rw [norm_frame (by linarith) (u₁ - u₂)]
  have h2 := norm_frame_le (a₁ - a₂) (c₁ - c₂) hu₂
  have hb : beta = 1 / 100 := rfl
  have ha : |a₁ - a₂| ≤ beta := by rw [abs_le]; constructor <;> linarith
  have hc : |c₁ - c₂| ≤ beta := by
    rw [abs_le]
    constructor <;> nlinarith
  linarith

/-- Two unit solutions of `c·u = −τ` that differ have `u₁·u₂ = 2τ² − 1`. -/
theorem inner_two_sol {c u₁ u₂ : Pt} {τ : ℝ} (hc : ‖c‖ = 1) (h₁ : ‖u₁‖ = 1) (h₂ : ‖u₂‖ = 1)
    (e₁ : inner ℝ c u₁ = -τ) (e₂ : inner ℝ c u₂ = -τ) (hne : u₁ ≠ u₂) :
    inner ℝ u₁ u₂ = 2 * τ ^ 2 - 1 := by
  have n₁ := inner_sq_add_det_sq (e := u₁) hc
  have n₂ := inner_sq_add_det_sq (e := u₂) hc
  rw [real_inner_comm, e₁, h₁] at n₁
  rw [real_inner_comm, e₂, h₂] at n₂
  have hL := inner_mul_add_det_mul c u₁ u₂
  rw [e₁, e₂, hc] at hL
  have hd : det2 c u₁ ≠ det2 c u₂ := by
    intro hd; apply hne
    rw [decompR hc u₁, decompR hc u₂, real_inner_comm, e₁, real_inner_comm, e₂, hd]
  have hd' : det2 c u₁ = - det2 c u₂ := by
    have : (det2 c u₁ - det2 c u₂) * (det2 c u₁ + det2 c u₂) = 0 := by linear_combination n₁ - n₂
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hd
    · linarith
  rw [hd'] at hL
  linear_combination -hL - n₂

theorem det2_eq_inner_perpR (a b : Pt) : det2 a b = inner ℝ (perp a) b := by
  rw [det2_pt, inner_pt]; simp; ring

theorem abs_det2_leR (a b : Pt) : |det2 a b| ≤ ‖a‖ * ‖b‖ := by
  rw [det2_eq_inner_perpR, ← norm_perp a]; exact abs_real_inner_le_norm _ _

theorem det2_add_left (a b e : Pt) : det2 (a + b) e = det2 a e + det2 b e := by
  simp only [det2_pt, PiLp.add_apply]; ring

theorem det2_neg_right (a e : Pt) : det2 a (-e) = - det2 a e := by
  simp only [det2_pt, PiLp.neg_apply]; ring

/-! ### The point set -/

theorem dist_mem_distSetS' {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) :
    dist x y ∈ distSetS X := by
  unfold distSetS pairsS
  refine mem_image.2 ⟨s(x, y), mem_filter.2 ⟨mk_mem_sym2_iff.2 ⟨hx, hy⟩, ?_⟩, ?_⟩
  · simpa using hxy
  · simp [pairDist]

theorem pos_of_mem_distSetS' {d : ℝ} (hd : d ∈ distSetS X) : 0 < d := by
  unfold distSetS pairsS at hd
  obtain ⟨z, hz, rfl⟩ := mem_image.1 hd
  induction z using Sym2.ind with
  | h a b =>
    have hab : a ≠ b := by simpa using (mem_filter.1 hz).2
    simpa [pairDist] using dist_pos.2 hab

theorem minDist_le_distR {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) :
    minDist X ≤ dist x y := by
  have hm := dist_mem_distSetS' hx hy hxy
  unfold minDist
  rw [dif_pos ⟨_, hm⟩]
  exact min'_le _ _ hm

theorem one_le_dist (h1 : minDist X = 1) {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) :
    1 ≤ dist x y := h1 ▸ minDist_le_distR hx hy hxy

theorem eq_of_dist_lt_one (h1 : minDist X = 1) {x y : Pt} (hx : x ∈ X) (hy : y ∈ X)
    (h : dist x y < 1) : x = y := by
  by_contra hxy; exact absurd (one_le_dist h1 hx hy hxy) (not_le.2 h)

theorem dist2_nonnegR (X : Finset Pt) : 0 ≤ dist2 X := by
  unfold dist2
  split_ifs with h
  · exact (pos_of_mem_distSetS' (mem_of_mem_erase (max'_mem _ h))).le
  · exact le_rfl

/-- The two largest distances, when `Δ₂ > 0`. -/
structure Two (X : Finset Pt) : Prop where
  pos : 0 < dist2 X
  lt : dist2 X < diam X
  le_diam : ∀ x ∈ X, ∀ y ∈ X, dist x y ≤ diam X
  gap : ∀ x ∈ X, ∀ y ∈ X, dist x y ≤ dist2 X ∨ dist x y = diam X

theorem two_of_pos (h : 0 < dist2 X) : Two X := by
  have h' := h
  unfold dist2 at h'
  split_ifs at h' with hne
  · have hne0 : (distSetS X).Nonempty := hne.mono (erase_subset _ _)
    have hd : diam X = (distSetS X).max' hne0 := by unfold diam; rw [dif_pos hne0]
    have hd2 : dist2 X = ((distSetS X).erase (diam X)).max' hne := by
      unfold dist2; rw [dif_pos hne]
    have h2 := max'_mem _ hne
    rw [← hd2] at h2
    have hle : ∀ x ∈ X, ∀ y ∈ X, dist x y ≤ diam X := by
      intro x hx y hy
      by_cases hxy : x = y
      · subst hxy; rw [dist_self, hd]; exact (pos_of_mem_distSetS' (max'_mem _ _)).le
      · rw [hd]; exact le_max' _ _ (dist_mem_distSetS' hx hy hxy)
    refine ⟨h, lt_of_le_of_ne (hd ▸ le_max' _ _ (mem_of_mem_erase h2)) (ne_of_mem_erase h2),
      hle, ?_⟩
    intro x hx y hy
    by_cases hxy : x = y
    · subst hxy; left; rw [dist_self]; exact h.le
    rcases (hle x hx y hy).lt_or_eq with hl | hl
    · left; rw [hd2]; exact le_max' _ _ (mem_erase.2 ⟨hl.ne, dist_mem_distSetS' hx hy hxy⟩)
    · exact Or.inr hl
  · exact absurd h' (lt_irrefl 0)

theorem mem_Dset_ofR {p q : Pt} (hp : p ∈ X) (hq : q ∈ X) (hpq : q ≠ p) (h : dist p q = diam X) :
    p ∈ Dset X := by
  unfold Dset partners
  exact mem_filter.2 ⟨hp, q, mem_filter.2 ⟨hq, hpq, h⟩⟩

theorem Normal.dist2_pos (hX : Normal X) : 0 < dist2 X := by
  have := hX.large; linarith

theorem Sset_sub : Sset X ⊆ X := filter_subset _ _

/-- `τ ≥ −1/2` once `Δ₂ ≥ 1`. -/
theorem neg_half_le_tau (hT : Two X) (h1 : 1 ≤ dist2 X) : -(1 / 2) ≤ tau X := by
  have ht : 0 < tgap X := by unfold tgap; linarith [hT.lt]
  have : (1 - tgap X ^ 2) / (2 * dist2 X) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  unfold tau; linarith

theorem abs_tau_le_one (hτ₁ : √3 / 2 + 3 * beta ≤ tau X) (hτ₂ : tau X ≤ 1) : |tau X| ≤ 1 := by
  have := Real.sqrt_nonneg 3
  rw [abs_le]; unfold beta at hτ₁; constructor <;> linarith

namespace IsRung

variable {F : DirField X} {v z : Pt}

theorem memX (h : IsRung F v z) : v ∈ X ∧ z ∈ X := ⟨Sset_sub h.1, Sset_sub h.2.2.1⟩

theorem ne (h : IsRung F v z) : v ≠ z := by
  intro e; have := h.2.2.2.2.1; rw [e, dist_self] at this; norm_num at this

/-- A rung forces `Δ₂ > 0` (so the two largest distances exist) and `Δ₂ ≥ 1`. -/
theorem two (h : IsRung F v z) : Two X ∧ 1 ≤ dist2 X := by
  obtain ⟨hv, hvD, hz, hzD, h1, hex⟩ := h
  have hvX := Sset_sub hv
  have hzX := Sset_sub hz
  have hvz : z ≠ v := by intro e; rw [e, dist_self] at h1; norm_num at h1
  have hpos : 0 < dist2 X := by
    rcases (dist2_nonnegR X).lt_or_eq with h' | h'
    · exact h'
    · exfalso
      have hp := F.partner_K v hv hvD
      rw [← h', dist_eq_zero] at hp
      rw [← hp] at hex
      rw [dist_comm] at hex
      exact hvD (mem_Dset_ofR hvX hzX hvz hex)
  have hT := two_of_pos hpos
  refine ⟨hT, ?_⟩
  rcases hT.gap v hvX z hzX with h' | h'
  · linarith
  · exact absurd (mem_Dset_ofR hvX hzX hvz h') hvD

theorem tau_ge (h : IsRung F v z) : -(1 / 2) ≤ tau X := neg_half_le_tau h.two.1 h.two.2

/-- `c = z − v` is a unit vector with `c·u_v = −τ`. -/
theorem inner_eq (h : IsRung F v z) : inner ℝ (z - v) (F.u v) = - tau X :=
  exact_identity_c F h.1 h.2.1 h.2.2.2.2.2 (by rw [dist_comm]; exact h.2.2.2.2.1)

theorem norm_c (h : IsRung F v z) : ‖z - v‖ = 1 := by
  rw [← dist_eq_norm, dist_comm]; exact h.2.2.2.2.1

end IsRung

/-- `δ`-edges inside `S` are non-degenerate pairs of points of `S`.

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem mem_edges {z : Sym2 Pt} (hz : z ∈ edges X) : ¬ z.IsDiag ∧ ∀ p ∈ z, p ∈ Sset X := by
  unfold edges pairsS at hz
  simp only [mem_filter, mem_sym2_iff] at hz
  exact ⟨hz.1.2, hz.1.1⟩

/-! ### The ball polygon `K`: convex, compact, interior, normals -/

theorem mem_KBall {y : Pt} : y ∈ KBall X ↔ ∀ w ∈ X, dist y w ≤ dist2 X := by
  unfold KBall; simp [Metric.mem_closedBall]

theorem KBall_convex (X : Finset Pt) : Convex ℝ (KBall X) :=
  convex_iInter₂ fun _ _ => convex_closedBall _ _

theorem KBall_isCompact {X : Finset Pt} (hX : X.Nonempty) : IsCompact (KBall X) := by
  obtain ⟨w, hw⟩ := hX
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_biInter fun _ _ => Metric.isClosed_closedBall) ?_
  exact (Metric.isBounded_closedBall (x := w) (r := dist2 X)).subset
    (fun y hy => Metric.mem_closedBall.2 ((mem_KBall.1 hy) w hw))

/-- Two distinct points of `K` give an interior point (their midpoint). -/
theorem KBall_interior_nonempty {a b : Pt} (ha : a ∈ KBall X) (hb : b ∈ KBall X) (hab : a ≠ b) :
    (interior (KBall X)).Nonempty := by
  set m : Pt := (1 / 2 : ℝ) • (a + b)
  have hsub : (⋂ w ∈ X, Metric.ball w (dist2 X)) ⊆ KBall X :=
    Set.iInter₂_mono fun _ _ => Metric.ball_subset_closedBall
  have hopen : IsOpen (⋂ w ∈ X, Metric.ball w (dist2 X)) :=
    isOpen_biInter_finset fun _ _ => Metric.isOpen_ball
  refine ⟨m, interior_mono hsub (hopen.interior_eq.symm ▸ ?_)⟩
  simp only [Set.mem_iInter, Metric.mem_ball]
  intro w hw
  have h1 := (mem_KBall.1 ha) w hw
  have h2 := (mem_KBall.1 hb) w hw
  have hd : 0 < dist a b := dist_pos.2 hab
  have hΔ : 0 ≤ dist2 X := dist2_nonnegR X
  have e1 := dist_sq_pt a w
  have e2 := dist_sq_pt b w
  have e3 := dist_sq_pt a b
  have em : dist m w ^ 2 = (dist a w ^ 2 + dist b w ^ 2) / 2 - dist a b ^ 2 / 4 := by
    rw [dist_sq_pt, e1, e2, e3]; simp only [m, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]; ring
  have : dist m w ^ 2 < dist2 X ^ 2 := by
    rw [em]; nlinarith [dist_nonneg (x := a) (y := w), dist_nonneg (x := b) (y := w)]
  exact lt_of_pow_lt_pow_left₀ 2 hΔ this

/-- `−(w − v)` is an outward normal of `K` at `v ∈ K` when `|vw| = Δ₂`, `w ∈ X`. -/
theorem neg_mem_normalCone {v w : Pt} (hv : v ∈ KBall X) (hw : w ∈ X) (hvw : dist v w = dist2 X)
    (c : ℝ) (hc : 0 ≤ c) : -(c • (w - v)) ∈ normalCone (KBall X) v := by
  intro y hy
  have h1 := (mem_KBall.1 hy) w hw
  have h2 : dist y w ^ 2 ≤ dist v w ^ 2 := by
    rw [hvw]; exact pow_le_pow_left₀ dist_nonneg h1 2
  rw [dist_sq_pt, dist_sq_pt] at h2
  rw [inner_neg_right, inner_smul_right, inner_pt]
  simp only [PiLp.sub_apply]
  have : 0 ≤ (y 0 - v 0) * (w 0 - v 0) + (y 1 - v 1) * (w 1 - v 1) := by
    nlinarith [sq_nonneg (y 0 - v 0), sq_nonneg (y 1 - v 1)]
  nlinarith

/-! ## §6 Region I: `τ ≤ √3/2 − 2β` -/

/-- **[C4]** the elevation window is `< 60°`: `arcsin(√3/2 − 2β) + arcsin β < π/3`.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `Real.arcsin` bounds. Difficulty M. -/
theorem c4_window : Real.arcsin (√3 / 2 - 2 * beta) + Real.arcsin beta < π / 3 := by
  have hb : beta = 1 / 100 := rfl
  have h3 : √3 < 1.7321 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h3' : (1.732 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hπ := Real.pi_gt_three
  have hB0 : 0 ≤ Real.arcsin beta := Real.arcsin_nonneg.2 (by rw [hb]; norm_num)
  have hB1 : Real.arcsin beta ≤ π / 2 := Real.arcsin_le_pi_div_two _
  have key : Real.arcsin (√3 / 2 - 2 * beta) < π / 3 - Real.arcsin beta := by
    rw [Real.arcsin_lt_iff_lt_sin ⟨by rw [hb]; linarith, by rw [hb]; linarith⟩
      ⟨by linarith, by linarith⟩]
    rw [Real.sin_sub, Real.sin_pi_div_three, Real.cos_pi_div_three, Real.cos_arcsin,
      Real.sin_arcsin (by rw [hb]; norm_num) (by rw [hb]; norm_num)]
    have hs : 1 - beta ^ 2 ≤ √(1 - beta ^ 2) := by
      rw [Real.le_sqrt (by rw [hb]; norm_num) (by rw [hb]; norm_num)]; rw [hb]; norm_num
    rw [hb] at hs ⊢
    nlinarith
  linarith

/-- Two unit vectors on the same side of `ℝu` whose elevations lie in a window of angular width
`< 60°` are less than `1` apart. -/
theorem same_side_close {u e₁ e₂ : Pt} (hu : ‖u‖ = 1) (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) {σ : ℝ}
    (hs₁ : 0 < σ * det2 u e₁) (hs₂ : 0 < σ * det2 u e₂) {L U : ℝ}
    (ha₁ : L ≤ inner ℝ e₁ u ∧ inner ℝ e₁ u ≤ U) (ha₂ : L ≤ inner ℝ e₂ u ∧ inner ℝ e₂ u ≤ U)
    (hw : Real.arcsin U - Real.arcsin L < π / 3) : ‖e₁ - e₂‖ < 1 := by
  have hL := inner_mul_add_det_mul u e₁ e₂
  rw [hu, real_inner_comm e₁ u, real_inner_comm e₂ u, one_pow, one_mul] at hL
  set a₁ := inner ℝ e₁ u
  set a₂ := inner ℝ e₂ u
  set c₁ := det2 u e₁
  set c₂ := det2 u e₂
  have n₁ := inner_sq_add_det_sq (e := e₁) hu
  have n₂ := inner_sq_add_det_sq (e := e₂) hu
  rw [h₁] at n₁; rw [h₂] at n₂
  have hcc : 0 < c₁ * c₂ := by
    have := mul_pos hs₁ hs₂
    have hσ : σ ≠ 0 := by rintro rfl; simp at hs₁
    have : 0 < σ ^ 2 * (c₁ * c₂) := by linarith [show σ * c₁ * (σ * c₂) = σ ^ 2 * (c₁ * c₂) by ring]
    exact pos_of_mul_pos_right this (sq_nonneg σ)
  have ha₁r : a₁ ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> nlinarith [sq_nonneg c₁]
  have ha₂r : a₂ ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> nlinarith [sq_nonneg c₂]
  have hcc' : c₁ * c₂ = Real.cos (Real.arcsin a₁) * Real.cos (Real.arcsin a₂) := by
    rw [Real.cos_arcsin, Real.cos_arcsin, ← Real.sqrt_mul (by nlinarith)]
    rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (by nlinarith) hcc.le]
    have e1 : 1 - a₁ ^ 2 = c₁ ^ 2 := by linarith
    have e2 : 1 - a₂ ^ 2 = c₂ ^ 2 := by linarith
    rw [e1, e2]; ring
  have hinner : inner ℝ e₁ e₂ = Real.cos (Real.arcsin a₁ - Real.arcsin a₂) := by
    rw [Real.cos_sub, ← hcc', Real.sin_arcsin ha₁r.1 ha₁r.2, Real.sin_arcsin ha₂r.1 ha₂r.2]
    linarith
  have hd : |Real.arcsin a₁ - Real.arcsin a₂| < π / 3 := by
    have m1 := Real.monotone_arcsin ha₁.1
    have m2 := Real.monotone_arcsin ha₁.2
    have m3 := Real.monotone_arcsin ha₂.1
    have m4 := Real.monotone_arcsin ha₂.2
    rw [abs_lt]; constructor <;> linarith
  have hcos : 1 / 2 < inner ℝ e₁ e₂ := by
    rw [hinner, ← Real.cos_abs, ← Real.cos_pi_div_three]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hd
  have hn : ‖e₁ - e₂‖ ^ 2 < 1 := by
    rw [@norm_sub_sq_real, h₁, h₂]; linarith
  nlinarith [norm_nonneg (e₁ - e₂)]

/-- `|a + b| ≤ β` for a good unit edge: `(q − p)·u_p + (p − q)·u_q = (q − p)·(u_p − u_q)`. -/
theorem good_sum_le {F : DirField X} {p q : Pt} (hp : p ∈ Sset X) (hq : q ∈ Sset X)
    (h1 : dist p q = 1) (hg : ang (F.u p) (F.u q) ≤ beta) :
    inner ℝ (q - p) (F.u p) + inner ℝ (p - q) (F.u q) ≤ beta := by
  have e : inner ℝ (q - p) (F.u p) + inner ℝ (p - q) (F.u q) =
      inner ℝ (q - p) (F.u p - F.u q) := by
    rw [inner_sub_right, ← neg_sub q p, inner_neg_left]; ring
  rw [e]
  refine (real_inner_le_norm _ _).trans ?_
  rw [← dist_eq_norm, dist_comm, h1, one_mul]
  exact (norm_sub_le_angR (F.norm_u hp) (F.norm_u hq)).trans hg

/-- Positive elevation from `D`-ends and from normal points. -/
theorem other_pos (hX : Normal X) (F : DirField X) {p q : Pt} (hp : p ∈ Sset X) (hpD : p ∉ Dset X)
    (hq : q ∈ Sset X) (h1 : dist p q = 1) : 0 < inner ℝ (p - q) (F.u q) := by
  have hT := two_of_pos hX.dist2_pos
  have hpos := hX.dist2_pos
  have hq1 : dist p q ^ 2 = 1 := by rw [h1]; norm_num
  by_cases hqD : q ∈ Dset X
  · refine lt_of_lt_of_le ?_ (exact_identity_a F hq hqD (Sset_sub hp))
    rw [hq1]; apply div_pos one_pos; linarith [hT.lt]
  · rcases exact_identity_b F hq hqD (Sset_sub hp) with h | h
    · refine lt_of_lt_of_le ?_ h; rw [hq1]; apply div_pos one_pos; linarith
    · exfalso; apply hpD
      refine mem_Dset_ofR (Sset_sub hp) (F.partner_mem q hq) ?_ h
      intro e; rw [e, dist_self] at h; linarith [hT.lt]

theorem tau_ge_neg_beta (hX : Normal X) : -beta ≤ tau X := by
  have hpos := hX.dist2_pos
  have hT := two_of_pos hpos
  have ht : 0 < tgap X := by unfold tgap; linarith [hT.lt]
  have hl := hX.large
  have : (1 - tgap X ^ 2) / (2 * dist2 X) ≤ beta := by
    rw [div_le_iff₀ (by linarith)]; unfold beta; nlinarith
  unfold tau; linarith

/-- The elevation window at `p` in Region I. -/
theorem regionI_window (hX : Normal X) (F : DirField X) (hτ : tau X ≤ √3 / 2 - 2 * beta)
    {p : Pt} (hp : p ∈ Sset X) :
    ∃ L U : ℝ, -1 < L ∧ U < 1 ∧ Real.arcsin U - Real.arcsin L < π / 3 ∧
      ∀ q ∈ Sset X, dist p q = 1 → ang (F.u p) (F.u q) ≤ beta →
        L ≤ inner ℝ (q - p) (F.u p) ∧ inner ℝ (q - p) (F.u p) ≤ U := by
  have hb : beta = 1 / 100 := rfl
  have h3 : √3 < 1.7321 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h3' : (1.732 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hpos := hX.dist2_pos
  have hT := two_of_pos hpos
  have hτβ := tau_ge_neg_beta hX
  have hc4 := c4_window
  by_cases hpD : p ∈ Dset X
  · refine ⟨0, √3 / 2 - beta, by norm_num, by rw [hb]; linarith, ?_, ?_⟩
    · rw [Real.arcsin_zero, sub_zero]
      have := (Real.arcsin_lt_iff_lt_sin (x := √3 / 2 - beta) (y := π / 3)
        ⟨by rw [hb]; linarith, by rw [hb]; linarith⟩
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩).2
      rw [Real.sin_pi_div_three] at this
      exact this (by rw [hb]; linarith)
    · intro q hq h1 hg
      have ha : 0 < inner ℝ (q - p) (F.u p) := by
        refine lt_of_lt_of_le ?_ (exact_identity_a F hp hpD (Sset_sub hq))
        rw [dist_comm, h1]; apply div_pos (by norm_num); linarith [hT.lt]
      have hs := good_sum_le hp hq h1 hg
      refine ⟨ha.le, ?_⟩
      by_cases hqD : q ∈ Dset X
      · have hb' : 0 < inner ℝ (p - q) (F.u q) := by
          refine lt_of_lt_of_le ?_ (exact_identity_a F hq hqD (Sset_sub hp))
          rw [h1]; apply div_pos (by norm_num); linarith [hT.lt]
        rw [hb] at hs ⊢; linarith
      · rcases exact_identity_b F hq hqD (Sset_sub hp) with h | h
        · have : 0 < inner ℝ (p - q) (F.u q) := by
            refine lt_of_lt_of_le ?_ h; rw [h1]; apply div_pos (by norm_num); linarith
          rw [hb] at hs ⊢; linarith
        · have := exact_identity_c F hq hqD h h1
          linarith
  · refine ⟨min (-tau X) 0, beta, ?_, by rw [hb]; norm_num, ?_, ?_⟩
    · rw [lt_min_iff]; constructor
      · rw [hb] at hτ; linarith
      · norm_num
    · rcases le_or_gt 0 (tau X) with h0 | h0
      · rw [min_eq_left (by linarith), Real.arcsin_neg]
        have := Real.monotone_arcsin hτ; linarith
      · rw [min_eq_right (by linarith), Real.arcsin_zero]
        have := Real.arcsin_nonneg.2 (show 0 ≤ √3 / 2 - 2 * beta by rw [hb]; linarith)
        linarith
    · intro q hq h1 hg
      rcases exact_identity_b F hp hpD (Sset_sub hq) with h | h
      · have ha : 0 < inner ℝ (q - p) (F.u p) := by
          refine lt_of_lt_of_le ?_ h; rw [dist_comm, h1]; apply div_pos (by norm_num); linarith
        have hs := good_sum_le hp hq h1 hg
        have hb' := other_pos hX F hp hpD hq h1
        exact ⟨(min_le_right _ _).trans ha.le, by linarith⟩
      · have := exact_identity_c F hp hpD h (by rw [dist_comm]; exact h1)
        rw [this]; exact ⟨min_le_left _ _, by linarith⟩

/-- **Region I degree bound**: every `p ∈ S` has at most two good `δ`-edges (one per side of
`ℝu_p`; none on the line).

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `exact_identity_a`, `exact_identity_b`, `exact_identity_c`, `c4_window`,
`DirField.norm_u`. Difficulty M–L. -/
theorem regionI_deg_le (hX : Normal X) (F : DirField X) (hτ : tau X ≤ √3 / 2 - 2 * beta)
    {p : Pt} (hp : p ∈ Sset X) : ((good X F).filter (fun z => p ∈ z)).card ≤ 2 := by
  obtain ⟨L, U, hL, hU, hw, hwin⟩ := regionI_window hX F hτ hp
  have hu := F.norm_u hp
  set G := (good X F).filter (fun z => p ∈ z)
  let P : ℝ → Sym2 Pt → Prop := fun σ z => ∃ q, z = s(p, q) ∧ q ∈ Sset X ∧ dist p q = 1 ∧
    ang (F.u p) (F.u q) ≤ beta ∧ 0 < σ * det2 (F.u p) (q - p)
  have hsplit : G ⊆ G.filter (P 1) ∪ G.filter (P (-1)) := by
    intro z hz
    obtain ⟨hz', hpz⟩ := mem_filter.1 hz
    obtain ⟨hze, hg⟩ := mem_filter.1 hz'
    obtain ⟨hnd, hS⟩ := mem_edges hze
    have hd : pairDist z = minDist X := (mem_filter.1 hze).2
    set q := Sym2.Mem.other hpz
    have hzq : z = s(p, q) := (Sym2.other_spec hpz).symm
    have hq : q ∈ Sset X := hS q (by rw [hzq]; exact Sym2.mem_mk_right _ _)
    have h1 : dist p q = 1 := by
      rw [← hX.minDist_eq, ← hd, hzq]; rfl
    have hgq : ang (F.u p) (F.u q) ≤ beta := hg p q hzq
    obtain ⟨ha, hb⟩ := hwin q hq h1 hgq
    have hn := inner_sq_add_det_sq (e := q - p) hu
    rw [← dist_eq_norm, dist_comm, h1] at hn
    have hdet : det2 (F.u p) (q - p) ≠ 0 := by
      intro h0; rw [h0] at hn
      nlinarith
    rcases hdet.lt_or_gt with h | h
    · exact mem_union.2 (Or.inr (mem_filter.2 ⟨hz, q, hzq, hq, h1, hgq, by linarith⟩))
    · exact mem_union.2 (Or.inl (mem_filter.2 ⟨hz, q, hzq, hq, h1, hgq, by linarith⟩))
  have hside : ∀ σ, (G.filter (P σ)).card ≤ 1 := by
    intro σ
    refine card_le_one.2 fun z₁ hz₁ z₂ hz₂ => ?_
    obtain ⟨q₁, e₁, hq₁, d₁, g₁, s₁⟩ := (mem_filter.1 hz₁).2
    obtain ⟨q₂, e₂, hq₂, d₂, g₂, s₂⟩ := (mem_filter.1 hz₂).2
    rw [e₁, e₂]
    have n₁ : ‖q₁ - p‖ = 1 := by rw [← dist_eq_norm, dist_comm, d₁]
    have n₂ : ‖q₂ - p‖ = 1 := by rw [← dist_eq_norm, dist_comm, d₂]
    have hc := same_side_close hu n₁ n₂ s₁ s₂ (hwin q₁ hq₁ d₁ g₁) (hwin q₂ hq₂ d₂ g₂) hw
    rw [sub_sub_sub_cancel_right, ← dist_eq_norm] at hc
    rw [eq_of_dist_lt_one hX.minDist_eq (Sset_sub hq₁) (Sset_sub hq₂) hc]
  calc G.card ≤ (G.filter (P 1) ∪ G.filter (P (-1))).card := card_le_card hsplit
    _ ≤ (G.filter (P 1)).card + (G.filter (P (-1))).card := card_union_le _ _
    _ ≤ 2 := by linarith [hside 1, hside (-1)]

/-- Region I: `#good ≤ |S|`.

TODO: none (handshake).
Acceptance: no `sorry` (inherits).
Depends on: `regionI_deg_le`, `two_mul_card_le_of_deg_le`, `mem_edges`. -/
theorem regionI_card_good (hX : Normal X) (F : DirField X) (hτ : tau X ≤ √3 / 2 - 2 * beta) :
    (good X F).card ≤ (Sset X).card := by
  have h := two_mul_card_le_of_deg_le (V := Sset X) (E := good X F) (k := 2)
    (fun z hz => mem_edges (mem_filter.1 hz).1) (fun p hp => regionI_deg_le hX F hτ hp)
  omega

/-- **Region I** (§6): `e(S) ≤ |S| + C`.

TODO: none (wiring).
Acceptance: no `sorry` (inherits).
Depends on: `card_good_add_bad`, `regionI_card_good`, `card_bad_le`. -/
theorem regionI (hX : Normal X) (F : DirField X) (hτ : tau X ≤ √3 / 2 - 2 * beta) :
    (eS X : ℝ) ≤ (Sset X).card + (cBad + 100) := by
  have h1 := card_good_add_bad F
  have h2 : ((good X F).card : ℝ) ≤ (Sset X).card := by exact_mod_cast regionI_card_good hX F hτ
  have h3 := card_bad_le hX F
  have : (eS X : ℝ) = (good X F).card + (bad X F).card := by exact_mod_cast h1.symm
  linarith

/-! ## §7 common: `τ > √3/2 − 2β` -/

/-- **[C5, C6]** `τ > √3/2 − 2β ⇒ τ > 2β`.

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem two_beta_lt_of {τ : ℝ} (h : √3 / 2 - 2 * beta < τ) : 2 * beta < τ := by
  have : (1.7 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  rw [beta] at *; linarith

/-- `good ≤ goodPure + mixedT`.

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem card_good_le_pure_add_mixed (F : DirField X) :
    (good X F).card ≤ (goodPure X F).card + (mixedT X F).card := by
  rw [goodPure]; exact card_le_card_sdiff_add_card

/-! ## §7.1 Mixed T-edges (Region II only) -/

/-- **[C5]** In Region II, `t − arcsin β ≥ 0.886`.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `tau_sub_tgap`. Difficulty M. -/
theorem c5_tgap (hX : Normal X) (hτ : √3 / 2 + 3 * beta ≤ tau X) :
    0.886 ≤ tgap X - Real.arcsin beta := by
  have hb : beta = 1 / 100 := rfl
  have h3' : (1.73205 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hpos := hX.dist2_pos
  have ht : √3 / 2 + 3 * beta ≤ tgap X := by
    by_cases h1 : tgap X ≤ 1
    · have e := tau_sub_tgap X
      have : (tgap X ^ 2 - 1) / (2 * dist2 X) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg _ (by linarith)
        have : 0 ≤ tgap X := by
          have := (two_of_pos hpos).lt; unfold tgap; linarith
        nlinarith
      linarith
    · have h3 : √3 < 1.7321 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
      rw [hb]; linarith
  have hy : Real.arcsin beta < 0.01002 := by
    rw [Real.arcsin_lt_iff_lt_sin ⟨by rw [hb]; norm_num, by rw [hb]; norm_num⟩
      ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩]
    have := Real.sin_gt_sub_cube (x := 0.01002) (by norm_num)
    rw [hb]; norm_num at this ⊢; linarith
  rw [hb] at ht; linarith

/-- **[C5]** `2π·10/0.886 < 71`.

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem c5_mixed : 2 * π * 10 / 0.886 < 71 := by
  have hp := Real.pi_lt_d4
  rw [div_lt_iff₀ (by norm_num)]; linarith

/-- `arcsin β < π/3`. -/
theorem arcsin_beta_lt : Real.arcsin beta < π / 3 := by
  have h3 : (1.7 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  rw [Real.arcsin_lt_iff_lt_sin ⟨by unfold beta; norm_num, by unfold beta; norm_num⟩
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, Real.sin_pi_div_three]
  unfold beta; linarith

/-- **Grid packing**: `1`-separated points within distance `2` of `x` number at most `81`
(cells of side `1/2`). -/
theorem card_sep_le_81 {P : Finset Pt} (hP : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → 1 ≤ dist a b) (x : Pt)
    (hx : ∀ a ∈ P, dist a x ≤ 2) : P.card ≤ 81 := by
  let f : Pt → ℤ × ℤ := fun a => (⌊2 * (a 0 - x 0)⌋, ⌊2 * (a 1 - x 1)⌋)
  have hbox : ∀ a ∈ P, f a ∈ (Icc (-4 : ℤ) 4) ×ˢ (Icc (-4 : ℤ) 4) := by
    intro a ha
    have hd := hx a ha
    have hsq := dist_sq_pt a x
    have h4 : dist a x ^ 2 ≤ 4 := by nlinarith [dist_nonneg (x := a) (y := x)]
    have b0 : |a 0 - x 0| ≤ 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (a 1 - x 1)]
    have b1 : |a 1 - x 1| ≤ 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (a 0 - x 0)]
    rw [abs_le] at b0 b1
    simp only [f, mem_product, mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [Int.le_floor]; push_cast; linarith
    · rw [Int.floor_le_iff]; push_cast; linarith
    · rw [Int.le_floor]; push_cast; linarith
    · rw [Int.floor_le_iff]; push_cast; linarith
  have := card_le_card_of_injOn f hbox (fun a ha b hb e => by
    by_contra hab
    have h1 := hP a ha b hb hab
    simp only [f, Prod.mk.injEq] at e
    have c0 := Int.floor_le (2 * (a 0 - x 0))
    have c1 := Int.lt_floor_add_one (2 * (a 0 - x 0))
    have c2 := Int.floor_le (2 * (b 0 - x 0))
    have c3 := Int.lt_floor_add_one (2 * (b 0 - x 0))
    have c4 := Int.floor_le (2 * (a 1 - x 1))
    have c5 := Int.lt_floor_add_one (2 * (a 1 - x 1))
    have c6 := Int.floor_le (2 * (b 1 - x 1))
    have c7 := Int.lt_floor_add_one (2 * (b 1 - x 1))
    rw [e.1] at c0 c1; rw [e.2] at c4 c5
    have d0 : |a 0 - b 0| < 1 / 2 := by rw [abs_lt]; constructor <;> linarith
    have d1 : |a 1 - b 1| < 1 / 2 := by rw [abs_lt]; constructor <;> linarith
    have hsq := dist_sq_pt a b
    have : dist a b ^ 2 < 1 := by
      rw [hsq]
      have := sq_abs (a 0 - b 0); have := sq_abs (a 1 - b 1)
      nlinarith [abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 1)]
    nlinarith [dist_nonneg (x := a) (y := b)])
  simpa using this

/-- Data of a mixed T-edge. -/
theorem mixedT_data {F : DirField X} {e : Sym2 Pt} (he : e ∈ mixedT X F) (h1 : minDist X = 1) :
    ∃ v w, e = s(v, w) ∧ v ∈ Sset X ∧ v ∉ Dset X ∧ w ∈ Sset X ∧ w ∈ Dset X ∧ dist v w = 1 ∧
      IsTEdge F v w ∧ ang (F.u v) (F.u w) ≤ beta := by
  obtain ⟨hT, v, w, rfl, hvD, hwD⟩ := mem_filter.1 he
  obtain ⟨hg, hTall⟩ := mem_filter.1 hT
  obtain ⟨hee, hgood⟩ := mem_filter.1 hg
  obtain ⟨-, hS⟩ := mem_edges hee
  have hd : pairDist s(v, w) = minDist X := (mem_filter.1 hee).2
  exact ⟨v, w, rfl, hS v (Sym2.mem_mk_left _ _), hvD, hS w (Sym2.mem_mk_right _ _), hwD,
    by rw [← h1, ← hd]; rfl, hTall v w rfl, hgood v w rfl⟩

/-- At most one T-neighbour on each side (elevation window `(0, β)`). -/
theorem tnbr_unique (hX : Normal X) {F : DirField X} {v w₁ w₂ : Pt} (hv : v ∈ Sset X)
    (hw₁ : w₁ ∈ Sset X) (hw₂ : w₂ ∈ Sset X) (d₁ : dist v w₁ = 1) (d₂ : dist v w₂ = 1)
    (t₁ : IsTEdge F v w₁) (t₂ : IsTEdge F v w₂) {σ : ℝ}
    (s₁ : 0 < σ * det2 (F.u v) (w₁ - v)) (s₂ : 0 < σ * det2 (F.u v) (w₂ - v)) : w₁ = w₂ := by
  have n₁ : ‖w₁ - v‖ = 1 := by rw [← dist_eq_norm, dist_comm, d₁]
  have n₂ : ‖w₂ - v‖ = 1 := by rw [← dist_eq_norm, dist_comm, d₂]
  have hc := same_side_close (F.norm_u hv) n₁ n₂ s₁ s₂ (L := 0) (U := beta)
    ⟨t₁.1.le, t₁.2.1.le⟩ ⟨t₂.1.le, t₂.2.1.le⟩
    (by rw [Real.arcsin_zero, sub_zero]; exact arcsin_beta_lt)
  rw [sub_sub_sub_cancel_right, ← dist_eq_norm] at hc
  exact eq_of_dist_lt_one hX.minDist_eq (Sset_sub hw₁) (Sset_sub hw₂) hc

/-! ### Directions, support points and the arc measure (for Lemma 7.1) -/

/-- An arc of directions of length `L ≤ 2π` (mod `2π`) has measure `≥ L` in `[0, 2π)`. -/
theorem vol_arc_ge (P : ℝ → Prop) {a L : ℝ} (_hL0 : 0 ≤ L) (hL : L ≤ 2 * π)
    (hP : ∀ θ : ℝ, ∀ k : ℤ, θ + k * (2 * π) ∈ Set.Ioo a (a + L) → P θ) :
    ENNReal.ofReal L ≤ MeasureTheory.volume {θ : ℝ | θ ∈ Set.Ico 0 (2 * π) ∧ P θ} := by
  have hp : (0 : ℝ) < 2 * π := by positivity
  set a' := toIcoMod hp 0 a
  set n := toIcoDiv hp 0 a
  have ha : a' + n • (2 * π) = a := toIcoMod_add_toIcoDiv_zsmul hp 0 a
  rw [zsmul_eq_mul] at ha
  have hm : a' ∈ Set.Ico 0 (0 + 2 * π) := toIcoMod_mem_Ico hp 0 a
  rw [zero_add] at hm
  by_cases hc : a' + L ≤ 2 * π
  · calc ENNReal.ofReal L = MeasureTheory.volume (Set.Ioo a' (a' + L)) := by
          rw [Real.volume_Ioo]; congr 1; ring
      _ ≤ _ := by
          apply MeasureTheory.measure_mono
          intro θ hθ
          refine ⟨⟨by linarith [hθ.1, hm.1], by linarith [hθ.2]⟩, hP θ n ?_⟩
          constructor <;> linarith [hθ.1, hθ.2]
  · push Not at hc
    have hd : Disjoint (Set.Ioo a' (2 * π)) (Set.Ioo 0 (a' + L - 2 * π)) := by
      rw [Set.disjoint_left]; intro θ h1 h2; linarith [h1.1, h2.2, hm.2]
    calc ENNReal.ofReal L
        = MeasureTheory.volume (Set.Ioo a' (2 * π)) +
            MeasureTheory.volume (Set.Ioo 0 (a' + L - 2 * π)) := by
          rw [Real.volume_Ioo, Real.volume_Ioo, ← ENNReal.ofReal_add (by linarith [hm.2])
            (by linarith)]
          congr 1; ring
      _ = MeasureTheory.volume (Set.Ioo a' (2 * π) ∪ Set.Ioo 0 (a' + L - 2 * π)) :=
          (MeasureTheory.measure_union hd measurableSet_Ioo).symm
      _ ≤ _ := by
          apply MeasureTheory.measure_mono
          intro θ hθ
          rcases hθ with hθ | hθ
          · refine ⟨⟨by linarith [hθ.1, hm.1], hθ.2⟩, hP θ n ?_⟩
            constructor <;> linarith [hθ.1, hθ.2, hm.1, hm.2]
          · refine ⟨⟨hθ.1.le, by linarith [hθ.2, hm.2]⟩, hP θ (n + 1) ?_⟩
            push_cast
            have e : ((n : ℝ) + 1) * (2 * π) = n * (2 * π) + 2 * π := by ring
            rw [e]
            constructor <;> linarith [hθ.1, hθ.2, hm.1, hm.2]

@[simp] theorem dirVec_apply0 (θ : ℝ) : dirVec θ 0 = Real.cos θ := by simp [dirVec]
@[simp] theorem dirVec_apply1 (θ : ℝ) : dirVec θ 1 = Real.sin θ := by simp [dirVec]

theorem dirVec_addR (θ ψ : ℝ) :
    dirVec (θ + ψ) = Real.cos ψ • dirVec θ + Real.sin ψ • perp (dirVec θ) := by
  rw [pt_ext_iff]; simp [Real.cos_add, Real.sin_add]; constructor <;> ring

theorem dirVec_add_int (θ : ℝ) (k : ℤ) : dirVec (θ + k * (2 * π)) = dirVec θ := by
  rw [pt_ext_iff]; simp [Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

theorem perp_neg (a : Pt) : perp (-a) = - perp a := by rw [pt_ext_iff]; simp

/-- Every unit vector is `dirVec θ` for some `θ ∈ [0, 2π)`. -/
theorem exists_angle {n : Pt} (hn : ‖n‖ = 1) : ∃ θ ∈ Set.Ico 0 (2 * π), dirVec θ = n := by
  have h := unit_sq hn
  have hb : -1 ≤ n 0 ∧ n 0 ≤ 1 := by constructor <;> nlinarith [sq_nonneg (n 1)]
  have hπ := Real.pi_pos
  rcases le_or_gt 0 (n 1) with h1 | h1
  · refine ⟨Real.arccos (n 0), ⟨Real.arccos_nonneg _, ?_⟩, ?_⟩
    · linarith [Real.arccos_le_pi (n 0)]
    · rw [pt_ext_iff]; simp only [dirVec_apply0, dirVec_apply1]
      refine ⟨Real.cos_arccos hb.1 hb.2, ?_⟩
      rw [Real.sin_arccos, Real.sqrt_eq_iff_mul_self_eq (by nlinarith) h1]; nlinarith
  · have hlt : n 0 < 1 := by nlinarith
    refine ⟨2 * π - Real.arccos (n 0), ⟨by linarith [Real.arccos_le_pi (n 0)], ?_⟩, ?_⟩
    · linarith [Real.arccos_pos.2 hlt]
    · rw [pt_ext_iff]; simp only [dirVec_apply0, dirVec_apply1]
      rw [Real.cos_two_pi_sub, Real.sin_two_pi_sub, Real.cos_arccos hb.1 hb.2, Real.sin_arccos]
      refine ⟨rfl, ?_⟩
      rw [neg_eq_iff_eq_neg, Real.sqrt_eq_iff_mul_self_eq (by nlinarith) (by linarith)]; nlinarith

theorem KBall_isClosed (X : Finset Pt) : IsClosed (KBall X) :=
  isClosed_biInter fun _ _ => Metric.isClosed_closedBall

/-- A maximiser of a unit linear functional over `K` is a boundary point. -/
theorem mem_frontier_of_max {y ν : Pt} (hy : y ∈ KBall X) (hν : ‖ν‖ = 1)
    (hmax : ∀ y' ∈ KBall X, inner ℝ y' ν ≤ inner ℝ y ν) : y ∈ frontier (KBall X) := by
  rw [(KBall_isClosed X).frontier_eq]
  refine ⟨hy, fun hint => ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
  have hm : y + (ε / 2) • ν ∈ KBall X := hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hν, mul_one,
      Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith)
  have := hmax _ hm
  rw [inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq, hν] at this
  simp at this; linarith

/-- Wedge algebra: `α ≥ 0`, `α² + b² = 1`, `−α cos φ + b sin φ ≥ 0` ⇒ `b ≥ cos φ`. -/
theorem cos_le_of_wedge {α b c s : ℝ} (hc : 0 < c) (hs : 0 < s) (hcs : c ^ 2 + s ^ 2 = 1)
    (hα : 0 ≤ α) (hαb : α ^ 2 + b ^ 2 = 1) (h : 0 ≤ -(α * c) + b * s) : c ≤ b := by
  by_contra hlt
  push Not at hlt
  have hb0 : 0 ≤ b := by
    by_contra hb; push Not at hb
    have : b * s < 0 := mul_neg_of_neg_of_pos hb hs
    nlinarith [mul_nonneg hα hc.le]
  have hbc2 : b ^ 2 < c ^ 2 := by nlinarith
  have hαs : s < α := by nlinarith
  have h1 : s * c < α * c := mul_lt_mul_of_pos_right hαs hc
  have h2 : b * s < c * s := mul_lt_mul_of_pos_right hlt hs
  nlinarith

theorem norm_rot {u e₀ : Pt} (hu : ‖u‖ = 1) (he₀ : ‖e₀‖ = 1) (hue : inner ℝ u e₀ = 0) (φ : ℝ) :
    ‖Real.cos φ • (-u) + Real.sin φ • e₀‖ = 1 := by
  have hcs := Real.cos_sq_add_sin_sq φ
  have : ‖Real.cos φ • (-u) + Real.sin φ • e₀‖ ^ 2 = 1 := by
    rw [@norm_add_sq_real, norm_smul, norm_smul, norm_neg, hu, he₀, inner_smul_left,
      inner_smul_right, inner_neg_left, hue]
    simp only [Real.norm_eq_abs, conj_trivial, mul_one, mul_pow, sq_abs]; linarith
  nlinarith [norm_nonneg (Real.cos φ • (-u) + Real.sin φ • e₀)]

/-- The key step of Lemma 7.1: a support point `y` of `K` in a direction `ν` obtained by rotating
the outward normal `−u` at `v` by `φ` towards `e₀` stays within distance `2` of `v`, provided
`φ + |e₀ − (z − v)| < t` for some `z ∈ D`. -/
theorem support_point_close {v z y u e₀ : Pt} {φ : ℝ} (hzD : z ∈ Dset X) (hvK : v ∈ KBall X)
    (hyK : y ∈ KBall X) (hu : ‖u‖ = 1) (he₀ : ‖e₀‖ = 1)
    (hframe : ∀ x : Pt, inner ℝ x u ^ 2 + inner ℝ x e₀ ^ 2 = ‖x‖ ^ 2)
    (hn₀ : -u ∈ normalCone (KBall X) v)
    (hmax : inner ℝ v (Real.cos φ • (-u) + Real.sin φ • e₀) ≤
      inner ℝ y (Real.cos φ • (-u) + Real.sin φ • e₀))
    (hφ0 : 0 < φ) (hφ1 : φ < 1) (hφt : φ + ‖e₀ - (z - v)‖ < tgap X) : dist y v ≤ 2 := by
  by_contra hfar
  push Not at hfar
  have hπ := Real.pi_gt_three
  have hcos : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hsin : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ0 (by linarith)
  have hcs := Real.cos_sq_add_sin_sq φ
  set w := y - v with hw
  set r := ‖w‖ with hr_def
  have hr : 2 < r := by rw [hr_def, hw, ← dist_eq_norm]; exact hfar
  have hr0 : 0 < r := by linarith
  set wh := r⁻¹ • w with hwh_def
  have hwh : ‖wh‖ = 1 := by
    rw [hwh_def, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr0), inv_mul_cancel₀ hr0.ne']
  have hq : v + r⁻¹ • w ∈ KBall X := (KBall_convex X).add_smul_sub_mem hvK hyK
    ⟨inv_nonneg.2 hr0.le, inv_le_one_of_one_le₀ (by linarith)⟩
  have htq := ball_polygon_c hzD hq
  have hαb : inner ℝ wh u ^ 2 + inner ℝ wh e₀ ^ 2 = 1 := by rw [hframe, hwh, one_pow]
  have hα : 0 ≤ inner ℝ wh u := by
    have h1 := hn₀ y hyK
    rw [inner_neg_right] at h1
    have h2 : 0 ≤ inner ℝ w u := by rw [hw]; linarith
    rw [hwh_def, inner_smul_left]; simp only [conj_trivial]; positivity
  have hwν : 0 ≤ -(inner ℝ wh u * Real.cos φ) + inner ℝ wh e₀ * Real.sin φ := by
    have h1 : 0 ≤ inner ℝ w (Real.cos φ • (-u) + Real.sin φ • e₀) := by
      rw [hw, inner_sub_left]; linarith
    have h2 : 0 ≤ inner ℝ wh (Real.cos φ • (-u) + Real.sin φ • e₀) := by
      rw [hwh_def, inner_smul_left]; simp only [conj_trivial]; positivity
    rw [inner_add_right, inner_smul_right, inner_smul_right, inner_neg_right] at h2
    linarith
  have hbc := cos_le_of_wedge hcos hsin hcs hα hαb hwν
  have hwe : ‖wh - e₀‖ ≤ φ := by
    have h2 : ‖wh - e₀‖ ^ 2 = 2 - 2 * inner ℝ wh e₀ := by
      rw [@norm_sub_sq_real, hwh, he₀]; ring
    have h3 := Real.one_sub_sq_div_two_le_cos (x := φ)
    have : ‖wh - e₀‖ ^ 2 ≤ φ ^ 2 := by rw [h2]; linarith
    exact (sq_le_sq₀ (norm_nonneg _) hφ0.le).1 this
  have hdz : dist z (v + r⁻¹ • w) = ‖(wh - e₀) + (e₀ - (z - v))‖ := by
    rw [dist_eq_norm, ← norm_neg]; congr 1; rw [hwh_def]; abel
  have := norm_add_le (wh - e₀) (e₀ - (z - v))
  linarith

/-- **Lemma 7.1** (path-free form): for a T-edge `vz` with `v ∈ S ∖ D`, `z ∈ S ∩ D`, the boundary
points of `K` within distance `2` of `v` carry turning `≥ t − arcsin β`.

**Statement changed** (was: a `1`-Lipschitz path `γ` with `γ 0 = v`, `γ '' [0,2] ⊆ ∂K` and turning
`≥ t − arcsin β`).  The path form needs an arc-length parametrisation of `∂K`; the only property
used downstream (`card_mixedT_le`) is that the set lies in `∂K` within distance `2` of `v`.
Proof (support points instead of tangents): for every direction `ν` obtained by rotating the
outward normal `−u_v` by `φ ∈ (0, t − arcsin β)` towards `z`'s side, a support point `y` of `K`
in direction `ν` satisfies `|y − v| < 1` — otherwise the point `q ∈ [v, y]` at distance `1` from
`v` has direction within `φ` of the tangent `e₀`, so `|q − z| ≤ φ + arcsin β < t ≤ dist(z, K)`.

TODO: none.
Acceptance: no `sorry`.
Depends on: `ball_polygon_a`, `ball_polygon_c`, `vol_arc_ge`, support points of `K`. -/
theorem lemma71 (hX : Normal X) (F : DirField X) (hτ : √3 / 2 + 3 * beta ≤ tau X) {v z : Pt}
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

/-- **Mixed T-edges** `≤ 1200` in Region II.

**Statement changed** (was `≤ 71`): the paper's `71` uses the arc-length multiplicity `M ≤ 10`
(points of `S ∖ D` are `1`-separated in arc length along `∂K`), which needs an arc-length
parametrisation of `∂K` that `lemma71`'s statement does not provide.  From `lemma71` as stated,
the arc from `v` only gives `|x − v| ≤ 2` for `x` on it, and a grid packing gives
multiplicity `≤ 81` K-ends per point, hence `#mixed ≤ 2 · 2π·81/0.886 < 1200`.  The constant is
absorbed in `regionII_eS_le` (unchanged statement) using the explicit bad-edge constants.

TODO: none (inherits `lemma71`, `turning_sum_le_closure`).
Acceptance: no `sorry` (inherits).
Depends on: `lemma71`, `turning_sum_le_closure`, `card_sep_le_81`, `tnbr_unique`, `c5_tgap`. -/
theorem card_mixedT_le (hX : Normal X) (F : DirField X) (hτ : √3 / 2 + 3 * beta ≤ tau X) :
    ((mixedT X F).card : ℝ) ≤ 1200 := by
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
    exact ⟨lemma71 hX F hτ hv hvD hw hwD hvw hT, hv⟩
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
  have hlow : ∑ v ∈ A, (0.886 : ℝ) ≤ ∑ v ∈ A, turning (KBall X) (Γ v) :=
    sum_le_sum fun v hv => (c5_tgap hX hτ).trans (hΓ v hv).2.1
  rw [sum_const, nsmul_eq_mul] at hlow
  have hπ := Real.pi_lt_d4
  have hAc : (A.card : ℝ) * 0.886 ≤ 2 * π * 81 := by push_cast at hsum; linarith
  have hA' : ((mixedT X F).card : ℝ) ≤ 2 * A.card := by exact_mod_cast hA
  nlinarith

/-! ## §7.2 Region II -/

/-- `τ > 1` ⇒ no rungs (3.2(c)).

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `tau_le_one_of_exception`. Difficulty S. -/
theorem rungs_eq_empty (F : DirField X) (hτ : 1 < tau X) : rungs X F = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro e he
  obtain ⟨v, w, -, hr⟩ := (mem_filter.1 he).2
  have := tau_le_one_of_exception F hr.1 hr.2.1 hr.2.2.2.2.2
    (by rw [dist_comm]; exact hr.2.2.2.2.1)
  linarith

/-- **Region II-high** (`τ > 1`): `e(S) ≤ |S| + C`.

TODO: none (wiring).
Acceptance: no `sorry` (inherits).
Depends on: `card_good_add_bad`, `good_subset_T_union_rungs`, `rungs_eq_empty`,
`card_tEdges_le`, `card_bad_le`. -/
theorem regionII_high (hX : Normal X) (F : DirField X) (hτ : 1 < tau X) :
    (eS X : ℝ) ≤ (Sset X).card + (cBad + 100) := by
  have hsub := good_subset_T_union_rungs hX F (by unfold beta; linarith)
  rw [rungs_eq_empty F hτ, union_empty] at hsub
  have h2 : ((good X F).card : ℝ) ≤ (Sset X).card :=
    by exact_mod_cast (card_le_card hsub).trans (card_tEdges_le hX F)
  have h3 := card_bad_le hX F
  have : (eS X : ℝ) = (good X F).card + (bad X F).card := by
    exact_mod_cast (card_good_add_bad F).symm
  linarith

/-- **[C5]** `2s + 6β < 1` for `√3/2 + 3β ≤ τ ≤ 1` (covers R1-at-z `2s + 2β`, R2
`2s + 2β + arcsin β`, R2-sym `2s + 4β + arcsin β`).

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem c5_sOff {τ : ℝ} (h1 : √3 / 2 + 3 * beta ≤ τ) (h2 : τ ≤ 1) :
    2 * √(1 - τ ^ 2) + 6 * beta < 1 := by
  have h3 : (1.732 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  rw [beta] at *
  have hτ : (0.896 : ℝ) ≤ τ := by linarith
  have hs : √(1 - τ ^ 2) < 0.47 := by
    rw [Real.sqrt_lt' (by norm_num)]; nlinarith
  linarith

/-- **[C5]** `cos(β/2) > √3/2 + 3β` (rhombi only near resonance).

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem c5_rhombus : √3 / 2 + 3 * beta < Real.cos (beta / 2) := by
  have h3 : √3 < 1.7321 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hc := Real.one_sub_sq_div_two_le_cos (x := beta / 2)
  rw [beta] at *
  norm_num at hc ⊢
  linarith

/-- **(R1) at `v`**: a K-vertex has at most one rung (in Region II).

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `rung_offset`, `c5_sOff`. Difficulty S–M. -/
theorem R1_v (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X ≤ 1) {v z₁ z₂ : Pt} (h₁ : IsRung F v z₁) (h₂ : IsRung F v z₂) : z₁ = z₂ := by
  obtain ⟨σ₁, hσ₁, e₁⟩ := rung_offset F h₁
  obtain ⟨σ₂, hσ₂, e₂⟩ := rung_offset F h₂
  have hu := F.norm_u h₁.1
  have hs := c5_sOff hτ₁ hτ₂
  have hs0 : 0 ≤ sOff X := Real.sqrt_nonneg _
  refine eq_of_dist_lt_one hX.minDist_eq h₁.memX.2 h₂.memX.2 ?_
  have e : z₁ - z₂ = (z₁ - v) - (z₂ - v) := by abel
  rw [dist_eq_norm, e, e₁, e₂]
  refine (norm_offset_sub hu hu hs0 hσ₁ hσ₂).trans_lt ?_
  simp only [sub_self, norm_zero, mul_zero, zero_add]
  unfold sOff; unfold beta at hs; linarith

/-- **(R1) at `z`**: a D-vertex has at most one good rung (`|v − v′| ≤ 2s + 2β < 1`).

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `rung_offset`, `c5_sOff`, rotation bound `|o(u) − o(u′)| ≤ ∠(u, u′)`.
Difficulty M. -/
theorem R1_z (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X ≤ 1) {v₁ v₂ z : Pt} (h₁ : IsRung F v₁ z) (h₂ : IsRung F v₂ z)
    (hg₁ : ang (F.u v₁) (F.u z) ≤ beta) (hg₂ : ang (F.u v₂) (F.u z) ≤ beta) : v₁ = v₂ := by
  obtain ⟨σ₁, hσ₁, e₁⟩ := rung_offset F h₁
  obtain ⟨σ₂, hσ₂, e₂⟩ := rung_offset F h₂
  have hu₁ := F.norm_u h₁.1
  have hu₂ := F.norm_u h₂.1
  have huz := F.norm_u h₁.2.2.1
  have hs := c5_sOff hτ₁ hτ₂
  have hs0 : 0 ≤ sOff X := Real.sqrt_nonneg _
  have hτ0 : |tau X| ≤ 1 := abs_tau_le_one hτ₁ hτ₂
  refine eq_of_dist_lt_one hX.minDist_eq h₁.memX.1 h₂.memX.1 ?_
  have e : v₁ - v₂ = (z - v₂) - (z - v₁) := by abel
  rw [dist_eq_norm, e, e₁, e₂]
  refine (norm_offset_sub hu₂ hu₁ hs0 hσ₂ hσ₁).trans_lt ?_
  have hd : ‖F.u v₂ - F.u v₁‖ ≤ 2 * beta := by
    have := norm_sub_le (F.u v₂ - F.u z) (F.u v₁ - F.u z)
    rw [sub_sub_sub_cancel_right] at this
    have a₁ := norm_sub_le_angR hu₁ huz
    have a₂ := norm_sub_le_angR hu₂ huz
    linarith
  have : |tau X| * ‖F.u v₂ - F.u v₁‖ ≤ 2 * beta :=
    (mul_le_of_le_one_left (norm_nonneg _) hτ0).trans hd
  have hb : (0 : ℝ) < beta := by unfold beta; norm_num
  unfold sOff; linarith


/-- Data of a right T-step `p → q`: unit step, elevation in `(0, β)`, on the right. -/
theorem IsSideT.step {F : DirField X} {p q : Pt} (h : IsSideT F (-1) p q) :
    ‖q - p‖ = 1 ∧ 0 < inner ℝ (q - p) (F.u p) ∧ inner ℝ (q - p) (F.u p) < beta ∧
      det2 (F.u p) (q - p) < 0 := by
  obtain ⟨-, -, h1, -, ⟨a, b, -, -⟩, hs⟩ := h
  refine ⟨by rw [← dist_eq_norm, dist_comm]; exact h1, a, b, by linarith⟩

/-- `|u_a − u_c| ≤ β₁ + β₂` from two angle bounds through `u_b`. -/
theorem norm_u_sub_leR {a b c : Pt} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    ‖a - c‖ ≤ ang a b + ang b c := by
  have := norm_sub_le (a - b) (c - b)
  rw [sub_sub_sub_cancel_right] at this
  have h1 := norm_sub_le_angR ha hb
  have h2 := norm_sub_le_angR hc hb
  rw [ang_comm c b] at h2
  linarith

/-- **(R2) proximity**: `(v₀, z₀)` a good rung, `v₁`/`z₁` the right pure T-neighbours of
`v₀`/`z₀`; if `v₁` has a good rung `(v₁, z′)` then `z′ = z₁` (`|z′ − z₁| ≤ 2s + 2β + arcsin β`).

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `rung_offset`, `c5_sOff`, T-step geometry. Difficulty M. -/
theorem R2 (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X) (hτ₂ : tau X ≤ 1)
    {v₀ z₀ v₁ z₁ z' : Pt} (hr₀ : IsRung F v₀ z₀) (hg₀ : ang (F.u v₀) (F.u z₀) ≤ beta)
    (hv : IsSideT F (-1) v₀ v₁) (hv₁ : v₁ ∉ Dset X) (hz : IsSideT F (-1) z₀ z₁)
    (hz₁ : z₁ ∈ Dset X) (hr : IsRung F v₁ z') (hg : ang (F.u v₁) (F.u z') ≤ beta) :
    z' = z₁ := by
  obtain ⟨σ₀, hσ₀, o₀⟩ := rung_offset F hr₀
  obtain ⟨σ₁, hσ₁, o₁⟩ := rung_offset F hr
  obtain ⟨n₁, a₁, a₁', c₁⟩ := hv.step
  obtain ⟨n₂, a₂, a₂', c₂⟩ := hz.step
  have huv₀ := F.norm_u hr₀.1
  have huz₀ := F.norm_u hr₀.2.2.1
  have huv₁ := F.norm_u hr.1
  have hs := c5_sOff hτ₁ hτ₂
  have hs0 : 0 ≤ sOff X := Real.sqrt_nonneg _
  have hτ0 := abs_tau_le_one hτ₁ hτ₂
  have hb : (0 : ℝ) < beta := by unfold beta; norm_num
  refine eq_of_dist_lt_one hX.minDist_eq hr.memX.2 (Sset_sub hz.2.1) ?_
  have e : z' - z₁ = ((v₁ - v₀) - (z₁ - z₀)) + ((z' - v₁) - (z₀ - v₀)) := by abel
  rw [dist_eq_norm, e, o₀, o₁]
  refine (norm_add_le _ _).trans_lt ?_
  have hE := norm_tstep_sub huv₀ huz₀ n₁ n₂ a₁ a₁' a₂ a₂' c₁ c₂
  have hO := norm_offset_sub huv₁ huv₀ hs0 hσ₁ hσ₀ (τ := tau X)
  have h1 : ‖F.u v₀ - F.u z₀‖ ≤ beta := (norm_sub_le_angR huv₀ huz₀).trans hg₀
  have h2 : ‖F.u v₁ - F.u v₀‖ ≤ beta := by
    rw [norm_sub_rev]; exact (norm_sub_le_angR huv₀ huv₁).trans hv.2.2.2.1
  have h3 : |tau X| * ‖F.u v₁ - F.u v₀‖ ≤ beta :=
    (mul_le_of_le_one_left (norm_nonneg _) hτ0).trans h2
  have hs' : 2 * sOff X + 6 * beta < 1 := hs
  linarith

/-- **(R2-sym) symmetric proximity**: same setting; if `z₁` has a good rung `(v′, z₁)` then
`v′ = v₁` (`|v′ − v₁| ≤ 2s + 4β + arcsin β ≤ 2s + 6β < 1`).

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `rung_offset`, `c5_sOff`, T-step geometry. Difficulty M. -/
theorem R2_sym (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X ≤ 1) {v₀ z₀ v₁ z₁ v' : Pt} (hr₀ : IsRung F v₀ z₀)
    (hg₀ : ang (F.u v₀) (F.u z₀) ≤ beta) (hv : IsSideT F (-1) v₀ v₁) (hv₁ : v₁ ∉ Dset X)
    (hz : IsSideT F (-1) z₀ z₁) (hz₁ : z₁ ∈ Dset X) (hr : IsRung F v' z₁)
    (hg : ang (F.u v') (F.u z₁) ≤ beta) : v' = v₁ := by
  obtain ⟨σ₀, hσ₀, o₀⟩ := rung_offset F hr₀
  obtain ⟨σ₁, hσ₁, o₁⟩ := rung_offset F hr
  obtain ⟨n₁, a₁, a₁', c₁⟩ := hv.step
  obtain ⟨n₂, a₂, a₂', c₂⟩ := hz.step
  have huv₀ := F.norm_u hr₀.1
  have huz₀ := F.norm_u hr₀.2.2.1
  have huv' := F.norm_u hr.1
  have huz₁ := F.norm_u hr.2.2.1
  have hs := c5_sOff hτ₁ hτ₂
  have hs0 : 0 ≤ sOff X := Real.sqrt_nonneg _
  have hτ0 := abs_tau_le_one hτ₁ hτ₂
  have hb : (0 : ℝ) < beta := by unfold beta; norm_num
  refine eq_of_dist_lt_one hX.minDist_eq hr.memX.1 (Sset_sub hv.2.1) ?_
  have e : v' - v₁ = ((z₁ - z₀) - (v₁ - v₀)) - ((z₁ - v') - (z₀ - v₀)) := by abel
  rw [dist_eq_norm, e, o₀, o₁]
  refine (norm_sub_le _ _).trans_lt ?_
  have hE := norm_tstep_sub huv₀ huz₀ n₁ n₂ a₁ a₁' a₂ a₂' c₁ c₂
  rw [norm_sub_rev] at hE
  have hO := norm_offset_sub huv' huv₀ hs0 hσ₁ hσ₀ (τ := tau X)
  have h1 : ‖F.u v₀ - F.u z₀‖ ≤ beta := (norm_sub_le_angR huv₀ huz₀).trans hg₀
  have h2 : ‖F.u v' - F.u v₀‖ ≤ 3 * beta := by
    have k1 := norm_u_sub_leR huv' huz₁ huz₀
    have k2 := norm_sub_le (F.u v' - F.u z₀) (F.u v₀ - F.u z₀)
    rw [sub_sub_sub_cancel_right] at k2
    have k3 : ang (F.u z₁) (F.u z₀) ≤ beta := by rw [ang_comm]; exact hz.2.2.2.1
    linarith
  have h3 : |tau X| * ‖F.u v' - F.u v₀‖ ≤ 3 * beta :=
    (mul_le_of_le_one_left (norm_nonneg _) hτ0).trans h2
  have hs' : 2 * sOff X + 6 * beta < 1 := hs
  linarith

/-- **(R3a) no three parallel rungs**: `u_v` solves `c·u = −τ`, which has two unit solutions,
and K-ends have distinct normals (Lemma 3.3).

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `exact_identity_c`, `u_ne`, `DirField.norm_u`. Difficulty M. -/
theorem R3_no_three_parallel (F : DirField X) {v₁ v₂ v₃ z₁ z₂ z₃ : Pt} (h₁ : IsRung F v₁ z₁)
    (h₂ : IsRung F v₂ z₂) (h₃ : IsRung F v₃ z₃) (e₁₂ : z₁ - v₁ = z₂ - v₂)
    (e₁₃ : z₁ - v₁ = z₃ - v₃) : v₁ = v₂ ∨ v₁ = v₃ ∨ v₂ = v₃ := by
  have hc := h₁.norm_c
  have key : ∀ {v z : Pt}, IsRung F v z → z - v = z₁ - v₁ →
      F.u v = (- tau X) • (z₁ - v₁) + det2 (z₁ - v₁) (F.u v) • perp (z₁ - v₁) ∧
      det2 (z₁ - v₁) (F.u v) ^ 2 = 1 - tau X ^ 2 := by
    intro v z h e
    have hi := h.inner_eq
    rw [e] at hi
    have hu := F.norm_u h.1
    have n := inner_sq_add_det_sq (e := F.u v) hc
    rw [real_inner_comm, hi, hu] at n
    refine ⟨?_, by linarith⟩
    conv_lhs => rw [decompR hc (F.u v)]
    rw [real_inner_comm, hi]
  obtain ⟨k₁, d₁⟩ := key h₁ rfl
  obtain ⟨k₂, d₂⟩ := key h₂ e₁₂.symm
  obtain ⟨k₃, d₃⟩ := key h₃ e₁₃.symm
  have ne : ∀ {a b : Pt}, a ∈ Sset X → a ∉ Dset X → b ∈ Sset X → b ∉ Dset X →
      F.u a = F.u b → a = b := by
    intro a b ha haD hb hbD e
    by_contra hab; exact u_ne F ha haD hb hbD hab e
  set c := z₁ - v₁
  have sq : ∀ x y : ℝ, x ^ 2 = y ^ 2 → x = y ∨ x = -y := fun x y h => by
    have : (x - y) * (x + y) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  rcases sq _ _ (d₁.trans d₂.symm) with e | e
  · left; exact ne h₁.1 h₁.2.1 h₂.1 h₂.2.1 (by rw [k₁, k₂, e])
  rcases sq _ _ (d₁.trans d₃.symm) with e' | e'
  · right; left; exact ne h₁.1 h₁.2.1 h₃.1 h₃.2.1 (by rw [k₁, k₃, e'])
  right; right
  exact ne h₂.1 h₂.2.1 h₃.1 h₃.2.1 (by rw [k₂, k₃]; congr 2; linarith)


/-- Planar core of (R3b): `x, y` two distinct common points of `C(0,1)` and `C(d,1)` ⇒
`x + y = d`. -/
theorem rhombus_real {x0 x1 y0 y1 d0 d1 : ℝ} (hx : x0 ^ 2 + x1 ^ 2 = 1) (hy : y0 ^ 2 + y1 ^ 2 = 1)
    (hxd : (d0 - x0) ^ 2 + (d1 - x1) ^ 2 = 1) (hyd : (d0 - y0) ^ 2 + (d1 - y1) ^ 2 = 1)
    (hxy : ¬ (x0 = y0 ∧ x1 = y1)) (hd : ¬ (d0 = 0 ∧ d1 = 0)) :
    x0 + y0 = d0 ∧ x1 + y1 = d1 := by
  set w0 := x0 - y0
  set w1 := x1 - y1
  set b0 := x0 + y0 - d0
  set b1 := x1 + y1 - d1
  have hwd : w0 * d0 + w1 * d1 = 0 := by
    simp only [w0, w1]; linear_combination (hyd - hxd - hy + hx) / 2
  have hwb : w0 * b0 + w1 * b1 = 0 := by
    simp only [w0, w1, b0, b1]; linear_combination hx - hy - (hyd - hxd - hy + hx) / 2
  have hbd : b0 * d0 + b1 * d1 = 0 := by
    simp only [b0, b1]; linear_combination (hx - hxd + hy - hyd) / 2
  have hw : 0 < w0 ^ 2 + w1 ^ 2 := by
    by_contra h; push Not at h
    apply hxy; constructor
    · have : w0 = 0 := by nlinarith [sq_nonneg w0, sq_nonneg w1]
      simp only [w0] at this; linarith
    · have : w1 = 0 := by nlinarith [sq_nonneg w0, sq_nonneg w1]
      simp only [w1] at this; linarith
  have hd' : 0 < d0 ^ 2 + d1 ^ 2 := by
    by_contra h; push Not at h
    apply hd; constructor <;> nlinarith [sq_nonneg d0, sq_nonneg d1]
  have hdet : (w0 * d1 - w1 * d0) ^ 2 = (w0 ^ 2 + w1 ^ 2) * (d0 ^ 2 + d1 ^ 2) := by
    linear_combination (-(w0 * d0 + w1 * d1)) * hwd
  have hdet0 : w0 * d1 - w1 * d0 ≠ 0 := by
    intro h; rw [h] at hdet; nlinarith [mul_pos hw hd']
  have e0 : (w0 * d1 - w1 * d0) * b0 = 0 := by linear_combination d1 * hwb - w1 * hbd
  have e1 : (w0 * d1 - w1 * d0) * b1 = 0 := by linear_combination w0 * hbd - d0 * hwb
  have := (mul_eq_zero.1 e0).resolve_left hdet0
  have := (mul_eq_zero.1 e1).resolve_left hdet0
  constructor <;> linarith

/-- **(R3b) rhombi force parallel rungs**: a unit rhombus `v₀v₁z₁z₀` has `z₀ − v₀ = z₁ − v₁`
(`v₁, z₀` are the two points of `C(v₀,1) ∩ C(z₁,1)`).

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: planar circle intersection. Difficulty M. -/
theorem R3_rhombus {v₀ v₁ z₀ z₁ : Pt} (h₀₁ : dist v₀ v₁ = 1) (h₁₁ : dist v₁ z₁ = 1)
    (h₁₀ : dist z₁ z₀ = 1) (h₀₀ : dist z₀ v₀ = 1) (hne : v₁ ≠ z₀) (hne' : v₀ ≠ z₁) :
    z₀ - v₀ = z₁ - v₁ := by
  have dsq : ∀ a b : Pt, dist a b = 1 → (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 = 1 := by
    intro a b h; rw [← dist_sq_pt, h, one_pow]
  have k1 := dsq _ _ h₀₁
  have k2 := dsq _ _ h₁₁
  have k3 := dsq _ _ h₁₀
  have k4 := dsq _ _ h₀₀
  have r := rhombus_real (x0 := v₁ 0 - v₀ 0) (x1 := v₁ 1 - v₀ 1) (y0 := z₀ 0 - v₀ 0)
    (y1 := z₀ 1 - v₀ 1) (d0 := z₁ 0 - v₀ 0) (d1 := z₁ 1 - v₀ 1)
    (by linear_combination k1) (by linear_combination k4)
    (by linear_combination k2) (by linear_combination k3)
    (by rintro ⟨a, b⟩; exact hne (pt_ext_iff.2 ⟨by linarith, by linarith⟩))
    (by rintro ⟨a, b⟩; exact hne' (pt_ext_iff.2 ⟨by linarith, by linarith⟩))
  rw [pt_ext_iff]; simp only [PiLp.sub_apply]
  constructor <;> linarith [r.1, r.2]

/-- **(R3c) rhombi only near resonance**: two parallel rungs whose K-ends are joined by a good
edge force `τ ≥ cos(β/2)` (their normals are exactly `2θ₀` apart, `θ₀ = arccos τ`).

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `exact_identity_c`, `u_ne`. Difficulty M. -/
theorem R3_resonance (F : DirField X) {v₀ v₁ z₀ z₁ : Pt} (h₀ : IsRung F v₀ z₀)
    (h₁ : IsRung F v₁ z₁) (hpar : z₀ - v₀ = z₁ - v₁) (hne : v₀ ≠ v₁)
    (hg : ang (F.u v₀) (F.u v₁) ≤ beta) : Real.cos (beta / 2) ≤ tau X := by
  have hc := h₀.norm_c
  have hu₀ := F.norm_u h₀.1
  have hu₁ := F.norm_u h₁.1
  have i₀ := h₀.inner_eq
  have i₁ := h₁.inner_eq
  rw [← hpar] at i₁
  have hne' : F.u v₀ ≠ F.u v₁ := u_ne F h₀.1 h₀.2.1 h₁.1 h₁.2.1 hne
  have hi := inner_two_sol hc hu₀ hu₁ i₀ i₁ hne'
  have hb : beta = 1 / 100 := rfl
  have hπ : beta ≤ π := by rw [hb]; linarith [Real.pi_gt_three]
  have hcos := cos_le_inner_of_ang_le hu₀ hu₁ hπ hg
  rw [hi, show beta = 2 * (beta / 2) by ring, Real.cos_two_mul] at hcos
  have hc2 := c5_rhombus
  have h3 : (1.7 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hτ := h₀.tau_ge
  by_contra hlt; push Not at hlt
  rw [hb] at hc2 hcos hlt
  nlinarith [mul_pos (sub_pos.2 hlt) (show 0 < Real.cos (1 / 100 / 2) + tau X by linarith)]

/-- **[C5] ownership ratios**: rhombus pairs `(4+m)/(2+m) ≤ 4/3` (`m ≥ 4`),
`(3+m)/(2+m) ≤ 4/3` (`m ≥ 2`); both-reach gaps `(1+k+d)/(k+d) ≤ 5/4` (`k, d ≥ 2`).

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S. -/
theorem ownership_ratios :
    (∀ m : ℝ, 4 ≤ m → (4 + m) / (2 + m) ≤ 4 / 3) ∧ (∀ m : ℝ, 2 ≤ m → (3 + m) / (2 + m) ≤ 4 / 3) ∧
      (∀ k d : ℝ, 2 ≤ k → 2 ≤ d → (1 + k + d) / (k + d) ≤ 5 / 4) := by
  refine ⟨fun m hm => ?_, fun m hm => ?_, fun k d hk hd => ?_⟩
  · rw [div_le_iff₀ (by linarith)]; linarith
  · rw [div_le_iff₀ (by linarith)]; linarith
  · rw [div_le_iff₀ (by linarith)]; linarith

section Ownership

variable {α : Type*} [DecidableEq α]

/-- **Abstract ownership/pairing count** (§7.2), by local discharging.

Rows: `K ⊆ V` (the `K`-row) and `V ∖ K` (the `D`-row).  `R a b`: `b` is the right (pure) T-neighbour
of `a` — a partial injection preserving rows.  `M v z`: `(v, z)` is a (good) rung — a matching
between the rows.  With (R2), (R2-sym) and no two consecutive rhombi (`hR3`):
`#Redges + #rungs ≤ (4/3)|V|`, and `≤ (5/4)|V|` if there are no rhombi at all (`hgen`).

Proof: every rung vertex set `{v, z}` is disjoint from the others; a non-rhombus rung with no
sink has both right neighbours unmatched (by (R2)/(R2-sym)) and claims them; the successor of a
rhombus rung is a non-rhombus rung (`hR3`), and the successor map is injective. -/
theorem own_count_core (V K : Finset α) (R M : α → α → Prop) (hKV : K ⊆ V)
    (hRV : ∀ a b, R a b → a ∈ V ∧ b ∈ V)
    (hRfun : ∀ a b b', R a b → R a b' → b = b')
    (hRinj : ∀ a a' b, R a b → R a' b → a = a')
    (hRrow : ∀ a b, R a b → (a ∈ K ↔ b ∈ K))
    (hMV : ∀ v z, M v z → v ∈ K ∧ z ∈ V ∧ z ∉ K)
    (hMfun : ∀ v z z', M v z → M v z' → z = z')
    (hMinj : ∀ v v' z, M v z → M v' z → v = v')
    (hR2 : ∀ v₀ z₀ v₁ z₁ z', M v₀ z₀ → R v₀ v₁ → R z₀ z₁ → M v₁ z' → z' = z₁)
    (hR2s : ∀ v₀ z₀ v₁ z₁ v', M v₀ z₀ → R v₀ v₁ → R z₀ z₁ → M v' z₁ → v' = v₁)
    (hR3 : ∀ v₀ z₀ v₁ z₁ v₂ z₂, M v₀ z₀ → R v₀ v₁ → R z₀ z₁ → M v₁ z₁ → R v₁ v₂ →
      R z₁ z₂ → ¬ M v₂ z₂) :
    3 * ((V.filter (fun a => ∃ b, R a b)).card + (K.filter (fun v => ∃ z, M v z)).card) ≤
        4 * V.card ∧
      ((∀ v₀ z₀ v₁ z₁, M v₀ z₀ → R v₀ v₁ → R z₀ z₁ → ¬ M v₁ z₁) →
        4 * ((V.filter (fun a => ∃ b, R a b)).card + (K.filter (fun v => ∃ z, M v z)).card) ≤
          5 * V.card) := by
  classical
  -- choice functions
  let rt : α → α := fun a => if h : ∃ b, R a b then h.choose else a
  let mt : α → α := fun v => if h : ∃ z, M v z then h.choose else v
  have hrt : ∀ a, (∃ b, R a b) → R a (rt a) := fun a h => by
    simp only [rt, dif_pos h]; exact h.choose_spec
  have hmt : ∀ v, (∃ z, M v z) → M v (mt v) := fun v h => by
    simp only [mt, dif_pos h]; exact h.choose_spec
  set Rs := V.filter (fun a => ∃ b, R a b)
  set N := V.filter (fun a => ¬ ∃ b, R a b)
  set Mv := K.filter (fun v => ∃ z, M v z)
  set ZM := V.filter (fun z => ∃ v, M v z)
  set A := V.filter (fun b => (∃ a, R a b ∧ ((∃ z, M a z) ∨ (∃ v, M v a))) ∧
    (¬ ∃ z, M b z) ∧ (¬ ∃ v, M v b))
  let sinkP : α → Prop := fun v => (¬ ∃ b, R v b) ∨ (¬ ∃ b, R (mt v) b)
  let rhP : α → Prop := fun v => ∃ v₁ z₁, R v v₁ ∧ R (mt v) z₁ ∧ M v₁ z₁
  set Ms := Mv.filter sinkP
  set Mh := Mv.filter rhP
  set Mo := Mv.filter (fun v => ¬ sinkP v ∧ ¬ rhP v)
  have hMvM : ∀ v ∈ Mv, M v (mt v) := fun v hv => hmt v (mem_filter.1 hv).2
  have hMvK : ∀ v ∈ Mv, v ∈ K := fun v hv => (mem_filter.1 hv).1
  -- (vi)
  have h6 : Rs.card + N.card = V.card := card_filter_add_card_filter_not _
  -- (i) `2|Mv| + |A| ≤ |V|`
  have hMZ : Mv.card ≤ ZM.card := by
    refine card_le_card_of_injOn mt (fun v hv => ?_) (fun v hv v' hv' e => ?_)
    · have := hMvM v hv
      exact mem_filter.2 ⟨(hMV _ _ this).2.1, v, this⟩
    · exact hMinj v v' (mt v) (hMvM v hv) (e ▸ hMvM v' hv')
  have h1 : Mv.card + ZM.card + A.card ≤ V.card := by
    have d1 : Disjoint Mv ZM := by
      rw [disjoint_left]; intro v hv hz
      obtain ⟨w, hw⟩ := (mem_filter.1 hz).2
      exact (hMV _ _ hw).2.2 (hMvK v hv)
    have d2 : Disjoint (Mv ∪ ZM) A := by
      rw [disjoint_left]; intro b hb ha
      obtain ⟨-, -, h1, h2⟩ := mem_filter.1 ha
      rcases mem_union.1 hb with hb | hb
      · exact h1 (mem_filter.1 hb).2
      · exact h2 (mem_filter.1 hb).2
    have hsub : Mv ∪ ZM ∪ A ⊆ V := by
      intro b hb
      rcases mem_union.1 hb with hb | hb
      · rcases mem_union.1 hb with hb | hb
        · exact hKV (hMvK b hb)
        · exact (mem_filter.1 hb).1
      · exact (mem_filter.1 hb).1
    have := card_le_card hsub
    rw [card_union_of_disjoint d2, card_union_of_disjoint d1] at this
    exact this
  -- non-sink, non-rhombus rungs have both right neighbours unmatched
  have hMoA : ∀ v ∈ Mo, rt v ∈ A ∧ rt (mt v) ∈ A ∧ rt v ∈ K ∧ rt (mt v) ∉ K := by
    intro v hv
    obtain ⟨hv, hns, hnr⟩ := mem_filter.1 hv
    have hM := hMvM v hv
    have hvK := hMvK v hv
    simp only [sinkP, not_or, not_not] at hns
    have r1 := hrt v hns.1
    have r2 := hrt (mt v) hns.2
    have k1 : rt v ∈ K := (hRrow _ _ r1).1 hvK
    have k2 : rt (mt v) ∉ K := fun h => (hMV _ _ hM).2.2 ((hRrow _ _ r2).2 h)
    have u1 : ¬ ∃ z, M (rt v) z := by
      rintro ⟨z', hz'⟩
      have := hR2 _ _ _ _ _ hM r1 r2 hz'
      exact hnr ⟨_, _, r1, r2, this ▸ hz'⟩
    have u2 : ¬ ∃ w, M w (rt (mt v)) := by
      rintro ⟨w, hw⟩
      have := hR2s _ _ _ _ _ hM r1 r2 hw
      exact hnr ⟨_, _, r1, r2, this ▸ hw⟩
    refine ⟨mem_filter.2 ⟨(hRV _ _ r1).2, ⟨v, r1, Or.inl ⟨_, hM⟩⟩, u1, ?_⟩,
      mem_filter.2 ⟨(hRV _ _ r2).2, ⟨mt v, r2, Or.inr ⟨v, hM⟩⟩, ?_, u2⟩, k1, k2⟩
    · rintro ⟨w, hw⟩; exact (hMV _ _ hw).2.2 k1
    · rintro ⟨z, hz⟩; exact k2 (hMV _ _ hz).1
  -- (ii) `2|Mo| ≤ |A|`
  have h2 : 2 * Mo.card ≤ A.card := by
    have hMo : ∀ v ∈ Mo, v ∈ Mv ∧ (∃ b, R v b) ∧ (∃ b, R (mt v) b) := by
      intro v hv
      obtain ⟨hv, hns, -⟩ := mem_filter.1 hv
      simp only [sinkP, not_or, not_not] at hns
      exact ⟨hv, hns⟩
    have i1 : (Mo.image rt).card = Mo.card := by
      refine card_image_of_injOn fun v hv v' hv' e => ?_
      obtain ⟨-, a, -⟩ := hMo v hv
      obtain ⟨-, a', -⟩ := hMo v' hv'
      exact hRinj _ _ _ (hrt v a) (e ▸ hrt v' a')
    have i2 : (Mo.image (fun v => rt (mt v))).card = Mo.card := by
      refine card_image_of_injOn fun v hv v' hv' e => ?_
      obtain ⟨m, -, a⟩ := hMo v hv
      obtain ⟨m', -, a'⟩ := hMo v' hv'
      have := hRinj _ _ _ (hrt _ a) ((show rt (mt v) = rt (mt v') from e) ▸ hrt _ a')
      exact hMinj _ _ _ (hMvM v m) (this ▸ hMvM v' m')
    have d : Disjoint (Mo.image rt) (Mo.image (fun v => rt (mt v))) := by
      rw [disjoint_left]; intro b hb hb'
      obtain ⟨v, hv, rfl⟩ := mem_image.1 hb
      obtain ⟨v', hv', e⟩ := mem_image.1 hb'
      exact (hMoA v' hv').2.2.2 (e ▸ (hMoA v hv).2.2.1)
    have hsub : Mo.image rt ∪ Mo.image (fun v => rt (mt v)) ⊆ A := by
      intro b hb
      rcases mem_union.1 hb with hb | hb
      · obtain ⟨v, hv, rfl⟩ := mem_image.1 hb; exact (hMoA v hv).1
      · obtain ⟨v, hv, rfl⟩ := mem_image.1 hb; exact (hMoA v hv).2.1
    have := card_le_card hsub
    rw [card_union_of_disjoint d, i1, i2] at this
    omega
  -- (iii) `|Ms| ≤ |N|`
  have h3 : Ms.card ≤ N.card := by
    let f : α → α := fun v => if ∃ b, R v b then mt v else v
    refine card_le_card_of_injOn f (fun v hv => ?_) (fun v hv v' hv' e => ?_)
    · obtain ⟨hv, hs⟩ := mem_filter.1 hv
      by_cases h : ∃ b, R v b
      · have hs' : ¬ ∃ b, R (mt v) b := by
          rcases hs with hs | hs
          · exact absurd h hs
          · exact hs
        simp only [f, if_pos h]
        exact mem_filter.2 ⟨(hMV _ _ (hMvM v hv)).2.1, hs'⟩
      · simp only [f, if_neg h]
        exact mem_filter.2 ⟨hKV (hMvK v hv), h⟩
    · have hv1 := (mem_filter.1 hv).1
      have hv1' := (mem_filter.1 hv').1
      simp only [f] at e
      split_ifs at e with h h'
      · exact hMinj _ _ _ (hMvM v hv1) (e ▸ hMvM v' hv1')
      · exact absurd (e ▸ hMvK v' hv1') (hMV _ _ (hMvM v hv1)).2.2
      · exact absurd (e.symm ▸ hMvK v hv1) (hMV _ _ (hMvM v' hv1')).2.2
      · exact e
  -- (iv) `|Mh| ≤ |Ms| + |Mo|`: the successor of a rhombus rung is not a rhombus rung
  have h4 : Mh.card ≤ Ms.card + Mo.card := by
    have hsub : Mh.image rt ⊆ Ms ∪ Mo := by
      intro b hb
      obtain ⟨v, hv, rfl⟩ := mem_image.1 hb
      obtain ⟨hv, v₁, z₁, r1, r2, m1⟩ := mem_filter.1 hv
      have e1 : rt v = v₁ := hRfun _ _ _ (hrt v ⟨_, r1⟩) r1
      rw [e1]
      have hv₁ : v₁ ∈ Mv := mem_filter.2 ⟨(hRrow _ _ r1).1 (hMvK v hv), _, m1⟩
      have hnr : ¬ rhP v₁ := by
        rintro ⟨v₂, z₂, r3, r4, m2⟩
        have e2 : mt v₁ = z₁ := hMfun _ _ _ (hMvM v₁ hv₁) m1
        rw [e2] at r4
        exact hR3 _ _ _ _ _ _ (hMvM v hv) r1 r2 m1 r3 r4 m2
      by_cases hs : sinkP v₁
      · exact mem_union.2 (Or.inl (mem_filter.2 ⟨hv₁, hs⟩))
      · exact mem_union.2 (Or.inr (mem_filter.2 ⟨hv₁, hs, hnr⟩))
    have hinj : (Mh.image rt).card = Mh.card := by
      refine card_image_of_injOn fun v hv v' hv' e => ?_
      obtain ⟨-, v₁, -, r1, -⟩ := mem_filter.1 hv
      obtain ⟨-, v₁', -, r1', -⟩ := mem_filter.1 hv'
      exact hRinj _ _ _ (hrt v ⟨_, r1⟩) ((show rt v = rt v' from e) ▸ hrt v' ⟨_, r1'⟩)
    have := (card_le_card hsub).trans (card_union_le _ _)
    omega
  -- (v) `|Mv| ≤ |Ms| + |Mh| + |Mo|`
  have h5 : Mv.card ≤ Ms.card + Mh.card + Mo.card := by
    have hsub : Mv ⊆ Ms ∪ Mh ∪ Mo := by
      intro v hv
      by_cases hs : sinkP v
      · exact mem_union.2 (Or.inl (mem_union.2 (Or.inl (mem_filter.2 ⟨hv, hs⟩))))
      by_cases hr : rhP v
      · exact mem_union.2 (Or.inl (mem_union.2 (Or.inr (mem_filter.2 ⟨hv, hr⟩))))
      · exact mem_union.2 (Or.inr (mem_filter.2 ⟨hv, hs, hr⟩))
    have := (card_le_card hsub).trans (card_union_le _ _)
    have := card_union_le Ms Mh
    omega
  refine ⟨by omega, fun hgen => ?_⟩
  have h0 : Mh.card = 0 := by
    rw [card_eq_zero, eq_empty_iff_forall_notMem]
    intro v hv
    obtain ⟨hv, v₁, z₁, r1, r2, m1⟩ := mem_filter.1 hv
    exact hgen _ _ _ _ (hMvM v hv) r1 r2 m1
  omega

end Ownership

/-! ### Geometric input for the ownership count -/

/-- For a good T-step `p → q`, the side flips when seen from `q`:
`det(u_q, p − q)` has the opposite sign of `det(u_p, q − p)`. -/
theorem tstep_flip {F : DirField X} {p q : Pt} (hp : p ∈ Sset X) (hq : q ∈ Sset X)
    (h1 : dist p q = 1) (hg : ang (F.u p) (F.u q) ≤ beta) (ha : 0 < inner ℝ (q - p) (F.u p))
    (ha' : inner ℝ (q - p) (F.u p) < beta) :
    det2 (F.u q) (p - q) * det2 (F.u p) (q - p) < 0 := by
  have hup := F.norm_u hp
  have huq := F.norm_u hq
  have he : ‖q - p‖ = 1 := by rw [← dist_eq_norm, dist_comm, h1]
  have n := inner_sq_add_det_sq (e := q - p) hup
  rw [he] at n
  have hw : ‖F.u q - F.u p‖ ≤ beta := by
    rw [norm_sub_rev]; exact (norm_sub_le_angR hup huq).trans hg
  have hd := abs_det2_leR (F.u q - F.u p) (q - p)
  rw [he, mul_one] at hd
  have e : det2 (F.u q) (p - q) = -(det2 (F.u p) (q - p) + det2 (F.u q - F.u p) (q - p)) := by
    rw [← neg_sub q p, det2_neg_right, ← det2_add_left]; congr 2; abel
  rw [e]
  have hb : beta = 1 / 100 := rfl
  set c := det2 (F.u p) (q - p)
  set w := det2 (F.u q - F.u p) (q - p)
  rw [abs_le] at hd
  rw [hb] at hw ha'
  have hc : 99 / 100 < |c| := by
    rw [lt_abs]
    rcases le_or_gt 0 c with h | h
    · left; nlinarith
    · right; nlinarith
  rw [lt_abs] at hc
  rcases hc with hc | hc <;> nlinarith

/-- The pure right-T-neighbour relation of a row. -/
def RowR (F : DirField X) (a b : Pt) : Prop := IsSideT F (-1) a b ∧ (a ∈ Dset X ↔ b ∈ Dset X)

/-- Good rungs, as a relation `K-end → D-end`. -/
def RungM (X : Finset Pt) (F : DirField X) (v z : Pt) : Prop := IsRung F v z ∧ s(v, z) ∈ good X F

theorem RungM.ang {F : DirField X} {v z : Pt} (h : RungM X F v z) : ang (F.u v) (F.u z) ≤ beta :=
  (mem_filter.1 h.2).2 v z rfl

/-- (T1) for right neighbours. -/
theorem rowR_fun (hX : Normal X) {F : DirField X} {a b b' : Pt} (h : RowR F a b)
    (h' : RowR F a b') : b = b' := by
  obtain ⟨n₁, a₁, a₁', c₁⟩ := h.1.step
  obtain ⟨n₂, a₂, a₂', c₂⟩ := h'.1.step
  have hc := same_side_close (F.norm_u h.1.1) n₁ n₂ (σ := -1) (by linarith) (by linarith)
    (L := 0) (U := beta) ⟨a₁.le, a₁'.le⟩ ⟨a₂.le, a₂'.le⟩
    (by rw [Real.arcsin_zero, sub_zero]; exact arcsin_beta_lt)
  rw [sub_sub_sub_cancel_right, ← dist_eq_norm] at hc
  exact eq_of_dist_lt_one hX.minDist_eq (Sset_sub h.1.2.1) (Sset_sub h'.1.2.1) hc

/-- (T2)-type injectivity: a vertex has at most one left neighbour. -/
theorem rowR_inj (hX : Normal X) {F : DirField X} {a a' b : Pt} (h : RowR F a b)
    (h' : RowR F a' b) : a = a' := by
  have flip : ∀ {a : Pt}, RowR F a b → ‖a - b‖ = 1 ∧ 0 < inner ℝ (a - b) (F.u b) ∧
      inner ℝ (a - b) (F.u b) < beta ∧ 0 < 1 * det2 (F.u b) (a - b) := by
    intro a h
    obtain ⟨ha, hb, h1, hg, ⟨x, y, z, w⟩, hs⟩ := h.1
    have := tstep_flip ha hb h1 hg x y
    refine ⟨by rw [← dist_eq_norm, h1], z, w, ?_⟩
    have : det2 (F.u a) (b - a) < 0 := by linarith
    nlinarith
  obtain ⟨n₁, a₁, a₁', c₁⟩ := flip h
  obtain ⟨n₂, a₂, a₂', c₂⟩ := flip h'
  have hc := same_side_close (F.norm_u h.1.2.1) n₁ n₂ c₁ c₂
    (L := 0) (U := beta) ⟨a₁.le, a₁'.le⟩ ⟨a₂.le, a₂'.le⟩
    (by rw [Real.arcsin_zero, sub_zero]; exact arcsin_beta_lt)
  rw [sub_sub_sub_cancel_right, ← dist_eq_norm] at hc
  exact eq_of_dist_lt_one hX.minDist_eq (Sset_sub h.1.1) (Sset_sub h'.1.1) hc

/-- No 2-cycles of right neighbours. -/
theorem rowR_no_two_cycle {F : DirField X} {a b : Pt} (h : RowR F a b) (h' : RowR F b a) :
    False := by
  obtain ⟨ha, hb, h1, hg, ⟨x, y, -, -⟩, -⟩ := h.1
  have := tstep_flip ha hb h1 hg x y
  have s1 := h.1.2.2.2.2.2
  have s2 := h'.1.2.2.2.2.2
  nlinarith

/-- A rhombus of a good rung, two pure right T-steps and a good rung forces parallel rungs. -/
theorem rhombus_par {F : DirField X} {v₀ z₀ v₁ z₁ : Pt} (m₀ : RungM X F v₀ z₀)
    (rv : RowR F v₀ v₁) (rz : RowR F z₀ z₁) (m₁ : RungM X F v₁ z₁) : z₀ - v₀ = z₁ - v₁ := by
  refine R3_rhombus rv.1.2.2.1 m₁.1.2.2.2.2.1 (by rw [dist_comm]; exact rz.1.2.2.1)
    (by rw [dist_comm]; exact m₀.1.2.2.2.2.1) ?_ ?_
  · intro e; exact m₁.1.2.1 (e ▸ m₀.1.2.2.2.1)
  · intro e; exact m₀.1.2.1 (e ▸ m₁.1.2.2.2.1)

/-- The abstract ownership count, instantiated. -/
theorem ownership_core (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X ≤ 1) :
    3 * (((Sset X).filter (fun a => ∃ b, RowR F a b)).card +
        (((Sset X).filter (fun v => v ∉ Dset X)).filter (fun v => ∃ z, RungM X F v z)).card) ≤
        4 * (Sset X).card ∧
      (tau X < Real.cos (beta / 2) →
        4 * (((Sset X).filter (fun a => ∃ b, RowR F a b)).card +
          (((Sset X).filter (fun v => v ∉ Dset X)).filter (fun v => ∃ z, RungM X F v z)).card) ≤
          5 * (Sset X).card) := by
  have core := own_count_core (Sset X) ((Sset X).filter (fun v => v ∉ Dset X)) (RowR F)
    (RungM X F) (filter_subset _ _)
    (fun a b h => ⟨h.1.1, h.1.2.1⟩)
    (fun a b b' h h' => rowR_fun hX h h')
    (fun a a' b h h' => rowR_inj hX h h')
    (fun a b h => by
      simp only [mem_filter]
      exact ⟨fun ⟨_, hd⟩ => ⟨h.1.2.1, fun hb => hd (h.2.2 hb)⟩,
        fun ⟨_, hd⟩ => ⟨h.1.1, fun ha => hd (h.2.1 ha)⟩⟩)
    (fun v z h => ⟨mem_filter.2 ⟨h.1.1, h.1.2.1⟩, h.1.2.2.1,
      fun hz => (mem_filter.1 hz).2 h.1.2.2.2.1⟩)
    (fun v z z' h h' => R1_v hX F hτ₁ hτ₂ h.1 h'.1)
    (fun v v' z h h' => R1_z hX F hτ₁ hτ₂ h.1 h'.1 h.ang h'.ang)
    (fun v₀ z₀ v₁ z₁ z' m₀ rv rz m' => R2 hX F hτ₁ hτ₂ m₀.1 m₀.ang rv.1
      (fun h => m₀.1.2.1 (rv.2.2 h)) rz.1 (rz.2.1 m₀.1.2.2.2.1) m'.1 m'.ang)
    (fun v₀ z₀ v₁ z₁ v' m₀ rv rz m' => R2_sym hX F hτ₁ hτ₂ m₀.1 m₀.ang rv.1
      (fun h => m₀.1.2.1 (rv.2.2 h)) rz.1 (rz.2.1 m₀.1.2.2.2.1) m'.1 m'.ang)
    (fun v₀ z₀ v₁ z₁ v₂ z₂ m₀ r₀ s₀ m₁ r₁ s₁ m₂ => by
      have p₁ := rhombus_par m₀ r₀ s₀ m₁
      have p₂ := rhombus_par m₁ r₁ s₁ m₂
      rcases R3_no_three_parallel F m₀.1 m₁.1 m₂.1 p₁ (p₁.trans p₂) with e | e | e
      · have := r₀.1.2.2.1; rw [e, dist_self] at this; norm_num at this
      · rw [e] at r₀; exact rowR_no_two_cycle r₀ r₁
      · have := r₁.1.2.2.1; rw [e, dist_self] at this; norm_num at this)
  refine ⟨core.1, fun hlt => core.2 fun v₀ z₀ v₁ z₁ m₀ r₀ s₀ m₁ => ?_⟩
  have hpar := rhombus_par m₀ r₀ s₀ m₁
  have hne : v₀ ≠ v₁ := by
    intro e; have := r₀.1.2.2.1; rw [e, dist_self] at this; norm_num at this
  exact absurd (R3_resonance F m₀.1 m₁.1 hpar hne r₀.1.2.2.2.1) (not_le.2 hlt)

/-- Pure good edges are pure right-T-edges or good rungs:
`#goodPure ≤ #{a : a has a pure right T-neighbour} + #{K-ends of good rungs}`. -/
theorem card_goodPure_le (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X ≤ 1) :
    (goodPure X F).card ≤ ((Sset X).filter (fun a => ∃ b, RowR F a b)).card +
        (((Sset X).filter (fun v => v ∉ Dset X)).filter (fun v => ∃ z, RungM X F v z)).card := by
  classical
  have hτ : 2 * beta < tau X := by
    have := Real.sqrt_nonneg 3; unfold beta at hτ₁ ⊢; linarith
  set Rs := (Sset X).filter (fun a => ∃ b, RowR F a b)
  set Mv := ((Sset X).filter (fun v => v ∉ Dset X)).filter (fun v => ∃ z, RungM X F v z)
  let rt : Pt → Pt := fun a => if h : ∃ b, RowR F a b then h.choose else a
  let mt : Pt → Pt := fun v => if h : ∃ z, RungM X F v z then h.choose else v
  have hrt : ∀ a, (h : ∃ b, RowR F a b) → RowR F a (rt a) := fun a h => by
    simp only [rt, dif_pos h]; exact h.choose_spec
  have hmt : ∀ v, (h : ∃ z, RungM X F v z) → RungM X F v (mt v) := fun v h => by
    simp only [mt, dif_pos h]; exact h.choose_spec
  have hsub : goodPure X F ⊆ Rs.image (fun a => s(a, rt a)) ∪ Mv.image (fun v => s(v, mt v)) := by
    intro e he
    obtain ⟨heg, hem⟩ := mem_sdiff.1 he
    rcases mem_union.1 (good_subset_T_union_rungs hX F hτ heg) with hT | hR
    · obtain ⟨-, hTall⟩ := mem_filter.1 hT
      have hge := heg
      obtain ⟨hee, hgood⟩ := mem_filter.1 hge
      obtain ⟨hnd, hS⟩ := mem_edges hee
      have hd : pairDist e = minDist X := (mem_filter.1 hee).2
      induction e using Sym2.ind with
      | _ p q =>
      have hp : p ∈ Sset X := hS p (Sym2.mem_mk_left _ _)
      have hq : q ∈ Sset X := hS q (Sym2.mem_mk_right _ _)
      have h1 : dist p q = 1 := by rw [← hX.minDist_eq, ← hd]; rfl
      have hg : ang (F.u p) (F.u q) ≤ beta := hgood p q rfl
      have hg' : ang (F.u q) (F.u p) ≤ beta := hgood q p Sym2.eq_swap
      have hTpq := hTall p q rfl
      have hTqp := hTall q p Sym2.eq_swap
      have hrow : (p ∈ Dset X ↔ q ∈ Dset X) := by
        constructor
        · intro hpD; by_contra hqD
          exact hem (mem_filter.2 ⟨hT, q, p, Sym2.eq_swap, hqD, hpD⟩)
        · intro hqD; by_contra hpD
          exact hem (mem_filter.2 ⟨hT, p, q, rfl, hpD, hqD⟩)
      have hflip := tstep_flip hp hq h1 hg hTpq.1 hTpq.2.1
      have n := inner_sq_add_det_sq (e := q - p) (F.norm_u hp)
      rw [← dist_eq_norm, dist_comm, h1] at n
      have hb : beta = 1 / 100 := rfl
      have hne : det2 (F.u p) (q - p) ≠ 0 := by
        intro h0; rw [h0] at n
        obtain ⟨x1, x2, -, -⟩ := hTpq
        rw [hb] at x2; nlinarith
      refine mem_union.2 (Or.inl (mem_image.2 ?_))
      rcases hne.lt_or_gt with hlt | hgt
      · have hR : RowR F p q := ⟨⟨hp, hq, h1, hg, hTpq, by linarith⟩, hrow⟩
        refine ⟨p, mem_filter.2 ⟨hp, q, hR⟩, ?_⟩
        rw [rowR_fun hX (hrt p ⟨q, hR⟩) hR]
      · have hlt : det2 (F.u q) (p - q) < 0 := by nlinarith
        have hR : RowR F q p :=
          ⟨⟨hq, hp, by rw [dist_comm]; exact h1, hg', hTqp, by linarith⟩, hrow.symm⟩
        refine ⟨q, mem_filter.2 ⟨hq, p, hR⟩, ?_⟩
        rw [rowR_fun hX (hrt q ⟨p, hR⟩) hR]; exact Sym2.eq_swap
    · obtain ⟨hge, v, w, rfl, hr⟩ := mem_filter.1 hR
      have hM : RungM X F v w := ⟨hr, hge⟩
      refine mem_union.2 (Or.inr (mem_image.2 ⟨v, mem_filter.2 ⟨mem_filter.2 ⟨hr.1, hr.2.1⟩,
        w, hM⟩, ?_⟩))
      rw [R1_v hX F hτ₁ hτ₂ (hmt v ⟨w, hM⟩).1 hr]
  exact (card_le_card hsub).trans ((card_union_le _ _).trans
    (add_le_add card_image_le card_image_le))

/-- **Ownership count, no rhombi** (`√3/2 + 3β ≤ τ < cos(β/2)`): pure good edges `≤ (5/4)|S|`.

TODO: none — proved.
Acceptance: no `sorry`.
Proof: `ownership_core` (the abstract local-discharging count `own_count_core`, instantiated with
pure right T-steps `RowR` and good rungs `RungM`) and `card_goodPure_le`.  Instead of the
walk/ownership bookkeeping of the write-up, each rung `(v, z)` claims `{v, z}` and, when neither
end is a path end and it is not a rhombus rung, both right neighbours `v₁, z₁`, which are unmatched
by (R2)/(R2-sym); rhombi are excluded by `R3_rhombus` + `R3_resonance`.
Depends on: `R1_v`, `R1_z`, `R2`, `R2_sym`, `R3_rhombus`, `R3_resonance`,
`good_subset_T_union_rungs`. -/
theorem ownership_rest (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X < Real.cos (beta / 2)) :
    ((goodPure X F).card : ℝ) ≤ 5 / 4 * (Sset X).card := by
  have hτ₂' : tau X ≤ 1 := hτ₂.le.trans (Real.cos_le_one _)
  have h1 := (ownership_core hX F hτ₁ hτ₂').2 hτ₂
  have h2 := card_goodPure_le hX F hτ₁ hτ₂'
  have : 4 * (goodPure X F).card ≤ 5 * (Sset X).card := by omega
  have : (4 : ℝ) * (goodPure X F).card ≤ 5 * (Sset X).card := by exact_mod_cast this
  linarith

/-- **Ownership + pairing** (`cos(β/2) ≤ τ ≤ 1`): pure good edges `≤ (4/3)|S|`.

TODO: none — proved.
Acceptance: no `sorry`.
Proof: as `ownership_rest`; a rhombus rung borrows `1/3` from its successor rung, which is not a
rhombus rung (`R3_rhombus` twice + `R3_no_three_parallel`, no 2-cycles of T-steps) and has a
sink or two unmatched right neighbours; the successor map is injective.
Depends on: `R1_v`, `R1_z`, `R2`, `R2_sym`, `R3_rhombus`, `R3_no_three_parallel`,
`good_subset_T_union_rungs`. -/
theorem ownership_res (hX : Normal X) (F : DirField X) (hτ₁ : Real.cos (beta / 2) ≤ tau X)
    (hτ₂ : tau X ≤ 1) : ((goodPure X F).card : ℝ) ≤ 4 / 3 * (Sset X).card := by
  have hτ₁' : √3 / 2 + 3 * beta ≤ tau X := c5_rhombus.le.trans hτ₁
  have h1 := (ownership_core hX F hτ₁' hτ₂).1
  have h2 := card_goodPure_le hX F hτ₁' hτ₂
  have : 3 * (goodPure X F).card ≤ 4 * (Sset X).card := by omega
  have : (3 : ℝ) * (goodPure X F).card ≤ 4 * (Sset X).card := by exact_mod_cast this
  linarith

/-- Region II wiring: `e(S) ≤ goodPure + 1200 + 1.837·10⁷ ≤ goodPure + cBad + 100`.

TODO: none.
Acceptance: no `sorry` (inherits).
Depends on: `card_good_add_bad`, `card_good_le_pure_add_mixed`, `card_mixedT_le`,
`bad_subset`, `card_badKK_le`, `card_badDD_le`, `card_badC1_le`, `card_badC2_le`. -/
theorem regionII_eS_le (hX : Normal X) (F : DirField X) (hτ : √3 / 2 + 3 * beta ≤ tau X) :
    (eS X : ℝ) ≤ (goodPure X F).card + (cBad + 100) := by
  have h1 : (eS X : ℝ) = (good X F).card + (bad X F).card := by
    exact_mod_cast (card_good_add_bad F).symm
  have h2 : ((good X F).card : ℝ) ≤ (goodPure X F).card + (mixedT X F).card := by
    exact_mod_cast card_good_le_pure_add_mixed F
  have h3 := card_mixedT_le hX F hτ
  -- the explicit bad-edge constants (as in `card_bad_le`), to absorb the mixed count
  have h := card_le_card (bad_subset F)
  have k1 := card_union_le (badKK X F ∪ badDD X F ∪ badC1 X F) (badC2 X F)
  have k2 := card_union_le (badKK X F ∪ badDD X F) (badC1 X F)
  have k3 := card_union_le (badKK X F) (badDD X F)
  have e1 := card_badKK_le hX F
  have e2 := card_badDD_le hX F
  have e3 := card_badC1_le hX F
  have e4 := card_badC2_le hX F
  have h4 : ((bad X F).card : ℝ) ≤ (badKK X F).card + (badDD X F).card + (badC1 X F).card +
      (badC2 X F).card := by
    exact_mod_cast h.trans (k1.trans (by omega))
  unfold cBad
  linarith

/-- **Region II-rest**: `e(S) ≤ (5/4)|S| + C` (gives `36n/25`). -/
theorem regionII_rest (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 + 3 * beta ≤ tau X)
    (hτ₂ : tau X < Real.cos (beta / 2)) :
    (eS X : ℝ) ≤ 5 / 4 * (Sset X).card + (cBad + 100) := by
  have := regionII_eS_le hX F hτ₁
  have := ownership_rest hX F hτ₁ hτ₂
  linarith

/-- **Region II-near-resonant**: `e(S) ≤ (4/3)|S| + C` (gives `54n/37`). -/
theorem regionII_res (hX : Normal X) (F : DirField X) (hτ₁ : Real.cos (beta / 2) ≤ tau X)
    (hτ₂ : tau X ≤ 1) : (eS X : ℝ) ≤ 4 / 3 * (Sset X).card + (cBad + 100) := by
  have := regionII_eS_le hX F (c5_rhombus.le.trans hτ₁)
  have := ownership_res hX F hτ₁ hτ₂
  linarith

/-! ## §7.3 Region III: `√3/2 − 2β < τ < √3/2 + 3β` -/

/-- **[C6]** `√3/2 + 3β < cos(π/7)` and `cos(3π/14) < √3/2 − 2β`.

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: nothing. Difficulty S–M. -/
theorem c6 : √3 / 2 + 3 * beta < Real.cos (π / 7) ∧ Real.cos (3 * π / 14) < √3 / 2 - 2 * beta := by
  have h3 : (1.732 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h3' : √3 < 1.7321 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hpl := Real.pi_lt_d4
  have hpg := Real.pi_gt_d4
  refine ⟨?_, ?_⟩
  · have hc := Real.one_sub_sq_div_two_le_cos (x := π / 7)
    have : (π / 7) ^ 2 < (3.1416 / 7) ^ 2 := by
      apply pow_lt_pow_left₀ (by linarith) (by positivity) (by norm_num)
    rw [beta]; norm_num at this ⊢; nlinarith
  · have hx : |3 * π / 14| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    have hb := Real.cos_bound hx
    have hlo : (3 * 3.1415 / 14 : ℝ) ^ 2 < (3 * π / 14) ^ 2 := by
      apply pow_lt_pow_left₀ (by linarith) (by norm_num) (by norm_num)
    have h4 : |3 * π / 14| ^ 4 ≤ 1 := by
      have := pow_le_one₀ (abs_nonneg _) hx (n := 4); exact this
    rw [abs_le] at hb
    rw [beta]; norm_num at hlo ⊢; nlinarith

/-- K-vertices having a rung. -/
def rungVerts (X : Finset Pt) (F : DirField X) : Finset Pt :=
  (Sset X \ Dset X).filter (fun v => ∃ z, IsRung F v z)

/-- `P₁`: rung K-vertices of `Δ₂`-degree exactly 1. -/
def P1set (X : Finset Pt) (F : DirField X) : Finset Pt :=
  (rungVerts X F).filter (fun v => deg2 X v = 1)

/-- Corner vertices: rung K-vertices with a second `Δ₂`-partner. -/
def cornerVerts (X : Finset Pt) (F : DirField X) : Finset Pt :=
  (rungVerts X F).filter (fun v => ¬ deg2 X v = 1)


/-- The direction field with the partner of `v ∉ D` changed to another `Δ₂`-partner `w`. -/
def DirField.redirect (F : DirField X) {v w : Pt} (hw : w ∈ X) (hvw : dist v w = dist2 X)
    (hvD : v ∉ Dset X) : DirField X where
  partner := Function.update F.partner v w
  partner_mem p hp := by
    by_cases h : p = v
    · subst h; simpa using hw
    · simpa [h] using F.partner_mem p hp
  partner_K p hp hpD := by
    by_cases h : p = v
    · subst h; simpa using hvw
    · simpa [h] using F.partner_K p hp hpD
  partner_D p hp hpD := by
    by_cases h : p = v
    · subst h; exact absurd hpD hvD
    · simpa [h] using F.partner_D p hp hpD

theorem DirField.redirect_partner (F : DirField X) {v w : Pt} (hw : w ∈ X)
    (hvw : dist v w = dist2 X) (hvD : v ∉ Dset X) : (F.redirect hw hvw hvD).partner v = w := by
  simp [DirField.redirect]

/-- Corner inequality, algebra: `c·u = −τ`, `c·u' > 0`, `τ > 0` ⇒ `u·u' < √(1 − τ²)`. -/
theorem inner_lt_sOff {c u u' : Pt} {τ : ℝ} (hc : ‖c‖ = 1) (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1)
    (e : inner ℝ c u = -τ) (hτ : 0 < τ) (hpos : 0 < inner ℝ c u') :
    inner ℝ u u' < √(1 - τ ^ 2) := by
  have n₁ := inner_sq_add_det_sq (e := u) hc
  have n₂ := inner_sq_add_det_sq (e := u') hc
  rw [real_inner_comm, e, hu] at n₁
  rw [real_inner_comm, hu'] at n₂
  have hL := inner_mul_add_det_mul c u u'
  rw [e, hc] at hL
  set d := det2 c u
  set b := det2 c u'
  set a := inner ℝ c u'
  set s := √(1 - τ ^ 2)
  have hs : s ^ 2 = 1 - τ ^ 2 := Real.sq_sqrt (by nlinarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hdb : d * b ≤ s := by
    by_contra h; push Not at h
    have : s ^ 2 < (d * b) ^ 2 := by nlinarith
    nlinarith [sq_nonneg a]
  have : inner ℝ u u' = -τ * a + d * b := by linear_combination -hL
  nlinarith [mul_pos hτ hpos]

/-- **Corner lemma**: `v ∈ S ∖ D` with a rung and a second `Δ₂`-partner `w′`:
`∠(u_v, u′) ≥ min(2θ₀, 90° − θ₀) > 2π/7`.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `exact_identity_b`, `exact_identity_c`, `c6`. Difficulty M–L. -/
theorem corner_lemma (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 - 2 * beta < tau X)
    (hτ₂ : tau X < √3 / 2 + 3 * beta) {v z w' : Pt} (hr : IsRung F v z) (hw' : w' ∈ X)
    (hw'v : dist v w' = dist2 X) (hne : w' ≠ F.partner v) :
    2 * π / 7 < ang (F.u v) ((dist2 X)⁻¹ • (w' - v)) := by
  have hv := hr.1
  have hvD := hr.2.1
  have hw'X := hw'
  have hT := hr.two
  have hpos := hT.1.pos
  set F' := F.redirect hw' hw'v hvD
  have hp' : F'.partner v = w' := F.redirect_partner hw' hw'v hvD
  have hu'eq : F'.u v = (dist2 X)⁻¹ • (w' - v) := by
    unfold DirField.u; rw [hp', hw'v]
  rw [← hu'eq]
  have hc := hr.norm_c
  have hu := F.norm_u hv
  have hu' := F'.norm_u hv
  have i₀ := hr.inner_eq
  have hπ := Real.pi_gt_three
  have h3 : (1.7 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hτ0 : 0 < tau X := by unfold beta at hτ₁; linarith
  obtain ⟨c61, c62⟩ := c6
  by_cases hzw : dist z w' = diam X
  · -- the other root of `c·u = −τ`: angle `2θ₀`
    have i₁ : inner ℝ (z - v) (F'.u v) = - tau X :=
      exact_identity_c F' hv hvD (by rw [hp']; exact hzw) (by rw [dist_comm]; exact hr.2.2.2.2.1)
    have hne' : F.u v ≠ F'.u v := by
      intro e
      apply hne
      have hpK := F.partner_K v hv hvD
      unfold DirField.u at e
      rw [hp', hpK, hw'v] at e
      have := smul_right_injective Pt (inv_ne_zero hpos.ne') e
      simpa using this.symm
    have hi := inner_two_sol hc hu hu' i₀ i₁ hne'
    refine lt_ang_of_inner_lt hu hu' (by positivity) (by linarith) ?_
    rw [hi, show 2 * π / 7 = 2 * (π / 7) by ring, Real.cos_two_mul]
    have : tau X < Real.cos (π / 7) := hτ₂.trans c61
    nlinarith
  · -- `c·u' > 0`, and `c·u_v = −τ`: angle `≥ 90° − θ₀`
    have hb := exact_identity_b F' hv hvD hr.memX.2
    rw [hp'] at hb
    have ha : 0 < inner ℝ (z - v) (F'.u v) := by
      rcases hb with hb | hb
      · refine lt_of_lt_of_le ?_ hb
        rw [dist_comm, hr.2.2.2.2.1]; positivity
      · exact absurd hb hzw
    have hlt := inner_lt_sOff hc hu hu' i₀ hτ0 ha
    refine lt_ang_of_inner_lt hu hu' (by positivity) (by linarith) (hlt.trans_le ?_)
    have e1 : Real.cos (2 * π / 7) = Real.sin (3 * π / 14) := by
      rw [← Real.cos_pi_div_two_sub]; congr 1; ring
    rw [e1]
    have hs0 : 0 < Real.sin (3 * π / 14) := Real.sin_pos_of_pos_of_lt_pi (by positivity)
      (by linarith)
    have hc0 : 0 < Real.cos (3 * π / 14) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    have hsc := Real.sin_sq_add_cos_sq (3 * π / 14)
    rw [Real.sqrt_le_left hs0.le]
    have : Real.cos (3 * π / 14) < tau X := c62.trans hτ₁
    nlinarith


/-- **At most 6 corner vertices** (their normal cones of `K` are wider than `2π/7` and
interior-disjoint).

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `corner_lemma`, `ball_polygon_b`, `turning_sum_le` (or disjoint cones). Difficulty M. -/
theorem card_cornerVerts_le (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 - 2 * beta < tau X)
    (hτ₂ : tau X < √3 / 2 + 3 * beta) : (cornerVerts X F).card ≤ 6 := by
  by_contra hlt
  push Not at hlt
  set C := cornerVerts X F
  have hmem : ∀ v ∈ C, v ∈ Sset X ∧ v ∉ Dset X ∧ (∃ z, IsRung F v z) ∧ deg2 X v ≠ 1 := by
    intro v hv
    obtain ⟨hv, hd⟩ := mem_filter.1 hv
    obtain ⟨hv, hz⟩ := mem_filter.1 hv
    exact ⟨(mem_sdiff.1 hv).1, (mem_sdiff.1 hv).2, hz, hd⟩
  have hK : ∀ v ∈ C, v ∈ KBall X := fun v hv =>
    ball_polygon_a (Sset_sub (hmem v hv).1) (hmem v hv).2.1
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.1 (by omega : 1 < C.card)
  have hint := KBall_interior_nonempty (hK a ha) (hK b hb) hab
  have hXne : X.Nonempty := ⟨a, Sset_sub (hmem a ha).1⟩
  have hconv := KBall_convex X
  have hcomp := KBall_isCompact hXne
  set γ : Pt → Set Pt := fun v => (fun _ : ℝ => v) '' Set.Icc 0 0
  have hγ : ∀ v, γ v = {v} := fun v => (Set.nonempty_Icc.2 le_rfl).image_const v
  have hsum := turning_sum_le hconv hcomp C γ
    (fun v hv => by rw [hγ]; exact Set.singleton_subset_iff.2 (ball_polygon_b (hmem v hv).1
      (hmem v hv).2.1)) (fun v _ => by rw [hγ]; exact isClosed_singleton) 1
    (fun x => by
      refine card_le_one.2 fun v hv v' hv' => ?_
      have h1 := (mem_filter.1 hv).2
      have h2 := (mem_filter.1 hv').2
      rw [hγ, Set.mem_singleton_iff] at h1 h2
      rw [← h1, ← h2])
  have hlow : ∀ v ∈ C, 2 * π / 7 < turning (KBall X) (γ v) := by
    intro v hv
    obtain ⟨hvS, hvD, ⟨z, hr⟩, hd⟩ := hmem v hv
    have hpne : (partners X (dist2 X) v).Nonempty := (mem_filter.1 hvS).2
    have h1 : 1 < (partners X (dist2 X) v).card := by
      have := hpne.card_pos; unfold deg2 at hd; omega
    obtain ⟨w', hw', hne⟩ := exists_mem_ne h1 (F.partner v)
    obtain ⟨hw'X, -, hw'v⟩ := mem_filter.1 hw'
    have hcor := corner_lemma hX F hτ₁ hτ₂ hr hw'X hw'v hne
    have hpos := hX.dist2_pos
    have hn₁ : -F.u v ∈ normalCone (KBall X) v := by
      unfold DirField.u
      exact neg_mem_normalCone (hK v hv) (F.partner_mem v hvS) (F.partner_K v hvS hvD) _
        (inv_nonneg.2 dist_nonneg)
    have hn₂ : -((dist2 X)⁻¹ • (w' - v)) ∈ normalCone (KBall X) v :=
      neg_mem_normalCone (hK v hv) hw'X hw'v _ (inv_nonneg.2 hpos.le)
    have hu := F.norm_u hvS
    have hu' : ‖(dist2 X)⁻¹ • (w' - v)‖ = 1 := by
      rw [norm_smul, ← dist_eq_norm, dist_comm, hw'v, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hpos), inv_mul_cancel₀ hpos.ne']
    have hfr : γ v ⊆ frontier (KBall X) := by
      rw [hγ]; exact Set.singleton_subset_iff.2 (ball_polygon_b hvS hvD)
    have hta := turning_ge_angle hconv hcomp hint (γ := fun _ : ℝ => v) (le_refl (0 : ℝ))
      continuousOn_const hfr hn₁ hn₂
      (neg_ne_zero.2 (norm_ne_zero_iff.1 (by rw [hu]; norm_num)))
      (neg_ne_zero.2 (norm_ne_zero_iff.1 (by rw [hu']; norm_num)))
    unfold ang at hta hcor
    rw [InnerProductGeometry.angle_neg_neg] at hta
    exact hcor.trans_le hta
  have := sum_lt_sum_of_nonempty ⟨a, ha⟩ hlow
  rw [sum_const, nsmul_eq_mul] at this
  have h7 : (7 : ℝ) ≤ C.card := by exact_mod_cast hlt
  have hπ := Real.pi_pos
  push_cast at hsum
  nlinarith

/-- A K-vertex has at most two rungs (the positions `v + o_±`), so `#rungs ≤ 2 #rungVerts`.

TODO: none — proved.
Acceptance: no `sorry`.
Depends on: `rung_offset`. Difficulty M. -/
theorem card_rungs_le (hX : Normal X) (F : DirField X) :
    (rungs X F).card ≤ 2 * (rungVerts X F).card := by
  classical
  let f : Sym2 Pt → Pt := fun e =>
    if h : ∃ v w, e = s(v, w) ∧ IsRung F v w then h.choose else 0
  have hf : ∀ e, (h : ∃ v w, e = s(v, w) ∧ IsRung F v w) →
      ∃ w, e = s(f e, w) ∧ IsRung F (f e) w := by
    intro e h
    have : f e = h.choose := dif_pos h
    rw [this]; exact h.choose_spec
  refine card_le_mul_card_image_of_maps_to (f := f) ?_ 2 ?_
  · intro e he
    obtain ⟨w, -, hr⟩ := hf e (mem_filter.1 he).2
    exact mem_filter.2 ⟨mem_sdiff.2 ⟨hr.1, hr.2.1⟩, w, hr⟩
  · intro v _
    let o : ℝ → Pt := fun σ => v + ((-tau X) • F.u v + (σ * sOff X) • perp (F.u v))
    have hsub : (rungs X F).filter (fun e => f e = v) ⊆ {s(v, o 1), s(v, o (-1))} := by
      intro e he
      obtain ⟨he, hfe⟩ := mem_filter.1 he
      obtain ⟨w, hew, hr⟩ := hf e (mem_filter.1 he).2
      rw [hfe] at hew hr
      obtain ⟨σ, hσ, ho⟩ := rung_offset F hr
      have hw : w = o σ := by simp only [o]; rw [← ho]; abel
      rw [hew, hw]
      rcases hσ with rfl | rfl <;> simp
    exact (card_le_card hsub).trans (card_le_two)

/-- `rungVerts = P₁ ⊔ corners`.

TODO: none — proved (Phase 2).
Acceptance: no `sorry`.
Depends on: definitions. Difficulty S. -/
theorem card_rungVerts (F : DirField X) :
    (rungVerts X F).card = (P1set X F).card + (cornerVerts X F).card := by
  rw [P1set, cornerVerts, card_filter_add_card_filter_not]

/-- **Region III** (§7.3): `e(S) ≤ |S| + 2|P₁| + C` with `P₁ ⊆ S` of `Δ₂`-degree 1.

TODO: none (wiring).
Acceptance: no `sorry` (inherits).
Depends on: `good_subset_T_union_rungs`, `card_tEdges_le`, `card_rungs_le`, `card_rungVerts`,
`card_cornerVerts_le`, `card_good_add_bad`, `card_bad_le`, `two_beta_lt_of`. -/
theorem regionIII (hX : Normal X) (F : DirField X) (hτ₁ : √3 / 2 - 2 * beta < tau X)
    (hτ₂ : tau X < √3 / 2 + 3 * beta) :
    ∃ P₁ ⊆ Sset X, (∀ v ∈ P₁, deg2 X v = 1) ∧
      (eS X : ℝ) ≤ (Sset X).card + 2 * P₁.card + (cBad + 100) := by
  refine ⟨P1set X F, fun v hv => ?_, fun v hv => (mem_filter.1 hv).2, ?_⟩
  · exact (mem_sdiff.1 (mem_filter.1 (mem_filter.1 hv).1).1).1
  have hsub := good_subset_T_union_rungs hX F (two_beta_lt_of hτ₁)
  have hg := (card_le_card hsub).trans (card_union_le _ _)
  have hT := card_tEdges_le hX F
  have hR := card_rungs_le hX F
  have hV := card_rungVerts F
  have hC := card_cornerVerts_le hX F hτ₁ hτ₂
  have hgood : ((good X F).card : ℝ) ≤ (Sset X).card + 2 * (P1set X F).card + 12 := by
    exact_mod_cast (show (good X F).card ≤ (Sset X).card + 2 * (P1set X F).card + 12 by omega)
  have h3 := card_bad_le hX F
  have : (eS X : ℝ) = (good X F).card + (bad X F).card := by
    exact_mod_cast (card_good_add_bad F).symm
  linarith

end

end Erdos132Main
