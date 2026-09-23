import Erdos132.E132Convex
import Mathlib.Analysis.Convex.Independent
import Mathlib.Data.Finset.Sym

/-!
# Erdős Problem 132, convex case: statements for finite point sets

`E132Convex.lean` proves the `n = 7, 11` results for an *ordered* strictly convex polygon
`p : Fin n → ℝ²` (every index-increasing triple positively oriented).  This file removes the
ordering: for a finite set `S ⊆ ℝ²` in convex position,

* convex position is Mathlib's `ConvexIndependent ℝ ((↑) : S → ℝ²)` (no point of `S` lies in the
  convex hull of the others);
* distances are counted over **unordered** pairs `{x, y} ⊆ S`, `x ≠ y` (as non-diagonal elements
  of `S.sym2`), and a distance `d` is *rare* if `1 ≤ #{pairs at distance d} ≤ #S`.

**Bridge** (`exists_strictConvexPolygon`).  Fix any `p₀ ∈ S`.  On `S \ {p₀}` the relation
`a ≺ b :⇔ 0 < orient p₀ a b` is a strict total order:
* total, because three distinct points of `S` are never collinear (the middle one would lie in
  the segment of the other two);
* transitive, because `a ≺ b ≺ c ⪯ a` would put `p₀` in the triangle `abc`.
Listing `p₀` followed by `S \ {p₀}` in `≺`-increasing order gives a strictly convex polygon: for
`a ≺ b ≺ c`, `orient a b c ≤ 0` would put `b` in the triangle `p₀ a c`.
-/

open Finset

namespace Erdos132Convex

/-! ## Convex-hull membership from coordinates -/

/-- A convex combination (given coordinatewise) of `A, B, C` lies in their convex hull. -/
theorem mem_hull3 {P A B C : Pt} {w0 w1 w2 : ℝ} (h0 : 0 ≤ w0) (h1 : 0 ≤ w1) (h2 : 0 ≤ w2)
    (hs : w0 + w1 + w2 = 1) (hx : P 0 = w0 * A 0 + w1 * B 0 + w2 * C 0)
    (hy : P 1 = w0 * A 1 + w1 * B 1 + w2 * C 1) :
    P ∈ convexHull ℝ ({A, B, C} : Set Pt) := by
  have hP : P = w0 • A + w1 • B + w2 • C := by
    ext i
    fin_cases i
    · simp [hx]
    · simp [hy]
  rw [hP]
  have := (convex_convexHull ℝ ({A, B, C} : Set Pt)).sum_mem (t := Finset.univ)
    (w := ![w0, w1, w2]) (z := ![A, B, C]) ?_ ?_ ?_
  · simpa [Fin.sum_univ_three, add_assoc] using this
  · intro i _; fin_cases i <;> simp [h0, h1, h2]
  · simp [Fin.sum_univ_three, hs]
  · intro i _; fin_cases i <;> exact subset_convexHull ℝ _ (by simp)

/-- Barycentric coordinates: if `P` is on the inner side of all three sides of the positively
oriented triangle `ABC`, then `P ∈ conv{A, B, C}`. -/
theorem hull_of_orient {P A B C : Pt} (h1 : 0 ≤ orient P B C) (h2 : 0 ≤ orient A P C)
    (h3 : 0 ≤ orient A B P) (hD : 0 < orient A B C) :
    P ∈ convexHull ℝ ({A, B, C} : Set Pt) := by
  have hsum : orient P B C + orient A P C + orient A B P = orient A B C := by
    simp only [orient]; ring
  refine mem_hull3 (w0 := orient P B C / orient A B C) (w1 := orient A P C / orient A B C)
    (w2 := orient A B P / orient A B C) (div_nonneg h1 hD.le) (div_nonneg h2 hD.le)
    (div_nonneg h3 hD.le) ?_ ?_ ?_
  · rw [← add_div, ← add_div, hsum, div_self hD.ne']
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
      ← add_div, eq_div_iff hD.ne']
    simp only [orient]; ring
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
      ← add_div, eq_div_iff hD.ne']
    simp only [orient]; ring

/-! ## Consequences of convex position -/

/-- Convex position, in the "not in the hull of the others" form. -/
def NotInHull (S : Finset Pt) : Prop := ∀ x ∈ S, x ∉ convexHull ℝ ((S : Set Pt) \ {x})

theorem notInHull_of_convexIndependent {S : Finset Pt}
    (hS : ConvexIndependent ℝ ((↑) : S → Pt)) : NotInHull S := by
  exact convexIndependent_set_iff_notMem_convexHull_sdiff.1 hS

/-- A point of `S` is not in the hull of three other points of `S`. -/
theorem not_mem_hull3 {S : Finset Pt} (hS : NotInHull S) {P A B C : Pt} (hP : P ∈ S)
    (hA : A ∈ S) (hB : B ∈ S) (hC : C ∈ S) (hPA : P ≠ A) (hPB : P ≠ B) (hPC : P ≠ C) :
    P ∉ convexHull ℝ ({A, B, C} : Set Pt) := by
  intro h
  refine hS P hP (convexHull_mono ?_ h)
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨mem_coe.2 hA, fun h => hPA (Set.mem_singleton_iff.1 h).symm⟩
  · exact ⟨mem_coe.2 hB, fun h => hPB (Set.mem_singleton_iff.1 h).symm⟩
  · exact ⟨mem_coe.2 hC, fun h => hPC (Set.mem_singleton_iff.1 h).symm⟩

/-- No three distinct points of a convex-position set are collinear. -/
theorem orient_ne_zero {S : Finset Pt} (hS : NotInHull S) {x y z : Pt} (hx : x ∈ S)
    (hy : y ∈ S) (hz : z ∈ S) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    orient x y z ≠ 0 := by
  intro hc
  simp only [orient] at hc
  have hN : 0 < (y 0 - x 0) ^ 2 + (y 1 - x 1) ^ 2 := by
    by_contra hle
    apply hxy
    have h0 : y 0 - x 0 = 0 := by nlinarith [sq_nonneg (y 0 - x 0), sq_nonneg (y 1 - x 1)]
    have h1 : y 1 - x 1 = 0 := by nlinarith [sq_nonneg (y 0 - x 0), sq_nonneg (y 1 - x 1)]
    ext i; fin_cases i
    · simp; linarith
    · simp; linarith
  set t := ((y 0 - x 0) * (z 0 - x 0) + (y 1 - x 1) * (z 1 - x 1)) /
    ((y 0 - x 0) ^ 2 + (y 1 - x 1) ^ 2) with ht
  have e0 : z 0 - x 0 = t * (y 0 - x 0) := by
    rw [ht, div_mul_eq_mul_div, eq_div_iff hN.ne']
    linear_combination (-(y 1 - x 1)) * hc
  have e1 : z 1 - x 1 = t * (y 1 - x 1) := by
    rw [ht, div_mul_eq_mul_div, eq_div_iff hN.ne']
    linear_combination (y 0 - x 0) * hc
  clear_value t
  rcases lt_or_ge t 0 with htn | htn
  · -- `x` lies between `z` and `y`
    have h1t : 0 < 1 - t := by linarith
    refine not_mem_hull3 hS hx hz hy hy hxz hxy hxy (mem_hull3 (w0 := 1 / (1 - t))
      (w1 := -t / (1 - t)) (w2 := 0) (by positivity) (div_nonneg (by linarith) h1t.le) le_rfl
      ?_ ?_ ?_)
    · rw [add_zero, ← add_div, div_eq_one_iff_eq h1t.ne']; ring
    · field_simp; linear_combination (-1 : ℝ) * e0
    · field_simp; linear_combination (-1 : ℝ) * e1
  rcases le_or_gt t 1 with ht1 | ht1
  · -- `z` lies between `x` and `y`
    refine not_mem_hull3 hS hz hx hy hy (Ne.symm hxz) (Ne.symm hyz) (Ne.symm hyz)
      (mem_hull3 (w0 := 1 - t) (w1 := t) (w2 := 0) (by linarith) htn le_rfl (by ring) ?_ ?_)
    · linear_combination e0
    · linear_combination e1
  · -- `y` lies between `x` and `z`
    have ht0 : 0 < t := by linarith
    refine not_mem_hull3 hS hy hx hz hz (Ne.symm hxy) hyz hyz (mem_hull3 (w0 := 1 - 1 / t)
      (w1 := 1 / t) (w2 := 0) ?_ (by positivity) le_rfl (by ring) ?_ ?_)
    · rw [sub_nonneg, div_le_one ht0]; exact ht1.le
    · field_simp; linear_combination (-1 : ℝ) * e0
    · field_simp; linear_combination (-1 : ℝ) * e1

/-! ## The angular order around a vertex -/

/-- Transitivity of `a ≺ b :⇔ 0 < orient p₀ a b` on a convex-position set. -/
theorem orient_trans {S : Finset Pt} (hS : NotInHull S) {p₀ a b c : Pt} (h₀ : p₀ ∈ S)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (ha₀ : a ≠ p₀) (hb₀ : b ≠ p₀) (hc₀ : c ≠ p₀)
    (hab : 0 < orient p₀ a b) (hbc : 0 < orient p₀ b c) : 0 < orient p₀ a c := by
  by_contra hac
  rw [not_lt] at hac
  have e2 : orient a p₀ c = - orient p₀ a c := by simp only [orient]; ring
  have e3 : orient a b p₀ = orient p₀ a b := by simp only [orient]; ring
  have e4 : orient a b c = orient p₀ b c + orient a p₀ c + orient a b p₀ := by
    simp only [orient]; ring
  exact not_mem_hull3 hS h₀ ha hb hc ha₀.symm hb₀.symm hc₀.symm
    (hull_of_orient hbc.le (by linarith) (by linarith) (by linarith))

/-- `≺`-increasing triples are positively oriented. -/
theorem orient_pos_of_lt {S : Finset Pt} (hS : NotInHull S) {p₀ a b c : Pt} (h₀ : p₀ ∈ S)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hb₀ : b ≠ p₀)
    (hab : 0 < orient p₀ a b) (hbc : 0 < orient p₀ b c) (hac : 0 < orient p₀ a c) :
    0 < orient a b c := by
  by_contra h
  rw [not_lt] at h
  have hba : b ≠ a := by
    rintro rfl
    have : orient p₀ b b = 0 := by simp only [orient]; ring
    linarith
  have hbc' : b ≠ c := by
    rintro rfl
    have : orient p₀ b b = 0 := by simp only [orient]; ring
    linarith
  have e1 : orient b a c = - orient a b c := by simp only [orient]; ring
  exact not_mem_hull3 hS hb h₀ ha hc hb₀ hba hbc'
    (hull_of_orient (by linarith) hbc.le hab.le hac)

/-- **Bridge.** A finite set in convex position can be listed as a strictly convex polygon. -/
theorem exists_strictConvexPolygon {S : Finset Pt} (hS : NotInHull S) :
    ∃ (m : ℕ) (p : Fin m → Pt), Function.Injective p ∧ Set.range p = ↑S ∧
      StrictConvexPolygon p := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨p₀, h₀⟩
  · exact ⟨0, Fin.elim0, fun i => i.elim0, by simp, fun i => i.elim0⟩
  set T := S.erase p₀ with hTdef
  have hT : ∀ a : T, (a : Pt) ∈ S ∧ (a : Pt) ≠ p₀ :=
    fun a => ⟨mem_of_mem_erase a.2, ne_of_mem_erase a.2⟩
  let r : T → T → Prop := fun a b => 0 < orient p₀ a b
  have hswap : ∀ a b : Pt, orient p₀ b a = - orient p₀ a b := fun a b => by
    simp only [orient]; ring
  have : IsStrictTotalOrder T r :=
    { irrefl := fun a h => by
        have h' : 0 < orient p₀ a a := h
        have : orient p₀ a a = 0 := by simp only [orient]; ring
        rw [this] at h'
        exact lt_irrefl _ h'
      trans := fun a b c hab hbc => orient_trans hS h₀ (hT a).1 (hT b).1 (hT c).1 (hT a).2
        (hT b).2 (hT c).2 hab hbc
      trichotomous := fun a b hab hba => by
        by_contra hne
        have h := orient_ne_zero hS h₀ (hT a).1 (hT b).1 (hT a).2.symm (hT b).2.symm
          (fun h => hne (Subtype.ext h))
        rcases lt_or_gt_of_ne h with h | h
        · exact hba (show 0 < orient p₀ b a by rw [hswap]; linarith)
        · exact hab h }
  let : LinearOrder T := linearOrderOfSTO r
  let e : Fin T.card ≃o T := Fintype.orderIsoFinOfCardEq T (Fintype.card_coe T)
  let f : Fin T.card → Pt := fun i => (e i : Pt)
  have hmono : ∀ i j, i < j → 0 < orient p₀ (f i) (f j) := fun i j h => e.lt_iff_lt.2 h
  refine ⟨T.card + 1, Fin.cons p₀ f, ?_, ?_, ?_⟩
  · refine Fin.cons_injective_iff.2 ⟨?_, fun i j h => e.injective (Subtype.ext h)⟩
    rintro ⟨i, hi⟩
    exact (hT (e i)).2 hi
  · have hf : Set.range f = ↑T := by
      ext x
      simp only [Set.mem_range, mem_coe, f]
      constructor
      · rintro ⟨i, rfl⟩; exact (e i).2
      · intro hx; exact ⟨e.symm ⟨x, hx⟩, by simp⟩
    rw [Fin.range_cons, hf, hTdef, coe_erase, Set.insert_sdiff_singleton,
      Set.insert_eq_of_mem (mem_coe.2 h₀)]
  · intro i j k hij hjk
    have hj0 : (0 : Fin _) < j := lt_of_le_of_lt (Fin.zero_le _) hij
    obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.2 hj0.ne'
    obtain ⟨k', rfl⟩ := Fin.exists_succ_eq.2 (hj0.trans hjk).ne'
    have hjk' : j' < k' := Fin.succ_lt_succ_iff.1 hjk
    cases i using Fin.cases with
    | zero => simpa only [Fin.cons_zero, Fin.cons_succ] using hmono j' k' hjk'
    | succ i' =>
      have hij' : i' < j' := Fin.succ_lt_succ_iff.1 hij
      simp only [Fin.cons_succ]
      exact orient_pos_of_lt hS h₀ (hT _).1 (hT _).1 (hT _).1 (hT _).2 (hmono _ _ hij')
        (hmono _ _ hjk') (hmono _ _ (hij'.trans hjk'))

/-! ## Distances of a finite set -/

/-- The distance between the two points of an unordered pair. -/
noncomputable def pairDist (z : Sym2 Pt) : ℝ :=
  Sym2.lift ⟨fun x y => dist x y, fun x y => dist_comm x y⟩ z

/-- The unordered pairs `{x, y} ⊆ S` with `x ≠ y`. -/
noncomputable def pairsS (S : Finset Pt) : Finset (Sym2 Pt) := by
  classical exact S.sym2.filter (fun z => ¬ z.IsDiag)

/-- Number of unordered pairs of `S` at distance `d`. -/
noncomputable def multS (S : Finset Pt) (d : ℝ) : ℕ := by
  classical exact ((pairsS S).filter (fun z => pairDist z = d)).card

/-- The distances determined by `S`. -/
noncomputable def distSetS (S : Finset Pt) : Finset ℝ := by
  classical exact (pairsS S).image pairDist

/-- The rare distances of `S`: determined by `S` (so `≥ 1` pair) and by at most `#S` pairs. -/
noncomputable def rareDistsS (S : Finset Pt) : Finset ℝ := by
  classical exact (distSetS S).filter (fun d => multS S d ≤ S.card)

/-- A listing of `S` has length `#S`. -/
theorem card_eq_of_listing {S : Finset Pt} {n : ℕ} {p : Fin n → Pt}
    (hinj : Function.Injective p) (hrange : Set.range p = ↑S) : S.card = n := by
  classical
  have : S = univ.image p := by
    apply coe_injective; rw [coe_image, coe_univ, Set.image_univ, hrange]
  rw [this, card_image_of_injective _ hinj, card_univ, Fintype.card_fin]

/-- For a listing `p` of `S`, the rare distances of `S` are those of `p`. -/
theorem rareDistsS_eq {S : Finset Pt} {n : ℕ} {p : Fin n → Pt} (hinj : Function.Injective p)
    (hrange : Set.range p = ↑S) : rareDistsS S = rareDists p := by
  classical
  have hmemS : ∀ x, x ∈ S ↔ ∃ i, p i = x := fun x => by
    rw [← mem_coe, ← hrange]; rfl
  let φ : Fin n × Fin n → Sym2 Pt := fun e => s(p e.1, p e.2)
  have hpairs : pairsS S = (pairsF n).image φ := by
    ext z
    induction z using Sym2.ind with
    | _ x y =>
    simp only [pairsS, mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff, mem_image,
      pairsF, mem_univ, true_and, φ, Sym2.eq_iff, Prod.exists]
    constructor
    · rintro ⟨⟨hx, hy⟩, hxy⟩
      obtain ⟨i, rfl⟩ := (hmemS x).1 hx
      obtain ⟨j, rfl⟩ := (hmemS y).1 hy
      rcases lt_or_gt_of_ne (fun h : i = j => hxy (h ▸ rfl)) with h | h
      · exact ⟨i, j, h, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨j, i, h, Or.inr ⟨rfl, rfl⟩⟩
    · rintro ⟨i, j, hij, h⟩
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨⟨(hmemS _).2 ⟨i, rfl⟩, (hmemS _).2 ⟨j, rfl⟩⟩, fun h => hij.ne (hinj h)⟩
      · exact ⟨⟨(hmemS _).2 ⟨j, rfl⟩, (hmemS _).2 ⟨i, rfl⟩⟩, fun h => hij.ne' (hinj h)⟩
  have hinjOn : Set.InjOn φ ↑(pairsF n) := by
    rintro ⟨i, j⟩ hij ⟨k, l⟩ hkl h
    simp only [pairsF, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hij hkl
    rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have a1 : i = k := hinj h1
      have a2 : j = l := hinj h2
      rw [a1, a2]
    · have a1 : i = l := hinj h1
      have a2 : j = k := hinj h2
      rw [a1, a2] at hij
      exact absurd (hij.trans hkl) (lt_irrefl _)
  have hdist : ∀ e, pairDist (φ e) = dist (p e.1) (p e.2) := fun e => rfl
  have hD : distSetS S = distSet p := by
    unfold distSetS distSet
    rw [hpairs, image_image]
    rfl
  have hmult : ∀ d, multS S d = mult p d := by
    intro d
    unfold multS mult
    rw [hpairs, filter_image, card_image_of_injOn (hinjOn.mono (coe_subset.2 (filter_subset _ _)))]
    congr 1
  unfold rareDistsS rareDists
  rw [hD, card_eq_of_listing hinj hrange]
  exact filter_congr fun d _ => by rw [hmult]

/-- Main theorems for point sets: from the ordered version and the bridge. -/
theorem finset_of_polygon {n : ℕ} (h : ∀ p : Fin n → Pt, StrictConvexPolygon p →
    3 ≤ (rareDists p).card) {S : Finset Pt} (hn : S.card = n)
    (hS : ConvexIndependent ℝ ((↑) : S → Pt)) : 3 ≤ (rareDistsS S).card := by
  obtain ⟨m, p, hinj, hrange, hp⟩ :=
    exists_strictConvexPolygon (notInHull_of_convexIndependent hS)
  obtain rfl : m = n := (card_eq_of_listing hinj hrange).symm.trans hn
  rw [rareDistsS_eq hinj hrange]
  exact h p hp

/-- **Theorem 7 (point sets).** Seven points in convex position determine at least three
distances that each occur for at least one and at most 7 of the 21 pairs. -/
theorem erdos132_convex7_finset (S : Finset Pt) (hn : S.card = 7)
    (hS : ConvexIndependent ℝ ((↑) : S → Pt)) : 3 ≤ (rareDistsS S).card :=
  finset_of_polygon erdos132_convex7 hn hS

/-- **Theorem 11 (point sets).** Eleven points in convex position determine at least three
distances that each occur for at least one and at most 11 of the 55 pairs. -/
theorem erdos132_convex11_finset (S : Finset Pt) (hn : S.card = 11)
    (hS : ConvexIndependent ℝ ((↑) : S → Pt)) : 3 ≤ (rareDistsS S).card :=
  finset_of_polygon erdos132_convex11 hn hS

end Erdos132Convex

#print axioms Erdos132Convex.erdos132_convex7_finset
#print axioms Erdos132Convex.erdos132_convex11_finset
