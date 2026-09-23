import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Analysis.InnerProductSpace.Convex
import Std.Tactic.BVDecide

/-!
# Erdős Problem 132, convex case: `n = 7` and `n = 11`

A strictly convex `n`-gon `p : Fin n → ℝ²` (vertices listed in counter-clockwise order, every
triple `i < j < k` positively oriented) has at least three distances that each occur at most
`n` times among the `C(n,2)` vertex pairs.  This file proves it for `n = 7` and `n = 11`
(Theorems 7 and 11 of `problems/132/angle_B3.md`).

Proof architecture (see `problems/132/lean/README.md`):

1. **Geometry (Lemma Q).**  For `i < j < k < l` the diagonals of the convex quadrilateral meet
   at an interior point `O`, so `|ik| + |jl| > |ij| + |kl|` and `> |jk| + |il|`.
2. **Ordinal reduction.**  Colour each pair by the rank of its distance.  Lemma Q becomes the
   ordinal condition `QOrd`.  Lemma R (counting) bounds the number of distinct distances by `Dm`
   when at most two distances are rare.  `OrdNoCE n Dm` says: every `QOrd` colouring with
   colours `< Dm` has at least three rare colour classes.
3. **Certificate.**  `OrdNoCE n Dm` is reduced (with a Lean-proved encoding lemma) to a pure
   `BitVec` statement `BVNoCE`, discharged by `bv_decide`: CaDiCaL produces an LRAT proof and
   Lean's *verified* LRAT checker (`Std.Tactic.BVDecide`) checks it.  The only trusted step is
   the compiled evaluation of that checker, which `bv_decide` records as an auxiliary axiom
   `…._native.bv_decide.ax_…` stating `verifyBVExpr expr cert = true` (disclosed; this is the
   same trust base as `native_decide`).
-/

open Finset

set_option maxRecDepth 100000

namespace Erdos132Convex

/-! ## Geometry -/

/-- Points of the Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- Twice the signed area of the triangle `abc` (positive iff counter-clockwise). -/
noncomputable def orient (a b c : Pt) : ℝ :=
  (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)

/-- `p` lists the vertices of a strictly convex polygon in counter-clockwise order:
every index-increasing triple is positively oriented. -/
def StrictConvexPolygon {n : ℕ} (p : Fin n → Pt) : Prop :=
  ∀ i j k : Fin n, i < j → j < k → 0 < orient (p i) (p j) (p k)

/-- Coordinates of a point of the line through `a, b`. -/
theorem lineMap_apply' (a b : Pt) (u : ℝ) (i : Fin 2) :
    (AffineMap.lineMap a b u : Pt) i = a i + u * (b i - a i) := by
  rw [AffineMap.lineMap_apply]
  simp [vsub_eq_sub, vadd_eq_add]
  ring

/-- `orient` vanishes on a point of the line through `a, b`. -/
theorem orient_lineMap (a b : Pt) (u : ℝ) : orient a b (AffineMap.lineMap a b u) = 0 := by
  simp only [orient, lineMap_apply']; ring

/-- `orient x y ·` is affine along a segment. -/
theorem orient_lineMap_right (x y a c : Pt) (t : ℝ) :
    orient x y (AffineMap.lineMap a c t) = (1 - t) * orient x y a + t * orient x y c := by
  simp only [orient, lineMap_apply']; ring

/-- Strict triangle inequality when `o` is not on the line `ab` (detected by orientation). -/
theorem dist_lt_of_orient_ne {a b o : Pt} (h : orient a b o ≠ 0) :
    dist a b < dist a o + dist o b := by
  refine lt_of_le_of_ne (dist_triangle a o b) (fun he => h ?_)
  obtain ⟨u, -, hu⟩ := (dist_add_dist_eq_iff (a := a) (b := o) (c := b)).1 he.symm
  rw [← hu, orient_lineMap]

/-- A point of the segment `ab` splits `dist a b`. -/
theorem dist_lineMap_add (a b : Pt) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    dist a (AffineMap.lineMap a b t) + dist (AffineMap.lineMap a b t) b = dist a b :=
  (dist_add_dist_eq_iff).2 ⟨t, ⟨h0, h1⟩, rfl⟩

/-- **Quadrilateral inequality** for a positively oriented convex quadrilateral `ABCE`.
The diagonals meet at `O = lineMap A C t = lineMap B E s` with `0 < s, t < 1`, and `O` lies on
none of the four side lines. -/
theorem quad_ineq {A B C E : Pt} (h1 : 0 < orient A B C) (h2 : 0 < orient A B E)
    (h3 : 0 < orient A C E) (h4 : 0 < orient B C E) :
    dist A B + dist C E < dist A C + dist B E ∧ dist B C + dist A E < dist A C + dist B E := by
  set t := orient A B E / (orient A B E + orient B C E) with ht
  set s := orient A B C / (orient A B C + orient A C E) with hs
  have ht0 : 0 < t := div_pos h2 (by linarith)
  have ht1 : t < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hs0 : 0 < s := div_pos h1 (by linarith)
  have hs1 : s < 1 := (div_lt_one (by linarith)).2 (by linarith)
  set O := AffineMap.lineMap A C t with hO
  have hO' : O = AffineMap.lineMap B E s := by
    have hsum : orient A B E + orient B C E = orient A B C + orient A C E := by
      simp only [orient]; ring
    ext i
    fin_cases i
    all_goals
      simp only [hO, lineMap_apply', ht, hs, Fin.zero_eta, Fin.mk_one]
      rw [hsum]
      field_simp
      simp only [orient]
      ring
  have eAC := dist_lineMap_add A C ht0.le ht1.le
  have eBE := dist_lineMap_add B E hs0.le hs1.le
  rw [← hO'] at eBE
  rw [← hO] at eAC
  have sAB : dist A B < dist A O + dist O B := dist_lt_of_orient_ne (by
    rw [hO, orient_lineMap_right]
    have : orient A B A = 0 := by simp only [orient]; ring
    rw [this]; positivity)
  have sCE : dist C E < dist C O + dist O E := dist_lt_of_orient_ne (by
    rw [hO, orient_lineMap_right]
    have : orient C E C = 0 := by simp only [orient]; ring
    have h' : orient C E A = orient A C E := by simp only [orient]; ring
    rw [this, h']
    have : 0 < 1 - t := by linarith
    positivity)
  have sBC : dist B C < dist B O + dist O C := dist_lt_of_orient_ne (by
    rw [hO, orient_lineMap_right]
    have : orient B C C = 0 := by simp only [orient]; ring
    have h' : orient B C A = orient A B C := by simp only [orient]; ring
    rw [this, h']
    have : 0 < 1 - t := by linarith
    positivity)
  have sAE : dist A E < dist A O + dist O E := dist_lt_of_orient_ne (by
    rw [hO, orient_lineMap_right]
    have : orient A E A = 0 := by simp only [orient]; ring
    have h' : orient A E C = - orient A C E := by simp only [orient]; ring
    rw [this, h']
    have : 0 < t * orient A C E := by positivity
    linarith)
  have d1 := dist_comm O B
  have d2 := dist_comm C O
  constructor <;> linarith

/-- **Lemma Q** for a strictly convex polygon. -/
theorem lemmaQ {n : ℕ} {p : Fin n → Pt} (hp : StrictConvexPolygon p) {i j k l : Fin n}
    (hij : i < j) (hjk : j < k) (hkl : k < l) :
    dist (p i) (p j) + dist (p k) (p l) < dist (p i) (p k) + dist (p j) (p l) ∧
    dist (p j) (p k) + dist (p i) (p l) < dist (p i) (p k) + dist (p j) (p l) :=
  quad_ineq (hp i j k hij hjk) (hp i j l hij (hjk.trans hkl)) (hp i k l (hij.trans hjk) hkl)
    (hp j k l hjk hkl)

/-! ## Distances, multiplicities, the target statement -/

/-- The vertex pairs `i < j`. -/
def pairsF (n : ℕ) : Finset (Fin n × Fin n) := univ.filter (fun e => e.1 < e.2)

/-- The set of distinct distances. -/
noncomputable def distSet {n : ℕ} (p : Fin n → Pt) : Finset ℝ :=
  (pairsF n).image (fun e => dist (p e.1) (p e.2))

/-- Multiplicity of the distance `d`: the number of pairs `i < j` at distance `d`. -/
noncomputable def mult {n : ℕ} (p : Fin n → Pt) (d : ℝ) : ℕ := by
  classical exact ((pairsF n).filter (fun e => dist (p e.1) (p e.2) = d)).card

/-- The *rare* distances: those occurring at most `n` times (and at least once). -/
noncomputable def rareDists {n : ℕ} (p : Fin n → Pt) : Finset ℝ := by
  classical exact (distSet p).filter (fun d => mult p d ≤ n)

/-! ## The ordinal model -/

/-- Ordinal quadrilateral condition for diagonal colours `a, b` and opposite-side colours
`s, t`: the diagonals are not dominated by the sides under either matching. -/
def Qc (a b s t : ℕ) : Prop := ¬ (a ≤ s ∧ b ≤ t) ∧ ¬ (a ≤ t ∧ b ≤ s)

/-- A colouring of the pairs `i < j` satisfies the ordinal Lemma Q. -/
def QOrd (n : ℕ) (c : Fin n → Fin n → ℕ) : Prop :=
  ∀ i j k l : Fin n, i < j → j < k → k < l →
    Qc (c i k) (c j l) (c i j) (c k l) ∧ Qc (c i k) (c j l) (c j k) (c i l)

/-- Size of colour class `t`. -/
def cnt (n : ℕ) (c : Fin n → Fin n → ℕ) (t : ℕ) : ℕ :=
  ((pairsF n).filter (fun e => c e.1 e.2 = t)).card

/-- **No `(n, ≤ Dm)` ordinal counterexample**: every `QOrd` colouring with colours `< Dm`
has at least three colours whose class size lies in `[1, n]`. -/
def OrdNoCE (n Dm : ℕ) : Prop :=
  ∀ c : Fin n → Fin n → ℕ, (∀ i j : Fin n, i < j → c i j < Dm) → QOrd n c →
    3 ≤ ((range Dm).filter (fun t => 1 ≤ cnt n c t ∧ cnt n c t ≤ n)).card

/-- Rank of a real number `d` among the distinct distances: `#{d' ∈ distSet p : d' < d}`. -/
noncomputable def rk {n : ℕ} (p : Fin n → Pt) (d : ℝ) : ℕ :=
  ((distSet p).filter (· < d)).card

/-- Rank of the distance of the pair `(i, j)` among all distinct distances. -/
noncomputable def rank {n : ℕ} (p : Fin n → Pt) (i j : Fin n) : ℕ :=
  rk p (dist (p i) (p j))

/-- Pairs `i < j` realise elements of `distSet`. -/
theorem dist_mem_distSet {n : ℕ} (p : Fin n → Pt) {i j : Fin n} (h : i < j) :
    dist (p i) (p j) ∈ distSet p :=
  mem_image.2 ⟨(i, j), by simp [pairsF, h], rfl⟩

/-- `rk` is an order embedding on `distSet`. -/
theorem rk_le_iff {n : ℕ} (p : Fin n → Pt) {x y : ℝ} (hy : y ∈ distSet p) :
    rk p x ≤ rk p y ↔ x ≤ y := by
  constructor
  · intro h
    by_contra hxy
    replace hxy := not_le.1 hxy
    have : (distSet p).filter (· < y) ⊂ (distSet p).filter (· < x) := by
      refine ⟨fun d hd => ?_, fun hsub => ?_⟩
      · simp only [mem_filter] at hd ⊢; exact ⟨hd.1, hd.2.trans hxy⟩
      · have := hsub (mem_filter.2 ⟨hy, hxy⟩)
        simp at this
    exact absurd (card_lt_card this) (not_lt.2 h)
  · intro h
    exact card_le_card (fun d hd => by
      simp only [mem_filter] at hd ⊢; exact ⟨hd.1, hd.2.trans_le h⟩)

/-- Rank comparison is distance comparison (for `k < l`). -/
theorem rank_le_iff {n : ℕ} (p : Fin n → Pt) (i j : Fin n) {k l : Fin n} (hkl : k < l) :
    rank p i j ≤ rank p k l ↔ dist (p i) (p j) ≤ dist (p k) (p l) :=
  rk_le_iff p (dist_mem_distSet p hkl)

/-- Ranks of pairs are `< #distSet`. -/
theorem rank_lt_card {n : ℕ} (p : Fin n → Pt) {i j : Fin n} (h : i < j) :
    rank p i j < (distSet p).card := by
  refine card_lt_card ⟨filter_subset _ _, fun hsub => ?_⟩
  have := hsub (dist_mem_distSet p h)
  simp at this

/-- The rank colouring of a strictly convex polygon satisfies the ordinal Lemma Q. -/
theorem qord_rank {n : ℕ} {p : Fin n → Pt} (hp : StrictConvexPolygon p) : QOrd n (rank p) := by
  intro i j k l hij hjk hkl
  have hik := hij.trans hjk
  have hjl := hjk.trans hkl
  have hil := hik.trans hkl
  obtain ⟨q1, q2⟩ := lemmaQ hp hij hjk hkl
  simp only [Qc, rank_le_iff p _ _ hij, rank_le_iff p _ _ hkl, rank_le_iff p _ _ hjk,
    rank_le_iff p _ _ hil]
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩ <;> linarith [h.1, h.2]

/-- The multiplicities sum to the number of pairs. -/
theorem sum_mult {n : ℕ} (p : Fin n → Pt) : ∑ d ∈ distSet p, mult p d = (pairsF n).card := by
  classical
  rw [card_eq_sum_card_image (fun e : Fin n × Fin n => dist (p e.1) (p e.2)) (pairsF n)]
  rfl

/-- **Lemma R**: with at most two rare distances, `(D - 2)(n + 1) ≤ #pairs`. -/
theorem lemmaR {n : ℕ} (p : Fin n → Pt) (h : (rareDists p).card ≤ 2) :
    ((distSet p).card - 2) * (n + 1) ≤ (pairsF n).card := by
  classical
  set S := distSet p
  set NR := S.filter (fun d => ¬ mult p d ≤ n)
  have hsplit : (rareDists p).card + NR.card = S.card := by
    unfold rareDists; exact card_filter_add_card_filter_not _
  have h1 : NR.card * (n + 1) ≤ ∑ d ∈ NR, mult p d := by
    rw [← smul_eq_mul]
    exact card_nsmul_le_sum _ _ _ (fun d hd => by
      have := (mem_filter.1 hd).2; omega)
  have h2 : ∑ d ∈ NR, mult p d ≤ ∑ d ∈ S, mult p d :=
    sum_le_sum_of_subset (filter_subset _ _)
  rw [sum_mult] at h2
  calc (S.card - 2) * (n + 1) ≤ NR.card * (n + 1) := Nat.mul_le_mul_right _ (by omega)
    _ ≤ _ := h1.trans h2

/-- Transfer: if `D ≤ Dm` and there is no ordinal counterexample, there are `≥ 3` rare
distances.  Every rare colour `t` is the rank of a rare distance. -/
theorem rare_of_ord {n Dm : ℕ} {p : Fin n → Pt} (hp : StrictConvexPolygon p)
    (hD : (distSet p).card ≤ Dm) (h : OrdNoCE n Dm) : 3 ≤ (rareDists p).card := by
  classical
  have h3 := h (rank p) (fun i j hij => (rank_lt_card p hij).trans_le hD) (qord_rank hp)
  refine h3.trans ((card_le_card fun t ht => ?_).trans (card_image_le (f := rk p)))
  obtain ⟨-, hc1, hcn⟩ := mem_filter.1 ht
  obtain ⟨⟨i, j⟩, hij, rfl⟩ : ∃ e ∈ pairsF n, rank p e.1 e.2 = t := by
    obtain ⟨e, he⟩ := card_pos.1 (by omega : 0 < cnt n (rank p) t)
    exact ⟨e, (mem_filter.1 he).1, (mem_filter.1 he).2⟩
  have hij' : i < j := (mem_filter.1 hij).2
  refine mem_image.2 ⟨dist (p i) (p j), ?_, rfl⟩
  refine mem_filter.2 ⟨dist_mem_distSet p hij', ?_⟩
  have : (pairsF n).filter (fun e => dist (p e.1) (p e.2) = dist (p i) (p j)) =
      (pairsF n).filter (fun e => rank p e.1 e.2 = rank p i j) := by
    refine filter_congr fun e he => ?_
    have he' : e.1 < e.2 := (mem_filter.1 he).2
    rw [le_antisymm_iff, le_antisymm_iff, rank_le_iff p _ _ hij', rank_le_iff p _ _ he']
  unfold mult
  convert hcn using 1
  rw [this]
  rfl

/-- Geometry + Lemma R + the ordinal statement give the theorem. -/
theorem main_of_ord {n Dm : ℕ} {p : Fin n → Pt} (hp : StrictConvexPolygon p)
    (hDm : (pairsF n).card < (Dm - 1) * (n + 1)) (h : OrdNoCE n Dm) :
    3 ≤ (rareDists p).card := by
  by_cases hD : (distSet p).card ≤ Dm
  · exact rare_of_ord hp hD h
  · by_contra h3
    have := lemmaR p (by omega)
    have := Nat.lt_of_mul_lt_mul_right (this.trans_lt hDm)
    omega

/-! ## The `BitVec` encoding

Colours are `BitVec 3`, class sizes `BitVec 8`, the number of rare classes `BitVec 4`.  The
pair / quadruple lists are explicit literals so that `simp` can unfold everything into a
quantifier-free `BitVec` formula for `bv_decide`. -/

/-- Size of colour class `t`, as an 8-bit sum over the list `L` of pairs. -/
def cntBV {n : ℕ} (L : List (Fin n × Fin n)) (x : Fin n → Fin n → BitVec 3) (t : BitVec 3) :
    BitVec 8 :=
  L.foldr (fun e acc => (if x e.1 e.2 = t then 1 else 0) + acc) 0

/-- Colour `t` is rare: class size in `[1, n]`. -/
def rareBV {n : ℕ} (L : List (Fin n × Fin n)) (x : Fin n → Fin n → BitVec 3) (t : BitVec 3) :
    Bool :=
  (cntBV L x t != 0) && decide (cntBV L x t ≤ BitVec.ofNat 8 n)

/-- Number of rare colours among `0, …, Dm - 1`. -/
def rareSumBV {n : ℕ} (L : List (Fin n × Fin n)) (x : Fin n → Fin n → BitVec 3) (Dm : ℕ) :
    BitVec 4 :=
  (List.range Dm).foldr (fun t acc => (if rareBV L x (BitVec.ofNat 3 t) = true then 1 else 0) + acc) 0

/-- Lemma Q (all four matchings) on one quadruple, `BitVec` version. -/
def QBV {n : ℕ} (x : Fin n → Fin n → BitVec 3) (q : Fin n × Fin n × Fin n × Fin n) : Prop :=
  ¬ (x q.1 q.2.2.1 ≤ x q.1 q.2.1 ∧ x q.2.1 q.2.2.2 ≤ x q.2.2.1 q.2.2.2) ∧
  ¬ (x q.1 q.2.2.1 ≤ x q.2.2.1 q.2.2.2 ∧ x q.2.1 q.2.2.2 ≤ x q.1 q.2.1) ∧
  ¬ (x q.1 q.2.2.1 ≤ x q.2.1 q.2.2.1 ∧ x q.2.1 q.2.2.2 ≤ x q.1 q.2.2.2) ∧
  ¬ (x q.1 q.2.2.1 ≤ x q.1 q.2.2.2 ∧ x q.2.1 q.2.2.2 ≤ x q.2.1 q.2.2.1)

/-- `BitVec` form of "no ordinal counterexample" for explicit pair / quadruple lists. -/
def BVNoCE (n Dm : ℕ) (L : List (Fin n × Fin n)) (Qs : List (Fin n × Fin n × Fin n × Fin n)) :
    Prop :=
  ∀ x : Fin n → Fin n → BitVec 3, (∀ e ∈ L, x e.1 e.2 < BitVec.ofNat 3 Dm) →
    (∀ q ∈ Qs, QBV x q) → rareSumBV L x Dm ≤ 2 → False

/-- A fold of `0/1` indicators computes `countP`, as long as there is no overflow. -/
theorem foldr_ite_toNat {α : Type*} (w : ℕ) (P : α → Prop) [DecidablePred P] (L : List α)
    (h : L.length < 2 ^ w) :
    (L.foldr (fun e acc => (if P e then (1 : BitVec w) else 0) + acc) 0).toNat =
      L.countP (fun e => decide (P e)) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.length_cons] at h
    have hc := List.countP_le_length (p := fun e => decide (P e)) (l := L)
    simp only [List.foldr_cons, BitVec.toNat_add, ih (by omega), List.countP_cons]
    have hw : 2 ≤ 2 ^ w := by omega
    have h1 : (1 : BitVec w).toNat = 1 := by
      rw [show (1 : BitVec w) = BitVec.ofNat w 1 from rfl, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have h0 : (0 : BitVec w).toNat = 0 := by
      rw [show (0 : BitVec w) = BitVec.ofNat w 0 from rfl, BitVec.toNat_ofNat, Nat.zero_mod]
    by_cases hp : P a
    · simp only [hp, ite_true, decide_true, h1]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · simp only [hp, ite_false, decide_false, h0]
      rw [Nat.mod_eq_of_lt (by omega)]
      simp

/-- `countP` over a duplicate-free list is a finset cardinality. -/
theorem countP_eq_card {α : Type*} [DecidableEq α] (P : α → Prop) [DecidablePred P]
    {M : List α} (hM : M.Nodup) :
    M.countP (fun e => decide (P e)) = (M.toFinset.filter P).card := by
  rw [List.countP_eq_length_filter, Finset.card_def, Finset.filter_val, List.toFinset_val,
    List.dedup_eq_self.2 hM, Multiset.filter_coe, Multiset.coe_card]

/-- 3-bit literals compare like naturals below `8`. -/
theorem ofNat3_le_iff {a b : ℕ} (ha : a < 8) (hb : b < 8) :
    BitVec.ofNat 3 a ≤ BitVec.ofNat 3 b ↔ a ≤ b := by
  rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by simpa using ha), Nat.mod_eq_of_lt (by simpa using hb)]

/-- 3-bit literals are equal iff the naturals are (below `8`). -/
theorem ofNat3_eq_iff {a b : ℕ} (ha : a < 8) (hb : b < 8) :
    BitVec.ofNat 3 a = BitVec.ofNat 3 b ↔ a = b := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by simpa using ha), Nat.mod_eq_of_lt (by simpa using hb)]

/-- All pairs `i < j` of `Fin n`, generated. -/
def pairsGen (n : Nat) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i => ((List.finRange n).filter (fun j => decide (i < j))).map (fun j => (i, j))

/-- Membership in `pairsGen`. -/
theorem mem_pairsGen {n : Nat} (e : Fin n × Fin n) : e ∈ pairsGen n ↔ e.1 < e.2 := by
  obtain ⟨a, b⟩ := e
  simp [pairsGen]

/-- `pairsGen` has no duplicates. -/
theorem nodup_pairsGen (n : Nat) : (pairsGen n).Nodup := by
  unfold pairsGen
  refine List.nodup_flatMap.2 ⟨fun i _ => ?_, ?_⟩
  · exact ((List.nodup_finRange n).filter _).map (fun a b h => (Prod.ext_iff.1 h).2)
  · refine (List.nodup_finRange n).pairwise_of_forall_ne fun i _ j _ hij => ?_
    simp only [Function.onFun]
    rw [List.disjoint_left]
    intro e h1 h2
    simp only [List.mem_map] at h1 h2
    obtain ⟨_, _, rfl⟩ := h1
    obtain ⟨_, _, h⟩ := h2
    exact hij (Prod.ext_iff.1 h).1.symm


/-- All quadruples `i < j < k < l` of `Fin n`, generated. -/
def quadsGen (n : Nat) : List (Fin n × Fin n × Fin n × Fin n) :=
  (pairsGen n).flatMap fun a => ((pairsGen n).filter (fun b => decide (a.2 < b.1))).map
    (fun b => (a.1, a.2, b.1, b.2))

/-- Members of `quadsGen` are increasing. -/
theorem quadsGen_inc {n : Nat} (q) (h : q ∈ quadsGen n) :
    q.1 < q.2.1 ∧ q.2.1 < q.2.2.1 ∧ q.2.2.1 < q.2.2.2 := by
  simp only [quadsGen, List.mem_flatMap, List.mem_map, List.mem_filter, mem_pairsGen,
    decide_eq_true_eq] at h
  obtain ⟨a, ha, b, ⟨hb, hab⟩, rfl⟩ := h
  exact ⟨ha, hab, hb⟩


/-- **Encoding correctness**: the `BitVec` statement implies the ordinal one.  A `QOrd`
colouring `c` gives the `BitVec` model `x i j = c i j` (as a 3-bit number); its class sizes and
rare-class count are computed without overflow. -/
theorem ordNoCE_of_bv {n Dm : ℕ} {L : List (Fin n × Fin n)}
    {Qs : List (Fin n × Fin n × Fin n × Fin n)}
    (hL' : L = pairsGen n) (hQs : Qs = quadsGen n) (hlen : L.length < 256) (hn : n < 256)
    (hDm : Dm < 8) (h : BVNoCE n Dm L Qs) : OrdNoCE n Dm := by
  classical
  have hL : ∀ e, e ∈ L ↔ e.1 < e.2 := fun e => hL' ▸ mem_pairsGen e
  have hnd : L.Nodup := hL' ▸ nodup_pairsGen n
  have hQ : ∀ q ∈ Qs, q.1 < q.2.1 ∧ q.2.1 < q.2.2.1 ∧ q.2.2.1 < q.2.2.2 :=
    fun q hq => quadsGen_inc q (hQs ▸ hq)
  intro c hc hq
  by_contra h3
  have hc8 : ∀ i j : Fin n, i < j → c i j < 8 := fun i j hij => (hc i j hij).trans hDm
  have hpairs : pairsF n = L.toFinset := by
    ext e; simp [pairsF, hL]
  let x : Fin n → Fin n → BitVec 3 := fun i j => BitVec.ofNat 3 (c i j)
  -- class sizes
  have hcnt : ∀ t, t < 8 → (cntBV L x (BitVec.ofNat 3 t)).toNat = cnt n c t := by
    intro t ht
    rw [cntBV, foldr_ite_toNat 8 _ L (by simpa using hlen), cnt, hpairs,
      ← countP_eq_card _ hnd]
    refine List.countP_congr fun e he => ?_
    simp only [x, decide_eq_true_eq]
    exact ofNat3_eq_iff (hc8 _ _ ((hL e).1 he)) ht
  have hrare : ∀ t, t < 8 →
      (rareBV L x (BitVec.ofNat 3 t) = true ↔ 1 ≤ cnt n c t ∧ cnt n c t ≤ n) := by
    intro t ht
    rw [← hcnt t ht]
    simp only [rareBV, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, BitVec.le_def,
      BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, ← BitVec.toNat_inj]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  refine h x (fun e he => ?_) (fun q hqm => ?_) ?_
  · have := hc _ _ ((hL e).1 he)
    rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by simpa using this.trans hDm), Nat.mod_eq_of_lt (by simpa using hDm)]
    exact this
  · obtain ⟨h1, h2, h3⟩ := hQ q hqm
    obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := hq _ _ _ _ h1 h2 h3
    have hik := h1.trans h2
    have hjl := h2.trans h3
    have hil := hik.trans h3
    simp only [QBV, x, ofNat3_le_iff (hc8 _ _ hik) (hc8 _ _ h1),
      ofNat3_le_iff (hc8 _ _ hik) (hc8 _ _ h3), ofNat3_le_iff (hc8 _ _ hik) (hc8 _ _ h2),
      ofNat3_le_iff (hc8 _ _ hik) (hc8 _ _ hil), ofNat3_le_iff (hc8 _ _ hjl) (hc8 _ _ h1),
      ofNat3_le_iff (hc8 _ _ hjl) (hc8 _ _ h3), ofNat3_le_iff (hc8 _ _ hjl) (hc8 _ _ h2),
      ofNat3_le_iff (hc8 _ _ hjl) (hc8 _ _ hil)]
    exact ⟨a1, a2, b1, b2⟩
  · have hsum : (rareSumBV L x Dm).toNat =
        ((range Dm).filter (fun t => 1 ≤ cnt n c t ∧ cnt n c t ≤ n)).card := by
      rw [rareSumBV, foldr_ite_toNat 4 _ _ (by simp; omega), ← List.toFinset_range,
        ← countP_eq_card _ (List.nodup_range)]
      refine List.countP_congr fun t ht => ?_
      simp only [decide_eq_true_eq]
      exact hrare t ((List.mem_range.1 ht).trans hDm)
    rw [BitVec.le_def, hsum]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat]
    omega

/-! ## Explicit pair and quadruple lists (generated) -/

/-- The 21 pairs `i < j` of `Fin 7`, lexicographic. -/
def pairs7 : List (Fin 7 × Fin 7) :=
    [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (1, 3), (1, 4), (1, 5),
    (1, 6), (2, 3), (2, 4), (2, 5), (2, 6), (3, 4), (3, 5), (3, 6), (4, 5), (4, 6),
    (5, 6)]

/-- The 35 quadruples `i < j < k < l` of `Fin 7`, lexicographic. -/
def quads7 : List (Fin 7 × Fin 7 × Fin 7 × Fin 7) :=
    [(0, 1, 2, 3), (0, 1, 2, 4), (0, 1, 2, 5), (0, 1, 2, 6), (0, 1, 3, 4), (0, 1, 3, 5),
    (0, 1, 3, 6), (0, 1, 4, 5), (0, 1, 4, 6), (0, 1, 5, 6), (0, 2, 3, 4), (0, 2, 3, 5),
    (0, 2, 3, 6), (0, 2, 4, 5), (0, 2, 4, 6), (0, 2, 5, 6), (0, 3, 4, 5), (0, 3, 4, 6),
    (0, 3, 5, 6), (0, 4, 5, 6), (1, 2, 3, 4), (1, 2, 3, 5), (1, 2, 3, 6), (1, 2, 4, 5),
    (1, 2, 4, 6), (1, 2, 5, 6), (1, 3, 4, 5), (1, 3, 4, 6), (1, 3, 5, 6), (1, 4, 5, 6),
    (2, 3, 4, 5), (2, 3, 4, 6), (2, 3, 5, 6), (2, 4, 5, 6), (3, 4, 5, 6)]

/-- The 55 pairs `i < j` of `Fin 11`, lexicographic. -/
def pairs11 : List (Fin 11 × Fin 11) :=
    [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10),
    (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, 3),
    (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 4), (3, 5), (3, 6),
    (3, 7), (3, 8), (3, 9), (3, 10), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10),
    (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 7), (6, 8), (6, 9), (6, 10), (7, 8),
    (7, 9), (7, 10), (8, 9), (8, 10), (9, 10)]

/-- The 330 quadruples `i < j < k < l` of `Fin 11`, lexicographic. -/
def quads11 : List (Fin 11 × Fin 11 × Fin 11 × Fin 11) :=
    [(0, 1, 2, 3), (0, 1, 2, 4), (0, 1, 2, 5), (0, 1, 2, 6), (0, 1, 2, 7), (0, 1, 2, 8),
    (0, 1, 2, 9), (0, 1, 2, 10), (0, 1, 3, 4), (0, 1, 3, 5), (0, 1, 3, 6), (0, 1, 3, 7),
    (0, 1, 3, 8), (0, 1, 3, 9), (0, 1, 3, 10), (0, 1, 4, 5), (0, 1, 4, 6), (0, 1, 4, 7),
    (0, 1, 4, 8), (0, 1, 4, 9), (0, 1, 4, 10), (0, 1, 5, 6), (0, 1, 5, 7), (0, 1, 5, 8),
    (0, 1, 5, 9), (0, 1, 5, 10), (0, 1, 6, 7), (0, 1, 6, 8), (0, 1, 6, 9), (0, 1, 6, 10),
    (0, 1, 7, 8), (0, 1, 7, 9), (0, 1, 7, 10), (0, 1, 8, 9), (0, 1, 8, 10), (0, 1, 9, 10),
    (0, 2, 3, 4), (0, 2, 3, 5), (0, 2, 3, 6), (0, 2, 3, 7), (0, 2, 3, 8), (0, 2, 3, 9),
    (0, 2, 3, 10), (0, 2, 4, 5), (0, 2, 4, 6), (0, 2, 4, 7), (0, 2, 4, 8), (0, 2, 4, 9),
    (0, 2, 4, 10), (0, 2, 5, 6), (0, 2, 5, 7), (0, 2, 5, 8), (0, 2, 5, 9), (0, 2, 5, 10),
    (0, 2, 6, 7), (0, 2, 6, 8), (0, 2, 6, 9), (0, 2, 6, 10), (0, 2, 7, 8), (0, 2, 7, 9),
    (0, 2, 7, 10), (0, 2, 8, 9), (0, 2, 8, 10), (0, 2, 9, 10), (0, 3, 4, 5), (0, 3, 4, 6),
    (0, 3, 4, 7), (0, 3, 4, 8), (0, 3, 4, 9), (0, 3, 4, 10), (0, 3, 5, 6), (0, 3, 5, 7),
    (0, 3, 5, 8), (0, 3, 5, 9), (0, 3, 5, 10), (0, 3, 6, 7), (0, 3, 6, 8), (0, 3, 6, 9),
    (0, 3, 6, 10), (0, 3, 7, 8), (0, 3, 7, 9), (0, 3, 7, 10), (0, 3, 8, 9), (0, 3, 8, 10),
    (0, 3, 9, 10), (0, 4, 5, 6), (0, 4, 5, 7), (0, 4, 5, 8), (0, 4, 5, 9), (0, 4, 5, 10),
    (0, 4, 6, 7), (0, 4, 6, 8), (0, 4, 6, 9), (0, 4, 6, 10), (0, 4, 7, 8), (0, 4, 7, 9),
    (0, 4, 7, 10), (0, 4, 8, 9), (0, 4, 8, 10), (0, 4, 9, 10), (0, 5, 6, 7), (0, 5, 6, 8),
    (0, 5, 6, 9), (0, 5, 6, 10), (0, 5, 7, 8), (0, 5, 7, 9), (0, 5, 7, 10), (0, 5, 8, 9),
    (0, 5, 8, 10), (0, 5, 9, 10), (0, 6, 7, 8), (0, 6, 7, 9), (0, 6, 7, 10), (0, 6, 8, 9),
    (0, 6, 8, 10), (0, 6, 9, 10), (0, 7, 8, 9), (0, 7, 8, 10), (0, 7, 9, 10), (0, 8, 9, 10),
    (1, 2, 3, 4), (1, 2, 3, 5), (1, 2, 3, 6), (1, 2, 3, 7), (1, 2, 3, 8), (1, 2, 3, 9),
    (1, 2, 3, 10), (1, 2, 4, 5), (1, 2, 4, 6), (1, 2, 4, 7), (1, 2, 4, 8), (1, 2, 4, 9),
    (1, 2, 4, 10), (1, 2, 5, 6), (1, 2, 5, 7), (1, 2, 5, 8), (1, 2, 5, 9), (1, 2, 5, 10),
    (1, 2, 6, 7), (1, 2, 6, 8), (1, 2, 6, 9), (1, 2, 6, 10), (1, 2, 7, 8), (1, 2, 7, 9),
    (1, 2, 7, 10), (1, 2, 8, 9), (1, 2, 8, 10), (1, 2, 9, 10), (1, 3, 4, 5), (1, 3, 4, 6),
    (1, 3, 4, 7), (1, 3, 4, 8), (1, 3, 4, 9), (1, 3, 4, 10), (1, 3, 5, 6), (1, 3, 5, 7),
    (1, 3, 5, 8), (1, 3, 5, 9), (1, 3, 5, 10), (1, 3, 6, 7), (1, 3, 6, 8), (1, 3, 6, 9),
    (1, 3, 6, 10), (1, 3, 7, 8), (1, 3, 7, 9), (1, 3, 7, 10), (1, 3, 8, 9), (1, 3, 8, 10),
    (1, 3, 9, 10), (1, 4, 5, 6), (1, 4, 5, 7), (1, 4, 5, 8), (1, 4, 5, 9), (1, 4, 5, 10),
    (1, 4, 6, 7), (1, 4, 6, 8), (1, 4, 6, 9), (1, 4, 6, 10), (1, 4, 7, 8), (1, 4, 7, 9),
    (1, 4, 7, 10), (1, 4, 8, 9), (1, 4, 8, 10), (1, 4, 9, 10), (1, 5, 6, 7), (1, 5, 6, 8),
    (1, 5, 6, 9), (1, 5, 6, 10), (1, 5, 7, 8), (1, 5, 7, 9), (1, 5, 7, 10), (1, 5, 8, 9),
    (1, 5, 8, 10), (1, 5, 9, 10), (1, 6, 7, 8), (1, 6, 7, 9), (1, 6, 7, 10), (1, 6, 8, 9),
    (1, 6, 8, 10), (1, 6, 9, 10), (1, 7, 8, 9), (1, 7, 8, 10), (1, 7, 9, 10), (1, 8, 9, 10),
    (2, 3, 4, 5), (2, 3, 4, 6), (2, 3, 4, 7), (2, 3, 4, 8), (2, 3, 4, 9), (2, 3, 4, 10),
    (2, 3, 5, 6), (2, 3, 5, 7), (2, 3, 5, 8), (2, 3, 5, 9), (2, 3, 5, 10), (2, 3, 6, 7),
    (2, 3, 6, 8), (2, 3, 6, 9), (2, 3, 6, 10), (2, 3, 7, 8), (2, 3, 7, 9), (2, 3, 7, 10),
    (2, 3, 8, 9), (2, 3, 8, 10), (2, 3, 9, 10), (2, 4, 5, 6), (2, 4, 5, 7), (2, 4, 5, 8),
    (2, 4, 5, 9), (2, 4, 5, 10), (2, 4, 6, 7), (2, 4, 6, 8), (2, 4, 6, 9), (2, 4, 6, 10),
    (2, 4, 7, 8), (2, 4, 7, 9), (2, 4, 7, 10), (2, 4, 8, 9), (2, 4, 8, 10), (2, 4, 9, 10),
    (2, 5, 6, 7), (2, 5, 6, 8), (2, 5, 6, 9), (2, 5, 6, 10), (2, 5, 7, 8), (2, 5, 7, 9),
    (2, 5, 7, 10), (2, 5, 8, 9), (2, 5, 8, 10), (2, 5, 9, 10), (2, 6, 7, 8), (2, 6, 7, 9),
    (2, 6, 7, 10), (2, 6, 8, 9), (2, 6, 8, 10), (2, 6, 9, 10), (2, 7, 8, 9), (2, 7, 8, 10),
    (2, 7, 9, 10), (2, 8, 9, 10), (3, 4, 5, 6), (3, 4, 5, 7), (3, 4, 5, 8), (3, 4, 5, 9),
    (3, 4, 5, 10), (3, 4, 6, 7), (3, 4, 6, 8), (3, 4, 6, 9), (3, 4, 6, 10), (3, 4, 7, 8),
    (3, 4, 7, 9), (3, 4, 7, 10), (3, 4, 8, 9), (3, 4, 8, 10), (3, 4, 9, 10), (3, 5, 6, 7),
    (3, 5, 6, 8), (3, 5, 6, 9), (3, 5, 6, 10), (3, 5, 7, 8), (3, 5, 7, 9), (3, 5, 7, 10),
    (3, 5, 8, 9), (3, 5, 8, 10), (3, 5, 9, 10), (3, 6, 7, 8), (3, 6, 7, 9), (3, 6, 7, 10),
    (3, 6, 8, 9), (3, 6, 8, 10), (3, 6, 9, 10), (3, 7, 8, 9), (3, 7, 8, 10), (3, 7, 9, 10),
    (3, 8, 9, 10), (4, 5, 6, 7), (4, 5, 6, 8), (4, 5, 6, 9), (4, 5, 6, 10), (4, 5, 7, 8),
    (4, 5, 7, 9), (4, 5, 7, 10), (4, 5, 8, 9), (4, 5, 8, 10), (4, 5, 9, 10), (4, 6, 7, 8),
    (4, 6, 7, 9), (4, 6, 7, 10), (4, 6, 8, 9), (4, 6, 8, 10), (4, 6, 9, 10), (4, 7, 8, 9),
    (4, 7, 8, 10), (4, 7, 9, 10), (4, 8, 9, 10), (5, 6, 7, 8), (5, 6, 7, 9), (5, 6, 7, 10),
    (5, 6, 8, 9), (5, 6, 8, 10), (5, 6, 9, 10), (5, 7, 8, 9), (5, 7, 8, 10), (5, 7, 9, 10),
    (5, 8, 9, 10), (6, 7, 8, 9), (6, 7, 8, 10), (6, 7, 9, 10), (6, 8, 9, 10), (7, 8, 9, 10)]


/-! ## The certificates (`bv_decide`) -/

/-- `n = 7`: no ordinal counterexample with `≤ 4` colours.  The LRAT proof (found by `bv_decide?`,
~1 s of SAT) is pinned in `lrat/bvNoCE7.lrat` (1.6 MB), so only the verified checker runs. -/
theorem bvNoCE7 : BVNoCE 7 4 pairs7 quads7 := by
  intro x h1 h2 h3
  simp only [pairs7, quads7, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true,
    QBV, rareSumBV, rareBV, cntBV, List.foldr_cons, List.foldr_nil, List.range_succ,
    List.range_zero, List.nil_append, List.cons_append, and_true] at h1 h2 h3
  bv_check "lrat/bvNoCE7.lrat"

/-- `n = 11`: no ordinal counterexample with `≤ 6` colours (`bv_decide`, ~20 s of SAT). -/
theorem bvNoCE11 : BVNoCE 11 6 pairs11 quads11 := by
  intro x h1 h2 h3
  simp only [pairs11, quads11, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff,
    implies_true, QBV, rareSumBV, rareBV, cntBV, List.foldr_cons, List.foldr_nil, List.range_succ,
    List.range_zero, List.nil_append, List.cons_append, and_true] at h1 h2 h3
  bv_decide (config := { timeout := 3000 })

theorem ordNoCE7 : OrdNoCE 7 4 :=
  ordNoCE_of_bv (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) bvNoCE7

theorem ordNoCE11 : OrdNoCE 11 6 :=
  ordNoCE_of_bv (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) bvNoCE11

/-! ## Main theorems -/

/-- **Theorem 7.** A strictly convex 7-gon has at least three distances occurring at most 7
times. -/
theorem erdos132_convex7 (p : Fin 7 → Pt) (hp : StrictConvexPolygon p) :
    3 ≤ (rareDists p).card :=
  main_of_ord (Dm := 4) hp (by decide) ordNoCE7

/-- **Theorem 11.** A strictly convex 11-gon has at least three distances occurring at most 11
times. -/
theorem erdos132_convex11 (p : Fin 11 → Pt) (hp : StrictConvexPolygon p) :
    3 ≤ (rareDists p).card :=
  main_of_ord (Dm := 6) hp (by decide) ordNoCE11

end Erdos132Convex

#print axioms Erdos132Convex.erdos132_convex7
#print axioms Erdos132Convex.erdos132_convex11
