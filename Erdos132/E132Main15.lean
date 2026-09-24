import Erdos132.E132Main
import Erdos132.E132Main15N1
import Erdos132.E132Main15RegionII
import Erdos132.E132Main15RegionIII

/-!
# Erdős Problem 132 — `min{μ(Δ₂), μ(δ)} ≤ (15/11)n + C₀` (assembly)

`angle_R4.md` §4 (Theorem R4).  In the nondegenerate regime every `τ`-region gives
`e(S) ≤ |S| + |Q| + cReg` with `Q ⊆ S` of `Δ₂`-degree 1; Theorem N1 gives
`μ(δ) ≤ e(S) + 5r + cN1`; weighted (VS) gives `μ(Δ₂) ≤ |Q| + (3/2)(|S| − |Q|)`; the LP with
weights `8/11, 3/11` (`lp15`) gives `(15/11)(s + r) + C`.

| regime (δ = 1, β = 1/100) | `e(S) ≤` | source |
|---|---|---|
| `n ≤ 3`, degenerate, small `Δ₂` | — | as in `erdos132_main` |
| I: `τ ≤ √3/2 − 2β` | `|S| + C` (`Q = ∅`) | `regionI` |
| III: `√3/2 − 2β < τ < √3/2 + 3β` | `|S| + |P₁| + C` | `regionIII15` |
| II: `√3/2 + 3β ≤ τ ≤ 1` | `|S| + |P₁| + C` | `regionII15` |
| II-high: `τ > 1` | `|S| + C` (`Q = ∅`) | `regionII_high` |
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

/-- LP step of the `15/11` theorem in the nondegenerate regime.

TODO: none — proved.
Acceptance: no `sorry` (inherits `E_bound15`).
Depends on: `VS_weighted`, `E_bound15`, `lp15`, `card_S_add_R`. -/
theorem assemble15 {Y : Finset Pt} (hN : Normal Y) {Q : Finset Pt} (hQS : Q ⊆ Sset Y)
    (hQ : ∀ v ∈ Q, deg2 Y v = 1) (he : (eS Y : ℝ) ≤ (Sset Y).card + Q.card + cReg) :
    min (mult Y (dist2 Y) : ℝ) (mult Y (minDist Y)) ≤ 15 / 11 * Y.card + 3 / 11 * (cN1 + cReg) := by
  have hsr : ((Sset Y).card : ℝ) + (Rset Y).card = Y.card := by exact_mod_cast card_S_add_R Y
  have hsp : ((Sset Y \ Q).card : ℝ) + Q.card = (Sset Y).card := by
    exact_mod_cast card_sdiff_add_card_eq_card hQS
  have h₂ := VS_weighted hQS hQ
  have h₂' : (mult Y (dist2 Y) : ℝ) ≤ Q.card + 3 / 2 * ((Sset Y).card - Q.card) := by linarith
  have h := lp15 (Nat.cast_nonneg Q.card) h₂' (E_bound15 hN) he
  rw [hsr] at h
  exact h

/-- The main theorem for a normalised set (`δ = 1`).

TODO: none — proved from the statements.
Acceptance: no `sorry` (inherits). -/
theorem main15_normalized (Y : Finset Pt) (h1 : minDist Y = 1) :
    min (mult Y (dist2 Y) : ℝ) (mult Y (minDist Y)) ≤ 15 / 11 * Y.card + C₀ := by
  have hn0 : (0 : ℝ) ≤ Y.card := Nat.cast_nonneg _
  have hC := consts15
  have hN₀ : (0 : ℝ) ≤ N₀ := by norm_num [N₀]
  have hcN : (0 : ℝ) ≤ cN1 := by norm_num [cN1]
  have hcR : (0 : ℝ) ≤ cReg := by norm_num [cReg, cBad]
  have hm₂ := min_le_left (mult Y (dist2 Y) : ℝ) (mult Y (minDist Y))
  have hmδ := min_le_right (mult Y (dist2 Y) : ℝ) (mult Y (minDist Y))
  have hδ3 := mult_minDist_le Y
  -- `n ≤ 3`
  by_cases h4 : Y.card < 4
  · have : (Y.card : ℝ) ≤ 3 := by exact_mod_cast Nat.lt_succ_iff.1 h4
    have : (10 : ℝ) ≤ C₀ := by norm_num [C₀]
    linarith
  rw [not_lt] at h4
  -- degenerate regime
  by_cases hd : 1.94 * dist2 Y < diam Y
  · have := degenerate h4 hd
    have : (1 : ℝ) ≤ C₀ := by norm_num [C₀]
    linarith
  rw [not_lt] at hd
  -- nondegenerate, small `Δ₂`
  by_cases hs : dist2 Y < 10 ^ 4
  · have := card_lt_N0 h1 hd hs
    linarith
  rw [not_lt] at hs
  -- nondegenerate, large: regions
  have hN : Normal Y := ⟨h4, h1, hd, hs⟩
  obtain ⟨F⟩ := dirField_nonempty Y
  have hcb : (0 : ℝ) ≤ cBad := by norm_num [cBad]
  have fin : ∀ {Q : Finset Pt}, Q ⊆ Sset Y → (∀ v ∈ Q, deg2 Y v = 1) →
      (eS Y : ℝ) ≤ (Sset Y).card + Q.card + cReg →
      min (mult Y (dist2 Y) : ℝ) (mult Y (minDist Y)) ≤ 15 / 11 * Y.card + C₀ := by
    intro Q hQS hQ he
    have := assemble15 hN hQS hQ he
    linarith
  have hP1 : P1set Y F ⊆ Sset Y := fun v hv =>
    (mem_sdiff.1 (mem_filter.1 (mem_filter.1 hv).1).1).1
  have hP1d : ∀ v ∈ P1set Y F, deg2 Y v = 1 := fun v hv => (mem_filter.1 hv).2
  by_cases hI : tau Y ≤ √3 / 2 - 2 * beta
  · refine fin (Q := ∅) (empty_subset _) (by simp) ?_
    have := regionI hN F hI
    simp only [card_empty, Nat.cast_zero, add_zero]
    unfold cReg; linarith
  rw [not_le] at hI
  by_cases hIII : tau Y < √3 / 2 + 3 * beta
  · exact fin hP1 hP1d (regionIII15 hN F hI hIII)
  rw [not_lt] at hIII
  by_cases hhigh : 1 < tau Y
  · refine fin (Q := ∅) (empty_subset _) (by simp) ?_
    have := regionII_high hN F hhigh
    simp only [card_empty, Nat.cast_zero, add_zero]
    unfold cReg; linarith
  rw [not_lt] at hhigh
  exact fin hP1 hP1d (regionII15 hN F hIII hhigh)

/-- **Erdős #132 / CDL Problem 1.6 upper bound, improved** (`angle_R4.md`, Theorem R4):
there is an absolute `C₀` with `min{μ(Δ₂), μ(δ)} ≤ (15/11)n + C₀` for every `n`-point planar
set, `n ≥ 2`.  Hence `L ≤ 15/11 < 54/37`.

TODO: none — proved from the lemma statements.
Acceptance: no `sorry` (inherits the lemma sorries until Phase 2 is complete). -/
theorem erdos132_main15 :
    ∃ C₀ : ℝ, ∀ X : Finset Pt, 2 ≤ X.card →
      (min (mult X (dist2 X)) (mult X (minDist X)) : ℝ) ≤ 15 / 11 * X.card + C₀ := by
  refine ⟨C₀, fun X hX => ?_⟩
  obtain ⟨Y, hc, h1, hm₂, hmδ⟩ := exists_normalize hX
  rw [← hm₂, ← hmδ, ← hc]
  exact main15_normalized Y h1

end Erdos132Main

#print axioms Erdos132Main.erdos132_main15
