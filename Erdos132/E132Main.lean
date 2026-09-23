import Erdos132.E132MainRegions
import Erdos132.E132MainDegen

/-!
# Erdős Problem 132 — `min{μ(Δ₂), μ(δ)} ≤ (54/37)n + C₀` (assembly, §9)

The main theorem `erdos132_main` is **fully proved**: there are no `sorry`s in
`E132MainDefs / Local / Regions / Degen / ConvexCurve / Ve87`, and
`#print axioms erdos132_main` = `[propext, Classical.choice, Quot.sound]`.
`vesztergombi87` ([Ve87]) is proved (`E132Ve87.lean`), not assumed.

| regime (δ = 1, β = 1/100) | `e(S)` bound | `min{μ(Δ₂), μ(δ)} ≤` |
|---|---|---|
| `n ≤ 3` | — | `9` |
| degenerate `Δ > 1.94Δ₂`, `n ≥ 4` | — | `n + 1` |
| nondegenerate, `Δ₂ < 10⁴` | — | `3n < 3N₀` |
| I | `|S| + C` | `18n/13 + C` |
| III | `|S| + 2|P₁| + C` | `7n/5 + C` |
| II-rest | `(5/4)|S| + C` | `36n/25 + C` |
| II-res | `(4/3)|S| + C` | `54n/37 + C` |
| II-high | `|S| + C` | `18n/13 + C` |
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)

namespace Erdos132Main

/-- LP step in the nondegenerate regime for an `e(S) ≤ k|S| + C` bound, `0 ≤ k ≤ 4/3`. -/
theorem assemble_k {Y : Finset Pt} {k : ℝ} (hk0 : 0 ≤ k) (hk : k ≤ 4 / 3)
    (he : (eS Y : ℝ) ≤ k * (Sset Y).card + (cBad + 100)) :
    min (mult Y (dist2 Y) : ℝ) (mult Y (minDist Y)) ≤ 54 / 37 * Y.card + (cBad + 100) := by
  have hsr : ((Sset Y).card : ℝ) + (Rset Y).card = Y.card := by exact_mod_cast card_S_add_R Y
  have h := lp_mix hk0 (by linarith) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by norm_num [cBad]) (VS Y) (E_bound Y) he
  have hv := lp_value_le hk0 hk (Nat.cast_nonneg Y.card)
  rw [hsr] at h
  linarith

/-- The main theorem for a normalised set (`δ = 1`). -/
theorem main_normalized (Y : Finset Pt) (h1 : minDist Y = 1) :
    min (mult Y (dist2 Y) : ℝ) (mult Y (minDist Y)) ≤ 54 / 37 * Y.card + C₀ := by
  have hn0 : (0 : ℝ) ≤ Y.card := Nat.cast_nonneg _
  have hC : 3 * N₀ + (cBad + 100) ≤ C₀ := by norm_num [N₀, cBad, C₀]
  have hN₀ : (0 : ℝ) ≤ N₀ := by norm_num [N₀]
  have hC10 : (10 : ℝ) ≤ C₀ := by norm_num [C₀]
  have hCb0 : (0 : ℝ) ≤ cBad + 100 := by norm_num [cBad]
  have hm₂ := min_le_left (mult Y (dist2 Y) : ℝ) (mult Y (minDist Y))
  have hmδ := min_le_right (mult Y (dist2 Y) : ℝ) (mult Y (minDist Y))
  have hδ3 := mult_minDist_le Y
  -- `n ≤ 3`
  by_cases h4 : Y.card < 4
  · have : (Y.card : ℝ) ≤ 3 := by exact_mod_cast Nat.lt_succ_iff.1 h4
    linarith
  rw [not_lt] at h4
  -- degenerate regime
  by_cases hd : 1.94 * dist2 Y < diam Y
  · have := degenerate h4 hd
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
  have hCb : (0 : ℝ) ≤ cBad + 100 := by norm_num [cBad]
  by_cases hI : tau Y ≤ √3 / 2 - 2 * beta
  · have := assemble_k (k := 1) (by norm_num) (by norm_num) (by linarith [regionI hN F hI])
    linarith
  rw [not_le] at hI
  by_cases hIII : tau Y < √3 / 2 + 3 * beta
  · obtain ⟨P, hPS, hPdeg, he⟩ := regionIII hN F hI hIII
    have hsr : ((Sset Y).card : ℝ) + (Rset Y).card = Y.card := by exact_mod_cast card_S_add_R Y
    have hsp : ((Sset Y \ P).card : ℝ) + P.card = (Sset Y).card := by
      exact_mod_cast card_sdiff_add_card_eq_card hPS
    have hPs : (P.card : ℝ) ≤ (Sset Y).card := by exact_mod_cast card_le_card hPS
    have h₂ := VS_weighted hPS hPdeg
    have h₂' : (mult Y (dist2 Y) : ℝ) ≤ P.card + 3 / 2 * ((Sset Y).card - P.card) := by
      linarith
    have h := lp_weighted (Nat.cast_nonneg P.card) hPs (Nat.cast_nonneg (Rset Y).card) hCb
      h₂' (E_bound Y) he
    have h75 : (7 : ℝ) / 5 * Y.card ≤ 54 / 37 * Y.card := by nlinarith
    rw [hsr] at h
    linarith
  rw [not_lt] at hIII
  by_cases hhigh : 1 < tau Y
  · have := assemble_k (k := 1) (by norm_num) (by norm_num)
      (by linarith [regionII_high hN F hhigh])
    linarith
  rw [not_lt] at hhigh
  by_cases hrest : tau Y < Real.cos (beta / 2)
  · have := assemble_k (k := 5 / 4) (by norm_num) (by norm_num) (regionII_rest hN F hIII hrest)
    linarith
  rw [not_lt] at hrest
  have := assemble_k (k := 4 / 3) (by norm_num) (by norm_num) (regionII_res hN F hrest hhigh)
  linarith

/-- **Erdős #132 / CDL Problem 1.6 upper bound**: there is an absolute `C₀` with
`min{μ(Δ₂), μ(δ)} ≤ (54/37)n + C₀` for every `n`-point planar set, `n ≥ 2`.  Hence
`L ≤ 54/37 < 3/2`.

Assembly of §9 from the (fully proved) lemmas. -/
theorem erdos132_main :
    ∃ C₀ : ℝ, ∀ X : Finset Pt, 2 ≤ X.card →
      ((min (mult X (dist2 X)) (mult X (minDist X)) : ℕ) : ℝ) ≤ 54 / 37 * X.card + C₀ := by
  refine ⟨C₀, fun X hX => ?_⟩
  obtain ⟨Y, hc, h1, hm₂, hmδ⟩ := exists_normalize hX
  rw [← hm₂, ← hmδ, ← hc, Nat.cast_min]
  exact main_normalized Y h1

end Erdos132Main

#print axioms Erdos132Main.erdos132_main
