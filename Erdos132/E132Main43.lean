import Erdos132.E132Main15
import Erdos132.E132Main43Good
import Erdos132.E132Main43Classify
import Erdos132.E132Main43Charge

/-!
# Erdős Problem 132 — `min{μ(Δ₂), μ(δ)} ≤ (4/3)n + C` (Theorem N3 and assembly)

`angle_R6.md` §1 (Theorem N3, Corollary `L ≤ 4/3`).

* **Theorem N3** (`N3`): `Σ_{y∈R} v(y) ≤ 8|R| + 4|E43|`, by the charging lemma `charge_sum`
  with receivers `Low X y`: good heavy points have a frame (`frame_of_good`), are fans or caps
  (`heavy_type`) with `v ≤ 8 + |Low|` (`heavy_low`); receivers are in `R` with `v ≤ 7`
  (`low_receiver`) and private (`low_disjoint`); `|E43| ≤ cE43` (`card_E43_le`).
* `E_bound43`: `μ(δ) ≤ e(S) + 4r + 2cE43` (exact identity `mu_delta_identity`).
* Regions (unchanged from `15/11`): `e(S) ≤ |S| + |Q| + cReg` with `Q ⊆ S` of `Δ₂`-degree 1;
  weighted (VS): `μ(Δ₂) ≤ |Q| + (3/2)(|S| − |Q|)`; LP with weights `2/3, 1/3` (`lp43`).
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

variable {X : Finset Pt}

/-- **Theorem N3** (§1): `Σ_{y∈R} (deg y + m_y) ≤ 8|R| + 4|E43|`.

TODO: none — proved from the statements (wiring).
Acceptance: no `sorry` (inherits).
Depends on: `charge_sum`, `vR_le_twelve`, `frame_of_good`, `heavy_low`, `heavy_type`,
`low_receiver`, `low_disjoint`. -/
theorem N3 (hX : Normal X) :
    ∑ y ∈ Rset X, vR X y ≤ 8 * (Rset X).card + 4 * (E43 X).card := by
  have hE : E43 X ⊆ Rset X := fun y hy => (mem_filter.1 (mem_filter.1 hy).1).1
  have hgood : ∀ y ∈ Rset X \ E43 X, 9 ≤ vR X y → y ∈ heavy X ∧ IsGood43 X y := by
    intro y hy h9
    obtain ⟨hyR, hyE⟩ := mem_sdiff.1 hy
    have hh : y ∈ heavy X := mem_filter.2 ⟨hyR, h9⟩
    refine ⟨hh, ?_⟩
    by_contra hg
    exact hyE (mem_filter.2 ⟨hh, hg⟩)
  apply charge_sum (vR X) (Low X) (fun y _ => vR_le_twelve X y) hE
  · intro y hy h9
    obtain ⟨hh, hg⟩ := hgood y hy h9
    obtain ⟨n, hF⟩ := frame_of_good hX hh hg
    have hyR := (mem_sdiff.1 hy).1
    exact ⟨fun a ha => (low_receiver hX hF hyR ha).1, heavy_low hX hF hyR h9,
      fun a ha => (low_receiver hX hF hyR ha).2⟩
  · intro y hy h9 y' hy' h9' hne
    obtain ⟨hh, hg⟩ := hgood y hy h9
    obtain ⟨hh', hg'⟩ := hgood y' hy' h9'
    obtain ⟨n, hF⟩ := frame_of_good hX hh hg
    obtain ⟨n', hF'⟩ := frame_of_good hX hh' hg'
    have hyR := (mem_sdiff.1 hy).1
    have hyR' := (mem_sdiff.1 hy').1
    exact low_disjoint hX hF hF' hyR hyR' (heavy_type hX hF hyR h9)
      (heavy_type hX hF' hyR' h9') hne

/-- **(E″)** `μ(δ) ≤ e(S) + 4r + 2cE43`: the exact identity with Theorem N3.

TODO: none — proved from the statements (wiring).
Acceptance: no `sorry` (inherits).
Depends on: `mu_delta_identity`, `N3`, `card_E43_le`. -/
theorem E_bound43 (hX : Normal X) :
    (mult X (minDist X) : ℝ) ≤ eS X + 4 * (Rset X).card + 2 * cE43 := by
  have hid := mu_delta_identity X
  have hN : ∑ y ∈ Rset X, (degδ X y + mS X y) ≤ 8 * (Rset X).card + 4 * (E43 X).card :=
    N3 hX
  have hc := card_E43_le hX
  have h1 : 2 * mult X (minDist X) ≤ 2 * eS X + 8 * (Rset X).card + 4 * (E43 X).card := by
    omega
  have h2 : (2 * mult X (minDist X) : ℝ) ≤
      2 * eS X + 8 * (Rset X).card + 4 * (E43 X).card := by exact_mod_cast h1
  linarith

/-- LP step of the `4/3` theorem in the nondegenerate regime.

TODO: none — proved.
Acceptance: no `sorry` (inherits `E_bound43`).
Depends on: `VS_weighted`, `E_bound43`, `lp43`, `card_S_add_R`. -/
theorem assemble43 {Y : Finset Pt} (hN : Normal Y) {Q : Finset Pt} (hQS : Q ⊆ Sset Y)
    (hQ : ∀ v ∈ Q, deg2 Y v = 1) (he : (eS Y : ℝ) ≤ (Sset Y).card + Q.card + cReg) :
    min (mult Y (dist2 Y) : ℝ) (mult Y (minDist Y)) ≤
      4 / 3 * Y.card + 1 / 3 * (2 * cE43 + cReg) := by
  have hsr : ((Sset Y).card : ℝ) + (Rset Y).card = Y.card := by
    exact_mod_cast card_S_add_R Y
  have hsp : ((Sset Y \ Q).card : ℝ) + Q.card = (Sset Y).card := by
    exact_mod_cast card_sdiff_add_card_eq_card hQS
  have h₂ := VS_weighted hQS hQ
  have h₂' : (mult Y (dist2 Y) : ℝ) ≤ Q.card + 3 / 2 * ((Sset Y).card - Q.card) := by linarith
  have h := lp43 h₂' (E_bound43 hN) he
  rw [hsr] at h
  exact h

/-- The main theorem for a normalised set (`δ = 1`).

TODO: none — proved from the statements.
Acceptance: no `sorry` (inherits). -/
theorem main43_normalized (Y : Finset Pt) (h1 : minDist Y = 1) :
    min (mult Y (dist2 Y) : ℝ) (mult Y (minDist Y)) ≤ 4 / 3 * Y.card + C43 := by
  have hn0 : (0 : ℝ) ≤ Y.card := Nat.cast_nonneg _
  have hC := consts43
  have hN₀ : (0 : ℝ) ≤ N₀ := by norm_num [N₀]
  have hcE : (0 : ℝ) ≤ cE43 := by norm_num [cE43]
  have hcR : (0 : ℝ) ≤ cReg := by norm_num [cReg, cBad]
  have hm₂ := min_le_left (mult Y (dist2 Y) : ℝ) (mult Y (minDist Y))
  have hmδ := min_le_right (mult Y (dist2 Y) : ℝ) (mult Y (minDist Y))
  have hδ3 := mult_minDist_le Y
  -- `n ≤ 3`
  by_cases h4 : Y.card < 4
  · have : (Y.card : ℝ) ≤ 3 := by exact_mod_cast Nat.lt_succ_iff.1 h4
    have : (10 : ℝ) ≤ C43 := by norm_num [C43]
    linarith
  rw [not_lt] at h4
  -- degenerate regime
  by_cases hd : 1.94 * dist2 Y < diam Y
  · have := degenerate h4 hd
    have : (1 : ℝ) ≤ C43 := by norm_num [C43]
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
      min (mult Y (dist2 Y) : ℝ) (mult Y (minDist Y)) ≤ 4 / 3 * Y.card + C43 := by
    intro Q hQS hQ he
    have := assemble43 hN hQS hQ he
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

/-- **Erdős #132 / CDL Problem 1.6 upper bound, `4/3`** (`angle_R6.md`, Corollary of Theorem
N3): there is an absolute `C₀` with `min{μ(Δ₂), μ(δ)} ≤ (4/3)n + C₀` for every `n`-point planar
set, `n ≥ 2`.  Hence `L ≤ 4/3 < 15/11`.

TODO: none — proved from the lemma statements.
Acceptance: no `sorry` (inherits). -/
theorem erdos132_main43 :
    ∃ C₀ : ℝ, ∀ X : Finset Pt, 2 ≤ X.card →
      (min (mult X (dist2 X)) (mult X (minDist X)) : ℝ) ≤ 4 / 3 * X.card + C₀ := by
  refine ⟨C43, fun X hX => ?_⟩
  obtain ⟨Y, hc, h1, hm₂, hmδ⟩ := exists_normalize hX
  rw [← hm₂, ← hmδ, ← hc]
  exact main43_normalized Y h1

end Erdos132Main

#print axioms Erdos132Main.erdos132_main43
