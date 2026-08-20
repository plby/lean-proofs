/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos980.External.Erdos822.SlopeAwareBeta

/-!
# Concrete slope-aware affine prime-pair bound

This packages the checked filtered beta main term, the local Euler-product
comparison, and the explicit slope-prime loss into the estimate used for a
fixed collision fiber.
-/

namespace Erdos822

open scoped BigOperators
open Erdos851.FiniteCombinatorialSieve

theorem exists_twoAffinePrimeCandidates_slopeAware_pair_bound :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ a b q q' X z y S : ℕ,
        q.Prime → q'.Prime → y < q → y < q' →
        2 ≤ z → z ≤ y → 1 < y → 101 ≤ S →
        Real.log A ≤ 4 * (S - 100 : ℕ) / 99 →
        let V := Erdos851.localEulerProduct
          (Erdos851.pairShiftDensity (affineDetNat a q b q')) z y
        let L := slopePrimeLoss (affineDetNat a q b q') a b z y
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let D := y ^ S
        ((twoAffinePrimeCandidates a q b q' X y).card : ℝ) ≤
          (X : ℝ) * ((1 + eta) * (V * L)) + (D : ℝ) ^ 2 := by
  obtain ⟨A, hA, hmain⟩ :=
    exists_slopeAware_concrete_finiteMainTerm_bounds
  refine ⟨A, hA, ?_⟩
  intro a b q q' X z y S hq hq' hyq hyq' hz hzy hy hS hlog
  dsimp only
  let P := ascendingSlopeAwareSievePrimes a b z (y + 1)
  let stop := rosserStoppingPredicate 100 (y ^ S)
  let E := ∏ p ∈ slopeAwareSievePrimes a b z (y + 1),
    (1 - twoAffineNu a q b q' p)
  have hconstants :
      ∀ p ∈ slopeAwareSievePrimes a b z (y + 1),
        ¬ p ∣ q ∧ ¬ p ∣ q' :=
    constants_not_dvd_on_slopeAware_of_prime_gt hq hq' hyq hyq'
  have hprime := twoAffinePrimeCandidates_card_le_slopeAware_upperMain
    (a := a) (b := b) (q := q) (q' := q') (X := X)
    (z := z) (y := y) (S := S)
    hq hq' hyq hyq' hz hy (by omega : 1 ≤ S)
  dsimp only at hprime
  have hbeta := hmain a q b q' z y S hz hzy hy hS hconstants hlog
  dsimp only at hbeta
  have hEuler :
      E ≤ Erdos851.localEulerProduct
          (Erdos851.pairShiftDensity (affineDetNat a q b q')) z y *
        slopePrimeLoss (affineDetNat a q b q') a b z y := by
    exact slopeAware_localEulerProduct_le_pair_mul_slopeLoss
      hz hconstants
  calc
    ((twoAffinePrimeCandidates a q b q' X y).card : ℝ) ≤
        (X : ℝ) * upperMainTerm stop (twoAffineNu a q b q') P +
          ((y ^ S : ℕ) : ℝ) ^ 2 := by
      simpa [P, stop] using hprime
    _ ≤ (X : ℝ) *
          ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) * E) +
          ((y ^ S : ℕ) : ℝ) ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hbeta.2 (Nat.cast_nonneg X)
      simpa [P, stop, E, add_comm] using
        (add_le_add_right hmul (((y ^ S : ℕ) : ℝ) ^ 2))
    _ ≤ (X : ℝ) *
          ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
            (Erdos851.localEulerProduct
              (Erdos851.pairShiftDensity (affineDetNat a q b q')) z y *
              slopePrimeLoss (affineDetNat a q b q') a b z y)) +
          ((y ^ S : ℕ) : ℝ) ^ 2 := by
      have hetaNonneg :
          0 ≤ 1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100) := by
        positivity
      have hmulE := mul_le_mul_of_nonneg_left hEuler hetaNonneg
      have hmulX := mul_le_mul_of_nonneg_left hmulE (Nat.cast_nonneg X)
      simpa [add_comm] using
        (add_le_add_right hmulX (((y ^ S : ℕ) : ℝ) ^ 2))

end Erdos822
