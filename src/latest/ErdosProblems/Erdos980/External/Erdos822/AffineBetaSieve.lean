/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos980.External.Erdos822.AffineBoundingSieve
import ErdosProblems.Erdos851.ConcreteBetaCardinality

/-!
# Quantitative beta-sieve bound for two affine forms

The finite CRT and endpoint estimates from the preceding files satisfy the
generic Rosser-sieve interface.  Since the local density agrees with the
pair-shift density at the absolute determinant, the already checked
dimension-two beta-sieve main-term theorem applies verbatim.
-/

namespace Erdos822

open Erdos851.FiniteCombinatorialSieve
open Erdos851.FiniteSieveApplication
open List

/-- Rosser's upper main term bounds the actual affine sifted cardinality,
with the standard square distribution-level loss. -/
theorem twoAffineBoundingSieve_cardinality_le_upperMain
    {a s b t X z y S : ℕ} (hz : 2 ≤ z) (hzy : z ≤ y) (hS : 1 ≤ S)
    (hadmissible : ∀ p : ℕ, p.Prime →
      p ∣ Erdos387.sievePrimeProduct z (y + 1) → ¬ p ∣ a ∧ ¬ p ∣ b) :
    let P := Erdos851.ascendingSievePrimes z y
    let D := y ^ S
    let stop := rosserStoppingPredicate 100 D
    ((siftedTwoAffineCandidates a s b t X z (y + 1)).card : ℝ) ≤
      (X : ℝ) * upperMainTerm stop (twoAffineNu a s b t) P +
        (D : ℝ) ^ 2 := by
  classical
  dsimp only
  let P := Erdos851.ascendingSievePrimes z y
  let D := y ^ S
  let stop := rosserStoppingPredicate 100 D
  let sieve := twoAffineBoundingSieve a s b t X z (y + 1) hz hadmissible
  have hprod : P.prod = sieve.prodPrimes := by
    change P.prod = Erdos387.sievePrimeProduct z (y + 1)
    exact Erdos851.ascendingSievePrimes_prod z y
  have hsort : P.Pairwise (· ≤ ·) :=
    Erdos851.ascendingSievePrimes_pairwise z y
  have hnodup : P.Nodup := Erdos851.ascendingSievePrimes_nodup z y
  have hprime : ∀ p ∈ P, p.Prime :=
    Erdos851.ascendingSievePrimes_prime
  have hD : 1 ≤ D := by
    dsimp [D]
    exact one_le_pow₀ (by omega)
  have hrem : ∀ d : ℕ, d ∣ sieve.prodPrimes → d ≤ D →
      |sieve.rem d| ≤ (d : ℝ) := by
    intro d hd _hdD
    have hsq : Squarefree d :=
      Squarefree.squarefree_of_dvd hd sieve.prodPrimes_squarefree
    exact (twoAffineBoundingSieve_abs_rem_le_nuClasses
      (a := a) (s := s) (b := b) (t := t) (X := X) (z := z) (Y := y + 1)
      hd).trans (by exact_mod_cast twoAffineNuClasses_le hsq)
  have hupper := boundingSieve_siftedSum_le_upperMain_add_sq
    sieve P stop D hprod hsort hnodup hprime
    (by
      intro u hu hadm
      apply prod_le_of_upperAdmissible_rosserStoppingPredicate
        (by norm_num : 1 ≤ 100) hD
        (hsort.sublist (List.mem_sublists.mp hu))
        (by
          intro p hp
          exact (hprime p ((List.mem_sublists.mp hu).subset hp)).one_le)
        hadm)
    hrem
  change _ ≤ sieve.totalMass *
      upperMainTerm stop (fun p ↦ sieve.nu p) P + (D : ℝ) ^ 2 at hupper
  rw [show sieve.totalMass = (X : ℝ) by
      exact twoAffineBoundingSieve_totalMass,
    show sieve.siftedSum =
        ((siftedTwoAffineCandidates a s b t X z (y + 1)).card : ℝ) by
      exact twoAffineBoundingSieve_siftedSum] at hupper
  exact hupper

open Erdos851.BetaSieveFundamental

/-- End-to-end dimension-two beta-sieve upper bound for two affine forms,
uniform in the determinant. -/
theorem exists_twoAffine_concrete_cardinality_upper_bound :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ a s b t X z y S : ℕ,
        (∀ p : ℕ, p.Prime →
          p ∣ Erdos387.sievePrimeProduct z (y + 1) → ¬ p ∣ a ∧ ¬ p ∣ b) →
        2 ≤ z → z ≤ y → 1 < y → 101 ≤ S →
        Real.log A ≤ 4 * (S - 100 : ℕ) / 99 →
        let V := Erdos851.localEulerProduct
          (Erdos851.pairShiftDensity (affineDetNat a s b t)) z y
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let D := y ^ S
        ((siftedTwoAffineCandidates a s b t X z (y + 1)).card : ℝ) ≤
          (X : ℝ) * ((1 + eta) * V) + (D : ℝ) ^ 2 := by
  classical
  obtain ⟨A, hA, hmain⟩ :=
    Erdos851.BetaSieveFundamental.exists_pairShift_concrete_finiteMainTerm_bounds
  refine ⟨A, hA, ?_⟩
  intro a s b t X z y S hadmissible hz hzy hy hS hlog
  dsimp only
  let P := Erdos851.ascendingSievePrimes z y
  let D := y ^ S
  let stop := rosserStoppingPredicate 100 D
  have hm := hmain (affineDetNat a s b t) z y S hz hzy hy hS hlog
  dsimp only at hm
  have hb := twoAffineBoundingSieve_cardinality_le_upperMain
    (a := a) (s := s) (b := b) (t := t) (X := X)
    (z := z) (y := y) (S := S) hz hzy (by omega) hadmissible
  dsimp only at hb
  have hnu : ∀ p ∈ P,
      twoAffineNu a s b t p =
        Erdos851.pairShiftDensity (affineDetNat a s b t) p := by
    intro p hpMem
    have hp : p.Prime :=
      Erdos851.ascendingSievePrimes_prime p hpMem
    have hpDiv : p ∣ Erdos387.sievePrimeProduct z (y + 1) := by
      rw [← Erdos851.ascendingSievePrimes_prod z y]
      exact List.dvd_prod hpMem
    exact twoAffineNu_eq_pairShiftDensity_of_not_dvd hp
      (hadmissible p hp hpDiv).1 (hadmissible p hp hpDiv).2
  rw [Erdos851.upperMainTerm_congr_on stop (twoAffineNu a s b t)
    (Erdos851.pairShiftDensity (affineDetNat a s b t)) P hnu] at hb
  have hmupper := hm.2
  change
    upperMainTerm stop
        (Erdos851.pairShiftDensity (affineDetNat a s b t)) P ≤
      (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
        Erdos851.localEulerProduct
          (Erdos851.pairShiftDensity (affineDetNat a s b t)) z y at hmupper
  calc
    ((siftedTwoAffineCandidates a s b t X z (y + 1)).card : ℝ) ≤
        (X : ℝ) *
            upperMainTerm stop
              (Erdos851.pairShiftDensity (affineDetNat a s b t)) P +
          (D : ℝ) ^ 2 := hb
    _ ≤ (X : ℝ) *
          ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
            Erdos851.localEulerProduct
              (Erdos851.pairShiftDensity (affineDetNat a s b t)) z y) +
          (D : ℝ) ^ 2 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hmupper (Nat.cast_nonneg X)) le_rfl

end Erdos822
