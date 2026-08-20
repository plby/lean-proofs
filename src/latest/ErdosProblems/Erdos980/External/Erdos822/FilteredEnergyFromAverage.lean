/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos980.External.Erdos822.GoodCofactorMass
import ErdosProblems.Erdos980.External.Erdos822.ZeroDeterminant

/-!
# Energy assembly for filtered odd cofactor layers

The arithmetic exceptional-set argument replaces the raw odd layer by a
subfinset.  The pointwise sieve bound and the beta-remainder estimate are
monotone under that replacement, so the global assembly is recorded once in
this filtered form.
-/

namespace Erdos822

open scoped BigOperators

/-- A linear main-weight sum on any subfamily of the odd raw cofactors gives
linear shifted-totient energy for the corresponding outer inputs. -/
theorem exists_filteredOdd_collisionEnergy_le_of_logMassMainSum :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 < C ∧
      ∀ N S K : ℕ, ∀ B : Finset ℕ,
        B ⊆ oddRawCofactors N →
        2 ≤ N → 0 < S → 101 ≤ S →
        let y := Nat.nthRoot (4 * S) N
        2 ≤ y →
        Real.log A ≤ 4 * (S - 100 : ℕ) / 99 →
        (∑ m ∈ B,
            ∑ m' ∈ B.erase m,
              logMassMainWeight A C (N ^ 60) m m' 2 y S) ≤
          K * ((N ^ 60 : ℕ) : ℝ) →
        (collisionEnergy
          (outerInputs (fun _ => B) (N ^ 60))
          shiftedTotient : ℝ) ≤
          (K + 6) * ((N ^ 60 : ℕ) : ℝ) := by
  obtain ⟨A, C, hA, hC, hpoint⟩ :=
    exists_outerCollisionPairs_le_logMassFiberWeight
  refine ⟨A, C, hA, hC, ?_⟩
  intro N S K B hB hN hS hS101
  dsimp only
  intro hyTwo hlog hmain
  let y := Nat.nthRoot (4 * S) N
  have hy2 : 2 ≤ y := by simpa [y] using hyTwo
  have hpos : ∀ m ∈ B, 0 < m := by
    intro m hm
    exact oddRawCofactors_pos (hB hm)
  have hlarge : ∀ m ∈ B,
      ∀ p ∈ outerPrimes (N ^ 60) m, m < p := by
    intro m hm p hp
    exact oddOuterPrime_large_of_mem hN (hB hm) hp
  have hylarge : ∀ m ∈ B,
      ∀ p ∈ outerPrimes (N ^ 60) m, y < p := by
    intro m hm p hp
    dsimp [y]
    exact oddOuterPrime_gt_slowSieveCutoff hN hS (hB hm) hp
  have hG : ∀ m ∈ B,
      ∀ m' ∈ B.erase m,
      ((outerCollisionPairs (N ^ 60) m m').card : ℝ) ≤
        logMassFiberWeight A C (N ^ 60) m m' 2 y S := by
    intro m hm m' hm'
    exact hpoint (N ^ 60) m m' 2 y S
      (hpos m hm)
      (hpos m' (Finset.mem_erase.mp hm').2)
      (hlarge m hm)
      (hlarge m' (Finset.mem_erase.mp hm').2)
      (hylarge m hm)
      (hylarge m' (Finset.mem_erase.mp hm').2)
      (by norm_num) (by omega) (by omega) hS101 hlog
  have herrRaw :
      (∑ m ∈ oddRawCofactors N,
          ∑ m' ∈ (oddRawCofactors N).erase m,
            (((y ^ S : ℕ) : ℝ) ^ 2)) ≤
        4 * ((N ^ 60 : ℕ) : ℝ) := by
    simpa [y] using sum_oddRaw_slowSieveCutoff_error_sq_le N S
      (by omega) hS
  have herr :
      (∑ m ∈ B,
          ∑ m' ∈ B.erase m,
            (((y ^ S : ℕ) : ℝ) ^ 2)) ≤
        4 * ((N ^ 60 : ℕ) : ℝ) := by
    calc
      (∑ m ∈ B,
          ∑ m' ∈ B.erase m,
            (((y ^ S : ℕ) : ℝ) ^ 2)) ≤
          ∑ m ∈ B,
            ∑ m' ∈ (oddRawCofactors N).erase m,
              (((y ^ S : ℕ) : ℝ) ^ 2) := by
        apply Finset.sum_le_sum
        intro m hm
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.erase_subset_erase m hB)
        intro m' hm' hnot
        positivity
      _ ≤ ∑ m ∈ oddRawCofactors N,
            ∑ m' ∈ (oddRawCofactors N).erase m,
              (((y ^ S : ℕ) : ℝ) ^ 2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hB
        intro m hm hnot
        positivity
      _ ≤ 4 * ((N ^ 60 : ℕ) : ℝ) := herrRaw
  have hsum :
      (∑ m ∈ B,
          ∑ m' ∈ B.erase m,
            logMassFiberWeight A C (N ^ 60) m m' 2 y S) ≤
        (K + 4) * ((N ^ 60 : ℕ) : ℝ) := by
    unfold logMassFiberWeight
    simp_rw [Finset.sum_add_distrib]
    calc
      (∑ m ∈ B,
          ∑ m' ∈ B.erase m,
              logMassMainWeight A C (N ^ 60) m m' 2 y S) +
          ∑ m ∈ B,
            ∑ m' ∈ B.erase m,
              (((y ^ S : ℕ) : ℝ) ^ 2) ≤
          K * ((N ^ 60 : ℕ) : ℝ) +
            4 * ((N ^ 60 : ℕ) : ℝ) :=
        add_le_add hmain herr
      _ = (K + 4) * ((N ^ 60 : ℕ) : ℝ) := by
        push_cast
        ring
  have henergy :=
    collisionEnergy_outerInputs_cast_le_of_sum_majorant
      (fun _ => B) (N ^ 60)
      (fun m m' => logMassFiberWeight A C (N ^ 60) m m' 2 y S)
      (K + 4)
      (by
        have : 1 ≤ N ^ 60 := one_le_pow₀ (by omega)
        exact this)
      hpos hlarge hG hsum
  convert henergy using 1 <;> push_cast <;> ring

end Erdos822
