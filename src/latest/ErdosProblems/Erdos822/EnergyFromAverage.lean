/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.GlobalEnergyAssembly
import ErdosProblems.Erdos822.SieveErrorAverage

/-!
# From the arithmetic cofactor average to linear energy

All local and finite-sieve work is now encapsulated in one nonnegative main
weight.  If its off-diagonal double sum is linear, the already-checked
diagonal decomposition and root-cutoff remainder estimate give linear
collision energy.
-/

namespace Erdos822

open scoped BigOperators

/-- Main logarithmic/arithmetic majorant for one off-diagonal cofactor
fiber. -/
noncomputable def logMassMainWeight
    (A C : ℝ) (x m m' z y S : ℕ) : ℝ :=
  let B := reducedCollisionRight m m'
  let U := max (x / m) (x / m')
  let X := U / B + 1
  let W :=
    C ^ 2 * (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
      Real.exp
        (2 * divisorReciprocalMass (reducedTotientDet m m') z y +
          6 * (shiftedTotientReciprocalMass m z y +
            shiftedTotientReciprocalMass m' z y))
  let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
  (X : ℝ) * ((1 + eta) * W)

/-- Main weight plus the square beta-sieve remainder. -/
noncomputable def logMassFiberWeight
    (A C : ℝ) (x m m' z y S : ℕ) : ℝ :=
  logMassMainWeight A C x m m' z y S +
    (((y ^ S : ℕ) : ℝ) ^ 2)

theorem logMassFiberWeight_nonneg
    (A C : ℝ) (x m m' z y S : ℕ) (hA : 0 ≤ A) :
    0 ≤ logMassFiberWeight A C x m m' z y S := by
  unfold logMassFiberWeight logMassMainWeight
  dsimp only
  have heta : 0 ≤ (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100) := by
    positivity
  have honeeta :
      0 ≤ 1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100) := by
    linarith
  positivity

/-- The logarithmic fiber theorem gives a pointwise bound by the named
fiber weight, including the empty-fiber case. -/
theorem exists_outerCollisionPairs_le_logMassFiberWeight :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 < C ∧
      ∀ x m m' z y S : ℕ,
        0 < m → 0 < m' →
        (∀ p ∈ outerPrimes x m, m < p) →
        (∀ p ∈ outerPrimes x m', m' < p) →
        (∀ p ∈ outerPrimes x m, y < p) →
        (∀ p ∈ outerPrimes x m', y < p) →
        2 ≤ z → z ≤ y → 1 < y → 101 ≤ S →
        Real.log A ≤ 4 * (S - 100 : ℕ) / 99 →
        ((outerCollisionPairs x m m').card : ℝ) ≤
          logMassFiberWeight A C x m m' z y S := by
  obtain ⟨A, C, hA, hC, hfiber⟩ :=
    exists_outerCollisionPairs_log_mass_bound
  refine ⟨A, C, hA, hC, ?_⟩
  intro x m m' z y S hm hm' hlarge hlarge' hy hy'
    hz hzy hyTwo hS hlog
  by_cases hne : (outerCollisionPairs x m m').Nonempty
  · have h := hfiber x m m' z y S hm hm' hlarge hlarge' hy hy'
      hz hzy hyTwo hS hlog hne
    simpa [logMassFiberWeight, logMassMainWeight] using h
  · have hempty : outerCollisionPairs x m m' = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact logMassFiberWeight_nonneg A C x m m' z y S
      (le_trans (by norm_num) hA)

/-- Once the GIL arithmetic main-weight average is bounded, the odd raw
family has linear shifted-totient collision energy at the perfect-power
scale. -/
theorem exists_oddRaw_collisionEnergy_le_of_logMassMainSum :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 < C ∧
      ∀ N S K : ℕ,
        2 ≤ N → 0 < S → 101 ≤ S →
        let y := Nat.nthRoot (4 * S) N
        2 ≤ y →
        Real.log A ≤ 4 * (S - 100 : ℕ) / 99 →
        (∑ m ∈ oddRawCofactors N,
            ∑ m' ∈ (oddRawCofactors N).erase m,
              logMassMainWeight A C (N ^ 60) m m' 2 y S) ≤
          K * ((N ^ 60 : ℕ) : ℝ) →
        (collisionEnergy
          (outerInputs (fun _ => oddRawCofactors N) (N ^ 60))
          shiftedTotient : ℝ) ≤
          (K + 6) * ((N ^ 60 : ℕ) : ℝ) := by
  obtain ⟨A, C, hA, hC, hpoint⟩ :=
    exists_outerCollisionPairs_le_logMassFiberWeight
  refine ⟨A, C, hA, hC, ?_⟩
  intro N S K hN hS hS101
  dsimp only
  intro hyTwo hlog hmain
  let y := Nat.nthRoot (4 * S) N
  have hydef : y = Nat.nthRoot (4 * S) N := rfl
  have hy2 : 2 ≤ y := by simpa [y] using hyTwo
  have hpos : ∀ m ∈ oddRawCofactors N, 0 < m := by
    intro m hm
    exact oddRawCofactors_pos hm
  have hlarge : ∀ m ∈ oddRawCofactors N,
      ∀ p ∈ outerPrimes (N ^ 60) m, m < p := by
    intro m hm p hp
    exact oddOuterPrime_large_of_mem hN hm hp
  have hylarge : ∀ m ∈ oddRawCofactors N,
      ∀ p ∈ outerPrimes (N ^ 60) m, y < p := by
    intro m hm p hp
    dsimp [y]
    exact oddOuterPrime_gt_slowSieveCutoff hN hS hm hp
  have hG : ∀ m ∈ oddRawCofactors N,
      ∀ m' ∈ (oddRawCofactors N).erase m,
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
  have herr :
      (∑ m ∈ oddRawCofactors N,
          ∑ m' ∈ (oddRawCofactors N).erase m,
            (((y ^ S : ℕ) : ℝ) ^ 2)) ≤
        4 * ((N ^ 60 : ℕ) : ℝ) := by
    simpa [y] using sum_oddRaw_slowSieveCutoff_error_sq_le N S
      (by omega) hS
  have hsum :
      (∑ m ∈ oddRawCofactors N,
          ∑ m' ∈ (oddRawCofactors N).erase m,
            logMassFiberWeight A C (N ^ 60) m m' 2 y S) ≤
        (K + 4) * ((N ^ 60 : ℕ) : ℝ) := by
    unfold logMassFiberWeight
    simp_rw [Finset.sum_add_distrib]
    calc
      (∑ m ∈ oddRawCofactors N,
          ∑ m' ∈ (oddRawCofactors N).erase m,
              logMassMainWeight A C (N ^ 60) m m' 2 y S) +
          ∑ m ∈ oddRawCofactors N,
            ∑ m' ∈ (oddRawCofactors N).erase m,
              (((y ^ S : ℕ) : ℝ) ^ 2) ≤
          K * ((N ^ 60 : ℕ) : ℝ) +
            4 * ((N ^ 60 : ℕ) : ℝ) :=
        add_le_add hmain herr
      _ = (K + 4) * ((N ^ 60 : ℕ) : ℝ) := by
        push_cast
        ring
  have henergy :=
    collisionEnergy_outerInputs_cast_le_of_sum_majorant
      (fun _ => oddRawCofactors N) (N ^ 60)
      (fun m m' => logMassFiberWeight A C (N ^ 60) m m' 2 y S)
      (K + 4)
      (by
        have : 1 ≤ N ^ 60 := one_le_pow₀ (by omega)
        exact this)
      hpos hlarge hG hsum
  convert henergy using 1 <;> push_cast <;> ring

end Erdos822
