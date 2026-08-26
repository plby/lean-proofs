/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.BoundedMassPrimeBlocks
import ErdosProblems.Erdos822.MediumRangeInfrastructure

/-! # Uniform reciprocal prime mass with a full modulus saving -/

namespace Erdos822

open scoped BigOperators Classical
open Filter

theorem eventually_slowSieveError_mul_harmonic_le {S : ℕ} (hS : 0 < S) :
    ∀ᶠ N : ℕ in atTop,
      (((Nat.nthRoot (4 * S) N) ^ S : ℕ) : ℝ) ^ 2 * (harmonic N : ℝ) ≤ N := by
  filter_upwards [eventually_harmonic_pow_le_natCast 2] with N hH
  have hroot : (Nat.nthRoot (4 * S) N) ^ (4 * S) ≤ N :=
    Nat.pow_nthRoot_le_iff.mpr (Or.inl (by omega))
  have hE : ((((Nat.nthRoot (4 * S) N) ^ S : ℕ) : ℝ) ^ 2) ^ 2 ≤ N := by
    exact_mod_cast (show (((Nat.nthRoot (4 * S) N) ^ S) ^ 2) ^ 2 ≤ N by
      simpa only [← pow_mul, show S * 2 * 2 = 4 * S by omega] using hroot)
  have hprod := mul_le_mul hE hH (by positivity) (Nat.cast_nonneg (α := ℝ) N)
  have hH0 : 0 ≤ (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun j hj ↦ by positivity
  nlinarith only [hprod, hH0, Nat.cast_nonneg (α := ℝ) ((Nat.nthRoot (4 * S) N) ^ S),
    Nat.cast_nonneg (α := ℝ) N]

theorem exists_eventually_boundedMass_prime_progression_mass :
    ∀ C : ℝ, ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (P : Finset ℕ) (L d a : ℕ), 0 < d → d * N ≤ L →
        primeDivisorReciprocalMass d ≤ C →
        (∀ q ∈ P, L < q ∧ q ≤ N * L ∧ q.Prime ∧ q % d = a % d) →
        (∑ q ∈ P, (1 : ℝ) / q) ≤ B / d := by
  intro C
  obtain ⟨S, hS, hbound⟩ := exists_fixed_depth_boundedMass_primeSet_bound
  obtain ⟨D, hD, hcount⟩ := hbound C
  let B := 2 * D * ((1 : ℝ) / Real.log 2 + 8 * S) + 1
  have hSpos : 0 < S := by omega
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  filter_upwards [eventually_ge_atTop 2, eventually_nthRoot_ge (4 * S) 2 (by omega),
    eventually_slowSieveError_mul_harmonic_le hSpos] with N hN hy herror
  let y := Nat.nthRoot (4 * S) N
  have hyN : y ≤ N := nthRoot_le_self_of_pos (by omega)
  have hH0 : 0 ≤ (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun j hj ↦ by positivity
  have hmain : 2 * (D / Real.log (y : ℝ)) * (harmonic N : ℝ) ≤ B - 1 := by
    have h := mul_le_mul_of_nonneg_left (harmonic_div_log_slowSieveCutoff_le hSpos hy)
      (show (0 : ℝ) ≤ 2 * D by positivity)
    calc
      _ = (2 * D) * ((harmonic N : ℝ) / Real.log (y : ℝ)) := by ring
      _ ≤ (2 * D) * ((1 : ℝ) / Real.log 2 + 8 * S) := h
      _ = B - 1 := by dsimp [B]; ring
  intro P L d a hd hdN hmass hP
  have hNL : N ≤ L := (Nat.le_mul_of_pos_left N hd).trans hdN
  have hL : 0 < L := (by omega : 0 < N).trans_le hNL
  have hdL : d ≤ L := (Nat.le_mul_of_pos_right d (by omega : 0 < N)).trans hdN
  have hbound' := hcount P N L d a y hL hd hdL hmass hy
    (fun q hq ↦ ⟨(hP q hq).1, (hP q hq).2.1, (hP q hq).2.2.1,
      (hyN.trans hNL).trans_lt (hP q hq).1, (hP q hq).2.2.2⟩)
  have herr : (((y ^ S : ℕ) : ℝ) ^ 2 * (harmonic N : ℝ)) / L ≤ (1 : ℝ) / d := by
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hLR : (0 : ℝ) < L := by exact_mod_cast hL
    have hdNR : (d : ℝ) * N ≤ L := by exact_mod_cast hdN
    calc
      _ ≤ (N : ℝ) / L := div_le_div_of_nonneg_right herror (by positivity)
      _ ≤ (1 : ℝ) / d := (div_le_div_iff₀ hLR hdR).mpr (by simpa [mul_comm] using hdNR)
  calc
    _ ≤ (2 * (D / Real.log (y : ℝ)) / d + ((y ^ S : ℕ) : ℝ) ^ 2 / L) * (harmonic N : ℝ) := hbound'
    _ = (2 * (D / Real.log (y : ℝ)) * (harmonic N : ℝ)) / d +
        (((y ^ S : ℕ) : ℝ) ^ 2 * (harmonic N : ℝ)) / L := by ring
    _ ≤ (B - 1) / d + 1 / d :=
      add_le_add (div_le_div_of_nonneg_right hmain (by positivity)) herr
    _ = _ := by ring

#print axioms exists_eventually_boundedMass_prime_progression_mass

end Erdos822
