/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierFullIntegral
import ErdosProblems.Erdos4b.SingularPrimeAverage

/-!
# Finite products over the small, rough, and cofactor prime cutoffs

These identities connect the prime-subtype Fourier products to the
natural-prime products used in the arithmetic singular series.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem prod_boundedFourierPrimes_nat (Y : ℕ) (f : ℕ → ℝ) :
    (∏ p ∈ boundedFourierPrimes Y, f p) = ∏ p ∈ Nat.primesLE Y, f p :=
  Finset.prod_subtype_of_mem f (fun _ hp ↦ (Nat.mem_primesLE.mp hp).2)

theorem prod_boundedFourierPrimes_small {w Y : ℕ} (hwy : w ≤ Y) (f : ℕ → ℝ) :
    (∏ p ∈ boundedFourierPrimes Y, if p.val ≤ w then f p else 1) =
      ∏ p ∈ Nat.primesLE w, f p := by
  rw [prod_boundedFourierPrimes_nat Y (fun p ↦ if p ≤ w then f p else 1), ← Finset.prod_filter]
  have hset : (Nat.primesLE Y).filter (fun p ↦ p ≤ w) = Nat.primesLE w := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hpY, hp⟩, hpw⟩
      exact ⟨hpw, hp⟩
    · rintro ⟨hpw, hp⟩
      exact ⟨⟨hpw.trans hwy, hp⟩, hpw⟩
  rw [hset]

theorem prod_boundedFourierPrimes_rough (w Y : ℕ) (f : ℕ → ℝ) :
    (∏ p ∈ boundedFourierPrimes Y, if w < p.val then f p else 1) =
      ∏ p ∈ BoundedGaps.Maynard.roughPrimeSupport w Y, f p := by
  rw [prod_boundedFourierPrimes_nat Y (fun p ↦ if w < p then f p else 1), ← Finset.prod_filter]
  have hset : (Nat.primesLE Y).filter (fun p ↦ w < p) =
      BoundedGaps.Maynard.roughPrimeSupport w Y := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE, BoundedGaps.Maynard.roughPrimeSupport,
      Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hpY, hp⟩, hwp⟩
      exact ⟨⟨by omega, hpY⟩, hp⟩
    · rintro ⟨⟨hwp, hpY⟩, hp⟩
      exact ⟨⟨hpY, hp⟩, by omega⟩
  rw [hset]

theorem prod_boundedFourierPrimes_fixed (w Y m : ℕ) (f : ℕ → ℝ) :
    (∏ p ∈ boundedFourierPrimes Y, if w < p.val ∧ p.val ∣ m then f p else 1) =
      ∏ p ∈ fixedSingularPrimeSupport w Y m, f p := by
  rw [prod_boundedFourierPrimes_nat Y (fun p ↦ if w < p ∧ p ∣ m then f p else 1),
    ← Finset.prod_filter]
  have hset : (Nat.primesLE Y).filter (fun p ↦ w < p ∧ p ∣ m) =
      fixedSingularPrimeSupport w Y m := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE, fixedSingularPrimeSupport,
      BoundedGaps.Maynard.roughPrimeSupport, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hpY, hp⟩, hwp, hpm⟩
      exact ⟨⟨⟨by omega, hpY⟩, hp⟩, hpm⟩
    · rintro ⟨⟨⟨hwp, hpY⟩, hp⟩, hpm⟩
      exact ⟨⟨hpY, hp⟩, (by omega), hpm⟩
  rw [hset]

end

end Erdos4b
