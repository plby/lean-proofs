import ErdosProblems.Erdos6.LargeExcess

/-!
# Erdős Problem 6

This file proves that the gaps between consecutive primes contain infinitely
many strictly increasing runs of length three.

The analytic input is the Maynard--Tao prime-tuples theorem, in the form
needed by Banks--Freiberg--Turnage-Butterbaugh.  The remaining argument uses
their congruence construction and the admissible tuple of powers of two.
-/

namespace Erdos6

open Set

/-- The gap after the zero-based `n`th prime. -/
noncomputable abbrev primeGap (n : ℕ) : ℕ := BoundedGaps.primeGap n

/-- Successive differences between powers of two grow strictly. -/
theorem powTwo_gap_strictMono {a b c : ℕ} (hab : a < b) (hbc : b < c) :
    2 ^ b - 2 ^ a < 2 ^ c - 2 ^ b := by
  have habPow : 2 ^ a < 2 ^ b := Nat.pow_lt_pow_right (by omega) hab
  have hbcPow : 2 ^ (b + 1) ≤ 2 ^ c :=
    Nat.pow_le_pow_right (by omega) (by omega)
  rw [pow_succ] at hbcPow
  have haPos : 0 < 2 ^ a := pow_pos (by omega) _
  have hbPos : 0 < 2 ^ b := pow_pos (by omega) _
  have hleft : 2 ^ b - 2 ^ a < 2 ^ b := Nat.sub_lt hbPos haPos
  have hdouble : 2 ^ b + 2 ^ b ≤ 2 ^ c := by omega
  have hright : 2 ^ b ≤ 2 ^ c - 2 ^ b := Nat.le_sub_of_add_le hdouble
  exact hleft.trans_le hright

/-- The first `k` positive powers of two, used as the Maynard tuple. -/
def powersOfTwo (k : ℕ) : Finset ℕ :=
  (Finset.range k).image fun j => 2 ^ (j + 1)

theorem mem_powersOfTwo {k h : ℕ} :
    h ∈ powersOfTwo k ↔ ∃ j < k, h = 2 ^ (j + 1) := by
  simp [powersOfTwo, eq_comm]

theorem powersOfTwo_card (k : ℕ) : (powersOfTwo k).card = k := by
  rw [powersOfTwo, Finset.card_image_iff.mpr, Finset.card_range]
  intro a ha b hb hab
  have := Nat.pow_right_injective (a := 2) (by omega) hab
  omega

/-- Every finite tuple of positive powers of two is admissible. -/
theorem powersOfTwo_admissible (k : ℕ) :
    BoundedGaps.IsAdmissible (powersOfTwo k) := by
  rw [BoundedGaps.isAdmissible_iff_avoids_residue]
  intro p hp
  by_cases hpTwo : p = 2
  · subst p
    refine ⟨1, by omega, ?_⟩
    intro h hh
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hh
    simp [pow_succ]
  · refine ⟨0, hp.pos, ?_⟩
    intro h hh
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hh
    intro hmod
    have hdvd : p ∣ 2 ^ (j + 1) := Nat.dvd_of_mod_eq_zero hmod
    have hpDvdTwo : p ∣ 2 := hp.dvd_of_dvd_pow hdvd
    exact hpTwo ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpDvdTwo)

/-- Four consecutive primes at increasing power-of-two shifts give one
strictly increasing triple of prime gaps. -/
theorem increasing_gaps_of_consecutive_power_translates
    {r n a b c d : ℕ} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (h₀ : Nat.nth Nat.Prime r = n + 2 ^ a)
    (h₁ : Nat.nth Nat.Prime (r + 1) = n + 2 ^ b)
    (h₂ : Nat.nth Nat.Prime (r + 2) = n + 2 ^ c)
    (h₃ : Nat.nth Nat.Prime (r + 3) = n + 2 ^ d) :
    primeGap r < primeGap (r + 1) ∧
      primeGap (r + 1) < primeGap (r + 2) := by
  have gap₀ : primeGap r = 2 ^ b - 2 ^ a := by
    simp [BoundedGaps.primeGap, h₀, h₁, Nat.add_sub_add_left]
  have gap₁ : primeGap (r + 1) = 2 ^ c - 2 ^ b := by
    simp [BoundedGaps.primeGap, h₁, h₂, Nat.add_assoc,
      Nat.add_sub_add_left]
  have gap₂ : primeGap (r + 2) = 2 ^ d - 2 ^ c := by
    simp [BoundedGaps.primeGap, h₂, h₃, Nat.add_assoc,
      Nat.add_sub_add_left]
  rw [gap₀, gap₁, gap₂]
  exact ⟨powTwo_gap_strictMono hab hbc, powTwo_gap_strictMono hbc hcd⟩

/-- The exact elementary reduction from the BFT output to Erdős Problem 6. -/
theorem erdos_6_of_consecutive_power_quadruples
    (hblocks : ∀ N : ℕ, ∃ r n a b c d : ℕ,
      N < r ∧ a < b ∧ b < c ∧ c < d ∧
      Nat.nth Nat.Prime r = n + 2 ^ a ∧
      Nat.nth Nat.Prime (r + 1) = n + 2 ^ b ∧
      Nat.nth Nat.Prime (r + 2) = n + 2 ^ c ∧
      Nat.nth Nat.Prime (r + 3) = n + 2 ^ d) :
    {n | primeGap n < primeGap (n + 1) ∧
      primeGap (n + 1) < primeGap (n + 2)}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro N
  obtain ⟨r, n, a, b, c, d, hNr, hab, hbc, hcd, h₀, h₁, h₂, h₃⟩ :=
    hblocks N
  refine ⟨r, ?_, hNr⟩
  exact increasing_gaps_of_consecutive_power_translates hab hbc hcd
    h₀ h₁ h₂ h₃

namespace Maynard

/-- Positive Maynard excess above `3` forces four prime shifts arbitrarily
far out.  This is the threshold conversion used in the four-prime case. -/
theorem infinitelyOftenAtLeastFourPrimeShifts_of_eventuallyPositiveSieveExcess
    {H : Finset ℕ}
    (hpos : BoundedGaps.Maynard.HasEventuallyPositiveSieveExcess H 3) :
    BoundedGaps.InfinitelyOftenAtLeastPrimeShifts H 4 := by
  obtain ⟨N₀, hN₀⟩ := hpos
  intro T
  let N := max N₀ (T + 1)
  obtain ⟨w, hw, hexcess⟩ := hN₀ N (le_max_left _ _)
  obtain ⟨n, hn, hcount⟩ :=
    BoundedGaps.Maynard.exists_primeShiftCount_gt_of_sieveExcess_pos hw hexcess
  refine ⟨n, ?_, ?_⟩
  · have hNn := (Finset.mem_Ico.mp hn).1
    have hTN : T + 1 ≤ N := le_max_right _ _
    omega
  · have hcountNat : 3 < BoundedGaps.primeShiftCount H n := by
      exact_mod_cast hcount
    omega

end Maynard

/-- Erdős Problem 6: three consecutive prime gaps are strictly increasing
for infinitely many starting indices. -/
theorem erdos_6 :
    {n | primeGap n < primeGap (n + 1) ∧
      primeGap (n + 1) < primeGap (n + 2)}.Infinite := by
  apply erdos_6_of_consecutive_power_quadruples
  exact Maynard.consecutive_power_quadruples_of_isolated_four_shifts
    Maynard.hasIsolatedFourPowerPrimeShifts

end Erdos6

#print axioms Erdos6.erdos_6
