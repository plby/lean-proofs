import ErdosProblems.Erdos6.BFTResidue
import BoundedGaps.Maynard.ImprovedGPY.SieveSums

/-!
# The BFT residue family and positivity extraction
-/

namespace Erdos6.Maynard

open Filter Set

noncomputable section

theorem largePowerTuple_le_max {h : ℕ} (hh : h ∈ largePowerTuple) :
    h ≤ 2 ^ largeK := by
  obtain ⟨j, hj, rfl⟩ := mem_largePowerTuple.mp hh
  exact Nat.pow_le_pow_right (by omega) (by omega)

def BFTResidueData (N v : ℕ) : Prop :=
  v < BoundedGaps.Maynard.engelsmaMaynardModulus N ∧
    (∀ h ∈ largePowerTuple,
      Nat.Coprime (v + h) (BoundedGaps.Maynard.engelsmaMaynardModulus N)) ∧
    ∀ a ∈ badOffsets largePowerTuple (2 ^ largeK),
      assignedPrime (2 ^ largeK) a ∣ v + a

noncomputable def bftPreSieveResidue (N : ℕ) : ℕ := by
  classical
  exact if h : ∃ v, BFTResidueData N v then Classical.choose h
    else preSieveResidue largePowerTuple largePowerTuple_admissible N

theorem bftPreSieveResidue_lt (N : ℕ) :
    bftPreSieveResidue N < BoundedGaps.Maynard.engelsmaMaynardModulus N := by
  classical
  by_cases h : ∃ v, BFTResidueData N v
  · simpa [bftPreSieveResidue, h] using (Classical.choose_spec h).1
  · simpa [bftPreSieveResidue, h] using
      preSieveResidue_lt largePowerTuple largePowerTuple_admissible N

theorem bftPreSieveResidue_coprime (N : ℕ) {h : ℕ}
    (hh : h ∈ largePowerTuple) :
    Nat.Coprime (bftPreSieveResidue N + h)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N) := by
  classical
  by_cases hex : ∃ v, BFTResidueData N v
  · simpa [bftPreSieveResidue, hex] using (Classical.choose_spec hex).2.1 h hh
  · simpa [bftPreSieveResidue, hex] using
      preSieveResidue_coprime largePowerTuple largePowerTuple_admissible N hh

theorem eventually_bftPreSieveResidue_assigned :
    ∀ᶠ N : ℕ in atTop,
      ∀ a ∈ badOffsets largePowerTuple (2 ^ largeK),
        assignedPrime (2 ^ largeK) a ∣ bftPreSieveResidue N + a := by
  obtain ⟨D₀, hD₀⟩ := assignedPrime_le_cutoff_eventually
    largePowerTuple (2 ^ largeK)
  obtain ⟨N₀, hN₀⟩ := BoundedGaps.Maynard.exists_tripleLogCutoff_ge D₀
  filter_upwards [eventually_ge_atTop (N₀ + 1)] with N hN
  have hcut : D₀ ≤ BoundedGaps.Maynard.tripleLogCutoff (N - 1) :=
    hN₀ (N - 1) (by omega)
  obtain ⟨v, hvlt, hvcop, hvassign⟩ := exists_bftPreSieveResidueClass
    largePowerTuple_admissible
    (fun h hh => largePowerTuple_le_max hh)
    (hD₀ _ hcut)
  have hdata : BFTResidueData N v := by
    exact ⟨hvlt, hvcop, hvassign⟩
  have hex : ∃ v, BFTResidueData N v := ⟨v, hdata⟩
  simpa [bftPreSieveResidue, hex] using (Classical.choose_spec hex).2.2

theorem eventually_assignedPrime_le_cutoff :
    ∀ᶠ N : ℕ in atTop,
      ∀ a ∈ badOffsets largePowerTuple (2 ^ largeK),
        assignedPrime (2 ^ largeK) a ≤
          BoundedGaps.Maynard.tripleLogCutoff (N - 1) := by
  obtain ⟨D₀, hD₀⟩ := assignedPrime_le_cutoff_eventually
    largePowerTuple (2 ^ largeK)
  obtain ⟨N₀, hN₀⟩ := BoundedGaps.Maynard.exists_tripleLogCutoff_ge D₀
  filter_upwards [eventually_ge_atTop (N₀ + 1)] with N hN a ha
  exact hD₀ _ (hN₀ (N - 1) (by omega)) a ha

theorem eventually_assignedPrime_lt_scale :
    ∀ᶠ N : ℕ in atTop,
      ∀ a ∈ badOffsets largePowerTuple (2 ^ largeK),
        assignedPrime (2 ^ largeK) a < N := by
  let B := (badOffsets largePowerTuple (2 ^ largeK)).sup
    (assignedPrime (2 ^ largeK))
  filter_upwards [eventually_ge_atTop (B + 1)] with N hN a ha
  have hpB : assignedPrime (2 ^ largeK) a ≤ B :=
    Finset.le_sup (f := assignedPrime (2 ^ largeK)) ha
  omega

/-- A positive excess for the prescribed pre-sieved weight has a positive
summand with at least four prime shifts.  Positivity of that summand records
the required congruence class. -/
theorem exists_four_prime_shifts_in_residue_of_excess_pos
    {N v W : ℕ} {D : Finset (largePowerTuple → ℕ)}
    {lambda : (largePowerTuple → ℕ) → ℝ}
    (hpos : 0 < BoundedGaps.Maynard.sieveExcess largePowerTuple N 3
      (BoundedGaps.Maynard.preSievedSquareDivisorWeight
        largePowerTuple D lambda v W)) :
    ∃ n ∈ Finset.Ico N (2 * N),
      4 ≤ BoundedGaps.primeShiftCount largePowerTuple n ∧
      n ≡ v [MOD W] := by
  classical
  let w := BoundedGaps.Maynard.preSievedSquareDivisorWeight
    largePowerTuple D lambda v W
  have hw : ∀ n, 0 ≤ w n := by
    intro n
    exact BoundedGaps.Maynard.preSievedSquareDivisorWeight_nonneg _ _ _ _ _ _
  have hsum : 0 < ∑ n ∈ Finset.Ico N (2 * N),
      ((BoundedGaps.primeShiftCount largePowerTuple n : ℝ) - 3) * w n := by
    simpa only [← BoundedGaps.Maynard.sieveExcess_eq_sum] using hpos
  by_contra hnone
  push Not at hnone
  have hterm : ∀ n ∈ Finset.Ico N (2 * N),
      ((BoundedGaps.primeShiftCount largePowerTuple n : ℝ) - 3) * w n ≤ 0 := by
    intro n hn
    by_cases hc : 4 ≤ BoundedGaps.primeShiftCount largePowerTuple n
    · have hnotmod : ¬ n ≡ v [MOD W] := fun hm => hnone n hn hc hm
      have hwzero : w n = 0 := by
        simp [w, BoundedGaps.Maynard.preSievedSquareDivisorWeight, hnotmod]
      rw [hwzero, mul_zero]
    · have hcReal :
          (BoundedGaps.primeShiftCount largePowerTuple n : ℝ) ≤ 3 := by
        exact_mod_cast (by omega : BoundedGaps.primeShiftCount largePowerTuple n ≤ 3)
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hcReal) (hw n)
  exact (not_lt_of_ge (Finset.sum_nonpos hterm)) hsum

/-- Eventual positivity for the BFT residue family yields isolated four-prime
translates, retaining the congruence information discarded by the usual
Maynard positivity wrapper. -/
theorem hasIsolatedFourPowerPrimeShifts_of_eventually_positive_bft_excess
    {D : ℕ → Finset (largePowerTuple → ℕ)}
    {lambda : ℕ → (largePowerTuple → ℕ) → ℝ}
    (hpos : ∀ᶠ N : ℕ in atTop,
      0 < BoundedGaps.Maynard.sieveExcess largePowerTuple N 3
        (BoundedGaps.Maynard.preSievedSquareDivisorWeight
          largePowerTuple (D N) (lambda N) (bftPreSieveResidue N)
            (BoundedGaps.Maynard.engelsmaMaynardModulus N))) :
    HasIsolatedFourPowerPrimeShifts := by
  intro T
  have hassign := eventually_bftPreSieveResidue_assigned
  have hcutoff := eventually_assignedPrime_le_cutoff
  have hprimeBound := eventually_assignedPrime_lt_scale
  have hall := hpos.and (hassign.and (hcutoff.and hprimeBound))
  rw [eventually_atTop] at hall
  obtain ⟨N₀, hN₀⟩ := hall
  let N := max N₀ (T + 1)
  have hallN :
      0 < BoundedGaps.Maynard.sieveExcess largePowerTuple N 3
          (BoundedGaps.Maynard.preSievedSquareDivisorWeight
            largePowerTuple (D N) (lambda N) (bftPreSieveResidue N)
              (BoundedGaps.Maynard.engelsmaMaynardModulus N)) ∧
        (∀ a ∈ badOffsets largePowerTuple (2 ^ largeK),
          assignedPrime (2 ^ largeK) a ∣ bftPreSieveResidue N + a) ∧
        (∀ a ∈ badOffsets largePowerTuple (2 ^ largeK),
          assignedPrime (2 ^ largeK) a ≤
            BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ∧
          ∀ a ∈ badOffsets largePowerTuple (2 ^ largeK),
            assignedPrime (2 ^ largeK) a < N := by
    exact hN₀ N (le_max_left _ _)
  obtain ⟨n, hnIco, hcount, hnmod⟩ :=
    exists_four_prime_shifts_in_residue_of_excess_pos hallN.1
  refine ⟨n, ?_, hcount, ?_⟩
  · have hNn := (Finset.mem_Ico.mp hnIco).1
    have hTN : T + 1 ≤ N := le_max_right _ _
    omega
  · intro z hnz hzmax hzprime
    let a := z - n
    have hna : n + a = z := Nat.add_sub_of_le hnz.le
    have ha1 : 1 ≤ a := by dsimp [a]; omega
    have haM : a ≤ 2 ^ largeK := by dsimp [a]; omega
    by_cases haH : a ∈ largePowerTuple
    · exact ⟨a, haH, hna.symm⟩
    · have haBad : a ∈ badOffsets largePowerTuple (2 ^ largeK) := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ha1, haM⟩, haH⟩
      let p := assignedPrime (2 ^ largeK) a
      have hpPrime : p.Prime := assignedPrime_prime _ _
      have hpCut : p ≤ BoundedGaps.Maynard.tripleLogCutoff (N - 1) :=
        hallN.2.2.1 a haBad
      have hpW : p ∣ BoundedGaps.Maynard.engelsmaMaynardModulus N := by
        exact hpPrime.dvd_primorial_iff.mpr hpCut
      have hnmodp : n ≡ bftPreSieveResidue N [MOD p] :=
        Nat.ModEq.of_dvd hpW hnmod
      have hpva : p ∣ bftPreSieveResidue N + a := hallN.2.1 a haBad
      have hpna : p ∣ n + a := by
        apply Nat.modEq_zero_iff_dvd.mp
        exact (hnmodp.add_right a).trans (Nat.modEq_zero_iff_dvd.mpr hpva)
      have hpz : p ∣ z := by simpa only [hna] using hpna
      have hpEq : p = z := (Nat.prime_dvd_prime_iff_eq hpPrime hzprime).mp hpz
      have hpN : p < N := hallN.2.2.2 a haBad
      have hNn := (Finset.mem_Ico.mp hnIco).1
      omega

end

end Erdos6.Maynard
