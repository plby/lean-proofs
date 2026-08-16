import ErdosProblems.Erdos6.BFTExtraction
import Mathlib.Data.Nat.ChineseRemainder

/-!
# A pre-sieve residue isolating the powers-of-two tuple

For every unwanted offset `a`, choose a distinct fixed prime `p_a` larger
than all offsets.  The Chinese remainder theorem sets `v ≡ -a (mod p_a)`.
At all other pre-sieve primes it chooses an arbitrary residue avoided by the
admissible tuple.  Once the triple-log primorial contains the finitely many
`p_a`, the resulting class is both a valid Maynard pre-sieve class and makes
every unwanted translate composite.
-/

namespace Erdos6.Maynard

open scoped BigOperators Function

noncomputable section

def badOffsets (H : Finset ℕ) (M : ℕ) : Finset ℕ :=
  (Finset.Icc 1 M).filter fun a => a ∉ H

noncomputable def assignedPrime (M a : ℕ) : ℕ :=
  Nat.nth Nat.Prime (M + a + 1)

theorem assignedPrime_prime (M a : ℕ) :
    (assignedPrime M a).Prime := by
  exact Nat.prime_nth_prime (M + a + 1)

theorem assignedPrime_gt (M a : ℕ) : M < assignedPrime M a := by
  have hle : M + a + 1 ≤ Nat.nth Nat.Prime (M + a + 1) := by
    apply Nat.le_nth
    intro hf
    exact (Nat.infinite_setOfPred_prime hf).elim
  exact lt_of_lt_of_le (by omega) hle

theorem assignedPrime_injective (M : ℕ) :
    Function.Injective (assignedPrime M) := by
  intro a b hab
  have hi : M + a + 1 = M + b + 1 :=
    Nat.nth_injective Nat.infinite_setOfPred_prime hab
  omega

def assignedPrimes (H : Finset ℕ) (M : ℕ) : Finset ℕ :=
  (badOffsets H M).image (assignedPrime M)

theorem mem_assignedPrimes_iff {H : Finset ℕ} {M p : ℕ} :
    p ∈ assignedPrimes H M ↔
      ∃ a ∈ badOffsets H M, assignedPrime M a = p := by
  simp [assignedPrimes]

theorem badOffset_data {H : Finset ℕ} {M a : ℕ}
    (ha : a ∈ badOffsets H M) :
    1 ≤ a ∧ a ≤ M ∧ a ∉ H := by
  have h := (Finset.mem_filter.mp ha)
  have hi := Finset.mem_Icc.mp h.1
  exact ⟨hi.1, hi.2, h.2⟩

theorem assignedPrime_le_cutoff_eventually (H : Finset ℕ) (M : ℕ) :
    ∃ D₀ : ℕ, ∀ D, D₀ ≤ D →
      ∀ a ∈ badOffsets H M, assignedPrime M a ≤ D := by
  let D₀ := (badOffsets H M).sup (assignedPrime M)
  refine ⟨D₀, ?_⟩
  intro D hD a ha
  exact (Finset.le_sup (f := assignedPrime M) ha).trans hD

/-- CRT with prescribed avoided residues at the assigned primes. -/
theorem exists_bftPreSieveResidueClass
    {H : Finset ℕ} {M D : ℕ}
    (hH : BoundedGaps.IsAdmissible H)
    (hHM : ∀ h ∈ H, h ≤ M)
    (hD : ∀ a ∈ badOffsets H M, assignedPrime M a ≤ D) :
    ∃ v : ℕ, v < primorial D ∧
      (∀ h ∈ H, Nat.Coprime (v + h) (primorial D)) ∧
      ∀ a ∈ badOffsets H M, assignedPrime M a ∣ v + a := by
  classical
  let P := D.primesLE
  have hP : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primesLE hp
  have havoided : ∀ p ∈ P, ∃ r < p,
      (∀ h ∈ H, h % p ≠ r) ∧
      ∀ a ∈ badOffsets H M, assignedPrime M a = p → r = a := by
    intro p hpP
    by_cases hpAssigned : p ∈ assignedPrimes H M
    · obtain ⟨a, haBad, hpa⟩ := mem_assignedPrimes_iff.mp hpAssigned
      have haData := badOffset_data haBad
      have hpM : M < p := by rw [← hpa]; exact assignedPrime_gt M a
      have hap : a < p := haData.2.1.trans_lt hpM
      refine ⟨a, hap, ?_, ?_⟩
      · intro h hhH
        have hhM := hHM h hhH
        have hhp : h < p := hhM.trans_lt hpM
        have hne : h ≠ a := by
          intro hha
          subst h
          exact haData.2.2 hhH
        simpa [Nat.mod_eq_of_lt hhp, Nat.mod_eq_of_lt hap] using hne
      · intro b hbBad hpb
        have hinj := assignedPrime_injective M
        exact hinj (hpa.trans hpb.symm)
    · obtain ⟨r, hrp, hrAvoid⟩ :=
        (BoundedGaps.isAdmissible_iff_avoids_residue H).mp hH p (hP p hpP)
      refine ⟨r, hrp, hrAvoid, ?_⟩
      intro a haBad hpa
      exact False.elim (hpAssigned (mem_assignedPrimes_iff.mpr
        ⟨a, haBad, hpa⟩))
  choose chosen chosen_lt chosen_avoid chosen_assigned using havoided
  let residue : ℕ → ℕ := fun p =>
    if hp : p ∈ P then p - chosen p hp else 0
  have hnonzero : ∀ p ∈ P, p ≠ 0 := by
    intro p hp
    exact (hP p hp).ne_zero
  have hpairwise : Set.Pairwise (P : Set ℕ) (Nat.Coprime on id) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq
  let v : ℕ := Nat.chineseRemainderOfFinset residue id P hnonzero hpairwise
  have hvlt : v < ∏ p ∈ P, p :=
    Nat.chineseRemainderOfFinset_lt_prod residue id hnonzero hpairwise
  have hvcoprime : ∀ h ∈ H, Nat.Coprime (v + h) (∏ p ∈ P, p) := by
    intro h hh
    apply Nat.Coprime.prod_right
    intro p hp
    apply Nat.Coprime.symm
    apply (hP p hp).coprime_iff_not_dvd.mpr
    intro hpdiv
    have hv : v ≡ residue p [MOD p] :=
      (Nat.chineseRemainderOfFinset residue id P hnonzero hpairwise).property p hp
    have hzero : v + h ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hpdiv
    have hzeroResidue : 0 ≡ residue p + h [MOD p] :=
      hzero.symm.trans (hv.add_right h)
    have hadd := hzeroResidue.add_right (chosen p hp)
    have hchosenLe : chosen p hp ≤ p := (chosen_lt p hp).le
    have hchosenMod : chosen p hp ≡ h [MOD p] := by
      simp only [residue, dif_pos hp] at hadd
      have hpadd : p + h ≡ h [MOD p] := by simp [Nat.ModEq]
      have : chosen p hp ≡ p + h [MOD p] := by
        convert hadd using 1 <;> omega
      exact this.trans hpadd
    have hmod : h % p = chosen p hp := by
      unfold Nat.ModEq at hchosenMod
      simpa [Nat.mod_eq_of_lt (chosen_lt p hp)] using hchosenMod.symm
    exact chosen_avoid p hp h hh hmod
  have hvassigned : ∀ a ∈ badOffsets H M, assignedPrime M a ∣ v + a := by
    intro a haBad
    let p := assignedPrime M a
    have hpPrime : p.Prime := assignedPrime_prime M a
    have hpP : p ∈ P := by
      exact Nat.mem_primesLE.mpr ⟨hD a haBad, hpPrime⟩
    have hvmod : v ≡ residue p [MOD p] :=
      (Nat.chineseRemainderOfFinset residue id P hnonzero hpairwise).property p hpP
    have hchosen : chosen p hpP = a :=
      chosen_assigned p hpP a haBad rfl
    have haLt : a < p := (badOffset_data haBad).2.1.trans_lt (assignedPrime_gt M a)
    have hsum : residue p + a = p := by
      simp only [residue, dif_pos hpP]
      rw [hchosen]
      omega
    apply Nat.modEq_zero_iff_dvd.mp
    have := hvmod.add_right a
    rw [hsum] at this
    simpa [Nat.ModEq] using this
  simpa only [P, primorial_eq_prod_primesLE] using
    ⟨v, hvlt, hvcoprime, hvassigned⟩

/-- The BFT residue exists for every sufficiently large triple-log cutoff. -/
theorem eventually_exists_bftPreSieveResidueClass
    {H : Finset ℕ} {M : ℕ}
    (hH : BoundedGaps.IsAdmissible H)
    (hHM : ∀ h ∈ H, h ≤ M) :
    ∀ᶠ D : ℕ in Filter.atTop, ∃ v : ℕ, v < primorial D ∧
      (∀ h ∈ H, Nat.Coprime (v + h) (primorial D)) ∧
      ∀ a ∈ badOffsets H M, assignedPrime M a ∣ v + a := by
  obtain ⟨D₀, hD₀⟩ := assignedPrime_le_cutoff_eventually H M
  filter_upwards [Filter.eventually_ge_atTop D₀] with D hD
  exact exists_bftPreSieveResidueClass hH hHM (hD₀ D hD)

end

end Erdos6.Maynard
