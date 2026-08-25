import Util.MaynardBFT.ProgressionIsolation
import Util.MaynardBFT.ProgressionWeights
import Util.MaynardBFT.Positivity

/-! # Arbitrarily late isolated prime clusters in the chosen progression -/

namespace MaynardBFT

open Filter Erdos6.Maynard BoundedGaps.Maynard

def ResidueData (H : Finset ℕ) (q b M N v : ℕ) : Prop :=
  v ≡ b [MOD q] ∧ (∀ h ∈ H, Nat.Coprime (v + h) (progressionModulus q N)) ∧
    ∀ a ∈ badOffsets H M, assignedPrime M a ∣ v + a

noncomputable def isolationResidue (H : Finset ℕ) (q b M N : ℕ) : ℕ := by
  classical
  exact if hex : ∃ v, ResidueData H q b M N v then Classical.choose hex else 0

theorem eventually_isolationResidue_data
    {H : Finset ℕ} {q b M : ℕ} (hq : 0 < q) (hb : b.Coprime q)
    (hH : BoundedGaps.IsAdmissible H)
    (hdiv : ∀ h ∈ H, q ∣ h) (hHM : ∀ h ∈ H, h ≤ M) (hqM : q ≤ M) :
    ∀ᶠ N : ℕ in atTop, ResidueData H q b M N (isolationResidue H q b M N) := by
  classical
  obtain ⟨D₀, hD₀⟩ := assignedPrime_le_cutoff_eventually H M
  filter_upwards [tendsto_shifted_tripleLogCutoff.eventually (eventually_ge_atTop D₀)]
    with N hN
  have hex : ∃ v, ResidueData H q b M N v :=
    exists_progression_isolating_residue hq hb hH hdiv hHM hqM (hD₀ _ hN)
  simpa only [isolationResidue, dif_pos hex] using Classical.choose_spec hex

theorem isolated_clusters_of_eventually_positive_excess
    {H : Finset ℕ} {q b M m : ℕ} {alpha : ℝ} {F : (H → ℝ) → ℝ}
    (hdata : ∀ᶠ N : ℕ in atTop, ResidueData H q b M N (isolationResidue H q b M N))
    (hpos : ∀ᶠ N : ℕ in atTop,
      0 < sieveExcess H N (m - 1 : ℕ)
        (progressionWeight H q alpha (isolationResidue H q b M) F N)) :
    ∀ T : ℕ, ∃ n : ℕ, T < n ∧ m ≤ BoundedGaps.primeShiftCount H n ∧ n ≡ b [MOD q] ∧
      ∀ z, n < z → z ≤ n + M → z.Prime → ∃ h ∈ H, z = n + h := by
  intro T
  obtain ⟨D₀, hD₀⟩ := assignedPrime_le_cutoff_eventually H M
  let B := (badOffsets H M).sup (assignedPrime M)
  have hall := hpos.and (hdata.and
    ((tendsto_shifted_tripleLogCutoff.eventually (eventually_ge_atTop D₀)).and
      (eventually_ge_atTop (B + 1))))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hall
  let N := max N₀ (T + 1)
  have hallN := hN₀ N (le_max_left _ _)
  obtain ⟨n, hnIco, hcount, hnmod⟩ := prime_shifts_in_residue_of_excess_pos hallN.1
  have hNn := (Finset.mem_Ico.mp hnIco).1
  have hTN : T + 1 ≤ N := le_max_right _ _
  have hnq : n ≡ b [MOD q] :=
    (hnmod.of_dvd (dvd_mul_right q (maynardModulus N))).trans hallN.2.1.1
  refine ⟨n, by omega, hcount, hnq, ?_⟩
  intro z hnz hzmax hzprime
  let a := z - n
  have hna : n + a = z := Nat.add_sub_of_le hnz.le
  have ha1 : 1 ≤ a := by dsimp [a]; omega
  have haM : a ≤ M := by dsimp [a]; omega
  by_cases haH : a ∈ H
  · exact ⟨a, haH, hna.symm⟩
  · have haBad : a ∈ badOffsets H M :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ha1, haM⟩, haH⟩
    let p := assignedPrime M a
    have hpPrime : p.Prime := assignedPrime_prime M a
    have hpCut : p ≤ tripleLogCutoff (N - 1) := hD₀ _ hallN.2.2.1 a haBad
    have hpW : p ∣ progressionModulus q N :=
      (hpPrime.dvd_primorial_iff.mpr hpCut).trans (Nat.dvd_mul_left _ _)
    have hpva : p ∣ isolationResidue H q b M N + a := hallN.2.1.2.2 a haBad
    have hpna : p ∣ n + a := ((hnmod.add_right a).dvd_iff hpW).mpr hpva
    have hpz : p ∣ z := by simpa only [hna] using hpna
    have hpEq : p = z := (Nat.prime_dvd_prime_iff_eq hpPrime hzprime).mp hpz
    have hpB : p ≤ B := Finset.le_sup (f := assignedPrime M) haBad
    have hBN := hallN.2.2.2
    omega

end MaynardBFT
