import ErdosProblems.Erdos421.LargePrimeCofactors

/-! # Divisibility bounds for errors from freezing a roughness cutoff -/

namespace Erdos421

theorem roughIndicator_antitone (n : ℕ) : Antitone (roughIndicator n) := by
  classical
  intro w z hwz
  unfold roughIndicator
  by_cases hz : RoughAt n z
  · simp [hz, hz.mono hwz]
  · simp only [hz, ↓reduceIte]
    split_ifs <;> norm_num

theorem roughIndicator_difference_le (n : ℕ) {w z : ℕ} (hwz : w ≤ z) :
    roughIndicator n w - roughIndicator n z ≤
      ∑ p ∈ sievePrimes w z, if p ∣ n then (1 : ℝ) else 0 := by
  classical
  by_cases hw : RoughAt n w
  · by_cases hz : RoughAt n z
    · simp [roughIndicator, hw, hz]
    · have hn1 : n ≠ 1 := by
        intro hn1
        exact hz (roughAt_iff_minFac.mpr (Or.inl hn1))
      have hl : w ≤ n.minFac := (roughAt_iff_minFac.mp hw).resolve_left hn1
      have hu : n.minFac < z := by
        by_contra h
        exact hz (roughAt_iff_minFac.mpr (Or.inr (by omega)))
      have hp : n.minFac ∈ sievePrimes w z :=
        Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hl, hu⟩, Nat.minFac_prime hn1⟩
      have h := Finset.single_le_sum
        (f := fun p ↦ if p ∣ n then (1 : ℝ) else 0)
        (fun p _ ↦ by split_ifs <;> norm_num) hp
      simpa [roughIndicator, hw, hz, Nat.minFac_dvd] using h
  · have hz : ¬ RoughAt n z := fun h ↦ hw (h.mono hwz)
    simp [roughIndicator, hw, hz]

theorem primeCofactorWeight_antitone (P : Finset ℕ) (n : ℕ) :
    Antitone (fun z ↦ primeCofactorWeight P z n) := by
  intro w z hwz
  apply Finset.sum_le_sum
  intro p hp
  split_ifs
  · exact roughIndicator_antitone _ hwz
  · exact le_rfl

theorem primeCofactorWeight_difference_le (P : Finset ℕ) (n : ℕ) {w z : ℕ}
    (hwz : w ≤ z) :
    primeCofactorWeight P w n - primeCofactorWeight P z n ≤
      ∑ p ∈ P, ∑ q ∈ sievePrimes w z, if p * q ∣ n then (1 : ℝ) else 0 := by
  classical
  rw [primeCofactorWeight, primeCofactorWeight, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro p hp
  by_cases hpn : p ∣ n
  · simp only [hpn, ↓reduceIte]
    calc
      _ ≤ ∑ q ∈ sievePrimes w z, if q ∣ n / p then (1 : ℝ) else 0 :=
        roughIndicator_difference_le (n / p) hwz
      _ = _ := by
        apply Finset.sum_congr rfl
        intro q hq
        simp only [Nat.dvd_div_iff_mul_dvd hpn]
  · simp only [hpn, ↓reduceIte, sub_self]
    exact Finset.sum_nonneg (fun q _ ↦ by split_ifs <;> norm_num)

end Erdos421
