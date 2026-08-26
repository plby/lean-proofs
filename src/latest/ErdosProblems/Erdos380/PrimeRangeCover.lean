import ErdosProblems.Erdos380.SingletonBands

/-! # A finite cover of the exceptional prime ranges -/

open Filter
open scoped Topology BigOperators

namespace Erdos380

lemma exists_power_band {S a b p : ℕ} (hS : 1 ≤ S) (hap : S ^ a < p) (hpb : p ≤ S ^ b) :
    ∃ j ∈ Finset.Ico a b, S ^ j < p ∧ p ≤ S ^ (j + 1) := by
  let hex : ∃ j : ℕ, p ≤ S ^ j := ⟨b, hpb⟩
  let J := Nat.find hex
  have hJ : p ≤ S ^ J := Nat.find_spec hex
  have hJb : J ≤ b := Nat.find_min' hex hpb
  have haJ : a < J := by
    by_contra h
    have hJa : J ≤ a := by omega
    have hpower : S ^ J ≤ S ^ a := pow_le_pow_right₀ hS hJa
    omega
  have hJpos : 0 < J := by omega
  have hjJ : J - 1 < J := by omega
  have hlow : S ^ (J - 1) < p := Nat.lt_of_not_ge (Nat.find_min hex hjJ)
  refine ⟨J - 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hlow, ?_⟩
  simpa only [Nat.sub_add_cancel (show 1 ≤ J by omega)] using hJ

def exceptionalPrimeBands : Finset ℕ := Finset.Ico 490 920 ∪ Finset.Ico 1100 2005

lemma exceptionalPrimeBands_lt {j : ℕ} (hj : j ∈ exceptionalPrimeBands) : j < 2005 := by
  simp only [exceptionalPrimeBands, Finset.mem_union, Finset.mem_Ico] at hj
  omega

lemma exceptionalPrimeBands_rankin_margin {j : ℕ} (hj : j ∈ exceptionalPrimeBands) :
    (j + 1) * (2005 - j) < 1000000 := by
  have hjle : j ≤ 2005 := (exceptionalPrimeBands_lt hj).le
  have hsub : ((2005 - j : ℕ) : ℝ) = 2005 - (j : ℝ) := by
    rw [Nat.cast_sub hjle]
    norm_num
  have hreal : ((j : ℝ) + 1) * (2005 - (j : ℝ)) < 1000000 := by
    simp only [exceptionalPrimeBands, Finset.mem_union, Finset.mem_Ico] at hj
    rcases hj with hj | hj
    · have hjhi : (j : ℝ) ≤ 919 := by exact_mod_cast (by omega : j ≤ 919)
      have hm : 0 ≤ (919 - (j : ℝ)) * (1085 - (j : ℝ)) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    · have hjlo : (1100 : ℝ) ≤ j := by exact_mod_cast hj.1
      have hm : 0 ≤ ((j : ℝ) - 1100) * ((j : ℝ) - 904) := mul_nonneg (by linarith) (by linarith)
      nlinarith
  have hcast : (((j + 1) * (2005 - j) : ℕ) : ℝ) < 1000000 := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, hsub] using hreal
  exact_mod_cast hcast

noncomputable def exceptionalPrimeBandSingletons (N : ℕ) : Finset ℕ :=
  exceptionalPrimeBands.biUnion fun j => singletonPrimeBand N (scaleBase N ^ j) (scaleBase N ^ (j + 1))

lemma singletonPrimeBand_power_subset_biUnion (N S a b : ℕ) (hS : 1 ≤ S) (F : Finset ℕ)
    (hab : Finset.Ico a b ⊆ F) :
    singletonPrimeBand N (S ^ a) (S ^ b) ⊆ F.biUnion (fun j => singletonPrimeBand N (S ^ j) (S ^ (j + 1))) := by
  classical
  intro n hn
  obtain ⟨hnA, hlo, hhi⟩ := Finset.mem_filter.mp hn
  obtain ⟨j, hj, hjlo, hjhi⟩ := exists_power_band hS hlo hhi
  exact Finset.mem_biUnion.mpr ⟨j, hab hj, Finset.mem_filter.mpr ⟨hnA, hjlo, hjhi⟩⟩

lemma singletonPrimeBand_power_subset_exceptional (N a b : ℕ)
    (hab : Finset.Ico a b ⊆ exceptionalPrimeBands) :
    singletonPrimeBand N (scaleBase N ^ a) (scaleBase N ^ b) ⊆ exceptionalPrimeBandSingletons N :=
  singletonPrimeBand_power_subset_biUnion N (scaleBase N) a b (one_le_scaleBase N) exceptionalPrimeBands hab

theorem eventually_exceptionalPrimeBandSingletons_bound : ∀ᶠ N : ℕ in atTop,
    ((exceptionalPrimeBandSingletons N).card : ℝ) ≤
      (2 * exceptionalPrimeBands.card : ℝ) * N / (scaleBase N : ℝ) ^ 2005 := by
  have hbands : ∀ᶠ N : ℕ in atTop, ∀ j ∈ exceptionalPrimeBands,
      ((singletonPrimeBand N (scaleBase N ^ j) (scaleBase N ^ (j + 1))).card : ℝ) ≤
        2 * N / (scaleBase N : ℝ) ^ 2005 := by
    apply (eventually_all_finset exceptionalPrimeBands).mpr
    intro j hj
    have heq : j + (2005 - j) = 2005 := Nat.add_sub_of_le (exceptionalPrimeBands_lt hj).le
    simpa only [heq] using eventually_singletonPrimeBand_scale_bound j (2005 - j)
      (exceptionalPrimeBands_rankin_margin hj)
  filter_upwards [hbands] with N hN
  calc
    ((exceptionalPrimeBandSingletons N).card : ℝ) ≤
        ∑ j ∈ exceptionalPrimeBands,
          ((singletonPrimeBand N (scaleBase N ^ j) (scaleBase N ^ (j + 1))).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := exceptionalPrimeBands)
        (t := fun j => singletonPrimeBand N (scaleBase N ^ j) (scaleBase N ^ (j + 1))))
    _ ≤ ∑ _ ∈ exceptionalPrimeBands, 2 * (N : ℝ) / (scaleBase N : ℝ) ^ 2005 :=
      Finset.sum_le_sum hN
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end Erdos380
