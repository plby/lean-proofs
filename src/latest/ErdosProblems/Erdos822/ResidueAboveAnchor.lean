/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.LargeDivisorRigidity
import ErdosProblems.Erdos822.IntegerResidueBlocks

/-! # Reciprocal progressions strictly above a representative -/

namespace Erdos822

open scoped BigOperators Classical

theorem sum_inv_integerResidueInterval_above_anchor_le {d a U : ℕ} (hd : 0 < d) :
    (∑ q ∈ integerResidueInterval d a a U, (1 : ℝ) / q) ≤ (harmonic U : ℝ) / d := by
  let Q := integerResidueInterval d a a U
  have hsub : Q.image (fun q ↦ q - a) ⊆ (Finset.Icc 1 U).filter (d ∣ ·) := by
    intro n hn
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨haq, hqU, hmod⟩ := mem_integerResidueInterval_iff.mp hq
    have hamod : a ≡ q [MOD d] := hmod.symm
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hamod.dvd'⟩
  have hinj : Set.InjOn (fun q ↦ q - a) Q := by
    intro q hq q' hq' heq
    have hqa := (mem_integerResidueInterval_iff.mp hq).1
    have hq'a := (mem_integerResidueInterval_iff.mp hq').1
    change q - a = q' - a at heq
    omega
  calc
    _ ≤ ∑ q ∈ Q, (1 : ℝ) / (q - a : ℕ) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqa := (mem_integerResidueInterval_iff.mp hq).1
      exact one_div_le_one_div_of_le (by exact_mod_cast (show 0 < q - a by omega))
        (by exact_mod_cast Nat.sub_le q a)
    _ = ∑ n ∈ Q.image (fun q ↦ q - a), (1 : ℝ) / n := by rw [Finset.sum_image hinj]
    _ ≤ ∑ n ∈ (Finset.Icc 1 U).filter (d ∣ ·), (1 : ℝ) / n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn hnot ↦ by positivity)
    _ = (harmonic (U / d) : ℝ) / d := sum_inv_filter_Icc_dvd_eq_harmonic_div hd
    _ ≤ (harmonic U : ℝ) / d :=
      div_le_div_of_nonneg_right (harmonic_cast_mono (Nat.div_le_self U d)) (by positivity)

theorem sum_inv_largePrimes_above_anchor_modEq_le {N d a : ℕ}
    (hN : 1 ≤ N) (hd : 0 < d) :
    (∑ q ∈ (largePrimes N).filter (fun q ↦ a < q ∧ q ≡ a [MOD d]), (1 : ℝ) / q) ≤
      23 * (harmonic N : ℝ) / d := by
  have hsub : (largePrimes N).filter (fun q ↦ a < q ∧ q ≡ a [MOD d]) ⊆
      integerResidueInterval d a a (N ^ 22) := by
    intro q hq
    obtain ⟨hq, haq, hmod⟩ := Finset.mem_filter.mp hq
    exact mem_integerResidueInterval_iff.mpr ⟨haq, (mem_largePrimes_iff.mp hq).2.1, hmod⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q hq hnot ↦ by positivity)).trans ?_
  refine (sum_inv_integerResidueInterval_above_anchor_le hd).trans ?_
  have hH := harmonic_pow_le_mul_harmonic hN 22
  norm_num at hH
  exact div_le_div_of_nonneg_right hH (by positivity)

#print axioms sum_inv_largePrimes_above_anchor_modEq_le

end Erdos822
