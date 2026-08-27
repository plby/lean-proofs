/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.PrimeCounting

/-!
# Dimension-uniform rough-prime power tails

The loss linear in the sieve dimension is cancelled by beginning the
reciprocal three-halves-power sum above its square. The proof compares
with all integers, so it needs no prime-number asymptotic.
-/

namespace Erdos4b.FGKMT

noncomputable section

open MeasureTheory
open scoped BigOperators

theorem sum_Ioc_neg_three_halves_le {k : ℕ} (hk : 0 < k) (N : ℕ) :
    (∑ n ∈ Finset.Ioc (k ^ 2) N, (n : ℝ) ^ (-3 / 2 : ℝ)) ≤ 2 / (k : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkSq : (0 : ℝ) < (k ^ 2 : ℕ) := by exact_mod_cast pow_pos hk 2
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-3 / 2 : ℝ))
      (Set.Ici (k ^ 2 : ℕ)) := by
    intro a ha b _ hab
    exact Real.rpow_le_rpow_of_nonpos (hkSq.trans_le ha) hab (by norm_num)
  have hint : IntegrableOn (fun t : ℝ => t ^ (-3 / 2 : ℝ))
      (Set.Ioi (k ^ 2 : ℕ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hkSq
  have hsum := (hanti.mono Set.Icc_subset_Ici_self).sum_Ico_le_integral (b := N)
    hint (fun t ht => Real.rpow_nonneg (hkSq.le.trans ht.le) _)
  have hshift :
      (∑ n ∈ Finset.Ico (k ^ 2) N, ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) =
        ∑ n ∈ Finset.Ioc (k ^ 2) N, (n : ℝ) ^ (-3 / 2 : ℝ) := by
    apply Finset.sum_bij (fun n _ => n + 1)
    · intro n hn
      simp only [Finset.mem_Ico] at hn
      simp only [Finset.mem_Ioc]
      omega
    · intro a _ b _ hab
      omega
    · intro n hn
      simp only [Finset.mem_Ioc] at hn
      refine ⟨n - 1, ?_, ?_⟩
      · simp only [Finset.mem_Ico]
        omega
      · omega
    · intro n _
      rfl
  rw [hshift] at hsum
  have hpower : ((k ^ 2 : ℕ) : ℝ) ^ ((-3 / 2 : ℝ) + 1) = (k : ℝ)⁻¹ := by
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul hkR.le]
    norm_num [Real.rpow_neg_one]
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1) hkSq, hpower] at hsum
  convert hsum using 1
  ring

def roughQuarterMajorant (k p : ℕ) : ℝ :=
  if k ^ 2 < p then (4 * (k : ℝ) + 2) * (p : ℝ) ^ (-3 / 2 : ℝ) else 0

theorem roughQuarterMajorant_nonneg (k p : ℕ) : 0 ≤ roughQuarterMajorant k p := by
  unfold roughQuarterMajorant
  split_ifs <;> positivity

theorem sum_roughQuarterMajorant_primesBelow_le {k : ℕ} (hk : 0 < k) (N : ℕ) :
    (∑ p ∈ N.primesBelow, roughQuarterMajorant k p) ≤ 12 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkOne : (1 : ℝ) ≤ k := by exact_mod_cast hk
  let s := N.primesBelow.filter (fun p => k ^ 2 < p)
  have hsub : s ⊆ Finset.Ioc (k ^ 2) N := by
    intro p hp
    obtain ⟨hpN, hpk⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Ioc.mpr ⟨hpk, (Nat.lt_of_mem_primesBelow hpN).le⟩
  calc
    (∑ p ∈ N.primesBelow, roughQuarterMajorant k p) =
        (4 * (k : ℝ) + 2) * ∑ p ∈ s, (p : ℝ) ^ (-3 / 2 : ℝ) := by
      simp only [roughQuarterMajorant, ← Finset.sum_filter, Finset.mul_sum, s]
    _ ≤ (4 * (k : ℝ) + 2) *
        ∑ p ∈ Finset.Ioc (k ^ 2) N, (p : ℝ) ^ (-3 / 2 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    _ ≤ (4 * (k : ℝ) + 2) * (2 / (k : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_Ioc_neg_three_halves_le hk N) (by positivity)
    _ ≤ 12 := by
      rw [← mul_div_assoc, div_le_iff₀ hkR]
      linarith

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.sum_roughQuarterMajorant_primesBelow_le
