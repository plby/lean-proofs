import ErdosProblems.Erdos587.SchwartzWeights
import ErdosProblems.Erdos587.ReciprocalPoisson

/-!
# Summing all reciprocal Fourier blocks

Uniform interval means and summable variation bounds control the whole
integer-indexed Fourier series, without a truncation or expanding blocks.
-/

open scoped BigOperators

namespace Erdos587

lemma tsum_int_eq_tsum_blocks {K : ℕ} (hK : 0 < K) {F : ℤ → ℂ} (hF : Summable F) :
    (∑' n : ℤ, F n) = ∑' j : ℤ, ∑ n ∈ Finset.range K, F ((K : ℤ) * j + n) := by
  let : NeZero K := ⟨hK.ne'⟩
  let e := Int.divModEquiv K
  have he : Summable (fun p : ℤ × Fin K => F (e.symm p)) :=
    hF.comp_injective e.symm.injective
  calc
    _ = ∑' p : ℤ × Fin K, F (e.symm p) := (e.symm.tsum_eq F).symm
    _ = ∑' j : ℤ, ∑' n : Fin K, F (e.symm (j, n)) := he.tsum_prod
    _ = _ := by
      apply tsum_congr
      intro j
      simp only [e, Int.divModEquiv_symm_apply, tsum_fintype, mul_comm]
      exact Fin.sum_univ_eq_sum_range (fun n : ℕ => F (j * (K : ℤ) + n)) K

/-- Sum a finite family of absolutely convergent series using a summable
bound on the first moment of each column. Absolute convergence is itself a
consequence of that column bound. -/
lemma sum_norm_tsum_le_of_column_bound {ι α : Type*} (D : Finset ι) (F : ι → α → ℂ)
    (V : α → ℝ) (hV : Summable V) (hbound : ∀ j, (∑ r ∈ D, ‖F r j‖) ≤ V j) :
    (∑ r ∈ D, ‖∑' j, F r j‖) ≤ ∑' j, V j := by
  have hsum : Summable (fun j => ∑ r ∈ D, ‖F r j‖) := by
    apply hV.of_norm_bounded
    intro j
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    exact hbound j
  have hnorm (r : ι) (hr : r ∈ D) : Summable (fun j => ‖F r j‖) := by
    apply hsum.of_norm_bounded
    intro j
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact Finset.single_le_sum (fun r _ => norm_nonneg (F r j)) hr
  calc
    _ ≤ ∑ r ∈ D, ∑' j, ‖F r j‖ := by
      exact Finset.sum_le_sum (fun r hr => norm_tsum_le_tsum_norm (hnorm r hr))
    _ = ∑' j, ∑ r ∈ D, ‖F r j‖ := (Summable.tsum_finsetSum hnorm).symm
    _ ≤ ∑' j, V j := hsum.tsum_le_tsum hbound hV

/-- A summable block-variation bound transfers an interval mean to the full
weighted series. The functions need not have unit modulus, so this also
applies after subtracting a complete-period mean. -/
lemma sum_norm_weighted_series_le_of_interval_means {ι : Type*} (D : Finset ι)
    (K : ℕ) (hK : 0 < K) (g w : ι → ℤ → ℂ) {C B : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hmean : ∀ (s : ι → ℤ) (l : ι → ℕ), (∀ r ∈ D, l r ≤ K) →
      (∑ r ∈ D, ‖∑ n ∈ Finset.range (l r), g r (s r + n)‖ ^ 2) ≤ B)
    (hvar : ∀ r ∈ D, ∀ j : ℤ,
      finiteVariationNorm (fun n => w r ((K : ℤ) * j + n)) K ≤
        C / (1 + |(j : ℝ)|) ^ 2)
    (hsum : ∀ r ∈ D, Summable (fun n : ℤ => w r n * g r n)) :
    (∑ r ∈ D, ‖∑' n : ℤ, w r n * g r n‖) ≤
      (C * Real.sqrt ((D.card : ℝ) * B)) * ∑' j : ℤ, 1 / (1 + |(j : ℝ)|) ^ 2 := by
  let F : ι → ℤ → ℂ := fun r j => ∑ n ∈ Finset.range K,
    w r ((K : ℤ) * j + n) * g r ((K : ℤ) * j + n)
  have hblock (j : ℤ) : (∑ r ∈ D, ‖F r j‖) ≤
      (C * Real.sqrt ((D.card : ℝ) * B)) * (1 / (1 + |(j : ℝ)|) ^ 2) := by
    have hV : 0 ≤ C / (1 + |(j : ℝ)|) ^ 2 := by positivity
    have h := sum_norm_weighted_le_of_partial_means D K
      (fun r n => g r ((K : ℤ) * j + n))
      (fun r n => w r ((K : ℤ) * j + n)) (fun _ => K) hV hB
      (fun _ _ => le_rfl) (fun l hl => hmean (fun _ => (K : ℤ) * j) l hl)
      (fun r hr => hvar r hr j)
    have heq : (C / (1 + |(j : ℝ)|) ^ 2) * Real.sqrt ((D.card : ℝ) * B) =
        (C * Real.sqrt ((D.card : ℝ) * B)) * (1 / (1 + |(j : ℝ)|) ^ 2) := by ring
    rw [heq] at h
    exact h
  have htotal := sum_norm_tsum_le_of_column_bound D F _
    (summable_block_decay.mul_left (C * Real.sqrt ((D.card : ℝ) * B))) hblock
  have heq (r : ι) (hr : r ∈ D) :
      (∑' n : ℤ, w r n * g r n) = ∑' j, F r j :=
    tsum_int_eq_tsum_blocks hK (hsum r hr)
  calc
    _ = ∑ r ∈ D, ‖∑' j, F r j‖ := Finset.sum_congr rfl (fun r hr => congrArg norm (heq r hr))
    _ ≤ _ := by simpa only [tsum_mul_left] using htotal

/-- Specialization to the reciprocal quadratic phases. -/
lemma sum_norm_weighted_series_le_of_block_variation {ι : Type*} (D : Finset ι)
    (K : ℕ) (hK : 0 < K) (θ β : ι → ℝ) (w : ι → ℤ → ℂ) {C B : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hmean : ∀ (s : ι → ℤ) (l : ι → ℕ), (∀ r ∈ D, l r ≤ K) →
      (∑ r ∈ D, ‖∑ n ∈ Finset.range (l r),
        phase (θ r * ((s r : ℝ) + n) ^ 2 + β r * ((s r : ℝ) + n))‖ ^ 2) ≤ B)
    (hvar : ∀ r ∈ D, ∀ j : ℤ,
      finiteVariationNorm (fun n => w r ((K : ℤ) * j + n)) K ≤
        C / (1 + |(j : ℝ)|) ^ 2)
    (hsum : ∀ r ∈ D, Summable (fun n : ℤ => w r n * phase (θ r * (n : ℝ) ^ 2 + β r * n))) :
    (∑ r ∈ D, ‖∑' n : ℤ, w r n * phase (θ r * (n : ℝ) ^ 2 + β r * n)‖) ≤
      (C * Real.sqrt ((D.card : ℝ) * B)) * ∑' j : ℤ, 1 / (1 + |(j : ℝ)|) ^ 2 := by
  apply sum_norm_weighted_series_le_of_interval_means D K hK _ w hC hB _ hvar hsum
  intro s l hl
  simpa only [Int.cast_add, Int.cast_natCast] using hmean s l hl

end Erdos587
