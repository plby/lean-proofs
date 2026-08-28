import Wikipedia.NoExoticSixSphere.SardRankInduction

/-!
# Sard's theorem on finite-dimensional real vector spaces

Strong induction on the source dimension combines the nonzero-rank Fubini
reduction with the finite-order vanishing strata and the high-order flat
estimate. The zero-dimensional source and target cases are included. No
lower-dimensional Sard hypothesis remains in the final theorem.
-/

open scoped ContDiff
open Set Module MeasureTheory MeasureTheory.Measure

namespace NoExoticSixSphere.Sard

theorem measure_criticalValues_eq_zero_of_finrank (n : ℕ) :
    ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
      [MeasurableSpace F] [BorelSpace F]
      (μ : Measure F) [IsAddHaarMeasure μ] (f : E → F) (U : Set E),
      finrank ℝ E = n → IsOpen U → ContDiffOn ℝ ∞ f U →
        μ (f '' {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x)}) = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E F _ _ _ _ _ _ _ _ μ _ f U hd hU hf
    rcases subsingleton_or_nontrivial F with hF | hF
    · let : Subsingleton F := hF
      apply measure_mono_null (t := ∅) _ (measure_empty (μ := μ))
      rintro _ ⟨x, hx, rfl⟩
      exact (hx.2 (fun y ↦ ⟨0, Subsingleton.elim _ _⟩)).elim
    · let : Nontrivial F := hF
      by_cases hn : n = 0
      · have hk : finrank ℝ E < (0 + 1) * finrank ℝ F := by
          simpa only [hd, hn, Nat.zero_add, one_mul] using (Module.finrank_pos (R := ℝ) (M := F))
        apply measure_mono_null _ (measure_image_flatPoints_eq_zero μ hU hf 0 hk)
        apply image_mono
        intro x hx
        exact ⟨hx.1, fun j hj hjk ↦ by omega⟩
      · have hlt : finrank ℝ E - 1 < n := by omega
        have hzero := measure_image_zero_derivative_of_lowerDimension μ
          (fun g V hV hg ↦ ih (finrank ℝ E - 1) hlt
            (EuclideanSpace ℝ (Fin (finrank ℝ E - 1))) F μ g V
            (by simp) hV hg) hU hf
        have hnonzero := measure_image_nonzero_critical_of_lowerDimension μ
          (fun g V hV hg ↦ ih (finrank ℝ E - 1) hlt
            (EuclideanSpace ℝ (Fin (finrank ℝ E - 1)))
            (EuclideanSpace ℝ (Fin (finrank ℝ F - 1))) volume g V
            (by simp) hV hg) hU hf
        apply measure_mono_null _ (measure_union_null hzero hnonzero)
        rintro _ ⟨x, hx, rfl⟩
        by_cases hD : fderiv ℝ f x = 0
        · exact Or.inl ⟨x, ⟨hx.1, hD⟩, rfl⟩
        · exact Or.inr ⟨x, ⟨hx.1, hx.2, hD⟩, rfl⟩

theorem measure_criticalValues_eq_zero
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [IsAddHaarMeasure μ]
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    μ (f '' {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x)}) = 0 :=
  measure_criticalValues_eq_zero_of_finrank (finrank ℝ E) E F μ f U rfl hU hf

end NoExoticSixSphere.Sard
