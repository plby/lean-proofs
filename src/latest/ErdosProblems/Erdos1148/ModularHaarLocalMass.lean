import ErdosProblems.Erdos1148.ModularHaarMeasure

/-! # Local quotient mass for sets with injective projection -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Measure Function
open scoped MatrixGroups ENNReal Pointwise

lemma integral_smul_eq_smul_cancel_right (γ δ : SL(2, ℤ)) (g : SL(2, ℝ))
    (h : γ • g = δ • g) : γ = δ := by
  apply Matrix.SpecialLinearGroup.map_intCast_injective (R := ℝ)
  exact mul_right_cancel h

theorem haar_mass_le_modularHaarMeasure_image {E : Set SL(2, ℝ)}
    (hE : MeasurableSet E) (himage : MeasurableSet (modularMk '' E))
    (hinj : Set.InjOn modularMk E) :
    (Measure.haar (G := SL(2, ℝ))) E ≤ modularHaarMeasure (modularMk '' E) := by
  have hdisj : Pairwise (Disjoint on fun γ : SL(2, ℤ) => γ • E ∩ modularHaarDomain) := by
    intro γ δ hne
    apply Set.disjoint_left.mpr
    rintro g ⟨⟨a, ha, hag⟩, _⟩ ⟨⟨b, hb, hbg⟩, _⟩
    have hproj : modularMk a = modularMk b := by
      calc
        modularMk a = modularMk (γ • a) := (modularMk_integral_mul γ a).symm
        _ = modularMk (δ • b) := congrArg modularMk (hag.trans hbg.symm)
        _ = modularMk b := modularMk_integral_mul δ b
    have hab := hinj ha hb hproj
    subst b
    exact hne (integral_smul_eq_smul_cancel_right γ δ a (hag.trans hbg.symm))
  have hsub : (⋃ γ : SL(2, ℤ), γ • E ∩ modularHaarDomain) ⊆
      modularMk ⁻¹' (modularMk '' E) ∩ modularHaarDomain := by
    intro g hg
    obtain ⟨γ, ⟨a, ha, rfl⟩, hg⟩ := Set.mem_iUnion.mp hg
    exact ⟨⟨a, ha, (modularMk_integral_mul γ a).symm⟩, hg⟩
  calc
    (Measure.haar (G := SL(2, ℝ))) E =
        ∑' γ : SL(2, ℤ), (Measure.haar (G := SL(2, ℝ))) (γ • E ∩ modularHaarDomain) :=
      modularHaarDomain_isFundamentalDomain.measure_eq_tsum E
    _ = (Measure.haar (G := SL(2, ℝ))) (⋃ γ : SL(2, ℤ), γ • E ∩ modularHaarDomain) :=
      (measure_iUnion hdisj (fun γ => (hE.const_smul γ).inter measurableSet_modularHaarDomain)).symm
    _ ≤ (Measure.haar (G := SL(2, ℝ))) (modularMk ⁻¹' (modularMk '' E) ∩ modularHaarDomain) :=
      measure_mono hsub
    _ = modularHaarMeasure (modularMk '' E) := (modularHaarMeasure_apply himage).symm

theorem haar_mass_le_normalizedModularHaarMeasure_image {E : Set SL(2, ℝ)}
    (hE : MeasurableSet E) (himage : MeasurableSet (modularMk '' E))
    (hinj : Set.InjOn modularMk E) :
    (modularHaarMeasure Set.univ)⁻¹ * (Measure.haar (G := SL(2, ℝ))) E ≤
      normalizedModularHaarMeasure (modularMk '' E) := by
  change (modularHaarMeasure Set.univ)⁻¹ * (Measure.haar (G := SL(2, ℝ))) E ≤
    (modularHaarMeasure Set.univ)⁻¹ * modularHaarMeasure (modularMk '' E)
  exact mul_le_mul_right (haar_mass_le_modularHaarMeasure_image hE himage hinj) _

end Erdos1148.DukeArithmetic
