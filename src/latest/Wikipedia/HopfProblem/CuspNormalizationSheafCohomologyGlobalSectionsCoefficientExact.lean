import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyGlobalSectionsCoefficientComplex

/-!
# Explicit kernels and cokernels of the literal coefficient differential

The two cycle coordinates are the first and third curve coordinates;
the final quotient coordinate is the value at P minus the value at Q.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections

/-- The two independent cycles are (u, u+v, v). -/
def coefficientCycles : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun u := ![u 0, u 0 + u 1, u 1]
  map_add' u v := by
    ext i
    fin_cases i
    · rfl
    · change (u 0 + v 0) + (u 1 + v 1) = (u 0 + u 1) + (v 0 + v 1)
      abel
    · rfl
  map_smul' c u := by
    ext i
    fin_cases i
    · rfl
    · change c • u 0 + c • u 1 = c • (u 0 + u 1)
      exact (smul_add c (u 0) (u 1)).symm
    · rfl

theorem coefficientCycles_injective : Function.Injective coefficientCycles := by
  intro u v h
  ext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 2

instance coefficientCycles_mono : Mono (ModuleCat.ofHom coefficientCycles) := by
  apply ConcreteCategory.mono_of_injective
  exact coefficientCycles_injective

/-- The explicit cycle parametrization followed by the literal last differential. -/
abbrev coefficientKernelComplex : ShortComplex (ModuleCat ℂ) :=
  ShortComplex.moduleCatMk coefficientCycles coefficientDifferential (by
    apply LinearMap.ext
    intro u
    funext t
    change u 0 - (u 0 + u 1) + u 1 = 0
    abel)

theorem coefficientKernelComplex_exact : coefficientKernelComplex.Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have h : x 0 - x 1 + x 2 = 0 := congrFun hx 0
  refine ⟨![x 0, x 2], ?_⟩
  change coefficientCycles ![x 0, x 2] = x
  funext i
  fin_cases i
  · rfl
  · change x 0 + x 2 = x 1
    apply sub_eq_zero.mp
    exact (show x 0 + x 2 - x 1 = x 0 - x 1 + x 2 by abel).trans h
  · rfl

/-- The final quotient is measured by the actual source order P minus Q. -/
def coefficientDifference : (Fin 2 → ℂ) →ₗ[ℂ] ℂ where
  toFun b := b 0 - b 1
  map_add' b c := by
    simp only [Pi.add_apply]
    abel
  map_smul' c b := by
    simp only [Pi.smul_apply, smul_sub, RingHom.id_apply]

theorem coefficientDifference_surjective : Function.Surjective coefficientDifference := by
  intro c
  exact ⟨![c, 0], sub_zero c⟩

instance coefficientDifference_epi : Epi (ModuleCat.ofHom coefficientDifference) := by
  apply ConcreteCategory.epi_of_surjective
  exact coefficientDifference_surjective

/-- The literal differential followed by the actual difference of the endpoint coordinates. -/
abbrev coefficientCokernelComplex : ShortComplex (ModuleCat ℂ) :=
  ShortComplex.moduleCatMk coefficientDifferential coefficientDifference (by
    ext a
    exact sub_self _)

theorem coefficientCokernelComplex_exact : coefficientCokernelComplex.Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have h : x 0 = x 1 := sub_eq_zero.mp hx
  refine ⟨![x 0, 0, 0], ?_⟩
  change coefficientDifferential ![x 0, 0, 0] = x
  funext i
  fin_cases i
  · change x 0 - 0 + 0 = x 0
    simp only [sub_zero, add_zero]
  · change x 0 - 0 + 0 = x 1
    simpa only [sub_zero, add_zero] using h

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections
