import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationSingular

/-!
# Original integral cochains extend along injective continuous maps

Extend the original function on singular-simplex generators, then use
the actual free-chain universal property. Pointwise injectivity makes
the original simplex map injective and gives the exact restriction
identity. No chosen topological retraction is needed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCochainExtension

open FirstHurewicz

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem simplex_comp_injective (f : C(X, Y)) (hf : Function.Injective f) (n : ℕ) :
    Function.Injective (fun σ : SingularSimplex X n ↦ f.comp σ) := by
  intro σ τ h
  apply ContinuousMap.ext
  intro x
  exact hf (ContinuousMap.congr_fun h x)

def extendCochain (f : C(X, Y)) (n : ℕ) (β : Chains X n →ₗ[ℤ] ℤ) :
    Chains Y n →ₗ[ℤ] ℤ :=
  chainLift Y n (Function.extend (fun σ : SingularSimplex X n ↦ f.comp σ)
    (fun σ ↦ β (simplexChain X n σ)) (fun _ ↦ 0))

theorem extendCochain_inducedChain (f : C(X, Y)) (hf : Function.Injective f)
    (n : ℕ) (β : Chains X n →ₗ[ℤ] ℤ) :
    (extendCochain f n β).comp (inducedChain f n) = β := by
  apply chainMap_ext X n
  intro σ
  rw [LinearMap.comp_apply, inducedChain_simplex]
  change chainLift Y n _ (simplexChain Y n (f.comp σ)) = _
  rw [chainLift_simplex]
  exact (simplex_comp_injective f hf n).extend_apply _ _ σ

theorem exists_cochain_extension (f : C(X, Y)) (hf : Function.Injective f)
    (n : ℕ) (β : Chains X n →ₗ[ℤ] ℤ) :
    ∃ B : Chains Y n →ₗ[ℤ] ℤ, B.comp (inducedChain f n) = β :=
  ⟨extendCochain f n β, extendCochain_inducedChain f hf n β⟩

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCochainExtension
