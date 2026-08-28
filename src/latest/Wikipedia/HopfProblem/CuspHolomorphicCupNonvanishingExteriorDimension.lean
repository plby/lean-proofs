import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyDimensions
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The actual exterior-square dimension in the cusp calculation

The dimension is for the genuine exterior power of the original
Ext-defined holomorphic H¹, with the original pointwise complex scalar
action. Its value follows from the proved holomorphic cohomology
calculation, not from an assumed description of the cup product.
-/

noncomputable section

open CategoryTheory
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspHolomorphicCupNonvanishing

open CuspNormalization SheafResolution CuspQuotient ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
  (hR : SmallDrift C r)

/-- The actual exterior square of holomorphic H¹ has complex dimension one. -/
theorem holomorphicExterior_finrank :
    Module.finrank ℂ
      (⋀[ℂ]^2 (CategoryTheory.Sheaf.H.{0} (reducedSheaf C r hr hr1 hC hR) 1)) = 1 := by
  let : Module.Finite ℂ (CategoryTheory.Sheaf.H.{0} (reducedSheaf C r hr hr1 hC hR) 1) :=
    Module.finite_of_finrank_pos (by
      rw [SheafCohomology.reducedH1_finrank C r hr hr1 hC hR]
      decide)
  rw [exteriorPower.finrank_eq, SheafCohomology.reducedH1_finrank C r hr hr1 hC hR]
  rfl

/-- A nonzero linear map between actual one-dimensional vector spaces is bijective. -/
theorem bijective_of_finrank_one {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (f : V →ₗ[ℂ] W)
    (hV : Module.finrank ℂ V = 1) (hW : Module.finrank ℂ W = 1) (hf : f ≠ 0) :
    Function.Bijective f := by
  let : FiniteDimensional ℂ V := FiniteDimensional.of_finrank_eq_succ hV
  let : FiniteDimensional ℂ W := FiniteDimensional.of_finrank_eq_succ hW
  have hs : Function.Surjective f := surjective_of_nonzero_of_finrank_eq_one hW hf
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (hV.trans hW.symm)).mpr hs, hs⟩

end Wikipedia.HopfProblem.CuspHolomorphicCupNonvanishing
