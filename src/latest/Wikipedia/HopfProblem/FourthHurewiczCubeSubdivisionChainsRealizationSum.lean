import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsRealization

/-!
# Signed realization as a sum of the actual individual realizations

The equality follows from the free ordered-chain generators and retains
the canonical integral action on actual singular chains.
-/

noncomputable section

namespace Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision

open FirstHurewicz SingularMayerVietoris HigherHurewicz.CubeTriangulation

variable {X : Type} [TopologicalSpace X]

private theorem linearMap_zsmul_apply {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] (r : ℤ) (f : M →ₗ[ℤ] N) (a : M) :
    (r • f) a = r • f a :=
  map_zsmul (LinearMap.evalAddMonoidHom a) r f

theorem orientedPrismRealization_eq_sum {n : ℕ} (p : C(CubeN (n + 1), X))
    (m : ℕ) (c : FormalChains (Fin 2 × Fin (n + 1)) (m + 1)) :
    orientedPrismRealization p m c =
      ∑ e : Equiv.Perm (Fin n), cubeOrientation e • prismCubeRealization p e m c := by
  classical
  have h : orientedPrismRealization p m =
      ∑ e : Equiv.Perm (Fin n), cubeOrientation e • prismCubeRealization p e m := by
    apply formalChains_ext
    intro v
    simp only [orientedPrismRealization_simplex, LinearMap.sum_apply,
      linearMap_zsmul_apply, prismCubeRealization_simplex]
  simpa only [LinearMap.sum_apply, linearMap_zsmul_apply] using LinearMap.congr_fun h c

end Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision
