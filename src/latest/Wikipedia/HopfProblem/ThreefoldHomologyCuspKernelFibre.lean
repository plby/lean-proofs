import Wikipedia.HopfProblem.ThreefoldHomologyCuspKernelFibreMap
import Wikipedia.HopfProblem.ThreefoldHomologyCuspKernelCoinvariants

/-!
# The exact original cusp fibre kernel in every degree

The canonical map from genuine cusp Wang coinvariants onto the actual
full cap is surjective by the geometric fibre inclusion theorem.  Both
groups have independently proved finite free coordinates of ranks
`1, 2, 4, 2, 1`.  Integral equal-rank surjectivity makes this actual map
an isomorphism.  Consequently the exact fibre kernel is the range of
the original Wang difference, with no assumption about its marking.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ThreefoldHomologyCuspFibre

open SingularMayerVietoris MappingTorusHomology ThreefoldOverlapMappingTorus
open PeriodTorusHigherHomology SpecialPeriods.Threefold ThreefoldHomologyFinitenessCusp

local notation "f₀" => ThreefoldOverlapMappingTorus.monodromy none

/-- The actual quotient-to-cap map is bijective over the integers in every degree. -/
theorem cuspFibreCoinvariantMap_bijective (n : ℕ) :
    Function.Bijective (cuspFibreCoinvariantMap n) := by
  have := cuspWangCokernel_free n
  have := cuspWangCokernel_finite n
  have : Module.Free ℤ (SingularHomology (localPiece (some none)) n) :=
    fullHomology_free Cusp.specialData n
  have : Module.Finite ℤ (SingularHomology (localPiece (some none)) n) :=
    fullHomology_finite Cusp.specialData n
  have hr : Module.finrank ℤ (SingularHomology (localPiece (some none)) n) =
      CuspCentralHomology.centralBetti n := fullHomology_finrank Cusp.specialData n
  apply OrzechProperty.bijective_of_surjective_of_finrank_le
    (cuspFibreCoinvariantMap n) (cuspFibreCoinvariantMap_surjective n)
  rw [cuspWangCokernel_finrank, hr]

/-- The original fibre-to-cap coefficient induces this actual all-degree equivalence. -/
def cuspFibreCoinvariantEquiv (n : ℕ) :
    CuspWangCokernel n ≃ₗ[ℤ] SingularHomology (localPiece (some none)) n :=
  LinearEquiv.ofBijective (cuspFibreCoinvariantMap n) (cuspFibreCoinvariantMap_bijective n)

@[simp] theorem cuspFibreCoinvariantEquiv_toLinearMap (n : ℕ) :
    (cuspFibreCoinvariantEquiv n).toLinearMap = cuspFibreCoinvariantMap n := rfl

@[simp] theorem cuspFibreCoinvariantEquiv_apply (n : ℕ) (a : CuspWangCokernel n) :
    cuspFibreCoinvariantEquiv n a =
      boundaryFillingHomologyMap none n (cokernelInclusion f₀ n a) := rfl

/-- Quotient representatives map by the literal original fibre inclusion. -/
@[simp] theorem cuspFibreCoinvariantEquiv_mk (n : ℕ) (a : SingularHomology RealTorus₄ n) :
    cuspFibreCoinvariantEquiv n (Submodule.Quotient.mk a) =
      singularHomologyMap (fibreToFilling none) n a :=
  cuspFibreCoinvariantMap_mk n a

/-- The geometric original fibre kernel is precisely the true Wang-difference image. -/
theorem fibreToFilling_cusp_kernel_eq_wangDifference_range (n : ℕ) :
    LinearMap.ker (singularHomologyMap (fibreToFilling none) n) =
      LinearMap.range (wangDifference f₀ n) := by
  apply le_antisymm ?_ (cuspWangDifference_le_fibreCap_kernel n)
  intro a ha
  apply (Submodule.Quotient.mk_eq_zero _).mp
  apply (cuspFibreCoinvariantMap_bijective n).injective
  rw [cuspFibreCoinvariantMap_mk, map_zero]
  exact ha

/-- The original cap and original boundary kill exactly the same fibre classes. -/
theorem fibreToFilling_cusp_eq_zero_iff_fibreHomologyMap_eq_zero (n : ℕ)
    (a : SingularHomology RealTorus₄ n) :
    singularHomologyMap (fibreToFilling none) n a = 0 ↔ fibreHomologyMap f₀ n a = 0 := by
  change a ∈ LinearMap.ker (singularHomologyMap (fibreToFilling none) n) ↔
    a ∈ LinearMap.ker (fibreHomologyMap f₀ n)
  rw [fibreToFilling_cusp_kernel_eq_wangDifference_range, wang_exact_at_fibre]

end Wikipedia.HopfProblem.ThreefoldHomologyCuspFibre
