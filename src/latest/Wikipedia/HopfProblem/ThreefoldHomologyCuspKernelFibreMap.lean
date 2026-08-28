import Wikipedia.HopfProblem.ThreefoldHomologyCuspFibre
import Wikipedia.HopfProblem.MappingTorusHomology

/-!
# The actual cusp fibre map on genuine Wang coinvariants

Compose the original Wang cokernel inclusion with the original
boundary-to-filling coefficient.  This defines a canonical map on the
actual coinvariants in every degree.  Its value on a quotient class is
the literal fibre inclusion, and the already proved geometric fibre
surjectivity makes this quotient map surjective.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ThreefoldHomologyCuspFibre

open SingularMayerVietoris MappingTorusHomology ThreefoldOverlapMappingTorus
open PeriodTorusHigherHomology SpecialPeriods.Threefold

local notation "f₀" => ThreefoldOverlapMappingTorus.monodromy none

/-- The actual original cap map applied to the genuine Wang cokernel inclusion. -/
def cuspFibreCoinvariantMap (n : ℕ) :
    (SingularHomology RealTorus₄ n ⧸ LinearMap.range (wangDifference f₀ n)) →ₗ[ℤ]
      SingularHomology (localPiece (some none)) n :=
  intLinearMapOfAddHom
    { toFun a := boundaryFillingHomologyMap none n (cokernelInclusion f₀ n a)
      map_zero' := by rw [map_zero, map_zero]
      map_add' a b := by rw [map_add, map_add] }

@[simp] theorem cuspFibreCoinvariantMap_apply (n : ℕ)
    (a : SingularHomology RealTorus₄ n ⧸ LinearMap.range (wangDifference f₀ n)) :
    cuspFibreCoinvariantMap n a =
      boundaryFillingHomologyMap none n (cokernelInclusion f₀ n a) := rfl

/-- The canonical quotient map retains the literal original real-period fibre inclusion. -/
@[simp] theorem cuspFibreCoinvariantMap_mk (n : ℕ) (a : SingularHomology RealTorus₄ n) :
    cuspFibreCoinvariantMap n (Submodule.Quotient.mk a) =
      singularHomologyMap (fibreToFilling none) n a := by
  rw [cuspFibreCoinvariantMap_apply, cokernelInclusion_mk]
  exact LinearMap.congr_fun (boundaryFillingHomologyMap_fibre none n) a

/-- Surjectivity follows from the actual full fixed-radius cap geometry. -/
theorem cuspFibreCoinvariantMap_surjective (n : ℕ) :
    Function.Surjective (cuspFibreCoinvariantMap n) := by
  intro a
  obtain ⟨b, hb⟩ := fibreToFilling_homology_surjective n a
  exact ⟨Submodule.Quotient.mk b, (cuspFibreCoinvariantMap_mk n b).trans hb⟩

/-- Every genuine Wang difference is killed by the original cap fibre map. -/
theorem cuspWangDifference_le_fibreCap_kernel (n : ℕ) :
    LinearMap.range (wangDifference f₀ n) ≤
      LinearMap.ker (singularHomologyMap (fibreToFilling none) n) := by
  intro a ha
  have hq : (Submodule.Quotient.mk a :
      SingularHomology RealTorus₄ n ⧸ LinearMap.range (wangDifference f₀ n)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ha
  change singularHomologyMap (fibreToFilling none) n a = 0
  rw [← cuspFibreCoinvariantMap_mk, hq, map_zero]

end Wikipedia.HopfProblem.ThreefoldHomologyCuspFibre
