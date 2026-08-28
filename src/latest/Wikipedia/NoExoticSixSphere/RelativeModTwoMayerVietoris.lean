import Wikipedia.NoExoticSixSphere.RelativeModTwoSmallSequence
import Wikipedia.NoExoticSixSphere.ModTwoDualBiproduct
import Wikipedia.NoExoticSixSphere.RelativeMayerVietoris

/-!
# Mayer--Vietoris for actual relative mod-two cohomology

The native small-cochain sequence is transported through the original
open-union comparison and the canonical biproduct comparison. All terms
are the actual relative cohomology groups, and the connecting map comes
from the proved short exact cochain row.
-/

noncomputable section

open CategoryTheory Limits

namespace NoExoticSixSphere.RelativeModTwoMayerVietoris

open RelativeModTwoCochains (Cohomology)

variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- Canonical comparison with the two original relative cohomology groups. -/
def middleEquiv (n : ℕ) : MiddleCohomology U V n ≃ₗ[ℤ] (Cohomology U n × Cohomology V n) :=
  ModTwoDualComplex.cohomologyBiprodEquiv (RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) U)
    (RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) V) n

def differenceMap (n : ℕ) : (Cohomology U n × Cohomology V n) →ₗ[ℤ] Cohomology (U ∩ V) n :=
  (secondMap U V n).comp (middleEquiv U V n).symm.toLinearMap

variable (hU : IsOpen U) (hV : IsOpen V)

/-- The original dual quotient map computes cohomology of the actual open union. -/
def smallUnionEquiv (n : ℕ) : Cohomology (U ∪ V) n ≃ₗ[ℤ] SmallCohomology U V n := by
  let := RelativeCoefficients.smallToUnionQuotient_dual_quasiIso U V hU hV
  exact (isoOfQuasiIsoAt (ModTwoDualComplex.map
    (RelativeCoefficients.smallToUnionQuotient (ModuleCat.of ℤ ℤ) U V)) n).toLinearEquiv

theorem smallUnionEquiv_toLinearMap (n : ℕ) :
    (smallUnionEquiv U V hU hV n).toLinearMap =
      (HomologicalComplex.homologyMap (ModTwoDualComplex.map
        (RelativeCoefficients.smallToUnionQuotient (ModuleCat.of ℤ ℤ) U V)) n).hom := rfl

/-- Original restriction to the two subsets, through the proved canonical comparisons. -/
def firstMap (n : ℕ) : Cohomology (U ∪ V) n →ₗ[ℤ] (Cohomology U n × Cohomology V n) :=
  (middleEquiv U V n).toLinearMap.comp
    ((smallFirstMap U V n).comp (smallUnionEquiv U V hU hV n).toLinearMap)

/-- The actual cohomological connecting map, with the small term identified by excision. -/
def connecting (n : ℕ) : Cohomology (U ∩ V) n →ₗ[ℤ] Cohomology (U ∪ V) (n + 1) :=
  (smallUnionEquiv U V hU hV (n + 1)).symm.toLinearMap.comp (smallConnecting U V n)

/-- The first map is induced by the original relative sum map, with no substituted action. -/
theorem firstMap_eq (n : ℕ) :
    firstMap U V hU hV n = (middleEquiv U V n).toLinearMap.comp
      (HomologicalComplex.homologyMap (ModTwoDualComplex.map
        (RelativeMayerVietoris.rightMap (ModuleCat.of ℤ ℤ) U V)) n).hom := by
  rw [← RelativeMayerVietoris.smallRightMap_quotient, ModTwoDualComplex.map_comp,
    HomologicalComplex.homologyMap_comp]
  rfl

/-- Exactness at the genuine relative group of the union. -/
theorem exact_left (n : ℕ) :
    LinearMap.range (connecting U V hU hV n) = LinearMap.ker (firstMap U V hU hV (n + 1)) := by
  let E := smallUnionEquiv U V hU hV (n + 1)
  let M := middleEquiv U V (n + 1)
  apply Submodule.ext
  intro a
  constructor
  · rintro ⟨c, rfl⟩
    change M (smallFirstMap U V (n + 1) (E (E.symm (smallConnecting U V n c)))) = 0
    rw [LinearEquiv.apply_symm_apply]
    have hc : smallFirstMap U V (n + 1) (smallConnecting U V n c) = 0 :=
      (small_exact_left U V n).le ⟨c, rfl⟩
    exact (congrArg M hc).trans M.map_zero
  · intro ha
    change M (smallFirstMap U V (n + 1) (E a)) = 0 at ha
    have ha' : E a ∈ LinearMap.ker (smallFirstMap U V (n + 1)) :=
      M.injective (ha.trans M.map_zero.symm)
    obtain ⟨c, hc⟩ := (small_exact_left U V n).ge ha'
    refine ⟨c, E.injective ?_⟩
    exact (E.apply_symm_apply (smallConnecting U V n c)).trans hc

/-- Exactness at the product of the two genuine relative cohomology groups. -/
theorem exact_middle (n : ℕ) :
    LinearMap.range (firstMap U V hU hV n) = LinearMap.ker (differenceMap U V n) := by
  let E := smallUnionEquiv U V hU hV n
  let M := middleEquiv U V n
  apply Submodule.ext
  intro a
  constructor
  · rintro ⟨b, rfl⟩
    change secondMap U V n (M.symm (M (smallFirstMap U V n (E b)))) = 0
    rw [LinearEquiv.symm_apply_apply]
    exact (small_exact_middle U V n).le ⟨E b, rfl⟩
  · intro ha
    change M.symm a ∈ LinearMap.ker (secondMap U V n) at ha
    obtain ⟨b, hb⟩ := (small_exact_middle U V n).ge ha
    refine ⟨E.symm b, ?_⟩
    change M (smallFirstMap U V n (E (E.symm b))) = a
    rw [LinearEquiv.apply_symm_apply, hb, LinearEquiv.apply_symm_apply]

/-- Exactness at the genuine relative cohomology of the intersection. -/
theorem exact_right (n : ℕ) :
    LinearMap.range (differenceMap U V n) = LinearMap.ker (connecting U V hU hV n) := by
  let E := smallUnionEquiv U V hU hV (n + 1)
  let M := middleEquiv U V n
  apply Submodule.ext
  intro a
  constructor
  · rintro ⟨b, rfl⟩
    change E.symm (smallConnecting U V n (secondMap U V n (M.symm b))) = 0
    have hb : smallConnecting U V n (secondMap U V n (M.symm b)) = 0 :=
      (small_exact_right U V n).le ⟨M.symm b, rfl⟩
    exact (congrArg E.symm hb).trans E.symm.map_zero
  · intro ha
    change E.symm (smallConnecting U V n a) = 0 at ha
    have ha' : a ∈ LinearMap.ker (smallConnecting U V n) :=
      E.symm.injective (ha.trans E.symm.map_zero.symm)
    obtain ⟨b, hb⟩ := (small_exact_right U V n).ge ha'
    refine ⟨M b, ?_⟩
    change secondMap U V n (M.symm (M b)) = a
    rw [LinearEquiv.symm_apply_apply]
    exact hb

end NoExoticSixSphere.RelativeModTwoMayerVietoris
