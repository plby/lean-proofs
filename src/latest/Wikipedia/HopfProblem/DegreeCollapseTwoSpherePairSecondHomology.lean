import Wikipedia.HopfProblem.DegreeCollapseSurgeryPairConnectivity
import Wikipedia.HopfProblem.SphereHomologyVanishing
import Wikipedia.NoExoticSixSphere.Definitions
import Wikipedia.NoExoticSixSphere.GLOrthonormalization
import Wikipedia.NoExoticSixSphere.Topology.SimplyConnectedSphere
import Mathlib.LinearAlgebra.Isomorphisms

/-!

# Integral H2 of a two-sphere surgery pair, including pairs with boundary

The proof uses the two actual inclusions into the common whole-handle body.
It only needs the closed-piece surgery pair and compact Hausdorff ends,
so it applies directly to the nonnegative halves as well as to closed ends.
No simple connectivity or vanishing of H2 is an input to the quotient.
-/

noncomputable section

open Function Set

namespace Wikipedia.HopfProblem.DegreeCollapse.SurgeryPairBody.TwoSphere

open NoExoticSixSphere GLOrthonormalization SingularMayerVietoris SphereHomology
open Wikipedia.SmoothSixDPoincare

local instance : SimplyConnectedSpace (Sphere 2) := EuclideanSphere.simplyConnectedSpace 0
local instance : SimplyConnectedSpace (Sphere 4) := EuclideanSphere.simplyConnectedSpace 2
local instance : Subsingleton (SingularHomology (Sphere 2) 1) :=
  unitSphere_homology_subsingleton 1 1 (by decide) (by decide)
local instance : Subsingleton (SingularHomology (Sphere 4) 1) :=
  unitSphere_homology_subsingleton 3 1 (by decide) (by decide)
local instance : Subsingleton (SingularHomology (Sphere 4) 2) :=
  unitSphere_homology_subsingleton 3 2 (by decide) (by decide)

variable {R X Y : Type} [TopologicalSpace R] [TopologicalSpace X]
  [CompactSpace X] [T2Space X] [TopologicalSpace Y] [CompactSpace Y]
  (D : SurgeryBoundaryPair (Vector 3) (Vector 5) R X Y)

include D in
theorem simplyConnected_iff : SimplyConnectedSpace Y ↔ SimplyConnectedSpace X :=
  SurgeryPairBody.simplyConnected_iff D

def newBodySecondHomologyEquiv :
    SingularHomology Y 2 ≃ₗ[ℤ] SingularHomology (Space D) 2 :=
  LinearEquiv.ofBijective (singularHomologyMap (newMap D) 2)
    ⟨(newHandleData D).old_injective 2 (by decide),
      (newHandleData D).old_surjective 1⟩

def secondHomologyMap : SingularHomology X 2 →ₗ[ℤ] SingularHomology Y 2 :=
  (newBodySecondHomologyEquiv D).symm.toLinearMap.comp
    (singularHomologyMap (oldMap D) 2)

theorem secondHomologyMap_inclusions (x : SingularHomology X 2) :
    singularHomologyMap (newMap D) 2 (secondHomologyMap D x) =
      singularHomologyMap (oldMap D) 2 x :=
  (newBodySecondHomologyEquiv D).apply_symm_apply _

theorem secondHomologyMap_surjective : Surjective (secondHomologyMap D) :=
  (newBodySecondHomologyEquiv D).symm.surjective.comp ((oldHandleData D).old_surjective 1)

def attachingClass : SingularHomology X 2 :=
  singularHomologyMap D.attachingSphere 2 (unitSphereTopClass 1)

omit [CompactSpace X] [T2Space X] [CompactSpace Y] in
theorem attaching_range_span :
    LinearMap.range (singularHomologyMap D.attachingSphere 2) =
      Submodule.span ℤ {attachingClass D} := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨k, rfl⟩ := unitSphereTopClass_generates 1 v
    rw [map_zsmul]
    exact Submodule.mem_span_singleton.mpr ⟨k,
      int_smul_eq_zsmul (SingularHomology X 2).isModule k (attachingClass D)⟩
  · intro hx
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hx
    refine ⟨k • unitSphereTopClass 1, ?_⟩
    rw [map_zsmul]
    exact (int_smul_eq_zsmul (SingularHomology X 2).isModule k (attachingClass D)).symm.trans hk

theorem secondHomologyMap_ker :
    LinearMap.ker (secondHomologyMap D) = Submodule.span ℤ {attachingClass D} := by
  change LinearMap.ker ((newBodySecondHomologyEquiv D).symm.toLinearMap.comp
    (singularHomologyMap (oldMap D) 2)) = _
  rw [LinearMap.ker_comp_of_ker_eq_bot _
    (LinearMap.ker_eq_bot.mpr (newBodySecondHomologyEquiv D).symm.injective)]
  rw [← exact_at_old D 2 (by decide), attaching_range_span]

theorem secondHomologyMap_attachingClass : secondHomologyMap D (attachingClass D) = 0 := by
  apply LinearMap.mem_ker.mp
  rw [secondHomologyMap_ker]
  exact Submodule.subset_span (mem_singleton _)

def secondHomologyQuotient :
    (SingularHomology X 2 ⧸ Submodule.span ℤ {attachingClass D}) ≃ₗ[ℤ]
      SingularHomology Y 2 := by
  let E := (Submodule.quotEquivOfEq _ _ (secondHomologyMap_ker D).symm).trans
    ((secondHomologyMap D).quotKerEquivOfSurjective (secondHomologyMap_surjective D))
  let ea : (SingularHomology X 2 ⧸ Submodule.span ℤ {attachingClass D}) ≃+
      SingularHomology Y 2 :=
    { toEquiv := E.toEquiv
      map_add' := fun x y ↦ E.map_add' x y }
  exact ea.toIntLinearEquiv

theorem secondHomologyQuotient_mk (x : SingularHomology X 2) :
    secondHomologyQuotient D (Submodule.Quotient.mk x) = secondHomologyMap D x := rfl

theorem target_secondHomology_of_span_top (h : Submodule.span ℤ {attachingClass D} = ⊤) :
    Subsingleton (SingularHomology Y 2) := by
  have hz : secondHomologyMap D = 0 :=
    LinearMap.ker_eq_top.mp ((secondHomologyMap_ker D).trans h)
  have hzero (y : SingularHomology Y 2) : y = 0 := by
    obtain ⟨x, rfl⟩ := secondHomologyMap_surjective D y
    rw [hz, LinearMap.zero_apply]
  exact ⟨fun y z ↦ (hzero y).trans (hzero z).symm⟩

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryPairBody.TwoSphere
