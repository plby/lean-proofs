import Wikipedia.NoExoticSixSphere.RelativeSimplexCycles
import Wikipedia.NoExoticSixSphere.RelativeTwoSkeletonNormalization

/-!
# Normalized tetrahedra represent actual third relative homology

Under the stated connectivity hypotheses, the coherent normalization
assigns a genuine relative cycle to each singular tetrahedron. This
linear assignment preserves the original relative class, vanishes on
subspace chains and four-boundaries, and is surjective onto the actual
third relative homology. These assertions concern homology, not an
unproved relative homotopy classification.
-/

noncomputable section

open Set
open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris
open SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.RelativeNormalizedThreeHomology

open RelativeSingularHomology RelativeTwoSkeletonNormalization

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
  (U : Set X) [SimplyConnectedSpace U] (a : U)
  (hπ : Function.Surjective
    (HigherHomotopy.map (N := Fin 2) (subtypeInclusion U) (y := a) rfl))

def relativeSimplex (smp : C(Simplex 3, X)) : RelativeSimplexCycles.RelativeSimplex U 3 :=
  ⟨endpoint U a hπ 3 smp, endpoint_tetrahedron_boundary U a hπ smp⟩

def cycleOperator : Chains X 3 →ₗ[ℤ] ModuleHomology.Cycle (complex U) 3 :=
  chainLift X 3 fun smp ↦ RelativeSimplexCycles.cycle U 2 (relativeSimplex U a hπ smp)

theorem cycleOperator_simplex (smp : C(Simplex 3, X)) :
    cycleOperator U a hπ (simplexChain X 3 smp) =
      RelativeSimplexCycles.cycle U 2 (relativeSimplex U a hπ smp) :=
  chainLift_simplex X 3 _ smp

theorem cycleOperator_val (c : Chains X 3) :
    (cycleOperator U a hπ c).val =
      quotientMap U 3 (simplexEndpointOperator 3 (homotopy U a hπ 3) 1 c) := by
  have he : (ModuleHomology.Cycle (complex U) 3).subtype.comp (cycleOperator U a hπ) =
      (quotientMap U 3).comp (simplexEndpointOperator 3 (homotopy U a hπ 3) 1) := by
    apply chainMap_ext X 3
    intro smp
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, cycleOperator_simplex,
      simplexEndpointOperator_simplex]
    rfl
  exact LinearMap.congr_fun he c

def classOperator : Chains X 3 →ₗ[ℤ] Homology U 3 :=
  (ModuleHomology.cycleClass (complex U) 3).comp (cycleOperator U a hπ)

theorem classOperator_simplex (smp : C(Simplex 3, X)) :
    classOperator U a hπ (simplexChain X 3 smp) =
      RelativeSimplexCycles.homologyClass U 2 (relativeSimplex U a hπ smp) := by
  change ModuleHomology.cycleClass (complex U) 3
    (cycleOperator U a hπ (simplexChain X 3 smp)) = _
  rw [cycleOperator_simplex]
  rfl

theorem classOperator_eq (c : Chains X 3)
    (hc : ((complex U).d 3 2).hom (quotientMap U 3 c) = 0) :
    classOperator U a hπ c = ModuleHomology.cycleClass (complex U) 3
      (ModuleHomology.mkCycle (complex U) 3 (quotientMap U 3 c) hc) := by
  have he : cycleOperator U a hπ c =
      RelativeSimplexHomotopyHomology.endpointCycle U 2
        (homotopy U a hπ 2) (homotopy U a hπ 3) (homotopy_face U a hπ 2)
        (homotopy_mem U a hπ 2) c hc := by
    apply Subtype.ext
    exact cycleOperator_val U a hπ c
  change ModuleHomology.cycleClass (complex U) 3 (cycleOperator U a hπ c) = _
  rw [he]
  apply RelativeSimplexHomotopyHomology.endpointCycle_class
  intro smp
  ext s
  exact homotopy_zero U a hπ 3 smp s

theorem classOperator_supported (c : Chains X 3) (hc : c ∈ supportedChainSubmodule U 3) :
    classOperator U a hπ c = 0 := by
  have he : cycleOperator U a hπ c = 0 := by
    apply Subtype.ext
    rw [cycleOperator_val]
    exact (quotientMap_eq_zero_iff U 3 _).mpr
      (SimplexHomotopyChainSupport.endpoint_mem U 3 (homotopy U a hπ 3)
        (homotopy_mem U a hπ 3) 1 c hc)
  change ModuleHomology.cycleClass (complex U) 3 (cycleOperator U a hπ c) = 0
  rw [he, map_zero]

theorem classOperator_boundary (c : Chains X 4) :
    classOperator U a hπ (((singularComplex X).d 4 3).hom c) = 0 := by
  have he : cycleOperator U a hπ (((singularComplex X).d 4 3).hom c) =
      ModuleHomology.boundaryCycle (complex U) 3
        (quotientMap U 4 (simplexEndpointOperator 4 (homotopy U a hπ 4) 1 c)) := by
    apply Subtype.ext
    rw [cycleOperator_val, ModuleHomology.boundaryCycle_val, boundary_quotientMap,
      simplexEndpointOperator_boundary 3 _ _ (homotopy_face U a hπ 3)]
  change ModuleHomology.cycleClass (complex U) 3
    (cycleOperator U a hπ (((singularComplex X).d 4 3).hom c)) = 0
  rw [he, ModuleHomology.cycleClass_boundary]

theorem classOperator_surjective : Function.Surjective (classOperator U a hπ) := by
  intro z
  obtain ⟨k, hk⟩ := ModuleHomology.cycleClass_surjective (complex U) 3 z
  obtain ⟨c, hc⟩ := quotientMap_surjective U 3 k.val
  have hcycle : ((complex U).d 3 2).hom (quotientMap U 3 c) = 0 := by
    rw [hc]
    exact ModuleHomology.cycle_condition (complex U) 3 k
  refine ⟨c, (classOperator_eq U a hπ c hcycle).trans ?_⟩
  have he : ModuleHomology.mkCycle (complex U) 3 (quotientMap U 3 c) hcycle = k :=
    Subtype.ext hc
  rw [he, hk]

theorem signed_faces (smp : C(Simplex 4, X)) :
    (∑ i : Fin 5, (-1 : ℤ) ^ i.val •
      RelativeSimplexCycles.homologyClass U 2
        (relativeSimplex U a hπ (smp.comp (simplexFace 3 i)))) = 0 := by
  simpa only [boundary_simplex, map_sum, map_zsmul, classOperator_simplex] using
    classOperator_boundary U a hπ (simplexChain X 4 smp)

end NoExoticSixSphere.RelativeNormalizedThreeHomology
