import Wikipedia.NoExoticSixSphere.RelativeSimplexCycles

/-!
# Relative homology represented by an actual coherent normalization

This construction applies in every positive degree. Its input is an
actual simplex homotopy family with the proved face and support identities,
and an endpoint boundary condition. It uses the original relative chains
and homology and introduces no homotopy-detection assumption.
-/

noncomputable section

open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris
open SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.RelativeNormalizedHomology

open RelativeSingularHomology

variable {X : Type} [TopologicalSpace X] (U : Set X) (n : ℕ)
  (H : ∀ k, C(Simplex k, X) → C(I × Simplex k, X))
  (hb : ∀ smp : C(Simplex (n + 1), X), ∀ s ∈ simplexBoundary (n + 1),
    timeSlice (H (n + 1) smp) 1 s ∈ U)

def relativeSimplex (smp : C(Simplex (n + 1), X)) :
    RelativeSimplexCycles.RelativeSimplex U (n + 1) :=
  ⟨timeSlice (H (n + 1) smp) 1, hb smp⟩

def cycleOperator : Chains X (n + 1) →ₗ[ℤ] ModuleHomology.Cycle (complex U) (n + 1) :=
  chainLift X (n + 1) fun smp ↦ RelativeSimplexCycles.cycle U n (relativeSimplex U n H hb smp)

theorem cycleOperator_simplex (smp : C(Simplex (n + 1), X)) :
    cycleOperator U n H hb (simplexChain X (n + 1) smp) =
      RelativeSimplexCycles.cycle U n (relativeSimplex U n H hb smp) :=
  chainLift_simplex X (n + 1) _ smp

theorem cycleOperator_val (c : Chains X (n + 1)) :
    (cycleOperator U n H hb c).val =
      quotientMap U (n + 1) (simplexEndpointOperator (n + 1) (H (n + 1)) 1 c) := by
  have he : (ModuleHomology.Cycle (complex U) (n + 1)).subtype.comp (cycleOperator U n H hb) =
      (quotientMap U (n + 1)).comp (simplexEndpointOperator (n + 1) (H (n + 1)) 1) := by
    apply chainMap_ext X (n + 1)
    intro smp
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, cycleOperator_simplex,
      simplexEndpointOperator_simplex]
    rfl
  exact LinearMap.congr_fun he c

def classOperator : Chains X (n + 1) →ₗ[ℤ] Homology U (n + 1) :=
  (ModuleHomology.cycleClass (complex U) (n + 1)).comp (cycleOperator U n H hb)

theorem classOperator_simplex (smp : C(Simplex (n + 1), X)) :
    classOperator U n H hb (simplexChain X (n + 1) smp) =
      RelativeSimplexCycles.homologyClass U n (relativeSimplex U n H hb smp) := by
  change ModuleHomology.cycleClass (complex U) (n + 1)
    (cycleOperator U n H hb (simplexChain X (n + 1) smp)) = _
  rw [cycleOperator_simplex]
  rfl

variable (h₀ : ∀ k smp s, H k smp (0, s) = smp s)
  (hf : ∀ k, FaceCompatibleHomotopies k (H k) (H (k + 1)))
  (hm : ∀ k smp, (∀ s, smp s ∈ U) → ∀ p, H k smp p ∈ U)

include h₀ hf hm in
theorem classOperator_eq (c : Chains X (n + 1))
    (hc : ((complex U).d (n + 1) n).hom (quotientMap U (n + 1) c) = 0) :
    classOperator U n H hb c = ModuleHomology.cycleClass (complex U) (n + 1)
      (ModuleHomology.mkCycle (complex U) (n + 1) (quotientMap U (n + 1) c) hc) := by
  have he : cycleOperator U n H hb c =
      RelativeSimplexHomotopyHomology.endpointCycle U n (H n) (H (n + 1))
        (hf n) (hm n) c hc := by
    apply Subtype.ext
    exact cycleOperator_val U n H hb c
  change ModuleHomology.cycleClass (complex U) (n + 1) (cycleOperator U n H hb c) = _
  rw [he]
  apply RelativeSimplexHomotopyHomology.endpointCycle_class
  intro smp
  ext s
  exact h₀ (n + 1) smp s

include hm in
theorem classOperator_supported (c : Chains X (n + 1))
    (hc : c ∈ supportedChainSubmodule U (n + 1)) : classOperator U n H hb c = 0 := by
  have he : cycleOperator U n H hb c = 0 := by
    apply Subtype.ext
    rw [cycleOperator_val]
    exact (quotientMap_eq_zero_iff U (n + 1) _).mpr
      (SimplexHomotopyChainSupport.endpoint_mem U (n + 1) (H (n + 1)) (hm (n + 1)) 1 c hc)
  change ModuleHomology.cycleClass (complex U) (n + 1) (cycleOperator U n H hb c) = 0
  rw [he, map_zero]

include hf in
theorem classOperator_boundary (c : Chains X (n + 2)) :
    classOperator U n H hb (((singularComplex X).d (n + 2) (n + 1)).hom c) = 0 := by
  have he : cycleOperator U n H hb (((singularComplex X).d (n + 2) (n + 1)).hom c) =
      ModuleHomology.boundaryCycle (complex U) (n + 1)
        (quotientMap U (n + 2) (simplexEndpointOperator (n + 2) (H (n + 2)) 1 c)) := by
    apply Subtype.ext
    rw [cycleOperator_val, ModuleHomology.boundaryCycle_val, boundary_quotientMap,
      simplexEndpointOperator_boundary (n + 1) _ _ (hf (n + 1))]
  change ModuleHomology.cycleClass (complex U) (n + 1)
    (cycleOperator U n H hb (((singularComplex X).d (n + 2) (n + 1)).hom c)) = 0
  rw [he, ModuleHomology.cycleClass_boundary]

include h₀ hf hm in
theorem classOperator_surjective : Function.Surjective (classOperator U n H hb) := by
  intro z
  obtain ⟨k, hk⟩ := ModuleHomology.cycleClass_surjective (complex U) (n + 1) z
  obtain ⟨c, hc⟩ := quotientMap_surjective U (n + 1) k.val
  have hcycle : ((complex U).d (n + 1) n).hom (quotientMap U (n + 1) c) = 0 := by
    rw [hc]
    exact ModuleHomology.cycle_condition (complex U) (n + 1) k
  refine ⟨c, (classOperator_eq U n H hb h₀ hf hm c hcycle).trans ?_⟩
  have he : ModuleHomology.mkCycle (complex U) (n + 1) (quotientMap U (n + 1) c) hcycle = k :=
    Subtype.ext hc
  rw [he, hk]

include hf in
theorem signed_faces (smp : C(Simplex (n + 2), X)) :
    (∑ i : Fin (n + 3), (-1 : ℤ) ^ i.val • RelativeSimplexCycles.homologyClass U n
      (relativeSimplex U n H hb (smp.comp (simplexFace (n + 1) i)))) = 0 := by
  simpa only [boundary_simplex, map_sum, map_zsmul, classOperator_simplex] using
    classOperator_boundary U n H hb hf (simplexChain X (n + 2) smp)

end NoExoticSixSphere.RelativeNormalizedHomology
