import Wikipedia.HopfProblem.DegreeCollapseRelativeIntegralCapNaturality
import Wikipedia.NoExoticSixSphere.CoefficientHomologyZero
import Wikipedia.NoExoticSixSphere.ModTwoCapUnit

/-!
# Augmentation of the actual integral top cap is original evaluation

On an original simplex the top front face is the whole simplex and
the remaining zero-simplex has augmentation one. This gives the identity
on integral chains, on the genuine relative quotient, and finally on
both original class groups. No coefficient reduction or duality premise
is used.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCap

open FirstHurewicz SingularCohomologyCup NoExoticSixSphere

/-- The original coefficient-sum map with its integral-chain source explicit. -/
def augmentationChain (X : Type) [TopologicalSpace X] : Chains X 0 →ₗ[ℤ] ℤ :=
  CoefficientChains.augmentationChain (ModuleCat.of ℤ ℤ) X

/-- The original integral homology augmentation with its native source explicit. -/
def augmentation (X : Type) [TopologicalSpace X] : (singularComplex X).homology 0 →ₗ[ℤ] ℤ :=
  CoefficientChains.augmentation (ModuleCat.of ℤ ℤ) X

variable {X : Type} [TopologicalSpace X]

theorem augmentation_simplex (σ : SingularSimplex X 0) :
    augmentationChain X (simplexChain X 0 σ) = 1 :=
  CoefficientChains.augmentationChain_simplex (ModuleCat.of ℤ ℤ) X σ 1

theorem augmentation_cycleClass
    (z : SingularMayerVietoris.ModuleHomology.Cycle (singularComplex X) 0) :
    augmentation X (SingularMayerVietoris.ModuleHomology.cycleClass (singularComplex X) 0 z) =
      augmentationChain X z.val :=
  CoefficientChains.augmentation_cycleClass (ModuleCat.of ℤ ℤ) X z

/-- The exact integral top-cap identity on each original singular simplex. -/
theorem augmentation_cap_simplex (n : ℕ) (α : Cochain X n) (σ : SingularSimplex X n) :
    augmentationChain X
      (capInDegree (q := 0) (Nat.add_zero n) α (simplexChain X n σ)) = α (simplexChain X n σ) := by
  rw [capInDegree_simplex, map_zsmul, augmentation_simplex,
    ModTwoCapProduct.windowFace_full, ContinuousMap.comp_id]
  simp only [zsmul_eq_mul, Int.cast_id, mul_one]

theorem augmentation_cap (n : ℕ) (α : Cochain X n) (c : Chains X n) :
    augmentationChain X
      (capInDegree (q := 0) (Nat.add_zero n) α c) = α c := by
  have he : (augmentationChain X).comp
      (capInDegree (q := 0) (Nat.add_zero n) α) = α := by
    apply chainMap_ext X n
    intro σ
    exact augmentation_cap_simplex n α σ
  exact LinearMap.congr_fun he c

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCap

namespace Wikipedia.HopfProblem.DegreeCollapse.RelativeIntegralCap

open FirstHurewicz SingularMayerVietoris NoExoticSixSphere
open RelativeSingularHomology

variable {X : Type} [TopologicalSpace X] (U : Set X)

/-- The original relative quotient retains the same integral augmentation-cap identity. -/
theorem augmentation_cap (n : ℕ) (α : Cochain U n) (c : (complex U).X n) :
    IntegralCap.augmentationChain X
      (capInDegree U (q := 0) (Nat.add_zero n) α c) = α c := by
  obtain ⟨b, rfl⟩ := quotientMap_surjective U n c
  rw [capInDegree_quotientMap]
  exact IntegralCap.augmentation_cap n (toAbsolute U n α) b

/-- Augmenting the original top cap gives the actual cohomology-homology evaluation. -/
theorem augmentation_capProduct (n : ℕ) (a : Cohomology U n) (c : (complex U).homology n) :
    IntegralCap.augmentation X
        (capProductInDegree U (q := 0) (Nat.add_zero n) a c) =
      SingularCohomologyFree.cohomologyEvaluation (complex U) n a c := by
  obtain ⟨α, rfl⟩ := SingularCohomologyFree.cocycleClass_surjective (cochainComplex U) n a
  obtain ⟨z, rfl⟩ := ModuleHomology.cycleClass_surjective (complex U) n c
  change IntegralCap.augmentation X
    (capProduct U n 0 (SingularCohomologyFree.cocycleClass (cochainComplex U) n α)
      (ModuleHomology.cycleClass (complex U) n z)) = _
  apply (congrArg (IntegralCap.augmentation X) (capProduct_cocycle_cycle U n 0 α z)).trans
  apply (IntegralCap.augmentation_cycleClass
    (capCycles U n 0 α.val (cocycle_coboundary_zero U n α) z)).trans
  exact (congrArg (IntegralCap.augmentationChain X)
    (capCycles_val U n 0 α.val (cocycle_coboundary_zero U n α) z)).trans
      ((augmentation_cap U n α.val z.val).trans
        (SingularCohomologyFree.cohomologyEvaluation_cocycle_cycle (complex U) n α z).symm)

end Wikipedia.HopfProblem.DegreeCollapse.RelativeIntegralCap
