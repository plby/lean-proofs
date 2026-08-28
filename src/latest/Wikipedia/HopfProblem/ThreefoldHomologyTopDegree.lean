import Wikipedia.HopfProblem.ThreefoldHomologyTopDegreeColumns
import Wikipedia.HopfProblem.ThreefoldHomologyTopDegreeAlgebra

/-!
# The actual sixth integral homology is infinite cyclic

The genuine top connecting map identifies sixth homology with the kernel
of the original three boundary maps.  The two actual elliptic columns
form an isomorphism onto the regular term.  The kernel is consequently
the graph over the actual cusp boundary group, whose genuine Wang map
identifies it with the integral top homology of the four-torus.

This calculation neither uses Poincaré duality nor assumes any value for
the cusp column or any lower-degree attachment matrix.
-/

noncomputable section

open scoped TensorProduct

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.TopDegree

open SingularMayerVietoris ThreefoldHomologyTopDegreeAlgebra

/-- The unchanged map has the required literal invertible elliptic column. -/
theorem groupedAttachmentFifth_columnIso
    (a : SingularHomology (RegularOverlap none) 5) (b : EllipticOverlapFifth) :
    groupedAttachmentFifth (a, b) =
      singularHomologyMap (overlapToRegularFamily none) 5 a + ellipticAttachmentFifthEquiv b := by
  change groupedAttachmentFifth (a, b) =
    singularHomologyMap (overlapToRegularFamily none) 5 a +
      ellipticAttachmentFifthEquiv.toLinearMap b
  rw [ellipticAttachmentFifthEquiv_toLinearMap, groupedAttachmentFifth_apply]

/-- The original top kernel is canonically its cusp component. -/
def homologySixCuspEquiv :
    SingularHomology Space 6 ≃ₗ[ℤ] SingularHomology (RegularOverlap none) 5 :=
  (homologySixGroupedKernelEquiv.toAddEquiv.trans
    (kernelEquivOfColumnIso groupedAttachmentFifth
      (singularHomologyMap (overlapToRegularFamily none) 5)
      ellipticAttachmentFifthEquiv groupedAttachmentFifth_columnIso).toAddEquiv).toIntLinearEquiv

/-- The forward map is exactly the cusp component of the genuine star boundary. -/
@[simp] theorem homologySixCuspEquiv_apply (a : SingularHomology Space 6) :
    homologySixCuspEquiv a = starConnectingHomomorphism 5 a none := by
  change (homologySixGroupedKernelEquiv a :
    SingularHomology (RegularOverlap none) 5 × EllipticOverlapFifth).1 = _
  rw [homologySixGroupedKernelEquiv_val]

/-- Genuine sixth integral singular homology of the constructed threefold is `ℤ`. -/
def homologySixEquiv : SingularHomology Space 6 ≃ₗ[ℤ] ℤ :=
  homologySixCuspEquiv.trans (overlapFifthEquiv none)

@[simp] theorem homologySixEquiv_apply (a : SingularHomology Space 6) :
    homologySixEquiv a = overlapFifthEquiv none (starConnectingHomomorphism 5 a none) := by
  change overlapFifthEquiv none (homologySixCuspEquiv a) = _
  rw [homologySixCuspEquiv_apply]

theorem homologySix_free : Module.Free ℤ (SingularHomology Space 6) :=
  Module.Free.of_equiv homologySixEquiv.symm

theorem homologySix_torsionFree : Module.IsTorsionFree ℤ (SingularHomology Space 6) := by
  have := homologySix_free
  infer_instance

theorem homologySix_finrank : Module.finrank ℤ (SingularHomology Space 6) = 1 := by
  rw [homologySixEquiv.finrank_eq]
  exact Module.finrank_self ℤ

theorem rationalBetti_six : Finiteness.rationalBetti 6 = 1 := by
  have := homologySix_free
  change Module.finrank ℚ (ℚ ⊗[ℤ] SingularHomology Space 6) = 1
  rw [Module.finrank_baseChange, homologySix_finrank]

/-- The generator selected by the actual cusp connecting and Wang coordinates. -/
def topClass : SingularHomology Space 6 := homologySixEquiv.symm 1

@[simp] theorem homologySixEquiv_topClass : homologySixEquiv topClass = 1 :=
  LinearEquiv.apply_symm_apply _ _

theorem topClass_ne_zero : topClass ≠ 0 := by
  intro h
  have he := congrArg homologySixEquiv h
  rw [homologySixEquiv_topClass, map_zero] at he
  exact one_ne_zero he

/-- Every actual top class is an integral multiple of this actual generator. -/
theorem eq_smul_topClass (a : SingularHomology Space 6) :
    a = homologySixEquiv a • topClass := by
  apply homologySixEquiv.injective
  rw [map_zsmul, homologySixEquiv_topClass]
  simp

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.TopDegree
