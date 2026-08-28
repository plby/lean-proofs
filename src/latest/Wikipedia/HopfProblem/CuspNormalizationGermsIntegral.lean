import Wikipedia.HopfProblem.CuspNormalizationGermsRestriction

/-!
# The actual finite integral branch-germ extension

The ring on the singular coordinate-plane union is a ring of actual
ambient-analytic functions modulo equality near the union.  Its map to
the product of analytic branch-germ rings is obtained from the actual
restriction maps, and is proved injective, finite and integral.

These assertions do not assert that the branch rings are integrally
closed.  That additional analytic assertion is needed to identify this
finite birational extension with the integral closure.
-/

noncomputable section

open Set Filter Topology

namespace Wikipedia.HopfProblem.CuspNormalization.Germs

private theorem quotientKerEquivRange_mk {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (r : R) :
    f.quotientKerEquivRange (Ideal.Quotient.mk (RingHom.ker f) r) =
      f.rangeRestrict r := by
  simp [RingHom.quotientKerEquivRange]

private theorem quotientKerEquivRange_symm_rangeRestrict
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : R) :
    f.quotientKerEquivRange.symm (f.rangeRestrict r) =
      Ideal.Quotient.mk (RingHom.ker f) r := by
  apply f.quotientKerEquivRange.injective
  rw [RingEquiv.apply_symm_apply, quotientKerEquivRange_mk]

/-- The image-ring comparison sends each actual restricted ambient germ
to its actual tuple of branch restrictions. -/
@[simp] theorem restrictedEquivBranchImage_rangeRestrict
    (s : Finset (Fin 3)) (φ : AmbientGerm) :
    restrictedEquivBranchImage s ((toPlaneUnion s).rangeRestrict φ) =
      (toBranches s).rangeRestrict φ := by
  change (toBranches s).quotientKerEquivRange
    (Ideal.quotEquivOfEq (kernel_toPlaneUnion s)
      ((toPlaneUnion s).quotientKerEquivRange.symm
        ((toPlaneUnion s).rangeRestrict φ))) = _
  rw [quotientKerEquivRange_symm_rangeRestrict, Ideal.quotEquivOfEq_mk,
    quotientKerEquivRange_mk]

/-- The actual pullback from singular function germs to the disjoint
smooth branches.  This is an inclusion after the proved kernel comparison. -/
def restrictionToBranches (s : Finset (Fin 3)) :
    RestrictedAnalyticGerm s →+* (s → BranchGerm) :=
  (BranchImage s).subtype.comp (restrictedEquivBranchImage s).toRingHom

@[simp] theorem restrictionToBranches_rangeRestrict
    (s : Finset (Fin 3)) (φ : AmbientGerm) :
    restrictionToBranches s ((toPlaneUnion s).rangeRestrict φ) = toBranches s φ := by
  change (restrictedEquivBranchImage s ((toPlaneUnion s).rangeRestrict φ) :
    s → BranchGerm) = _
  rw [restrictedEquivBranchImage_rangeRestrict]
  rfl

/-- No nonzero singular function germ vanishes on all of its branches. -/
theorem restrictionToBranches_injective (s : Finset (Fin 3)) :
    Function.Injective (restrictionToBranches s) :=
  Subtype.val_injective.comp (restrictedEquivBranchImage s).injective

/-- Each analytic branch germ extends to an actual singular function
germ by making a representative constant in the omitted coordinate. -/
theorem restrictionToBranches_coordinate_surjective
    (s : Finset (Fin 3)) (j : s) :
    Function.Surjective (fun φ : RestrictedAnalyticGerm s =>
      restrictionToBranches s φ j) := by
  intro ψ
  refine ⟨(toPlaneUnion s).rangeRestrict (extendBranch j ψ), ?_⟩
  change restrictionToBranches s ((toPlaneUnion s).rangeRestrict (extendBranch j ψ)) j = ψ
  rw [restrictionToBranches_rangeRestrict, toBranches_apply, toBranch_extendBranch]

/-- The actual ring map to all analytic branch germs is finite. -/
theorem restrictionToBranches_finite (s : Finset (Fin 3)) :
    (restrictionToBranches s).Finite := by
  exact (GermsFinite.range_inclusion_finite (toBranches s)
    (toBranches_coordinate_surjective s)).comp
      (RingHom.Finite.of_surjective (restrictedEquivBranchImage s).toRingHom
        (restrictedEquivBranchImage s).surjective)

/-- The actual ring map to all analytic branch germs is integral. -/
theorem restrictionToBranches_isIntegral (s : Finset (Fin 3)) :
    (restrictionToBranches s).IsIntegral :=
  (restrictionToBranches_finite s).to_isIntegral

/-- In module language the scalar action is the actual germ restriction,
not an unrelated transported ring structure. -/
theorem restrictionToBranches_moduleFinite (s : Finset (Fin 3)) :
    letI := (restrictionToBranches s).toAlgebra
    Module.Finite (RestrictedAnalyticGerm s) (s → BranchGerm) :=
  restrictionToBranches_finite s

end Wikipedia.HopfProblem.CuspNormalization.Germs
