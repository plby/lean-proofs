import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyResolutionLinearOne

/-!
# Actual cokernel comparisons induced by an isomorphism of complexes
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.ResolutionLinear

variable {A B : ShortComplex AddCommGrpCat.{0}}

/-- The actual map on final categorical cokernels. -/
def cokernelComplexMap (φ : A ⟶ B) : cokernel A.g ⟶ cokernel B.g :=
  cokernel.map A.g B.g φ.τ₂ φ.τ₃ φ.comm₂₃.symm

@[reassoc] theorem cokernelComplexMap_π (φ : A ⟶ B) :
    cokernel.π A.g ≫ cokernelComplexMap φ = φ.τ₃ ≫ cokernel.π B.g :=
  cokernel.π_desc _ _ _

/-- A genuine complex isomorphism induces the corresponding actual cokernel isomorphism. -/
def cokernelComplexIso (e : A ≅ B) : cokernel A.g ≅ cokernel B.g :=
  cokernel.mapIso A.g B.g (ShortComplex.π₂.mapIso e) (ShortComplex.π₃.mapIso e)
    e.hom.comm₂₃.symm

@[reassoc] theorem cokernelComplexIso_π (e : A ≅ B) :
    cokernel.π A.g ≫ (cokernelComplexIso e).hom = e.hom.τ₃ ≫ cokernel.π B.g :=
  cokernel.π_desc _ _ _

/-- Naturality holds on the actual quotient objects, not just representative values. -/
theorem cokernelComplexIso_naturality (e : A ≅ B) (φ : A ⟶ A) (ψ : B ⟶ B)
    (h : φ ≫ e.hom = e.hom ≫ ψ) :
    cokernelComplexMap φ ≫ (cokernelComplexIso e).hom =
      (cokernelComplexIso e).hom ≫ cokernelComplexMap ψ := by
  apply (cancel_epi (cokernel.π A.g)).mp
  have h₃ := congrArg (fun k : A ⟶ B => k.τ₃) h
  change φ.τ₃ ≫ e.hom.τ₃ = e.hom.τ₃ ≫ ψ.τ₃ at h₃
  have hp := congrArg (fun k => k ≫ cokernel.π B.g) h₃
  simpa only [Category.assoc, cokernelComplexMap_π_assoc,
    cokernelComplexIso_π_assoc, cokernelComplexMap_π, cokernelComplexIso_π] using hp

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.ResolutionLinear
