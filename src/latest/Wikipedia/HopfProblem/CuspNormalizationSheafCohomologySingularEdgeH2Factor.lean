import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologySingularEdgeH2Basic

/-!
# The original kernel equivalence is the restriction of the original H² map

Inverting the proved normalization kernel square identifies the old
native constant edge map with precisely the restriction of the actual
singular-to-holomorphic map. The original kernel inclusions are retained.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologySingularEdge

open CuspQuotient ToricSpace SheafResolution ConstantSheafSingularComparison
open SheafCohomologyConstantEdge

private theorem inverse_inclusion_square {D : Type*} [Category D]
    {K K' A A' : D} (k : K ≅ K') (e : A ≅ A') (i : K ⟶ A) (i' : K' ⟶ A')
    (h : k.hom ≫ i' = i ≫ e.hom) : k.inv ≫ i = i' ≫ e.inv := by
  apply (cancel_epi k.hom).mp
  rw [← Category.assoc, k.hom_inv_id, Category.id_comp, ← Category.assoc, h,
    Category.assoc, e.hom_inv_id, Category.comp_id]

private theorem compose_restriction {D : Type*} [Category D]
    {K K' A A' B : D} (k : K' ⟶ K) (i : K ⟶ A) (i' : K' ⟶ A')
    (e : A' ⟶ A) (c : A ⟶ B) (r : K ⟶ B)
    (hr : r = i ≫ c) (hk : k ≫ i = i' ≫ e) :
    k ≫ r = i' ≫ (e ≫ c) := by
  rw [hr, ← Category.assoc, hk, Category.assoc]

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The inverse of the old kernel comparison preserves the same
actual inclusions and the inverse canonical cohomology comparison. -/
@[reassoc] theorem normalizationH2KernelIso_inv_ι :
    (normalizationH2KernelIso C ε hε hε1 hC hR).inv ≫
      kernel.ι (constantH2EdgeMap C ε hε) =
    kernel.ι (singularNormalizationH2Map C ε hε) ≫
      (cuspComplexSheafH2Iso C ε hε hε1 hC hR).inv :=
  inverse_inclusion_square (normalizationH2KernelIso C ε hε hε1 hC hR)
    (cuspComplexSheafH2Iso C ε hε hε1 hC hR)
    (kernel.ι (constantH2EdgeMap C ε hε))
    (kernel.ι (singularNormalizationH2Map C ε hε))
    (normalizationH2KernelIso_ι C ε hε hε1 hC hR)

/-- The original singular kernel is isomorphic to genuine holomorphic
H² by the two already proved canonical native isomorphisms. -/
def singularH2KernelHolomorphicIso :
    singularNormalizationH2Kernel C ε hε ≅
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 2) :=
  (normalizationH2KernelIso C ε hε hε1 hC hR).symm ≪≫
    constantsH2EdgeIso C ε hε hε1 hC hR

/-- Its forward map is exactly the restriction of the full original
singular-to-holomorphic H² map along the original kernel inclusion. -/
@[reassoc] theorem singularH2KernelHolomorphicIso_hom :
    (singularH2KernelHolomorphicIso C ε hε hε1 hC hR).hom =
      kernel.ι (singularNormalizationH2Map C ε hε) ≫
        singularH2HolomorphicMap C ε hε hε1 hC hR := by
  exact compose_restriction
    (normalizationH2KernelIso C ε hε hε1 hC hR).inv
    (kernel.ι (constantH2EdgeMap C ε hε))
    (kernel.ι (singularNormalizationH2Map C ε hε))
    (cuspComplexSheafH2Iso C ε hε hε1 hC hR).inv
    ((CategoryTheory.Sheaf.functorH _ 2).map (reducedConstantsMap C ε hε hε1 hC hR))
    (constantsH2EdgeIso C ε hε hε1 hC hR).hom
    (constantsH2EdgeIso_hom C ε hε hε1 hC hR)
    (normalizationH2KernelIso_inv_ι C ε hε hε1 hC hR)

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologySingularEdge
