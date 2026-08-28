import Wikipedia.HopfProblem.CuspComplementCircleEquivarianceActions
import Wikipedia.HopfProblem.CuspComplementFinitePresentation

/-!
# Circle-equivariance of the actual finite carved quotient presentation

The literal carved-coordinate circle maps descend through the unchanged
original cusp relation. The already constructed homeomorphism to the actual
compact complement intertwines this quotient action with the independent
restriction of the original global delta-circle action.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspComplement

open SpecialPeriods SpecialPeriods.Threefold Homology

local notation "Circle" => AddCircle (1 : ℝ)

/-- The original cusp relation is preserved by the literal carved-coordinate action. -/
theorem coordinateRelation_carvedCircleAction (t : Circle) {p q : carvedCoordinates}
    (h : coordinateRelation.r p q) :
    coordinateRelation.r (carvedCircleAction t p) (carvedCircleAction t q) := by
  apply (coordinateRelation_iff _ _).mpr
  rw [presentationMap_carvedCircleAction, presentationMap_carvedCircleAction]
  exact congrArg (capComplementCircleAction t) ((coordinateRelation_iff p q).mp h)

/-- Descent of the actual source action through the existing original-relation quotient. -/
def finiteModelCircleAction (t : Circle) : FiniteModel → FiniteModel :=
  Quotient.map (carvedCircleAction t)
    (fun {_ _} h => coordinateRelation_carvedCircleAction t h)

@[simp] theorem finiteModelCircleAction_mk (t : Circle) (p : carvedCoordinates) :
    finiteModelCircleAction t (Quotient.mk coordinateRelation p) =
      Quotient.mk coordinateRelation (carvedCircleAction t p) := rfl

@[simp] theorem finiteModelCircleAction_zero (q : FiniteModel) :
    finiteModelCircleAction 0 q = q := by
  induction q using Quotient.inductionOn with
  | h p => simp only [finiteModelCircleAction_mk, carvedCircleAction_zero]

theorem finiteModelCircleAction_add (s t : Circle) (q : FiniteModel) :
    finiteModelCircleAction (s + t) q =
      finiteModelCircleAction s (finiteModelCircleAction t q) := by
  induction q using Quotient.inductionOn with
  | h p => simp only [finiteModelCircleAction_mk, carvedCircleAction_add]

@[instance_reducible] def finiteModelCircleAddAction : AddAction Circle FiniteModel where
  vadd := finiteModelCircleAction
  zero_vadd := finiteModelCircleAction_zero
  add_vadd := finiteModelCircleAction_add

theorem finiteModelMap_circleAction (t : Circle) (q : FiniteModel) :
    finiteModelMap (finiteModelCircleAction t q) =
      capComplementCircleAction t (finiteModelMap q) := by
  induction q using Quotient.inductionOn with
  | h p =>
    simpa only [finiteModelCircleAction_mk, finiteModelMap_mk] using
      presentationMap_carvedCircleAction t p

/-- Exact equivariance of the original finite-quotient homeomorphism. -/
theorem finiteModelHomeomorph_circleAction (t : Circle) (q : FiniteModel) :
    finiteModelHomeomorph (finiteModelCircleAction t q) =
      capComplementCircleAction t (finiteModelHomeomorph q) := by
  induction q using Quotient.inductionOn with
  | h p =>
    simpa only [finiteModelCircleAction_mk, finiteModelHomeomorph_mk] using
      presentationMap_carvedCircleAction t p

theorem finiteModelHomeomorph_circleAction_coe (t : Circle) (q : FiniteModel) :
    (finiteModelHomeomorph (finiteModelCircleAction t q) : Threefold.Space) =
      DeltaSweep.actionMap (t, (finiteModelHomeomorph q : Threefold.Space)) := by
  rw [finiteModelHomeomorph_circleAction]
  rfl

theorem finiteModelHomeomorph_symm_circleAction (t : Circle) (x : capComplement) :
    finiteModelHomeomorph.symm (capComplementCircleAction t x) =
      finiteModelCircleAction t (finiteModelHomeomorph.symm x) := by
  apply finiteModelHomeomorph.injective
  rw [finiteModelHomeomorph.apply_symm_apply, finiteModelHomeomorph_circleAction,
    finiteModelHomeomorph.apply_symm_apply]

/-- Joint continuity is for the genuine quotient topology and the explicit descended maps. -/
theorem finiteModelCircleAction_continuous :
    Continuous (fun q : Circle × FiniteModel => finiteModelCircleAction q.1 q.2) := by
  apply finiteModelHomeomorph.comp_continuous_iff.mp
  simpa only [Function.comp_def, finiteModelHomeomorph_circleAction] using
    capComplementCircleAction_continuous.comp
      (continuous_fst.prodMk (finiteModelHomeomorph.continuous.comp continuous_snd))

theorem finiteModelCircleAddAction_continuous :
    letI := finiteModelCircleAddAction
    ContinuousVAdd Circle FiniteModel := by
  let := finiteModelCircleAddAction
  exact ⟨finiteModelCircleAction_continuous⟩

theorem finiteModelHomeomorph_vadd (t : Circle) (q : FiniteModel) :
    letI := finiteModelCircleAddAction
    letI := capComplementCircleAddAction
    finiteModelHomeomorph (t +ᵥ q) = t +ᵥ finiteModelHomeomorph q := by
  let := finiteModelCircleAddAction
  let := capComplementCircleAddAction
  exact finiteModelHomeomorph_circleAction t q

end Wikipedia.HopfProblem.CuspComplement
