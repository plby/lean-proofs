import Wikipedia.HopfProblem.CuspCentralHomologySpecializationRadius

/-!
# Continuity of prescribed specialization at an arbitrary ambient radius

The explicit representative formula is continuous on the small admissible
tube and is invariant under the original deck action.  Its actual quotient
descent is therefore continuous even when the ambient radius itself is not
admissible.  The proof keeps the level inclusion, the upstairs map, and the
quotient descent separate.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction CuspControlledRetraction CuspCollapse SpecializationModel

theorem levelToPunctured_continuous (η : ℝ) (t : ℂ) (ht : t ≠ 0) :
    Continuous (levelToPunctured η t ht) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val

/-- The explicit upstairs formula is continuous using period data only
on the smaller admissible disc. -/
theorem prescribedFibreUpstairs_continuous_of_smallRadius
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) {δ η : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hCδ : ∀ i j, ContinuousOn (fun z => C z i j) (Metric.ball 0 δ))
    (hRC : SmallDrift C δ) (hRF : SmallDrift (frozen C) δ) (hηδ : η < δ)
    (t : ℂ) (ht : t ≠ 0) : Continuous (prescribedFibreUpstairs C r hr η t ht) := by
  change Continuous (centralProject C r hr ∘
    (straightenedPrescribedCollapse C η ∘ levelToPunctured η t ht))
  have hc : Continuous (straightenedPrescribedCollapse C η) :=
    straightenedPrescribedCollapse_continuous C hδ hδ1 hCδ hRC hRF hηδ
  have hp : Continuous (levelToPunctured η t ht) := levelToPunctured_continuous η t ht
  have hi : Continuous (straightenedPrescribedCollapse C η ∘ levelToPunctured η t ht) :=
    Continuous.comp (f := levelToPunctured η t ht)
      (g := straightenedPrescribedCollapse C η) hc hp
  exact Continuous.comp
    (f := straightenedPrescribedCollapse C η ∘ levelToPunctured η t ht)
    (g := centralProject C r hr) (centralProject_continuous C r hr) hi

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ)
    (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hδ1 : δ < 1) (hRC : SmallDrift C δ) (hRF : SmallDrift (frozen C) δ)
    (η : ℝ) (hηδ : η < δ) (t : ℂ) (ht : t ≠ 0)

include hC hδ hδ1 hRC hRF in
/-- The actual fixed-level quotient topology gives continuity of the
independent descent at the original ambient radius. -/
theorem prescribedFibreCollapse_continuous_of_smallRadius :
    Continuous (prescribedFibreCollapse C r hr (hηδ.trans_le hδr) t ht) := by
  have hCδ (i j) : ContinuousOn (fun z => C z i j) (Metric.ball 0 δ) :=
    ((hC i j).mono (Metric.ball_subset_ball hδr)).continuousOn
  have hf : Continuous (prescribedFibreUpstairs C r hr η t ht) :=
    prescribedFibreUpstairs_continuous_of_smallRadius C r hr hδ hδ1 hCδ hRC hRF hηδ t ht
  exact levelDescend_continuous C (hηδ.trans_le hδr) t
    (prescribedFibreUpstairs C r hr η t ht) hC hf
    (prescribedFibreUpstairs_compatible C hδ1 hRC hRF hηδ r hr
      (hηδ.trans_le hδr) t ht)

include hC hδ hδ1 hRC hRF in
/-- Passing from the redundant closed-level subtype to the literal
original fibre preserves continuity of the prescribed map. -/
theorem prescribedActualFibreCollapse_continuous_of_smallRadius (htη : ‖t‖ ≤ η) :
    Continuous (prescribedActualFibreCollapse C r hr (hηδ.trans_le hδr) t ht htη) := by
  change Continuous (prescribedFibreCollapse C r hr (hηδ.trans_le hδr) t ht ∘
    (quotientLevelFibreHomeomorph C r η t htη).symm)
  exact (prescribedFibreCollapse_continuous_of_smallRadius
    C r δ hr hδ hδr hC hδ1 hRC hRF η hηδ t ht).comp
      (quotientLevelFibreHomeomorph C r η t htη).symm.continuous

/-- The independently prescribed original-radius map, bundled only
after its continuity has been established from the actual quotient. -/
def smallRadiusActualFibreCollapseMap (htη : ‖t‖ ≤ η) :
    C(ActualQuotientFibre C r t, QuotientCentralFibre C r) where
  toFun := prescribedActualFibreCollapse C r hr (hηδ.trans_le hδr) t ht htη
  continuous_toFun := prescribedActualFibreCollapse_continuous_of_smallRadius
    C r δ hr hδ hδr hC hδ1 hRC hRF η hηδ t ht htη

@[simp] theorem smallRadiusActualFibreCollapseMap_apply (htη : ‖t‖ ≤ η)
    (q : ActualQuotientFibre C r t) :
    smallRadiusActualFibreCollapseMap C r δ hr hδ hδr hC hδ1 hRC hRF η hηδ t ht htη q =
      prescribedActualFibreCollapse C r hr (hηδ.trans_le hδr) t ht htη q := rfl

end Wikipedia.HopfProblem.CuspCentralHomology
