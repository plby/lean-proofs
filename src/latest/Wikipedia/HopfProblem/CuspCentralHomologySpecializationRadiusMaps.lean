import Wikipedia.HopfProblem.CuspCentralHomologyTopDegreesRadius
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelProduct

/-!
# Radius naturality of the actual specialization maps

The existing central-fibre radius homeomorphism keeps each original
toric representative. It therefore commutes with the central projection,
the honeycomb collapse, its free-source quotient, and its marked product
presentation. These are equalities of the actual continuous maps.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction CuspCollapse CuspHoneycomb SpecializationModel

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hδ : 0 < δ)

/-- Changing the ambient radius keeps the original central toric representative. -/
@[simp] theorem centralRadiusHomeomorph_centralProject (x : CentralFibre) :
    centralRadiusHomeomorph C r δ hδr hC hδ (centralProject C δ hδ x) =
      centralProject C r (hδ.trans_le hδr) x := by
  apply Subtype.ext
  change (openQuotientRadiusHomeomorph C hδr hC (centralProject C δ hδ x).1).1 =
    (centralProject C r (hδ.trans_le hδr) x).1
  simp only [centralProject, openQuotientRadiusHomeomorph_quotientMap, openQuotientMap]

@[simp] theorem centralRadiusHomeomorph_symm_centralProject (x : CentralFibre) :
    (centralRadiusHomeomorph C r δ hδr hC hδ).symm
      (centralProject C r (hδ.trans_le hδr) x) = centralProject C δ hδ x := by
  apply (centralRadiusHomeomorph C r δ hδr hC hδ).injective
  rw [Homeomorph.apply_symm_apply, centralRadiusHomeomorph_centralProject]

theorem centralRadiusHomeomorph_comp_centralProject :
    (centralRadiusHomeomorph C r δ hδr hC hδ :
      C(QuotientCentralFibre C δ, QuotientCentralFibre C r)).comp
        ⟨centralProject C δ hδ, centralProject_continuous C δ hδ⟩ =
      ⟨centralProject C r (hδ.trans_le hδr),
        centralProject_continuous C r (hδ.trans_le hδr)⟩ := by
  apply ContinuousMap.ext
  intro x
  exact centralRadiusHomeomorph_centralProject C r δ hδr hC hδ x

@[simp] theorem centralRadiusHomeomorph_centralCollapseMap (p : PhasePositiveSpace) :
    centralRadiusHomeomorph C r δ hδr hC hδ (centralCollapseMap C δ hδ p) =
      centralCollapseMap C r (hδ.trans_le hδr) p :=
  centralRadiusHomeomorph_centralProject C r δ hδr hC hδ (centralPolarMap p)

/-- The honeycomb positive coordinate and the compact phase are independent
of the ambient radius, so the literal map commutes with radius comparison. -/
@[simp] theorem centralRadiusHomeomorph_honeycombCollapseMap (p : PhasePlane) :
    centralRadiusHomeomorph C r δ hδr hC hδ (honeycombCollapseMap C δ hδ p) =
      honeycombCollapseMap C r (hδ.trans_le hδr) p :=
  centralRadiusHomeomorph_centralCollapseMap C r δ hδr hC hδ
    (phaseCoordinatesHomeomorph (C 0) p)

theorem centralRadiusHomeomorph_comp_honeycombCollapseMap :
    (centralRadiusHomeomorph C r δ hδr hC hδ :
      C(QuotientCentralFibre C δ, QuotientCentralFibre C r)).comp
        ⟨honeycombCollapseMap C δ hδ, honeycombCollapseMap_continuous C δ hδ⟩ =
      ⟨honeycombCollapseMap C r (hδ.trans_le hδr),
        honeycombCollapseMap_continuous C r (hδ.trans_le hδr)⟩ := by
  apply ContinuousMap.ext
  intro p
  exact centralRadiusHomeomorph_honeycombCollapseMap C r δ hδr hC hδ p

/-- Radius comparison also preserves the actual free-source quotient map. -/
@[simp] theorem centralRadiusHomeomorph_sourceCollapse (q : SourceModel (C 0)) :
    centralRadiusHomeomorph C r δ hδr hC hδ (sourceCollapse C δ hδ q) =
      sourceCollapse C r (hδ.trans_le hδr) q := by
  induction q using Quotient.inductionOn with
  | h p => exact centralRadiusHomeomorph_honeycombCollapseMap C r δ hδr hC hδ p

theorem centralRadiusHomeomorph_comp_sourceCollapse :
    (centralRadiusHomeomorph C r δ hδr hC hδ :
      C(QuotientCentralFibre C δ, QuotientCentralFibre C r)).comp
        (sourceCollapse C δ hδ) = sourceCollapse C r (hδ.trans_le hδr) := by
  apply ContinuousMap.ext
  intro q
  exact centralRadiusHomeomorph_sourceCollapse C r δ hδr hC hδ q

/-- The marked source product is independent of the ambient cusp radius. -/
@[simp] theorem centralRadiusHomeomorph_productCollapse
    (p : CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) :
    centralRadiusHomeomorph C r δ hδr hC hδ (productCollapse C δ hδ p) =
      productCollapse C r (hδ.trans_le hδr) p :=
  centralRadiusHomeomorph_sourceCollapse C r δ hδr hC hδ
    ((sourceProductHomeomorph (C 0)).symm p)

theorem centralRadiusHomeomorph_comp_productCollapse :
    (centralRadiusHomeomorph C r δ hδr hC hδ :
      C(QuotientCentralFibre C δ, QuotientCentralFibre C r)).comp
        (productCollapse C δ hδ) = productCollapse C r (hδ.trans_le hδr) := by
  apply ContinuousMap.ext
  intro p
  exact centralRadiusHomeomorph_productCollapse C r δ hδr hC hδ p

end Wikipedia.HopfProblem.CuspCentralHomology
