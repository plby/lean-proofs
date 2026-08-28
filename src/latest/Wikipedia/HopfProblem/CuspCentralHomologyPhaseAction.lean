import Wikipedia.HopfProblem.CuspCentralHomologyDoubleLocusStrata
import Mathlib.Topology.CompactOpen

/-!
# The actual compact fibre-torus action on the central cusp quotient

Multiplication of the original compact phase respects the exact
lattice-and-stabilizer relation. It therefore acts on the original central
quotient, not just on a chosen cell presentation. The action is jointly
continuous and preserves the genuine double locus.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction CuspPositiveRetraction CuspCollapse

def phaseMultiply (u : CompactFibreTorus) (p : PhasePositiveSpace) : PhasePositiveSpace :=
  (u * p.1, p.2)

/-- Original phase multiplication preserves the full actual fibre relation. -/
theorem centralCollapseRelation_phaseMultiply (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (u : CompactFibreTorus) (p q : PhasePositiveSpace)
    (h : centralCollapseRelation C₀ p q) :
    centralCollapseRelation C₀ (phaseMultiply u p) (phaseMultiply u q) := by
  obtain ⟨v, hv, hu⟩ := h
  refine ⟨v, hv, ?_⟩
  change (u * p.1)⁻¹ * (deckFibrePhase C₀ v * (u * q.1)) ∈
    MulAction.stabilizer CompactFibreTorus (p.2.1 : Space)
  have he : (u * p.1)⁻¹ * (deckFibrePhase C₀ v * (u * q.1)) =
      p.1⁻¹ * (deckFibrePhase C₀ v * q.1) := by
    calc
      _ = p.1⁻¹ * ((u⁻¹ * u) * (deckFibrePhase C₀ v * q.1)) := by
        simp only [mul_inv_rev]
        ac_rfl
      _ = p.1⁻¹ * (deckFibrePhase C₀ v * q.1) := by rw [inv_mul_cancel, one_mul]
  rw [he]
  exact hu

def phaseMultiplyModel (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (u : CompactFibreTorus) :
    CentralCollapseModel C₀ → CentralCollapseModel C₀ :=
  Quotient.map' (phaseMultiply u) (centralCollapseRelation_phaseMultiply C₀ u)

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The action on the literal central fibre of the original cusp quotient. -/
def centralPhaseAction (u : CompactFibreTorus) (x : QuotientCentralFibre C ε) :
    QuotientCentralFibre C ε :=
  centralCollapseModelMap C ε hε
    (phaseMultiplyModel (C 0) u ((centralCollapseEquiv C ε hε).symm x))

@[simp] theorem centralPhaseAction_collapse (u : CompactFibreTorus) (p : PhasePositiveSpace) :
    centralPhaseAction C ε hε u (centralCollapseMap C ε hε p) =
      centralCollapseMap C ε hε (u * p.1, p.2) := by
  unfold centralPhaseAction
  rw [centralCollapseEquiv_symm_map]
  rfl

/-- The descended action is exactly the original compact fibre action
followed by the original quotient projection. -/
theorem centralPhaseAction_project (u : CompactFibreTorus) (x : CentralFibre) :
    centralPhaseAction C ε hε u (centralProject C ε hε x) =
      centralProject C ε hε
        ⟨compactFibreAction u (x : Space), by rw [time_compactFibreAction, x.2]⟩ := by
  obtain ⟨⟨v, q⟩, rfl⟩ := centralPolarMap_surjective x
  change centralPhaseAction C ε hε u (centralCollapseMap C ε hε (v, q)) = _
  rw [centralPhaseAction_collapse]
  apply congrArg (centralProject C ε hε)
  apply Subtype.ext
  exact (compactFibreAction_mul u v (q.1 : Space)).symm

@[simp] theorem centralPhaseAction_one (x : QuotientCentralFibre C ε) :
    centralPhaseAction C ε hε 1 x = x := by
  obtain ⟨p, rfl⟩ := centralCollapseMap_surjective C ε hε x
  simp only [centralPhaseAction_collapse, one_mul, Prod.eta]

theorem centralPhaseAction_mul (u v : CompactFibreTorus) (x : QuotientCentralFibre C ε) :
    centralPhaseAction C ε hε u (centralPhaseAction C ε hε v x) =
      centralPhaseAction C ε hε (u * v) x := by
  obtain ⟨p, rfl⟩ := centralCollapseMap_surjective C ε hε x
  simp only [centralPhaseAction_collapse, mul_assoc]

/-- A named action structure avoids changing ambient quotient instances. -/
@[instance_reducible] def centralPhaseMulAction :
    MulAction CompactFibreTorus (QuotientCentralFibre C ε) where
  smul := centralPhaseAction C ε hε
  one_smul := centralPhaseAction_one C ε hε
  mul_smul u v x := (centralPhaseAction_mul C ε hε u v x).symm

@[simp] theorem centralPhaseAction_branchCount (u : CompactFibreTorus)
    (x : QuotientCentralFibre C ε) :
    CuspQuotient.branchCount C ε (centralPhaseAction C ε hε u x).1 =
      CuspQuotient.branchCount C ε x.1 := by
  obtain ⟨p, rfl⟩ := centralCollapseMap_surjective C ε hε x
  rw [centralPhaseAction_collapse, centralCollapseMap_branchCount, centralCollapseMap_branchCount]

theorem centralPhaseAction_mem_boundary_iff (u : CompactFibreTorus)
    (x : QuotientCentralFibre C ε) :
    centralPhaseAction C ε hε u x ∈ centralBoundary C ε hε ↔ x ∈ centralBoundary C ε hε := by
  rw [mem_centralBoundary_iff_branchCount, centralPhaseAction_branchCount,
    mem_centralBoundary_iff_branchCount]

/-- Restriction to the literal central double locus. -/
def boundaryPhaseAction (u : CompactFibreTorus) (x : centralBoundary C ε hε) :
    centralBoundary C ε hε :=
  ⟨centralPhaseAction C ε hε u x.1,
    (centralPhaseAction_mem_boundary_iff C ε hε u x.1).mpr x.2⟩

@[simp] theorem boundaryPhaseAction_coe (u : CompactFibreTorus)
    (x : centralBoundary C ε hε) :
    (boundaryPhaseAction C ε hε u x : QuotientCentralFibre C ε) =
      centralPhaseAction C ε hε u x.1 := rfl

@[simp] theorem boundaryPhaseAction_one (x : centralBoundary C ε hε) :
    boundaryPhaseAction C ε hε 1 x = x :=
  Subtype.ext (centralPhaseAction_one C ε hε x.1)

theorem boundaryPhaseAction_mul (u v : CompactFibreTorus) (x : centralBoundary C ε hε) :
    boundaryPhaseAction C ε hε u (boundaryPhaseAction C ε hε v x) =
      boundaryPhaseAction C ε hε (u * v) x :=
  Subtype.ext (centralPhaseAction_mul C ε hε u v x.1)

@[instance_reducible] def boundaryPhaseMulAction :
    MulAction CompactFibreTorus (centralBoundary C ε hε) where
  smul := boundaryPhaseAction C ε hε
  one_smul := boundaryPhaseAction_one C ε hε
  mul_smul u v x := (boundaryPhaseAction_mul C ε hε u v x).symm

variable (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))

include hC in
/-- Joint continuity follows from the actual quotient map and local
compactness of the original phase torus. -/
theorem centralPhaseAction_continuous :
    Continuous (fun p : CompactFibreTorus × QuotientCentralFibre C ε =>
      centralPhaseAction C ε hε p.1 p.2) := by
  apply (centralCollapseMap_isQuotientMap C ε hε hC).continuous_lift_prod_right
  have hm : Continuous (fun p : CompactFibreTorus × PhasePositiveSpace =>
      (p.1 * p.2.1, p.2.2)) :=
    (continuous_fst.mul continuous_snd.fst).prodMk continuous_snd.snd
  exact ((centralCollapseMap_continuous C ε hε).comp hm).congr
    (fun p => (centralPhaseAction_collapse C ε hε p.1 p.2).symm)

def centralPhaseActionMap :
    C(CompactFibreTorus × QuotientCentralFibre C ε, QuotientCentralFibre C ε) :=
  ⟨fun p => centralPhaseAction C ε hε p.1 p.2, centralPhaseAction_continuous C ε hε hC⟩

@[simp] theorem centralPhaseActionMap_apply
    (p : CompactFibreTorus × QuotientCentralFibre C ε) :
    centralPhaseActionMap C ε hε hC p = centralPhaseAction C ε hε p.1 p.2 := rfl

include hC in
theorem boundaryPhaseAction_continuous :
    Continuous (fun p : CompactFibreTorus × centralBoundary C ε hε =>
      boundaryPhaseAction C ε hε p.1 p.2) :=
  ((centralPhaseAction_continuous C ε hε hC).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

def boundaryPhaseActionMap :
    C(CompactFibreTorus × centralBoundary C ε hε, centralBoundary C ε hε) :=
  ⟨fun p => boundaryPhaseAction C ε hε p.1 p.2, boundaryPhaseAction_continuous C ε hε hC⟩

@[simp] theorem boundaryPhaseActionMap_apply
    (p : CompactFibreTorus × centralBoundary C ε hε) :
    boundaryPhaseActionMap C ε hε hC p = boundaryPhaseAction C ε hε p.1 p.2 := rfl

end Wikipedia.HopfProblem.CuspCentralHomology
