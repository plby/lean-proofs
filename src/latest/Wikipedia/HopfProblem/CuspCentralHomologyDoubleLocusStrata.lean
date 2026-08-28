import Wikipedia.HopfProblem.CuspCentralHomologyOpenCoverBoundary
import Wikipedia.HopfProblem.CuspCentralHomologyEdgeBranches
import Wikipedia.HopfProblem.CuspHoneycombStrata
import Wikipedia.HopfProblem.CuspDoubleCurves

/-!
# The radial boundary is the genuine central double locus

The radius-one subset of the actual quotient central fibre is precisely
the locus of at least two original toric branches. Its complement is the
one-branch stratum, and the boundary is the union of the three actual
double curves. These identifications need only a positive cusp radius;
no regularity or small-drift assumption is used.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction CuspPositiveRetraction CuspCollapse
open CuspHoneycomb CuspHoneycombTiling

local notation "Plane" => CuspHoneycombTiling.Plane

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The actual central projection preserves the chart-independent branch count. -/
@[simp] theorem centralProject_branchCount (x : CentralFibre) :
    CuspQuotient.branchCount C ε (centralProject C ε hε x).1 =
      ToricSpace.branchCount (x : Space) := rfl

/-- Compact phases do not change the branch count in the original quotient. -/
@[simp] theorem centralCollapseMap_branchCount (p : PhasePositiveSpace) :
    CuspQuotient.branchCount C ε (centralCollapseMap C ε hε p).1 =
      ToricSpace.branchCount (p.2.1 : Space) := by
  change ToricSpace.branchCount (compactFibreAction p.1 (p.2.1 : Space)) = _
  exact branchCount_torusAction _ _

@[simp] theorem fundamentalCellMap_branchCount (p : FundamentalCell) :
    CuspQuotient.branchCount C ε (fundamentalCellMap C ε hε p).1 =
      ToricSpace.branchCount ((honeycombHomeomorph (C 0) (p.2 : Plane)).1 : Space) :=
  centralCollapseMap_branchCount C ε hε (p.1, honeycombHomeomorph (C 0) (p.2 : Plane))

/-- Including both endpoints, every actual compatible boundary point has
at least two branches. -/
theorem edgeArcPositive_branchCount_ge_two (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) :
    2 ≤ ToricSpace.branchCount ((edgeArcPositive C₀ k t).1 : Space) := by
  by_cases ht0 : t = 0
  · subst t
    rw [edgeArcPositive_zero_branchCount]
    decide
  by_cases ht1 : t = 1
  · subst t
    rw [edgeArcPositive_one_branchCount]
    decide
  rw [edgeArcPositive_branchCount C₀ k t ht0 ht1]

/-- The geometric radius-one boundary is exactly the original quotient
double locus, not a substitute subset of a model space. -/
theorem mem_centralBoundary_iff_branchCount (q : QuotientCentralFibre C ε) :
    q ∈ centralBoundary C ε hε ↔ 2 ≤ CuspQuotient.branchCount C ε q.1 := by
  constructor
  · intro hq
    obtain ⟨k, t, u, rfl⟩ := (mem_centralBoundary_iff_edgeArc C ε hε q).mp hq
    rw [centralCollapseMap_branchCount]
    exact edgeArcPositive_branchCount_ge_two (C 0) k t
  · intro hq
    obtain ⟨p, rfl⟩ := fundamentalCellMap_surjective C ε hε q
    apply (fundamentalCellMap_mem_centralBoundary_iff C ε hε p).mpr
    by_contra hp
    have hi : (p.2 : Plane) ∈ interior baseCell :=
      (mem_interior_iff_notMem_frontier p.2.2).mpr hp
    have hb : ToricSpace.branchCount
        ((honeycombHomeomorph (C 0) (p.2 : Plane)).1 : Space) = 1 :=
      (honeycombHomeomorph_branchCount_eq_one_iff (C 0) (p.2 : Plane)).mpr
        ⟨0, by simpa only [cell_zero] using hi⟩
    rw [fundamentalCellMap_branchCount, hb] at hq
    exact (by decide : ¬2 ≤ (1 : ℕ)) hq

theorem centralBoundary_eq_doubleLocus :
    centralBoundary C ε hε =
      {q : QuotientCentralFibre C ε | 2 ≤ CuspQuotient.branchCount C ε q.1} := by
  ext q
  exact mem_centralBoundary_iff_branchCount C ε hε q

/-- The actual open-cell region is exactly the one-branch stratum. -/
theorem mem_innerRegion_iff_branchCount_eq_one (q : QuotientCentralFibre C ε) :
    q ∈ innerRegion C ε hε ↔ CuspQuotient.branchCount C ε q.1 = 1 := by
  rw [innerRegion_eq_compl_centralBoundary]
  change ¬q ∈ centralBoundary C ε hε ↔ CuspQuotient.branchCount C ε q.1 = 1
  rw [mem_centralBoundary_iff_branchCount]
  have hp : 0 < CuspQuotient.branchCount C ε q.1 :=
    (CuspQuotient.branchCount_pos_iff C ε q.1).mpr q.2
  omega

theorem innerRegion_eq_oneBranchLocus :
    innerRegion C ε hε =
      {q : QuotientCentralFibre C ε | CuspQuotient.branchCount C ε q.1 = 1} := by
  ext q
  exact mem_innerRegion_iff_branchCount_eq_one C ε hε q

/-- The three previously constructed actual double curves exhaust the
central boundary, with the inherited central-fibre topology. -/
theorem centralBoundary_eq_union_doubleCurves :
    centralBoundary C ε hε = ⋃ i : Fin 3,
      (Subtype.val : QuotientCentralFibre C ε → CuspQuotient.QuotientSpace C ε) ⁻¹'
        CuspQuotient.doubleCurve C ε hε i := by
  rw [← Set.preimage_iUnion, ← CuspQuotient.double_locus_eq_union C ε hε]
  exact centralBoundary_eq_doubleLocus C ε hε

/-- Closedness of the genuine double locus does not require any analytic
or small-drift hypothesis on the correction matrix. -/
theorem centralBoundary_isClosed_unconditional : IsClosed (centralBoundary C ε hε) := by
  rw [centralBoundary_eq_union_doubleCurves]
  apply isClosed_iUnion_of_finite
  intro i
  exact (CuspQuotient.doubleCurve_isClosed C ε hε i).preimage continuous_subtype_val

theorem innerRegion_isOpen_unconditional : IsOpen (innerRegion C ε hε) := by
  rw [innerRegion_eq_compl_centralBoundary]
  exact (centralBoundary_isClosed_unconditional C ε hε).isOpen_compl

end Wikipedia.HopfProblem.CuspCentralHomology
