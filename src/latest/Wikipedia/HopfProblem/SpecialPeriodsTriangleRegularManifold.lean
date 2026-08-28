import Wikipedia.HopfProblem.SpecialPeriodsTriangleRegularTopology
import Wikipedia.HopfProblem.CuspPuncturedCovering

/-!
# Complex charts on regular orbit quotients

The free locus inherits the original manifold charts.  Its orbit quotient
gets the covering atlas, whose changes of charts are locally the original
holomorphic action.  Thus the quotient map is locally biholomorphic for these
constructed atlases, not merely for a transported or assumed complex structure.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.FreeActionLocus

variable (G X E : Type*) [Group G] [TopologicalSpace X] [MulAction G X]
    [T2Space X] [LocallyCompactSpace X] [ContinuousConstSMul G X]
    [ProperlyDiscontinuousSMul G X] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [ChartedSpace E X]

/-- The regular domain uses the charts inherited from the actual open subset. -/
instance chartedSpace : ChartedSpace E (Space G X) :=
  inferInstanceAs (ChartedSpace E (opens G X))

instance isManifold (n : ℕ∞ω) [IsManifold (modelWithCornersSelf ℂ E) n X] :
    IsManifold (modelWithCornersSelf ℂ E) n (Space G X) :=
  inferInstanceAs (IsManifold (modelWithCornersSelf ℂ E) n (opens G X))

/-- Restricting a holomorphic action to its invariant regular domain preserves
holomorphicity in the inherited charts. -/
theorem smul_contMDiff (n : ℕ∞ω)
    (hG : ∀ g : G, ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n
      (fun x : X => g • x)) (g : G) :
    ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n
      (fun x : Space G X => g • x) := by
  intro x
  have he : ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n
      (fun y : Space G X => ((g • y : Space G X) : X)) x ↔
      ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n
        (fun y : Space G X => g • y) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff (U := opens G X)
      (fun y : Space G X => g • y) univ x
  exact he.mp (((hG g).comp (contMDiff_subtype_val (U := opens G X))) x)

/-- Covering charts, built from actual inverse branches of the orbit map. -/
@[instance_reducible] def quotientChartedSpace : ChartedSpace E (OrbitSpace G X) :=
  CoveringQuotient.chartedSpace (E := E) (quotientCovering G X)

theorem quotient_isManifold (n : ℕ∞ω) [IsManifold (modelWithCornersSelf ℂ E) n X]
    (hG : ∀ g : G, ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n
      (fun x : X => g • x)) :
    letI := quotientChartedSpace G X E
    IsManifold (modelWithCornersSelf ℂ E) n (OrbitSpace G X) :=
  CoveringQuotient.isManifold (quotientCovering G X) n (smul_contMDiff G X E n hG)

theorem project_contMDiff (n : ℕ∞ω) [IsManifold (modelWithCornersSelf ℂ E) n X]
    (hG : ∀ g : G, ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n
      (fun x : X => g • x)) :
    letI := quotientChartedSpace G X E
    ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n (project G X) :=
  CoveringQuotient.contMDiff_project (quotientCovering G X) n (smul_contMDiff G X E n hG)

/-- The covering map is a local biholomorphism in the constructed quotient atlas. -/
theorem project_isLocalDiffeomorph [IsManifold (modelWithCornersSelf ℂ E) ω X]
    (hG : ∀ g : G, ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
      (fun x : X => g • x)) :
    letI := quotientChartedSpace G X E
    IsLocalDiffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (project G X) :=
  CoveringQuotient.project_isLocalDiffeomorph (quotientCovering G X)
    (smul_contMDiff G X E ω hG)

end Wikipedia.HopfProblem.FreeActionLocus
