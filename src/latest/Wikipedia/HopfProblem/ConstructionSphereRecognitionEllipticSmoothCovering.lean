import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticSmoothDescent
import Wikipedia.HopfProblem.QuotientManifold

/-!
# The unchanged period-torus covering is locally a diffeomorphism

The local inverses are the actual inverse branches of the quotient map.
Their regularity is proved in the original discrete-quotient atlas from
the locally constant lattice difference, without a new quotient atlas.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (L : Submodule ℤ E) [DiscreteTopology L]

/-- The native discrete-quotient charts also give the open-set descent criterion. -/
theorem discrete_contMDiffOn_of_comp_mkQ
    {F H N : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]
    (I : ModelWithCorners ℂ F H) (n : ℕ∞ω) {f : E ⧸ L → N} {U : Set (E ⧸ L)}
    (hU : IsOpen U)
    (hf : ContMDiffOn 𝓘(ℂ, E) I n (f ∘ L.mkQ) (L.mkQ ⁻¹' U)) :
    ContMDiffOn 𝓘(ℂ, E) I n f U := by
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  rw [contMDiffAt_iff_source]
  have hxchart : x ∈ (DiscreteQuotient.chart L x).source := mem_chart_source E x
  have hmem : DiscreteQuotient.chart L x x ∈ L.mkQ ⁻¹' U := by
    change L.mkQ (DiscreteQuotient.chart L x x) ∈ U
    rw [DiscreteQuotient.mkQ_chart L x x hxchart]
    exact hx
  have hh := hf.contMDiffAt ((hU.preimage L.continuous_mkQ).mem_nhds hmem)
  have hchart : chartAt E x = DiscreteQuotient.chart L x := rfl
  simpa [extChartAt, OpenPartialHomeomorph.extend, hchart, DiscreteQuotient.chart_symm] using
    hh.contMDiffWithinAt (s := Set.univ)

/-- Each original inverse branch of the period projection is complex analytic. -/
theorem discrete_localInverse_contMDiffOn (n : ℕ∞ω) (x : E) :
    ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E) n
      ((DiscreteQuotient.quotient_localHomeomorph L).localInverseAt x)
      ((DiscreteQuotient.quotient_localHomeomorph L).localInverseAt x).source := by
  let hq := DiscreteQuotient.quotient_localHomeomorph L
  let e := hq.localInverseAt x
  apply discrete_contMDiffOn_of_comp_mkQ L 𝓘(ℂ, E) n e.open_source
  apply ContDiffOn.contMDiffOn
  apply contDiffOn_of_sub_mem_discrete L
  · exact e.continuousOn.comp L.continuous_mkQ.continuousOn (fun _ hz => hz)
  · intro z hz
    exact (Submodule.Quotient.eq L).mp
      (hq.apply_localInverseAt_of_mem (x := x) hz)

/-- The original period projection is locally a complex diffeomorphism in its native atlas. -/
theorem discreteProject_isLocalDiffeomorph (n : ℕ∞ω) :
    IsLocalDiffeomorph 𝓘(ℂ, E) 𝓘(ℂ, E) n (L.mkQ : E → E ⧸ L) := by
  intro x
  let hq := DiscreteQuotient.quotient_localHomeomorph L
  let e := hq.localInverseAt x
  let p : PartialDiffeomorph 𝓘(ℂ, E) 𝓘(ℂ, E) E (E ⧸ L) n :=
    { toPartialEquiv := e.symm.toPartialEquiv
      open_source := e.open_target
      open_target := e.open_source
      contMDiffOn_toFun := by
        change ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E) n e.symm e.target
        rw [show (e.symm : E → E ⧸ L) = L.mkQ from hq.localInverseAt_symm x]
        exact (DiscreteQuotient.contMDiff_mkQ L n).contMDiffOn
      contMDiffOn_invFun := discrete_localInverse_contMDiffOn L n x }
  refine ⟨p, hq.self_mem_localInverseAt_target, ?_⟩
  intro z _
  change L.mkQ z = e.symm z
  rw [show (e.symm : E → E ⧸ L) = L.mkQ from hq.localInverseAt_symm x]

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticSmooth
