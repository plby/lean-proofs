import Wikipedia.NoExoticSixSphere.ChartClosedBallFundamentalClass

/-!
# Compact neighborhoods carrying constructed relative fundamental classes

Every neighborhood of a point in the original manifold contains a closed
chart-ball neighborhood. Its actual relative mod-two fundamental class is
constructed by the preceding evaluation isomorphisms. This is a local
existence theorem, not a global assembly or duality theorem.
-/

noncomputable section

open Metric Set Filter
open scoped Topology

namespace NoExoticSixSphere.ChartClosedBall

variable {E M : Type} [NormedAddCommGroup E] [TopologicalSpace M]

/-- A positive-radius closed chart ball centered at the chart image is a genuine neighborhood. -/
theorem support_mem_nhds (e : OpenPartialHomeomorph M E) (x : M) (hx : x ∈ e.source)
    (R : ℝ) (hR : 0 < R) (hB : closedBall (e x) R ⊆ e.target) :
    support e (e x) R ∈ 𝓝 x := by
  have hO := e.isOpen_inter_preimage (isOpen_ball (x := e x) (ε := R))
  have hxO : x ∈ e.source ∩ e ⁻¹' ball (e x) R := ⟨hx, mem_ball_self hR⟩
  apply Filter.mem_of_superset (hO.mem_nhds hxO)
  intro y hy
  exact (mem_support_iff e (e x) R hB y hy.1).mpr (ball_subset_closedBall hy.2)

/-- Shrinking in a supplied actual chart gives a closed chart ball inside any neighborhood. -/
theorem exists_support_subset (e : OpenPartialHomeomorph M E) (x : M) (hx : x ∈ e.source)
    (U : Set M) (hU : U ∈ 𝓝 x) :
    ∃ R : ℝ, 0 < R ∧ closedBall (e x) R ⊆ e.target ∧ support e (e x) R ⊆ U := by
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hU
  have hO : IsOpen (e.target ∩ e.symm ⁻¹' V) := e.isOpen_inter_preimage_symm hV
  have hxO : e x ∈ e.target ∩ e.symm ⁻¹' V := by
    refine ⟨e.map_source hx, ?_⟩
    simpa only [mem_preimage, e.left_inv hx] using hxV
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hxO)
  have hsmall : closedBall (e x) (r / 2) ⊆ e.target ∩ e.symm ⁻¹' V :=
    (closedBall_subset_ball (half_lt_self hr)).trans hball
  refine ⟨r / 2, half_pos hr, fun y hy => (hsmall hy).1, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact hVU (hsmall hz).2

end NoExoticSixSphere.ChartClosedBall

namespace NoExoticSixSphere.SupportedRelativeHomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]

/-- Every original neighborhood contains a compact neighborhood with a unique actual
relative mod-two fundamental class. No class or evaluation isomorphism is an input. -/
theorem exists_compact_fundamental_neighborhood (x : M) (U : Set M) (hU : U ∈ 𝓝 x) :
    ∃ K : Set M, IsCompact K ∧ K ∈ 𝓝 x ∧ K ⊆ U ∧
      ∃! c : Homology (ModuleCat.of ℤ (ZMod 2)) K (n + 3),
        IsFundamentalOn (E := E) n K c := by
  let e := chartAt E x
  have hx : x ∈ e.source := mem_chart_source E x
  obtain ⟨R, hR, hB, hKU⟩ := ChartClosedBall.exists_support_subset e x hx U hU
  exact ⟨ChartClosedBall.support e (e x) R,
    ChartClosedBall.support_isCompact e (e x) R hB,
    ChartClosedBall.support_mem_nhds e x hx R hR hB, hKU,
    ChartClosedBall.existsUnique_fundamentalClass n e (e x) R hR.le hB⟩

end NoExoticSixSphere.SupportedRelativeHomology
