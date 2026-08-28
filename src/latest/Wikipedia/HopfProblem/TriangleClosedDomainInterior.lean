import Wikipedia.HopfProblem.TriangleClosedDomainBasic

/-!
# The ambient interior and frontier of the closed triangle

The original triangle image is exactly the topological interior of its
closed set in `OnePoint ℂ`.  Infinity is not an interior point: the real
ray stays outside the closed triangle and also escapes to infinity.
Thus the boundary used for compactification is the literal frontier of
the closed triangle, not merely a selected complement of a dense subset.
-/

noncomputable section

open Set Filter Topology
open scoped OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

open RiemannBoundary

theorem coe_mem_interior_triangleClosedSet_iff (z : ℂ) :
    (z : OnePoint ℂ) ∈ interior triangleClosedSet ↔ z ∈ triangleInterior := by
  have hp : ((↑) : ℂ → OnePoint ℂ) ⁻¹' triangleClosedSet = triangleClosedRegion := by
    ext w
    exact coe_mem_triangleClosedSet_iff w
  have he := OnePoint.isOpenEmbedding_coe.isOpenMap.preimage_interior_eq_interior_preimage
    OnePoint.continuous_coe triangleClosedSet
  rw [hp, interior_triangleClosedRegion] at he
  exact Set.ext_iff.mp he z

/-- The actual real ray approaches infinity through points outside the
closed triangle, since every finite triangle point has positive height. -/
theorem triangleClosedSet_infty_notMem_interior :
    (∞ : OnePoint ℂ) ∉ interior triangleClosedSet := by
  have hn : Tendsto (fun t : ℝ => ‖(t : ℂ)‖) atTop atTop :=
    tendsto_atTop_mono (fun t => by
      simpa only [Complex.ofReal_re, id_eq] using Complex.re_le_norm (t : ℂ)) tendsto_id
  have hc : Tendsto (fun t : ℝ => (t : ℂ)) atTop (cocompact ℂ) := by
    simpa only [Metric.cobounded_eq_cocompact] using
      tendsto_norm_atTop_iff_cobounded.mp hn
  have hcoe : Tendsto ((↑) : ℂ → OnePoint ℂ) (cocompact ℂ) (𝓝 ∞) := by
    simpa only [coclosedCompact_eq_cocompact] using (OnePoint.tendsto_coe_infty (X := ℂ))
  have hcl : (∞ : OnePoint ℂ) ∈ closure triangleClosedSetᶜ := by
    apply isClosed_closure.mem_of_tendsto (hcoe.comp hc)
    filter_upwards with t
    exact subset_closure (triangleClosedSet_no_real_points (by simp))
  simpa only [closure_compl, mem_compl_iff] using hcl

/-- The closed source has precisely the original source image as its
ambient topological interior. -/
theorem interior_triangleClosedSet :
    interior triangleClosedSet = onePointDomain triangleInterior := by
  ext x
  induction x using OnePoint.rec with
  | infty => simp only [triangleClosedSet_infty_notMem_interior,
      infty_notMem_onePointDomain]
  | coe z =>
    rw [coe_mem_interior_triangleClosedSet_iff, coe_mem_onePointDomain]

theorem triangleClosedSet_regularClosed :
    closure (interior triangleClosedSet) = triangleClosedSet := by
  rw [interior_triangleClosedSet]
  rfl

/-- The frontier of the actual closed set is the same boundary already
obtained from the original open triangle image. -/
theorem frontier_triangleClosedSet :
    frontier triangleClosedSet = frontier (onePointDomain triangleInterior) := by
  change closure triangleClosedSet \ interior triangleClosedSet =
    closure (onePointDomain triangleInterior) \ interior (onePointDomain triangleInterior)
  rw [triangleClosedSet_isClosed.closure_eq, interior_triangleClosedSet,
    (isOpen_onePointDomain triangleInterior_isOpen).interior_eq]
  rfl

theorem triangleClosedBoundary_iff_frontier_closed (x : TriangleClosedDomain) :
    x ∉ triangleClosedInterior ↔ x.val ∈ frontier triangleClosedSet := by
  rw [frontier_triangleClosedSet]
  exact triangleClosedBoundary_iff_frontier x

theorem triangle_infty_mem_frontier_closed :
    (∞ : OnePoint ℂ) ∈ frontier triangleClosedSet := by
  rw [frontier_triangleClosedSet]
  exact triangle_infty_mem_frontier

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
