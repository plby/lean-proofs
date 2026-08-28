import Wikipedia.HopfProblem.SpecialPeriodsTriangleInterior
import Wikipedia.HopfProblem.RiemannBoundaryIdealTopology

/-!
# The actual ideal vertex of the closed triangle

The vertical ray `-1 + (t + 2) * I` lies in the genuine triangle interior
for nonnegative `t` and escapes every compact subset of the complex plane.
It therefore approaches infinity through the finite one-point image of
that interior. No boundary parametrization or Jordan-domain hypothesis is
used to establish this ideal boundary point.
-/

noncomputable section

open Filter Set Topology
open scoped OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- A concrete vertical ray in the source triangle. -/
def triangleVerticalRay (t : ℝ) : ℂ := -1 + ((t : ℂ) + 2) * Complex.I

@[simp] theorem triangleVerticalRay_re (t : ℝ) : (triangleVerticalRay t).re = -1 := by
  simp [triangleVerticalRay]

@[simp] theorem triangleVerticalRay_im (t : ℝ) : (triangleVerticalRay t).im = t + 2 := by
  simp [triangleVerticalRay]

/-- Every nonnegative point on this ray is inside the actual open triangle. -/
theorem triangleVerticalRay_mem {t : ℝ} (ht : 0 ≤ t) :
    triangleVerticalRay t ∈ triangleInterior := by
  rw [mem_triangleInterior_iff_epigraph, triangleVerticalRay_re, triangleVerticalRay_im]
  refine ⟨stripLeft_lt_neg_one, by norm_num, ?_⟩
  linarith [boundaryHeight_le_one (-1)]

theorem triangleVerticalRay_eventually_mem :
    ∀ᶠ t : ℝ in atTop, triangleVerticalRay t ∈ triangleInterior :=
  (eventually_ge_atTop (0 : ℝ)).mono fun _ ht => triangleVerticalRay_mem ht

/-- The imaginary part of the explicit interior ray goes to positive infinity. -/
theorem triangleVerticalRay_im_tendsto :
    Tendsto (fun t : ℝ => (triangleVerticalRay t).im) atTop atTop := by
  simpa only [triangleVerticalRay_im, id_eq] using
    (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_id)

theorem triangleVerticalRay_norm_tendsto :
    Tendsto (fun t : ℝ => ‖triangleVerticalRay t‖) atTop atTop :=
  tendsto_atTop_mono (fun t => Complex.im_le_norm (triangleVerticalRay t))
    triangleVerticalRay_im_tendsto

/-- This particular interior ray escapes every compact subset of `ℂ`. -/
theorem triangleVerticalRay_tendsto_cocompact :
    Tendsto triangleVerticalRay atTop (cocompact ℂ) := by
  simpa only [Metric.cobounded_eq_cocompact] using
    tendsto_norm_atTop_iff_cobounded.mp triangleVerticalRay_norm_tendsto

/-- The explicit finite points converge to the actual ideal point of the
one-point compactification. -/
theorem triangleVerticalRay_tendsto_infty :
    Tendsto (fun t : ℝ => (triangleVerticalRay t : OnePoint ℂ)) atTop (𝓝 ∞) := by
  have hcoe : Tendsto ((↑) : ℂ → OnePoint ℂ) (cocompact ℂ) (𝓝 ∞) := by
    simpa only [coclosedCompact_eq_cocompact] using (OnePoint.tendsto_coe_infty (X := ℂ))
  exact hcoe.comp triangleVerticalRay_tendsto_cocompact

/-- The convergence is through the interior, rather than merely through
unspecified points in the ambient one-point compactification. -/
theorem triangleVerticalRay_tendsto_interior_infty :
    Tendsto (fun t : ℝ => (triangleVerticalRay t : OnePoint ℂ)) atTop
      (𝓝[RiemannBoundary.onePointDomain triangleInterior] ∞) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨triangleVerticalRay_tendsto_infty, ?_⟩
  exact triangleVerticalRay_eventually_mem.mono fun _ ht =>
    RiemannBoundary.coe_mem_onePointDomain.mpr ht

/-- Infinity really is a boundary point of the finite triangle interior. -/
theorem triangle_infty_mem_frontier :
    (∞ : OnePoint ℂ) ∈ frontier (RiemannBoundary.onePointDomain triangleInterior) :=
  RiemannBoundary.infty_mem_frontier_onePointDomain_of_cocompact
    triangleVerticalRay_tendsto_cocompact triangleVerticalRay_eventually_mem

theorem triangle_infty_mem_closure :
    (∞ : OnePoint ℂ) ∈ closure (RiemannBoundary.onePointDomain triangleInterior) :=
  frontier_subset_closure triangle_infty_mem_frontier

/-- Limits from the triangle interior at infinity use a nontrivial filter. -/
theorem triangle_infty_nhdsWithin_neBot :
    NeBot (𝓝[RiemannBoundary.onePointDomain triangleInterior] (∞ : OnePoint ℂ)) :=
  mem_closure_iff_nhdsWithin_neBot.mp triangle_infty_mem_closure

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
