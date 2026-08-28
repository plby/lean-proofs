import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientEllipticCharts

/-!
# Exact branching orders of the actual elliptic quotient coordinates

Dividing a centered Cayley coordinate by a nonzero radius preserves its
simple zero.  Its `m`th power therefore has analytic order exactly `m`.
The actual quotient chart agrees with this expression on the chosen open
elliptic neighbourhood, so its pulled-back complex germ has the same order.
In particular, the two actual elliptic quotient coordinates have branching
orders three and four.  No complex atlas on the entire orbit space is needed
for these coordinate-germ statements.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- The normalized Cayley coordinate, extended through the actual local
upper-half-plane inclusion, is analytic at every upper-half-plane point. -/
theorem normalizedCayley_analyticAt (a z : ℍ) (r : ℝ) (hr : r ≠ 0) :
    AnalyticAt ℂ (normalizedCayley a r ∘ ofComplex) (z : ℂ) :=
  (cayleyCoordinate_analyticAt a z).div analyticAt_const (Complex.ofReal_ne_zero.mpr hr)

/-- A nonzero radius normalization preserves the simple Cayley zero. -/
theorem normalizedCayley_order_center (a : ℍ) (r : ℝ) (hr : r ≠ 0) :
    analyticOrderAt (normalizedCayley a r ∘ ofComplex) (a : ℂ) = 1 := by
  have hc : AnalyticAt ℂ (fun _ : ℂ => (r : ℂ)⁻¹) (a : ℂ) := analyticAt_const
  have hcorder : analyticOrderAt (fun _ : ℂ => (r : ℂ)⁻¹) (a : ℂ) = 0 :=
    hc.analyticOrderAt_eq_zero.mpr (inv_ne_zero (Complex.ofReal_ne_zero.mpr hr))
  have he : normalizedCayley a r ∘ ofComplex =
      (cayleyCoordinate a ∘ ofComplex) * (fun _ : ℂ => (r : ℂ)⁻¹) := by
    funext z
    exact div_eq_mul_inv _ _
  rw [he, analyticOrderAt_mul (cayleyCoordinate_analyticAt a a) hc,
    cayleyCoordinate_order_center, hcorder, add_zero]

/-- Analyticity of the normalized positive-power branch expression. -/
theorem normalizedCayleyBranch_analyticAt (a z : ℍ) (r : ℝ) (hr : r ≠ 0) (m : ℕ) :
    AnalyticAt ℂ (normalizedCayleyBranch a r m ∘ ofComplex) (z : ℂ) :=
  (normalizedCayley_analyticAt a z r hr).pow m

/-- The normalized branch has exact order `m`, including the case `m = 0`. -/
theorem normalizedCayleyBranch_order_center (a : ℍ) (r : ℝ) (hr : r ≠ 0) (m : ℕ) :
    analyticOrderAt (normalizedCayleyBranch a r m ∘ ofComplex) (a : ℂ) = (m : ℕ∞) := by
  change analyticOrderAt ((normalizedCayley a r ∘ ofComplex) ^ m) (a : ℂ) = _
  rw [analyticOrderAt_pow (normalizedCayley_analyticAt a a r hr),
    normalizedCayley_order_center a r hr]
  simp

/-- The genuine quotient-coordinate germ equals the normalized branch
germ on an actual open complex neighbourhood of its center. -/
theorem ellipticFullChart_complexGerm_eventuallyEq (j : Elliptic.Kind) :
    (ellipticFullChart j ∘ triangleOrbitProjection ∘ ofComplex) =ᶠ[𝓝 (ellipticCenter j : ℂ)]
      (normalizedCayleyBranch (ellipticCenter j) (ellipticNeighborhoodRadius j) j.order ∘
        ofComplex) := by
  have hU : IsOpen (UpperHalfPlane.coe '' (ellipticNeighborhood j : Set ℍ)) :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ (ellipticNeighborhood j).isOpen
  have hcenter : (ellipticCenter j : ℂ) ∈
      UpperHalfPlane.coe '' (ellipticNeighborhood j : Set ℍ) :=
    ⟨ellipticCenter j, ellipticCenter_mem_neighborhood j, rfl⟩
  filter_upwards [hU.mem_nhds hcenter] with z hz
  obtain ⟨w, hw, rfl⟩ := hz
  simp only [Function.comp_apply, ofComplex_apply]
  exact ellipticFullChart_projection j ⟨w, hw⟩

/-- Analyticity of the actual quotient coordinate pulled back to the
ambient complex germ at the elliptic center. -/
theorem ellipticFullChart_complexGerm_analyticAt (j : Elliptic.Kind) :
    AnalyticAt ℂ (ellipticFullChart j ∘ triangleOrbitProjection ∘ ofComplex)
      (ellipticCenter j : ℂ) :=
  (normalizedCayleyBranch_analyticAt (ellipticCenter j) (ellipticCenter j)
    (ellipticNeighborhoodRadius j) (ellipticNeighborhoodRadius_pos j).ne' j.order).congr
      (ellipticFullChart_complexGerm_eventuallyEq j).symm

/-- The exact ramification order of the actual quotient projection in
its actual elliptic quotient coordinate. -/
theorem ellipticFullChart_order_center (j : Elliptic.Kind) :
    analyticOrderAt (ellipticFullChart j ∘ triangleOrbitProjection ∘ ofComplex)
      (ellipticCenter j : ℂ) = (j.order : ℕ∞) := by
  rw [analyticOrderAt_congr (ellipticFullChart_complexGerm_eventuallyEq j)]
  exact normalizedCayleyBranch_order_center (ellipticCenter j)
    (ellipticNeighborhoodRadius j) (ellipticNeighborhoodRadius_pos j).ne' j.order

/-- The first actual elliptic quotient coordinate branches to order three. -/
theorem ellipticFullChart_order_centerOne :
    analyticOrderAt (ellipticFullChart .three ∘ triangleOrbitProjection ∘ ofComplex)
      (centerOne : ℂ) = 3 :=
  ellipticFullChart_order_center .three

/-- The second actual elliptic quotient coordinate branches to order four. -/
theorem ellipticFullChart_order_centerTwo :
    analyticOrderAt (ellipticFullChart .four ∘ triangleOrbitProjection ∘ ofComplex)
      (centerTwo : ℂ) = 4 :=
  ellipticFullChart_order_center .four

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
