import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspCompactification
import Wikipedia.HopfProblem.SpecialPeriodsDiscriminantBounds
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

/-!
# Actual compact descent of triangle-invariant real functions

A continuous invariant function on the original upper half-plane descends
through the actual orbit quotient.  Extend that function by an arbitrary
value at the added cusp.  A limit of `-∞` upstairs transfers to the punctured
cusp, because every point of an actual cusp image has a representative above
the corresponding height cutoff.  Compactness then gives a global upper
bound, without assuming descended data or a quotient parametrization.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Construction

variable (f : ℍ → ℝ)
variable (hinv : ∀ (g : TriangleGroup) (z : ℍ),
  f (triangleGeometricRepresentation g z) = f z)

/-- Descent through the literal triangle-orbit quotient. -/
def orbitDescend : TriangleOrbitSpace → ℝ :=
  Quotient.lift f fun x y hxy => by
    change ∃ g : TriangleGroup, triangleGeometricRepresentation g y = x at hxy
    obtain ⟨g, hg⟩ := hxy
    exact (congrArg f hg).symm.trans (hinv g y)

@[simp] theorem orbitDescend_projection (z : ℍ) :
    orbitDescend f hinv (triangleOrbitProjection z) = f z := rfl

/-- The actual quotient topology makes the descended function continuous. -/
theorem orbitDescend_continuous (hf : Continuous f) :
    Continuous (orbitDescend f hinv) :=
  hf.quotient_lift _

/-- The literal one-point extension, with arbitrary prescribed cusp value. -/
def compactDescend (c : ℝ) : TriangleCompactifiedOrbitSpace → ℝ :=
  OnePoint.rec c (orbitDescend f hinv)

@[simp] theorem compactDescend_cusp (c : ℝ) :
    compactDescend f hinv c triangleCuspPoint = c := rfl

@[simp] theorem compactDescend_openInclusion (c : ℝ) (q : TriangleOrbitSpace) :
    compactDescend f hinv c (triangleOpenInclusion q) = orbitDescend f hinv q := rfl

@[simp] theorem compactDescend_projection (c : ℝ) (z : ℍ) :
    compactDescend f hinv c (triangleOpenInclusion (triangleOrbitProjection z)) = f z := rfl

theorem compactDescend_continuousAt_openInclusion (c : ℝ) (hf : Continuous f)
    (q : TriangleOrbitSpace) :
    ContinuousAt (compactDescend f hinv c) (triangleOpenInclusion q) :=
  OnePoint.continuousAt_coe.mpr (orbitDescend_continuous f hinv hf).continuousAt

/-- No continuity at the arbitrarily assigned cusp value is asserted. -/
theorem compactDescend_continuousOn (c : ℝ) (hf : Continuous f) :
    ContinuousOn (compactDescend f hinv c)
      ({triangleCuspPoint} : Set TriangleCompactifiedOrbitSpace)ᶜ := by
  intro x hx
  induction x using OnePoint.rec with
  | infty => exact (hx rfl).elim
  | coe q =>
      exact (compactDescend_continuousAt_openInclusion f hinv c hf q).continuousWithinAt

/-- Any eventual property of invariant values high in the original upper
half-plane holds on a genuine punctured neighborhood of the added cusp. -/
theorem compactDescend_eventually_of_atImInfty (c : ℝ) (P : ℝ → Prop)
    (hP : ∀ᶠ z in atImInfty, P (f z)) :
    ∀ᶠ x in 𝓝[≠] triangleCuspPoint, P (compactDescend f hinv c x) := by
  obtain ⟨Y, hY⟩ := (UpperHalfPlane.atImInfty_mem _).mp hP
  filter_upwards [nhdsWithin_le_nhds (Triangle.cuspNeighborhood_mem_nhds Y),
    self_mem_nhdsWithin] with x hx hxne
  induction x using OnePoint.rec with
  | infty => exact (hxne rfl).elim
  | coe q =>
      obtain ⟨z, hz, rfl⟩ := (Triangle.mem_cuspImage Y q).mp
        ((Triangle.openInclusion_mem_cuspNeighborhood Y q).mp hx)
      exact hY z hz.le

/-- Negative divergence transfers through the constructed quotient and its
actual cusp neighborhoods; the value assigned at the cusp is irrelevant. -/
theorem compactDescend_tendsto_atBot (c : ℝ)
    (hlim : Tendsto f atImInfty atBot) :
    Tendsto (compactDescend f hinv c) (𝓝[≠] triangleCuspPoint) atBot := by
  refine tendsto_atBot.mpr fun R => ?_
  exact compactDescend_eventually_of_atImInfty f hinv c (fun t => t ≤ R)
    (hlim.eventually_le_atBot R)

end Wikipedia.HopfProblem.SpecialPeriods.Construction

namespace Wikipedia.HopfProblem.SpecialPeriods.Construction

/-- The global upper bound follows from genuine compactification and descent,
not from a compact-base or descended-function hypothesis. -/
theorem bddAbove_range_of_triangle_invariant_tendsto_atBot (f : ℍ → ℝ)
    (hf : Continuous f)
    (hinv : ∀ (g : TriangleGroup) (z : ℍ),
      f (triangleGeometricRepresentation g z) = f z)
    (hlim : Tendsto f atImInfty atBot) : BddAbove (range f) := by
  apply (bddAbove_image_punctured_of_tendsto_atBot triangleCuspPoint
    (compactDescend f hinv 0) (compactDescend_continuousOn f hinv 0 hf)
    (compactDescend_tendsto_atBot f hinv 0 hlim)).mono
  rintro _ ⟨z, rfl⟩
  exact ⟨triangleOpenInclusion (triangleOrbitProjection z),
    triangleOpenInclusion_ne_cusp _, compactDescend_projection f hinv 0 z⟩

end Wikipedia.HopfProblem.SpecialPeriods.Construction
