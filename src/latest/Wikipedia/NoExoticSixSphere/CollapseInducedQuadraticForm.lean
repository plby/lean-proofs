import Wikipedia.NoExoticSixSphere.PositiveNormalFrameHomotopy
import Wikipedia.NoExoticSixSphere.CollapseInducedFrame
import Wikipedia.NoExoticSixSphere.NormalizedFramedCollapseData
import Wikipedia.NoExoticSixSphere.OrthonormalRangeFrame

/-!
# The actual collapse differential induces the prescribed quadratic form

Construct the smooth normal frame from the canonical orthogonal right
inverse of the original collapse-coordinate differential. The proved
differential identity identifies this actual frame with the prescribed
one times the positive tube radius. The explicit normal-frame homotopy
therefore identifies their geometric quadratic forms and Arf invariants.
For radius-normalized collapse data the two normal frames are equal.

No homotopy or bordism classification of collapse maps is inferred here.
-/

noncomputable section

open Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData

open GLOrthonormalization

section Frame

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (Vector n) M]
  {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel}
  (d : e.FramedCollapseData a)

def coordinateNormalOperator (x : M) : e.NormalModel →L[ℝ] Vector e.ambientDimension :=
  orthogonalRightInverse (fderiv ℝ d.coordinates (e.toFun x))

theorem coordinateNormalOperator_eq (x : M) :
    d.coordinateNormalOperator x = d.radius • a.ambient x :=
  d.orthogonalRightInverse_coordinates x

theorem contMDiff_coordinateNormalOperator :
    ContMDiff (𝓡 n) 𝓘(ℝ, e.NormalModel →L[ℝ] Vector e.ambientDimension) ∞
      d.coordinateNormalOperator := by
  have h : d.coordinateNormalOperator = fun x ↦ d.radius • a.ambient x :=
    funext d.coordinateNormalOperator_eq
  rw [h]
  have hc : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun _ : M ↦ d.radius) := contMDiff_const
  exact hc.smul a.contMDiff_ambient

theorem coordinateNormalOperator_injective (x : M) :
    Injective (d.coordinateNormalOperator x) :=
  orthogonalRightInverse_injective _ (d.surjective_differential _ (d.range_subset ⟨x, rfl⟩))

theorem coordinateNormalOperator_range (x : M) :
    (d.coordinateNormalOperator x).range = (e.normalProjection x).range := by
  rw [coordinateNormalOperator, range_orthogonalRightInverse _
    (d.surjective_differential _ (d.range_subset ⟨x, rfl⟩)),
    d.kernel_eq_tangentImage, e.range_normalProjection]
  rfl

def coordinateInducedNormalFrame : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel :=
  SmoothRangeFrame.ofOperator d.coordinateNormalOperator d.contMDiff_coordinateNormalOperator
    d.coordinateNormalOperator_injective d.coordinateNormalOperator_range

theorem coordinateInducedNormalFrame_ambient (x : M) :
    d.coordinateInducedNormalFrame.ambient x = d.coordinateNormalOperator x :=
  SmoothRangeFrame.ofOperator_ambient _ _ _ _ x

theorem coordinateInducedNormalFrame_eq_radius (x : M) :
    d.coordinateInducedNormalFrame.ambient x = d.radius • a.ambient x :=
  (d.coordinateInducedNormalFrame_ambient x).trans (d.coordinateNormalOperator_eq x)

theorem coordinateInducedNormalFrame_eq_of_radius_one (hr : d.radius = 1) :
    d.coordinateInducedNormalFrame = a := by
  apply SmoothRangeFrame.eq_of_ambient_eq
  intro x
  rw [d.coordinateInducedNormalFrame_eq_radius, hr, one_smul]

theorem normalized_coordinateInducedNormalFrame : d.normalized.coordinateInducedNormalFrame = a :=
  d.normalized.coordinateInducedNormalFrame_eq_of_radius_one d.normalized_radius

end Frame

open Wikipedia.HopfProblem SphereHomologyCoefficients

attribute [local instance] modHomologyModule

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [SimplyConnectedSpace M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel}
  (d : e.FramedCollapseData a) (r r' : TubularRetraction e) (m m' : M)
  [Subsingleton (π_ 2 M m)] [Subsingleton (π_ 2 M m')]

theorem modTwoHomologyQuadraticForm_coordinateInduced :
    e.modTwoHomologyQuadraticForm a r m =
      e.modTwoHomologyQuadraticForm d.coordinateInducedNormalFrame r' m' :=
  e.modTwoHomologyQuadraticForm_eq_of_normal_family a d.coordinateInducedNormalFrame r r' m m'
    (e.positiveNormalFamily a (fun _ ↦ d.radius) continuous_const)
    (e.positiveNormalFamily_injective a _ continuous_const (fun _ ↦ d.radius_pos))
    (e.positiveNormalFamily_range a _ continuous_const)
    (e.positiveNormalFamily_zero a _ continuous_const)
    (fun x ↦ (e.positiveNormalFamily_one a _ continuous_const x).trans
      (d.coordinateInducedNormalFrame_eq_radius x).symm)

theorem geometricArf_coordinateInduced :
    GeometricArf.invariant e a r m =
      GeometricArf.invariant e d.coordinateInducedNormalFrame r' m' :=
  GeometricArf.invariant_eq_of_quadraticForm_eq e a d.coordinateInducedNormalFrame r r' m m'
    (d.modTwoHomologyQuadraticForm_coordinateInduced r r' m m')

end NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData
