import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenState
import Wikipedia.HopfProblem.DegreeCollapseCompactHomologyFinite

/-!

# A primitive free coordinate admits an actual collared surgery without finiteness

Construct the embedded positive representative, the normalized framed
attaching product and its time data. The original exterior quotient
identifies the new positive-half third homology with the coordinate's
kernel. Neither that kernel nor the negative half is assumed finite.
The result is an actual state step, retaining its original boundary.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse

open NoExoticSixSphere GLOrthonormalization SevenSurgery
open SingularMayerVietoris SphereHomology
open FramedAttachingProduct UnitSurgery ExteriorTwist

namespace TimeCollar

variable {M B : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [CompactSpace M] [IsManifold (𝓡 7) ∞ M] [T2Space M] [TopologicalSpace B]
  [SimplyConnectedSpace M] [Subsingleton (SingularHomology M 2)]
  (e : EuclideanEmbedding 7 M) (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  {t : M → ℝ} (C : TimeCollar t B) [SimplyConnectedSpace (NonnegativeHalf t)]
  [Subsingleton (SingularHomology B 2)] [Subsingleton (SingularHomology B 3)]
  [Subsingleton (SingularHomology B 4)]

include C in
theorem exists_primitive_surgery_quotient
    (ht : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ t)
    (hreg : ∀ p, t p = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) t p))
    (σ : SingularHomology (NonnegativeHalf t) 3 →+ ℤ)
    (c : SingularHomology (NonnegativeHalf t) 3) (hc : σ c = 1) :
    ∃ (f : C(Sphere 3, M)) (A : FramedAttachingProduct e a f) (hA : A.radius = 2)
      (T : TimeData A), T.time = t ∧
      Nonempty (SingularHomology (PositiveHalf A hA T) 3 ≃+ σ.ker) := by
  let : Subsingleton (SingularHomology (NonnegativeHalf t) 2) :=
    C.half_homology_subsingleton 2
  obtain ⟨f, hf, hi, hdf, hpos, hclass⟩ := C.exists_positive_homology_core e a c
  obtain ⟨R⟩ := EuclideanEmbedding.nonempty_tubularRetraction e a
  obtain ⟨A, hA, T, hT, _⟩ := exists_positive_even_twist_family
    e a R f hf hi hdf t ht hreg hpos (spherePole 3)
  subst t
  have hcore : (closedBoundaryPair A hA).attachingSphere = f := by
    apply ContinuousMap.ext
    intro s
    exact A.tube_core s
  have hc' : singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3
      (unitSphereTopClass 2) = c := by
    apply C.halfInclusion_homology_injective 3
    change singularHomologyMap (halfToClosed A T) 3
      (singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3 (unitSphereTopClass 2)) = _
    rw [halfToClosed_attachingClass, hcore]
    exact hclass
  let σL : SingularHomology (OldPositiveHalf A T) 3 →ₗ[ℤ] ℤ :=
    ConstantSheafSingularComparison.addHomToIntLinearMap σ
  have hσL : σL (singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3
      (unitSphereTopClass 2)) = 1 := by
    change σ _ = 1
    rw [hc', hc]
  exact ⟨f, A, hA, T, rfl, ⟨primitiveThirdHomologyEquiv A hA T C σL hσL⟩⟩

end TimeCollar

namespace CollaredSevenState

variable {B : Type} [TopologicalSpace B] (S : CollaredSevenState B)

theorem half_third_homology_finitely_generated [Subsingleton (SingularHomology B 3)] :
    Module.Finite ℤ (SingularHomology (TimeCollar.NonnegativeHalf S.time) 3) := by
  let : Module.Finite ℤ (SingularHomology S.Space 3) :=
    MorseFiniteness.compactManifold_middleHomology_finite (Vector 7) S.Space
  exact Module.Finite.of_injective (singularHomologyMap (TimeCollar.halfInclusion S.time) 3)
    (S.collar.halfInclusion_homology_injective 3)

theorem successor_of_primitive_coordinate
    [Subsingleton (SingularHomology B 2)] [Subsingleton (SingularHomology B 3)]
    [Subsingleton (SingularHomology B 4)]
    (σ : SingularHomology (TimeCollar.NonnegativeHalf S.time) 3 →+ ℤ)
    (c : SingularHomology (TimeCollar.NonnegativeHalf S.time) 3) (hc : σ c = 1) :
    ∃ U : CollaredSevenState B, S.Step U ∧
      Nonempty (SingularHomology (TimeCollar.NonnegativeHalf U.time) 3 ≃+ σ.ker) := by
  obtain ⟨f, A, hA, T, hT, hE⟩ := S.collar.exists_primitive_surgery_quotient
    S.embedding S.normalFrame S.time_smooth S.time_regular σ c hc
  exact ⟨S.perform A hA T hT, S.step_perform A hA T hT, hE⟩

end CollaredSevenState

end Wikipedia.HopfProblem.DegreeCollapse
