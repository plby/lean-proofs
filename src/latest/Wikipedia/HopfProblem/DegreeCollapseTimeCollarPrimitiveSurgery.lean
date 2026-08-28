import Wikipedia.HopfProblem.DegreeCollapseTimeCollarPositiveCore
import Wikipedia.HopfProblem.DegreeCollapseSevenPrimitiveQuotient
import Wikipedia.HopfProblem.DegreeCollapseSevenCollaredFiniteHomology
import Wikipedia.HopfProblem.DegreeCollapseSevenShrunkEvenTwists

/-!
# Construct the actual collared surgery for a primitive free class

The positive embedded representative, normalized attaching product, and
regular time data are all constructed from the original primitive class.
The actual quotient theorem removes its free summand. The unchanged
negative half recovers finite ambient H3 and zero new-half H4, without
requiring finite old ambient H3 or zero old-half H4.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

open NoExoticSixSphere GLOrthonormalization SevenSurgery
open SingularMayerVietoris SphereHomology
open FramedAttachingProduct UnitSurgery ExteriorTwist

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M]
  (e : EuclideanEmbedding 7 M) (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)

def HasPrimitiveReduction (t : M → ℝ) (N : ℕ) : Prop :=
  ∃ (f : C(Sphere 3, M)) (A : FramedAttachingProduct e a f) (hA : A.radius = 2)
    (T : TimeData A) (_hT : T.time = t),
    Finite (SingularHomology (PositiveHalf A hA T) 3) ∧
    Nat.card (SingularHomology (PositiveHalf A hA T) 3) = N ∧
    (∀ x : SingularHomology (PositiveHalf A hA T) 3, (2 : ℤ) • x = 0) ∧
    SimplyConnectedSpace (PositiveHalf A hA T) ∧
    Subsingleton (SingularHomology (PositiveHalf A hA T) 2) ∧
    Subsingleton (SingularHomology (PositiveHalf A hA T) 4) ∧
    Finite (SingularHomology (Target A hA) 3)

variable {B : Type} [TopologicalSpace B] {t : M → ℝ} (C : TimeCollar t B)
  [SimplyConnectedSpace M] [Subsingleton (SingularHomology M 2)]
  [SimplyConnectedSpace (NonnegativeHalf t)]
  [Subsingleton (SingularHomology B 2)] [Subsingleton (SingularHomology B 3)]
  [Subsingleton (SingularHomology B 4)]
  [Finite (SingularHomology (NonnegativeHalf (fun p ↦ -t p)) 3)]
  (ht : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ t)
  (hreg : ∀ p, t p = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) t p))

include C ht hreg in
theorem primitiveReduction_of_coordinate
    (σ : SingularHomology (NonnegativeHalf t) 3 →+ ℤ) [Finite σ.ker]
    (c : SingularHomology (NonnegativeHalf t) 3) (hc : σ c = 1)
    (h2 : ∀ x : σ.ker, (2 : ℤ) • x = 0) :
    HasPrimitiveReduction e a t (Nat.card σ.ker) := by
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
  let : Finite σL.toAddMonoidHom.ker := inferInstanceAs (Finite σ.ker)
  let : Finite (SingularHomology (PositiveHalf A hA T) 3) :=
    primitive_new_third_finite A hA T C σL hσL
  refine ⟨f, A, hA, T, rfl, inferInstance,
    primitive_new_third_card A hA T C σL hσL,
    primitive_new_third_two A hA T C σL hσL h2,
    positiveHalf_simplyConnected A hA T, positiveHalf_second_homology A hA T,
    positiveHalf_fourth_homology_of_collared_halves A hA T C,
    target_homology_finite_of_collared_halves A hA T C 2⟩

end Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
