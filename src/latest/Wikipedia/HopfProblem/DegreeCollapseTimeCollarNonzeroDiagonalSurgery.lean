import Wikipedia.HopfProblem.DegreeCollapseTimeCollarPositiveCore
import Wikipedia.HopfProblem.DegreeCollapseTimeCollarLinking
import Wikipedia.HopfProblem.DegreeCollapseSevenCollaredMeridianLinking
import Wikipedia.HopfProblem.DegreeCollapseSevenShrunkTwistInvariants

/-!
# A nonzero actual half diagonal gives a strictly decreasing collared surgery

Construct the positive embedded representative, its normalized attaching
product, time data, and full even-twist family. The proved collared
meridian/linking comparison supplies the nonzero character value. The
original integral selection theorem then gives an actual strict decrease,
retaining simple connectivity and zero second and fourth homology.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

open NoExoticSixSphere GLOrthonormalization SevenSurgery
open SingularMayerVietoris SphereHomology
open FramedAttachingProduct UnitSurgery ExteriorTwist

local instance : Fact (Module.finrank ℝ (Vector 7) = 7) := ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M]
  (e : EuclideanEmbedding 7 M) (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)

def HasStrictReduction (t : M → ℝ) (v : Sphere 3) : Prop :=
  ∃ (f : C(Sphere 3, M)) (A : FramedAttachingProduct e a f) (hA : A.radius = 2)
    (T : TimeData A) (_hT : T.time = t) (j : ℤ) (Q : ShrunkEvenTwist A v j),
    Finite (SingularHomology
      (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 3) ∧
    Nat.card (SingularHomology
      (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 3) <
        Nat.card (SingularHomology (NonnegativeHalf t) 3) ∧
    SimplyConnectedSpace
      (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) ∧
    Subsingleton (SingularHomology
      (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 2) ∧
    Subsingleton (SingularHomology
      (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 4)

variable {B : Type} [TopologicalSpace B] {t : M → ℝ} (C : TimeCollar t B)
  [SimplyConnectedSpace M] [Subsingleton (SingularHomology M 2)] [Finite (SingularHomology M 3)]
  [SimplyConnectedSpace (NonnegativeHalf t)]
  [Subsingleton (SingularHomology B 2)] [Subsingleton (SingularHomology B 3)]
  [Subsingleton (SingularHomology B 4)]
  (ht : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ t)
  (hreg : ∀ p, t p = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) t p))

include C ht hreg in
theorem strictReduction_of_positive_core (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f) (hi : Injective f)
    (hdf : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s)) (hpos : ∀ s, 0 < t (f s))
    (v : Sphere 3)
    (hn : IntegralSevenLinking.linking (E := Vector 7) M
      (singularHomologyMap f 3 (unitSphereTopClass 2))
      (singularHomologyMap f 3 (unitSphereTopClass 2)) ≠ 0) :
    HasStrictReduction e a t v := by
  let : Subsingleton (SingularHomology M 4) :=
    IntegralSevenDuality.fourth_homology_subsingleton (E := Vector 7) M
  let : Subsingleton (SingularHomology (NonnegativeHalf t) 2) := C.half_homology_subsingleton 2
  let : Subsingleton (SingularHomology (NonnegativeHalf t) 4) := C.half_homology_subsingleton 4
  let : Finite (SingularHomology (NonnegativeHalf t) 3) := C.half_homology_finite 3
  obtain ⟨R⟩ := EuclideanEmbedding.nonempty_tubularRetraction e a
  obtain ⟨A, hA, T, hT, hfamily⟩ :=
    exists_positive_even_twist_family e a R f hf hi hdf t ht hreg hpos v
  have CT : TimeCollar T.time B := by rw [hT]; exact C
  let : SimplyConnectedSpace (OldPositiveHalf A T) := by
    change SimplyConnectedSpace {p : M // 0 ≤ T.time p}
    rw [hT]
    exact inferInstanceAs (SimplyConnectedSpace (NonnegativeHalf t))
  let : Subsingleton (SingularHomology (OldPositiveHalf A T) 2) := by
    change Subsingleton (SingularHomology {p : M // 0 ≤ T.time p} 2)
    rw [hT]
    exact inferInstanceAs (Subsingleton (SingularHomology (NonnegativeHalf t) 2))
  let : Subsingleton (SingularHomology (OldPositiveHalf A T) 4) := by
    change Subsingleton (SingularHomology {p : M // 0 ≤ T.time p} 4)
    rw [hT]
    exact inferInstanceAs (Subsingleton (SingularHomology (NonnegativeHalf t) 4))
  let : Finite (SingularHomology (OldPositiveHalf A T) 3) := by
    change Finite (SingularHomology {p : M // 0 ≤ T.time p} 3)
    rw [hT]
    exact inferInstanceAs (Finite (SingularHomology (NonnegativeHalf t) 3))
  have hcore : (closedBoundaryPair A hA).attachingSphere = f := by
    apply ContinuousMap.ext
    intro s
    exact A.tube_core s
  have hdiag : IntegralSevenLinking.linking (E := Vector 7) M
      (singularHomologyMap (closedBoundaryPair A hA).attachingSphere 3 (unitSphereTopClass 2))
      (singularHomologyMap (closedBoundaryPair A hA).attachingSphere 3 (unitSphereTopClass 2)) ≠ 0 := by
    rw [hcore]
    exact hn
  have hχ := (collaredMeridianCharacter_core_ne_zero_iff A hA T CT v).2 hdiag
  obtain ⟨j, Q, hfinite, hlt⟩ :=
    exists_strict_shrunk_twist_of_meridianCharacter A hA T v v hfamily hχ
  have hcard : Nat.card (SingularHomology (OldPositiveHalf A T) 3) =
      Nat.card (SingularHomology (NonnegativeHalf t) 3) := by
    change Nat.card (SingularHomology {p : M // 0 ≤ T.time p} 3) = _
    rw [hT]
  have hconn := Q.low_connectivity hA T
  refine ⟨f, A, hA, T, hT, j, Q, hfinite, hlt.trans_eq hcard, hconn.1, hconn.2, ?_⟩
  let := hfinite
  exact Q.fourth_homology_of_finite hA T

include ht hreg in
theorem strictReduction_of_diagonal (c : SingularHomology (NonnegativeHalf t) 3)
    (hc : C.halfLinking (E := Vector 7) c c ≠ 0) (v : Sphere 3) : HasStrictReduction e a t v := by
  let : Subsingleton (SingularHomology (NonnegativeHalf t) 2) := C.half_homology_subsingleton 2
  obtain ⟨f, hf, hi, hdf, hpos, hclass⟩ := C.exists_positive_homology_core e a c
  have hdiag : IntegralSevenLinking.linking (E := Vector 7) M
      (singularHomologyMap f 3 (unitSphereTopClass 2))
      (singularHomologyMap f 3 (unitSphereTopClass 2)) ≠ 0 := by
    rw [hclass]
    exact hc
  exact C.strictReduction_of_positive_core e a ht hreg f hf hi hdf hpos v hdiag

end Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
