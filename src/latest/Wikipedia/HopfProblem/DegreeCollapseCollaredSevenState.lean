import Wikipedia.HopfProblem.DegreeCollapseTimeCollarExceptionalSurgery
import Mathlib.Logic.Relation

/-!
# Native collared seven-manifolds and their actual positive surgery steps

A state retains its original space, topology, smooth atlas, closed
embedding, full normal framing, regular time, and actual collar over a
fixed boundary space. Simple connectivity and zero ambient H2 are kept.
Finite H3 is deliberately not part of a state: an exceptional first
surgery may have a free summand. A step is an actual positive framed
surgery, and reachability is its finite reflexive-transitive closure.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse

open NoExoticSixSphere GLOrthonormalization SevenSurgery
open SingularMayerVietoris FramedAttachingProduct UnitSurgery

structure CollaredSevenState (B : Type) [TopologicalSpace B] where
  Space : Type
  [topology : TopologicalSpace Space]
  [atlas : ChartedSpace (Vector 7) Space]
  [smooth : IsManifold (𝓡 7) ∞ Space]
  [compact : CompactSpace Space]
  [separated : T2Space Space]
  [simplyConnected : SimplyConnectedSpace Space]
  [secondHomology : Subsingleton (SingularHomology Space 2)]
  embedding : EuclideanEmbedding 7 Space
  normalFrame : SmoothRangeFrame (𝓡 7) embedding.normalProjection embedding.NormalModel
  time : Space → ℝ
  time_smooth : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ time
  time_regular : ∀ p, time p = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) time p)
  collar : TimeCollar time B
  [halfSimplyConnected : SimplyConnectedSpace (TimeCollar.NonnegativeHalf time)]

attribute [instance] CollaredSevenState.topology CollaredSevenState.atlas
  CollaredSevenState.smooth CollaredSevenState.compact CollaredSevenState.separated
  CollaredSevenState.simplyConnected CollaredSevenState.secondHomology
  CollaredSevenState.halfSimplyConnected

namespace CollaredSevenState

variable {B : Type} [TopologicalSpace B] (S : CollaredSevenState B)

def ofCollar {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
    [IsManifold (𝓡 7) ∞ M] [CompactSpace M] [T2Space M] [SimplyConnectedSpace M]
    [Subsingleton (SingularHomology M 2)]
    (e : EuclideanEmbedding 7 M) (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
    (t : M → ℝ) (ht : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ t)
    (hreg : ∀ p, t p = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) t p))
    (C : TimeCollar t B) [SimplyConnectedSpace (TimeCollar.NonnegativeHalf t)] :
    CollaredSevenState B where
  Space := M
  topology := inferInstance
  atlas := inferInstance
  smooth := inferInstance
  compact := inferInstance
  separated := inferInstance
  simplyConnected := inferInstance
  secondHomology := inferInstance
  embedding := e
  normalFrame := a
  time := t
  time_smooth := ht
  time_regular := hreg
  collar := C
  halfSimplyConnected := inferInstance

def thirdCard : ℕ := Nat.card (SingularHomology (TimeCollar.NonnegativeHalf S.time) 3)

def perform {f : Sphere 3 → S.Space}
    (A : FramedAttachingProduct S.embedding S.normalFrame f) (hA : A.radius = 2)
    (T : TimeData A) (hT : T.time = S.time) : CollaredSevenState B where
  Space := Target A hA
  topology := inferInstance
  atlas := targetChartedSpace A hA
  smooth := by
    let := targetChartedSpace A hA
    exact target_isManifold A hA
  compact := compactSpace_target A hA
  separated := inferInstance
  simplyConnected := (target_simplyConnected_iff A hA).2 inferInstance
  secondHomology := target_second_homology A hA
  embedding := by
    let := targetChartedSpace A hA
    exact inducedEmbedding A hA
  normalFrame := by
    let := targetChartedSpace A hA
    exact normalFraming A hA
  time := timeFunction A hA T
  time_smooth := by
    let := targetChartedSpace A hA
    exact contMDiff_timeFunction A hA T
  time_regular := by
    let := targetChartedSpace A hA
    exact regular_timeFunction_zero A hA T
  collar := preservedTimeCollar A hA T (by rw [hT]; exact S.collar)
  halfSimplyConnected := by
    let : SimplyConnectedSpace (OldPositiveHalf A T) := by
      change SimplyConnectedSpace {p : S.Space // 0 ≤ T.time p}
      rw [hT]
      exact inferInstanceAs (SimplyConnectedSpace (TimeCollar.NonnegativeHalf S.time))
    exact positiveHalf_simplyConnected A hA T

def Step (U : CollaredSevenState B) : Prop :=
  ∃ (f : Sphere 3 → S.Space)
    (A : FramedAttachingProduct S.embedding S.normalFrame f) (hA : A.radius = 2)
    (T : TimeData A) (hT : T.time = S.time), U = S.perform A hA T hT

abbrev Reachable (U : CollaredSevenState B) : Prop := Relation.ReflTransGen Step S U

theorem step_perform {f : Sphere 3 → S.Space}
    (A : FramedAttachingProduct S.embedding S.normalFrame f) (hA : A.radius = 2)
    (T : TimeData A) (hT : T.time = S.time) : S.Step (S.perform A hA T hT) :=
  ⟨f, A, hA, T, hT, rfl⟩

theorem perform_thirdCard {f : Sphere 3 → S.Space}
    (A : FramedAttachingProduct S.embedding S.normalFrame f) (hA : A.radius = 2)
    (T : TimeData A) (hT : T.time = S.time) :
    (S.perform A hA T hT).thirdCard = Nat.card (SingularHomology (PositiveHalf A hA T) 3) := rfl

theorem perform_finite_third {f : Sphere 3 → S.Space}
    (A : FramedAttachingProduct S.embedding S.normalFrame f) (hA : A.radius = 2)
    (T : TimeData A) (hT : T.time = S.time)
    [Finite (SingularHomology S.Space 3)] [Finite (SingularHomology (PositiveHalf A hA T) 3)] :
    Finite (SingularHomology (S.perform A hA T hT).Space 3) :=
  target_third_finite_of_half A hA T

end CollaredSevenState
end Wikipedia.HopfProblem.DegreeCollapse
