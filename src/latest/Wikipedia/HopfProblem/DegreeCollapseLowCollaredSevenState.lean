import Wikipedia.HopfProblem.DegreeCollapseLowPositiveAttachingTime
import Wikipedia.HopfProblem.DegreeCollapseLowSurgeryTimeCollar
import Wikipedia.HopfProblem.DegreeCollapseLowInducedEndNormalFraming
import Mathlib.Logic.Relation

/-!

# Native framed collared seven-manifolds before connectivity surgery

These states keep the original manifold atlas, actual closed embedding,
full normal framing, regular time and collar over the fixed boundary.
Neither simple connectivity nor vanishing of H2 is a field. A transition
is a constructed positive one- or two-sphere surgery on the native end.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse

open NoExoticSixSphere GLOrthonormalization LowSurgery
open FramedAttachingProduct NativeSurgery RoundedTrace

structure LowCollaredSevenState (B : Type) [TopologicalSpace B] where
  Space : Type
  [topology : TopologicalSpace Space]
  [atlas : ChartedSpace (Vector 7) Space]
  [smooth : IsManifold (𝓡 7) ∞ Space]
  [compact : CompactSpace Space]
  [separated : T2Space Space]
  embedding : EuclideanEmbedding 7 Space
  normalFrame : SmoothRangeFrame (𝓡 7) embedding.normalProjection embedding.NormalModel
  time : Space → ℝ
  time_smooth : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ time
  time_regular : ∀ p, time p = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) time p)
  collar : TimeCollar time B

attribute [instance] LowCollaredSevenState.topology LowCollaredSevenState.atlas
  LowCollaredSevenState.smooth LowCollaredSevenState.compact LowCollaredSevenState.separated

namespace LowCollaredSevenState

variable {B : Type} [TopologicalSpace B] (S : LowCollaredSevenState B)

def ofCollar {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
    [IsManifold (𝓡 7) ∞ M] [CompactSpace M]
    (e : EuclideanEmbedding 7 M) (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
    (t : M → ℝ) (ht : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ t)
    (hreg : ∀ p, t p = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) t p))
    (C : TimeCollar t B) : LowCollaredSevenState B where
  Space := M
  topology := inferInstance
  atlas := inferInstance
  smooth := inferInstance
  compact := inferInstance
  separated := e.closedEmbedding.isEmbedding.t2Space
  embedding := e
  normalFrame := a
  time := t
  time_smooth := ht
  time_regular := hreg
  collar := C

abbrev PositiveHalf := {p : S.Space // 0 ≤ S.time p}

def perform {d : ℕ} {f : NoExoticSixSphere.Sphere d → S.Space}
    (A : FramedAttachingProduct S.embedding S.normalFrame f) (hA : A.radius = 2)
    (T : TimeData A) (hT : T.time = S.time) : LowCollaredSevenState B where
  Space := otherBoundaryPart A
  topology := inferInstance
  atlas := by
    let := boundaryChartedSpace A
    infer_instance
  smooth := by
    let := boundaryChartedSpace A
    let := boundary_isManifold A
    infer_instance
  compact := compactSpace_otherBoundaryPart A
  separated := inferInstance
  embedding := by
    let := boundaryChartedSpace A
    exact otherBoundaryEuclideanEmbedding A
  normalFrame := by
    let := boundaryChartedSpace A
    exact inducedOtherEndNormalFraming A
  time := timeFunction A hA T
  time_smooth := by
    let := boundaryChartedSpace A
    exact contMDiff_timeFunction A hA T
  time_regular := by
    let := boundaryChartedSpace A
    exact regular_timeFunction_zero A hA T
  collar := preservedTimeCollar A hA T (by rw [hT]; exact S.collar)

def Step (U : LowCollaredSevenState B) : Prop :=
  ∃ d : ℕ, 0 < d ∧ d ≤ 2 ∧
    ∃ (f : NoExoticSixSphere.Sphere d → S.Space)
      (A : FramedAttachingProduct S.embedding S.normalFrame f) (hA : A.radius = 2)
      (T : TimeData A) (hT : T.time = S.time), U = S.perform A hA T hT

abbrev Reachable (U : LowCollaredSevenState B) : Prop := Relation.ReflTransGen Step S U

theorem step_perform {d : ℕ} (hd : 0 < d) (hsmall : d ≤ 2)
    {f : NoExoticSixSphere.Sphere d → S.Space}
    (A : FramedAttachingProduct S.embedding S.normalFrame f) (hA : A.radius = 2)
    (T : TimeData A) (hT : T.time = S.time) : S.Step (S.perform A hA T hT) :=
  ⟨d, hd, hsmall, f, A, hA, T, hT, rfl⟩

theorem exists_step_of_positive_core {d : ℕ} (hd : 0 < d) (hsmall : d ≤ 2)
    (f : C(NoExoticSixSphere.Sphere d, S.Space))
    (hf : ContMDiff (𝓡 d) (𝓡 7) ∞ f) (hi : Injective f)
    (hdf : ∀ s, Injective (mfderiv (𝓡 d) (𝓡 7) f s)) (hpos : ∀ s, 0 < S.time (f s)) :
    ∃ (A : FramedAttachingProduct S.embedding S.normalFrame f) (hA : A.radius = 2)
      (T : TimeData A) (hT : T.time = S.time), S.Step (S.perform A hA T hT) := by
  obtain ⟨A, hA, T, hT⟩ := exists_positive_framed_surgery_timeData hd (hsmall.trans (by decide))
    S.embedding S.normalFrame f hf hi hdf S.time S.time_smooth S.time_regular hpos
  exact ⟨A, hA, T, hT, S.step_perform hd hsmall A hA T hT⟩

end LowCollaredSevenState
end Wikipedia.HopfProblem.DegreeCollapse
