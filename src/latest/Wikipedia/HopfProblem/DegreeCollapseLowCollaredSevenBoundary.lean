import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenState
import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenBoundary
import Wikipedia.HopfProblem.DegreeCollapseLowSurgeryZeroDiffeomorph

/-!

# The native smooth zero boundary is preserved along the actual surgery path

Every state uses its own regular-fiber atlas on its literal zero set.
Equality of time functions identifies the two native source atlases,
and the original surgery zero-fiber diffeomorphism supplies the step.
Finite path induction composes these actual diffeomorphisms; no boundary
atlas is transferred along an arbitrary homeomorphism.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState

open NoExoticSixSphere GLOrthonormalization LowSurgery
open FramedAttachingProduct NativeSurgery RoundedTrace

variable {B : Type} [TopologicalSpace B] (S : LowCollaredSevenState B)

abbrev Zero := {p : S.Space // S.time p = 0}

def zeroTimeMap : C(S.Space, ℝ) := ⟨S.time, S.time_smooth.continuous⟩

@[instance_reducible]
def zeroAtlas : ChartedSpace (Vector 6) S.Zero :=
  regularFiberAtlas S.zeroTimeMap S.time_smooth 0 S.time_regular 6 (by simp)

theorem zero_isManifold : letI := S.zeroAtlas; IsManifold (𝓡 6) ∞ S.Zero :=
  regularFiber_isManifold S.zeroTimeMap S.time_smooth 0 S.time_regular 6 (by simp)

def performZeroDiffeomorph {d : ℕ} {f : NoExoticSixSphere.Sphere d → S.Space}
    (A : FramedAttachingProduct S.embedding S.normalFrame f) (hA : A.radius = 2)
    (T : TimeData A) (hT : T.time = S.time) :
    letI := S.zeroAtlas;
    letI := (S.perform A hA T hT).zeroAtlas;
    S.Zero ≃ₘ⟮𝓡 6, 𝓡 6⟯ (S.perform A hA T hT).Zero := by
  let := S.zeroAtlas
  let := boundaryChartedSpace A
  let := originalZeroAtlas A T
  let := (S.perform A hA T hT).zeroAtlas
  let E : S.Zero ≃ₘ⟮𝓡 6, 𝓡 6⟯ OriginalZero A T :=
    CollaredSevenState.regularZeroCongr S.zeroTimeMap (originalTimeMap A T)
    S.time_smooth T.smooth S.time_regular T.regular
    (ContinuousMap.ext (fun p ↦ (congrFun hT p).symm))
  exact E.trans (zeroDiffeomorph A hA T)

theorem Step.zero_diffeomorphic {S U : LowCollaredSevenState B} (h : S.Step U) :
    letI := S.zeroAtlas;
    letI := U.zeroAtlas;
    Nonempty (S.Zero ≃ₘ⟮𝓡 6, 𝓡 6⟯ U.Zero) := by
  obtain ⟨d, _, _, f, A, hA, T, hT, rfl⟩ := h
  exact ⟨S.performZeroDiffeomorph A hA T hT⟩

theorem Reachable.zero_diffeomorphic {S U : LowCollaredSevenState B} (h : S.Reachable U) :
    letI := S.zeroAtlas;
    letI := U.zeroAtlas;
    Nonempty (S.Zero ≃ₘ⟮𝓡 6, 𝓡 6⟯ U.Zero) := by
  induction h with
  | refl =>
    let := S.zeroAtlas
    exact ⟨Diffeomorph.refl (𝓡 6) S.Zero ∞⟩
  | @tail U V hSU hUV ih =>
    let := S.zeroAtlas
    let := U.zeroAtlas
    let := V.zeroAtlas
    obtain ⟨F⟩ := ih
    obtain ⟨G⟩ := hUV.zero_diffeomorphic
    exact ⟨F.trans G⟩

end Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState

