import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenReversal
import Wikipedia.HopfProblem.DegreeCollapseLowSurgeryNegativeHalf

/-!

# Finite native low-surgery paths preserve the original opposite half

Each step uses the actual retained-negative-half homeomorphism. Equality of
the original time functions gives only the literal source-subtype comparison.
Finite path induction composes these maps, so simple connectivity and all
vanishing homology groups of the opposite half persist through the path.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState

open NoExoticSixSphere GLOrthonormalization LowSurgery
open FramedAttachingProduct NativeSurgery SingularMayerVietoris PeriodTorusHigherHomology

variable {B : Type} [TopologicalSpace B] (S : LowCollaredSevenState B)

def performNegativeHalfHomeomorph {d : ℕ} {f : NoExoticSixSphere.Sphere d → S.Space}
    (A : FramedAttachingProduct S.embedding S.normalFrame f) (hA : A.radius = 2)
    (T : TimeData A) (hT : T.time = S.time) :
    S.NegativeHalf ≃ₜ (S.perform A hA T hT).NegativeHalf := by
  let E : S.NegativeHalf ≃ₜ TimeCollar.NonnegativeHalf (fun p ↦ -T.time p) :=
    Homeomorph.setCongr (by rw [hT])
  exact E.trans (negativeHalfHomeomorph A hA T)

theorem Step.negative_half_homeomorphic {S U : LowCollaredSevenState B} (h : S.Step U) :
    Nonempty (S.NegativeHalf ≃ₜ U.NegativeHalf) := by
  obtain ⟨d, _, _, f, A, hA, T, hT, rfl⟩ := h
  exact ⟨S.performNegativeHalfHomeomorph A hA T hT⟩

theorem Reachable.negative_half_homeomorphic {S U : LowCollaredSevenState B}
    (h : S.Reachable U) : Nonempty (S.NegativeHalf ≃ₜ U.NegativeHalf) := by
  induction h with
  | refl => exact ⟨Homeomorph.refl S.NegativeHalf⟩
  | @tail U V hSU hUV ih =>
    obtain ⟨E⟩ := ih
    obtain ⟨F⟩ := hUV.negative_half_homeomorphic
    exact ⟨E.trans F⟩

theorem Reachable.negative_half_simplyConnected {S U : LowCollaredSevenState B}
    (h : S.Reachable U) [SimplyConnectedSpace S.NegativeHalf] :
    SimplyConnectedSpace U.NegativeHalf := by
  obtain ⟨E⟩ := h.negative_half_homeomorphic
  exact E.symm.toHomotopyEquiv.simplyConnectedSpace

theorem Reachable.negative_half_homology_subsingleton {S U : LowCollaredSevenState B}
    (h : S.Reachable U) (k : ℕ) [Subsingleton (SingularHomology S.NegativeHalf k)] :
    Subsingleton (SingularHomology U.NegativeHalf k) := by
  obtain ⟨E⟩ := h.negative_half_homeomorphic
  exact (homeomorphHomologyEquiv E k).symm.injective.subsingleton

end Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState
