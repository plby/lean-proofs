import Wikipedia.HopfProblem.DegreeCollapseSurgeryPairHomology
import Wikipedia.HopfProblem.DegreeCollapseEmbeddedHandleConnectivity

/-!
# Connectivity and low homology of the original two surgery ends

Both constructed whole-handle presentations have the same actual body.
Simply connected attaching spheres therefore identify simple connectivity
of the original ends. Vanishing of two consecutive sphere homology groups
makes both original inclusions bijective in the intervening degree and
gives an equivalence retaining their exact comparison in the common body.
-/

noncomputable section

open Function

namespace Wikipedia.HopfProblem.DegreeCollapse.SurgeryPairBody

open Wikipedia.SmoothSixDPoincare PuncturedHandle MorseHandle
open SingularMayerVietoris

variable {E F R X Y : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace R] [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [TopologicalSpace Y] [CompactSpace Y] (d : SurgeryBoundaryPair E F R X Y)

omit [CompactSpace Y] in
theorem body_simplyConnected_iff_old [SimplyConnectedSpace (UnitSphere E)] :
    SimplyConnectedSpace (Space d) ↔ SimplyConnectedSpace X :=
  (oldHandleData d).simplyConnected_iff

theorem body_simplyConnected_iff_new [SimplyConnectedSpace (UnitSphere F)] :
    SimplyConnectedSpace (Space d) ↔ SimplyConnectedSpace Y :=
  (newHandleData d).simplyConnected_iff

include d in
theorem simplyConnected_iff [SimplyConnectedSpace (UnitSphere E)]
    [SimplyConnectedSpace (UnitSphere F)] :
    SimplyConnectedSpace Y ↔ SimplyConnectedSpace X :=
  (body_simplyConnected_iff_new d).symm.trans (body_simplyConnected_iff_old d)

variable (k : ℕ)
  [Subsingleton (SingularHomology (UnitSphere E) k)]
  [Subsingleton (SingularHomology (UnitSphere E) (k + 1))]
  [Subsingleton (SingularHomology (UnitSphere F) k)]
  [Subsingleton (SingularHomology (UnitSphere F) (k + 1))]

def lowHomologyEquiv : SingularHomology X (k + 1) ≃ₗ[ℤ] SingularHomology Y (k + 1) :=
  (LinearEquiv.ofBijective (singularHomologyMap (oldMap d) (k + 1))
    ⟨(oldHandleData d).old_injective (k + 1) (Nat.succ_ne_zero k),
      (oldHandleData d).old_surjective k⟩).trans
    (LinearEquiv.ofBijective (singularHomologyMap (newMap d) (k + 1))
      ⟨(newHandleData d).old_injective (k + 1) (Nat.succ_ne_zero k),
        (newHandleData d).old_surjective k⟩).symm

theorem lowHomologyEquiv_inclusions (x : SingularHomology X (k + 1)) :
    singularHomologyMap (newMap d) (k + 1) (lowHomologyEquiv d k x) =
      singularHomologyMap (oldMap d) (k + 1) x := by
  let e := LinearEquiv.ofBijective (singularHomologyMap (newMap d) (k + 1))
    ⟨(newHandleData d).old_injective (k + 1) (Nat.succ_ne_zero k),
      (newHandleData d).old_surjective k⟩
  exact e.apply_symm_apply (singularHomologyMap (oldMap d) (k + 1) x)

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryPairBody
