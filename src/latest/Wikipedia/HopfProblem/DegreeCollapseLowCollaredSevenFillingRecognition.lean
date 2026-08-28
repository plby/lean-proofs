import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenPiOneBothHalves
import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenComponent

/-!

# Native sphere recognition from the supplied framed collared filling

Select the actual component meeting the spherical boundary, retaining the
original atlas, embedding, normal frame and collar. Finite native surgery
paths make both halves simply connected. The earlier homology reductions
and smooth disk recognition then apply. The only geometric input is the
supplied framed collared state; no connectivity or homology condition on
its ambient manifold or either half is assumed.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState

open NoExoticSixSphere

variable {B : Type} [TopologicalSpace B]

theorem nonempty_zero_sphere_diffeomorph_of_filling
    (S : LowCollaredSevenState B) (eBoundary : B ≃ₜ Sphere 6) :
    letI := S.zeroAtlas
    Nonempty (S.Zero ≃ₘ⟮𝓡 6, 𝓡 6⟯ Sphere 6) := by
  let : SimplyConnectedSpace B := eBoundary.toHomotopyEquiv.simplyConnectedSpace
  let b : B := Classical.arbitrary _
  let : PathConnectedSpace (S.component b).Space := S.component_pathConnected b
  let := S.zeroAtlas
  let := (S.component b).zeroAtlas
  obtain ⟨F⟩ := (S.component b).nonempty_zero_sphere_diffeomorph_of_connected eBoundary
  exact ⟨(S.componentZeroDiffeomorph b).symm.trans F⟩

end Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState
