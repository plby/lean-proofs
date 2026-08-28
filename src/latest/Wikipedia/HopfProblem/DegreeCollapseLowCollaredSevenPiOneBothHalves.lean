import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenPiOneElimination
import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenRecognition

/-!

# Kill both original half fundamental groups while retaining the zero atlas

Finite generation is derived from the connected compact native ambient
manifold and the actual collar. After clearing the positive half, the
retained negative-half homeomorphism transports its finite generation.
Reverse time and clear that group. The first simply connected half survives
through the second path by the same retained-half comparison. The existing
H2, H3 and disk-recognition results then apply with no initial connectivity
assumption on either half's fundamental group.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState

open NoExoticSixSphere Wikipedia.SmoothSixDPoincare

variable {B : Type} [TopologicalSpace B]

theorem exists_simplyConnected_both_halves_of_connected (S : LowCollaredSevenState B)
    [PathConnectedSpace S.Space] [SimplyConnectedSpace B] :
    ∃ U V : LowCollaredSevenState B, S.Reachable U ∧ U.reverse.Reachable V ∧
      SimplyConnectedSpace V.PositiveHalf ∧ SimplyConnectedSpace V.NegativeHalf := by
  let : LocallyPathConnectedSpace S.Space :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 7)) S.Space
  let : PathConnectedSpace S.NegativeHalf := S.collar.reverse.half_pathConnected
  have hOld : ∀ x : S.NegativeHalf, Group.FG (FundamentalGroup S.NegativeHalf x) :=
    S.collar.reverse.compact_half_fundamentalGroup_finite (EuclideanSpace ℝ (Fin 7))
  obtain ⟨U, hSU, hU⟩ := S.exists_simplyConnected_of_connected
  let := hU
  obtain ⟨e⟩ := hSU.negative_half_homeomorphic
  let : PathConnectedSpace U.reverse.PositiveHalf :=
    FundamentalGroupTools.pathConnected_of_homotopyEquiv e.toHomotopyEquiv.symm
  let b : B := Classical.arbitrary _
  let : Group.FG (FundamentalGroup U.reverse.PositiveHalf (U.reverse.positiveBasepoint b)) :=
    FundamentalGroupFiniteness.of_homotopyEquiv e.toHomotopyEquiv hOld _
  let : SimplyConnectedSpace U.reverse.NegativeHalf :=
    U.reverseNegativeHalfHomeomorph.toHomotopyEquiv.simplyConnectedSpace
  obtain ⟨V, hUV, hV⟩ := U.reverse.exists_simplyConnected_of_finitelyGenerated b
  exact ⟨U, V, hSU, hUV, hV, hUV.negative_half_simplyConnected⟩

theorem nonempty_zero_sphere_diffeomorph_of_connected
    (S : LowCollaredSevenState B) (eBoundary : B ≃ₜ Sphere 6)
    [PathConnectedSpace S.Space] :
    letI := S.zeroAtlas
    Nonempty (S.Zero ≃ₘ⟮𝓡 6, 𝓡 6⟯ Sphere 6) := by
  let : SimplyConnectedSpace B := eBoundary.toHomotopyEquiv.simplyConnectedSpace
  obtain ⟨U, V, hSU, hUV, hVP, hVN⟩ := S.exists_simplyConnected_both_halves_of_connected
  let := hVP
  let := hVN
  let := S.zeroAtlas
  let := V.zeroAtlas
  obtain ⟨D⟩ := zero_diffeomorphic_after_reversed_path hSU hUV
  obtain ⟨F⟩ := V.nonempty_zero_sphere_diffeomorph eBoundary
  exact ⟨D.trans F⟩

end Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState
