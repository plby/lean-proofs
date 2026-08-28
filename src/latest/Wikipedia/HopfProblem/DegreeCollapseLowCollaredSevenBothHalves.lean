import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenNegativeHalf
import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenH2Elimination

/-!

# Clear H2 on both original halves by actual native surgery paths

Clear the positive half, reverse the actual time, and clear the new positive
half. The proved opposite-half homeomorphism retains the first cleared group
and both simple-connectivity properties. Compose the native zero-boundary
diffeomorphisms of the two paths with the actual reversal comparison.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState

open NoExoticSixSphere SingularMayerVietoris PeriodTorusHigherHomology

variable {B : Type} [TopologicalSpace B]

theorem exists_h2_zero_both_halves (S : LowCollaredSevenState B)
    [SimplyConnectedSpace S.PositiveHalf] [SimplyConnectedSpace S.NegativeHalf]
    [Subsingleton (SingularHomology B 2)] :
    ∃ U V : LowCollaredSevenState B, S.Reachable U ∧ U.reverse.Reachable V ∧
      SimplyConnectedSpace V.PositiveHalf ∧ SimplyConnectedSpace V.NegativeHalf ∧
      Subsingleton (SingularHomology V.PositiveHalf 2) ∧
      Subsingleton (SingularHomology V.NegativeHalf 2) := by
  obtain ⟨U, hSU, hUSC, hUH2⟩ := S.exists_h2_zero
  let := hUSC
  let := hUH2
  let : SimplyConnectedSpace U.NegativeHalf := hSU.negative_half_simplyConnected
  let : SimplyConnectedSpace U.reverse.PositiveHalf :=
    inferInstanceAs (SimplyConnectedSpace U.NegativeHalf)
  let : SimplyConnectedSpace U.reverse.NegativeHalf :=
    U.reverseNegativeHalfHomeomorph.toHomotopyEquiv.simplyConnectedSpace
  let : Subsingleton (SingularHomology U.reverse.NegativeHalf 2) :=
    (homeomorphHomologyEquiv U.reverseNegativeHalfHomeomorph 2).injective.subsingleton
  obtain ⟨V, hUV, hVSC, hVH2⟩ := U.reverse.exists_h2_zero
  exact ⟨U, V, hSU, hUV, hVSC, hUV.negative_half_simplyConnected,
    hVH2, hUV.negative_half_homology_subsingleton 2⟩

theorem zero_diffeomorphic_after_reversed_path {S U V : LowCollaredSevenState B}
    (hSU : S.Reachable U) (hUV : U.reverse.Reachable V) :
    letI := S.zeroAtlas
    letI := V.zeroAtlas
    Nonempty (S.Zero ≃ₘ⟮𝓡 6, 𝓡 6⟯ V.Zero) := by
  let := S.zeroAtlas
  let := U.zeroAtlas
  let := U.reverse.zeroAtlas
  let := V.zeroAtlas
  obtain ⟨D⟩ := hSU.zero_diffeomorphic
  obtain ⟨E⟩ := hUV.zero_diffeomorphic
  exact ⟨D.trans (U.reverseZeroDiffeomorph.trans E)⟩

end Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState
