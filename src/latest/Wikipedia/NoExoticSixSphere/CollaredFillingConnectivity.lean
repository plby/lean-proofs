import Wikipedia.NoExoticSixSphere.CollaredFramedConnectivity
import Wikipedia.NoExoticSixSphere.CollaredFillingFramedComparison
import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenComponent
import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenPromotion
import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenFilling

/-!
# Constructed two-connected framed fillings with general two-connected boundary

The input is an actual compact framed collared seven-manifold. Its boundary
need only be simply connected with zero second integral homology: neither
spherical boundary nor zero middle boundary homology is required. Select
the actual boundary component, perform the constructed finite low-surgery
paths on both halves, and retain the original native zero-boundary atlas.

The resulting positive half is genuinely normally framed and two-connected.
The complete induced zero-frame comparison now reaches its literal native
boundary and agrees there with its actual seven-frame and outward normal.
An independently prescribed external boundary frame is not identified here,
and middle torsion is not removed.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.CollaredFillingConnectivity

open GLOrthonormalization Wikipedia.HopfProblem
open DegreeCollapse SingularMayerVietoris

variable {B : Type} [TopologicalSpace B] [SimplyConnectedSpace B]
  [Subsingleton (SingularHomology B 2)]

theorem exists_twoConnected_framed_state (S : LowCollaredSevenState B) (b : B) :
    ∃ U : CollaredSevenState B,
      Subsingleton (SingularHomology U.Half 2) ∧
      (∀ w : U.Half, Subsingleton (π_ 2 U.Half w)) ∧
      Nonempty (CollaredFillingBoundary.Comparison S U b) := by
  let : Subsingleton (SingularHomology B 1) :=
    CollaredFramedConnectivity.firstHomology_subsingleton b
  obtain ⟨V, hVP, hVN, hVP2, hVN2, hpi, hF⟩ :=
    CollaredFramedConnectivity.exists_twoConnected_state S b
  let := hVP
  let := hVN
  let := hVP2
  let := hVN2
  let U := V.toCollaredSevenState
  let : Subsingleton (SingularHomology U.Half 2) := hVP2
  refine ⟨U, hVP2, hpi, ?_⟩
  let := S.zeroAtlas
  let := V.zeroAtlas
  let := U.halfBoundaryAtlas
  obtain ⟨F⟩ := hF
  exact ⟨F.trans (CollaredFillingBoundary.promotionComparison V b)⟩

theorem exists_twoConnected_state (S : LowCollaredSevenState B) :
    ∃ U : CollaredSevenState B,
      Subsingleton (SingularHomology U.Half 2) ∧
      (∀ w : U.Half, Subsingleton (π_ 2 U.Half w)) ∧
      letI := S.zeroAtlas; letI := U.zeroAtlas;
        Nonempty (S.Zero ≃ₘ⟮𝓡 6, 𝓡 6⟯ U.Zero) := by
  obtain ⟨U, hH, hpi, hF⟩ := exists_twoConnected_framed_state S (Classical.arbitrary B)
  refine ⟨U, hH, hpi, ?_⟩
  let := S.zeroAtlas
  let := U.zeroAtlas
  let := U.halfBoundaryAtlas
  obtain ⟨F⟩ := hF
  exact ⟨F.diffeomorph.trans U.halfBoundaryDiffeomorph⟩

theorem exists_twoConnected_filling (S : LowCollaredSevenState B) :
    letI := S.zeroAtlas;
    ∃ F : FramedSevenFilling.{0, 0, 0, 0} (𝓡 6) S.Zero,
      letI := F.topology;
      SimplyConnectedSpace F.W ∧ ∀ w : F.W, Subsingleton (π_ 2 F.W w) := by
  let := S.zeroAtlas
  obtain ⟨U, _, hpi, hF⟩ := exists_twoConnected_framed_state S (Classical.arbitrary B)
  obtain ⟨F⟩ := hF
  refine ⟨CollaredFillingBoundary.fillingOfComparison F, ?_, hpi⟩
  change SimplyConnectedSpace U.Half
  infer_instance

theorem exists_twoConnected_framed_filling (S : LowCollaredSevenState B) (b : B) :
    ∃ U : CollaredSevenState B, ∃ F : CollaredFillingBoundary.Comparison S U b,
      letI := S.zeroAtlas;
      let W := CollaredFillingBoundary.fillingOfComparison F;
      letI := W.topology;
      SimplyConnectedSpace W.W ∧ ∀ w : W.W, Subsingleton (π_ 2 W.W w) := by
  obtain ⟨U, _, hpi, hF⟩ := exists_twoConnected_framed_state S b
  obtain ⟨F⟩ := hF
  refine ⟨U, F, ?_, hpi⟩
  change SimplyConnectedSpace U.Half
  infer_instance

end NoExoticSixSphere.CollaredFillingConnectivity
