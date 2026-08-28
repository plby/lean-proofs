import Wikipedia.NoExoticSixSphere.ClopenFramedConnectivity
import Wikipedia.NoExoticSixSphere.StabilizedQuadraticTransport
import Wikipedia.NoExoticSixSphere.CollaredZeroFramedPath
import Wikipedia.NoExoticSixSphere.CollaredZeroClopenArfVanishing

/-!
# Return native component Arf vanishing along an actual framed surgery comparison

The chosen component is carried to its literal diffeomorphism image in
the final zero fiber. Its complement remains a topological six-sphere.
The constructed restricted framed comparison identifies the original
Arf invariants. Thus the final two-connected-half theorem gives vanishing
for the original component and its original induced normal frame.
Neither whole zero fiber is required to be connected.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.CollaredZero

open GLOrthonormalization EuclideanEmbedding Wikipedia.HopfProblem.DegreeCollapse
open Wikipedia.HopfProblem.SingularMayerVietoris

variable {B : Type} [TopologicalSpace B] (S T : LowCollaredSevenState B)
  [SimplyConnectedSpace T.PositiveHalf] [Subsingleton (SingularHomology T.PositiveHalf 2)]
  (b : B) (F : Comparison S T b)
  (V : TopologicalSpace.Opens S.Zero) (hV : IsClosed (V : Set S.Zero))
  [SimplyConnectedSpace V] (v : V) [Subsingleton (π_ 2 V v)]

include F in
theorem clopenGeometricArf_eq_zero_of_comparison
    (hX : ↥((V : Set S.Zero)ᶜ) ≃ₜ Sphere 6) :
    letI := S.zeroAtlas;
    letI := S.zero_isManifold;
    letI := clopenCompactSpace S V hV;
    let eV := ClopenEmbedding.restrict (embedding S) V hV;
    let aV := ClopenEmbedding.restrictNormalFrame (embedding S) V hV
      (normalFrame S (referencePoint S b));
    ∀ (rV : eV.TubularRetraction), GeometricArf.invariant eV aV rV v = 0 := by
  let := S.zeroAtlas
  let := S.zero_isManifold
  let := T.zeroAtlas
  let := T.zero_isManifold
  let := clopenCompactSpace S V hV
  let G : StabilizedFramedDiffeomorph (embedding S) (normalFrame S (referencePoint S b))
      (embedding T) (normalFrame T (referencePoint T b)) := F
  let W := G.clopenImage V
  have hW : IsClosed (W : Set T.Zero) := G.clopenImage_closed V hV
  let : SimplyConnectedSpace W := G.clopenImage_simplyConnected V
  let w : W := (G.restrictClopen V hV).diffeomorph v
  let : Subsingleton (π_ 2 W w) := G.clopenImage_piTwo_subsingleton V v w
  let : Nonempty W := ⟨w⟩
  let := clopenCompactSpace T W hW
  let eW := ClopenEmbedding.restrict (embedding T) W hW
  let aW := ClopenEmbedding.restrictNormalFrame (embedding T) W hW
    (normalFrame T (referencePoint T b))
  obtain ⟨rW⟩ := eW.nonempty_tubularRetraction aW
  dsimp only
  intro rV
  have hz := clopenGeometricArf_eq_zero_of_compl_sixSphere T W hW
    (referencePoint T b) w ((G.clopenComplementHomeomorph V).trans hX) rW
  exact ((G.restrictClopen V hV).geometricArf_eq rV rW v w).trans hz

end NoExoticSixSphere.CollaredZero
