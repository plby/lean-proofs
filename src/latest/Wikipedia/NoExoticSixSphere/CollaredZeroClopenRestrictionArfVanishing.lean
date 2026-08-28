import Wikipedia.NoExoticSixSphere.CollaredZeroClopenRestrictionIdentification
import Wikipedia.NoExoticSixSphere.CollaredZeroLowSurgeryArf
import Wikipedia.NoExoticSixSphere.CollaredZeroClopenLowSurgeryArf
import Wikipedia.NoExoticSixSphere.IteratedSphereSuspensionArf

/-!
# Return boundary Arf vanishing from an actual clopen state restriction

If the restricted state retains just the selected two-connected boundary,
the whole-boundary theorem applies. If it retains the whole original
boundary, the clopen-boundary theorem applies when its positive half is
path connected and the complementary boundary is a topological six-sphere.
Both conclusions concern the original embedding and original induced frame.
-/

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.CollaredZero.ClopenRestriction

open GLOrthonormalization EuclideanEmbedding Wikipedia.HopfProblem.DegreeCollapse

variable {B : Type} [TopologicalSpace B] (S : LowCollaredSevenState B)
  (U : Opens S.Space) (hU : IsClosed (U : Set S.Space))
  (V : Opens S.Zero) (hV : IsClosed (V : Set S.Zero)) [SimplyConnectedSpace V]
  (m : S.Space) (m' : (S.restrictClopen U hU).Space)
  (v : V) [Subsingleton (π_ 2 V v)]

include m'

theorem clopenGeometricArf_eq_zero_of_zeroOpen_eq (h : S.zeroOpen U = V) :
    letI := S.zeroAtlas; letI := S.zero_isManifold;
    letI := clopenCompactSpace S V hV;
    let eV := ClopenEmbedding.restrict (embedding S) V hV;
    let aV := ClopenEmbedding.restrictNormalFrame (embedding S) V hV (normalFrame S m);
    ∀ rV : eV.TubularRetraction, GeometricArf.invariant eV aV rV v = 0 := by
  let := S.zeroAtlas
  let := S.zero_isManifold
  let := clopenCompactSpace S V hV
  let T := S.restrictClopen U hU
  let := T.zeroAtlas
  let := T.zero_isManifold
  let := zeroCompactSpace T
  let F := comparisonOfZeroOpenEq S U hU m m' V hV h
  let : SimplyConnectedSpace T.Zero :=
    F.diffeomorph.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace
  let z : T.Zero := F.diffeomorph.symm v
  let : Subsingleton (π_ 2 T.Zero z) :=
    SphereMapSuspension.piTwo_subsingleton_of_homeomorph F.diffeomorph.symm.toHomeomorph v z
  let : Nonempty T.Zero := ⟨z⟩
  obtain ⟨rT⟩ := (embedding T).nonempty_tubularRetraction (normalFrame T m')
  dsimp only
  intro rV
  exact (F.geometricArf_eq rT rV z v).symm.trans
    (geometricArf_eq_zero_of_twoConnected_boundary T m' z rT)

theorem clopenGeometricArf_eq_zero_of_full_restriction
    [hhalf : PathConnectedSpace (S.restrictClopen U hU).PositiveHalf]
    (hfull : S.zeroOpen U = ⊤) (hX : ↥((V : Set S.Zero)ᶜ) ≃ₜ Sphere 6) :
    letI := S.zeroAtlas; letI := S.zero_isManifold;
    letI := clopenCompactSpace S V hV;
    let eV := ClopenEmbedding.restrict (embedding S) V hV;
    let aV := ClopenEmbedding.restrictNormalFrame (embedding S) V hV (normalFrame S m);
    ∀ rV : eV.TubularRetraction, GeometricArf.invariant eV aV rV v = 0 := by
  let := S.zeroAtlas
  let := S.zero_isManifold
  let := clopenCompactSpace S V hV
  let T := S.restrictClopen U hU
  let := T.zeroAtlas
  let := T.zero_isManifold
  let F := comparisonOfFullSymm S U hU m m' hfull
  let W := F.clopenImage V
  have hW : IsClosed (W : Set T.Zero) := F.clopenImage_closed V hV
  let : SimplyConnectedSpace W := F.clopenImage_simplyConnected V
  let w : W := (F.restrictClopen V hV).diffeomorph v
  let : Subsingleton (π_ 2 W w) := F.clopenImage_piTwo_subsingleton V v w
  let : Nonempty W := ⟨w⟩
  let := clopenCompactSpace T W hW
  let eW := ClopenEmbedding.restrict (embedding T) W hW
  let aW := ClopenEmbedding.restrictNormalFrame (embedding T) W hW (normalFrame T m')
  obtain ⟨rW⟩ := eW.nonempty_tubularRetraction aW
  dsimp only
  intro rV
  exact ((F.restrictClopen V hV).geometricArf_eq rV rW v w).trans
    (clopenGeometricArf_eq_zero_of_half_pathConnected T W hW m' w
      ((F.clopenComplementHomeomorph V).trans hX) rW)

end NoExoticSixSphere.CollaredZero.ClopenRestriction
