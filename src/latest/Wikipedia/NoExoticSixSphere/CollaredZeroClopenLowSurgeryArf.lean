import Wikipedia.NoExoticSixSphere.CollaredZeroClopenArfTransport
import Wikipedia.NoExoticSixSphere.LowCollaredFillingConnectivity
import Wikipedia.HopfProblem.DegreeCollapseTimeCollarZero

/-!
# Native low surgery proves original component Arf vanishing

The initial positive half is only assumed path connected. Its original
boundary has a two-connected clopen component and a topological six-sphere
complement. These data imply the boundary second-homology input to the
constructed low surgeries. The surgeries produce a two-connected positive
half and an actual full zero-frame comparison. Restricting that comparison
returns Arf vanishing to the original component and original frame.

No initial simple connectivity, vanishing half second homology, surgery
sequence, or stabilized framed comparison is assumed. Path connectedness
of the initial positive half is still an explicit hypothesis.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.CollaredZero

open GLOrthonormalization EuclideanEmbedding Wikipedia.HopfProblem.DegreeCollapse
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {B : Type} [TopologicalSpace B] (S : LowCollaredSevenState B)
  [hhalf : PathConnectedSpace S.PositiveHalf]
  (V : TopologicalSpace.Opens S.Zero) (hV : IsClosed (V : Set S.Zero))
  [SimplyConnectedSpace V] (m : S.Space) (v : V) [Subsingleton (π_ 2 V v)]

include hhalf in
theorem clopenGeometricArf_eq_zero_of_half_pathConnected
    (hX : ↥((V : Set S.Zero)ᶜ) ≃ₜ Sphere 6) :
    letI := S.zeroAtlas;
    letI := S.zero_isManifold;
    letI := clopenCompactSpace S V hV;
    let eV := ClopenEmbedding.restrict (embedding S) V hV;
    let aV := ClopenEmbedding.restrictNormalFrame (embedding S) V hV (normalFrame S m);
    ∀ (rV : eV.TubularRetraction), GeometricArf.invariant eV aV rV v = 0 := by
  let : Subsingleton (SingularHomology S.Zero 2) :=
    NativeBoundarySum.secondHomology_subsingleton_of_compl_sixSphere V hV v hX
  let : Subsingleton (SingularHomology B 2) :=
    (homeomorphHomologyEquiv S.collar.zeroHomeomorph 2).symm.injective.subsingleton
  let b : B := S.collar.zeroHomeomorph v.val
  obtain ⟨T, hST, hT, hT2, _, _⟩ :=
    LowCollaredFillingConnectivity.exists_twoConnected_positive_state S b
  let := hT
  let := hT2
  obtain ⟨F⟩ := comparison_of_reachable hST b
  let := S.zeroAtlas
  let := S.zero_isManifold
  let := clopenCompactSpace S V hV
  dsimp only
  intro rV
  rw [normalFrame_point_independent S (referencePoint S b) m]
  exact clopenGeometricArf_eq_zero_of_comparison S T b F V hV v hX rV

end NoExoticSixSphere.CollaredZero
