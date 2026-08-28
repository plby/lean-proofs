import Wikipedia.NoExoticSixSphere.CollaredFramedConnectivity
import Wikipedia.NoExoticSixSphere.CollaredZeroArfVanishing
import Wikipedia.NoExoticSixSphere.StabilizedQuadraticTransport
import Wikipedia.HopfProblem.DegreeCollapseTimeCollarZero

/-!
# A two-connected native collared boundary has zero original geometric Arf invariant

The actual component and finite low-surgery constructions supply a
two-connected half and a full native zero-frame comparison. The proved
Arf transport returns boundary vanishing to the original induced frame.
No initial half connectivity or filling connectivity hypothesis remains.
The whole boundary is assumed two-connected in this result.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.CollaredZero

open GLOrthonormalization EuclideanEmbedding Wikipedia.HopfProblem
open DegreeCollapse SingularMayerVietoris PeriodTorusHigherHomology

variable {B : Type} [TopologicalSpace B] (S : LowCollaredSevenState B)
  [SimplyConnectedSpace S.Zero] (m : S.Space) (z : S.Zero)
  [Subsingleton (π_ 2 S.Zero z)]

theorem geometricArf_eq_zero_of_twoConnected_boundary :
    letI := S.zeroAtlas;
    letI := S.zero_isManifold;
    letI := zeroCompactSpace S;
    ∀ (rZ : (embedding S).TubularRetraction),
      GeometricArf.invariant (embedding S) (normalFrame S m) rZ z = 0 := by
  let : SimplyConnectedSpace B := S.collar.zeroHomeomorph.symm.toHomotopyEquiv.simplyConnectedSpace
  let : Subsingleton (SingularHomology S.Zero 2) :=
    TwoConnectedCoefficients.secondHomology_subsingleton z
  let : Subsingleton (SingularHomology B 2) :=
    (homeomorphHomologyEquiv S.collar.zeroHomeomorph 2).symm.injective.subsingleton
  let b : B := S.collar.zeroHomeomorph z
  obtain ⟨T, hTP, _, hTP2, _, _, hF⟩ :=
    CollaredFramedConnectivity.exists_twoConnected_state S b
  let := hTP
  let := hTP2
  let := S.zeroAtlas
  let := S.zero_isManifold
  let := zeroCompactSpace S
  let := T.zeroAtlas
  let := T.zero_isManifold
  let := zeroCompactSpace T
  obtain ⟨F⟩ := hF
  let G : StabilizedFramedDiffeomorph (embedding S) (normalFrame S (referencePoint S b))
      (embedding T) (normalFrame T (referencePoint T b)) := F
  let : SimplyConnectedSpace T.Zero := T.collar.zeroHomeomorph.toHomotopyEquiv.simplyConnectedSpace
  let : Subsingleton (SingularHomology T.Zero 2) :=
    (homeomorphHomologyEquiv T.collar.zeroHomeomorph 2).injective.subsingleton
  let zT : T.Zero := G.diffeomorph z
  let : Subsingleton (π_ 2 T.Zero zT) :=
    (SecondHurewicz.SimplyConnected.hurewiczPi2Equiv zT).injective.subsingleton
  let : Nonempty T.Zero := ⟨zT⟩
  obtain ⟨rT⟩ := (embedding T).nonempty_tubularRetraction (normalFrame T (referencePoint T b))
  intro rZ
  rw [normalFrame_point_independent S (referencePoint S b) m]
  exact (G.geometricArf_eq rZ rT z zT).trans
    (geometricArf_eq_zero T (referencePoint T b) zT rT)

end NoExoticSixSphere.CollaredZero
