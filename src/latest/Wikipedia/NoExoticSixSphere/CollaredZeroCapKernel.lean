import Wikipedia.NoExoticSixSphere.CollaredZeroQuadraticKernel
import Wikipedia.NoExoticSixSphere.TimeCollarBoundaryPairing
import Wikipedia.NoExoticSixSphere.GeometricCapPairingComparison

/-!
# The actual low-surgery zero fiber's cap and geometric polar kernels

The boundary homeomorphism only adds the literal half subtype and fixes
ambient points. Its composite inclusion is the original zero-to-half map.
The native regular-fiber atlas is retained. On a two-connected zero fiber,
the proved geometric-cap comparison identifies self-orthogonality with that
of the original induced-frame quadratic form's polar pairing.
-/

noncomputable section

open Function ContinuousMap
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.CollaredZero

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse
open Wikipedia.HopfProblem.SingularMayerVietoris Wikipedia.HopfProblem.SphereHomologyCoefficients

attribute [local instance] modHomologyModule

variable {B : Type} [TopologicalSpace B] (S : LowCollaredSevenState B)

theorem zeroCompactSpace : CompactSpace S.Zero :=
  (isClosed_eq S.zeroTimeMap.continuous continuous_const
    ).isClosedEmbedding_subtypeVal.compactSpace

def boundaryHomeomorph : S.Zero ≃ₜ TimeCollarDuality.boundary S.time where
  toFun p := ⟨⟨p.val, p.property.symm.le⟩, p.property⟩
  invFun p := ⟨p.val.val, p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem presentationInclusion_eq_halfInclusion :
    TimeCollarDuality.presentationInclusion (boundaryHomeomorph S) = halfInclusion S := rfl

variable [Subsingleton (SingularHomology S.PositiveHalf 2)]

theorem capKernel_selfOrthogonal [Subsingleton (SingularHomology S.Zero 2)]
    (b : ModHomology 2 S.Zero 3) :
    letI := S.zeroAtlas;
    letI := zeroCompactSpace S;
    letI : Fact (Module.finrank ℝ (Vector 6) = (3 + 2) + 1) := ⟨by simp⟩;
    (∀ a : ModHomology 2 S.Zero 3, modHomologyMap 2 (halfInclusion S) 3 a = 0 →
      ZeroSecondHomologyCap.pairing (E := Vector 6) S.Zero a b = 0) ↔
      modHomologyMap 2 (halfInclusion S) 3 b = 0 := by
  let := S.zeroAtlas
  let := zeroCompactSpace S
  let : Fact (Module.finrank ℝ (Vector 6) = (3 + 2) + 1) := ⟨by simp⟩
  let : Subsingleton (SingularHomology (TimeCollar.NonnegativeHalf S.time) 2) :=
    ‹Subsingleton (SingularHomology S.PositiveHalf 2)›
  exact TimeCollarDuality.presentationCapKernel_selfOrthogonal S.collar (boundaryHomeomorph S) b

variable [SimplyConnectedSpace S.Zero] (m : S.Space) (z : S.Zero)
  [Subsingleton (π_ 2 S.Zero z)]

theorem originalPolarKernel_selfOrthogonal :
    letI := S.zeroAtlas;
    letI := S.zero_isManifold;
    letI := zeroCompactSpace S;
    ∀ (rZ : (embedding S).TubularRetraction) (b : ModHomology 2 S.Zero 3),
      (∀ a : ModHomology 2 S.Zero 3, modHomologyMap 2 (halfInclusion S) 3 a = 0 →
        ((embedding S).modTwoHomologyQuadraticForm (normalFrame S m) rZ z).polarBilin a b = 0) ↔
        modHomologyMap 2 (halfInclusion S) 3 b = 0 := by
  let := S.zeroAtlas
  let := S.zero_isManifold
  let := zeroCompactSpace S
  let : Fact (Module.finrank ℝ (Vector 6) = (3 + 2) + 1) := ⟨by simp⟩
  let := TwoConnectedCoefficients.secondHomology_subsingleton z
  intro rZ b
  have hpair (a b : ModHomology 2 S.Zero 3) :
      ZeroSecondHomologyCap.pairing (E := Vector 6) S.Zero a b =
        ((embedding S).modTwoHomologyQuadraticForm (normalFrame S m) rZ z).polarBilin a b := by
    rw [ZeroSecondHomologyCap.pairing_eq_connected S.Zero z,
      (embedding S).modTwoHomologyQuadraticForm_polar]
    exact (embedding S).cap_pairing_eq_geometric (normalFrame S m) rZ z a b
  simpa only [hpair] using capKernel_selfOrthogonal S b

end NoExoticSixSphere.CollaredZero
