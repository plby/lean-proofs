import Wikipedia.NoExoticSixSphere.CollaredZeroCapKernel
import Wikipedia.NoExoticSixSphere.GeometricArfInvariant
import Wikipedia.NoExoticSixSphere.ArfMetabolic

/-!
# Vanishing of the original Arf invariant on a two-connected collared boundary

The actual zero-to-half homology kernel is a mod-two submodule. The proved
geometric quadratic-kernel vanishing and original polar self-orthogonality
make it metabolic. The algebraic Gauss-sum theorem therefore gives zero
for the original geometric Arf invariant and original induced normal frame.
This does not treat a disconnected boundary or assert Arf detection.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.CollaredZero

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse
open Wikipedia.HopfProblem.SingularMayerVietoris Wikipedia.HopfProblem.SphereHomologyCoefficients

attribute [local instance] modHomologyModule

variable {B : Type} [TopologicalSpace B] (S : LowCollaredSevenState B)

def halfModTwoKernel : Submodule (ZMod 2) (ModHomology 2 S.Zero 3) :=
  LinearMap.ker ((modHomologyMap 2 (halfInclusion S) 3).toAddMonoidHom.toZModLinearMap 2)

theorem mem_halfModTwoKernel (a : ModHomology 2 S.Zero 3) :
    a ∈ halfModTwoKernel S ↔ modHomologyMap 2 (halfInclusion S) 3 a = 0 := Iff.rfl

variable [SimplyConnectedSpace S.PositiveHalf]
  [Subsingleton (SingularHomology S.PositiveHalf 2)]
  [SimplyConnectedSpace S.Zero] (m : S.Space) (z : S.Zero)
  [Subsingleton (π_ 2 S.Zero z)]

theorem geometricArf_eq_zero :
    letI := S.zeroAtlas;
    letI := S.zero_isManifold;
    letI := zeroCompactSpace S;
    ∀ (rZ : (embedding S).TubularRetraction),
      GeometricArf.invariant (embedding S) (normalFrame S m) rZ z = 0 := by
  let := S.zeroAtlas
  let := S.zero_isManifold
  let := zeroCompactSpace S
  intro rZ
  let : Finite (ModHomology 2 S.Zero 3) :=
    compactManifold_modTwoMiddleHomology_finiteType (Vector 6) S.Zero z
  let : Fintype (ModHomology 2 S.Zero 3) := Fintype.ofFinite _
  apply Arf.invariant_eq_zero_of_selfOrthogonal
    ((embedding S).modTwoHomologyQuadraticForm (normalFrame S m) rZ z)
    ((embedding S).modTwoHomologyQuadraticForm_nondegenerate (normalFrame S m) rZ z)
    (halfModTwoKernel S)
  · intro l
    exact modTwoQuadraticForm_zero_on_full_kernel S m z rZ l.val l.property
  · intro v
    constructor
    · intro hv
      apply (originalPolarKernel_selfOrthogonal S m z rZ v).mp
      intro a ha
      exact hv ⟨a, ha⟩
    · intro hv l
      exact (originalPolarKernel_selfOrthogonal S m z rZ v).mpr hv l.val l.property

end NoExoticSixSphere.CollaredZero
