import Wikipedia.NoExoticSixSphere.CollaredZeroClopenQuadraticKernel
import Wikipedia.NoExoticSixSphere.CollaredZeroComponentCapKernel
import Wikipedia.NoExoticSixSphere.GeometricArfInvariant
import Wikipedia.NoExoticSixSphere.ArfMetabolic

/-!
# Arf vanishing on the native component opposite a topological six-sphere

The complement homeomorphism is the literal decomposition into two clopen
sets. Its right inclusion is exactly the original component inclusion.
The other component's zero middle homology supplies self-orthogonality,
while the actual restricted induced frame supplies quadratic vanishing.
Thus the chosen component's genuine geometric Arf invariant is zero.
No identification with a framed Hopf model or stable detection is assumed.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.CollaredZero

open GLOrthonormalization EuclideanEmbedding
open Wikipedia.HopfProblem.DegreeCollapse
open Wikipedia.HopfProblem.SingularMayerVietoris Wikipedia.HopfProblem.SphereHomologyCoefficients

attribute [local instance] modHomologyModule

variable {B : Type} [TopologicalSpace B] (S : LowCollaredSevenState B)
  (U : TopologicalSpace.Opens S.Zero) (hU : IsClosed (U : Set S.Zero))

theorem rightHalfInclusion_clopenComplement :
    rightHalfInclusion S (NativeBoundarySum.clopenComplementHomeomorph U hU) =
      clopenHalfInclusion S U := by
  unfold rightHalfInclusion
  rw [NativeBoundarySum.inr_clopenComplementHomeomorph]
  rfl

def clopenModTwoKernel : Submodule (ZMod 2) (ModHomology 2 U 3) :=
  LinearMap.ker ((modHomologyMap 2 (clopenHalfInclusion S U) 3).toAddMonoidHom.toZModLinearMap 2)

variable [Subsingleton (SingularHomology S.PositiveHalf 2)]
  [SimplyConnectedSpace U] (m : S.Space) (u : U) [Subsingleton (π_ 2 U u)]

theorem clopenPolarKernel_selfOrthogonal_of_compl_sixSphere
    (hX : ↥((U : Set S.Zero)ᶜ) ≃ₜ Sphere 6) :
    letI := S.zeroAtlas;
    letI := S.zero_isManifold;
    letI := clopenCompactSpace S U hU;
    let eU := ClopenEmbedding.restrict (embedding S) U hU;
    let aU := ClopenEmbedding.restrictNormalFrame (embedding S) U hU (normalFrame S m);
    ∀ (rU : eU.TubularRetraction) (b : ModHomology 2 U 3),
      (∀ a : ModHomology 2 U 3, modHomologyMap 2 (clopenHalfInclusion S U) 3 a = 0 →
        (eU.modTwoHomologyQuadraticForm aU rU u).polarBilin a b = 0) ↔
        modHomologyMap 2 (clopenHalfInclusion S U) 3 b = 0 := by
  let := S.zeroAtlas
  let := S.zero_isManifold
  let := clopenCompactSpace S U hU
  dsimp only
  intro rU b
  have he := rightPolarKernel_selfOrthogonal_of_sixSphere S
    (NativeBoundarySum.clopenComplementHomeomorph U hU) u
    (ClopenEmbedding.restrict (embedding S) U hU)
    (ClopenEmbedding.restrictNormalFrame (embedding S) U hU (normalFrame S m)) rU hX b
  simpa only [rightHalfInclusion_clopenComplement] using he

variable [SimplyConnectedSpace S.PositiveHalf]

theorem clopenGeometricArf_eq_zero_of_compl_sixSphere
    (hX : ↥((U : Set S.Zero)ᶜ) ≃ₜ Sphere 6) :
    letI := S.zeroAtlas;
    letI := S.zero_isManifold;
    letI := clopenCompactSpace S U hU;
    let eU := ClopenEmbedding.restrict (embedding S) U hU;
    let aU := ClopenEmbedding.restrictNormalFrame (embedding S) U hU (normalFrame S m);
    ∀ (rU : eU.TubularRetraction), GeometricArf.invariant eU aU rU u = 0 := by
  let := S.zeroAtlas
  let := S.zero_isManifold
  let := clopenCompactSpace S U hU
  let eU := ClopenEmbedding.restrict (embedding S) U hU
  let aU := ClopenEmbedding.restrictNormalFrame (embedding S) U hU (normalFrame S m)
  dsimp only
  intro rU
  let : Finite (ModHomology 2 U 3) :=
    compactManifold_modTwoMiddleHomology_finiteType (Vector 6) U u
  let : Fintype (ModHomology 2 U 3) := Fintype.ofFinite _
  apply Arf.invariant_eq_zero_of_selfOrthogonal (eU.modTwoHomologyQuadraticForm aU rU u)
    (eU.modTwoHomologyQuadraticForm_nondegenerate aU rU u) (clopenModTwoKernel S U)
  · intro l
    exact modTwoQuadraticForm_zero_on_clopen_kernel S U hU m u rU l.val l.property
  · intro v
    constructor
    · intro hv
      apply (clopenPolarKernel_selfOrthogonal_of_compl_sixSphere S U hU m u hX rU v).mp
      intro a ha
      exact hv ⟨a, ha⟩
    · intro hv l
      exact (clopenPolarKernel_selfOrthogonal_of_compl_sixSphere S U hU m u hX rU v).mpr
        hv l.val l.property

end NoExoticSixSphere.CollaredZero
