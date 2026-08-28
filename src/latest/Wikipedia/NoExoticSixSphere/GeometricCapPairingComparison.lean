import Wikipedia.NoExoticSixSphere.FramedSpherePairingComparison
import Wikipedia.NoExoticSixSphere.ModTwoHomologyQuadraticParity
import Wikipedia.HopfProblem.DegreeCollapseEmbeddedSphereRepresentative

/-!
# The original geometric middle pairing equals the original cap pairing

The existing native kink insertion and finite Whitney cancellation
theorem constructs an embedded immersive representative of every sphere
map in a simply connected compact six-manifold. Native Hurewicz and
homotopy invariance give such a representative of every actual mod-two
middle class. The proved embedded-sphere comparison therefore identifies
the two original pairings on all classes. Actual cap duality then proves
nondegeneracy of the geometric pairing and of the original quadratic
form's polar form, without a nondegeneracy or representative hypothesis.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff Topology
open Wikipedia.HopfProblem SphereHomologyCoefficients

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization

attribute [local instance] SphereNormalCapNormalization.ambientDimension modHomologyModule

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [SimplyConnectedSpace M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (r : TubularRetraction e) (m : M) [Subsingleton (π_ 2 M m)]

include e r m in
/-- Actual native middle classes have constructed embedded immersive sphere representatives. -/
theorem exists_embedded_modTwoMiddle_representative (b : ModHomology 2 M 3) :
    ∃ f : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ f ∧ Topology.IsClosedEmbedding f ∧
      (∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) f x)) ∧ SixSphereMiddleParity.sphereClass f = b := by
  obtain ⟨f, hf⟩ := SmoothCube.modTwoSphereClass_surjective m b
  rw [SmoothCube.modTwoSphereClass_eq_standard f] at hf
  obtain ⟨g, hg, H, hd, hi⟩ :=
    DegreeCollapse.TripleParameters.exists_embedded_sphere_representative e r f.val
  exact ⟨g, hg, hi, hd, (SixSphereMiddleParity.sphereClass_homotopic H).symm.trans hf⟩

include a in
/-- The comparison holds for every pair of original native middle homology classes. -/
theorem cap_pairing_eq_geometric (b c : ModHomology 2 M 3) :
    MiddleCapEvaluation.pairing (E := Vector 6) m b c = modTwoHomologyIntersection e r m b c := by
  obtain ⟨f, hf, hi, hd, rfl⟩ := exists_embedded_modTwoMiddle_representative e r m b
  exact cap_pairing_eq_geometric_all_right_of_embedding e f r hf hi.injective hd m a c

include a in
/-- Equality of the actual bilinear forms, not just a comparison on chosen representatives. -/
theorem cap_pairing_eq_geometric_form :
    MiddleCapEvaluation.pairing (E := Vector 6) m = modTwoHomologyIntersection e r m := by
  ext b c
  exact cap_pairing_eq_geometric e a r m b c

include a in
/-- Nondegeneracy of the original geometric intersection form follows from actual cap duality. -/
theorem modTwoHomologyIntersection_nondegenerate :
    (modTwoHomologyIntersection e r m).Nondegenerate := by
  rw [← cap_pairing_eq_geometric_form e a r m]
  exact MiddleCapEvaluation.pairing_nondegenerate (E := Vector 6) m

/-- The original geometric quadratic obstruction has a proved nondegenerate polar form. -/
theorem modTwoHomologyQuadraticForm_nondegenerate :
    (modTwoHomologyQuadraticForm e a r m).polarBilin.Nondegenerate := by
  rw [modTwoHomologyQuadraticForm_polar]
  exact modTwoHomologyIntersection_nondegenerate e a r m

end NoExoticSixSphere.EuclideanEmbedding
