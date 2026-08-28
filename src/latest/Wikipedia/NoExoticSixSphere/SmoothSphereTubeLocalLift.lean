import Wikipedia.NoExoticSixSphere.TransverseTubeNormalCoordinate
import Wikipedia.NoExoticSixSphere.SphereNormalCapNormalization
import Wikipedia.HopfProblem.SingularMayerVietoris

/-!
# Actual local lifts into a smooth whole-source sphere tube

The given partial diffeomorphism has the entire normal product as its
source. Its original inverse gives a continuous lift on every open
source region mapping into the tube. Native transversality makes the
normal coordinate of this actual lift locally a homeomorphism.
-/

noncomputable section

open Set Topology
open Wikipedia.HopfProblem SingularMayerVietoris
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SmoothSphereTube

open SphereNormalCapNormalization

variable {M : Type} [TopologicalSpace M] [ChartedSpace AmbientVector M]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 3)) (𝓡 6) (Sphere 3 × NormalVector) M ∞)
  (hsource : Φ.source = univ)

/-- The actual whole-source tube as a continuous map. -/
def tube : C(Sphere 3 × NormalVector, M) :=
  ⟨Φ, (Φ.toOpenPartialHomeomorph.isOpenEmbedding hsource).continuous⟩

theorem isOpenEmbedding_tube : IsOpenEmbedding (tube Φ hsource) :=
  Φ.toOpenPartialHomeomorph.isOpenEmbedding hsource

variable (g : C(Sphere 3, M)) (U : Set (Sphere 3))
  (htarget : ∀ x ∈ U, g x ∈ Φ.target)

/-- The original inverse tube on the specified source neighborhood. -/
def lift : C(U, Sphere 3 × NormalVector) :=
  ⟨fun x => Φ.symm (g x), continuous_iff_continuousAt.mpr fun x => by
    have hi : ContinuousAt (Φ.symm : M → Sphere 3 × NormalVector) (g x) :=
      (Φ.contMDiffOn_invFun.contMDiffAt
        (Φ.open_target.mem_nhds (htarget x x.property))).continuousAt
    exact ContinuousAt.comp (f := fun z : U => g z) hi
      (g.continuous.comp continuous_subtype_val).continuousAt⟩

/-- Lifting and applying the same tube recovers the exact original restricted map. -/
theorem tube_comp_lift : (tube Φ hsource).comp (lift Φ g U htarget) =
    g.comp (subtypeInclusion U) := by
  ext x
  exact Φ.right_inv (htarget x x.property)

include hsource in
/-- A core point lifts to its original sphere point and zero normal coordinate. -/
theorem lift_core (f : Sphere 3 → M) (hcore : ∀ s, Φ (s, 0) = f s)
    (x : Sphere 3) (y : U) (hxy : f x = g y) : lift Φ g U htarget y = (x, 0) := by
  have hx : (x, (0 : NormalVector)) ∈ Φ.source := hsource.symm ▸ Set.mem_univ _
  exact (congrArg Φ.symm ((hcore x).trans hxy).symm).trans (Φ.left_inv hx)

include hsource in
/-- Native transversality gives local invertibility of the actual lifted normal coordinate. -/
theorem localHomeomorphOn_normal_lift (hU : IsOpen U) (f : Sphere 3 → M)
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (hcore : ∀ s, Φ (s, 0) = f s) (x : Sphere 3) (y : U) (hxy : f x = g y)
    (ht : Function.Surjective ((mfderiv (𝓡 3) (𝓡 6) f x).coprod
      (mfderiv (𝓡 3) (𝓡 6) g y))) :
    IsLocalHomeomorphOn (ContinuousMap.snd.comp (lift Φ g U htarget)) ({y} : Set U) := by
  have hx : (x, (0 : NormalVector)) ∈ Φ.source := hsource.symm ▸ Set.mem_univ _
  have hn := TubeNormalCoordinates.isLocalDiffeomorphAt_normal Φ f g hf hg hcore x y hx hxy ht
  have hl : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ (TubeNormalCoordinates.normal Φ g)
      ({y.val} : Set (Sphere 3)) := by
    intro z
    have hz : z.val = y.val := z.property
    exact hz.symm ▸ hn
  exact hl.isLocalHomeomorphOn.comp
    hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
      (show MapsTo (Subtype.val : U → Sphere 3) {y} {y.val} from fun _ hz =>
        congrArg Subtype.val hz)

end NoExoticSixSphere.SmoothSphereTube
