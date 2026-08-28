import Wikipedia.NoExoticSixSphere.FourAnnulusPuncturedDomain
import Wikipedia.NoExoticSixSphere.ManifoldFourDiskOperator

/-!
# The actual prescribed normal and derivative columns on the punctured annulus

The operator uses the prescribed normal frame of the original embedding
and the actual four derivative columns of the embedded annulus map.
Their complementary ranges give injectivity everywhere on the original
punctured domain. Both endpoint restrictions retain their literal source
vectors, including the radius-two scaling at the outer boundary.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel SphereAnnulus

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (g : Vector 4 → M)
  (hg : ∀ x ∈ domain 3, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)

include hg in
theorem continuousOn_normalFourAnnulusOperator :
    ContinuousOn (e.normalFourDiskOperator a g) (domain 3) :=
  fun x hx ↦ (e.contDiffAt_normalFourDiskOperator a g x (hg x hx)).continuousAt.continuousWithinAt

variable (P : GenericFourAnnulus.ParityBallSystem g)

def puncturedFourAnnulusOperatorMap :
    C(P.puncturedAnnulus,
      Monomorphism.Space e.ambientDimension ((e.ambientDimension - 7) + 4)) where
  toFun x := ⟨e.normalFourDiskOperator a g x.val,
    e.normalFourDiskOperator_injective a g x.val
      ((hg x.val x.property.1).mdifferentiableAt (by simp))
      (P.injective_mfderiv_on_puncturedAnnulus x.val x.property)⟩
  continuous_toFun := ((e.continuousOn_normalFourAnnulusOperator a g hg).comp_continuous
    continuous_subtype_val (fun x ↦ x.property.1)).subtype_mk _

theorem puncturedFourAnnulusOperatorMap_value (x : P.puncturedAnnulus) :
    (e.puncturedFourAnnulusOperatorMap a g hg P x).val = e.normalFourDiskOperator a g x.val := rfl

theorem puncturedFourAnnulusOperatorMap_inner_value (q : Sphere 3) :
    (e.puncturedFourAnnulusOperatorMap a g hg P (P.innerBoundary q)).val =
      e.normalFourDiskOperator a g q.val := rfl

theorem puncturedFourAnnulusOperatorMap_outer_value (q : Sphere 3) :
    (e.puncturedFourAnnulusOperatorMap a g hg P (P.outerBoundary q)).val =
      e.normalFourDiskOperator a g ((2 : ℝ) • q.val) := rfl

def puncturedFourAnnulusFrameMap :
    C(P.puncturedAnnulus, Space e.ambientDimension ((e.ambientDimension - 7) + 4)) :=
  (Monomorphism.normalize e.ambientDimension ((e.ambientDimension - 7) + 4)).comp
    (e.puncturedFourAnnulusOperatorMap a g hg P)

def puncturedFourAnnulusGlobalFrameMap :
    C(P.puncturedAnnulus,
      Space (3 + (((e.ambientDimension - 7) + 2) + 2)) (((e.ambientDimension - 7) + 2) + 2)) := by
  have hd := e.dimension_le_ambient (g 0)
  have hN : e.ambientDimension = 3 + (((e.ambientDimension - 7) + 2) + 2) := by omega
  have hk : (e.ambientDimension - 7) + 4 = ((e.ambientDimension - 7) + 2) + 2 := by omega
  let H : C(Space e.ambientDimension ((e.ambientDimension - 7) + 4),
      Space (3 + (((e.ambientDimension - 7) + 2) + 2)) (((e.ambientDimension - 7) + 2) + 2)) :=
    dimensionHomeomorph hN hk
  exact H.comp (e.puncturedFourAnnulusFrameMap a g hg P)

end NoExoticSixSphere.EuclideanEmbedding
