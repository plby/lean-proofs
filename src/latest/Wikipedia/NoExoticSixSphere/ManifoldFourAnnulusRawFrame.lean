import Wikipedia.NoExoticSixSphere.ManifoldFourAnnulusBoundaryHomotopy
import Wikipedia.NoExoticSixSphere.ManifoldFourDiskRawFrame

/-!
# Two-ended homotopy with the exact original raw normal columns

The normal-block interpolation remains in its original normal range,
disjoint from the actual derivative range on the punctured annulus.
It therefore gives a homotopy through injective operators while fixing
all derivative columns. At both ends it converts the checked operator
homotopy into one with the prescribed raw normal-frame columns.
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
  (P : GenericFourAnnulus.ParityBallSystem g)

include hg in
theorem continuousOn_rawNormalFourAnnulusOperator :
    ContinuousOn (e.rawNormalFourDiskOperator a g) (domain 3) :=
  fun x hx ↦
    (e.contDiffAt_rawNormalFourDiskOperator a g x (hg x hx)).continuousAt.continuousWithinAt

def puncturedRawFourAnnulusOperatorMap :
    C(P.puncturedAnnulus,
      Monomorphism.Space e.ambientDimension ((e.ambientDimension - 7) + 4)) where
  toFun x := ⟨e.rawNormalFourDiskOperator a g x.val,
    e.rawNormalFourDiskOperator_injective a g x.val
      ((hg x.val x.property.1).mdifferentiableAt (by simp))
      (P.injective_mfderiv_on_puncturedAnnulus x.val x.property)⟩
  continuous_toFun := ((e.continuousOn_rawNormalFourAnnulusOperator a g hg).comp_continuous
    continuous_subtype_val (fun x ↦ x.property.1)).subtype_mk _

theorem puncturedRawFourAnnulusOperatorMap_value (x : P.puncturedAnnulus) :
    (e.puncturedRawFourAnnulusOperatorMap a g hg P x).val =
      e.rawNormalFourDiskOperator a g x.val := rfl

theorem puncturedRawFourAnnulusOperatorMap_inner_value (q : Sphere 3) :
    (e.puncturedRawFourAnnulusOperatorMap a g hg P (P.innerBoundary q)).val =
      e.rawNormalFourDiskOperator a g q.val := rfl

theorem puncturedRawFourAnnulusOperatorMap_outer_value (q : Sphere 3) :
    (e.puncturedRawFourAnnulusOperatorMap a g hg P (P.outerBoundary q)).val =
      e.rawNormalFourDiskOperator a g ((2 : ℝ) • q.val) := rfl

theorem puncturedRawFourAnnulusOperatorMap_homotopic :
    (e.puncturedRawFourAnnulusOperatorMap a g hg P).Homotopic
      (e.puncturedFourAnnulusOperatorMap a g hg P) := by
  let A := fun x : P.puncturedAnnulus ↦ a.ambient (g x.val)
  let D := fun x : P.puncturedAnnulus ↦ e.fourDiskDerivative g x.val
  have hgc : Continuous (fun x : P.puncturedAnnulus ↦ g x.val) :=
    (show ContinuousOn g (domain 3) from
      fun x hx ↦ (hg x hx).continuousAt.continuousWithinAt).comp_continuous
        continuous_subtype_val (fun x ↦ x.property.1)
  have hA : Continuous A := a.contMDiff_ambient.continuous.comp hgc
  have hDc : ContinuousOn (e.fourDiskDerivative g) (domain 3) :=
    fun x hx ↦ (e.contDiffAt_fourDiskDerivative g x (hg x hx)).continuousAt.continuousWithinAt
  have hD : Continuous D := hDc.comp_continuous continuous_subtype_val (fun x ↦ x.property.1)
  apply OperatorSum.homotopic_normalize_left A D hA hD
    (fun x ↦ a.ambient_injective (g x.val))
    (fun x ↦ (GenericFourDisk.injective_embedded_derivative_iff e g x.val
      ((hg x.val x.property.1).mdifferentiableAt (by simp))).mpr
        (P.injective_mfderiv_on_puncturedAnnulus x.val x.property))
    (fun x ↦ e.rawFourDiskNormal_range_disjoint a g x.val
      ((hg x.val x.property.1).mdifferentiableAt (by simp)))
  · intro x
    rfl
  · intro x
    rfl

theorem puncturedRawFourAnnulusOperatorMap_outer_homotopic_inner
    (heven : Even (AnnulusDoublePoints.singularSet g).ncard) :
    ((e.puncturedRawFourAnnulusOperatorMap a g hg P).comp P.outerBoundary).Homotopic
      ((e.puncturedRawFourAnnulusOperatorMap a g hg P).comp P.innerBoundary) := by
  have h := e.puncturedRawFourAnnulusOperatorMap_homotopic a g hg P
  exact (h.comp (ContinuousMap.Homotopic.refl P.outerBoundary)).trans
    ((e.puncturedFourAnnulusOperatorMap_outer_homotopic_inner a g hg P heven).trans
      (h.comp (ContinuousMap.Homotopic.refl P.innerBoundary)).symm)

end NoExoticSixSphere.EuclideanEmbedding
