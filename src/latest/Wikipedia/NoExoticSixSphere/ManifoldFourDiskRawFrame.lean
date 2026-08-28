import Wikipedia.NoExoticSixSphere.ManifoldFourDiskBoundaryExtension
import Wikipedia.NoExoticSixSphere.NormalColumnNormalization

/-!
# Returning to the original raw normal columns of the four-disk

Normalize only the prescribed normal columns, leaving the actual disk
derivative fixed. On the original punctured disk the whole interpolation
is injective. Consequently extension of the normalized boundary operator
gives extension with the exact original raw normal-frame columns.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel DiskBoundary
open Wikipedia.HopfProblem.DegreeCollapse

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (g : Vector 4 → M)

def rawNormalFourDiskOperator (x : Vector 4) :
    Vector ((e.ambientDimension - 7) + 4) →L[ℝ] Vector e.ambientDimension :=
  OperatorSum.operator (a.ambient (g x)) (e.fourDiskDerivative g x)

theorem rawFourDiskNormal_range_disjoint (x : Vector 4)
    (hg : MDifferentiableAt (𝓡 4) (𝓡 7) g x) :
    Disjoint (a.ambient (g x)).range (e.fourDiskDerivative g x).range := by
  rw [a.ambient_range, e.range_normalProjection]
  exact (e.tangentImage (g x)).orthogonal_disjoint.symm.mono_right
    (e.fourDiskDerivative_range g x hg)

theorem rawNormalFourDiskOperator_injective (x : Vector 4)
    (hg : MDifferentiableAt (𝓡 4) (𝓡 7) g x)
    (hi : Injective (mfderiv (𝓡 4) (𝓡 7) g x)) :
    Injective (e.rawNormalFourDiskOperator a g x) :=
  OperatorSum.injective_operator _ _ (a.ambient_injective (g x))
    ((GenericFourDisk.injective_embedded_derivative_iff e g x hg).mpr hi)
    (e.rawFourDiskNormal_range_disjoint a g x hg)

theorem contDiffAt_fourDiskDerivative (x : Vector 4)
    (hg : ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x) :
    ContDiffAt ℝ ∞ (e.fourDiskDerivative g) x :=
  (e.smooth.contMDiffAt.comp x hg).contDiffAt.fderiv_right (by simp)

theorem contDiffAt_rawNormalFourDiskOperator (x : Vector 4)
    (hg : ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x) :
    ContDiffAt ℝ ∞ (e.rawNormalFourDiskOperator a g) x :=
  OperatorSum.contDiffAt_operator
    (a.contMDiff_ambient.contMDiffAt.comp x hg).contDiffAt
    (e.contDiffAt_fourDiskDerivative g x hg)

variable (hg : ∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
  (P : GenericFourDisk.ParityBallSystem g)

include hg in
theorem continuousOn_rawNormalFourDiskOperator :
    ContinuousOn (e.rawNormalFourDiskOperator a g) (closedBall 0 1) :=
  fun x hx ↦
    (e.contDiffAt_rawNormalFourDiskOperator a g x (hg x hx)).continuousAt.continuousWithinAt

def puncturedRawFourDiskOperatorMap :
    C(P.puncturedDisk, Monomorphism.Space e.ambientDimension ((e.ambientDimension - 7) + 4)) where
  toFun x := ⟨e.rawNormalFourDiskOperator a g x.val,
    e.rawNormalFourDiskOperator_injective a g x.val
      ((hg x.val x.property.1).mdifferentiableAt (by simp))
      (P.injective_mfderiv_on_puncturedDisk x.val x.property)⟩
  continuous_toFun := ((e.continuousOn_rawNormalFourDiskOperator a g hg).comp_continuous
    continuous_subtype_val (fun x ↦ x.property.1)).subtype_mk _

theorem puncturedRawFourDiskOperatorMap_value (x : P.puncturedDisk) :
    (e.puncturedRawFourDiskOperatorMap a g hg P x).val =
      e.rawNormalFourDiskOperator a g x.val := rfl

theorem puncturedRawFourDiskOperatorMap_homotopic :
    (e.puncturedRawFourDiskOperatorMap a g hg P).Homotopic
      (e.puncturedFourDiskOperatorMap a g hg P) := by
  let A := fun x : P.puncturedDisk ↦ a.ambient (g x.val)
  let D := fun x : P.puncturedDisk ↦ e.fourDiskDerivative g x.val
  have hgc : Continuous (fun x : P.puncturedDisk ↦ g x.val) :=
    (show ContinuousOn g (closedBall 0 1) from
      fun x hx ↦ (hg x hx).continuousAt.continuousWithinAt).comp_continuous
        continuous_subtype_val (fun x ↦ x.property.1)
  have hA : Continuous A := a.contMDiff_ambient.continuous.comp hgc
  have hDc : ContinuousOn (e.fourDiskDerivative g) (closedBall 0 1) :=
    fun x hx ↦ (e.contDiffAt_fourDiskDerivative g x (hg x hx)).continuousAt.continuousWithinAt
  have hD : Continuous D := hDc.comp_continuous continuous_subtype_val (fun x ↦ x.property.1)
  apply OperatorSum.homotopic_normalize_left A D hA hD
    (fun x ↦ a.ambient_injective (g x.val))
    (fun x ↦ (GenericFourDisk.injective_embedded_derivative_iff e g x.val
      ((hg x.val x.property.1).mdifferentiableAt (by simp))).mpr
        (P.injective_mfderiv_on_puncturedDisk x.val x.property))
    (fun x ↦ e.rawFourDiskNormal_range_disjoint a g x.val
      ((hg x.val x.property.1).mdifferentiableAt (by simp)))
  · intro x
    rfl
  · intro x
    rfl

include hg P in
theorem fourDiskRawOuterOperator_extends (heven : Even (DiskDoublePoints.singularSet g).ncard) :
    Extends ((e.puncturedRawFourDiskOperatorMap a g hg P).comp P.outerBoundary) := by
  obtain ⟨H⟩ := e.puncturedRawFourDiskOperatorMap_homotopic a g hg P
  apply (extends_homotopic_iff ⟨H.compContinuousMap P.outerBoundary⟩).mpr
  exact e.fourDiskOuterOperator_extends a g hg P heven

include hg P in
theorem exists_rawFourDiskOperator_extension
    (heven : Even (DiskDoublePoints.singularSet g).ncard) :
    ∃ F : C(DiskCylinder.Disk (E := Vector 4),
        Monomorphism.Space e.ambientDimension ((e.ambientDimension - 7) + 4)),
      ∀ s : Sphere 3, (F (DiskCylinder.boundaryToDisk s)).val =
        e.rawNormalFourDiskOperator a g s.val := by
  obtain ⟨F, hF⟩ := e.fourDiskRawOuterOperator_extends a g hg P heven
  exact ⟨F, fun s ↦ congrArg Subtype.val (hF s)⟩

end NoExoticSixSphere.EuclideanEmbedding
