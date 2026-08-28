import Wikipedia.NoExoticSixSphere.FourDiskPuncturedDomain
import Wikipedia.NoExoticSixSphere.ComplementaryOperatorCoordinates
import Wikipedia.NoExoticSixSphere.ManifoldNormalChartCoordinates

/-!
# The actual normal and derivative columns of the punctured four-disk

The normal frame is the prescribed frame of the original embedding. The
last four columns are the actual derivative of the embedded disk map.
Smoothness is required only at points of the closed disk. Orthogonality
of the two ranges gives an injective operator on its original punctured
domain, without asserting immersion at the deleted singularities.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (g : Vector 4 → M)

def fourDiskDerivative (x : Vector 4) : Vector 4 →L[ℝ] Vector e.ambientDimension :=
  fderiv ℝ (e.toFun ∘ g) x

def fourDiskNormalOperator (x : Vector 4) :
    Vector (e.ambientDimension - 7) →L[ℝ] Vector e.ambientDimension :=
  (a.orthonormal (g x)).val

def normalFourDiskOperator (x : Vector 4) :
    Vector ((e.ambientDimension - 7) + 4) →L[ℝ] Vector e.ambientDimension :=
  OperatorSum.operator (e.fourDiskNormalOperator a g x) (e.fourDiskDerivative g x)

theorem fourDiskDerivative_range (x : Vector 4)
    (hg : MDifferentiableAt (𝓡 4) (𝓡 7) g x) :
    (e.fourDiskDerivative g x).range ≤ e.tangentImage (g x) := by
  have he : e.fourDiskDerivative g x =
      (mfderiv (𝓡 7) (𝓡 e.ambientDimension) e.toFun (g x)).comp
        (mfderiv (𝓡 4) (𝓡 7) g x) := by
    rw [fourDiskDerivative, ← mfderiv_eq_fderiv,
      mfderiv_comp x (e.smooth.mdifferentiableAt (by simp)) hg]
  rw [he]
  rintro v ⟨w, rfl⟩
  exact ⟨mfderiv (𝓡 4) (𝓡 7) g x w, rfl⟩

theorem fourDiskNormalOperator_range (x : Vector 4) :
    (e.fourDiskNormalOperator a g x).range = (e.tangentImage (g x))ᗮ :=
  (a.orthonormal_range (g x)).trans (e.range_normalProjection (g x))

theorem normalFourDiskOperator_injective (x : Vector 4)
    (hg : MDifferentiableAt (𝓡 4) (𝓡 7) g x)
    (hi : Injective (mfderiv (𝓡 4) (𝓡 7) g x)) :
    Injective (e.normalFourDiskOperator a g x) := by
  apply OperatorSum.injective_operator
  · exact Stiefel.injective (a.orthonormal (g x))
  · exact (GenericFourDisk.injective_embedded_derivative_iff e g x hg).mpr hi
  · rw [e.fourDiskNormalOperator_range]
    exact (e.tangentImage (g x)).orthogonal_disjoint.symm.mono_right
      (e.fourDiskDerivative_range g x hg)

theorem contDiffAt_normalFourDiskOperator (x : Vector 4)
    (hg : ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x) :
    ContDiffAt ℝ ∞ (e.normalFourDiskOperator a g) x := by
  apply OperatorSum.contDiffAt_operator
  · exact (a.contMDiff_orthonormal.contMDiffAt.comp x hg).contDiffAt
  · exact ((e.smooth.contMDiffAt.comp x hg).contDiffAt.fderiv_right (by simp))

variable (hg : ∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)

include hg in
theorem continuousOn_normalFourDiskOperator :
    ContinuousOn (e.normalFourDiskOperator a g) (closedBall 0 1) :=
  fun x hx ↦ (e.contDiffAt_normalFourDiskOperator a g x (hg x hx)).continuousAt.continuousWithinAt

variable (P : GenericFourDisk.ParityBallSystem g)

def puncturedFourDiskOperatorMap :
    C(P.puncturedDisk, Monomorphism.Space e.ambientDimension ((e.ambientDimension - 7) + 4)) where
  toFun x := ⟨e.normalFourDiskOperator a g x.val,
    e.normalFourDiskOperator_injective a g x.val
      ((hg x.val x.property.1).mdifferentiableAt (by simp))
      (P.injective_mfderiv_on_puncturedDisk x.val x.property)⟩
  continuous_toFun := ((e.continuousOn_normalFourDiskOperator a g hg).comp_continuous
    continuous_subtype_val (fun x ↦ x.property.1)).subtype_mk _

theorem puncturedFourDiskOperatorMap_value (x : P.puncturedDisk) :
    (e.puncturedFourDiskOperatorMap a g hg P x).val = e.normalFourDiskOperator a g x.val := rfl

def puncturedFourDiskFrameMap :
    C(P.puncturedDisk, Space e.ambientDimension ((e.ambientDimension - 7) + 4)) :=
  (Monomorphism.normalize e.ambientDimension ((e.ambientDimension - 7) + 4)).comp
    (e.puncturedFourDiskOperatorMap a g hg P)

def puncturedFourDiskGlobalFrameMap :
    C(P.puncturedDisk,
      Space (3 + (((e.ambientDimension - 7) + 2) + 2)) (((e.ambientDimension - 7) + 2) + 2)) := by
  have hd := e.dimension_le_ambient (g 0)
  have hN : e.ambientDimension = 3 + (((e.ambientDimension - 7) + 2) + 2) := by omega
  have hk : (e.ambientDimension - 7) + 4 = ((e.ambientDimension - 7) + 2) + 2 := by omega
  let H : C(Space e.ambientDimension ((e.ambientDimension - 7) + 4),
      Space (3 + (((e.ambientDimension - 7) + 2) + 2)) (((e.ambientDimension - 7) + 2) + 2)) :=
    dimensionHomeomorph hN hk
  exact H.comp (e.puncturedFourDiskFrameMap a g hg P)

end NoExoticSixSphere.EuclideanEmbedding
