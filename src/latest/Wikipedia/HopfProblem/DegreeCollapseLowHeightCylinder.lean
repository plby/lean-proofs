import Wikipedia.NoExoticSixSphere.SmoothManifoldHeightCylinder
import Wikipedia.HopfProblem.DegreeCollapseLowSurgeryBoundaryFrame

/-!

# Actual height cylinders with the low-surgery stabilization coordinates

The original native manifold dimension and the graph dimension are independent.
The exact distinguished height, original embedding derivative and original
normal columns plus graph axes are retained. Their range is the actual full
normal space of the cylinder, computed from its native derivative.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowHeightCylinder

open NoExoticSixSphere GLOrthonormalization StabilizedSpanningDisk

variable (d : ℕ) {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M)

def heightCylinder (p : M × ℝ) : Vector (e.ambientDimension + (1 + (1 + (d + 1)))) :=
  coordinates e.ambientDimension (d + 1) ((e.toFun p.1, p.2), 0)

theorem continuous_heightCylinder : Continuous (heightCylinder d e) :=
  (coordinates e.ambientDimension (d + 1)).continuous.comp
    (((e.closedEmbedding.continuous.comp continuous_fst).prodMk continuous_snd).prodMk
      continuous_const)

theorem injective_heightCylinder : Injective (heightCylinder d e) := by
  intro p q h
  have he := (coordinates e.ambientDimension (d + 1)).injective h
  have hm : e.toFun p.1 = e.toFun q.1 := congrArg (fun z ↦ z.1.1) he
  have ht : p.2 = q.2 := congrArg (fun z ↦ z.1.2) he
  exact Prod.ext (e.closedEmbedding.injective hm) ht

theorem isEmbedding_heightCylinder : IsEmbedding (heightCylinder d e) :=
  (coordinates e.ambientDimension (d + 1)).toHomeomorph.isEmbedding.comp
    ((isEmbedding_prodMkLeft (0 : ℝ × Vector (d + 1))).comp
      (e.closedEmbedding.isEmbedding.prodMap (IsEmbedding.id : IsEmbedding (id : ℝ → ℝ))))

theorem heightCylinder_zero (m : M) :
    (heightCylinder d e) (m, 0) =
      appendZeroMap e.ambientDimension (1 + (1 + (d + 1))) (e.toFun m) :=
  coordinates_old e.ambientDimension (d + 1) (e.toFun m)

theorem closedEmbedding_heightCylinder_slab [CompactSpace M] (l u : ℝ) :
    IsClosedEmbedding (fun p : M × Icc l u ↦ (heightCylinder d e) (p.1, p.2.val)) := by
  have hc : Continuous (fun p : M × Icc l u ↦ (heightCylinder d e) (p.1, p.2.val)) :=
    (continuous_heightCylinder d e).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  apply hc.isClosedEmbedding
  intro p q h
  have he := (injective_heightCylinder d e) h
  exact Prod.ext (congrArg (Prod.fst : M × ℝ → M) he)
    (Subtype.ext (congrArg (Prod.snd : M × ℝ → ℝ) he))

end Wikipedia.HopfProblem.DegreeCollapse.LowHeightCylinder

namespace Wikipedia.HopfProblem.DegreeCollapse.LowHeightCylinder

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable (d : ℕ) {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M)

theorem contMDiff_heightCylinder :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (e.ambientDimension + (1 + (1 + (d + 1))))) ∞
      (heightCylinder d e) :=
  (coordinates e.ambientDimension (d + 1)).contDiff.contMDiff.comp
    (((e.smooth.comp contMDiff_fst).prodMk_space contMDiff_snd).prodMk_space
      contMDiff_const)

theorem mfderiv_heightCylinder_apply (p : M × ℝ) (v : Vector n × ℝ) :
    mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (e.ambientDimension + (1 + (1 + (d + 1)))))
        (heightCylinder d e) p v =
      coordinates e.ambientDimension (d + 1)
        ((mfderiv (𝓡 n) (𝓡 e.ambientDimension) e.toFun p.1 v.1, v.2), 0) := by
  let F : M × ℝ → (Vector e.ambientDimension × ℝ) × (ℝ × Vector (d + 1)) :=
    fun q ↦ ((e.toFun q.1, q.2), 0)
  have hF : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, (Vector e.ambientDimension × ℝ) × (ℝ × Vector (d + 1))) ∞ F :=
    ((e.smooth.comp contMDiff_fst).prodMk_space contMDiff_snd).prodMk_space contMDiff_const
  let B : Vector n →L[ℝ] Vector e.ambientDimension :=
    mfderiv (𝓡 n) (𝓡 e.ambientDimension) e.toFun p.1
  have hBder : HasMFDerivAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 e.ambientDimension)
      (fun q : M × ℝ ↦ e.toFun q.1) p
      (B.comp (ContinuousLinearMap.fst ℝ (Vector n) ℝ)) := by
    exact (e.smooth.mdifferentiableAt (by simp)).hasMFDerivAt.comp p (hasMFDerivAt_fst p)
  have hSder : HasMFDerivAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (Prod.snd : M × ℝ → ℝ) p (ContinuousLinearMap.snd ℝ (Vector n) ℝ) :=
    hasMFDerivAt_snd p
  have hD : mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, (Vector e.ambientDimension × ℝ) × (ℝ × Vector (d + 1))) F p =
        ((B.comp (ContinuousLinearMap.fst ℝ (Vector n) ℝ)).prod
            (ContinuousLinearMap.snd ℝ (Vector n) ℝ)).prod 0 := by
    exact (hasMFDerivAt_prodMk_space (hasMFDerivAt_prodMk_space hBder hSder)
      (hasMFDerivAt_const (0 : ℝ × Vector (d + 1)) p)).mfderiv
  have hL : MDifferentiableAt 𝓘(ℝ, (Vector e.ambientDimension × ℝ) × (ℝ × Vector (d + 1)))
      (𝓡 (e.ambientDimension + (1 + (1 + (d + 1)))))
        (coordinates e.ambientDimension (d + 1)) (F p) :=
    (coordinates e.ambientDimension (d + 1)).differentiableAt.mdifferentiableAt
  have he : (heightCylinder d e) = (coordinates e.ambientDimension (d + 1)) ∘ F := rfl
  rw [he, mfderiv_comp p
    hL
    (hF.mdifferentiableAt (by simp)), mfderiv_eq_fderiv,
    (coordinates e.ambientDimension (d + 1)).hasFDerivAt.fderiv, hD]
  rfl

def heightCylinderDerivative (p : M × ℝ) :
    (Vector n × ℝ) →L[ℝ] Vector (e.ambientDimension + (1 + (1 + (d + 1)))) :=
  mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (e.ambientDimension + (1 + (1 + (d + 1))))) (heightCylinder d e) p

theorem heightCylinderDerivative_apply (p : M × ℝ) (v : Vector n × ℝ) :
    (heightCylinderDerivative d e) p v = coordinates e.ambientDimension (d + 1)
      ((mfderiv (𝓡 n) (𝓡 e.ambientDimension) e.toFun p.1 v.1, v.2), 0) :=
  (mfderiv_heightCylinder_apply d e) p v

theorem injective_heightCylinderDerivative (p : M × ℝ) :
    Injective ((heightCylinderDerivative d e) p) := by
  intro v w he
  rw [(heightCylinderDerivative_apply d e), (heightCylinderDerivative_apply d e)] at he
  have hp := (coordinates e.ambientDimension (d + 1)).injective he
  exact Prod.ext (e.injective_mfderiv p.1 (congrArg (fun z ↦ z.1.1) hp))
    (congrArg (fun z ↦ z.1.2) hp)

variable (a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel)

theorem heightCylinder_frame_normal (p : M × ℝ) :
    (LowSurgery.boundaryFrameOperator d (a.orthonormal p.1).val).range ≤
      ((heightCylinderDerivative d e) p).rangeᗮ := by
  have ha : (a.orthonormal p.1).val.range = e.normalFiber p.1 :=
    (a.orthonormal_range p.1).trans (e.range_normalProjection p.1)
  rintro _ ⟨w, rfl⟩
  apply (Submodule.mem_orthogonal _ _).mpr
  rintro _ ⟨v, rfl⟩
  change inner ℝ
    ((heightCylinderDerivative d e) p v)
    (LowSurgery.boundaryFrameOperator d (a.orthonormal p.1).val w) = 0
  rw [(heightCylinderDerivative_apply d e), LowSurgery.boundaryFrameOperator_apply,
    inner_coordinates]
  simp only [inner_zero_right, inner_zero_left, add_zero, Prod.fst_zero, Prod.snd_zero]
  exact Submodule.inner_right_of_mem_orthogonal
    (show _ ∈ e.tangentImage p.1 from ⟨v.1, rfl⟩) (ha.le ⟨_, rfl⟩)

theorem heightCylinder_frame_range (p : M × ℝ) :
    (LowSurgery.boundaryFrameOperator d (a.orthonormal p.1).val).range =
      ((heightCylinderDerivative d e) p).rangeᗮ := by
  let B : Vector ((e.ambientDimension - n) + (1 + (d + 1))) →L[ℝ]
      Vector (e.ambientDimension + (1 + (1 + (d + 1)))) :=
    LowSurgery.boundaryFrameOperator d (a.orthonormal p.1).val
  let D : (Vector n × ℝ) →L[ℝ] Vector (e.ambientDimension + (1 + (1 + (d + 1)))) :=
    (heightCylinderDerivative d e) p
  change B.range = D.rangeᗮ
  apply Submodule.eq_of_le_of_finrank_eq ((heightCylinder_frame_normal d e) a p)
  have hiB : Injective B := Stiefel.injective (LowSurgery.boundaryFrame d (a.orthonormal p.1))
  have hiD : Injective D := (injective_heightCylinderDerivative d e) p
  rw [LinearMap.finrank_range_of_inj hiB, finrank_euclideanSpace_fin]
  have hdim := D.range.finrank_add_finrank_orthogonal
  simp only [LinearMap.finrank_range_of_inj hiD, Module.finrank_prod,
    finrank_euclideanSpace_fin, Module.finrank_self] at hdim
  have hN := e.dimension_le_ambient p.1
  change (n + 1) + Module.finrank ℝ D.rangeᗮ = e.ambientDimension + (1 + (1 + (d + 1))) at hdim
  dsimp only [D] at hdim
  omega

end Wikipedia.HopfProblem.DegreeCollapse.LowHeightCylinder
