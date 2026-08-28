import Wikipedia.NoExoticSixSphere.ManifoldHeightCylinder

/-!
# The native smooth cylinder immersion and its actual normal frame

The product uses the original manifold atlas. Its derivative consists of
the original embedding derivative and the independent height direction.
The original normal columns and five graph axes span exactly its normal
space, not merely a chosen plane family.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere

theorem hasMFDerivAt_prodMk_space {E H X F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : X → F} {g : X → G} {x : X} {df : E →L[ℝ] F} {dg : E →L[ℝ] G}
    (hf : HasMFDerivAt I 𝓘(ℝ, F) f x df) (hg : HasMFDerivAt I 𝓘(ℝ, G) g x dg) :
    HasMFDerivAt I 𝓘(ℝ, F × G) (fun y ↦ (f y, g y)) x (df.prod dg) :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

end NoExoticSixSphere

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M)

theorem contMDiff_heightCylinder :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (e.ambientDimension + 6)) ∞ e.heightCylinder :=
  (coordinates e.ambientDimension 4).contDiff.contMDiff.comp
    (((e.smooth.comp contMDiff_fst).prodMk_space contMDiff_snd).prodMk_space
      contMDiff_const)

theorem mfderiv_heightCylinder_apply (p : M × ℝ) (v : Vector n × ℝ) :
    mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (e.ambientDimension + 6)) e.heightCylinder p v =
      coordinates e.ambientDimension 4
        ((mfderiv (𝓡 n) (𝓡 e.ambientDimension) e.toFun p.1 v.1, v.2), 0) := by
  let F : M × ℝ → (Vector e.ambientDimension × ℝ) × (ℝ × Vector 4) :=
    fun q ↦ ((e.toFun q.1, q.2), 0)
  have hF : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, (Vector e.ambientDimension × ℝ) × (ℝ × Vector 4)) ∞ F :=
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
      𝓘(ℝ, (Vector e.ambientDimension × ℝ) × (ℝ × Vector 4)) F p =
        ((B.comp (ContinuousLinearMap.fst ℝ (Vector n) ℝ)).prod
            (ContinuousLinearMap.snd ℝ (Vector n) ℝ)).prod 0 := by
    exact (hasMFDerivAt_prodMk_space (hasMFDerivAt_prodMk_space hBder hSder)
      (hasMFDerivAt_const (0 : ℝ × Vector 4) p)).mfderiv
  have hL : MDifferentiableAt 𝓘(ℝ, (Vector e.ambientDimension × ℝ) × (ℝ × Vector 4))
      (𝓡 (e.ambientDimension + 6)) (coordinates e.ambientDimension 4) (F p) :=
    (coordinates e.ambientDimension 4).differentiableAt.mdifferentiableAt
  have he : e.heightCylinder = (coordinates e.ambientDimension 4) ∘ F := rfl
  rw [he, mfderiv_comp p
    hL
    (hF.mdifferentiableAt (by simp)), mfderiv_eq_fderiv,
    (coordinates e.ambientDimension 4).hasFDerivAt.fderiv, hD]
  rfl

def heightCylinderDerivative (p : M × ℝ) :
    (Vector n × ℝ) →L[ℝ] Vector (e.ambientDimension + 6) :=
  mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (e.ambientDimension + 6)) e.heightCylinder p

theorem heightCylinderDerivative_apply (p : M × ℝ) (v : Vector n × ℝ) :
    e.heightCylinderDerivative p v = coordinates e.ambientDimension 4
      ((mfderiv (𝓡 n) (𝓡 e.ambientDimension) e.toFun p.1 v.1, v.2), 0) :=
  e.mfderiv_heightCylinder_apply p v

theorem injective_heightCylinderDerivative (p : M × ℝ) :
    Injective (e.heightCylinderDerivative p) := by
  intro v w he
  rw [e.heightCylinderDerivative_apply, e.heightCylinderDerivative_apply] at he
  have hp := (coordinates e.ambientDimension 4).injective he
  exact Prod.ext (e.injective_mfderiv p.1 (congrArg (fun z ↦ z.1.1) hp))
    (congrArg (fun z ↦ z.1.2) hp)

variable (a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel)

theorem heightCylinder_frame_normal (p : M × ℝ) :
    (boundaryFrameOperator (a.orthonormal p.1).val).range ≤
      (e.heightCylinderDerivative p).rangeᗮ := by
  have ha : (a.orthonormal p.1).val.range = e.normalFiber p.1 :=
    (a.orthonormal_range p.1).trans (e.range_normalProjection p.1)
  rintro _ ⟨w, rfl⟩
  apply (Submodule.mem_orthogonal _ _).mpr
  rintro _ ⟨v, rfl⟩
  change inner ℝ
    (e.heightCylinderDerivative p v)
    (boundaryFrameOperator (a.orthonormal p.1).val w) = 0
  rw [e.heightCylinderDerivative_apply, boundaryFrameOperator_apply, inner_coordinates]
  simp only [inner_zero_right, inner_zero_left, add_zero, Prod.fst_zero, Prod.snd_zero]
  exact Submodule.inner_right_of_mem_orthogonal
    (show _ ∈ e.tangentImage p.1 from ⟨v.1, rfl⟩) (ha.le ⟨_, rfl⟩)

theorem heightCylinder_frame_range (p : M × ℝ) :
    (boundaryFrameOperator (a.orthonormal p.1).val).range =
      (e.heightCylinderDerivative p).rangeᗮ := by
  let B : Vector ((e.ambientDimension - n) + 5) →L[ℝ] Vector (e.ambientDimension + 6) :=
    boundaryFrameOperator (a.orthonormal p.1).val
  let D : (Vector n × ℝ) →L[ℝ] Vector (e.ambientDimension + 6) :=
    e.heightCylinderDerivative p
  change B.range = D.rangeᗮ
  apply Submodule.eq_of_le_of_finrank_eq (e.heightCylinder_frame_normal a p)
  have hiB : Injective B := Stiefel.injective (boundaryFrame (a.orthonormal p.1))
  have hiD : Injective D := e.injective_heightCylinderDerivative p
  rw [LinearMap.finrank_range_of_inj hiB, finrank_euclideanSpace_fin]
  have hdim := D.range.finrank_add_finrank_orthogonal
  simp only [LinearMap.finrank_range_of_inj hiD, Module.finrank_prod,
    finrank_euclideanSpace_fin, Module.finrank_self] at hdim
  have hN := e.dimension_le_ambient p.1
  change (n + 1) + Module.finrank ℝ D.rangeᗮ = e.ambientDimension + 6 at hdim
  dsimp only [D] at hdim
  omega

end NoExoticSixSphere.EuclideanEmbedding
