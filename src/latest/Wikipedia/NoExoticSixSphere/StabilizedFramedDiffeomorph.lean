import Wikipedia.NoExoticSixSphere.FramedBlockAssociativity
import Wikipedia.NoExoticSixSphere.SmoothFrameCoordinates
import Wikipedia.NoExoticSixSphere.NormalBundle

/-!
# Actual stabilized framed diffeomorphisms and their composition

A comparison consists of a native smooth diffeomorphism and fixed ambient
and normal-coordinate isometries identifying the actual embeddings and
frames after ordinary coordinate stabilization. Composition constructs one
such endpoint comparison with the sum of the two numbers of added axes.
Only a comparison adding no axes is inverted without further stabilization.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere

open GLOrthonormalization Stiefel OrthogonalFrameAppend

structure StabilizedFramedDiffeomorph {n : ℕ} {M M' : Type*}
    [TopologicalSpace M] [ChartedSpace (Vector n) M]
    [TopologicalSpace M'] [ChartedSpace (Vector n) M']
    (e : EuclideanEmbedding n M) (a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel)
    (e' : EuclideanEmbedding n M')
    (a' : SmoothRangeFrame (𝓡 n) e'.normalProjection e'.NormalModel) where
  extra : ℕ
  ambient : Vector (e.ambientDimension + extra) ≃ₗᵢ[ℝ] Vector e'.ambientDimension
  normal : Vector ((e.ambientDimension - n) + extra) ≃ₗᵢ[ℝ]
    Vector (e'.ambientDimension - n)
  diffeomorph : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ M'
  embedding_eq : ∀ x, e'.toFun (diffeomorph x) =
    ambient (appendZeroMap e.ambientDimension extra (e.toFun x))
  frame_eq : ∀ x v, a'.ambient (diffeomorph x) (normal v) =
    ambient (BlockSum.operator extra (a.ambient x) v)

namespace StabilizedFramedDiffeomorph

variable {n : ℕ} {M₁ M₂ M₃ : Type*}
  [TopologicalSpace M₁] [ChartedSpace (Vector n) M₁]
  [TopologicalSpace M₂] [ChartedSpace (Vector n) M₂]
  [TopologicalSpace M₃] [ChartedSpace (Vector n) M₃]
  {e₁ : EuclideanEmbedding n M₁} {e₂ : EuclideanEmbedding n M₂}
  {e₃ : EuclideanEmbedding n M₃}
  {a₁ : SmoothRangeFrame (𝓡 n) e₁.normalProjection e₁.NormalModel}
  {a₂ : SmoothRangeFrame (𝓡 n) e₂.normalProjection e₂.NormalModel}
  {a₃ : SmoothRangeFrame (𝓡 n) e₃.normalProjection e₃.NormalModel}

def ofReverseNormal (k : ℕ) (D : M₁ ≃ₘ⟮𝓡 n, 𝓡 n⟯ M₂)
    (J : Vector (e₁.ambientDimension + k) ≃ₗᵢ[ℝ] Vector e₂.ambientDimension)
    (Q : Vector (e₂.ambientDimension - n) ≃ₗᵢ[ℝ] Vector ((e₁.ambientDimension - n) + k))
    (he : ∀ x, e₂.toFun (D x) = J (appendZeroMap e₁.ambientDimension k (e₁.toFun x)))
    (hf : ∀ x v, a₂.ambient (D x) v = J (BlockSum.operator k (a₁.ambient x) (Q v))) :
    StabilizedFramedDiffeomorph e₁ a₁ e₂ a₂ where
  extra := k
  ambient := J
  normal := Q.symm
  diffeomorph := D
  embedding_eq := he
  frame_eq x v := (hf x (Q.symm v)).trans
    (congrArg (fun w ↦ J (BlockSum.operator k (a₁.ambient x) w)) (Q.apply_symm_apply v))

def refl (e : EuclideanEmbedding n M₁)
    (a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel) :
    StabilizedFramedDiffeomorph e a e a where
  extra := 0
  ambient := LinearIsometryEquiv.refl ℝ (Vector e.ambientDimension)
  normal := LinearIsometryEquiv.refl ℝ (Vector (e.ambientDimension - n))
  diffeomorph := Diffeomorph.refl (𝓡 n) M₁ ∞
  embedding_eq x := by
    change e.toFun x = appendZeroMap e.ambientDimension 0 (e.toFun x)
    exact (FramedBlock.appendZero_zero e.ambientDimension (e.toFun x)).symm
  frame_eq x v := by
    change a.ambient x v = BlockSum.operator 0 (a.ambient x) v
    rw [BlockSum.operator_zero]

def trans (F : StabilizedFramedDiffeomorph e₁ a₁ e₂ a₂)
    (G : StabilizedFramedDiffeomorph e₂ a₂ e₃ a₃) :
    StabilizedFramedDiffeomorph e₁ a₁ e₃ a₃ where
  extra := F.extra + G.extra
  ambient := (FramedBlock.associator e₁.ambientDimension F.extra G.extra).symm.trans
    ((extendColumnChange F.ambient G.extra).trans G.ambient)
  normal := (FramedBlock.associator (e₁.ambientDimension - n) F.extra G.extra).symm.trans
    ((extendColumnChange F.normal G.extra).trans G.normal)
  diffeomorph := F.diffeomorph.trans G.diffeomorph
  embedding_eq x := by
    change e₃.toFun (G.diffeomorph (F.diffeomorph x)) =
      G.ambient (extendColumnChange F.ambient G.extra
        ((FramedBlock.associator e₁.ambientDimension F.extra G.extra).symm
          (appendZeroMap e₁.ambientDimension (F.extra + G.extra) (e₁.toFun x))))
    rw [G.embedding_eq, F.embedding_eq]
    apply congrArg G.ambient
    rw [← FramedBlock.extend_appendZero F.ambient G.extra]
    apply congrArg (extendColumnChange F.ambient G.extra)
    apply (FramedBlock.associator e₁.ambientDimension F.extra G.extra).injective
    rw [LinearIsometryEquiv.apply_symm_apply, FramedBlock.appendZero_assoc]
  frame_eq x v := by
    change a₃.ambient (G.diffeomorph (F.diffeomorph x))
        (G.normal (extendColumnChange F.normal G.extra
          ((FramedBlock.associator (e₁.ambientDimension - n) F.extra G.extra).symm v))) =
      G.ambient (extendColumnChange F.ambient G.extra
        ((FramedBlock.associator e₁.ambientDimension F.extra G.extra).symm
          (BlockSum.operator (F.extra + G.extra) (a₁.ambient x) v)))
    rw [G.frame_eq]
    apply congrArg G.ambient
    rw [FramedBlock.block_natural G.extra (BlockSum.operator F.extra (a₁.ambient x))
      (a₂.ambient (F.diffeomorph x)) F.ambient F.normal (F.frame_eq x)]
    apply congrArg (extendColumnChange F.ambient G.extra)
    apply (FramedBlock.associator e₁.ambientDimension F.extra G.extra).injective
    rw [LinearIsometryEquiv.apply_symm_apply, FramedBlock.operator_assoc,
      LinearIsometryEquiv.apply_symm_apply]

theorem trans_diffeomorph (F : StabilizedFramedDiffeomorph e₁ a₁ e₂ a₂)
    (G : StabilizedFramedDiffeomorph e₂ a₂ e₃ a₃) :
    (F.trans G).diffeomorph = F.diffeomorph.trans G.diffeomorph := rfl

theorem trans_extra (F : StabilizedFramedDiffeomorph e₁ a₁ e₂ a₂)
    (G : StabilizedFramedDiffeomorph e₂ a₂ e₃ a₃) :
    (F.trans G).extra = F.extra + G.extra := rfl

theorem frame_eq_of_source_columns (F : StabilizedFramedDiffeomorph e₁ a₁ e₂ a₂)
    (x : M₁) {k : ℕ} (C : Vector k →L[ℝ] Vector e₁.ambientDimension)
    (Q : Vector (e₁.ambientDimension - n) ≃ₗᵢ[ℝ] Vector k)
    (h : a₁.ambient x = C.comp Q.toContinuousLinearMap)
    (v : Vector ((e₁.ambientDimension - n) + F.extra)) :
    a₂.ambient (F.diffeomorph x) (F.normal v) =
      F.ambient (BlockSum.operator F.extra C (extendColumnChange Q F.extra v)) := by
  rw [F.frame_eq, h, block_comp_columnChange]
  rfl

def symmOfZero (F : StabilizedFramedDiffeomorph e₁ a₁ e₂ a₂) (h : F.extra = 0) :
    StabilizedFramedDiffeomorph e₂ a₂ e₁ a₁ := by
  rcases F with ⟨k, J, Q, D, he, hf⟩
  change k = 0 at h
  subst k
  refine
    { extra := 0
      ambient := J.symm
      normal := Q.symm
      diffeomorph := D.symm
      embedding_eq := ?_
      frame_eq := ?_ }
  · intro y
    change e₁.toFun (D.symm y) = J.symm (appendZeroMap e₂.ambientDimension 0 (e₂.toFun y))
    rw [FramedBlock.appendZero_zero]
    apply J.injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    have hxy := he (D.symm y)
    rw [D.apply_symm_apply, FramedBlock.appendZero_zero] at hxy
    exact hxy.symm
  · intro y v
    change a₁.ambient (D.symm y) (Q.symm v) = J.symm (BlockSum.operator 0 (a₂.ambient y) v)
    rw [BlockSum.operator_zero]
    apply J.injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    have hxy := hf (D.symm y) (Q.symm v)
    rw [D.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply, BlockSum.operator_zero] at hxy
    exact hxy.symm

end StabilizedFramedDiffeomorph
end NoExoticSixSphere
