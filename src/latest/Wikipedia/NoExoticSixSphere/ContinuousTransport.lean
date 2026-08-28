import Wikipedia.NoExoticSixSphere.ProjectionTransport

/-!
# Continuous transport and frames of projection ranges

This is the continuous version of ambient range transport. It is used for
topological homotopies, whose intermediate slices need not be smooth.
-/

namespace NoExoticSixSphere

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M]

/-- A continuous family of invertible ambient operators intertwining two operator families. -/
structure ContinuousRangeTransport (P Q : M → F →L[ℝ] F) where
  toFun : M → F →L[ℝ] F
  continuous : Continuous toFun
  invertible : ∀ x, (toFun x).IsInvertible
  intertwines : ∀ x, Q x * toFun x = toFun x * P x

namespace ContinuousRangeTransport

variable {P Q R : M → F →L[ℝ] F}

/-- Identity transport. -/
noncomputable def refl (P : M → F →L[ℝ] F) : ContinuousRangeTransport P P where
  toFun _ := 1
  continuous := continuous_const
  invertible _ := ⟨ContinuousLinearEquiv.refl ℝ F, rfl⟩
  intertwines _ := by rw [mul_one, one_mul]

/-- Continuous transports compose in their natural order. -/
noncomputable def trans (a : ContinuousRangeTransport P Q) (b : ContinuousRangeTransport Q R) :
    ContinuousRangeTransport P R where
  toFun x := b.toFun x * a.toFun x
  continuous := b.continuous.clm_comp a.continuous
  invertible x := (b.invertible x).comp (a.invertible x)
  intertwines x := by
    calc
      R x * (b.toFun x * a.toFun x) = (R x * b.toFun x) * a.toFun x :=
        (mul_assoc _ _ _).symm
      _ = (b.toFun x * Q x) * a.toFun x := by rw [b.intertwines x]
      _ = b.toFun x * (Q x * a.toFun x) := mul_assoc _ _ _
      _ = b.toFun x * (a.toFun x * P x) := by rw [a.intertwines x]
      _ = (b.toFun x * a.toFun x) * P x := (mul_assoc _ _ _).symm

/-- The inverse of an everywhere-invertible continuous operator family is continuous. -/
theorem continuous_inverse [CompleteSpace F] (a : ContinuousRangeTransport P Q) :
    Continuous (fun x ↦ (a.toFun x).inverse) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact ContinuousAt.comp (f := a.toFun) (x := x)
    ((a.invertible x).contDiffAt_map_inverse (n := 0)).continuousAt a.continuous.continuousAt

/-- Continuous ambient transport can be reversed. -/
noncomputable def symm [CompleteSpace F] (a : ContinuousRangeTransport P Q) :
    ContinuousRangeTransport Q P where
  toFun x := (a.toFun x).inverse
  continuous := a.continuous_inverse
  invertible x := (a.invertible x).inverse
  intertwines x := by
    apply ContinuousLinearMap.ext
    intro v
    change P x ((a.toFun x).inverse v) = (a.toFun x).inverse (Q x v)
    apply (a.invertible x).injective
    rw [(a.invertible x).self_apply_inverse]
    have h := congrArg (fun L : F →L[ℝ] F ↦ L ((a.toFun x).inverse v)) (a.intertwines x)
    change Q x (a.toFun x ((a.toFun x).inverse v)) = a.toFun x (P x ((a.toFun x).inverse v)) at h
    rw [(a.invertible x).self_apply_inverse] at h
    exact h.symm

/-- Intertwining and invertibility identify the actual ranges. -/
theorem map_range (a : ContinuousRangeTransport P Q) (x : M) :
    Submodule.map (a.toFun x).toLinearMap (P x).range = (Q x).range := by
  rw [← LinearMap.range_comp]
  have hlin : (a.toFun x).toLinearMap.comp (P x).toLinearMap =
      (Q x).toLinearMap.comp (a.toFun x).toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap (a.intertwines x).symm
  rw [hlin]
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (a.invertible x).surjective)

/-- Continuous ambient transport restricts to equivalences of its actual range fibers. -/
noncomputable def rangeEquiv (a : ContinuousRangeTransport P Q) (x : M) :
    (P x).range ≃L[ℝ] (Q x).range :=
  (invertibleOperatorEquiv (a.toFun x) (a.invertible x)).ofSubmodules
    (P x).range (Q x).range (a.map_range x)

/-- The explicit projection intertwiner supplies transport whenever it is invertible. -/
noncomputable def ofProjections
    (hP : ∀ x, IsIdempotentElem (P x)) (hQ : ∀ x, IsIdempotentElem (Q x))
    (hcP : Continuous P) (hcQ : Continuous Q)
    (hinv : ∀ x, (projectionIntertwiner (P x) (Q x)).IsInvertible) :
    ContinuousRangeTransport P Q where
  toFun x := projectionIntertwiner (P x) (Q x)
  continuous := (hcQ.clm_comp hcP).add
    ((continuous_const.sub hcQ).clm_comp (continuous_const.sub hcP))
  invertible := hinv
  intertwines x := projectionIntertwiner_intertwines (P x) (Q x) (hP x) (hQ x)

end ContinuousRangeTransport

/-- A global continuous frame of actual projection ranges. -/
structure ContinuousRangeFrame (P : M → F →L[ℝ] F) (K : Type*)
    [NormedAddCommGroup K] [NormedSpace ℝ K] where
  equiv : ∀ x, K ≃L[ℝ] (P x).range
  continuous : Continuous (fun x ↦ (P x).range.subtypeL.comp (equiv x).toContinuousLinearMap)

/-- A continuous range frame pulls back along an arbitrary continuous base map. -/
noncomputable def ContinuousRangeFrame.comap
    {K X : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K] [TopologicalSpace X]
    {P : M → F →L[ℝ] F} (a : ContinuousRangeFrame P K) (f : X → M) (hf : Continuous f) :
    ContinuousRangeFrame (fun x ↦ P (f x)) K where
  equiv x := a.equiv (f x)
  continuous := a.continuous.comp hf

/-- Transporting a fixed basis gives a continuous frame on the endpoint ranges. -/
noncomputable def continuousFrameOfConstantTransport
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    {P₀ : F →L[ℝ] F} {Q : M → F →L[ℝ] F}
    (a : ContinuousRangeTransport (fun _ ↦ P₀) Q) (q : K ≃L[ℝ] P₀.range) :
    ContinuousRangeFrame Q K where
  equiv x := q.trans (a.rangeEquiv x)
  continuous := by
    have heq : (fun x ↦ (Q x).range.subtypeL.comp
        (q.trans (a.rangeEquiv x)).toContinuousLinearMap) =
        (fun x ↦ (a.toFun x).comp (P₀.range.subtypeL.comp q.toContinuousLinearMap)) := by
      funext x
      apply ContinuousLinearMap.ext
      intro v
      rfl
    rw [heq]
    exact a.continuous.clm_comp continuous_const

end NoExoticSixSphere
