import Wikipedia.NoExoticSixSphere.ProjectionTransport

/-!
# Smooth ambient transport between operator ranges

Smooth invertible ambient operators that intertwine two operator families
identify their ranges. Such transports compose and invert. These facts support
the homotopy-invariance argument for smooth projection bundles.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- A smooth family of invertible ambient operators intertwining two operator families. -/
structure SmoothRangeTransport (I : ModelWithCorners ℝ B H)
    (P Q : M → F →L[ℝ] F) where
  toFun : M → F →L[ℝ] F
  smooth : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ toFun
  invertible : ∀ x, (toFun x).IsInvertible
  intertwines : ∀ x, Q x * toFun x = toFun x * P x

namespace SmoothRangeTransport

variable {P Q R : M → F →L[ℝ] F}

/-- Identity transport. -/
noncomputable def refl (P : M → F →L[ℝ] F) : SmoothRangeTransport I P P where
  toFun _ := 1
  smooth := contMDiff_const
  invertible _ := ⟨ContinuousLinearEquiv.refl ℝ F, rfl⟩
  intertwines x := by rw [mul_one, one_mul]

/-- Smooth transports compose in their natural order. -/
noncomputable def trans (a : SmoothRangeTransport I P Q) (b : SmoothRangeTransport I Q R) :
    SmoothRangeTransport I P R where
  toFun x := b.toFun x * a.toFun x
  smooth := b.smooth.clm_comp a.smooth
  invertible x := (b.invertible x).comp (a.invertible x)
  intertwines x := by
    calc
      R x * (b.toFun x * a.toFun x) = (R x * b.toFun x) * a.toFun x :=
        (mul_assoc _ _ _).symm
      _ = (b.toFun x * Q x) * a.toFun x := by rw [b.intertwines x]
      _ = b.toFun x * (Q x * a.toFun x) := mul_assoc _ _ _
      _ = b.toFun x * (a.toFun x * P x) := by rw [a.intertwines x]
      _ = (b.toFun x * a.toFun x) * P x := (mul_assoc _ _ _).symm

/-- The inverse family of an everywhere-invertible smooth transport is smooth. -/
theorem contMDiff_inverse (a : SmoothRangeTransport I P Q) :
    ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ (fun x ↦ (a.toFun x).inverse) := by
  intro x
  exact ContDiffAt.comp_contMDiffAt (f := a.toFun) (x := x)
    (a.invertible x).contDiffAt_map_inverse a.smooth.contMDiffAt

/-- Smooth transport can be reversed. -/
noncomputable def symm (a : SmoothRangeTransport I P Q) : SmoothRangeTransport I Q P where
  toFun x := (a.toFun x).inverse
  smooth := a.contMDiff_inverse
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

omit [CompleteSpace F] in
/-- The intertwining identity and invertibility identify the actual ranges. -/
theorem map_range (a : SmoothRangeTransport I P Q) (x : M) :
    Submodule.map (a.toFun x).toLinearMap (P x).range = (Q x).range := by
  rw [← LinearMap.range_comp]
  have hlin : (a.toFun x).toLinearMap.comp (P x).toLinearMap =
      (Q x).toLinearMap.comp (a.toFun x).toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap (a.intertwines x).symm
  rw [hlin]
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (a.invertible x).surjective)

/-- Smooth ambient transport restricts to a continuous linear equivalence of the actual fibers. -/
noncomputable def rangeEquiv (a : SmoothRangeTransport I P Q) (x : M) :
    (P x).range ≃L[ℝ] (Q x).range :=
  (invertibleOperatorEquiv (a.toFun x) (a.invertible x)).ofSubmodules
    (P x).range (Q x).range (a.map_range x)

/-- The explicit intertwiner supplies transport whenever it is everywhere invertible. -/
noncomputable def ofProjections
    (hP : ∀ x, IsIdempotentElem (P x)) (hQ : ∀ x, IsIdempotentElem (Q x))
    (hsP : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ P)
    (hsQ : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ Q)
    (hinv : ∀ x, (projectionIntertwiner (P x) (Q x)).IsInvertible) :
    SmoothRangeTransport I P Q where
  toFun x := projectionIntertwiner (P x) (Q x)
  smooth := (hsQ.clm_comp hsP).add
    ((contMDiff_const.sub hsQ).clm_comp (contMDiff_const.sub hsP))
  invertible := hinv
  intertwines x := projectionIntertwiner_intertwines (P x) (Q x) (hP x) (hQ x)

end SmoothRangeTransport

end NoExoticSixSphere
