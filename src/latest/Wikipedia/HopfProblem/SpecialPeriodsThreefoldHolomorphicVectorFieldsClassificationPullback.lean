import Wikipedia.HopfProblem.HolomorphicVectorFields
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Native holomorphic vector-field pullback

A local biholomorphism pulls back a genuine holomorphic tangent section
by the inverse of its actual manifold differential.
-/

open Bundle Set
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification

variable {E M F N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℂ, F) ω N]

local notation "IM" => modelWithCornersSelf ℂ E
local notation "IN" => modelWithCornersSelf ℂ F

omit [CompleteSpace E] [IsManifold IM ω M] [IsManifold IN ω N] in
theorem localDiffeomorph_mfderiv_isInvertible (f : M → N)
    (hf : IsLocalDiffeomorph IM IN ω f) (x : M) :
    (mfderiv IM IN f x).IsInvertible :=
  ⟨(hf x).mfderivToContinuousLinearEquiv (by simp), rfl⟩

/-- The inverse differential applied to the original tangent section. -/
noncomputable def pullback (f : M → N) (hf : IsLocalDiffeomorph IM IN ω f)
    (v : Wikipedia.HopfProblem.HolomorphicVectorFields.Field F N) :
    Wikipedia.HopfProblem.HolomorphicVectorFields.Field E M where
  toFun := VectorField.mpullback IM IN f v
  contMDiff_toFun := v.contMDiff.mpullback_vectorField hf.contMDiff
    (localDiffeomorph_mfderiv_isInvertible f hf) (by simp)

theorem pullback_apply (f : M → N) (hf : IsLocalDiffeomorph IM IN ω f)
    (v : Wikipedia.HopfProblem.HolomorphicVectorFields.Field F N) (x : M) :
    pullback f hf v x = (mfderiv IM IN f x).inverse (v (f x)) := rfl

/-- The pulled-back vector is carried to the original vector by the
genuine differential, without any prescribed coordinate formula. -/
theorem pullback_map (f : M → N) (hf : IsLocalDiffeomorph IM IN ω f)
    (v : Wikipedia.HopfProblem.HolomorphicVectorFields.Field F N) (x : M) :
    mfderiv IM IN f x (pullback f hf v x) = v (f x) := by
  let e := (hf x).mfderivToContinuousLinearEquiv (by simp)
  change e ((e : TangentSpace IM x →L[ℂ] TangentSpace IN (f x)).inverse (v (f x))) = _
  rw [ContinuousLinearMap.inverse_equiv]
  exact e.apply_symm_apply _

/-- A lifted tangent value is uniquely specified by its differential image. -/
theorem pullback_eq_iff (f : M → N) (hf : IsLocalDiffeomorph IM IN ω f)
    (v : Wikipedia.HopfProblem.HolomorphicVectorFields.Field F N) (x : M)
    (u : TangentSpace IM x) :
    pullback f hf v x = u ↔ mfderiv IM IN f x u = v (f x) := by
  rw [pullback_apply]
  exact (localDiffeomorph_mfderiv_isInvertible f hf x).inverse_apply_eq.trans eq_comm

/-- A deck map preserves the native pullback through its actual differential. -/
theorem pullback_covariant (f : M → N) (hf : IsLocalDiffeomorph IM IN ω f)
    (v : Wikipedia.HopfProblem.HolomorphicVectorFields.Field F N)
    (g : M → M) (hg : ContMDiff IM IM ω g) (hfg : ∀ x, f (g x) = f x) (x : M) :
    mfderiv IM IM g x (pullback f hf v x) = pullback f hf v (g x) := by
  apply ((hf (g x)).mfderivToContinuousLinearEquiv (by simp)).injective
  change mfderiv IM IN f (g x) (mfderiv IM IM g x (pullback f hf v x)) =
    mfderiv IM IN f (g x) (pullback f hf v (g x))
  rw [pullback_map]
  have hcomp : f ∘ g = f := funext hfg
  rw [← ContinuousLinearMap.comp_apply,
    ← mfderiv_comp x (hf.contMDiff.mdifferentiable (by simp) (g x))
      (hg.mdifferentiable (by simp) x), hcomp]
  exact (pullback_map f hf v x).trans
    (congrArg (fun y => (v y : F)) (hfg x).symm)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification
