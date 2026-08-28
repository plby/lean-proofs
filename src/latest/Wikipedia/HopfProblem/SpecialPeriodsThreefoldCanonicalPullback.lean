import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalLocalFrames
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Intrinsic canonical pullback along actual local biholomorphisms

The canonical fibre comparison is defined by pulling continuous alternating
top covectors back along the actual manifold derivative.  A local
biholomorphism makes this map a continuous linear equivalence.  In particular,
the construction applies directly to a patch inclusion into a larger
manifold, not just to a diffeomorphism with the open patch as its codomain.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Pullback

local notation "I" => modelWithCornersSelf ℂ Model

variable {M N P : Type*}
  [TopologicalSpace M] [ChartedSpace Model M] [IsManifold I ω M]
  [TopologicalSpace N] [ChartedSpace Model N] [IsManifold I ω N]
  [TopologicalSpace P] [ChartedSpace Model P] [IsManifold I ω P]

/-- Pullback on the genuine canonical fibres, using the actual `mfderiv`. -/
def pullbackLinear (f : M → N) (x : M) :
    (Atlas.core N).Fiber (f x) →L[ℂ] (Atlas.core M).Fiber x :=
  (Atlas.intrinsicEquiv M x).symm.toContinuousLinearMap.comp
    ((ContinuousAlternatingMap.compContinuousLinearMapCLM (mfderiv I I f x)).comp
      (Atlas.intrinsicEquiv N (f x)).toContinuousLinearMap)

/-- The intrinsic top covector is exactly derivative pullback. -/
theorem intrinsic_pullbackLinear (f : M → N) (x : M)
    (v : (Atlas.core N).Fiber (f x)) :
    Atlas.intrinsicEquiv M x (pullbackLinear f x v) =
      (Atlas.intrinsicEquiv N (f x) v).compContinuousLinearMap (mfderiv I I f x) := by
  change (Atlas.intrinsicEquiv M x) ((Atlas.intrinsicEquiv M x).symm _) = _
  exact (Atlas.intrinsicEquiv M x).apply_symm_apply _

/-- In the preferred tangent coordinates, the coefficient is multiplied by
the determinant of the actual manifold derivative. -/
theorem pullbackLinear_preferred_coefficient (f : M → N) (x : M)
    (v : (Atlas.core N).Fiber (f x)) :
    id (α := ℂ) (pullbackLinear f x v) =
      LinearMap.det (mfderiv I I f x).toLinearMap * id (α := ℂ) v := by
  change coefficientEquiv.symm
    ((coefficientEquiv (id (α := ℂ) v)).compContinuousLinearMap (mfderiv I I f x)) = _
  exact (congrArg coefficientEquiv.symm
    (coefficientEquiv_pullback (id (α := ℂ) v) (mfderiv I I f x))).trans
      (coefficientEquiv.symm_apply_apply _)

/-- A local biholomorphism gives an isomorphism of the actual canonical
fibres by the contravariant continuous alternating-map construction. -/
def pullbackEquivAt {f : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I I ω f x) :
    (Atlas.core N).Fiber (f x) ≃L[ℂ] (Atlas.core M).Fiber x :=
  ((Atlas.intrinsicEquiv N (f x)).trans
    (hf.mfderivToContinuousLinearEquiv (by simp)).symm.continuousAlternatingMapCongrLeft).trans
      (Atlas.intrinsicEquiv M x).symm

@[simp] theorem pullbackEquivAt_apply {f : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I I ω f x) (v : (Atlas.core N).Fiber (f x)) :
    pullbackEquivAt hf v = pullbackLinear f x v := rfl

theorem intrinsic_pullbackEquivAt {f : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I I ω f x) (v : (Atlas.core N).Fiber (f x)) :
    Atlas.intrinsicEquiv M x (pullbackEquivAt hf v) =
      (Atlas.intrinsicEquiv N (f x) v).compContinuousLinearMap (mfderiv I I f x) :=
  intrinsic_pullbackLinear f x v

/-- A fibre comparison directly over a global local biholomorphism, such as
a genuine holomorphic patch inclusion. -/
def pullbackEquiv {f : M → N} (hf : IsLocalDiffeomorph I I ω f) (x : M) :
    (Atlas.core N).Fiber (f x) ≃L[ℂ] (Atlas.core M).Fiber x := pullbackEquivAt (hf x)

@[simp] theorem pullbackEquiv_apply {f : M → N} (hf : IsLocalDiffeomorph I I ω f)
    (x : M) (v : (Atlas.core N).Fiber (f x)) :
    pullbackEquiv hf x v = pullbackLinear f x v := rfl

theorem intrinsic_pullbackEquiv {f : M → N} (hf : IsLocalDiffeomorph I I ω f)
    (x : M) (v : (Atlas.core N).Fiber (f x)) :
    Atlas.intrinsicEquiv M x (pullbackEquiv hf x v) =
      (Atlas.intrinsicEquiv N (f x) v).compContinuousLinearMap (mfderiv I I f x) :=
  intrinsic_pullbackLinear f x v

/-- The inverse comparison is inverse pullback on genuine tangent covectors. -/
theorem intrinsic_pullbackEquivAt_symm {f : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I I ω f x) (v : (Atlas.core M).Fiber x) :
    Atlas.intrinsicEquiv N (f x) ((pullbackEquivAt hf).symm v) =
      (Atlas.intrinsicEquiv M x v).compContinuousLinearMap
        (hf.mfderivToContinuousLinearEquiv (by simp)).symm.toContinuousLinearMap := by
  simp only [pullbackEquivAt, ContinuousLinearEquiv.symm_trans_apply,
    ContinuousLinearEquiv.symm_symm, ContinuousLinearEquiv.apply_symm_apply]
  rfl

@[simp] theorem pullbackLinear_id (x : M) :
    pullbackLinear (id : M → M) x = ContinuousLinearMap.id ℂ ((Atlas.core M).Fiber x) := by
  apply ContinuousLinearMap.ext
  intro v
  change id (α := ℂ) (pullbackLinear (id : M → M) x v) = id (α := ℂ) v
  have h : LinearMap.det (mfderiv I I (id : M → M) x).toLinearMap = 1 := by
    rw [mfderiv_id]
    exact LinearMap.det_id
  exact (pullbackLinear_preferred_coefficient (id : M → M) x v).trans
    (by rw [h, one_mul])

/-- The native chain rule gives contravariant composition of canonical
pullback.  No determinant cocycle is supplied as data. -/
theorem pullbackLinear_comp {f : M → N} {g : N → P} {x : M}
    (hf : MDifferentiableAt I I f x) (hg : MDifferentiableAt I I g (f x)) :
    pullbackLinear (g ∘ f) x = (pullbackLinear f x).comp (pullbackLinear g (f x)) := by
  apply ContinuousLinearMap.ext
  intro v
  apply (Atlas.intrinsicEquiv M x).injective
  calc
    Atlas.intrinsicEquiv M x (pullbackLinear (g ∘ f) x v) =
        (Atlas.intrinsicEquiv P (g (f x)) v).compContinuousLinearMap
          (mfderiv I I (g ∘ f) x) := intrinsic_pullbackLinear (g ∘ f) x v
    _ = (Atlas.intrinsicEquiv P (g (f x)) v).compContinuousLinearMap
          ((mfderiv I I g (f x)).comp (mfderiv I I f x)) :=
      congrArg (fun A : Model →L[ℂ] Model =>
        (Atlas.intrinsicEquiv P (g (f x)) v).compContinuousLinearMap A)
          (mfderiv_comp x hg hf)
    _ = ((Atlas.intrinsicEquiv P (g (f x)) v).compContinuousLinearMap
          (mfderiv I I g (f x))).compContinuousLinearMap (mfderiv I I f x) := rfl
    _ = (Atlas.intrinsicEquiv N (f x) (pullbackLinear g (f x) v)).compContinuousLinearMap
          (mfderiv I I f x) :=
      congrArg (fun α : Atlas.IntrinsicTopCovector N (f x) =>
        α.compContinuousLinearMap (mfderiv I I f x))
          (intrinsic_pullbackLinear g (f x) v).symm
    _ = Atlas.intrinsicEquiv M x
          (pullbackLinear f x (pullbackLinear g (f x) v)) :=
      (intrinsic_pullbackLinear f x (pullbackLinear g (f x) v)).symm

/-- Pointwise compatibility with composition of local biholomorphisms. -/
theorem pullbackEquiv_comp {f : M → N} {g : N → P}
    (hf : IsLocalDiffeomorph I I ω f) (hg : IsLocalDiffeomorph I I ω g)
    (x : M) (v : (Atlas.core P).Fiber (g (f x))) :
    pullbackEquiv (fun y => IsLocalDiffeomorphAt.comp (K := I) (P := P)
      (hf y) (hg (f y))) x v =
      pullbackEquiv hf x (pullbackEquiv hg (f x) v) := by
  simp only [pullbackEquiv_apply]
  exact congrArg (fun A => A v) (pullbackLinear_comp ((hf x).mdifferentiableAt (by simp))
    ((hg (f x)).mdifferentiableAt (by simp)))

/-- The derivative-pullback comparison for an actual analytic diffeomorphism. -/
def diffeomorphPullback (e : Diffeomorph I I M N ω) (x : M) :
    (Atlas.core N).Fiber (e x) ≃L[ℂ] (Atlas.core M).Fiber x :=
  pullbackEquiv e.isLocalDiffeomorph x

@[simp] theorem diffeomorphPullback_apply (e : Diffeomorph I I M N ω) (x : M)
    (v : (Atlas.core N).Fiber (e x)) :
    diffeomorphPullback e x v = pullbackLinear e x v := rfl

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Pullback
