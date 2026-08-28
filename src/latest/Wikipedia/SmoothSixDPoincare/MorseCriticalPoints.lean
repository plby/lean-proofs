import Wikipedia.SmoothSixDPoincare.MorsePerturbation
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.DiscreteSubset

/-!
# Isolated and finite critical points

The isolation proof applies the inverse function theorem to the actual first
derivative, whose derivative is the nondegenerate Hessian. Compactness then
gives finiteness. No critical-point finiteness is postulated.
-/

noncomputable section

open Set
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.MorsePerturbation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def criticalPoints (f : E → ℝ) : Set E := {x | fderiv ℝ f x = 0}

/-- A nondegenerate actual Hessian supplies a continuous linear equivalence. -/
def hessianEquiv (f : E → ℝ) (x : E)
    (h : Function.Bijective (fderiv ℝ (fderiv ℝ f) x)) :
    E ≃L[ℝ] (E →L[ℝ] ℝ) :=
  (LinearEquiv.ofBijective (fderiv ℝ (fderiv ℝ f) x).toLinearMap h).toContinuousLinearEquiv

@[simp] theorem hessianEquiv_toContinuousLinearMap (f : E → ℝ) (x : E)
    (h : Function.Bijective (fderiv ℝ (fderiv ℝ f) x)) :
    (hessianEquiv f x h).toContinuousLinearMap = fderiv ℝ (fderiv ℝ f) x := by
  ext v w
  rfl

omit [FiniteDimensional ℝ E] in
theorem criticalPoints_isClosed {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    IsClosed (criticalPoints f) :=
  isClosed_eq (contDiff_fderiv hf).continuous continuous_const

theorem criticalPoints_isDiscrete {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hm : IsMorse f) :
    IsDiscrete (criticalPoints f) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  let L := hessianEquiv f x (hm x hx)
  have hdf := contDiff_fderiv hf
  have hL : HasFDerivAt (fderiv ℝ f) L.toContinuousLinearMap x := by
    rw [show L.toContinuousLinearMap = fderiv ℝ (fderiv ℝ f) x from
      hessianEquiv_toContinuousLinearMap f x (hm x hx)]
    exact (hdf.differentiable (by simp) x).hasFDerivAt
  let e := hdf.contDiffAt.toOpenPartialHomeomorph (fderiv ℝ f) hL (by simp)
  have he : x ∈ e.source := hdf.contDiffAt.mem_toOpenPartialHomeomorph_source hL (by simp)
  refine ⟨e.source, e.open_source, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, hyc⟩
    apply Set.mem_singleton_iff.mpr
    apply e.injOn hy he
    exact hyc.trans hx.symm
  · intro hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact ⟨he, hx⟩

/-- A smooth Morse function has only finitely many critical points in a compact set. -/
theorem finite_criticalPoints_inter {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hm : IsMorse f)
    {K : Set E} (hK : IsCompact K) : (K ∩ criticalPoints f).Finite :=
  (hK.inter_right (criticalPoints_isClosed hf)).finite
    ((criticalPoints_isDiscrete hf hm).mono inter_subset_right)

end Wikipedia.SmoothSixDPoincare.MorsePerturbation
