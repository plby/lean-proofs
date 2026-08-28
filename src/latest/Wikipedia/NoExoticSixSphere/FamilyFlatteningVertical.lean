import Wikipedia.NoExoticSixSphere.FamilyFlatteningDifferential
import Wikipedia.NoExoticSixSphere.SymmetricDividedDifference

/-!
# The flattened vertical derivative is the actual Schur residual

Differentiate the exact inverse-coordinate identities. The inverse vertical
vector has time component zero, last component one, and zero leading-output
derivative. The actual block equation then identifies its remaining output
with the Schur residual.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Topology

namespace NoExoticSixSphere.FamilyFlattening

open CorankOne

variable {T E F : Type}
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : T → E × ℝ → E × F}

def Data.verticalVector (d : Data f) (r : (T × E) × ℝ) : E × (T × ℝ) :=
  fderiv ℝ d.inverse r (0, 1)

theorem Data.verticalVector_parameters (d : Data f) {r : (T × E) × ℝ}
    (hr : r ∈ d.target) : (d.verticalVector r).2 = (0, 1) := by
  have hγ₀ := d.contDiffOn_inverse.contDiffAt (d.target.isOpen.mem_nhds hr)
  have hγ : DifferentiableAt ℝ d.inverse r := hγ₀.differentiableAt (by simp)
  have he : (fun q ↦ (d.inverse q).2) =ᶠ[𝓝 r]
      (fun q : (T × E) × ℝ ↦ (q.1.1, q.2)) := by
    filter_upwards [d.target.isOpen.mem_nhds hr] with q hq
    exact d.inverse_parameters hq
  have hfst : HasFDerivAt (Prod.fst : (T × E) × ℝ → T × E)
      (ContinuousLinearMap.fst ℝ (T × E) ℝ) r := hasFDerivAt_fst
  have hproj := hfst.fst.prodMk
    (hasFDerivAt_snd : HasFDerivAt (Prod.snd : (T × E) × ℝ → ℝ)
      (ContinuousLinearMap.snd ℝ (T × E) ℝ) r)
  have hEq := (hγ.hasFDerivAt.snd.congr_of_eventuallyEq he.symm).unique hproj
  exact congrArg (fun L : ((T × E) × ℝ) →L[ℝ] T × ℝ ↦ L (0, 1)) hEq

theorem Data.verticalVector_head (hf : ContDiff ℝ ∞ (uncurry f)) (d : Data f)
    {r : (T × E) × ℝ} (hr : r ∈ d.target) :
    fderiv ℝ (head f) (d.inverse r) (d.verticalVector r) = 0 := by
  have hγ₀ := d.contDiffOn_inverse.contDiffAt (d.target.isOpen.mem_nhds hr)
  have hγ : DifferentiableAt ℝ d.inverse r := hγ₀.differentiableAt (by simp)
  have hhead := ((contDiff_head f hf).differentiable (by simp) (d.inverse r)).hasFDerivAt
  have he : (fun q ↦ head f (d.inverse q)) =ᶠ[𝓝 r]
      (fun q : (T × E) × ℝ ↦ q.1.2) := by
    filter_upwards [d.target.isOpen.mem_nhds hr] with q hq
    exact d.head_inverse hq
  have hfst : HasFDerivAt (Prod.fst : (T × E) × ℝ → T × E)
      (ContinuousLinearMap.fst ℝ (T × E) ℝ) r := hasFDerivAt_fst
  have hEq := ((hhead.comp r hγ.hasFDerivAt).congr_of_eventuallyEq he.symm).unique hfst.snd
  exact congrArg (fun L : ((T × E) × ℝ) →L[ℝ] E ↦ L (0, 1)) hEq

theorem Data.vertical_flattened_eq (hf : ContDiff ℝ ∞ (uncurry f)) (d : Data f)
    {r : (T × E) × ℝ} (hr : r ∈ d.target) :
    SymmetricDifference.vertical d.flattened r = residual (spatial f (d.inverse r)) := by
  have hγ₀ := d.contDiffOn_inverse.contDiffAt (d.target.isOpen.mem_nhds hr)
  have hγ : DifferentiableAt ℝ d.inverse r := hγ₀.differentiableAt (by simp)
  have ht := ((contDiff_tail f hf).differentiable (by simp) (d.inverse r)).hasFDerivAt
  have hder : HasFDerivAt d.flattened
      ((fderiv ℝ (tail f) (d.inverse r)).comp (fderiv ℝ d.inverse r)) r :=
    ht.comp r hγ.hasFDerivAt
  change fderiv ℝ d.flattened r (0, 1) = _
  rw [hder.fderiv]
  change fderiv ℝ (tail f) (d.inverse r) (d.verticalVector r) = _
  have hv : d.verticalVector r = ((d.verticalVector r).1, (0, 1)) :=
    Prod.ext rfl (d.verticalVector_parameters hr)
  have hh := d.verticalVector_head hf hr
  rw [hv, fderiv_head_spatial f hf] at hh
  rw [hv, fderiv_tail_spatial f hf]
  exact tail_eq_residual_of_head_zero (spatial f (d.inverse r))
    (leading_invertible (d.source_chart _ (d.inverse_mem_source hr))) _ hh

end NoExoticSixSphere.FamilyFlattening
