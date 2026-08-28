import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersLineBundleTensorFibres
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersLineBundleGauges

/-!
# Powered native bundle comparisons act on full tensor powers

The power of an actual holomorphic line-bundle comparison is identified
with the tensor power of its fibrewise linear equivalence.  The equality
is on the full tensor product; elementary tensors are used only to prove
the equality of linear maps.
-/

noncomputable section

open Bundle
open scoped TensorProduct

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle.CrossGauge

open HolomorphicCharacterBundle Powers

variable {M ι κ : Type*} [TopologicalSpace M]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  [ChartedSpace H M] {I : ModelWithCorners ℂ E H}
  {A : TransitionData M ι} {B : TransitionData M κ}

/-- The genuine powered fibre comparison is the tensor power of the
original fibre comparison, on the whole tensor product. -/
theorem power_fiberTensorPowerEquiv (G : CrossGauge I A B) (n : ℕ) (x : M) :
    (fiberTensorPowerEquiv B x n).toLinearMap ∘ₗ
        (tensorPowerCongr (G.fiberEquiv x).toLinearEquiv n).toLinearMap =
      ((G.power n).fiberEquiv x).toLinearEquiv.toLinearMap ∘ₗ
        (fiberTensorPowerEquiv A x n).toLinearMap := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  let c : ℂ := G.value (A.indexAt x, B.indexAt x) x
  have hv (k : Fin n) : id (α := ℂ) (G.fiberEquiv x (v k)) =
      c * id (α := ℂ) (v k) := G.fiberEquiv_apply x (v k)
  have hp : id (α := ℂ) ((G.power n).fiberEquiv x
      (fiberTensorPowerEquiv A x n (PiTensorProduct.tprod ℂ v))) =
      c ^ n * id (α := ℂ) (fiberTensorPowerEquiv A x n (PiTensorProduct.tprod ℂ v)) :=
    G.power_fiberEquiv_apply n x _
  have hA : id (α := ℂ) (fiberTensorPowerEquiv A x n (PiTensorProduct.tprod ℂ v)) =
      ∏ k, id (α := ℂ) (v k) := fiberTensorPowerEquiv_tprod A x n v
  have hB : id (α := ℂ) (fiberTensorPowerEquiv B x n
      (tensorPowerCongr (G.fiberEquiv x).toLinearEquiv n (PiTensorProduct.tprod ℂ v))) =
      ∏ k, id (α := ℂ) (G.fiberEquiv x (v k)) :=
    (congrArg (fun w : Powers.TensorPower (B.core.Fiber x) n =>
      id (α := ℂ) (fiberTensorPowerEquiv B x n w))
        (tensorPowerCongr_tprod (G.fiberEquiv x).toLinearEquiv n v)).trans
      (fiberTensorPowerEquiv_tprod B x n (fun k => G.fiberEquiv x (v k)))
  change id (α := ℂ) (fiberTensorPowerEquiv B x n
      (tensorPowerCongr (G.fiberEquiv x).toLinearEquiv n (PiTensorProduct.tprod ℂ v))) =
    id (α := ℂ) ((G.power n).fiberEquiv x
      (fiberTensorPowerEquiv A x n (PiTensorProduct.tprod ℂ v)))
  calc
    _ = ∏ k, c * id (α := ℂ) (v k) :=
      hB.trans (Finset.prod_congr rfl (fun k _ => hv k))
    _ = c ^ n * ∏ k, id (α := ℂ) (v k) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = c ^ n * id (α := ℂ) (fiberTensorPowerEquiv A x n (PiTensorProduct.tprod ℂ v)) :=
      congrArg (fun z : ℂ => c ^ n * z) hA.symm
    _ = _ := hp.symm

/-- Pointwise form of the full tensor-power comparison identity. -/
theorem power_fiberTensorPowerEquiv_apply (G : CrossGauge I A B) (n : ℕ) (x : M)
    (v : Powers.TensorPower (A.core.Fiber x) n) :
    fiberTensorPowerEquiv B x n
        (tensorPowerCongr (G.fiberEquiv x).toLinearEquiv n v) =
      (G.power n).fiberEquiv x (fiberTensorPowerEquiv A x n v) :=
  DFunLike.congr_fun (power_fiberTensorPowerEquiv G n x) v

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle.CrossGauge
