/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTLongTensorSum
import ErdosProblems.Erdos4b.FGKMTMajorantEnergy

/-!
# The distinguished long factor may occur at any coordinate

Coordinate permutations preserve both the finite box and its arithmetic
product weight. Thus every one-long-factor square sum equals the
canonical sum with distinguished coordinate zero.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem oneLongTensor_reindex (k j : ℕ) (σ : Equiv.Perm (Fin j)) (i : Fin j)
    (t : Fin j → ℝ) : oneLongTensor k j i (t ∘ σ) = oneLongTensor k j (σ i) t := by
  classical
  calc
    _ = ∏ q : Fin j, oneLongFactor k (σ i) (σ q) (t (σ q)) := by
      apply Finset.prod_congr rfl
      intro q _hq
      simp only [oneLongFactor, Function.comp_apply, σ.injective.eq_iff]
    _ = _ := Equiv.prod_comp σ (fun q => oneLongFactor k (σ i) q (t q))

def oneLongTensorSieveSum (k M : ℕ) (g : ℕ → ℝ) (R j : ℕ) (i : Fin j) : ℝ :=
  ∑ e : Fin j → Fin (R ^ 2 + 1),
    oneLongTensor k j i (fun q => Real.log (e q).val / Real.log R) ^ 2 *
      roughSieveWeight M g (∏ q, (e q).val)

theorem oneLongTensorSieveSum_reindex (k M R j : ℕ) (g : ℕ → ℝ)
    (σ : Equiv.Perm (Fin j)) (i : Fin j) :
    oneLongTensorSieveSum k M g R j i = oneLongTensorSieveSum k M g R j (σ i) := by
  classical
  let E := Equiv.piCongrLeft (fun _ : Fin j => Fin (R ^ 2 + 1)) σ.symm
  unfold oneLongTensorSieveSum
  rw [← Equiv.sum_comp E (fun e : Fin j → Fin (R ^ 2 + 1) =>
    oneLongTensor k j i (fun q => Real.log (e q).val / Real.log R) ^ 2 *
      roughSieveWeight M g (∏ q, (e q).val))]
  apply Finset.sum_congr rfl
  intro e _he
  have hE (q : Fin j) : E e q = e (σ q) := by
    simp [E, Equiv.piCongrLeft_apply]
  simp only [hE]
  change oneLongTensor k j i ((fun q => Real.log (e q).val / Real.log R) ∘ σ) ^ 2 *
    roughSieveWeight M g (∏ q, (e (σ q)).val) = _
  rw [oneLongTensor_reindex, Equiv.prod_comp σ (fun q => (e q).val)]

theorem oneLongTensor_zero (k j : ℕ) (t : Fin (j + 1) → ℝ) :
    oneLongTensor k (j + 1) 0 t =
      dimensionLongFactor k (t 0) * ∏ i : Fin j, dimensionProfileFactor k (t i.succ) := by
  simp [oneLongTensor, oneLongFactor, Fin.prod_univ_succ]

theorem oneLongTensorSieveSum_zero (k M R j : ℕ) (g : ℕ → ℝ) :
    oneLongTensorSieveSum k M g R (j + 1) 0 = longTensorSieveSum k M g R j := by
  unfold oneLongTensorSieveSum longTensorSieveSum
  simp only [oneLongTensor_zero, mul_pow, Finset.prod_pow]

theorem oneLongTensorSieveSum_eq_long (k M R j : ℕ) (g : ℕ → ℝ) (i : Fin (j + 1)) :
    oneLongTensorSieveSum k M g R (j + 1) i = longTensorSieveSum k M g R j := by
  have h := oneLongTensorSieveSum_reindex k M R (j + 1) g (Equiv.swap i 0) i
  simpa only [Equiv.swap_apply_left, oneLongTensorSieveSum_zero] using h

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.oneLongTensorSieveSum_eq_long
