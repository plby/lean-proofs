/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Cancelling pairs in diagonal sextic identities with nonzero coefficients.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.QuadraticNormalization

namespace Erdos477.Geometry

open Polynomial

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]

theorem weighted_quadratic_sixth_pair_cancellation (a : Fin 4 → K)
    (ha : ∀ i, a i ≠ 0) (f : Fin 4 → K[X])
    (hf : ∀ i, (f i).natDegree ≤ 2) (hf0 : ∀ i, f i ≠ 0)
    (hinfty : ∃ i, (f i).natDegree = 2)
    (hroot : ∀ x : K, ∃ i, (f i).eval x ≠ 0)
    (hsum : C (a 0) * f 0 ^ 6 + C (a 1) * f 1 ^ 6 +
      C (a 2) * f 2 ^ 6 + C (a 3) * f 3 ^ 6 = 0) :
    C (a 0) * f 0 ^ 6 + C (a 1) * f 1 ^ 6 = 0 ∨
      C (a 0) * f 0 ^ 6 + C (a 2) * f 2 ^ 6 = 0 ∨
      C (a 1) * f 1 ^ 6 + C (a 2) * f 2 ^ 6 = 0 := by
  choose b hb using fun i => IsAlgClosed.exists_pow_nat_eq (a i) (by decide : 0 < 6)
  have hb0 (i) : b i ≠ 0 := by
    intro hi
    have h := hb i
    rw [hi, zero_pow (by decide)] at h
    exact ha i h.symm
  let g : Fin 4 → K[X] := fun i => C (b i) * f i
  have hgdeg (i) : (g i).natDegree = (f i).natDegree :=
    natDegree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr (hb0 i)) (f i)
  have hgp (i) : g i ^ 6 = C (a i) * f i ^ 6 := by
    dsimp only [g]
    rw [mul_pow, ← map_pow, hb]
  have hg0 (i) : g i ≠ 0 := mul_ne_zero (C_ne_zero.mpr (hb0 i)) (hf0 i)
  have hginfty : ∃ i, (g i).natDegree = 2 := by
    obtain ⟨i, hi⟩ := hinfty
    exact ⟨i, (hgdeg i).trans hi⟩
  have hgroot (x) : ∃ i, (g i).eval x ≠ 0 := by
    obtain ⟨i, hi⟩ := hroot x
    exact ⟨i, by simpa only [g, eval_mul, eval_C] using mul_ne_zero (hb0 i) hi⟩
  have hgsum : g 0 ^ 6 + g 1 ^ 6 + g 2 ^ 6 + g 3 ^ 6 = 0 := by
    simpa only [hgp] using hsum
  have h := quadratic_sixth_pair_cancellation_of_le g (fun i => (hgdeg i).trans_le (hf i))
    hg0 hginfty hgroot hgsum
  simpa only [hgp] using h

/-- In the sign pattern of the original sextic, every such quadratic
parametrization forces one of the three affine coordinate cancellations. -/
theorem diagonal_quadratic_sixth_pair_cancellation (c : K) (hc : c ≠ 0)
    (f : Fin 4 → K[X]) (hf : ∀ i, (f i).natDegree ≤ 2) (hf0 : ∀ i, f i ≠ 0)
    (hinfty : ∃ i, (f i).natDegree = 2)
    (hroot : ∀ x : K, ∃ i, (f i).eval x ≠ 0)
    (hsum : f 0 ^ 6 + f 1 ^ 6 - f 2 ^ 6 - C c * f 3 ^ 6 = 0) :
    f 0 ^ 6 + f 1 ^ 6 = 0 ∨ f 0 ^ 6 - f 2 ^ 6 = 0 ∨ f 1 ^ 6 - f 2 ^ 6 = 0 := by
  have ha : ∀ i : Fin 4, ![(1 : K), 1, -1, -c] i ≠ 0 := by
    intro i
    fin_cases i <;> simp [hc]
  have hsum' : C (1 : K) * f 0 ^ 6 + C 1 * f 1 ^ 6 +
      C (-1) * f 2 ^ 6 + C (-c) * f 3 ^ 6 = 0 := by
    simpa only [map_one, map_neg, one_mul, neg_mul, sub_eq_add_neg] using hsum
  have h := weighted_quadratic_sixth_pair_cancellation ![(1 : K), 1, -1, -c]
    ha f hf hf0 hinfty hroot hsum'
  simpa [sub_eq_add_neg] using h

#print axioms diagonal_quadratic_sixth_pair_cancellation
-- 'Erdos477.Geometry.diagonal_quadratic_sixth_pair_cancellation' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
