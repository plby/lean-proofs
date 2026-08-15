/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RationalEulerCoefficients
import ErdosProblems.Erdos387.RationalPowerSeriesRecurrence
import Mathlib.Tactic.LinearCombination

/-! # Division-free logarithmic derivative of the rational Euler product -/

namespace Erdos387

open Polynomial

namespace RationalWeil

variable {K R : Type*} [Field K] [Fintype K] [CommRing R] {N n : Nat}

noncomputable def finiteEulerProduct
    (w : MonicIrreducibleLE K N → R) : PowerSeries R :=
  ∏ P : MonicIrreducibleLE K N,
    localEuler P.poly.natDegree (w P)

noncomputable def finiteEulerLogDerivative
    (w : MonicIrreducibleLE K N → R) : PowerSeries R :=
  ∑ P : MonicIrreducibleLE K N,
    PowerSeries.C (P.poly.natDegree : R) *
      (localEuler P.poly.natDegree (w P) - 1)

private theorem X_mul_derivativeFun_prod_localEuler
    {I : Type*} [Fintype I] (e : I → Nat) (he : ∀ i, e i ≠ 0)
    (z : I → R) :
    PowerSeries.X * PowerSeries.derivative R
        (∏ i : I, localEuler (e i) (z i)) =
      (∏ i : I, localEuler (e i) (z i)) *
        (∑ i : I, PowerSeries.C (e i : R) *
          (localEuler (e i) (z i) - 1)) := by
  classical
  let s : Finset I := Finset.univ
  change PowerSeries.X * PowerSeries.derivative R
      (∏ i ∈ s, localEuler (e i) (z i)) =
    (∏ i ∈ s, localEuler (e i) (z i)) *
      (∑ i ∈ s, PowerSeries.C (e i : R) *
        (localEuler (e i) (z i) - 1))
  induction s using Finset.induction_on with
  | empty => simp [PowerSeries.derivative_one]
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        Derivation.leibniz]
      simp only [smul_eq_mul]
      have hlocal := X_mul_derivativeFun_localEuler (z a) (he a)
      linear_combination
        localEuler (e a) (z a) * ih +
          (∏ i ∈ s, localEuler (e i) (z i)) * hlocal

theorem X_mul_derivativeFun_finiteEulerProduct
    (w : MonicIrreducibleLE K N → R) :
    PowerSeries.X *
        PowerSeries.derivative R (finiteEulerProduct w) =
      finiteEulerProduct w * finiteEulerLogDerivative w := by
  rw [finiteEulerProduct, finiteEulerLogDerivative]
  exact X_mul_derivativeFun_prod_localEuler
    (fun P : MonicIrreducibleLE K N ↦ P.poly.natDegree)
    (fun P ↦ P.natDegree_pos.ne') w

theorem coeff_finiteEulerLogDerivative (hn : n ≠ 0)
    (w : MonicIrreducibleLE K N → R) :
    PowerSeries.coeff n (finiteEulerLogDerivative w) =
      ∑ P : MonicIrreducibleLE K N,
        if P.poly.natDegree ∣ n then
          (P.poly.natDegree : R) *
            w P ^ (n / P.poly.natDegree)
        else 0 := by
  classical
  rw [finiteEulerLogDerivative, map_sum]
  apply Finset.sum_congr rfl
  intro P hP
  rw [PowerSeries.coeff_C_mul, map_sub,
    coeff_localEuler (w P) P.natDegree_pos.ne',
    PowerSeries.coeff_one, if_neg hn]
  simp only [sub_zero]
  split_ifs <;> simp

theorem constantCoeff_finiteEulerLogDerivative
    (w : MonicIrreducibleLE K N → R) :
    PowerSeries.constantCoeff (finiteEulerLogDerivative w) = 0 := by
  classical
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    finiteEulerLogDerivative, map_sum]
  apply Finset.sum_eq_zero
  intro P hP
  rw [PowerSeries.coeff_C_mul, map_sub,
    coeff_localEuler (w P) P.natDegree_pos.ne',
    PowerSeries.coeff_one]
  simp

theorem nat_mul_coeff_finiteEulerProduct_eq_sum_positive
    (w : MonicIrreducibleLE K N → R) (n : Nat) :
    (n : R) * PowerSeries.coeff n (finiteEulerProduct w) =
      ∑ i ∈ Finset.range n,
        PowerSeries.coeff (n - (i + 1)) (finiteEulerProduct w) *
          PowerSeries.coeff (i + 1) (finiteEulerLogDerivative w) := by
  exact nat_mul_coeff_eq_sum_positive_of_X_mul_derivativeFun_eq_mul
    (X_mul_derivativeFun_finiteEulerProduct w)
    (constantCoeff_finiteEulerLogDerivative w) n

end RationalWeil

end Erdos387
