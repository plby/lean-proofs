/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RationalStepanovAuxiliary

/-!
# Degree of the rational Stepanov auxiliary polynomial

The cleared high block has degree at most `p^(h+3)` times the degree of its
low input.  This gives a degree bound which factors exactly as the number
`R` of imposed Hasse derivatives times an explicit trace-fiber bound.
-/

namespace Erdos387

open Polynomial
open Waring.Analytic.Stepanov

namespace RationalStepanov

/-- A strict degree bound for the rational auxiliary polynomial. -/
def rationalAuxiliaryDegreeBound (p h s : ℕ) : ℕ :=
  S p h + p ^ (h + 3) *
    (rationalPhaseAllowance p h s + p ^ (h + 3) * K p h)

/-- The corresponding upper bound for one rational trace fiber. -/
def rationalTraceFiberBound (p h s : ℕ) : ℕ :=
  p ^ (2 * (h + 3) - 1) + p ^ (h + 3) +
    p ^ 2 * rationalPhaseAllowance p h s

theorem rationalAuxiliaryDegreeBound_eq_R_mul
    (p h s : ℕ) :
    rationalAuxiliaryDegreeBound p h s =
      R p h * rationalTraceFiberBound p h s := by
  unfold rationalAuxiliaryDegreeBound rationalTraceFiberBound
  unfold S K R
  simp only [Nat.mul_add]
  have hS : p ^ (2 * h + 4) = p ^ (h + 1) * p ^ (h + 3) := by
    rw [← pow_add]
    exact congrArg (fun n : ℕ => p ^ n) (by omega)
  have hA : p ^ (h + 3) * rationalPhaseAllowance p h s =
      p ^ (h + 1) * (p ^ 2 * rationalPhaseAllowance p h s) := by
    rw [show h + 3 = (h + 1) + 2 by omega, pow_add]
    ring
  have hK : p ^ (h + 3) * (p ^ (h + 3) * p ^ h) =
      p ^ (h + 1) * p ^ (2 * (h + 3) - 1) := by
    calc
      p ^ (h + 3) * (p ^ (h + 3) * p ^ h) =
          p ^ (h + 3) * p ^ ((h + 3) + h) := by
            exact congrArg (p ^ (h + 3) * ·) (pow_add p (h + 3) h).symm
      _ = p ^ (h + 3 + (h + 3 + h)) := (pow_add _ _ _).symm
      _ = p ^ ((h + 1) + (2 * (h + 3) - 1)) :=
        congrArg (fun n : ℕ => p ^ n) (by omega)
      _ = p ^ (h + 1) * p ^ (2 * (h + 3) - 1) := pow_add _ _ _
  rw [hS, hA, hK]
  ring_nf

/-- The degree of one rational auxiliary summand is below the common bound. -/
theorem natDegree_rationalAuxiliaryTerm_lt
    {E : Type*} [Field E] {p h s i k : ℕ}
    (hp : 0 < p) {e lowN lowD : E[X]}
    (he : e.natDegree < S p h)
    (hN : lowN.natDegree ≤ s * frobeniusOrderSum p (h + 3))
    (hD : lowD.natDegree ≤ s * frobeniusOrderSum p (h + 3))
    (hi : i < p) (hk : k ≤ K p h) (pole : E) :
    (rationalAuxiliaryTerm p h pole i k e lowN lowD).natDegree <
      rationalAuxiliaryDegreeBound p h s := by
  let L := s * frobeniusOrderSum p (h + 3)
  have hi' : i ≤ p - 1 := by omega
  have hlow :
      (lowN ^ i * lowD ^ (p - 1 - i) *
        expand E (p ^ (h + 3)) ((X - C pole) ^ k)).natDegree ≤
        rationalPhaseAllowance p h s + p ^ (h + 3) * k := by
    have hNi : (lowN ^ i).natDegree ≤ i * L :=
      natDegree_pow_le_of_le i hN
    have hDi : (lowD ^ (p - 1 - i)).natDegree ≤
        (p - 1 - i) * L :=
      natDegree_pow_le_of_le _ hD
    have hcenter : ((X - C pole) ^ k : E[X]).natDegree ≤ k := by
      calc
        ((X - C pole) ^ k : E[X]).natDegree ≤
            k * (X - C pole : E[X]).natDegree := natDegree_pow_le
        _ ≤ k * 1 := Nat.mul_le_mul_left k (natDegree_X_sub_C_le pole)
        _ = k := Nat.mul_one k
    have hexpand :
        (expand E (p ^ (h + 3)) ((X - C pole) ^ k)).natDegree ≤
          p ^ (h + 3) * k := by
      rw [natDegree_expand]
      calc
        ((X - C pole) ^ k : E[X]).natDegree * p ^ (h + 3) ≤
            k * p ^ (h + 3) := Nat.mul_le_mul_right _ hcenter
        _ = p ^ (h + 3) * k := Nat.mul_comm _ _
    have hsum :
        i * L + (p - 1 - i) * L = rationalPhaseAllowance p h s := by
      unfold rationalPhaseAllowance L
      rw [← Nat.add_mul, Nat.add_sub_of_le hi']
      ring
    calc
      (lowN ^ i * lowD ^ (p - 1 - i) *
          expand E (p ^ (h + 3)) ((X - C pole) ^ k)).natDegree ≤
          (lowN ^ i).natDegree + (lowD ^ (p - 1 - i)).natDegree +
            (expand E (p ^ (h + 3)) ((X - C pole) ^ k)).natDegree := by
        exact (natDegree_mul_le.trans
          (Nat.add_le_add_right natDegree_mul_le _))
      _ ≤ i * L + (p - 1 - i) * L + p ^ (h + 3) * k := by omega
      _ = rationalPhaseAllowance p h s + p ^ (h + 3) * k := by rw [hsum]
  unfold rationalAuxiliaryTerm rationalAuxiliaryDegreeBound
  have houter :
      (expand E (p ^ (h + 3))
        (lowN ^ i * lowD ^ (p - 1 - i) *
          expand E (p ^ (h + 3)) ((X - C pole) ^ k))).natDegree ≤
        p ^ (h + 3) *
          (rationalPhaseAllowance p h s + p ^ (h + 3) * k) := by
    rw [natDegree_expand]
    calc
      (lowN ^ i * lowD ^ (p - 1 - i) *
          expand E (p ^ (h + 3)) ((X - C pole) ^ k)).natDegree *
            p ^ (h + 3) ≤
          (rationalPhaseAllowance p h s + p ^ (h + 3) * k) *
            p ^ (h + 3) := Nat.mul_le_mul_right _ hlow
      _ = p ^ (h + 3) *
          (rationalPhaseAllowance p h s + p ^ (h + 3) * k) :=
        Nat.mul_comm _ _
  have hk' : p ^ (h + 3) * k ≤ p ^ (h + 3) * K p h :=
    Nat.mul_le_mul_left _ hk
  calc
    (e * expand E (p ^ (h + 3))
      (lowN ^ i * lowD ^ (p - 1 - i) *
        expand E (p ^ (h + 3)) ((X - C pole) ^ k))).natDegree ≤
        e.natDegree +
          (expand E (p ^ (h + 3))
            (lowN ^ i * lowD ^ (p - 1 - i) *
              expand E (p ^ (h + 3)) ((X - C pole) ^ k))).natDegree :=
      natDegree_mul_le
    _ ≤ e.natDegree + p ^ (h + 3) *
        (rationalPhaseAllowance p h s + p ^ (h + 3) * k) :=
      Nat.add_le_add_left houter _
    _ < S p h + p ^ (h + 3) *
        (rationalPhaseAllowance p h s + p ^ (h + 3) * K p h) := by
      have := Nat.mul_le_mul_left (p ^ (h + 3))
        (Nat.add_le_add_left hk' (rationalPhaseAllowance p h s))
      omega

/-- The full rational auxiliary polynomial has the same strict degree bound. -/
theorem natDegree_rationalAuxiliaryPolynomial_lt
    {E : Type*} [Field E] {p h s : ℕ} (hp : 0 < p)
    {lowN lowD : E[X]}
    (hN : lowN.natDegree ≤ s * frobeniusOrderSum p (h + 3))
    (hD : lowD.natDegree ≤ s * frobeniusOrderSum p (h + 3))
    (pole : E) (a : AuxiliaryCoefficients E p h) :
    (rationalAuxiliaryPolynomial p h pole lowN lowD a).natDegree <
      rationalAuxiliaryDegreeBound p h s := by
  have hboundPos : 0 < rationalAuxiliaryDegreeBound p h s := by
    unfold rationalAuxiliaryDegreeBound S
    exact Nat.add_pos_left (Nat.pow_pos hp) _
  refine (natDegree_sum_le_of_forall_le _ _ ?_).trans_lt
    (Nat.pred_lt hboundPos.ne')
  intro i hiMem
  apply natDegree_sum_le_of_forall_le
  intro k hkMem
  exact Nat.le_pred_of_lt <|
    natDegree_rationalAuxiliaryTerm_lt hp
      (natDegree_auxiliaryCoefficientPolynomial_lt hp a i k)
      hN hD i.isLt (by omega) pole

end RationalStepanov

end Erdos387
