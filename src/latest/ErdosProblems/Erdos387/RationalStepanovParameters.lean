/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RationalPoleOrders
import Waring.Analytic.StepanovAuxiliaryLinear

/-!
# Parameters for the rational Stepanov construction

The coefficient, monomial, and derivative cutoffs are the existing pure
Stepanov parameters.  Only the reduced-condition degree changes: clearing a
rational trace fiber costs `(p-1) * s * (1+p+...+p^(h+2))`, where `s` is the
number of simple poles.  If `s < p`, the same strict dimension count holds.
-/

namespace Erdos387

open Waring.Analytic.Stepanov

namespace RationalStepanov

/-- Degree contribution from the denominator-cleared low rational trace. -/
def rationalPhaseAllowance (p h s : ℕ) : ℕ :=
  (p - 1) * s * frobeniusOrderSum p (h + 3)

/-- Degree bound for each reduced rational Hasse condition. -/
def rationalConditionDegree (p h s : ℕ) : ℕ :=
  S p h + rationalPhaseAllowance p h s + K p h

/-- The geometric sum identity in a subtraction-free natural-number form. -/
theorem pred_mul_frobeniusOrderSum_add_one
    {p m : ℕ} (hp : 0 < p) :
    (p - 1) * frobeniusOrderSum p m + 1 = p ^ m := by
  induction m with
  | zero => simp [frobeniusOrderSum]
  | succ m ih =>
      rw [show m + 1 = m + 1 by rfl, frobeniusOrderSum_succ,
        Nat.mul_add, pow_succ]
      calc
        (p - 1) * frobeniusOrderSum p m + (p - 1) * p ^ m + 1 =
            ((p - 1) * frobeniusOrderSum p m + 1) +
              (p - 1) * p ^ m := by ring
        _ = p ^ m + (p - 1) * p ^ m := by rw [ih]
        p ^ m + (p - 1) * p ^ m = (1 + (p - 1)) * p ^ m := by ring
        _ = p * p ^ m := by rw [Nat.add_sub_of_le hp]
        _ = p ^ m * p := Nat.mul_comm _ _

/-- The two lower-order contributions fit below the spare coefficient
spacing `p^(h+4)`. -/
theorem rationalPhaseAllowance_add_K_lt_pow
    {p h s : ℕ} (hp : 1 < p) (hs : s < p) :
    rationalPhaseAllowance p h s + K p h < p ^ (h + 4) := by
  have hp0 : 0 < p := hp.trans_le' (Nat.zero_le _)
  have hsle : s ≤ p - 1 := by omega
  have hgeom := pred_mul_frobeniusOrderSum_add_one
    (p := p) (m := h + 3) hp0
  have hK : K p h ≤ p ^ (h + 3) := by
    unfold K
    exact Nat.pow_le_pow_right hp0 (by omega)
  have hA : rationalPhaseAllowance p h s ≤
      (p - 1) * (p ^ (h + 3) - 1) := by
    unfold rationalPhaseAllowance
    have hrewrite :
        (p - 1) * frobeniusOrderSum p (h + 3) =
          p ^ (h + 3) - 1 := by omega
    calc
      (p - 1) * s * frobeniusOrderSum p (h + 3) =
          s * ((p - 1) * frobeniusOrderSum p (h + 3)) := by ring
      _ = s * (p ^ (h + 3) - 1) := by rw [hrewrite]
      _ ≤ (p - 1) * (p ^ (h + 3) - 1) :=
        Nat.mul_le_mul_right _ hsle
  have hpowpos : 0 < p ^ (h + 3) := Nat.pow_pos hp0
  have hpredpos : 0 < p - 1 := Nat.sub_pos_of_lt hp
  have hsub : p ^ (h + 3) - 1 < p ^ (h + 3) :=
    Nat.sub_lt hpowpos zero_lt_one
  have hcore :
      (p - 1) * (p ^ (h + 3) - 1) + p ^ (h + 3) <
        p * p ^ (h + 3) := by
    calc
      (p - 1) * (p ^ (h + 3) - 1) + p ^ (h + 3) <
          (p - 1) * p ^ (h + 3) + p ^ (h + 3) :=
        Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left hsub hpredpos) _
      _ = ((p - 1) + 1) * p ^ (h + 3) := by ring
      _ = p * p ^ (h + 3) := by rw [Nat.sub_add_cancel hp.le]
  calc
    rationalPhaseAllowance p h s + K p h ≤
        (p - 1) * (p ^ (h + 3) - 1) + p ^ (h + 3) :=
      Nat.add_le_add hA hK
    _ < p * p ^ (h + 3) := hcore
    _ = p ^ (h + 4) := by
      calc
        p * p ^ (h + 3) = p ^ 1 * p ^ (h + 3) := by rw [pow_one]
        _ = p ^ (1 + (h + 3)) := (pow_add p 1 (h + 3)).symm
        _ = p ^ (h + 4) := by congr 1 <;> omega

/-- The rational reduced system has strictly fewer scalar conditions than
unknown coefficients. -/
theorem rationalConstraints_lt_coefficients
    {p h s : ℕ} (hp : 1 < p) (hs : s < p) :
    R p h * rationalConditionDegree p h s <
      p * S p h * (K p h + 1) := by
  have hp0 : 0 < p := by omega
  have hinside :
      S p h + (rationalPhaseAllowance p h s + K p h) <
        S p h + p ^ (h + 4) :=
    Nat.add_lt_add_left (rationalPhaseAllowance_add_K_lt_pow hp hs) _
  have hRpos : 0 < R p h := Nat.pow_pos hp0
  have hmul := Nat.mul_lt_mul_of_pos_left hinside hRpos
  rw [← add_assoc] at hmul
  change R p h * rationalConditionDegree p h s <
      R p h * (S p h + p ^ (h + 4)) at hmul
  calc
    R p h * rationalConditionDegree p h s <
        R p h * (S p h + p ^ (h + 4)) := hmul
    _ = R p h * (p ^ (h + 4) * K p h + p ^ (h + 4)) := by
      rw [S_eq_K_mul_pow]
      ring
    _ = (R p h * p ^ (h + 4)) * (K p h + 1) := by ring
    _ = (p * S p h) * (K p h + 1) := by
      rw [R_mul_pow_eq_p_mul_S]
    _ = p * S p h * (K p h + 1) := rfl

end RationalStepanov

end Erdos387
