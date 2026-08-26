import ErdosProblems.Erdos1002.Statement
import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The Legendre continued-fraction bridge

This file isolates the exact continued-fraction input used in the proof of
Erdős Problem 1002.  Mathlib's Legendre theorem is stated for a canonical
rational number `q`; the manuscript uses a reduced fraction `m / p`.  The
lemmas below verify explicitly that a positive, coprime denominator `p` is the
canonical denominator of that rational, translate the scaled error
`|p * α - m|` into `|α - m / p|`, and then invoke Legendre's theorem.

No irrationality assumption on `α` is needed for Legendre's theorem.  Thus
the results below apply, in particular, whenever `α` is irrational.
-/

namespace Erdos1002

noncomputable section

/-- A reduced fraction with positive natural denominator has that denominator
as its canonical `ℚ` denominator. -/
theorem den_intDivNat_of_coprime (m : ℤ) (p : ℕ) (hp : 0 < p)
    (hcop : Nat.Coprime m.natAbs p) :
    ((m : ℚ) / (p : ℚ)).den = p := by
  have hden : (((m : ℚ) / (p : ℚ)).den : ℤ) = (p : ℤ) :=
    Rat.den_div_eq_of_coprime (by exact_mod_cast hp) (by simpa using! hcop)
  exact_mod_cast hden

/-- Casting the rational fraction `m / p` to `ℝ` gives the corresponding real
fraction.  This lemma records the coercions used by the bridge explicitly. -/
theorem cast_intDivNat_to_real (m : ℤ) (p : ℕ) :
    (((m : ℚ) / (p : ℚ) : ℚ) : ℝ) =
      (m : ℝ) / (p : ℝ) := by
  norm_cast

/-- Dividing the scaled approximation error by a positive denominator gives
the usual rational-approximation error. -/
theorem abs_sub_intDivNat_eq_scaled (alpha : ℝ) (m : ℤ) (p : ℕ)
    (hp : 0 < p) :
    |alpha - (m : ℝ) / (p : ℝ)| =
      |(p : ℝ) * alpha - (m : ℝ)| / (p : ℝ) := by
  have hpReal : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp
  calc
    |alpha - (m : ℝ) / (p : ℝ)| =
        |((p : ℝ) * alpha - (m : ℝ)) / (p : ℝ)| := by
          congr 1
          field_simp
    _ = |(p : ℝ) * alpha - (m : ℝ)| / (p : ℝ) := by
      rw [abs_div, abs_of_pos hpReal]

/-- The scaled smallness condition used for rational resonances implies
Legendre's approximation inequality.  Positivity of `p` is explicit because
the proof divides an inequality by `p`. -/
theorem legendreBound_of_scaled (alpha : ℝ) (m : ℤ) (p : ℕ)
    (hp : 0 < p)
    (hscaled :
      |(p : ℝ) * alpha - (m : ℝ)| < 1 / (2 * (p : ℝ))) :
    |alpha - (m : ℝ) / (p : ℝ)| <
      1 / (2 * (p : ℝ) ^ 2) := by
  rw [abs_sub_intDivNat_eq_scaled alpha m p hp]
  have hpReal : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp
  rw [div_lt_iff₀ hpReal]
  calc
    |(p : ℝ) * alpha - (m : ℝ)| < 1 / (2 * (p : ℝ)) := hscaled
    _ = (1 / (2 * (p : ℝ) ^ 2)) * (p : ℝ) := by
      field_simp

/-- Legendre's theorem in mathlib's native rational-convergent formulation. -/
theorem rat_eq_convergent_of_legendreBound (alpha : ℝ) (q : ℚ)
    (happrox : |alpha - (q : ℝ)| < 1 / (2 * (q.den : ℝ) ^ 2)) :
    ∃ n : ℕ, q = alpha.convergent n := by
  exact Real.exists_rat_eq_convergent happrox

/-- Legendre's theorem in the native general-continued-fraction formulation. -/
theorem convs_eq_rat_of_legendreBound (alpha : ℝ) (q : ℚ)
    (happrox : |alpha - (q : ℝ)| < 1 / (2 * (q.den : ℝ) ^ 2)) :
    ∃ n : ℕ, (GenContFract.of alpha).convs n = (q : ℝ) := by
  exact Real.exists_convs_eq_rat happrox

/-- Exact Legendre bridge for a reduced fraction `m / p`: if `p > 0`,
`m` and `p` are coprime, and `|α - m/p| < 1/(2p²)`, then the rational
`m/p` is one of the recursively defined rational convergents of `α`. -/
theorem intDivNat_eq_convergent_of_reduced (alpha : ℝ) (m : ℤ) (p : ℕ)
    (hp : 0 < p) (hcop : Nat.Coprime m.natAbs p)
    (happrox :
      |alpha - (m : ℝ) / (p : ℝ)| < 1 / (2 * (p : ℝ) ^ 2)) :
    ∃ n : ℕ, (m : ℚ) / (p : ℚ) = alpha.convergent n := by
  apply Real.exists_rat_eq_convergent
    (ξ := alpha) (q := (m : ℚ) / (p : ℚ))
  rw [den_intDivNat_of_coprime m p hp hcop, cast_intDivNat_to_real]
  exact happrox

/-- The same reduced-fraction bridge, expressed using
`(GenContFract.of α).convs`. -/
theorem convs_eq_intDivNat_of_reduced (alpha : ℝ) (m : ℤ) (p : ℕ)
    (hp : 0 < p) (hcop : Nat.Coprime m.natAbs p)
    (happrox :
      |alpha - (m : ℝ) / (p : ℝ)| < 1 / (2 * (p : ℝ) ^ 2)) :
    ∃ n : ℕ,
      (GenContFract.of alpha).convs n =
        (((m : ℚ) / (p : ℚ) : ℚ) : ℝ) := by
  apply Real.exists_convs_eq_rat
    (ξ := alpha) (q := (m : ℚ) / (p : ℚ))
  rw [den_intDivNat_of_coprime m p hp hcop, cast_intDivNat_to_real]
  exact happrox

/-- Direct form used for resonance estimates: the scaled inequality
`|pα - m| < 1/(2p)` forces the reduced fraction `m/p` to be a rational
continued-fraction convergent of `α`. -/
theorem intDivNat_eq_convergent_of_scaled (alpha : ℝ) (m : ℤ) (p : ℕ)
    (hp : 0 < p) (hcop : Nat.Coprime m.natAbs p)
    (hscaled :
      |(p : ℝ) * alpha - (m : ℝ)| < 1 / (2 * (p : ℝ))) :
    ∃ n : ℕ, (m : ℚ) / (p : ℚ) = alpha.convergent n := by
  exact intDivNat_eq_convergent_of_reduced alpha m p hp hcop
    (legendreBound_of_scaled alpha m p hp hscaled)

/-- Direct scaled-error bridge for the general-continued-fraction convergents. -/
theorem convs_eq_intDivNat_of_scaled (alpha : ℝ) (m : ℤ) (p : ℕ)
    (hp : 0 < p) (hcop : Nat.Coprime m.natAbs p)
    (hscaled :
      |(p : ℝ) * alpha - (m : ℝ)| < 1 / (2 * (p : ℝ))) :
    ∃ n : ℕ,
      (GenContFract.of alpha).convs n =
        (((m : ℚ) / (p : ℚ) : ℚ) : ℝ) := by
  exact convs_eq_intDivNat_of_reduced alpha m p hp hcop
    (legendreBound_of_scaled alpha m p hp hscaled)

end

end Erdos1002
