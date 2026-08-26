import ErdosProblems.Erdos788.AsymptoticRegularity
import ErdosProblems.Erdos788.UpperAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Converting the finite upper bound to an exponent bound

The finite construction produces a product of powers of `p`, `2`, and `r`.
This file performs the pointwise logarithmic calculation for the canonical
prime, dimension, and design choices.
-/

namespace Erdos788

/-- A deliberately rounded absolute constant for the upper exponent. -/
def upperExponentConstant : ℝ := 101000000

theorem upperExponentConstant_pos : 0 < upperExponentConstant := by
  norm_num [upperExponentConstant]

private theorem log_trevisanMonomial
    {p r D : ℕ} (hp : 0 < p) (hr : 0 < r) :
    Real.log (((130000 * p ^ (r + 3) * 2 ^ (D + 2 * r) * r ^ 3 : ℕ) : ℝ)) =
      Real.log 130000 + (r + 3 : ℕ) * Real.log p +
        (D + 2 * r : ℕ) * Real.log 2 + 3 * Real.log r := by
  push_cast
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- The logarithm of the monomial finite majorant has the desired
`1/2 + O(exponentCorrection N)` exponent. -/
theorem log_trevisanMonomial_le_chosen
    {N : ℕ} (h : ParameterRegular N)
    (C : ShortLinearCode (parameterPrime N) (2 * parameterDimension N)
      (trevisanEta (parameterPrime N) (parameterDimension N))) :
    Real.log
        (((130000 * parameterPrime N ^ (parameterDimension N + 3) *
          2 ^ ((SuffixDesign.build C.ell (parameterDimension N)).coordCard +
            2 * parameterDimension N) * parameterDimension N ^ 3 : ℕ) : ℝ)) ≤
      ((1 / 2 : ℝ) + upperExponentConstant * exponentCorrection N) *
        Real.log (N : ℝ) := by
  let L := Real.log (N : ℝ)
  let q := Real.log L
  let δ := exponentCorrection N
  let p := parameterPrime N
  let r := parameterDimension N
  let D := (SuffixDesign.build C.ell r).coordCard
  let A := L * δ
  have hL : 0 < L := h.1
  have hq : 2 ≤ q := h.2.1
  have hδ : 0 < δ := parameterRegular_correction_pos h
  have hδ1 : δ ≤ 1 := parameterRegular_correction_le_one h
  have hp2 : 2 < p := by simpa [p] using! two_lt_parameterPrime N
  have hpR : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hlp : 0 < Real.log (p : ℝ) := Real.log_pos hpR
  have hrNat : 0 < r := by
    apply parameterDimension_pos
    have hnR : (1 : ℝ) < N :=
      (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ N)).mp h.1
    exact_mod_cast hnR
  have hrR : (0 : ℝ) < r := by exact_mod_cast hrNat
  have hA0 : 0 < A := mul_pos hL hδ
  have hA2 : 2 ≤ A := by
    simpa [A, L, δ] using! parameterRegular_log_mul_correction h
  have hr : (r : ℝ) ≤ A := by
    simpa [r, A, L, δ] using! parameterDimension_le_log_mul_correction h
  have hD : (D : ℝ) ≤ 100000000 * A := by
    simpa [D, r, A, L, δ, mul_assoc] using! chosenDesign_coordCard_le h C
  have hpLog : Real.log (p : ℝ) ≤ 2 / δ := by
    simpa [p, δ] using! log_parameterPrime_le_two_div_correction h.1
      (by linarith [h.2.1]) h.2.2.1
  have hpLogInv : Real.log (p : ℝ) ≤ 2 * δ⁻¹ := by
    simpa [div_eq_mul_inv] using! hpLog
  have hlogr : Real.log (r : ℝ) ≤ Real.log (p : ℝ) := by
    have hrL : (r : ℝ) ≤ L := by
      simpa [r, L] using! parameterDimension_le_log h
    have hlogrQ : Real.log (r : ℝ) ≤ q := by
      apply Real.log_le_log hrR
      simpa [q, L] using! hrL
    have hqP : q ≤ Real.log (p : ℝ) := by
      simpa [q, L, p] using! loglog_le_log_parameterPrime N
    exact hlogrQ.trans hqP
  have hrlp : (r : ℝ) * Real.log (p : ℝ) ≤
      L / 2 + Real.log (p : ℝ) := by
    have hnR : (1 : ℝ) < N :=
      (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ N)).mp h.1
    have hn : 1 ≤ N := by exact_mod_cast hnR.le
    have hceil : (r : ℝ) <
        L / (2 * Real.log (p : ℝ)) + 1 := by
      simpa [r, L, p] using! cast_parameterDimension_lt_log_div_add_one hn
    exact (calc
      (r : ℝ) * Real.log (p : ℝ) <
          (L / (2 * Real.log (p : ℝ)) + 1) *
            Real.log (p : ℝ) := mul_lt_mul_of_pos_right hceil hlp
      _ = L / 2 + Real.log (p : ℝ) := by
        field_simp
      ).le
  have hcube : δ ^ 3 = q / L := by
    simpa [δ, q, L] using!
      exponentCorrection_pow_three h.1 (by linarith [h.2.1])
  have hqAδ : q = A * δ ^ 2 := by
    have hrel : L * δ ^ 3 = q := by
      rw [hcube]
      field_simp
    dsimp [A]
    rw [hrel.symm]
    ring
  have hinvA : δ⁻¹ ≤ A := by
    have hδsq : δ ^ 2 ≤ δ := by nlinarith [sq_nonneg δ]
    have hAδsq : 2 ≤ A * δ ^ 2 := by simpa [← hqAδ] using! hq
    have hAδ : 1 ≤ A * δ := by
      have := mul_le_mul_of_nonneg_left hδsq hA0.le
      nlinarith
    have hdiv : 1 / δ ≤ A := (div_le_iff₀ hδ).2 hAδ
    simpa [one_div] using! hdiv
  have hpA : Real.log (p : ℝ) ≤ 2 * A :=
    hpLogInv.trans (mul_le_mul_of_nonneg_left hinvA (by norm_num))
  have hlog2nonneg : 0 ≤ Real.log (2 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have hraw :=
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hraw
    exact hraw
  have hconst : Real.log (130000 : ℝ) ≤ 65000 * A := by
    have hraw :=
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 130000)
    nlinarith
  have hpPower : ((r + 3 : ℕ) : ℝ) * Real.log (p : ℝ) ≤
      L / 2 + 8 * A := by
    push_cast
    nlinarith
  have htwoPower : ((D + 2 * r : ℕ) : ℝ) * Real.log (2 : ℝ) ≤
      100000002 * A := by
    push_cast
    have hDlog : (D : ℝ) * Real.log (2 : ℝ) ≤ D := by
      simpa using! mul_le_mul_of_nonneg_left hlog2
        (by positivity : (0 : ℝ) ≤ (D : ℝ))
    have hrlog : (r : ℝ) * Real.log (2 : ℝ) ≤ r := by
      simpa using! mul_le_mul_of_nonneg_left hlog2
        (by positivity : (0 : ℝ) ≤ (r : ℝ))
    nlinarith
  have hrPower : 3 * Real.log (r : ℝ) ≤ 6 * A := by
    nlinarith
  rw [log_trevisanMonomial (by omega : 0 < p) hrNat]
  have hsum :
      Real.log (130000 : ℝ) + ((r + 3 : ℕ) : ℝ) * Real.log (p : ℝ) +
          ((D + 2 * r : ℕ) : ℝ) * Real.log (2 : ℝ) +
            3 * Real.log (r : ℝ) ≤
        L / 2 + upperExponentConstant * A := by
    calc
      Real.log (130000 : ℝ) + ((r + 3 : ℕ) : ℝ) * Real.log (p : ℝ) +
            ((D + 2 * r : ℕ) : ℝ) * Real.log (2 : ℝ) +
              3 * Real.log (r : ℝ) ≤
          (65000 * A + (L / 2 + 8 * A)) + 100000002 * A + 6 * A :=
        add_le_add (add_le_add (add_le_add hconst hpPower) htwoPower) hrPower
      _ = L / 2 + 100065016 * A := by ring
      _ ≤ L / 2 + 101000000 * A := by
        gcongr
        norm_num
      _ = L / 2 + upperExponentConstant * A := by
        rfl
  calc
    Real.log (130000 : ℝ) + ((r + 3 : ℕ) : ℝ) * Real.log (p : ℝ) +
          ((D + 2 * r : ℕ) : ℝ) * Real.log (2 : ℝ) +
            3 * Real.log (r : ℝ) ≤
        L / 2 + upperExponentConstant * A := hsum
    _ = ((1 / 2 : ℝ) + upperExponentConstant * δ) * L := by
      dsimp [A]
      ring

/-- The canonical finite bound is dominated by the advertised real power. -/
theorem cast_trevisanFiniteUpperBound_le_rpow_chosen
    {N : ℕ} (h : ParameterRegular N)
    (C : ShortLinearCode (parameterPrime N) (2 * parameterDimension N)
      (trevisanEta (parameterPrime N) (parameterDimension N))) :
    ((trevisanFiniteUpperBound (parameterPrime N) (parameterDimension N)
        (SuffixDesign.build C.ell (parameterDimension N)).coordCard : ℕ) : ℝ) ≤
      (N : ℝ) ^
        ((1 / 2 : ℝ) + upperExponentConstant * exponentCorrection N) := by
  have hr : 0 < parameterDimension N := by
    apply parameterDimension_pos
    have hnR : (1 : ℝ) < N :=
      (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ N)).mp h.1
    exact_mod_cast hnR
  have hmonoNat := trevisanFiniteUpperBound_le_monomial
    (two_lt_parameterPrime N) hr
    (D := (SuffixDesign.build C.ell (parameterDimension N)).coordCard)
  have hmonoReal :
      ((trevisanFiniteUpperBound (parameterPrime N) (parameterDimension N)
          (SuffixDesign.build C.ell (parameterDimension N)).coordCard : ℕ) : ℝ) ≤
        ((130000 * parameterPrime N ^ (parameterDimension N + 3) *
          2 ^ ((SuffixDesign.build C.ell (parameterDimension N)).coordCard +
            2 * parameterDimension N) * parameterDimension N ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast hmonoNat
  have hnPos : (0 : ℝ) < N := by
    have hnR : (1 : ℝ) < N :=
      (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ N)).mp h.1
    positivity
  have hlog := log_trevisanMonomial_le_chosen h C
  exact hmonoReal.trans (Real.le_rpow_of_log_le hnPos hlog)

end Erdos788
