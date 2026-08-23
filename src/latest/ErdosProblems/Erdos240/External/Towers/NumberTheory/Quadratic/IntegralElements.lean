import Mathlib

namespace Towers.NumberTheory

/-- The quadratic algebra `ℚ[ω]` with `ω² = m`, used as a coordinate model for `ℚ(√m)`. -/
abbrev QFModel (m : ℤ) := QuadraticAlgebra ℚ (m : ℚ) 0

namespace QFModel

private lemma trace_formula (m : ℤ) (x : QFModel m) :
    Algebra.trace ℚ (QFModel m) x = 2 * x.re := by
  have hmat : Algebra.leftMulMatrix (QuadraticAlgebra.basis (m : ℚ) 0) x =
      !![x.re, (m : ℚ) * x.im; x.im, x.re] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Algebra.leftMulMatrix_eq_repr_mul, QuadraticAlgebra.basis,
        QuadraticAlgebra.linearEquivTuple, QuadraticAlgebra.equivProd,
        QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis (m : ℚ) 0)]
  rw [hmat, Matrix.trace_fin_two_of]
  ring

private lemma algebraNorm_formula (m : ℤ) (x : QFModel m) :
    Algebra.norm ℚ x = x.re ^ 2 - (m : ℚ) * x.im ^ 2 := by
  have hmat : Algebra.leftMulMatrix (QuadraticAlgebra.basis (m : ℚ) 0) x =
      !![x.re, (m : ℚ) * x.im; x.im, x.re] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Algebra.leftMulMatrix_eq_repr_mul, QuadraticAlgebra.basis,
        QuadraticAlgebra.linearEquivTuple, QuadraticAlgebra.equivProd,
        QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  rw [Algebra.norm_eq_matrix_det (QuadraticAlgebra.basis (m : ℚ) 0)]
  rw [hmat, Matrix.det_fin_two_of]
  ring

/-- In a quadratic algebra, integrality is equivalent to integrality of the coordinate trace and
norm. This is the quadratic criterion used in Proposition 23. -/
theorem integral_trace_norm
    (m : ℤ) (x : QFModel m) :
    IsIntegral ℤ x ↔
      IsIntegral ℤ (2 * x.re) ∧
        IsIntegral ℤ (x.re ^ 2 - (m : ℚ) * x.im ^ 2) := by
  constructor
  · intro hx
    let conj : QFModel m →ₐ[ℤ] QFModel m :=
      { starRingEnd (QFModel m) with
        commutes' := fun z => by simp }
    have hconj : IsIntegral ℤ (star x) := by
      change IsIntegral ℤ ((starRingEnd (QFModel m)) x)
      exact hx.map conj
    have hinj : Function.Injective
        (IsScalarTower.toAlgHom ℤ ℚ (QFModel m)) := by
      intro a b hab
      have := congrArg QuadraticAlgebra.re hab
      simpa using this
    constructor
    · rw [← isIntegral_algHom_iff
          (IsScalarTower.toAlgHom ℤ ℚ (QFModel m)) hinj]
      have hsum := hx.add hconj
      convert hsum using 1
      · ext
        · simp [QuadraticAlgebra.re_star]
          ring
        · simp [QuadraticAlgebra.im_star]
    · rw [← isIntegral_algHom_iff
          (IsScalarTower.toAlgHom ℤ ℚ (QFModel m)) hinj]
      have hprod := hx.mul hconj
      convert hprod using 1
      · ext
        · simp [pow_two, QuadraticAlgebra.re_star, QuadraticAlgebra.re_mul]
          ring
        · simp [pow_two, QuadraticAlgebra.im_star, QuadraticAlgebra.im_mul]
          ring
  · rintro ⟨htrace, hnorm⟩
    obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.mp htrace
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hnorm
    let p : Polynomial ℤ :=
      Polynomial.X ^ 2 + (Polynomial.C (-t) * Polynomial.X + Polynomial.C n)
    refine ⟨p, ?_, ?_⟩
    · apply Polynomial.monic_X_pow_add
      simpa using Polynomial.degree_linear_lt (a := -t) (b := n)
    · change Polynomial.eval₂ (algebraMap ℤ (QFModel m)) x p = 0
      have hEval :
          Polynomial.eval₂ (algebraMap ℤ (QFModel m)) x p =
            x ^ 2 + (-algebraMap ℤ (QFModel m) t * x +
              algebraMap ℤ (QFModel m) n) := by
        dsimp [p]
        rw [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
          Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
          Polynomial.eval₂_X, Polynomial.eval₂_C, map_neg]
        rfl
      rw [hEval]
      change (t : ℚ) = 2 * x.re at ht
      change (n : ℚ) = x.re ^ 2 - (m : ℚ) * x.im ^ 2 at hn
      apply QuadraticAlgebra.ext
      · simp only [pow_two, eq_intCast, neg_mul, QuadraticAlgebra.re_add,
          QuadraticAlgebra.re_neg, QuadraticAlgebra.re_mul,
          QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast, mul_zero,
          zero_mul, add_zero, QuadraticAlgebra.re_zero]
        rw [ht, hn]
        ring_nf
      · simp only [pow_two, eq_intCast, neg_mul, QuadraticAlgebra.im_add,
          QuadraticAlgebra.im_neg, QuadraticAlgebra.im_mul,
          QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast, zero_mul,
          add_zero, mul_zero, QuadraticAlgebra.im_zero]
        rw [ht]
        ring_nf

private theorem rat_squarefree_sq
    (m : ℤ) (hm : Squarefree m) (q : ℚ)
    (h : IsIntegral ℤ ((m : ℚ) * q ^ 2)) : IsIntegral ℤ q := by
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  change (z : ℚ) = (m : ℚ) * q ^ 2 at hz
  have hqden : q * (q.den : ℚ) = q.num := by
    nth_rw 1 [← Rat.num_div_den q]
    field_simp
  have heqZ : m * q.num ^ 2 = z * (q.den : ℤ) ^ 2 := by
    apply Rat.intCast_injective
    calc
      ((m * q.num ^ 2 : ℤ) : ℚ) = (m : ℚ) * (q.num : ℚ) ^ 2 := by norm_cast
      _ = (m : ℚ) * q ^ 2 * (q.den : ℚ) ^ 2 := by
        rw [← hqden]
        ring
      _ = (z : ℚ) * (q.den : ℚ) ^ 2 := by rw [← hz]
      _ = ((z * (q.den : ℤ) ^ 2 : ℤ) : ℚ) := by norm_cast
  have heqN := congrArg Int.natAbs heqZ
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at heqN
  have hdvd : q.den * q.den ∣ m.natAbs * (q.num.natAbs * q.num.natAbs) := by
    refine ⟨z.natAbs, ?_⟩
    simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using heqN
  have hdvdNum : q.den ∣ q.num.natAbs * q.num.natAbs :=
    Squarefree.dvd_of_squarefree_of_mul_dvd_mul_right
      (Int.squarefree_natAbs.mpr hm) hdvd
  have hcop : q.den.Coprime (q.num.natAbs ^ 2) := q.reduced.symm.pow_right 2
  have hdvdOne : q.den ∣ 1 := hcop.dvd_of_dvd_mul_right <| by
    simpa [pow_two] using hdvdNum
  have hden : q.den = 1 := Nat.dvd_one.mp hdvdOne
  exact IsIntegrallyClosed.isIntegral_iff.mpr ⟨q.num, (Rat.den_eq_one_iff q).mp hden⟩

private lemma even_emod_four {a : ℤ} (ha : Even a) : a ^ 2 % 4 = 0 := by
  obtain ⟨k, rfl⟩ := ha
  ring_nf
  simp

private lemma even_coordinates_four
    {m a b : ℤ} (hm4 : ¬4 ∣ m) (hm1 : m % 4 ≠ 1)
    (hdiv : 4 ∣ a ^ 2 - m * b ^ 2) : Even a ∧ Even b := by
  have hmod : (a ^ 2 - m * b ^ 2) % 4 = 0 :=
    Int.dvd_iff_emod_eq_zero.mp hdiv
  by_cases hb : Even b
  · refine ⟨?_, hb⟩
    by_contra ha
    have haodd : Odd a := Int.not_even_iff_odd.mp ha
    rw [Int.sub_emod, Int.mul_emod, Int.sq_mod_four_eq_one_of_odd haodd,
      even_emod_four hb] at hmod
    norm_num at hmod
  · have hbodd : Odd b := Int.not_even_iff_odd.mp hb
    by_cases ha : Even a
    · have hma : m % 4 = 0 := by
        rw [Int.sub_emod, Int.mul_emod, even_emod_four ha,
          Int.sq_mod_four_eq_one_of_odd hbodd] at hmod
        omega
      exact False.elim <| hm4 (Int.dvd_iff_emod_eq_zero.mpr hma)
    · have haodd : Odd a := Int.not_even_iff_odd.mp ha
      have hma : m % 4 = 1 := by
        rw [Int.sub_emod, Int.mul_emod, Int.sq_mod_four_eq_one_of_odd haodd,
          Int.sq_mod_four_eq_one_of_odd hbodd] at hmod
        omega
      exact False.elim <| hm1 hma

private lemma same_parity_four
    {m a b : ℤ} (hm1 : m % 4 = 1)
    (hdiv : 4 ∣ a ^ 2 - m * b ^ 2) : Even (a - b) := by
  have hmod : (a ^ 2 - m * b ^ 2) % 4 = 0 :=
    Int.dvd_iff_emod_eq_zero.mp hdiv
  rw [Int.even_sub]
  constructor
  · intro ha
    by_contra hb
    have hbodd : Odd b := Int.not_even_iff_odd.mp hb
    rw [Int.sub_emod, Int.mul_emod, even_emod_four ha,
      Int.sq_mod_four_eq_one_of_odd hbodd, hm1] at hmod
    norm_num at hmod
  · intro hb
    by_contra ha
    have haodd : Odd a := Int.not_even_iff_odd.mp ha
    rw [Int.sub_emod, Int.mul_emod, Int.sq_mod_four_eq_one_of_odd haodd,
      even_emod_four hb, hm1] at hmod
    norm_num at hmod

/-- Proposition 23 reduced to doubled integer coordinates and one congruence modulo four. -/
theorem integral_doubled_coordinates
    (m : ℤ) (hm : Squarefree m) (x : QFModel m) :
    IsIntegral ℤ x ↔
      ∃ a b : ℤ,
        (a : ℚ) = 2 * x.re ∧
        (b : ℚ) = 2 * x.im ∧
        4 ∣ a ^ 2 - m * b ^ 2 := by
  rw [integral_trace_norm]
  constructor
  · rintro ⟨htrace, hnorm⟩
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp htrace
    have hscaledNorm : IsIntegral ℤ ((m : ℚ) * (2 * x.im) ^ 2) := by
      have hfour : IsIntegral ℤ (4 : ℚ) := isIntegral_algebraMap
      have h := (htrace.pow 2).sub (hfour.mul hnorm)
      rw [show (m : ℚ) * (2 * x.im) ^ 2 =
          (2 * x.re) ^ 2 - 4 * (x.re ^ 2 - (m : ℚ) * x.im ^ 2) by ring]
      exact h
    have him := rat_squarefree_sq m hm (2 * x.im) hscaledNorm
    obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp him
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hnorm
    refine ⟨a, b, ?_, ?_, ?_⟩
    · exact ha
    · exact hb
    · refine ⟨n, ?_⟩
      apply Rat.intCast_injective
      change ((a ^ 2 - m * b ^ 2 : ℤ) : ℚ) = ((4 * n : ℤ) : ℚ)
      push_cast
      change (a : ℚ) = 2 * x.re at ha
      change (b : ℚ) = 2 * x.im at hb
      change (n : ℚ) = x.re ^ 2 - (m : ℚ) * x.im ^ 2 at hn
      rw [ha, hb, hn]
      ring
  · rintro ⟨a, b, ha, hb, n, hn⟩
    constructor
    · rw [← ha]
      exact isIntegral_algebraMap
    · have hnorm : (n : ℚ) = x.re ^ 2 - (m : ℚ) * x.im ^ 2 := by
        have hnQ := congrArg (fun z : ℤ => (z : ℚ)) hn
        push_cast at hnQ
        rw [ha, hb] at hnQ
        nlinarith
      rw [← hnorm]
      exact isIntegral_algebraMap

private lemma not_dvd_squarefree {m : ℤ} (hm : Squarefree m) : ¬4 ∣ m := by
  intro hfour
  have hunit : IsUnit (2 : ℤ) := hm 2 <| by
    simpa using hfour
  rw [Int.isUnit_iff] at hunit
  omega

/-- Proposition 23 in the case `m % 4 ≠ 1`: the algebraic integers have integral coordinates. -/
theorem integral_integer_coordinates
    (m : ℤ) (hm : Squarefree m) (hm1 : m % 4 ≠ 1)
    (x : QFModel m) :
    IsIntegral ℤ x ↔
      ∃ a b : ℤ, x.re = (a : ℚ) ∧ x.im = (b : ℚ) := by
  rw [integral_doubled_coordinates m hm x]
  constructor
  · rintro ⟨a, b, ha, hb, hdiv⟩
    obtain ⟨haeven, hbeven⟩ :=
      even_coordinates_four (not_dvd_squarefree hm) hm1 hdiv
    obtain ⟨c, hc⟩ := haeven
    obtain ⟨d, hd⟩ := hbeven
    refine ⟨c, d, ?_, ?_⟩
    · change (a : ℚ) = 2 * x.re at ha
      rw [hc] at ha
      push_cast at ha
      linarith
    · change (b : ℚ) = 2 * x.im at hb
      rw [hd] at hb
      push_cast at hb
      linarith
  · rintro ⟨a, b, ha, hb⟩
    refine ⟨2 * a, 2 * b, ?_, ?_, ?_⟩
    · push_cast
      linarith
    · push_cast
      linarith
    · refine ⟨a ^ 2 - m * b ^ 2, ?_⟩
      ring

/-- Proposition 23 in the case `m % 4 = 1`: the algebraic integers are generated by
`(1 + ω) / 2`. -/
theorem integral_half_coordinates
    (m : ℤ) (hm : Squarefree m) (hm1 : m % 4 = 1)
    (x : QFModel m) :
    IsIntegral ℤ x ↔
      ∃ a b : ℤ,
        x.re = (a : ℚ) + (b : ℚ) / 2 ∧
        x.im = (b : ℚ) / 2 := by
  rw [integral_doubled_coordinates m hm x]
  constructor
  · rintro ⟨a, b, ha, hb, hdiv⟩
    obtain ⟨c, hc⟩ := same_parity_four hm1 hdiv
    refine ⟨c, b, ?_, ?_⟩
    · change (a : ℚ) = 2 * x.re at ha
      change (b : ℚ) = 2 * x.im at hb
      have hcQ := congrArg (fun z : ℤ => (z : ℚ)) hc
      push_cast at hcQ
      linarith
    · change (b : ℚ) = 2 * x.im at hb
      linarith
  · rintro ⟨a, b, ha, hb⟩
    refine ⟨2 * a + b, b, ?_, ?_, ?_⟩
    · push_cast
      linarith
    · linarith
    · obtain ⟨k, hk⟩ := Int.dvd_self_sub_of_emod_eq hm1
      refine ⟨a ^ 2 + a * b - k * b ^ 2, ?_⟩
      nlinarith

/-- Corollary 24: the algebraic integers in the model `ℚ[i]` are the Gaussian integers. -/
theorem gaussian_integer_coordinates
    (x : QFModel (-1)) :
    IsIntegral ℤ x ↔
      ∃ a b : ℤ, x.re = (a : ℚ) ∧ x.im = (b : ℚ) := by
  apply integral_integer_coordinates
  · exact (isUnit_neg_one : IsUnit (-1 : ℤ)).squarefree
  · norm_num

end QFModel

end Towers.NumberTheory
