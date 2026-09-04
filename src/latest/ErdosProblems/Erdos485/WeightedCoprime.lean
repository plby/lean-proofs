import ErdosProblems.Erdos485.Bivariate
import ErdosProblems.Erdos485.Weighted
import ErdosProblems.Erdos485.SquarefreeFactor
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Coprimality for the weighted Euler derivative

This file proves the distinct-weight coprimality input in Schinzel's
squarefree-gap argument.  The final statement is over `K(z)[y]`, because
that is the coefficient field used by the resultant.
-/

namespace Erdos485

open Polynomial
open scoped Polynomial.Bivariate

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- The two-variable weight, in Mathlib's bivariate convention: coordinate
`0` is the inner variable and coordinate `1` is the outer variable. -/
def mvWeight (n : ℕ) : Fin 2 → ℕ := ![1, n]

/-- The exponent vector corresponding to `y^a z^b`. -/
def mvExponent (a b : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 b + Finsupp.single 1 a

@[simp] theorem mvExponent_zero_apply (a b : ℕ) : mvExponent a b 0 = b := by
  simp [mvExponent]

@[simp] theorem mvExponent_one_apply (a b : ℕ) : mvExponent a b 1 = a := by
  simp [mvExponent]

theorem mvExponent_eq (d : Fin 2 →₀ ℕ) : d = mvExponent (d 1) (d 0) := by
  ext i
  fin_cases i <;> simp

@[simp] theorem mv_weight_mvExponent (n a b : ℕ) :
    Finsupp.weight (mvWeight n) (mvExponent a b) = n * a + b := by
  simp [Finsupp.weight, mvWeight, mvExponent, Nat.add_comm, Nat.mul_comm]

theorem mvExponent_inj {a b a' b' : ℕ} :
    mvExponent a b = mvExponent a' b' ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (fun d : Fin 2 →₀ ℕ ↦ d 1) h,
      by simpa using congrArg (fun d : Fin 2 →₀ ℕ ↦ d 0) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] theorem equivMvPolynomial_biMonomial (a b : ℕ) (c : K) :
    Polynomial.Bivariate.equivMvPolynomial K (biMonomial a b c) =
      MvPolynomial.monomial (mvExponent a b) c := by
  rw [show biMonomial a b c = C (C c) * (C X) ^ b * X ^ a by
    simp [biMonomial, ← C_mul_X_pow_eq_monomial]]
  simp only [map_mul, map_pow, Polynomial.Bivariate.equivMvPolynomial_C_C,
    Polynomial.Bivariate.equivMvPolynomial_C_X,
    Polynomial.Bivariate.equivMvPolynomial_X]
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.C_mul_monomial, MvPolynomial.monomial_mul]
  simp [mvExponent, add_comm]

@[simp] theorem coeff_equivMvPolynomial_mvExponent (F : BiPolynomial K) (a b : ℕ) :
    MvPolynomial.coeff (mvExponent a b)
        (Polynomial.Bivariate.equivMvPolynomial K F) = biCoeff F a b := by
  induction F using Polynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ, biCoeff]
  | monomial i p =>
      induction p using Polynomial.induction_on' with
      | add p q hp hq => simp [map_add, hp, hq, biCoeff]
      | monomial j c =>
          rw [show monomial i (monomial j c) = biMonomial i j c by rfl,
            equivMvPolynomial_biMonomial]
          simp only [MvPolynomial.coeff_monomial, biCoeff_biMonomial]
          simp [mvExponent_inj, eq_comm]

theorem mem_support_equivMvPolynomial_iff (F : BiPolynomial K) (d : Fin 2 →₀ ℕ) :
    d ∈ (Polynomial.Bivariate.equivMvPolynomial K F).support ↔
      (d 1, d 0) ∈ exponentPairs F := by
  rw [MvPolynomial.mem_support_iff, mem_exponentPairs_iff]
  rw [← coeff_equivMvPolynomial_mvExponent F (d 1) (d 0), ← mvExponent_eq d]

theorem mv_weight_eq_exponentWeight (n : ℕ) (d : Fin 2 →₀ ℕ) :
    Finsupp.weight (mvWeight n) d = exponentWeight n (d 1, d 0) := by
  rw [mvExponent_eq d, mv_weight_mvExponent]
  simp [exponentWeight]

/-- A weighted-Euler eigenvector becomes weighted homogeneous after the
bivariate polynomial is identified with an `MvPolynomial`. -/
theorem isWeightedHomogeneous_equivMvPolynomial_of_eigen
    {n : ℕ} {G : BiPolynomial K} {lam : K}
    (hG : G ≠ 0) (heig : weightedEuler n G = C (C lam) * G) :
    ∃ m : ℕ, MvPolynomial.IsWeightedHomogeneous (mvWeight n)
      (Polynomial.Bivariate.equivMvPolynomial K G) m := by
  let P := Polynomial.Bivariate.equivMvPolynomial K G
  have hP : P ≠ 0 := by
    intro hz
    apply hG
    apply (Polynomial.Bivariate.equivMvPolynomial K).injective
    simpa [P] using hz
  obtain ⟨d₀, hd₀⟩ := MvPolynomial.exists_coeff_ne_zero hP
  refine ⟨Finsupp.weight (mvWeight n) d₀, ?_⟩
  intro d hd
  have hdG : biCoeff G (d 1) (d 0) ≠ 0 := by
    rw [← coeff_equivMvPolynomial_mvExponent G (d 1) (d 0), ← mvExponent_eq d]
    exact hd
  have hd₀G : biCoeff G (d₀ 1) (d₀ 0) ≠ 0 := by
    rw [← coeff_equivMvPolynomial_mvExponent G (d₀ 1) (d₀ 0), ← mvExponent_eq d₀]
    exact hd₀
  rw [mv_weight_eq_exponentWeight, mv_weight_eq_exponentWeight]
  exact weights_eq_of_weightedEuler_eq_smul heig hdG hd₀G

/-- If a polynomial has at most one monomial in each weight and is divisible
by a nonzero weighted-homogeneous polynomial, that divisor divides a variable
monomial.  This is the graded-ideal form of the distinct-weight argument. -/
theorem exists_dvd_X_of_weightedHomogeneous_dvd_weightInjective
    {n m : ℕ} {P Q : MvPolynomial (Fin 2) K}
    (hP : P ≠ 0)
    (hPirred : Irreducible P)
    (hQ : Q ≠ 0)
    (hhom : MvPolynomial.IsWeightedHomogeneous (mvWeight n) P m)
    (hPQ : P ∣ Q)
    (hinj : Set.InjOn (Finsupp.weight (mvWeight n)) (Q.support : Set (Fin 2 →₀ ℕ))) :
    ∃ i : Fin 2, P ∣ MvPolynomial.X i := by
  classical
  obtain ⟨d, hd⟩ := MvPolynomial.exists_coeff_ne_zero hQ
  let w := mvWeight n
  let := MvPolynomial.weightedGradedAlgebra K w
  let I : Ideal (MvPolynomial (Fin 2) K) := Ideal.span {P}
  have hIhom : I.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨m, hhom⟩
  have hQI : Q ∈ I := by
    rw [show I = Ideal.span {P} by rfl, Ideal.mem_span_singleton]
    exact hPQ
  let Qd := MvPolynomial.weightedHomogeneousComponent w (Finsupp.weight w d) Q
  have hQdI : Qd ∈ I :=
    MvPolynomial.weightedHomogeneousComponent_mem_of_mem K w hIhom hQI _
  have hQdEq : Qd = MvPolynomial.monomial d (MvPolynomial.coeff d Q) := by
    calc
      Qd = MvPolynomial.monomial d (MvPolynomial.coeff d Qd) := by
        apply MvPolynomial.eq_monomial_of_support_subset_singleton
        intro e he
        have hec := MvPolynomial.mem_support_iff.mp he
        have hc := MvPolynomial.coeff_weightedHomogeneousComponent
          (w := w) (Finsupp.weight w d) Q e
        have hwt : Finsupp.weight w e = Finsupp.weight w d :=
          (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
            (w := w) (Finsupp.weight w d) Q) hec
        rw [show Qd = MvPolynomial.weightedHomogeneousComponent w
          (Finsupp.weight w d) Q by rfl, hc, if_pos hwt] at hec
        have heQ : e ∈ Q.support := MvPolynomial.mem_support_iff.mpr hec
        exact hinj heQ (MvPolynomial.mem_support_iff.mpr hd) hwt
      _ = MvPolynomial.monomial d (MvPolynomial.coeff d Q) := by
        congr 1
        simp [Qd, MvPolynomial.coeff_weightedHomogeneousComponent]
  have hPmono : P ∣ MvPolynomial.monomial d (MvPolynomial.coeff d Q) := by
    rw [← hQdEq, ← Ideal.mem_span_singleton]
    exact hQdI
  have hcUnit : IsUnit (MvPolynomial.C (MvPolynomial.coeff d Q) : MvPolynomial (Fin 2) K) :=
    (isUnit_iff_ne_zero.mpr hd).map MvPolynomial.C
  rw [MvPolynomial.monomial_eq] at hPmono
  have hPprod : P ∣ d.prod (fun i e ↦ (MvPolynomial.X i : MvPolynomial (Fin 2) K) ^ e) :=
    (IsUnit.dvd_mul_left hcUnit).mp hPmono
  -- A prime factor of a finite product divides one of its variable factors.
  have hPprime : Prime P := hPirred.prime
  have hPprod' : P ∣ ∏ i ∈ d.support,
      (MvPolynomial.X i : MvPolynomial (Fin 2) K) ^ d i := by
    simpa only [Finsupp.prod] using hPprod
  obtain ⟨i, _hi, hpi⟩ := (hPprime.dvd_finsetProd_iff
    (fun i ↦ (MvPolynomial.X i : MvPolynomial (Fin 2) K) ^ d i)).mp hPprod'
  exact ⟨i, hPprime.dvd_of_dvd_pow hpi⟩

/-- In the bivariate UFD, a squarefree factor of a nonzero thin polynomial
has no common irreducible factor with its weighted Euler derivative. -/
theorem isRelPrime_weightedEuler_of_squarefree_dvd_weightInjective
    {n : ℕ} (hn : 0 < n) {F H : BiPolynomial K}
    (hF : F ≠ 0) (hsq : Squarefree H) (hHF : H ∣ F)
    (hY : ¬(X : BiPolynomial K) ∣ H)
    (hZ : ¬(C X : BiPolynomial K) ∣ H)
    (hinj : Set.InjOn (exponentWeight n) (exponentPairs F : Set (ℕ × ℕ))) :
    IsRelPrime H (weightedEuler n H) := by
  apply WfDvdMonoid.isRelPrime_of_no_irreducible_factors
  · exact fun hz ↦ hsq.ne_zero hz.1
  · intro p hp hpH hpD
    have hpconst : ∀ c : K, p ≠ C (C c) := by
      intro c hpc
      by_cases hc : c = 0
      · subst c
        apply hp.ne_zero
        simpa using hpc
      · apply hp.not_isUnit
        rw [hpc]
        exact Polynomial.isUnit_C.mpr
          (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc))
    obtain ⟨lam, heig⟩ :=
      common_irreducible_factor_weightedHomogeneous hn hsq hp hpH hpD hpconst
    obtain ⟨m, hhom⟩ :=
      isWeightedHomogeneous_equivMvPolynomial_of_eigen hp.ne_zero heig
    let e := Polynomial.Bivariate.equivMvPolynomial K
    have hpMv : Irreducible (e p) := hp.map e.toMulEquiv
    have hFMv : e F ≠ 0 := by
      intro hz
      apply hF
      apply e.injective
      simpa using hz
    have hpFMv : e p ∣ e F := by
      exact map_dvd e.toMonoidHom (hpH.trans hHF)
    have hinjMv : Set.InjOn (Finsupp.weight (mvWeight n))
        ((e F).support : Set (Fin 2 →₀ ℕ)) := by
      intro d hd d' hd' hwt
      have hpair : (d 1, d 0) = (d' 1, d' 0) := by
        apply hinj
        · exact (mem_support_equivMvPolynomial_iff F d).mp hd
        · exact (mem_support_equivMvPolynomial_iff F d').mp hd'
        · simpa only [mv_weight_eq_exponentWeight] using hwt
      apply Finsupp.ext
      intro i
      fin_cases i
      · exact congrArg Prod.snd hpair
      · exact congrArg Prod.fst hpair
    obtain ⟨i, hpi⟩ :=
      exists_dvd_X_of_weightedHomogeneous_dvd_weightInjective
        hpMv.ne_zero hpMv hFMv hhom hpFMv hinjMv
    have hXi : Irreducible (MvPolynomial.X i : MvPolynomial (Fin 2) K) :=
      MvPolynomial.X_prime.irreducible
    have hassocMv : Associated (e p) (MvPolynomial.X i) :=
      hpMv.associated_of_dvd hXi hpi
    have haxisP : e.symm (MvPolynomial.X i) ∣ p := by
      obtain ⟨q, hq⟩ := hassocMv.dvd'
      refine ⟨e.symm q, ?_⟩
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using hq
    by_cases hi : i = 0
    · subst i
      apply hZ
      rw [Polynomial.Bivariate.equivMvPolynomial_symm_X_0] at haxisP
      exact haxisP.trans hpH
    · rw [Fin.eq_one_of_ne_zero i hi] at haxisP
      apply hY
      rw [Polynomial.Bivariate.equivMvPolynomial_symm_X_1] at haxisP
      exact haxisP.trans hpH

/-- The localized coprimality statement used by the resultant.  Passing to
the fraction field turns relative primality into Bezout coprimality.  The
only subtle point is descent of a possible common factor; its primitive
integer normalization descends by Gauss's lemma. -/
theorem weightedEuler_isCoprime_fractionRing_of_squarefree_dvd_weightInjective
    {n : ℕ} (hn : 0 < n) {F H : BiPolynomial K}
    (hF : F ≠ 0) (hsq : Squarefree H) (hHF : H ∣ F)
    (hY : ¬(X : BiPolynomial K) ∣ H)
    (hZ : ¬(C X : BiPolynomial K) ∣ H)
    (hinj : Set.InjOn (exponentWeight n) (exponentPairs F : Set (ℕ × ℕ))) :
    IsCoprime
      (H.map (algebraMap (Polynomial K) (FractionRing (Polynomial K))))
      ((weightedEuler n H).map
        (algebraMap (Polynomial K) (FractionRing (Polynomial K)))) := by
  let ι := algebraMap (Polynomial K) (FractionRing (Polynomial K))
  let : NormalizedGCDMonoid (Polynomial K) := Nonempty.some inferInstance
  have hrel : IsRelPrime H (weightedEuler n H) :=
    isRelPrime_weightedEuler_of_squarefree_dvd_weightInjective
      hn hF hsq hHF hY hZ hinj
  apply isCoprime_of_irreducible_dvd
  · intro hz
    exact ((Polynomial.map_ne_zero_iff (IsFractionRing.injective
      (Polynomial K) (FractionRing (Polynomial K)))).2 hsq.ne_zero) hz.1
  · intro g hg hgH hgD
    let J : Polynomial (Polynomial K) :=
      IsLocalization.integerNormalization (nonZeroDivisors (Polynomial K)) g
    let p : Polynomial (Polynomial K) := J.primPart
    obtain ⟨b, hb, hJ⟩ :=
      IsLocalization.integerNormalization_spec (nonZeroDivisors (Polynomial K)) g
    have hb0 : (b : Polynomial K) ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbι0 : ι (b : Polynomial K) ≠ 0 := by
      intro hz
      apply hb0
      exact (map_eq_zero_iff ι (IsFractionRing.injective
        (Polynomial K) (FractionRing (Polynomial K)))).mp hz
    have hsmul : (b : Polynomial K) • g ≠ 0 := by
      rw [Algebra.smul_def]
      change C (ι (b : Polynomial K)) * g ≠ 0
      exact mul_ne_zero (C_ne_zero.mpr hbι0) hg.ne_zero
    have hJmap0 : J.map ι ≠ 0 := by
      rw [show J.map ι = (b : Polynomial K) • g by simpa [J] using hJ]
      exact hsmul
    have hJ0 : J ≠ 0 := by
      intro hz
      apply hJmap0
      simp [hz]
    have hc0 : J.content ≠ 0 := by
      intro hz
      apply hJ0
      exact content_eq_zero_iff.mp hz
    have hcι0 : ι J.content ≠ 0 :=
      fun hz ↦ hc0 ((map_eq_zero_iff ι (IsFractionRing.injective
        (Polynomial K) (FractionRing (Polynomial K)))).mp hz)
    have hcUnit : IsUnit
        (C (ι J.content) : Polynomial (FractionRing (Polynomial K))) :=
      Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcι0)
    have hbUnit : IsUnit
        (C (ι (b : Polynomial K)) : Polynomial (FractionRing (Polynomial K))) :=
      Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hbι0)
    have hfac : J.map ι = C (ι J.content) * p.map ι := by
      calc
        J.map ι = (C J.content * p).map ι := by
          congr 1
          simpa [p] using J.eq_C_content_mul_primPart
        _ = C (ι J.content) * p.map ι := by
          rw [Polynomial.map_mul, Polynomial.map_C]
    have hscalar : J.map ι = C (ι (b : Polynomial K)) * g := by
      simpa [J, Algebra.smul_def] using hJ
    have hJp : Associated (J.map ι) (p.map ι) := by
      rw [hfac, mul_comm]
      exact associated_mul_unit_left _ _ hcUnit
    have hJg : Associated (J.map ι) g := by
      rw [hscalar, mul_comm]
      exact associated_mul_unit_left _ _ hbUnit
    have hpg : Associated (p.map ι) g := hJp.symm.trans hJg
    have hpHmap : p.map ι ∣ H.map ι := hpg.dvd.trans hgH
    have hpDmap : p.map ι ∣ (weightedEuler n H).map ι := hpg.dvd.trans hgD
    have hpH : p ∣ H :=
      J.isPrimitive_primPart.dvd_of_fraction_map_dvd_fraction_map hpHmap
    have hpD : p ∣ weightedEuler n H :=
      J.isPrimitive_primPart.dvd_of_fraction_map_dvd_fraction_map hpDmap
    have hpUnit : IsUnit p := hrel hpH hpD
    have hpMapUnit : IsUnit (p.map ι) :=
      hpUnit.map (Polynomial.mapRingHom ι)
    exact hg.not_isUnit (hpg.isUnit_iff.mp hpMapUnit)

end

end Erdos485
