/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RationalStepanovDegree

/-!
# Nonvanishing of the rational Stepanov auxiliary polynomial

At a supported pole, distinct nonzero auxiliary summands have distinct local
orders.  The coefficient-polynomial order occupies the lowest digit, the
homogeneous numerator index the next base-`p` digit, and the centered
full-extension monomial the remaining digits.  Hence the summand of least
order cannot cancel.
-/

namespace Erdos387

open Polynomial
open scoped BigOperators
open Waring.Analytic.Stepanov

namespace RationalStepanov

theorem rootMultiplicity_pow_of_ne_zero
    {E : Type*} [Field E] {P : E[X]} (hP : P ≠ 0) (r : E) (n : ℕ) :
    (P ^ n).rootMultiplicity r = n * P.rootMultiplicity r := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hP) hP),
        ih]
      ring

/-- The exact local order of one auxiliary summand before substituting the
specific rational-trace pole orders. -/
theorem rootMultiplicity_rationalAuxiliaryTerm
    {E : Type*} [Field E] {p h i k : ℕ} [Fact p.Prime]
    [CharP E p] (hp : 0 < p) (pole : E) (e lowN lowD : E[X])
    (he : e ≠ 0) (hN : lowN ≠ 0) (hD : lowD ≠ 0)
    (hfixed : pole ^ (p ^ (h + 3)) = pole) :
    (rationalAuxiliaryTerm p h pole i k e lowN lowD).rootMultiplicity pole =
      e.rootMultiplicity pole + p ^ (h + 3) *
        (i * lowN.rootMultiplicity pole +
          (p - 1 - i) * lowD.rootMultiplicity pole + p ^ (h + 3) * k) := by
  rw [rationalAuxiliaryTerm]
  have hcenter : ((X - C pole) ^ k : E[X]) ≠ 0 :=
    pow_ne_zero _ (X_sub_C_ne_zero pole)
  have hcenterExpand : expand E (p ^ (h + 3)) ((X - C pole) ^ k) ≠ 0 :=
    (expand_ne_zero (Nat.pow_pos hp)).mpr hcenter
  have hlowPowers : lowN ^ i * lowD ^ (p - 1 - i) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hN) (pow_ne_zero _ hD)
  have hinner :
      lowN ^ i * lowD ^ (p - 1 - i) *
        expand E (p ^ (h + 3)) ((X - C pole) ^ k) ≠ 0 :=
    mul_ne_zero hlowPowers hcenterExpand
  have houter : expand E (p ^ (h + 3))
      (lowN ^ i * lowD ^ (p - 1 - i) *
        expand E (p ^ (h + 3)) ((X - C pole) ^ k)) ≠ 0 :=
    (expand_ne_zero (Nat.pow_pos hp)).mpr hinner
  rw [rootMultiplicity_mul (mul_ne_zero he houter),
    rootMultiplicity_expand_pow, hfixed,
    rootMultiplicity_mul hinner,
    rootMultiplicity_mul hlowPowers,
    rootMultiplicity_pow_of_ne_zero hN,
    rootMultiplicity_pow_of_ne_zero hD,
    rootMultiplicity_expand_pow, hfixed,
    rootMultiplicity_X_sub_C_pow]

/-- Mixed-radix local-order label for a nonzero auxiliary summand. -/
def rationalPoleOrderLabel (p h eOrder i k : ℕ) : ℕ :=
  p ^ (h + 3) * ((p - 1) * frobeniusOrderSum p (h + 2)) + eOrder +
    p ^ (2 * (h + 3) - 1) * ((p - 1 - i) + p * k)

/-- The exact supported-pole order of a nonzero rational auxiliary term. -/
theorem rootMultiplicity_rationalAuxiliaryTerm_eq_label
    {p h i k : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [CharP E p] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) {r : ZMod p}
    (hr : r ∈ InverseRational.poleSupport coeff)
    (hiIndex : i < p) (e : E[X]) (he : e ≠ 0) :
    let pole := algebraMap (ZMod p) E r
    let lowN := lowRationalNumerator p (h + 3)
      (mappedSimplePoleNumeratorPolynomial (E := E) coeff)
      (mappedSimplePoleDenominatorPolynomial (E := E) coeff)
    let lowD := lowRationalDenominator p (h + 3)
      (mappedSimplePoleDenominatorPolynomial (E := E) coeff)
    (rationalAuxiliaryTerm p h pole i k e lowN lowD).rootMultiplicity pole =
      rationalPoleOrderLabel p h (e.rootMultiplicity pole) i k := by
  dsimp only
  let pole := algebraMap (ZMod p) E r
  let A := mappedSimplePoleNumeratorPolynomial (E := E) coeff
  let B := mappedSimplePoleDenominatorPolynomial (E := E) coeff
  let lowN := lowRationalNumerator p (h + 3) A B
  let lowD := lowRationalDenominator p (h + 3) B
  have hm : 0 < h + 3 := by omega
  obtain ⟨hD, hDord, hN, hNord⟩ :=
    lowRationalPoleOrders (E := E) coeff hr (h + 3) hm
  change lowD ≠ 0 at hD
  change lowD.rootMultiplicity pole = frobeniusOrderSum p (h + 3) at hDord
  change lowN ≠ 0 at hN
  change lowN.rootMultiplicity pole = frobeniusOrderSum p (h + 2) at hNord
  have hfixed : pole ^ (p ^ (h + 3)) = pole := by
    change iterateFrobenius E p (h + 3) pole = pole
    exact iterateFrobenius_algebraMap_zmod (h + 3) r
  have hraw := rootMultiplicity_rationalAuxiliaryTerm
    (p := p) (h := h) (i := i) (k := k)
    (Fact.out : p.Prime).pos pole e lowN lowD he hN hD hfixed
  rw [hraw, hNord, hDord]
  unfold rationalPoleOrderLabel
  rw [frobeniusOrderSum_succ p (h + 2)]
  have hi : p ^ (h + 3) * p ^ (h + 2) = p ^ (2 * (h + 3) - 1) := by
    rw [← pow_add]
    congr 1 <;> omega
  have hJ :
      p ^ (h + 3) * ((p - 1 - i) * p ^ (h + 2)) =
        p ^ (2 * (h + 3) - 1) * (p - 1 - i) := by
    calc
      p ^ (h + 3) * ((p - 1 - i) * p ^ (h + 2)) =
          (p ^ (h + 3) * p ^ (h + 2)) * (p - 1 - i) := by ring
      _ = p ^ (2 * (h + 3) - 1) * (p - 1 - i) := by rw [hi]
  have hq :
      p ^ (h + 3) * p ^ (h + 3) =
        p ^ (2 * (h + 3) - 1) * p := by
    calc
      p ^ (h + 3) * p ^ (h + 3) = p ^ ((h + 3) + (h + 3)) :=
        (pow_add _ _ _).symm
      _ = p ^ ((2 * (h + 3) - 1) + 1) :=
        congrArg (fun n : ℕ => p ^ n) (by omega)
      _ = p ^ (2 * (h + 3) - 1) * p := by rw [pow_add, pow_one]
  have hK :
      p ^ (h + 3) * (p ^ (h + 3) * k) =
        p ^ (2 * (h + 3) - 1) * (p * k) := by
    calc
      p ^ (h + 3) * (p ^ (h + 3) * k) =
          (p ^ (h + 3) * p ^ (h + 3)) * k := by ring
      _ = (p ^ (2 * (h + 3) - 1) * p) * k := by rw [hq]
      _ = p ^ (2 * (h + 3) - 1) * (p * k) := by ring
  have hi' : i ≤ p - 1 := by omega
  have hij : i + (p - 1 - i) = p - 1 := Nat.add_sub_of_le hi'
  have hphase :
      i * frobeniusOrderSum p (h + 2) +
          (p - 1 - i) *
            (frobeniusOrderSum p (h + 2) + p ^ (h + 2)) =
        (p - 1) * frobeniusOrderSum p (h + 2) +
          (p - 1 - i) * p ^ (h + 2) := by
    rw [Nat.mul_add]
    calc
      i * frobeniusOrderSum p (h + 2) +
          ((p - 1 - i) * frobeniusOrderSum p (h + 2) +
            (p - 1 - i) * p ^ (h + 2)) =
          (i + (p - 1 - i)) * frobeniusOrderSum p (h + 2) +
            (p - 1 - i) * p ^ (h + 2) := by ring
      _ = (p - 1) * frobeniusOrderSum p (h + 2) +
          (p - 1 - i) * p ^ (h + 2) := by rw [hij]
  have harith :
      e.rootMultiplicity pole + p ^ (h + 3) *
          (i * frobeniusOrderSum p (h + 2) +
            (p - 1 - i) *
              (frobeniusOrderSum p (h + 2) + p ^ (h + 2)) +
            p ^ (h + 3) * k) =
        p ^ (h + 3) * ((p - 1) * frobeniusOrderSum p (h + 2)) +
          e.rootMultiplicity pole +
          p ^ (2 * (h + 3) - 1) * ((p - 1 - i) + p * k) := by
    rw [hphase, Nat.mul_add, Nat.mul_add, hJ, hK]
    ring
  exact harith

/-- A nonzero coefficient family has a nonzero encoded coefficient
polynomial. -/
theorem exists_rationalAuxiliaryCoefficientPolynomial_ne_zero
    {E : Type*} [Field E] {p h : ℕ}
    {a : AuxiliaryCoefficients E p h} (ha : a ≠ 0) :
    ∃ i : Fin p, ∃ k : Fin (K p h + 1),
      auxiliaryCoefficientPolynomial a i k ≠ 0 := by
  by_contra hall
  push Not at hall
  apply ha
  funext i k
  change a i k = 0
  apply (degreeLTEquiv E (S p h)).symm.injective
  rw [map_zero]
  apply Subtype.ext
  exact hall i k

/-- Root multiplicity is bounded by degree for a nonzero polynomial. -/
theorem rootMultiplicity_le_natDegree_of_ne_zero
    {E : Type*} [Field E] {P : E[X]} (hP : P ≠ 0) (r : E) :
    P.rootMultiplicity r ≤ P.natDegree := by
  rw [rootMultiplicity_eq_natTrailingDegree]
  calc
    (taylor r P).natTrailingDegree ≤ (taylor r P).natDegree :=
      natTrailingDegree_le_natDegree _
    _ = P.natDegree := natDegree_taylor P r

/-- A finite sum of nonzero polynomials with pairwise distinct local orders
at one point cannot vanish. -/
theorem polynomial_sum_ne_zero_of_rootMultiplicity_injOn
    {E : Type*} [Field E] {I : Type*} [DecidableEq I]
    (r : E) (u : Finset I) (F : I → E[X])
    (hu : u.Nonempty) (hF : ∀ z ∈ u, F z ≠ 0)
    (hinj : Set.InjOn (fun z => (F z).rootMultiplicity r) (u : Set I)) :
    ∑ z ∈ u, F z ≠ 0 := by
  obtain ⟨z, hz, hmin⟩ := u.exists_min_image
    (fun w => (F w).rootMultiplicity r) hu
  let n := (F z).rootMultiplicity r
  have hdiv : (X - C r) ^ (n + 1) ∣ ∑ w ∈ u.erase z, F w := by
    apply Finset.dvd_sum
    intro w hw
    have hwu : w ∈ u := Finset.mem_of_mem_erase hw
    have hle : n ≤ (F w).rootMultiplicity r := hmin w hwu
    have hne : (F w).rootMultiplicity r ≠ n := by
      intro heq
      have hwz : w = z := hinj hwu hz (by simpa only [n] using heq)
      exact (Finset.ne_of_mem_erase hw) hwz
    apply (le_rootMultiplicity_iff (hF w hwu)).mp
    omega
  intro hsum
  have hdecomp := Finset.sum_erase_add u F hz
  rw [hsum] at hdecomp
  have hzEq : F z = -(∑ w ∈ u.erase z, F w) :=
    eq_neg_of_add_eq_zero_right hdecomp
  have hdvz : (X - C r) ^ (n + 1) ∣ F z := by
    rw [hzEq]
    exact dvd_neg.mpr hdiv
  exact (pow_rootMultiplicity_not_dvd (hF z hz) r) (by
    simpa only [n] using hdvz)

/-- Injectivity of the mixed-radix pole-order encoding. -/
theorem rationalPoleOrderLabel_injective
    {p h e₁ e₂ i₁ i₂ k₁ k₂ : ℕ} (hp : 1 < p)
    (he₁ : e₁ < S p h) (he₂ : e₂ < S p h)
    (hi₁ : i₁ < p) (hi₂ : i₂ < p)
    (heq : rationalPoleOrderLabel p h e₁ i₁ k₁ =
      rationalPoleOrderLabel p h e₂ i₂ k₂) :
    e₁ = e₂ ∧ i₁ = i₂ ∧ k₁ = k₂ := by
  let base := p ^ (2 * (h + 3) - 1)
  have hbasePos : 0 < base := Nat.pow_pos (by omega)
  have hSbase : S p h < base := by
    unfold S base
    exact Nat.pow_lt_pow_right hp (by omega)
  have he₁base : e₁ < base := he₁.trans hSbase
  have he₂base : e₂ < base := he₂.trans hSbase
  have hcore :
      e₁ + base * ((p - 1 - i₁) + p * k₁) =
        e₂ + base * ((p - 1 - i₂) + p * k₂) := by
    unfold rationalPoleOrderLabel at heq
    change
      p ^ (h + 3) * ((p - 1) * frobeniusOrderSum p (h + 2)) + e₁ +
          base * ((p - 1 - i₁) + p * k₁) =
        p ^ (h + 3) * ((p - 1) * frobeniusOrderSum p (h + 2)) + e₂ +
          base * ((p - 1 - i₂) + p * k₂) at heq
    omega
  have hemod := congrArg (fun n : ℕ => n % base) hcore
  have he : e₁ = e₂ := by
    simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt he₁base,
      Nat.mod_eq_of_lt he₂base] using hemod
  have hmul :
      base * ((p - 1 - i₁) + p * k₁) =
        base * ((p - 1 - i₂) + p * k₂) := by
    omega
  have hdigit : (p - 1 - i₁) + p * k₁ =
      (p - 1 - i₂) + p * k₂ :=
    Nat.mul_left_cancel hbasePos hmul
  have hj₁ : p - 1 - i₁ < p := by omega
  have hj₂ : p - 1 - i₂ < p := by omega
  have himod := congrArg (fun n : ℕ => n % p) hdigit
  have hj : p - 1 - i₁ = p - 1 - i₂ := by
    simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hj₁,
      Nat.mod_eq_of_lt hj₂] using himod
  have hi : i₁ = i₂ := by omega
  have hkMul : p * k₁ = p * k₂ := by omega
  exact ⟨he, hi, Nat.mul_left_cancel (by omega) hkMul⟩

/-- A summand with a nonzero coefficient polynomial is nonzero whenever the
two cleared low trace polynomials are nonzero. -/
theorem rationalAuxiliaryTerm_ne_zero
    {E : Type*} [Field E] {p h i k : ℕ} (hp : 0 < p)
    (pole : E) {e lowN lowD : E[X]}
    (he : e ≠ 0) (hN : lowN ≠ 0) (hD : lowD ≠ 0) :
    rationalAuxiliaryTerm p h pole i k e lowN lowD ≠ 0 := by
  unfold rationalAuxiliaryTerm
  apply mul_ne_zero he
  apply (expand_ne_zero (Nat.pow_pos hp)).mpr
  apply mul_ne_zero
  · exact mul_ne_zero (pow_ne_zero _ hN) (pow_ne_zero _ hD)
  · apply (expand_ne_zero (Nat.pow_pos hp)).mpr
    exact pow_ne_zero _ (X_sub_C_ne_zero pole)

/-- A nonzero coefficient family gives a nonzero rational Stepanov
auxiliary polynomial.  Cancellation is excluded at any chosen supported
pole of the rational phase. -/
theorem rationalAuxiliaryPolynomial_ne_zero
    {p h : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [CharP E p] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) {r : ZMod p}
    (hr : r ∈ InverseRational.poleSupport coeff)
    {a : AuxiliaryCoefficients E p h} (ha : a ≠ 0) :
    let pole := algebraMap (ZMod p) E r
    let lowN := lowRationalNumerator p (h + 3)
      (mappedSimplePoleNumeratorPolynomial (E := E) coeff)
      (mappedSimplePoleDenominatorPolynomial (E := E) coeff)
    let lowD := lowRationalDenominator p (h + 3)
      (mappedSimplePoleDenominatorPolynomial (E := E) coeff)
    rationalAuxiliaryPolynomial p h pole lowN lowD a ≠ 0 := by
  classical
  dsimp only
  let pole := algebraMap (ZMod p) E r
  let A := mappedSimplePoleNumeratorPolynomial (E := E) coeff
  let B := mappedSimplePoleDenominatorPolynomial (E := E) coeff
  let lowN := lowRationalNumerator p (h + 3) A B
  let lowD := lowRationalDenominator p (h + 3) B
  let I := Fin p × Fin (K p h + 1)
  let term : I → E[X] := fun z =>
    rationalAuxiliaryTerm p h pole z.1 z.2
      (auxiliaryCoefficientPolynomial a z.1 z.2) lowN lowD
  let u : Finset I := Finset.univ.filter fun z =>
    auxiliaryCoefficientPolynomial a z.1 z.2 ≠ 0
  have hm : 0 < h + 3 := by omega
  obtain ⟨hD, hDord, hN, hNord⟩ :=
    lowRationalPoleOrders (E := E) coeff hr (h + 3) hm
  change lowD ≠ 0 at hD
  change lowN ≠ 0 at hN
  obtain ⟨i, k, hik⟩ := exists_rationalAuxiliaryCoefficientPolynomial_ne_zero ha
  have hu : u.Nonempty := by
    refine Finset.filter_nonempty_iff.mpr ?_
    exact ⟨(i, k), Finset.mem_univ _, hik⟩
  have htermNe : ∀ z ∈ u, term z ≠ 0 := by
    intro z hz
    have he : auxiliaryCoefficientPolynomial a z.1 z.2 ≠ 0 :=
      (Finset.mem_filter.mp hz).2
    exact rationalAuxiliaryTerm_ne_zero (Fact.out : p.Prime).pos
      pole he hN hD
  have horder : ∀ z ∈ u,
      (term z).rootMultiplicity pole =
        rationalPoleOrderLabel p h
          ((auxiliaryCoefficientPolynomial a z.1 z.2).rootMultiplicity pole)
          z.1 z.2 := by
    intro z hz
    have he : auxiliaryCoefficientPolynomial a z.1 z.2 ≠ 0 :=
      (Finset.mem_filter.mp hz).2
    exact rootMultiplicity_rationalAuxiliaryTerm_eq_label
      (E := E) coeff hr z.1.isLt _ he
  have hinj : Set.InjOn
      (fun z : I => (term z).rootMultiplicity pole) (u : Set I) := by
    intro z hz w hw hzw
    have hez : auxiliaryCoefficientPolynomial a z.1 z.2 ≠ 0 :=
      (Finset.mem_filter.mp hz).2
    have hew : auxiliaryCoefficientPolynomial a w.1 w.2 ≠ 0 :=
      (Finset.mem_filter.mp hw).2
    have hezlt :
        (auxiliaryCoefficientPolynomial a z.1 z.2).rootMultiplicity pole <
          S p h :=
      (rootMultiplicity_le_natDegree_of_ne_zero hez pole).trans_lt
        (natDegree_auxiliaryCoefficientPolynomial_lt
          (Fact.out : p.Prime).pos a z.1 z.2)
    have hewlt :
        (auxiliaryCoefficientPolynomial a w.1 w.2).rootMultiplicity pole <
          S p h :=
      (rootMultiplicity_le_natDegree_of_ne_zero hew pole).trans_lt
        (natDegree_auxiliaryCoefficientPolynomial_lt
          (Fact.out : p.Prime).pos a w.1 w.2)
    change (term z).rootMultiplicity pole = (term w).rootMultiplicity pole at hzw
    rw [horder z hz, horder w hw] at hzw
    obtain ⟨heq, hiq, hkq⟩ := rationalPoleOrderLabel_injective
      (Fact.out : p.Prime).one_lt hezlt hewlt z.1.isLt w.1.isLt hzw
    exact Prod.ext (Fin.ext hiq) (Fin.ext hkq)
  have hnonzero : ∑ z ∈ u, term z ≠ 0 :=
    polynomial_sum_ne_zero_of_rootMultiplicity_injOn
      pole u term hu htermNe hinj
  have hsum : (∑ z ∈ u, term z) =
      rationalAuxiliaryPolynomial p h pole lowN lowD a := by
    rw [rationalAuxiliaryPolynomial]
    change (∑ z ∈ u, term z) =
      ∑ i : Fin p, ∑ k : Fin (K p h + 1), term (i, k)
    rw [← Fintype.sum_prod_type]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro z hzuniv hznot
    have hezero : auxiliaryCoefficientPolynomial a z.1 z.2 = 0 := by
      by_contra he
      exact hznot (Finset.mem_filter.mpr ⟨hzuniv, he⟩)
    simp [term, hezero, rationalAuxiliaryTerm]
  rw [← hsum]
  exact hnonzero

end RationalStepanov

end Erdos387
