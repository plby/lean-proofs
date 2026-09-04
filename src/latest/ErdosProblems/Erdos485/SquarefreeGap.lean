import ErdosProblems.Erdos485.SquarefreeFactor
import ErdosProblems.Erdos485.Weighted
import ErdosProblems.Erdos485.WeightedCoprime
import ErdosProblems.Erdos485.EvenMultiplicity
import ErdosProblems.Erdos485.ResultantSpecialize
import ErdosProblems.Erdos485.Bivariate
import ErdosProblems.Erdos485.Laurent
import ErdosProblems.Erdos485.Deformation

/-!
# The squarefree-gap lemma for Erdős problem 485

This file assembles the weighted Euler and resultant ingredients of Schinzel's
squarefree-gap argument.  A squarefree bivariate polynomial `H` whose Kronecker
specialization divides the square of its weighted Euler derivative is a unit,
provided `H` is coprime to that derivative and its `z`-degree is less than one
quarter of the Kronecker base.

The positive outer-degree case is the resultant contradiction.  When the
outer degree is zero, `H` is an inner univariate polynomial and the conclusion
is the elementary squarefree Euler-derivative lemma.  Keeping the latter case
separate is essential: a resultant of two outer constants contains no useful
degree information.
-/

namespace Erdos485

open Polynomial
open scoped Polynomial.Bivariate

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- Over a field, association in the iterated polynomial ring differs by a
nonzero scalar from the ground field.  This turns the UFD factorization API,
which naturally returns `Associated`, into the exact identity used by the
specialized-square calculation. -/
theorem exists_eq_C_C_mul_of_associated {F G : BiPolynomial K}
    (h : Associated F G) :
    ∃ c : K, c ≠ 0 ∧ F = C (C c) * G := by
  rcases h.symm with ⟨u, hu⟩
  obtain ⟨r, hr, hru⟩ := Polynomial.isUnit_iff.mp u.isUnit
  obtain ⟨c, hc, hcr⟩ := Polynomial.isUnit_iff.mp hr
  refine ⟨c, isUnit_iff_ne_zero.mp hc, ?_⟩
  rw [← hu, ← hru, ← hcr]
  ring

/-- Once the squarefree cofactor is a unit, the original factorization is
associated to a square. -/
theorem associated_sq_of_associated_sq_mul_of_isUnit
    {R : Type*} [CommMonoid R] {F A H : R}
    (h : Associated F (A ^ 2 * H)) (hH : IsUnit H) :
    Associated F (A ^ 2) := by
  rcases hH with ⟨u, rfl⟩
  exact h.trans (Associated.symm ⟨u, rfl⟩)

/-! ## Inner-degree bookkeeping for factors -/

/-- Swapping the two polynomial variables transposes bivariate coefficients. -/
theorem biCoeff_swap (F : BiPolynomial K) (a b : ℕ) :
    biCoeff (Polynomial.Bivariate.swap F) a b = biCoeff F b a := by
  induction F using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [map_add]
      change biCoeff (Polynomial.Bivariate.swap P) a b +
        biCoeff (Polynomial.Bivariate.swap Q) a b =
        biCoeff P b a + biCoeff Q b a
      rw [hP, hQ]
  | monomial i p =>
      induction p using Polynomial.induction_on' with
      | add P Q hP hQ =>
          have hm : monomial i (P + Q) = monomial i P + monomial i Q := by
            ext k
            simp [coeff_monomial]
          rw [hm, map_add]
          change biCoeff (Polynomial.Bivariate.swap (monomial i P)) a b +
            biCoeff (Polynomial.Bivariate.swap (monomial i Q)) a b =
            biCoeff (monomial i P) b a + biCoeff (monomial i Q) b a
          rw [hP, hQ]
      | monomial j c =>
          rw [Polynomial.Bivariate.swap_monomial_monomial]
          by_cases hbi : b = i
          · subst b
            by_cases haj : a = j
            · subst a
              simp [biCoeff]
            · simp [biCoeff, coeff_monomial, Ne.symm haj]
          · by_cases haj : a = j
            · subst a
              simp [biCoeff, coeff_monomial, Ne.symm hbi]
            · simp [biCoeff, coeff_monomial, Ne.symm hbi, Ne.symm haj]

/-- `maxCoeffDegree` is the ordinary outer degree after swapping the two
variables. -/
theorem maxCoeffDegree_eq_natDegree_swap (F : BiPolynomial K) :
    maxCoeffDegree F = (Polynomial.Bivariate.swap F).natDegree := by
  apply le_antisymm
  · unfold maxCoeffDegree
    apply Finset.sup_le
    intro a ha
    have hFa : F.coeff a ≠ 0 := mem_support_iff.mp ha
    have hlead : (F.coeff a).coeff (F.coeff a).natDegree ≠ 0 := by
      rw [coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hFa
    apply le_natDegree_of_ne_zero
    intro hz
    apply hlead
    have hs := congrArg (fun p : Polynomial K ↦ p.coeff a) hz
    rw [coeff_zero] at hs
    change biCoeff F a (F.coeff a).natDegree = 0
    rw [← biCoeff_swap F (F.coeff a).natDegree a]
    exact hs
  · by_cases hs : Polynomial.Bivariate.swap F = 0
    · rw [hs, natDegree_zero]
      exact Nat.zero_le _
    · have hlc : (Polynomial.Bivariate.swap F).coeff
          (Polynomial.Bivariate.swap F).natDegree ≠ 0 := by
        change (Polynomial.Bivariate.swap F).leadingCoeff ≠ 0
        exact leadingCoeff_ne_zero.mpr hs
      obtain ⟨a, ha⟩ := nonempty_support_iff.mpr hlc
      have ha0 : ((Polynomial.Bivariate.swap F).coeff
          (Polynomial.Bivariate.swap F).natDegree).coeff a ≠ 0 := mem_support_iff.mp ha
      have hFa : biCoeff F a (Polynomial.Bivariate.swap F).natDegree ≠ 0 := by
        rw [← biCoeff_swap F (Polynomial.Bivariate.swap F).natDegree a]
        exact ha0
      have haF : a ∈ F.support := mem_support_iff.mpr
        (fun hz ↦ hFa (by simp [biCoeff, hz]))
      exact (le_natDegree_of_ne_zero hFa).trans
        (Finset.le_sup (f := fun i ↦ (F.coeff i).natDegree) haF)

/-- A bivariate factor cannot have larger inner degree than a nonzero
multiple. -/
theorem maxCoeffDegree_le_of_dvd {H F : BiPolynomial K}
    (hHF : H ∣ F) (hF : F ≠ 0) : maxCoeffDegree H ≤ maxCoeffDegree F := by
  rw [maxCoeffDegree_eq_natDegree_swap, maxCoeffDegree_eq_natDegree_swap]
  obtain ⟨Q, hQ⟩ := hHF
  have hdvd : Polynomial.Bivariate.swap H ∣ Polynomial.Bivariate.swap F := by
    refine ⟨Polynomial.Bivariate.swap Q, ?_⟩
    rw [← map_mul, hQ]
  have hsF : Polynomial.Bivariate.swap F ≠ 0 :=
    by simpa using Polynomial.Bivariate.swap.injective.ne hF
  exact Polynomial.natDegree_le_of_dvd hdvd hsF

/-- A pointwise strict inner-exponent bound controls `maxCoeffDegree`. -/
theorem four_mul_maxCoeffDegree_lt_of_exponentPairs
    (F : BiPolynomial K) (n : ℕ) (hF : F ≠ 0)
    (hpair : ∀ ab ∈ exponentPairs F, 4 * ab.2 < n) :
    4 * maxCoeffDegree F < n := by
  have hsF : Polynomial.Bivariate.swap F ≠ 0 :=
    by simpa using Polynomial.Bivariate.swap.injective.ne hF
  have hlc : (Polynomial.Bivariate.swap F).coeff
      (Polynomial.Bivariate.swap F).natDegree ≠ 0 := by
    change (Polynomial.Bivariate.swap F).leadingCoeff ≠ 0
    exact leadingCoeff_ne_zero.mpr hsF
  obtain ⟨a, ha⟩ := nonempty_support_iff.mpr hlc
  have ha0 : ((Polynomial.Bivariate.swap F).coeff
      (Polynomial.Bivariate.swap F).natDegree).coeff a ≠ 0 := mem_support_iff.mp ha
  have hpairmem : (a, (Polynomial.Bivariate.swap F).natDegree) ∈ exponentPairs F := by
    rw [mem_exponentPairs_iff]
    rw [← biCoeff_swap F (Polynomial.Bivariate.swap F).natDegree a]
    exact ha0
  rw [maxCoeffDegree_eq_natDegree_swap]
  exact hpair _ hpairmem

/-- A maximum inner-degree bound strictly below `n` supplies `ZDegreeLT`. -/
theorem zDegreeLT_of_maxCoeffDegree_lt
    (H : BiPolynomial K) (n dZ : ℕ)
    (hHz : maxCoeffDegree H ≤ dZ) (hdZn : dZ < n) : ZDegreeLT n H := by
  intro a _ha
  exact (coeff_natDegree_le_maxCoeffDegree H a).trans hHz |>.trans_lt hdZn

/-- A nonzero coefficient with outer exponent zero excludes the outer variable
as a factor. -/
theorem outer_X_not_dvd_of_biCoeff_zero_ne {F : BiPolynomial K} {b : ℕ}
    (h : biCoeff F 0 b ≠ 0) : ¬(X : BiPolynomial K) ∣ F := by
  rintro ⟨Q, rfl⟩
  apply h
  simp [biCoeff]

/-- A nonzero coefficient with inner exponent zero excludes the inner variable
as a factor. -/
theorem inner_X_not_dvd_of_biCoeff_zero_ne {F : BiPolynomial K} {a : ℕ}
    (h : biCoeff F a 0 ≠ 0) : ¬(C X : BiPolynomial K) ∣ F := by
  rintro ⟨Q, rfl⟩
  apply h
  simp [biCoeff]

/-- Squarefreeness of an outer constant polynomial descends to its coefficient. -/
theorem squarefree_coeff_zero_of_squarefree_of_natDegree_eq_zero
    {H : BiPolynomial K} (hsq : Squarefree H) (hHy : H.natDegree = 0) :
    Squarefree (H.coeff 0) := by
  intro p hp
  apply Polynomial.isUnit_C.mp
  apply hsq (C p)
  obtain ⟨q, hq⟩ := hp
  refine ⟨C q, ?_⟩
  rw [eq_C_of_natDegree_eq_zero hHy, hq, map_mul, map_mul]

/-- If the inner variable does not divide an outer constant `H`, it does not
divide the unique inner coefficient of `H`. -/
theorem X_not_dvd_coeff_zero_of_C_X_not_dvd_of_natDegree_eq_zero
    {H : BiPolynomial K} (hX : ¬(C X : BiPolynomial K) ∣ H)
    (hHy : H.natDegree = 0) : ¬(X : Polynomial K) ∣ H.coeff 0 := by
  intro hp
  apply hX
  obtain ⟨q, hq⟩ := hp
  refine ⟨C q, ?_⟩
  rw [eq_C_of_natDegree_eq_zero hHy, hq, map_mul]

/-- The specialized-square identity and an exact square-times-squarefree
factorization force the specialization of `H` to divide the square of the
specialized weighted Euler derivative.

This is the multiplicity bridge in the squarefree-gap proof.  The monomial
factor `X^v` is put on the left of the cleared identity; the arbitrary-field
version of the even-multiplicity lemma then handles all irreducible factors,
including those without roots in the ground field. -/
theorem specialize_dvd_weightedEuler_sq_of_factorization
    (F A H : BiPolynomial K) (U : Polynomial K) (n v : ℕ) {c : K}
    (hc : c ≠ 0)
    (hfac : F = C (C c) * A ^ 2 * H)
    (hspec : specialize n F = U ^ 2 * X ^ v)
    (hU : U ≠ 0) :
    specialize n H ∣ (specialize n (weightedEuler n H)) ^ 2 := by
  have hfacSpec :
      specialize n F = C c * (specialize n A) ^ 2 * specialize n H := by
    rw [hfac]
    simp
  have hFspec : specialize n F ≠ 0 := by
    rw [hspec]
    exact mul_ne_zero (pow_ne_zero 2 hU) (pow_ne_zero v X_ne_zero)
  have hAspec : specialize n A ≠ 0 := by
    intro hzero
    apply hFspec
    rw [hfacSpec, hzero]
    simp
  have hHspec : specialize n H ≠ 0 := by
    intro hzero
    apply hFspec
    rw [hfacSpec, hzero]
    simp
  have hsq :
      X ^ v * U ^ 2 =
        C c * X ^ 0 * (specialize n A) ^ 2 * specialize n H := by
    calc
      X ^ v * U ^ 2 = specialize n F := by rw [hspec]; ring
      _ = C c * (specialize n A) ^ 2 * specialize n H := hfacSpec
      _ = C c * X ^ 0 * (specialize n A) ^ 2 * specialize n H := by ring
  have hdiv :=
    dvd_sq_X_mul_derivative_of_X_pow_mul_sq_eq_C_mul_X_pow_mul_sq_mul_charZero
      U (specialize n A) (specialize n H) v 0
      hU hAspec hHspec hc hsq
  rw [specialize_weightedEuler]
  exact hdiv

/-- The structural squarefree-gap theorem.

The hypotheses `hcop`, `hDy`, and `hDz` are supplied by the weighted Euler
lemmas.  The hypothesis `hdiv` is supplied by the cleared specialized-square
identity and the even-root-multiplicity lemma. -/
theorem squarefree_gap_isUnit_of_coprime_of_specialize_dvd
    (H : BiPolynomial K) (n dZ : ℕ)
    (hH : H ≠ 0)
    (hsq : Squarefree H)
    (hX : ¬(C X : BiPolynomial K) ∣ H)
    (hHz : maxCoeffDegree H ≤ dZ)
    (hDy : (weightedEuler n H).natDegree ≤ H.natDegree)
    (hDz : maxCoeffDegree (weightedEuler n H) ≤ dZ)
    (hcop : IsCoprime
      (H.map (algebraMap (Polynomial K) (FractionRing (Polynomial K))))
      ((weightedEuler n H).map
        (algebraMap (Polynomial K) (FractionRing (Polynomial K)))))
    (hdiv : specialize n H ∣ (specialize n (weightedEuler n H)) ^ 2)
    (hdeg : ZDegreeLT n H)
    (hgap : 4 * dZ < n) : IsUnit H := by
  by_cases hY : H.natDegree = 0
  · have hsq0 : Squarefree (H.coeff 0) :=
      squarefree_coeff_zero_of_squarefree_of_natDegree_eq_zero hsq hY
    have hX0 : ¬(X : Polynomial K) ∣ H.coeff 0 :=
      X_not_dvd_coeff_zero_of_C_X_not_dvd_of_natDegree_eq_zero hX hY
    have hdiv0 :
        H.coeff 0 ∣ (X * (H.coeff 0).derivative) ^ 2 := by
      have hc : H = C (H.coeff 0) := eq_C_of_natDegree_eq_zero hY
      rw [hc] at hdiv
      simpa only [weightedEuler_C, specialize_apply, eval₂_C, RingHom.id_apply] using hdiv
    have hu0 : IsUnit (H.coeff 0) :=
      squarefree_dvd_eulerSquare_isUnit (H.coeff 0) hsq0 hX0 hdiv0
    rw [eq_C_of_natDegree_eq_zero hY]
    exact Polynomial.isUnit_C.mpr hu0
  · have hYpos : 0 < H.natDegree := Nat.pos_of_ne_zero hY
    have hle : n ≤ 4 * dZ :=
      resultant_specialize_le_four_mul H (weightedEuler n H) n dZ
        hH hYpos hDy hHz hDz hcop hdiv hdeg
    omega

/-- Fully assembled squarefree-gap theorem once fraction-field coprimality is
available.  It consumes the `Associated` factorization returned by
`exists_sq_mul_squarefree_factor`, extracts its nonzero scalar, obtains Euler
divisibility from the specialized square, and supplies both Euler degree
bounds automatically. -/
theorem squarefree_gap_isUnit_of_associated_factorization
    (F A H : BiPolynomial K) (U : Polynomial K) (n v dZ : ℕ)
    (hassoc : Associated F (A ^ 2 * H))
    (hsq : Squarefree H)
    (hX : ¬(C X : BiPolynomial K) ∣ H)
    (hHz : maxCoeffDegree H ≤ dZ)
    (hcop : IsCoprime
      (H.map (algebraMap (Polynomial K) (FractionRing (Polynomial K))))
      ((weightedEuler n H).map
        (algebraMap (Polynomial K) (FractionRing (Polynomial K)))))
    (hdeg : ZDegreeLT n H)
    (hgap : 4 * dZ < n)
    (hspec : specialize n F = U ^ 2 * X ^ v)
    (hU : U ≠ 0) : IsUnit H := by
  have hH : H ≠ 0 := hsq.ne_zero
  obtain ⟨c, hc, hfac'⟩ := exists_eq_C_C_mul_of_associated hassoc
  have hfac : F = C (C c) * A ^ 2 * H := by
    rw [hfac']
    ring
  have hdiv :
      specialize n H ∣ (specialize n (weightedEuler n H)) ^ 2 :=
    specialize_dvd_weightedEuler_sq_of_factorization
      F A H U n v hc hfac hspec hU
  exact squarefree_gap_isUnit_of_coprime_of_specialize_dvd H n dZ
    hH hsq hX hHz (weightedEuler_natDegree_le n H)
    ((maxCoeffDegree_weightedEuler_le n H).trans hHz) hcop hdiv hdeg hgap

/-! ## The complete bridge from a Dirichlet deformation -/

/-- Fraction-field Euler coprimality for every squarefree factor of `F` that
misses the two coordinate axes.  This is separated as a named predicate so
the weighted-support lemma can be used without exposing its long type at each
call site. -/
def FactorsFractionCoprimeWeighted (n : ℕ) (F : BiPolynomial K) : Prop :=
  ∀ H : BiPolynomial K,
    Squarefree H → H ∣ F →
    ¬(X : BiPolynomial K) ∣ H → ¬(C X : BiPolynomial K) ∣ H →
    IsCoprime
      (H.map (algebraMap (Polynomial K) (FractionRing (Polynomial K))))
      ((weightedEuler n H).map
        (algebraMap (Polynomial K) (FractionRing (Polynomial K))))

/-- A nontrivial Dirichlet deformation is a nonzero scalar times a bivariate
square, assuming the localized weighted-Euler coprimality statement.

All other hypotheses of the squarefree-gap argument are derived here from
the fields of `Deformation`: nonvanishing, avoidance of both coordinate
axes, the strict one-quarter inner-degree gap, inheritance of that degree
bound by a factor, the specialized square identity, and nonvanishing of its
one-variable square root. -/
theorem Deformation.exists_eq_scalar_mul_sq_of_factorsFractionCoprimeWeighted
    {P : K[X]} (N : PrimitiveNormalization P) (D : Deformation N)
    (hcop : FactorsFractionCoprimeWeighted (N.poly ^ 2).natDegree D.F) :
    ∃ A : BiPolynomial K, ∃ c : K, c ≠ 0 ∧ D.F = C (C c) * A ^ 2 := by
  let : StrongNormalizationMonoid (Polynomial K) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let : StrongNormalizationMonoid (BiPolynomial K) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  have hF : D.F ≠ 0 := by
    intro hzero
    apply D.coeff_y_zero_ne
    simp [hzero, biCoeff]
  have hYF : ¬(X : BiPolynomial K) ∣ D.F :=
    outer_X_not_dvd_of_biCoeff_zero_ne D.coeff_y_zero_ne
  obtain ⟨a0, ha0⟩ := D.coeff_z_zero_ne
  have hZF : ¬(C X : BiPolynomial K) ∣ D.F :=
    inner_X_not_dvd_of_biCoeff_zero_ne ha0
  have hpair : ∀ ab ∈ exponentPairs D.F,
      4 * ab.2 < (N.poly ^ 2).natDegree := by
    intro ab hab
    rw [D.exponentPairs_eq] at hab
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hab
    exact D.four_mul_zExponent_lt j
  have hgap : 4 * maxCoeffDegree D.F < (N.poly ^ 2).natDegree :=
    four_mul_maxCoeffDegree_lt_of_exponentPairs D.F _ hF hpair
  obtain ⟨A, H, hassoc, hsq, hHF, _hmult⟩ :=
    exists_sq_mul_squarefree_factor D.F hF
  have hYH : ¬(X : BiPolynomial K) ∣ H :=
    not_dvd_of_dvd_of_not_dvd hHF hYF
  have hZH : ¬(C X : BiPolynomial K) ∣ H :=
    not_dvd_of_dvd_of_not_dvd hHF hZF
  have hHmax : maxCoeffDegree H ≤ maxCoeffDegree D.F :=
    maxCoeffDegree_le_of_dvd hHF hF
  have hdZn : maxCoeffDegree D.F < (N.poly ^ 2).natDegree := by omega
  have hHdeg : ZDegreeLT (N.poly ^ 2).natDegree H :=
    zDegreeLT_of_maxCoeffDegree_lt H _ _ hHmax hdZn
  have hn : 0 < (N.poly ^ 2).natDegree := by
    rw [Polynomial.natDegree_pow]
    exact Nat.mul_pos (by omega) N.natDegree_pos
  have hspecF : specialize (N.poly ^ 2).natDegree D.F ≠ 0 :=
    specialize_ne_zero hn D.zDegreeLT hF
  have hU : N.poly.comp (X ^ D.q) ≠ 0 := by
    intro hzero
    apply hspecF
    rw [D.specialize_eq, hzero]
    simp
  have hcopH : IsCoprime
      (H.map (algebraMap (Polynomial K) (FractionRing (Polynomial K))))
      ((weightedEuler (N.poly ^ 2).natDegree H).map
        (algebraMap (Polynomial K) (FractionRing (Polynomial K)))) :=
    hcop H hsq hHF hYH hZH
  have hHunit : IsUnit H :=
    squarefree_gap_isUnit_of_associated_factorization
      D.F A H (N.poly.comp (X ^ D.q)) (N.poly ^ 2).natDegree
      (Int.toNat (-D.shift)) (maxCoeffDegree D.F)
      hassoc hsq hZH hHmax hcopH hHdeg hgap D.specialize_eq hU
  obtain ⟨c, hc, heq⟩ :=
    eq_scalar_mul_sq_of_associated_sq_mul_isUnit D.F A H hassoc hHunit
  exact ⟨A, c, hc, heq⟩

/-- Every nontrivial Dirichlet deformation is a nonzero scalar times a
bivariate square.  The pairwise-distinct-weight hypothesis needed by the
squarefree-gap argument follows from the strict inner-degree bound carried by
`Deformation`. -/
theorem Deformation.exists_eq_scalar_mul_sq
    {P : K[X]} (N : PrimitiveNormalization P) (D : Deformation N) :
    ∃ A : BiPolynomial K, ∃ c : K, c ≠ 0 ∧ D.F = C (C c) * A ^ 2 := by
  apply D.exists_eq_scalar_mul_sq_of_factorsFractionCoprimeWeighted N
  intro H hsq hHF hY hZ
  have hn : 0 < (N.poly ^ 2).natDegree := by
    rw [Polynomial.natDegree_pow]
    exact Nat.mul_pos (by omega) N.natDegree_pos
  have hF : D.F ≠ 0 := by
    intro hzero
    apply D.coeff_y_zero_ne
    simp [hzero, biCoeff]
  exact weightedEuler_isCoprime_fractionRing_of_squarefree_dvd_weightInjective
    hn hF hsq hHF hY hZ (exponentWeight_injOn hn D.zDegreeLT)

end

end Erdos485
