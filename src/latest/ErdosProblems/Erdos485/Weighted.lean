import ErdosProblems.Erdos485.Bivariate
import ErdosProblems.Erdos485.ResultantDegree
import ErdosProblems.Erdos485.SquarefreeFactor
import Mathlib.RingTheory.Derivation.MapCoeffs

/-!
# Weighted Euler derivation for Erdős problem 485

For the nested representation `Polynomial (Polynomial K)` (outer variable `y`, inner
variable `z`), this file constructs the derivation

`D = n y ∂/∂y + z ∂/∂z`.

The coefficient formula shows that `D` acts diagonally on `y^a z^b`, with eigenvalue
`n * a + b`.  We record the consequences used in Schinzel's squarefree-gap argument.
-/

namespace Erdos485

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- The inner Euler derivation `z ∂/∂z` on `K[z]`. -/
def innerEulerDerivation : Derivation K (Polynomial K) (Polynomial K) :=
  (X : Polynomial K) • (Polynomial.derivative' : Derivation K (Polynomial K) (Polynomial K))

/-- Apply `z ∂/∂z` coefficientwise to a polynomial in the outer variable `y`. -/
def innerWeightedDerivation : Derivation K (BiPolynomial K) (BiPolynomial K) :=
  PolynomialModule.equivPolynomialSelf.compDer innerEulerDerivation.mapCoeffs

/-- The outer Euler derivation `n y ∂/∂y`, viewed as a `K`-derivation. -/
def outerWeightedDerivation (n : ℕ) : Derivation K (BiPolynomial K) (BiPolynomial K) :=
  (Polynomial.mkDerivation (Polynomial K)
    (C (C (n : K)) * X : BiPolynomial K)).restrictScalars K

/-- The weighted Euler derivation `n y ∂/∂y + z ∂/∂z`. -/
def weightedEulerDerivation (n : ℕ) : Derivation K (BiPolynomial K) (BiPolynomial K) :=
  outerWeightedDerivation n + innerWeightedDerivation

/-- Function notation for the weighted Euler derivation. -/
def weightedEuler (n : ℕ) (F : BiPolynomial K) : BiPolynomial K :=
  weightedEulerDerivation n F

@[simp] theorem innerEulerDerivation_apply (p : Polynomial K) :
    innerEulerDerivation p = X * p.derivative := by
  simp [innerEulerDerivation, Derivation.smul_apply, smul_eq_mul]

@[simp] theorem innerWeightedDerivation_coeff (F : BiPolynomial K) (a : ℕ) :
    (innerWeightedDerivation F).coeff a = X * (F.coeff a).derivative := by
  change (PolynomialModule.equivPolynomialSelf
      (innerEulerDerivation.mapCoeffs F)).coeff a = _
  rw [PolynomialModule.equivPolynomialSelf_apply_eq]
  rfl

@[simp] theorem outerWeightedDerivation_apply (n : ℕ) (F : BiPolynomial K) :
    outerWeightedDerivation n F = F.derivative * (C (C (n : K)) * X) := by
  rfl

theorem weightedEuler_apply (n : ℕ) (F : BiPolynomial K) :
    weightedEuler n F =
      F.derivative * (C (C (n : K)) * X) + innerWeightedDerivation F := by
  rfl

@[simp] theorem weightedEuler_zero (n : ℕ) :
    weightedEuler n (0 : BiPolynomial K) = 0 := by
  exact map_zero (weightedEulerDerivation n)

@[simp] theorem weightedEuler_one (n : ℕ) :
    weightedEuler n (1 : BiPolynomial K) = 0 := by
  exact Derivation.map_one_eq_zero (weightedEulerDerivation n)

@[simp] theorem weightedEuler_add (n : ℕ) (F G : BiPolynomial K) :
    weightedEuler n (F + G) = weightedEuler n F + weightedEuler n G := by
  exact map_add (weightedEulerDerivation n) F G

@[simp] theorem weightedEuler_mul (n : ℕ) (F G : BiPolynomial K) :
    weightedEuler n (F * G) = F * weightedEuler n G + G * weightedEuler n F := by
  simpa [weightedEuler, smul_eq_mul] using
    (Derivation.leibniz (weightedEulerDerivation n) F G)

@[simp] theorem innerWeightedDerivation_C (p : Polynomial K) :
    innerWeightedDerivation (C p) = C (X * p.derivative) := by
  ext (_ | a) b <;> simp

@[simp] theorem innerWeightedDerivation_X :
    innerWeightedDerivation (X : BiPolynomial K) = 0 := by
  ext a b
  rcases a with _ | (_ | a) <;> simp [coeff_X]

@[simp] theorem weightedEuler_C (n : ℕ) (p : Polynomial K) :
    weightedEuler n (C p) = C (X * p.derivative) := by
  rw [weightedEuler_apply]
  simp

@[simp] theorem weightedEuler_X (n : ℕ) :
    weightedEuler n (X : BiPolynomial K) = C (C (n : K)) * X := by
  rw [weightedEuler_apply]
  simp

@[simp] theorem weightedEuler_X_pow (n a : ℕ) :
    weightedEuler n (X ^ a : BiPolynomial K) = C (C ((n * a : ℕ) : K)) * X ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [pow_succ, weightedEuler_mul, ih, weightedEuler_X]
      have hc : C (C (((n * (a + 1) : ℕ) : K))) =
          C (C (n : K)) + C (C (((n * a : ℕ) : K))) := by
        push_cast
        simp only [← C_add]
        congr 2
        ring
      rw [hc]
      ring

@[simp] theorem weightedEuler_biMonomial [CharZero K]
    (n a b : ℕ) (c : K) :
    weightedEuler n (biMonomial a b c) =
      biMonomial a b (((n * a + b : ℕ) : K) * c) := by
  unfold biMonomial
  rw [← C_mul_X_pow_eq_monomial, weightedEuler_mul,
    weightedEuler_C, weightedEuler_X_pow]
  rcases b with _ | b
  · rw [derivative_monomial]
    simp only [Nat.cast_zero, mul_zero, monomial_zero_right, map_zero, zero_mul,
      mul_zero, zero_add]
    rw [← mul_assoc, ← C_mul, C_mul_X_pow_eq_monomial]
    ext i j
    simp [coeff_monomial]
    split_ifs <;> push_cast <;> ring
  · rw [derivative_monomial_succ, X_mul_monomial]
    rw [← mul_assoc, mul_comm (X ^ a) (C (monomial (b + 1) (c * (b + 1)))),
      ← add_mul, ← C_mul, ← C_add, C_mul_X_pow_eq_monomial]
    simp only [← C_eq_natCast, monomial_mul_C]
    ext i j
    by_cases hi : i = a
    · subst i
      simp [coeff_monomial, coeff_mul_C]
      split_ifs <;> push_cast <;> ring
    · have hai : a ≠ i := Ne.symm hi
      simp [coeff_monomial, hi, hai]

theorem coeff_X_mul_derivative [CharZero K] (p : Polynomial K) (b : ℕ) :
    (X * p.derivative).coeff b = (b : K) * p.coeff b := by
  rcases b with _ | b
  · simp
  · rw [coeff_X_mul, coeff_derivative]
    push_cast
    ring

/-- Outer coefficient formula for the weighted Euler derivation. -/
theorem weightedEuler_coeff [CharZero K] (n : ℕ) (F : BiPolynomial K) (a : ℕ) :
    (weightedEuler n F).coeff a =
      C (((n * a : ℕ) : K)) * F.coeff a + X * (F.coeff a).derivative := by
  rcases a with _ | a
  · rw [weightedEuler_apply]
    simp
  · rw [weightedEuler_apply, coeff_add, innerWeightedDerivation_coeff]
    rw [← mul_assoc, coeff_mul_X, coeff_mul_C, coeff_derivative]
    have hc : C ((((n * (a + 1) : ℕ) : K))) =
        C (((a + 1 : ℕ) : K)) * C (n : K) := by
      rw [← C_mul]
      congr 1
      push_cast
      ring
    rw [hc]
    simp only [← C_eq_natCast]
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_one]
    ring

/-- The diagonal coefficient action `D(y^a z^b) = (na+b)y^a z^b`. -/
theorem biCoeff_weightedEuler [CharZero K] (n : ℕ) (F : BiPolynomial K) (a b : ℕ) :
    biCoeff (weightedEuler n F) a b = ((n * a + b : ℕ) : K) * biCoeff F a b := by
  rw [biCoeff, weightedEuler_coeff, coeff_add, coeff_C_mul, coeff_X_mul_derivative]
  unfold biCoeff
  push_cast
  ring

/-- The weighted Euler derivation does not increase degree in the outer variable. -/
theorem weightedEuler_natDegree_le [CharZero K] (n : ℕ) (F : BiPolynomial K) :
    (weightedEuler n F).natDegree ≤ F.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro a ha
  rw [weightedEuler_coeff]
  have hFa : F.coeff a = 0 := coeff_eq_zero_of_natDegree_lt ha
  simp [hFa]

theorem exponentPairs_weightedEuler_subset [CharZero K] (n : ℕ) (F : BiPolynomial K) :
    exponentPairs (weightedEuler n F) ⊆ exponentPairs F := by
  intro ab hab
  rw [mem_exponentPairs_iff] at hab ⊢
  intro hz
  apply hab
  rw [biCoeff_weightedEuler, hz, mul_zero]

theorem weightedEuler_coeff_natDegree_le [CharZero K] (n : ℕ) (F : BiPolynomial K) (a : ℕ) :
    ((weightedEuler n F).coeff a).natDegree ≤ (F.coeff a).natDegree := by
  rw [weightedEuler_coeff]
  apply (natDegree_add_le _ _).trans
  apply max_le
  · exact natDegree_C_mul_le _ _
  · by_cases hd : (F.coeff a).derivative = 0
    · simp [hd]
    · rw [natDegree_X_mul hd]
      have hpos : 0 < (F.coeff a).natDegree := by
        apply Nat.pos_of_ne_zero
        intro hz
        exact hd (derivative_of_natDegree_zero hz)
      exact (Nat.add_le_add_right (natDegree_derivative_le (F.coeff a)) 1).trans
        (Nat.sub_add_cancel hpos).le

theorem maxCoeffDegree_weightedEuler_le [CharZero K] (n : ℕ) (F : BiPolynomial K) :
    maxCoeffDegree (weightedEuler n F) ≤ maxCoeffDegree F := by
  unfold maxCoeffDegree
  apply Finset.sup_le
  intro a ha
  have hcoeff : (weightedEuler n F).coeff a ≠ 0 := mem_support_iff.mp ha
  have hFa : F.coeff a ≠ 0 := by
    intro hz
    apply hcoeff
    rw [weightedEuler_coeff, hz]
    simp
  exact (weightedEuler_coeff_natDegree_le n F a).trans
    (Finset.le_sup (f := fun i ↦ (F.coeff i).natDegree) (mem_support_iff.mpr hFa))

theorem weightedEuler_ZDegreeLT [CharZero K] {m : ℕ} (n : ℕ) {F : BiPolynomial K}
    (hF : ZDegreeLT m F) : ZDegreeLT m (weightedEuler n F) := by
  intro a ha
  have hcoeff : (weightedEuler n F).coeff a ≠ 0 := mem_support_iff.mp ha
  have hFa : F.coeff a ≠ 0 := by
    intro hz
    apply hcoeff
    rw [weightedEuler_coeff, hz]
    simp
  have haF : a ∈ F.support := mem_support_iff.mpr hFa
  rw [weightedEuler_coeff]
  apply (natDegree_add_le _ _).trans_lt
  apply max_lt
  · exact (natDegree_C_mul_le _ _).trans_lt (hF a haF)
  · by_cases hd : (F.coeff a).derivative = 0
    · have hm : 0 < m := (Nat.zero_le _).trans_lt (hF a haF)
      simp [hd, hm]
    · rw [natDegree_X_mul hd]
      have hpos : 0 < (F.coeff a).natDegree := by
        apply Nat.pos_of_ne_zero
        intro hz
        exact hd (derivative_of_natDegree_zero hz)
      calc
        (F.coeff a).derivative.natDegree + 1 ≤
            (F.coeff a).natDegree - 1 + 1 :=
          Nat.add_le_add_right (natDegree_derivative_le (F.coeff a)) 1
        _ = (F.coeff a).natDegree := Nat.sub_add_cancel hpos
        _ < m := hF a haF

/-- Chain rule for the Kronecker specialization `y = x^n`, `z = x`. -/
theorem specialize_weightedEuler [CharZero K] (n : ℕ) (F : BiPolynomial K) :
    specialize n (weightedEuler n F) = X * (specialize n F).derivative := by
  induction F using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simp only [weightedEuler_add, map_add, derivative_add, mul_add, hP, hQ]
  | monomial a p =>
      induction p using Polynomial.induction_on' with
      | add p q hp hq =>
          simp only [map_add, weightedEuler_add, derivative_add, mul_add, hp, hq]
      | monomial b c =>
          change specialize n (weightedEuler n (biMonomial a b c)) =
            X * (specialize n (biMonomial a b c)).derivative
          rw [weightedEuler_biMonomial, specialize_biMonomial, specialize_biMonomial]
          rcases n * a + b with _ | w
          · simp
          · rw [derivative_monomial_succ, X_mul_monomial]
            congr 1
            push_cast
            ring

theorem eq_C_C_of_weightedEuler_eq_zero [CharZero K] {n : ℕ} (hn : 0 < n)
    {G : BiPolynomial K} (hG : weightedEuler n G = 0) :
    G = C (C (biCoeff G 0 0)) := by
  ext a b
  change biCoeff G a b = biCoeff (C (C (biCoeff G 0 0))) a b
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b
      simp [biCoeff]
    · have hc := congrArg (fun P : BiPolynomial K ↦ biCoeff P 0 b) hG
      rw [biCoeff_weightedEuler] at hc
      have hc' : (b : K) * biCoeff G 0 b = 0 := by simpa [biCoeff] using hc
      have hbK : (b : K) ≠ 0 := Nat.cast_ne_zero.mpr hb
      have hz : biCoeff G 0 b = 0 := (mul_eq_zero.mp hc').resolve_left hbK
      rw [hz]
      simp [biCoeff, coeff_C, hb]
  · have hc := congrArg (fun P : BiPolynomial K ↦ biCoeff P a b) hG
    rw [biCoeff_weightedEuler] at hc
    have hc' : ((n * a + b : ℕ) : K) * biCoeff G a b = 0 := by
      simpa [biCoeff] using hc
    have hwNat : n * a + b ≠ 0 :=
      Nat.ne_of_gt (Nat.add_pos_left (Nat.mul_pos hn (Nat.pos_of_ne_zero ha)) b)
    have hw : ((n * a + b : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hwNat
    have hz : biCoeff G a b = 0 := (mul_eq_zero.mp hc').resolve_left hw
    rw [hz]
    simp [biCoeff, coeff_C, ha]

theorem weightedEuler_ne_zero_of_not_constant [CharZero K] {n : ℕ} (hn : 0 < n)
    {G : BiPolynomial K} (hG : ∀ c : K, G ≠ C (C c)) :
    weightedEuler n G ≠ 0 := by
  intro hzero
  exact hG _ (eq_C_C_of_weightedEuler_eq_zero hn hzero)

/-- A nonzero polynomial dividing its weighted Euler derivative is an eigenvector of that
derivation.  The proof uses both partial-degree bounds: first the quotient is constant in `y`,
then its inner degree is zero. -/
theorem exists_scalar_of_dvd_weightedEuler [CharZero K]
    {n : ℕ} {G : BiPolynomial K} (hG : G ≠ 0)
    (hD : weightedEuler n G ≠ 0) (hdiv : G ∣ weightedEuler n G) :
    ∃ lam : K, weightedEuler n G = C (C lam) * G := by
  obtain ⟨Q, hQ⟩ := hdiv
  have hQ0 : Q ≠ 0 := by
    intro hz
    apply hD
    simpa [hz] using hQ
  have hle := weightedEuler_natDegree_le n G
  rw [hQ, natDegree_mul hG hQ0] at hle
  have hQdeg : Q.natDegree = 0 := by omega
  have hQC : Q = C (Q.coeff 0) := eq_C_of_natDegree_eq_zero hQdeg
  have hEq : weightedEuler n G = G * C (Q.coeff 0) :=
    hQ.trans (congrArg (fun R : BiPolynomial K ↦ G * R) hQC)
  have hq0 : Q.coeff 0 ≠ 0 := by
    intro hz
    apply hD
    rw [hEq, hz]
    simp
  have hc := congrArg (fun P : BiPolynomial K ↦ P.coeff G.natDegree) hEq
  rw [coeff_mul_C] at hc
  have hp : G.coeff G.natDegree ≠ 0 := by
    change G.leadingCoeff ≠ 0
    exact leadingCoeff_ne_zero.mpr hG
  have hpqle : (G.coeff G.natDegree * Q.coeff 0).natDegree ≤
      (G.coeff G.natDegree).natDegree := by
    rw [← hc]
    exact weightedEuler_coeff_natDegree_le n G G.natDegree
  rw [natDegree_mul hp hq0] at hpqle
  have hqdeg : (Q.coeff 0).natDegree = 0 := by omega
  obtain ⟨lam, hlam⟩ := natDegree_eq_zero.mp hqdeg
  refine ⟨lam, ?_⟩
  rw [hEq, ← hlam, mul_comm]

/-- Every nonzero monomial of a weighted-Euler eigenvector has the eigenvalue's weight. -/
theorem weight_eq_of_weightedEuler_eq_smul [CharZero K]
    {n : ℕ} {G : BiPolynomial K} {lam : K}
    (h : weightedEuler n G = C (C lam) * G) {a b : ℕ}
    (hab : biCoeff G a b ≠ 0) : ((n * a + b : ℕ) : K) = lam := by
  have hc := congrArg (fun P : BiPolynomial K ↦ biCoeff P a b) h
  rw [biCoeff_weightedEuler] at hc
  simp only [biCoeff, coeff_C_mul] at hc
  exact (mul_right_cancel₀ hab) hc

theorem weights_eq_of_weightedEuler_eq_smul [CharZero K]
    {n : ℕ} {G : BiPolynomial K} {lam : K}
    (h : weightedEuler n G = C (C lam) * G)
    {a b a' b' : ℕ} (hab : biCoeff G a b ≠ 0) (hab' : biCoeff G a' b' ≠ 0) :
    n * a + b = n * a' + b' := by
  apply Nat.cast_injective (R := K)
  exact (weight_eq_of_weightedEuler_eq_smul h hab).trans
    (weight_eq_of_weightedEuler_eq_smul h hab').symm

/-- If an irreducible divides a squarefree polynomial and its Euler derivative, then it also
divides its own Euler derivative. -/
theorem irreducible_dvd_own_weightedEuler_of_squarefree [CharZero K]
    {n : ℕ} {H p : BiPolynomial K} (hH : Squarefree H) (hp : Irreducible p)
    (hpH : p ∣ H) (hpD : p ∣ weightedEuler n H) : p ∣ weightedEuler n p := by
  obtain ⟨U, hHU⟩ := hpH
  have hnot : ¬p ∣ U := Squarefree.irreducible_not_dvd_cofactor hH hp hHU
  rw [hHU, weightedEuler_mul] at hpD
  obtain ⟨W, hW⟩ := hpD
  have hsecond : p ∣ U * weightedEuler n p := by
    refine ⟨W - weightedEuler n U, ?_⟩
    calc
      U * weightedEuler n p =
          (p * weightedEuler n U + U * weightedEuler n p) - p * weightedEuler n U := by ring
      _ = p * W - p * weightedEuler n U := by rw [hW]
      _ = p * (W - weightedEuler n U) := by ring
  exact (hp.prime.dvd_mul.mp hsecond).resolve_left hnot

/-- Common irreducible factors in the squarefree case are weighted-homogeneous. -/
theorem common_irreducible_factor_weightedHomogeneous [CharZero K]
    {n : ℕ} (hn : 0 < n) {H p : BiPolynomial K}
    (hH : Squarefree H) (hp : Irreducible p) (hpH : p ∣ H)
    (hpD : p ∣ weightedEuler n H) (hpconst : ∀ c : K, p ≠ C (C c)) :
    ∃ lam : K, weightedEuler n p = C (C lam) * p := by
  apply exists_scalar_of_dvd_weightedEuler hp.ne_zero
  · exact weightedEuler_ne_zero_of_not_constant hn hpconst
  · exact irreducible_dvd_own_weightedEuler_of_squarefree hH hp hpH hpD

end

end Erdos485
