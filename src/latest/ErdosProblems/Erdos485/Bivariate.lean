import Mathlib

/-!
# Bivariate polynomial infrastructure for Erdős problem 485

The orientation in this file is fixed as follows.  A polynomial in `K[y,z]` is represented by
`Polynomial (Polynomial K)`: the **outer** polynomial variable is `y`, while the variable of an
outer coefficient is `z`.  Thus `biMonomial a b c` means `c * y^a * z^b`, and specialization at
`y = x^n`, `z = x` sends its exponent pair `(a,b)` to the exponent `n * a + b`.
-/

open scoped Polynomial.Bivariate

namespace Erdos485

open Polynomial

noncomputable section

/-- Polynomials in `K[y,z]`, with `y` the outer and `z` the inner variable. -/
abbrev BiPolynomial (K : Type*) [Semiring K] := Polynomial (Polynomial K)

/-- The coefficient of `y^a z^b`. -/
def biCoeff {K : Type*} [Semiring K] (H : BiPolynomial K) (a b : ℕ) : K :=
  (H.coeff a).coeff b

/-- The monomial `c * y^a * z^b` in the outer-`y`, inner-`z` convention. -/
def biMonomial {K : Type*} [Semiring K] (a b : ℕ) (c : K) : BiPolynomial K :=
  monomial a (monomial b c)

@[simp] theorem biCoeff_biMonomial {K : Type*} [Semiring K]
    (a b i j : ℕ) (c : K) :
    biCoeff (biMonomial a b c) i j = if i = a ∧ j = b then c else 0 := by
  by_cases hia : i = a
  · subst i
    by_cases hjb : j = b
    · subst j; simp [biCoeff, biMonomial]
    · simp [biCoeff, biMonomial, coeff_monomial, hjb, Ne.symm hjb]
  · simp [biCoeff, biMonomial, coeff_monomial, hia, Ne.symm hia]

/-- The finite set of exponent pairs carrying nonzero coefficients. -/
def exponentPairs {K : Type*} [Semiring K] (H : BiPolynomial K) : Finset (ℕ × ℕ) :=
  H.support.biUnion fun a => (H.coeff a).support.image fun b => (a, b)

/-- The Kronecker weight corresponding to `y = x^n`, `z = x`. -/
def exponentWeight (n : ℕ) (ab : ℕ × ℕ) : ℕ := n * ab.1 + ab.2

/-- Specialization `K[y,z] → K[x]`, `y ↦ x^n`, `z ↦ x`. -/
def specialize {K : Type*} [CommSemiring K] (n : ℕ) : BiPolynomial K →+* Polynomial K :=
  eval₂RingHom (RingHom.id (Polynomial K)) (X ^ n)

@[simp] theorem specialize_apply {K : Type*} [CommSemiring K] (n : ℕ)
    (H : BiPolynomial K) : specialize n H = H.eval₂ (RingHom.id _) (X ^ n) := rfl

@[simp] theorem specialize_biMonomial {K : Type*} [CommSemiring K]
    (n a b : ℕ) (c : K) :
    specialize n (biMonomial a b c) = monomial (n * a + b) c := by
  rw [specialize_apply]
  unfold biMonomial
  rw [eval₂_monomial, RingHom.id_apply]
  rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial]
  rw [← pow_mul, mul_assoc, ← pow_add, add_comm]

@[simp] theorem mem_exponentPairs_iff {K : Type*} [Semiring K]
    (H : BiPolynomial K) (a b : ℕ) :
    (a, b) ∈ exponentPairs H ↔ biCoeff H a b ≠ 0 := by
  classical
  simp only [exponentPairs, Finset.mem_biUnion, Finset.mem_image, Prod.mk.injEq,
    exists_eq_right_right, mem_support_iff, biCoeff]
  constructor
  · rintro ⟨ha, hb⟩
    exact hb
  · intro hab
    refine ⟨?_, hab⟩
    intro ha
    apply hab
    exact (congrArg (fun p : Polynomial K => p.coeff b) ha).trans (coeff_zero b)

/-- Every inner (`z`) coefficient polynomial of `H` has degree strictly below `n`.
Only nonzero outer coefficients need to be checked. -/
def ZDegreeLT {K : Type*} [Semiring K] (n : ℕ) (H : BiPolynomial K) : Prop :=
  ∀ a ∈ H.support, (H.coeff a).natDegree < n

theorem snd_lt_of_mem_exponentPairs {K : Type*} [Semiring K]
    {n : ℕ} {H : BiPolynomial K} (hdeg : ZDegreeLT n H)
    {ab : ℕ × ℕ} (hab : ab ∈ exponentPairs H) : ab.2 < n := by
  have hcoeff : biCoeff H ab.1 ab.2 ≠ 0 := by
    simpa only [Prod.eta] using (mem_exponentPairs_iff H ab.1 ab.2).mp hab
  have ha : ab.1 ∈ H.support := mem_support_iff.mpr fun h =>
    hcoeff (by simp [biCoeff, h])
  exact (le_natDegree_of_ne_zero hcoeff).trans_lt (hdeg ab.1 ha)

/-- Under the digit bound `b < n`, Kronecker weights have no collisions. -/
theorem exponentWeight_injOn {K : Type*} [Semiring K]
    {n : ℕ} {H : BiPolynomial K} (hn : 0 < n) (hdeg : ZDegreeLT n H) :
    Set.InjOn (exponentWeight n) (exponentPairs H : Set (ℕ × ℕ)) := by
  intro ab hab cd hcd hw
  have hablt := snd_lt_of_mem_exponentPairs hdeg hab
  have hcdlt := snd_lt_of_mem_exponentPairs hdeg hcd
  have hsnd : ab.2 = cd.2 := by
    have hm := congrArg (fun e : ℕ => e % n) hw
    simpa [exponentWeight, Nat.mul_add_mod, Nat.mod_eq_of_lt hablt,
      Nat.mod_eq_of_lt hcdlt] using hm
  have hfst_mul : n * ab.1 = n * cd.1 := by
    have hadd : n * ab.1 + ab.2 = n * cd.1 + ab.2 := by
      simpa [exponentWeight, hsnd] using hw
    exact Nat.add_right_cancel hadd
  have hfst : ab.1 = cd.1 := Nat.eq_of_mul_eq_mul_left hn hfst_mul
  exact Prod.ext hfst hsnd

/-- The coefficient at the encoded exponent `n*a+b` is exactly the original bivariate
coefficient, provided all `z`-degrees are `< n` and `b < n`. -/
theorem coeff_specialize_exponentWeight {K : Type*} [CommSemiring K]
    {n : ℕ} {H : BiPolynomial K} (hn : 0 < n) (hdeg : ZDegreeLT n H)
    (a b : ℕ) (hb : b < n) :
    (specialize n H).coeff (n * a + b) = biCoeff H a b := by
  rw [specialize_apply, eval₂_eq_sum, coeff_sum]
  simp only [RingHom.id_apply, ← pow_mul]
  rw [sum_def]
  have hterm : ∀ i ∈ H.support, i ≠ a →
      (H.coeff i * X ^ (n * i)).coeff (n * a + b) = 0 := by
    intro i hi hia
    rw [coeff_mul_X_pow']
    by_cases hlt : i < a
    · rw [if_pos]
      · apply coeff_eq_zero_of_natDegree_lt
        apply (hdeg i hi).trans_le
        apply Nat.le_sub_of_add_le
        have hmul : n * (i + 1) ≤ n * a :=
          Nat.mul_le_mul_left n (Nat.succ_le_iff.mpr hlt)
        simpa [Nat.mul_succ, Nat.add_comm] using
          hmul.trans (Nat.le_add_right (n * a) b)
      · exact Nat.mul_le_mul_left n (Nat.le_of_lt hlt) |>.trans (Nat.le_add_right _ _)
    · have hai : a < i := lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm hia)
      rw [if_neg]
      have hstep : n * a + b < n * (a + 1) := by
        rw [Nat.mul_succ]
        exact Nat.add_lt_add_left hb _
      have hmul : n * (a + 1) ≤ n * i :=
        Nat.mul_le_mul_left n (Nat.succ_le_iff.mpr hai)
      exact not_le.mpr (hstep.trans_le hmul)
  rw [Finset.sum_eq_single a]
  · rw [coeff_mul_X_pow', if_pos (Nat.le_add_right _ _)]
    simp [biCoeff]
  · exact fun i hi hia => hterm i hi hia
  · intro ha
    have hc : H.coeff a = 0 := by
      simpa only [mem_support_iff, not_not] using ha
    simp [hc]

/-- With all `z`-degrees below `n`, specialization carries the bivariate support exactly to its
image under `(a,b) ↦ n*a+b`. -/
theorem support_specialize_eq_image {K : Type*} [CommSemiring K]
    {n : ℕ} {H : BiPolynomial K} (hn : 0 < n) (hdeg : ZDegreeLT n H) :
    (specialize n H).support = (exponentPairs H).image (exponentWeight n) := by
  classical
  ext e
  constructor
  · intro he
    let a := e / n
    let b := e % n
    have hb : b < n := Nat.mod_lt e hn
    have heq : n * a + b = e := by
      exact Nat.div_add_mod e n
    have hc : biCoeff H a b ≠ 0 := by
      have hs := coeff_specialize_exponentWeight hn hdeg a b hb
      rw [heq] at hs
      exact fun hz => (mem_support_iff.mp he) (hs.trans hz)
    refine Finset.mem_image.mpr ⟨(a, b), (mem_exponentPairs_iff H a b).mpr hc, ?_⟩
    simpa [exponentWeight] using heq
  · intro he
    obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp he
    have hb := snd_lt_of_mem_exponentPairs hdeg hab
    apply mem_support_iff.mpr
    simp only [exponentWeight]
    rw [coeff_specialize_exponentWeight hn hdeg ab.1 ab.2 hb]
    exact (mem_exponentPairs_iff H ab.1 ab.2).mp (by simpa only [Prod.eta] using hab)

/-- No support is lost under a collision-free Kronecker specialization. -/
theorem card_support_specialize {K : Type*} [CommSemiring K]
    {n : ℕ} {H : BiPolynomial K} (hn : 0 < n) (hdeg : ZDegreeLT n H) :
    (specialize n H).support.card = (exponentPairs H).card := by
  classical
  rw [support_specialize_eq_image hn hdeg]
  exact Finset.card_image_of_injOn (exponentWeight_injOn hn hdeg)

/-- A collision-free specialization of a nonzero bivariate polynomial is nonzero. -/
theorem specialize_ne_zero {K : Type*} [CommSemiring K]
    {n : ℕ} {H : BiPolynomial K} (hn : 0 < n) (hdeg : ZDegreeLT n H)
    (hH : H ≠ 0) : specialize n H ≠ 0 := by
  obtain ⟨a, ha⟩ := (nonempty_support_iff.mpr hH)
  have hcoeffa : H.coeff a ≠ 0 := mem_support_iff.mp ha
  obtain ⟨b, hb⟩ := nonempty_support_iff.mpr hcoeffa
  have hblt : b < n :=
    (le_natDegree_of_mem_supp b hb).trans_lt (hdeg a ha)
  have hc : (specialize n H).coeff (n * a + b) ≠ 0 := by
    rw [coeff_specialize_exponentWeight hn hdeg a b hblt]
    exact mem_support_iff.mp hb
  exact fun hzero => hc (by rw [hzero, coeff_zero])

/-- The outer `y`-degree is magnified by at least `n` under `y = x^n`, `z = x`.
The nonnegative `z`-exponent of a leading-`y` monomial can only raise the resulting degree. -/
theorem mul_natDegree_le_natDegree_specialize {K : Type*} [CommSemiring K]
    {n : ℕ} {H : BiPolynomial K} (hn : 0 < n) (hdeg : ZDegreeLT n H)
    (hH : H ≠ 0) :
    n * H.natDegree ≤ (specialize n H).natDegree := by
  have ha : H.natDegree ∈ H.support := by
    apply mem_support_iff.mpr
    rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hH
  have hcoeffa : H.coeff H.natDegree ≠ 0 := mem_support_iff.mp ha
  obtain ⟨b, hb⟩ := nonempty_support_iff.mpr hcoeffa
  have hblt : b < n :=
    (le_natDegree_of_mem_supp b hb).trans_lt (hdeg H.natDegree ha)
  have hc : (specialize n H).coeff (n * H.natDegree + b) ≠ 0 := by
    rw [coeff_specialize_exponentWeight hn hdeg H.natDegree b hblt]
    exact mem_support_iff.mp hb
  exact (Nat.le_add_right _ _).trans (le_natDegree_of_ne_zero hc)

end

end Erdos485
