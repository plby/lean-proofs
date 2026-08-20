import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monomial
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Hajós' lemma for sparse polynomials

The key operation in the usual proof is the Euler reduction
`X * P.derivative - C n * P`.  In characteristic zero its support is exactly the
support of `P` with the exponent `n` removed.  At a nonzero root it lowers the
root multiplicity by at most one.  Strong induction on the support then gives
Hajós' bound.
-/

open scoped Polynomial

noncomputable section

namespace Erdos485

open Polynomial

section Hajos

variable {K : Type*} [Field K] [CharZero K]

/-- The Euler reduction which deletes the term of exponent `n`. -/
def eulerReduce (p : K[X]) (n : ℕ) : K[X] :=
  X * p.derivative - C (n : K) * p

@[simp]
theorem coeff_eulerReduce (p : K[X]) (n k : ℕ) :
    (eulerReduce p n).coeff k = ((k : K) - (n : K)) * p.coeff k := by
  cases k with
  | zero => simp [eulerReduce]
  | succ k =>
      simp only [eulerReduce, coeff_sub, coeff_X_mul, coeff_derivative, coeff_C_mul,
        Nat.cast_succ]
      ring

/-- In characteristic zero, Euler reduction removes exactly the selected term. -/
theorem support_eulerReduce (p : K[X]) (n : ℕ) :
    (eulerReduce p n).support = p.support.erase n := by
  ext k
  simp only [mem_support_iff, coeff_eulerReduce, mul_ne_zero_iff, Finset.mem_erase]
  constructor
  · rintro ⟨hkn, hk⟩
    exact ⟨fun h ↦ hkn (by simp [h]), hk⟩
  · rintro ⟨hkn, hk⟩
    exact ⟨sub_ne_zero.mpr (Nat.cast_injective.ne hkn), hk⟩

theorem card_support_eulerReduce {p : K[X]} {n : ℕ} (hn : n ∈ p.support) :
    (eulerReduce p n).support.card + 1 = p.support.card := by
  have hpos : 0 < p.support.card := Finset.card_pos.mpr ⟨n, hn⟩
  rw [support_eulerReduce, Finset.card_erase_of_mem hn]
  omega

/-- A nonzero monomial cannot vanish at a nonzero point. -/
theorem two_le_card_support_of_isRoot {p : K[X]} {a : K}
    (hp : p ≠ 0) (ha : a ≠ 0) (hroot : p.IsRoot a) :
    2 ≤ p.support.card := by
  by_contra h
  have hcard : p.support.card ≤ 1 := by omega
  obtain ⟨n, c, rfl⟩ := Polynomial.card_support_le_one_iff_monomial.mp hcard
  have hc : c ≠ 0 := by
    intro hc
    apply hp
    simp [hc]
  have heval : (monomial n c).eval a ≠ 0 := by
    simp [Polynomial.eval_monomial, hc, ha]
  exact heval hroot

/-- **Hajós' lemma.**  The multiplicity of a nonzero root of a nonzero
characteristic-zero polynomial is strictly smaller than its number of terms. -/
theorem hajos_rootMultiplicity_lt_support_card {p : K[X]} {a : K}
    (hp : p ≠ 0) (ha : a ≠ 0) :
    p.rootMultiplicity a < p.support.card := by
  induction hcard : p.support.card using Nat.strong_induction_on generalizing p with
  | h N ih =>
      by_cases hroot : p.IsRoot a
      · have htwo : 2 ≤ p.support.card :=
          two_le_card_support_of_isRoot hp ha hroot
        obtain ⟨n, hn⟩ := p.support.nonempty_of_ne_empty (by
          intro hs
          simp [hs] at htwo)
        let q : K[X] := eulerReduce p n
        have hqcard : q.support.card + 1 = p.support.card := by
          simpa [q] using card_support_eulerReduce hn
        have hqcard_pos : 0 < q.support.card := by omega
        have hq : q ≠ 0 := by
          intro hqzero
          have : q.support.card = 0 := Polynomial.card_support_eq_zero.mpr hqzero
          omega
        have hqlt : q.support.card < N := by omega
        have hiq : q.rootMultiplicity a < q.support.card :=
          ih q.support.card hqlt hq rfl
        have hderiv :
            p.derivative.rootMultiplicity a = p.rootMultiplicity a - 1 :=
          Polynomial.derivative_rootMultiplicity_of_root hroot
        have hmult : p.rootMultiplicity a - 1 ≤ q.rootMultiplicity a := by
          rw [Polynomial.le_rootMultiplicity_iff hq]
          have hdderiv :
              (X - C a) ^ (p.rootMultiplicity a - 1) ∣ p.derivative := by
            rw [← hderiv]
            exact p.derivative.pow_rootMultiplicity_dvd a
          have hdp : (X - C a) ^ (p.rootMultiplicity a - 1) ∣ p :=
            (pow_dvd_pow (X - C a) (Nat.sub_le _ _)).trans
              (p.pow_rootMultiplicity_dvd a)
          apply dvd_sub
          · exact dvd_mul_of_dvd_right hdderiv X
          · exact dvd_mul_of_dvd_right hdp (C (n : K))
        have hrpos : 0 < p.rootMultiplicity a :=
          (Polynomial.rootMultiplicity_pos hp).mpr hroot
        omega
      · rw [Polynomial.rootMultiplicity_eq_zero hroot]
        have hnecard : p.support.card ≠ 0 := fun h ↦
          hp (Polynomial.card_support_eq_zero.mp h)
        omega

/-- A convenient inequality form of Hajós' lemma. -/
theorem hajos_support_bound {p : K[X]} {a : K} (hp : p ≠ 0) (ha : a ≠ 0)
    {m : ℕ} (hm : m ≤ p.rootMultiplicity a) :
    m + 1 ≤ p.support.card := by
  have h := hajos_rootMultiplicity_lt_support_card hp ha
  omega

/-- Reflection, and hence reversal, preserves the number of nonzero terms. -/
theorem card_support_reflect (p : K[X]) (N : ℕ) :
    (p.reflect N).support.card = p.support.card := by
  rw [Polynomial.reflect_support,
    Finset.card_image_of_injective _ (Polynomial.revAt N).injective]

theorem card_support_reverse (p : K[X]) :
    p.reverse.support.card = p.support.card := by
  exact card_support_reflect p p.natDegree

section AlgebraicallyClosed

variable [IsAlgClosed K]

/-- A polynomial with nonzero constant coefficient and positive degree has a
nonzero root; applying Hajós to its square gives the first nontrivial square
support bound. -/
theorem three_le_sq_support_card_of_coeff_zero_ne_algClosed {p : K[X]}
    (hp0 : p.coeff 0 ≠ 0) (hdeg : 0 < p.natDegree) :
    3 ≤ (p ^ 2).support.card := by
  have hp : p ≠ 0 := by
    intro hp
    simp [hp] at hp0
  have hpdeg : p.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hp]
    exact_mod_cast hdeg.ne'
  obtain ⟨a, haRoot⟩ := IsAlgClosed.exists_root p hpdeg
  have ha : a ≠ 0 := by
    intro ha
    subst a
    apply hp0
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact haRoot
  have hpSq : p ^ 2 ≠ 0 := pow_ne_zero _ hp
  have hm : 2 ≤ (p ^ 2).rootMultiplicity a := by
    rw [pow_two, Polynomial.rootMultiplicity_mul (mul_ne_zero hp hp)]
    have hpos : 0 < p.rootMultiplicity a :=
      (Polynomial.rootMultiplicity_pos hp).mpr haRoot
    omega
  exact hajos_support_bound hpSq ha hm

end AlgebraicallyClosed

/-- The algebraically-closed hypothesis in the preceding lemma can be removed
by mapping to an algebraic closure.  Injectivity of the coefficient map
preserves support exactly. -/
theorem three_le_sq_support_card_of_coeff_zero_ne {p : K[X]}
    (hp0 : p.coeff 0 ≠ 0) (hdeg : 0 < p.natDegree) :
    3 ≤ (p ^ 2).support.card := by
  let ι : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have hι : Function.Injective ι := RingHom.injective ι
  let q : (AlgebraicClosure K)[X] := p.map ι
  have hq0 : q.coeff 0 ≠ 0 := by
    intro hzero
    apply hp0
    apply hι
    simpa [q, ι] using hzero
  have hqdeg : 0 < q.natDegree := by
    change 0 < (p.map ι).natDegree
    rw [Polynomial.natDegree_map_eq_of_injective hι]
    exact hdeg
  have hqbound : 3 ≤ (q ^ 2).support.card :=
    three_le_sq_support_card_of_coeff_zero_ne_algClosed hq0 hqdeg
  have hpow : q ^ 2 = (p ^ 2).map ι := by
    simp [q, Polynomial.map_pow]
  rw [hpow, Polynomial.support_map_of_injective (p ^ 2) hι] at hqbound
  exact hqbound

/-- If a characteristic-zero polynomial has at least two terms, then its
square has at least three terms.  Reversal removes its largest monomial factor:
`p.reverse` has nonzero constant coefficient, the same number of terms as `p`,
and reversal commutes with squaring. -/
theorem three_le_sq_support_card {p : K[X]} (hpterms : 2 ≤ p.support.card) :
    3 ≤ (p ^ 2).support.card := by
  have hp : p ≠ 0 := by
    intro hpzero
    simp [hpzero] at hpterms
  let q : K[X] := p.reverse
  have hqterms : 2 ≤ q.support.card := by
    simpa [q, card_support_reverse] using hpterms
  have hq0 : q.coeff 0 ≠ 0 := by
    simpa [q] using (Polynomial.leadingCoeff_ne_zero.mpr hp)
  have hqdeg : 0 < q.natDegree := by
    by_contra hdeg
    have hdeg0 : q.natDegree = 0 := Nat.eq_zero_of_not_pos hdeg
    have hqeq : q = C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
    have hcard : q.support.card ≤ 1 := by
      rw [hqeq]
      simpa using
        (Polynomial.card_support_C_mul_X_pow_le_one (R := K)
          (c := q.coeff 0) (n := 0))
    omega
  have hqbound : 3 ≤ (q ^ 2).support.card :=
    three_le_sq_support_card_of_coeff_zero_ne hq0 hqdeg
  have hreverse : (p ^ 2).reverse = q ^ 2 := by
    simp [q, pow_two, Polynomial.reverse_mul_of_domain]
  calc
    3 ≤ (q ^ 2).support.card := hqbound
    _ = (p ^ 2).reverse.support.card := congrArg (fun r : K[X] ↦ r.support.card) hreverse.symm
    _ = (p ^ 2).support.card := card_support_reverse (p ^ 2)

end Hajos

end Erdos485
