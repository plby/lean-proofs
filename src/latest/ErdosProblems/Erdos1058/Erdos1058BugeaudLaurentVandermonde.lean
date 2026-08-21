import ErdosProblems.Erdos1058.Erdos1058BugeaudLaurentDeterminant

open scoped BigOperators
open Polynomial

noncomputable section

namespace Erdos1058.BugeaudLaurent

theorem signVariations_lt_card_support {P : ℚ[X]} (hP : P ≠ 0) :
    P.signVariations < P.support.card := by
  induction hcard : P.support.card using Nat.strong_induction_on generalizing P with
  | h n ih =>
      by_cases hE : P.eraseLead = 0
      · have hc : P.support.card = 1 :=
          Polynomial.card_support_eq_one_of_eraseLead_eq_zero hP hE
        rw [← hcard, hc]
        have hpform : P = Polynomial.monomial P.natDegree P.leadingCoeff := by
          simpa [hE] using
            (Polynomial.eraseLead_add_monomial_natDegree_leadingCoeff P).symm
        rw [hpform, Polynomial.signVariations_monomial]
        omega
      · have hlt : P.eraseLead.support.card < n := by
          rw [← hcard]
          exact Polynomial.eraseLead_support_card_lt hP
        have hi := ih P.eraseLead.support.card hlt hE rfl
        have hle := Polynomial.signVariations_le_eraseLead_succ P
        rw [← hcard, ← Polynomial.card_support_eraseLead_add_one hP]
        omega

def sparsePolynomial {n : ℕ} (exponent : Fin n → ℕ) (w : Fin n → ℚ) : ℚ[X] :=
  ∑ j : Fin n, Polynomial.monomial (exponent j) (w j)

lemma sparsePolynomial_coeff_of_injective {n : ℕ}
    (exponent : Fin n → ℕ) (hexponent : Function.Injective exponent)
    (w : Fin n → ℚ) (j : Fin n) :
    (sparsePolynomial exponent w).coeff (exponent j) = w j := by
  classical
  unfold sparsePolynomial
  rw [show (∑ x : Fin n, Polynomial.monomial (exponent x) (w x)) =
      ∑ x ∈ (Finset.univ : Finset (Fin n)),
        Polynomial.monomial (exponent x) (w x) by rfl]
  rw [Polynomial.finsetSum_coeff]
  calc
    ∑ x : Fin n, (Polynomial.monomial (exponent x) (w x)).coeff (exponent j) =
        ∑ x : Fin n, if x = j then w x else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Polynomial.coeff_monomial]
          by_cases hx : x = j
          · subst x
            simp
          · have hne : exponent x ≠ exponent j := fun h => hx (hexponent h)
            simp [hne, hx]
    _ = w j := by simp

lemma sparsePolynomial_ne_zero {n : ℕ}
    (exponent : Fin n → ℕ) (hexponent : Function.Injective exponent)
    (w : Fin n → ℚ) (hw : w ≠ 0) :
    sparsePolynomial exponent w ≠ 0 := by
  intro hzero
  apply hw
  funext j
  have hj := congrArg (fun P : ℚ[X] => P.coeff (exponent j)) hzero
  simpa [sparsePolynomial_coeff_of_injective exponent hexponent w j] using hj

lemma sparsePolynomial_support_card_le {n : ℕ}
    (exponent : Fin n → ℕ) (w : Fin n → ℚ) :
    (sparsePolynomial exponent w).support.card ≤ n := by
  classical
  calc
    (sparsePolynomial exponent w).support.card ≤
        (Finset.univ.image exponent).card := by
          apply Finset.card_le_card
          intro k hk
          rw [Polynomial.mem_support_iff] at hk
          by_contra hnot
          have hall : ∀ j : Fin n, exponent j ≠ k := by
            intro j hEq
            exact hnot (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hEq⟩)
          unfold sparsePolynomial at hk
          rw [show (∑ j : Fin n, Polynomial.monomial (exponent j) (w j)) =
              ∑ j ∈ (Finset.univ : Finset (Fin n)),
                Polynomial.monomial (exponent j) (w j) by rfl,
            Polynomial.finsetSum_coeff] at hk
          simp [Polynomial.coeff_monomial, hall] at hk
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = n := Fintype.card_fin n

lemma sparsePolynomial_eval {n : ℕ}
    (exponent : Fin n → ℕ) (w : Fin n → ℚ) (x : ℚ) :
    (sparsePolynomial exponent w).eval x =
      ∑ j : Fin n, x ^ exponent j * w j := by
  change (Polynomial.evalRingHom x)
      (∑ j : Fin n, Polynomial.monomial (exponent j) (w j)) = _
  rw [map_sum]
  simp [Polynomial.eval_monomial, mul_comm]

theorem generalizedVandermonde_det_ne_zero {n : ℕ}
    (scale : Fin n → ℚ) (hscalePos : ∀ i, 0 < scale i)
    (hscaleInj : Function.Injective scale)
    (exponent : Fin n → ℕ) (hexponent : Function.Injective exponent) :
    (Matrix.of fun (i j : Fin n) => scale i ^ exponent j).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨w, hw, hmul⟩ :=
    (Matrix.exists_mulVec_eq_zero_iff (M :=
      Matrix.of fun (i j : Fin n) => scale i ^ exponent j)).mpr hdet
  let P : ℚ[X] := sparsePolynomial exponent w
  have hP : P ≠ 0 := sparsePolynomial_ne_zero exponent hexponent w hw
  have heval : ∀ i : Fin n, P.eval (scale i) = 0 := by
    intro i
    have hi := congr_fun hmul i
    simpa [P, sparsePolynomial_eval, Matrix.mulVec, dotProduct] using hi
  have himage : Finset.univ.image scale ⊆
      P.roots.toFinset.filter (fun x : ℚ => 0 < x) := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    simp [Polynomial.mem_roots hP, heval i, hscalePos i]
  have hrootlower : n ≤ P.roots.countP (fun x : ℚ => 0 < x) := by
    rw [Multiset.countP_eq_card_filter]
    calc
      n = (Finset.univ.image scale).card := by
        rw [Finset.card_image_of_injective _ hscaleInj]
        simp
      _ ≤ (P.roots.toFinset.filter (fun x : ℚ => 0 < x)).card :=
        Finset.card_le_card himage
      _ ≤ (P.roots.filter (fun x : ℚ => 0 < x)).card := by
        simpa [Multiset.toFinset_filter] using
          (Multiset.toFinset_card_le (P.roots.filter (fun x : ℚ => 0 < x)))
  have hdescartes := Polynomial.roots_countP_pos_le_signVariations P
  have hvariations := signVariations_lt_card_support hP
  have hsupport := sparsePolynomial_support_card_le exponent w
  change P.support.card ≤ n at hsupport
  omega

end Erdos1058.BugeaudLaurent
