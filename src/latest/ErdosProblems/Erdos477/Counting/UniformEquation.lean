/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Replacing a curve equation by an integer equation of controlled height.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.PlaneInterpolation
import ErdosProblems.Erdos477.Counting.DegreeHeight

namespace Erdos477.Counting

open Erdos477.Geometry

variable {K : Type*} [Field K] [CharZero K]

noncomputable def planeCoefficientBound (D : ℕ) (B : ℝ) : ℝ :=
  ((D + 1 : ℝ) ^ 2 * B ^ D) ^ ((D + 1) ^ 2)

lemma one_le_planeCoefficientBound (D : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    1 ≤ planeCoefficientBound D B := by
  apply one_le_pow₀
  exact one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (by linarith [show (0 : ℝ) ≤ D from Nat.cast_nonneg D]))
    (one_le_pow₀ hB)

theorem exists_bounded_integer_equation (P : MvPolynomial (Fin 2) K) (hP : P ≠ 0)
    (D : ℕ) (hD : P.totalDegree ≤ D) (B : ℝ) (hB : 1 ≤ B)
    (S : Finset (Fin 2 → ℤ))
    (hS : ∀ z ∈ S, MvPolynomial.eval (fun k => (z k : K)) P = 0)
    (hheight : ∀ z ∈ S, ∀ k, |(z k : ℝ)| ≤ B) :
    ∃ Q : MvPolynomial (Fin 2) ℤ, Q ≠ 0 ∧ Q.totalDegree ≤ D ∧
      (∀ z ∈ S, MvPolynomial.eval z Q = 0) ∧
      ∀ e, |((Q.coeff e : ℤ) : ℝ)| ≤ planeCoefficientBound D B := by
  obtain ⟨Q, hQ, hsupport, hvan, hcoeff⟩ := exists_bounded_polynomial_with_support
    P hP P.support (fun _ h => h) S hS (B ^ D) (one_le_pow₀ hB)
    (fun z hz m hm => abs_eval_plane_monomial_le P D hD m hm z B hB (hheight z hz))
  refine ⟨Q, hQ, (Finset.sup_mono hsupport).trans hD, hvan, ?_⟩
  intro m
  apply (hcoeff m).trans
  have hcard := plane_support_card_le P D hD
  have hcardR : (P.support.card : ℝ) ≤ (D + 1 : ℝ) ^ 2 := by exact_mod_cast hcard
  have hbase : 1 ≤ (D + 1 : ℝ) ^ 2 * B ^ D :=
    one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ (by linarith [show (0 : ℝ) ≤ D from Nat.cast_nonneg D]))
      (one_le_pow₀ hB)
  calc
    _ ≤ ((D + 1 : ℝ) ^ 2 * B ^ D) ^ P.support.card :=
      pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_right hcardR (pow_nonneg (by linarith) _)) _
    _ ≤ _ := pow_le_pow_right₀ hbase hcard

omit [CharZero K] in
lemma associated_of_dvd_of_totalDegree_le (P Q : MvPolynomial (Fin 2) K)
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hdiv : P ∣ Q) (hdegree : Q.totalDegree ≤ P.totalDegree) :
    Associated P Q := by
  obtain ⟨G, hG⟩ := hdiv
  have hG0 : G ≠ 0 := by intro h; rw [h, mul_zero] at hG; exact hQ hG
  have hdegG : G.totalDegree = 0 := by
    rw [hG, MvPolynomial.totalDegree_mul_of_isDomain hP hG0] at hdegree
    omega
  have hconstant := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdegG
  have hcoeff : G.coeff 0 ≠ 0 := by
    intro h
    rw [h, map_zero] at hconstant
    exact hG0 hconstant
  have hunit : IsUnit G := by
    rw [hconstant]
    exact (isUnit_iff_ne_zero.mpr hcoeff).map MvPolynomial.C
  rw [hG]
  exact associated_mul_unit_right _ _ hunit

lemma card_integer_points_common_zeroes_le (P : MvPolynomial (Fin 2) K)
    (Q : MvPolynomial (Fin 2) ℤ) (hP : Irreducible P)
    (hdiv : ¬ P ∣ MvPolynomial.map (Int.castRingHom K) Q)
    (S : Finset (Fin 2 → ℤ))
    (hS : ∀ z ∈ S, MvPolynomial.eval (fun k => (z k : K)) P = 0 ∧
      MvPolynomial.eval z Q = 0) : S.card ≤ P.totalDegree * Q.totalDegree := by
  classical
  let π : (Fin 2 → ℤ) → K × K := fun z => (z 0, z 1)
  have hinj : Function.Injective π := by
    intro z w h
    have h0 : z 0 = w 0 := Int.cast_injective (congrArg Prod.fst h)
    have h1 : z 1 = w 1 := Int.cast_injective (congrArg Prod.snd h)
    ext k
    fin_cases k
    · exact h0
    · exact h1
  have h := card_common_zeroes_le P (MvPolynomial.map (Int.castRingHom K) Q)
    hP hdiv (S.image π) (by
      intro w hw
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
      have hvec : ![(π z).1, (π z).2] = fun k => (z k : K) := by ext k; fin_cases k <;> rfl
      rw [hvec, eval_integer_polynomial_map, (hS z hz).2, Int.cast_zero]
      exact ⟨(hS z hz).1, rfl⟩)
  rw [Finset.card_image_of_injective _ hinj,
    totalDegree_map_of_injective _ Int.cast_injective] at h
  exact h

/-- More than `d^2` integer points force the bounded interpolating equation
to be associated to the original irreducible degree-`d` equation. -/
theorem exists_bounded_associated_equation (P : MvPolynomial (Fin 2) K)
    (hP : Irreducible P) (B : ℝ) (hB : 1 ≤ B)
    (S : Finset (Fin 2 → ℤ)) (hcard : P.totalDegree ^ 2 < S.card)
    (hS : ∀ z ∈ S, MvPolynomial.eval (fun k => (z k : K)) P = 0)
    (hheight : ∀ z ∈ S, ∀ k, |(z k : ℝ)| ≤ B) :
    ∃ Q : MvPolynomial (Fin 2) ℤ, Q ≠ 0 ∧ Q.totalDegree ≤ P.totalDegree ∧
      Associated P (MvPolynomial.map (Int.castRingHom K) Q) ∧
      (∀ z ∈ S, MvPolynomial.eval z Q = 0) ∧
      ∀ e, |((Q.coeff e : ℤ) : ℝ)| ≤ planeCoefficientBound P.totalDegree B := by
  obtain ⟨Q, hQ, hdegree, hvan, hcoeff⟩ := exists_bounded_integer_equation P hP.ne_zero
    P.totalDegree le_rfl B hB S hS hheight
  have hdiv : P ∣ MvPolynomial.map (Int.castRingHom K) Q := by
    by_contra h
    have hbound := card_integer_points_common_zeroes_le P Q hP h S
      (fun z hz => ⟨hS z hz, hvan z hz⟩)
    have hbound' := hbound.trans (Nat.mul_le_mul_left P.totalDegree hdegree)
    nlinarith
  refine ⟨Q, hQ, hdegree, ?_, hvan, hcoeff⟩
  refine associated_of_dvd_of_totalDegree_le P _ hP.ne_zero ?_ hdiv ?_
  · intro h
    apply hQ
    exact (MvPolynomial.map_injective _ Int.cast_injective) (h.trans (map_zero _).symm)
  · rwa [totalDegree_map_of_injective _ Int.cast_injective]

#print axioms exists_bounded_associated_equation
-- 'Erdos477.Counting.exists_bounded_associated_equation' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
