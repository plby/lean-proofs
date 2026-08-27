import Arxiv.Arxiv2411_18291.IntegralSpan
import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Rational incidence and inclusion–exclusion inversion

The local decoder proves rational surjectivity on `q+r` vertices without
assuming invertibility of the inclusion matrix. Inclusion–exclusion recovers
each clique coefficient from its degrees; these facts are used to prove the
degree-divisibility criterion in Remark `rem:div`.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {q r : ℕ}

theorem boundary_map {R S : Type*} [AddCommMonoid R] [AddCommMonoid S]
    (f : R →+ S) (Φ : Block V q → R) :
    boundary r (fun Q => f (Φ Q)) = fun e => f (boundary r Φ e) := by
  funext e
  simp only [boundary, map_sum]
  apply sum_congr rfl
  intro Q _
  split_ifs <;> simp

theorem degree_map {R S : Type*} [AddCommMonoid R] [AddCommMonoid S]
    (f : R →+ S) (J : Block V r → R) (I : Finset V) :
    degree (fun e => f (J e)) I = f (degree J I) := by
  simp only [degree, map_sum]
  apply sum_congr rfl
  intro e _
  split_ifs <;> simp

/-- The explicit integer decoder, divided by its nonzero multiplier. -/
def rationalDecoder (q : ℕ) (e : Block V r) (Q : Block V q) : ℚ :=
  (q.descFactorial r : ℚ)⁻¹ * (localDecoder q e Q : ℚ)

theorem boundary_rationalDecoder (hn : Fintype.card V = q + r) (hqr : r ≤ q)
    (e : Block V r) :
    boundary r (rationalDecoder q e) = fun e' => if e' = e then (1 : ℚ) else 0 := by
  have hN : (q.descFactorial r : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hqr).ne'
  unfold rationalDecoder
  rw [boundary_mul]
  have hm := boundary_map (r := r) (Int.castAddHom ℚ) (localDecoder q e)
  simp only [Int.coe_castAddHom] at hm
  rw [hm, boundary_localDecoder hn hqr]
  funext e'
  by_cases h : e' = e <;> simp [h, hN]

/-- The inclusion operator is surjective over the rationals on `q+r` vertices. -/
theorem boundary_surjective_rat (hn : Fintype.card V = q + r) (hqr : r ≤ q) :
    Function.Surjective (boundary (V := V) (q := q) (R := ℚ) r) := by
  intro J
  refine ⟨∑ e : Block V r, fun Q => J e * rationalDecoder q e Q, ?_⟩
  rw [boundary_sum]
  simp_rw [boundary_mul, boundary_rationalDecoder hn hqr]
  funext e'
  simp [sum_apply, mul_ite]

omit [Fintype V] in
private theorem sum_powerset_sign_rat (S : Finset V) :
    (∑ I ∈ S.powerset, (-1 : ℚ) ^ I.card) = if S = ∅ then 1 else 0 := by
  exact_mod_cast (sum_powerset_neg_one_pow_card (x := S))

/-- Recover a clique coefficient by inclusion–exclusion over the complement
of its vertex set. The reconstruction holds for every ambient size. -/
theorem coefficient_from_degrees (Φ : Block V q → ℚ) (Q : Block V q) :
    (∑ I ∈ Q.valᶜ.powerset, (-1 : ℚ) ^ I.card * degree Φ I) = Φ Q := by
  calc
    _ = ∑ P : Block V q, ∑ I ∈ Q.valᶜ.powerset,
        if I ⊆ P.val then (-1 : ℚ) ^ I.card * Φ P else 0 := by
      unfold degree
      simp only [mul_sum, mul_ite, mul_zero]
      rw [sum_comm]
    _ = ∑ P : Block V q, if P = Q then Φ P else 0 := by
      apply sum_congr rfl
      intro P _
      rw [← sum_filter]
      have hf : Q.valᶜ.powerset.filter (fun I => I ⊆ P.val) =
          (Q.valᶜ ∩ P.val).powerset := by
        ext I
        simp [subset_inter_iff]
      rw [hf, ← sum_mul, sum_powerset_sign_rat]
      have hPQ : Q.valᶜ ∩ P.val = ∅ ↔ P = Q := by
        constructor
        · intro h
          apply Subtype.ext
          apply eq_of_subset_of_card_le _ (by rw [P.property, Q.property])
          intro v hvP
          by_contra hvQ
          have hv : v ∈ Q.valᶜ ∩ P.val := by simp [hvP, hvQ]
          rw [h] at hv
          simp at hv
        · rintro rfl
          ext v
          simp
      simp only [hPQ]
      split_ifs <;> simp
    _ = _ := by simp

end Arxiv2411_18291
