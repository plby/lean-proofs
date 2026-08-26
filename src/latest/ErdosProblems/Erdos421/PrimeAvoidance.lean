import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.ModEq
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

/-! # Choosing a prime with distinct tuple residues

The off-diagonal difference product gives a finite, explicit certificate
for excluding bad primes. Its use here loses a harmless factor of two
in the number of primes compared with a Vandermonde product.
-/

namespace Erdos421

def tupleDifferenceProduct {n : ℕ} (x : Fin n → ℕ) : ℕ :=
  ∏ ij ∈ (Finset.univ : Finset (Fin n)).offDiag, Nat.dist (x ij.1) (x ij.2)

theorem tupleDifferenceProduct_pos {n : ℕ} (x : Fin n → ℕ) (hx : Function.Injective x) :
    0 < tupleDifferenceProduct x := by
  apply Finset.prod_pos
  intro ij hij
  exact Nat.dist_pos_of_ne (fun he ↦ (Finset.mem_offDiag.mp hij).2.2 (hx he))

theorem tupleDifferenceProduct_le {n N : ℕ} (x : Fin n → ℕ) (hx : ∀ i, x i ≤ N) :
    tupleDifferenceProduct x ≤ N ^ (n * (n - 1)) := by
  calc
    tupleDifferenceProduct x ≤ ∏ _ij ∈ (Finset.univ : Finset (Fin n)).offDiag, N := by
      apply Finset.prod_le_prod
      · intro _ _
        exact Nat.zero_le _
      · intro ij _
        have h1 := hx ij.1
        have h2 := hx ij.2
        unfold Nat.dist
        omega
    _ = N ^ (n * (n - 1)) := by
      rw [Finset.prod_const, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin,
        Nat.mul_sub_left_distrib, mul_one]

theorem dvd_nat_dist_of_zmod_eq {p a b : ℕ} (h : (a : ZMod p) = (b : ZMod p)) :
    p ∣ Nat.dist a b := by
  have hm := (ZMod.natCast_eq_natCast_iff a b p).mp h
  exact dvd_add hm.symm.dvd' hm.dvd'

theorem injective_zmod_of_not_dvd_difference {n p : ℕ} (x : Fin n → ℕ)
    (hp : ¬p ∣ tupleDifferenceProduct x) :
    Function.Injective (fun i ↦ (x i : ZMod p)) := by
  intro i j he
  by_contra hij
  apply hp
  apply (dvd_nat_dist_of_zmod_eq he).trans
  unfold tupleDifferenceProduct
  exact Finset.dvd_prod_of_mem (fun ij : Fin n × Fin n ↦ Nat.dist (x ij.1) (x ij.2))
    (show (i, j) ∈ (Finset.univ : Finset (Fin n)).offDiag from
      Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hij⟩)

theorem exists_prime_not_dvd_of_product_gt (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {D : ℕ} (hD : 0 < D) (hprod : D < ∏ p ∈ S, p) :
    ∃ p ∈ S, ¬p ∣ D := by
  classical
  by_contra h
  push Not at h
  have hdiv : (∏ p ∈ S, p) ∣ D := by
    apply Finset.prod_dvd_of_isRelPrime
    · intro p hp q hq hpq
      apply Nat.coprime_iff_isRelPrime.mp
      apply (hS p hp).coprime_iff_not_dvd.mpr
      exact fun he ↦ hpq ((hS q hq).dvd_iff_eq (hS p hp).ne_one |>.mp he).symm
    · exact h
  exact (not_le_of_gt hprod) (Nat.le_of_dvd hD hdiv)

theorem exists_prime_distinct_tuple_residues {n N : ℕ} (x y : Fin n → ℕ)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hxN : ∀ i, x i ≤ N) (hyN : ∀ i, y i ≤ N)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hprod : N ^ (2 * (n * (n - 1))) < ∏ p ∈ S, p) :
    ∃ p ∈ S, Function.Injective (fun i ↦ (x i : ZMod p)) ∧
      Function.Injective (fun i ↦ (y i : ZMod p)) := by
  have hb : tupleDifferenceProduct x * tupleDifferenceProduct y < ∏ p ∈ S, p := by
    apply lt_of_le_of_lt (Nat.mul_le_mul (tupleDifferenceProduct_le x hxN)
      (tupleDifferenceProduct_le y hyN))
    simpa only [← pow_add, ← two_mul] using hprod
  obtain ⟨p, hp, hpd⟩ := exists_prime_not_dvd_of_product_gt S hS
    (Nat.mul_pos (tupleDifferenceProduct_pos x hx) (tupleDifferenceProduct_pos y hy)) hb
  refine ⟨p, hp, injective_zmod_of_not_dvd_difference x ?_,
    injective_zmod_of_not_dvd_difference y ?_⟩
  · exact fun h ↦ hpd (dvd_mul_of_dvd_left h _)
  · exact fun h ↦ hpd (dvd_mul_of_dvd_right h _)

end Erdos421
