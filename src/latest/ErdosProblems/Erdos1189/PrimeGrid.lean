/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Congruence classes as boxes in the finite product of prime-adic digits.
Informal source: Simpson's theorem and its finite-grid formulation in
Balister--Bollobás--Morris--Sahasrabudhe--Tiba.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.Digits
import ErdosProblems.Erdos1189.Grid
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Algebra.GCDMonoid.FinsetLemmas

namespace Erdos1189

open Finset
open scoped Function

abbrev PrimeCoordinate (N : ℕ) := (p : N.primeFactors) × Fin (N.factorization p)

def coordinateSize {N : ℕ} (i : PrimeCoordinate N) : ℕ := i.1

lemma coordinateSize_pos {N : ℕ} (i : PrimeCoordinate N) : 0 < coordinateSize i :=
  (Nat.prime_of_mem_primeFactors i.1.2).pos

def digitPoint (N n : ℕ) : Grid.Point (@coordinateSize N) :=
  fun i => ⟨digit i.1 n i.2, Nat.mod_lt _ (coordinateSize_pos i)⟩

def congruenceBox (N d a : ℕ) : Grid.Box (@coordinateSize N) :=
  fun i => if (i.2 : ℕ) < d.factorization i.1 then some (digitPoint N a i) else none

lemma mem_fixed_congruenceBox {N d a : ℕ} {i : PrimeCoordinate N} :
    i ∈ Grid.fixed (congruenceBox N d a) ↔ (i.2 : ℕ) < d.factorization i.1 := by
  simp [Grid.mem_fixed, congruenceBox]

lemma digitPoint_surjective (N : ℕ) : Function.Surjective (digitPoint N) := by
  intro x
  let f (p : N.primeFactors) : ℕ := finFunctionFinEquiv (fun e => x ⟨p, e⟩)
  let s (p : N.primeFactors) : ℕ := (p : ℕ) ^ N.factorization p
  have hs : ∀ p ∈ (univ : Finset N.primeFactors), s p ≠ 0 := by
    intro p _
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors p.2).ne_zero
  have hcop : Set.Pairwise (univ : Finset N.primeFactors) (Nat.Coprime on s) := by
    intro p _ q _ hpq
    exact Nat.pairwise_coprime_pow_primeFactors_factorization hpq
  let n := Nat.chineseRemainderOfFinset f s univ hs hcop
  refine ⟨n.val, ?_⟩
  funext i
  apply Fin.ext
  change digit i.1 n.val i.2 = (x i : ℕ)
  rw [digit_eq_of_modEq (n.prop i.1 (mem_univ _)) i.2.isLt]
  exact digit_finFunctionFinEquiv (p := i.1.val) (fun e => x ⟨i.1, e⟩) i.2

lemma modEq_primeFactors_iff {d n a : ℕ} (hd : d ≠ 0) :
    n ≡ a [MOD d] ↔ ∀ p ∈ d.primeFactors, n ≡ a [MOD p ^ d.factorization p] := by
  have hcop : d.primeFactors.toList.Pairwise
      (Nat.Coprime on fun p => p ^ d.factorization p) := by
    apply List.Nodup.pairwise_of_forall_ne d.primeFactors.nodup_toList
    intro p hp q hq hpq
    exact ((Nat.coprime_primes
      (Nat.prime_of_mem_primeFactors (mem_toList.mp hp))
      (Nat.prime_of_mem_primeFactors (mem_toList.mp hq))).mpr hpq).pow _ _
  have h := Nat.modEq_list_map_prod_iff (a := n) (b := a) hcop
  simpa only [mem_toList, prod_map_toList,
    ← Nat.prod_primeFactors_pow_factorization hd] using h

lemma contains_congruenceBox_iff {N d a n : ℕ} (hN : N ≠ 0) (hd : d ∣ N) :
    Grid.Contains (congruenceBox N d a) (digitPoint N n) ↔ n ≡ a [MOD d] := by
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hN hd
  constructor
  · intro h
    apply (modEq_primeFactors_iff hd0).mpr
    intro p hp
    apply (modEq_pow_iff_digits (Nat.prime_of_mem_primeFactors hp).pos).mpr
    intro e he
    have hpN : p ∈ N.primeFactors := Nat.primeFactors_mono hd hN hp
    have heN : e < N.factorization p :=
      lt_of_lt_of_le he ((Nat.factorization_le_iff_dvd hd0 hN).mpr hd p)
    exact congrArg Fin.val (h ⟨⟨p, hpN⟩, ⟨e, heN⟩⟩
      (digitPoint N a ⟨⟨p, hpN⟩, ⟨e, heN⟩⟩) (by simp [congruenceBox, he]))
  · intro h i v hv
    by_cases hi : (i.2 : ℕ) < d.factorization i.1
    · have hv' : digitPoint N a i = v := by simpa [congruenceBox, hi] using hv
      rw [← hv']
      apply Fin.ext
      apply digit_eq_of_modEq _ hi
      exact h.of_dvd ((Nat.prime_of_mem_primeFactors i.1.2).pow_dvd_iff_le_factorization hd0
        |>.mpr le_rfl)
    · simp [congruenceBox, hi] at hv

lemma familyFixed_lcm (D : Finset ℕ) (a : ℕ → ℕ) (hD : ∀ d ∈ D, d ≠ 0) :
    Grid.familyFixed (fun d => congruenceBox (D.lcm id) d (a d)) D = univ := by
  ext i
  simp only [mem_univ, iff_true, Grid.mem_familyFixed, mem_fixed_congruenceBox]
  apply Finset.lt_sup_iff.mp
  rw [← Finset.factorization_lcm hD]
  exact i.2.isLt

/-- Simpson's arithmetic weight, one slot per nonzero digit value. -/
def simpsonWeight (N : ℕ) : ℕ :=
  ∑ p ∈ N.primeFactors, N.factorization p * (p - 1)

lemma sum_coordinateSize (N : ℕ) :
    (∑ i : PrimeCoordinate N, (coordinateSize i - 1)) = simpsonWeight N := by
  simp only [PrimeCoordinate, coordinateSize, Fintype.sum_sigma, sum_const,
    card_univ, Fintype.card_fin, smul_eq_mul, simpsonWeight]
  exact Finset.sum_coe_sort N.primeFactors (fun p => N.factorization p * (p - 1))

end Erdos1189
