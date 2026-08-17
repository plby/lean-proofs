/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of the positive resolution of Erdős Problem 437.
https://www.erdosproblems.com/437

For every ε > 0 and every sufficiently large x, we construct a strictly
increasing finite sequence in [1,x] with more than x^(1-ε) square partial
products.  The finite combinatorial core is Lemma 4.2 of Bui--Pratt--
Zaharescu; the reservoir used here consists of fixed-size products of small
primes, so the only analytic input required for the qualitative result is the
prime number theorem.

Mathematical sources:
- H. M. Bui, K. Pratt, A. Zaharescu, Math. Proc. Camb. Phil. Soc. 176 (2024).
- T. Tao, "A result of Bui--Pratt--Zaharescu, and Erdős problem #437" (2024).

A detailed mathematical proof, including Tao's sharper quantitative bounds,
is in `tex/437.tex`.
-/

import Mathlib
import PrimeNumberTheoremAnd.Consequences

namespace Erdos437

open Filter
open scoped BigOperators Nat Real symmDiff

set_option autoImplicit false

/-- The product of the terms of `A` not exceeding `a`; when `A` is listed in
increasing order, this is the partial product ending at `a`. -/
def prefixProd (A : Finset ℕ) (a : ℕ) : ℕ :=
  ∏ b ∈ A.filter (· ≤ a), b

/-- The number of square partial products in the canonical increasing listing
of a finite set of positive integers. -/
def squarePrefixCount (A : Finset ℕ) : ℕ :=
  (A.filter fun a ↦ IsSquare (prefixProd A a)).card

/-- Indices of square partial products of a list. -/
def squarePrefixIndices (a : List ℕ) : Finset ℕ :=
  (Finset.range a.length).filter fun i ↦ IsSquare ((a.take (i + 1)).prod)

/-- Number of square partial products of a list. -/
def squarePartialProductCount (a : List ℕ) : ℕ :=
  (squarePrefixIndices a).card

/-- A finite set is an admissible sequence for cutoff `x` when all its terms
lie in the interval `[1,x]`.  Its canonical increasing listing is then the
sequence in the original problem. -/
def IsAdmissible (x : ℕ) (a : List ℕ) : Prop :=
  a.Pairwise (· < ·) ∧ ∀ n ∈ a, 1 ≤ n ∧ n ≤ x

/-- The exact positive-answer statement in Erdős Problem 437. -/
def PositiveAnswer : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
    ∃ a : List ℕ, IsAdmissible x a ∧
      (x : ℝ) ^ (1 - ε) < squarePartialProductCount a

/-! ## Squares and factorization parity -/

/-- A positive natural number whose prime valuations are all even is a square. -/
lemma isSquare_of_even_factorization {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → Even (n.factorization p)) : IsSquare n := by
  let r : ℕ := ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)
  rw [isSquare_iff_exists_mul_self]
  refine ⟨r, ?_⟩
  symm
  dsimp only [r]
  rw [← Finset.prod_mul_distrib]
  calc
    ∏ p ∈ n.primeFactors,
        p ^ (n.factorization p / 2) * p ^ (n.factorization p / 2) =
        ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
          apply Finset.prod_congr rfl
          intro p hp
          rw [← pow_add]
          obtain ⟨e, he⟩ := h p (Nat.prime_of_mem_primeFactors hp)
          congr 1
          omega
    _ = n := (Nat.prod_primeFactors_pow_factorization hn).symm

/-- The parity vector of a number on a finite set of primes. -/
def parityVector (P : Finset ℕ) (n : ℕ) : P → ZMod 2 :=
  fun p ↦ (n.factorization p : ZMod 2)

private lemma zmod_two_eq_one_of_ne_zero {z : ZMod 2} (hz : z ≠ 0) : z = 1 := by
  exact Fin.eq_one_of_ne_zero z hz

/-- The Bui--Pratt--Zaharescu finite lemma: more `P`-factored positive
integers than primes in `P` contain a nonempty square-product subcollection. -/
lemma exists_nonempty_square_subproduct
    (P C : Finset ℕ)
    (_hP : ∀ p ∈ P, p.Prime)
    (hCpos : ∀ n ∈ C, n ≠ 0)
    (hCfac : ∀ n ∈ C, n ∈ Nat.factoredNumbers P)
    (hcard : P.card < C.card) :
    ∃ S : Finset ℕ, S.Nonempty ∧ S ⊆ C ∧ IsSquare (∏ n ∈ S, n) := by
  let v : C → (P → ZMod 2) := fun n ↦ parityVector P n
  have hv : ¬ LinearIndependent (ZMod 2) v := by
    intro hv
    have hc := hv.fintype_card_le_finrank
    have hc' : C.card ≤ P.card := by
      simpa [v, Module.finrank_fintype_fun_eq_card] using hc
    exact (not_le_of_gt hcard) hc'
  obtain ⟨g, hsum, i, hgi⟩ := Fintype.not_linearIndependent_iff.mp hv
  let T : Finset C := Finset.univ.filter fun i ↦ g i ≠ 0
  have hTne : T.Nonempty := by
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgi⟩⟩
  let S : Finset ℕ := T.image Subtype.val
  have hScard : S.card = T.card := by
    exact Finset.card_image_of_injective _ Subtype.val_injective
  have hSne : S.Nonempty := by
    exact hTne.image Subtype.val
  have hSC : S ⊆ C := by
    intro n hn
    simp only [S, Finset.mem_image] at hn
    obtain ⟨i, -, rfl⟩ := hn
    exact i.2
  have hsumT : ∑ i ∈ T, v i = 0 := by
    calc
      ∑ i ∈ T, v i = ∑ i, g i • v i := by
        simp only [T, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : g j = 0
        · simp [hj]
        · simp [zmod_two_eq_one_of_ne_zero hj]
      _ = 0 := hsum
  have hparity : ∀ p ∈ P, ((∏ n ∈ S, n).factorization p : ZMod 2) = 0 := by
    intro p hp
    have hcoord := congrFun hsumT ⟨p, hp⟩
    simp only [Finset.sum_apply, Pi.zero_apply] at hcoord
    have hprod_ne : ∀ n ∈ S, n ≠ 0 := fun n hn ↦ hCpos n (hSC hn)
    rw [Nat.factorization_prod_apply hprod_ne, Nat.cast_sum]
    simp only [S]
    rw [Finset.sum_image Subtype.val_injective.injOn]
    simpa [v, parityVector] using hcoord
  refine ⟨S, hSne, hSC, isSquare_of_even_factorization ?_ ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun n hn ↦ hCpos n (hSC hn)
  · intro p hp
    by_cases hpP : p ∈ P
    · exact ZMod.natCast_eq_zero_iff_even.mp (hparity p hpP)
    · have hprod_fac : (∏ n ∈ S, n) ∈ Nat.factoredNumbers P := by
        have hprod : ∀ U : Finset ℕ, U ⊆ C →
            (∏ n ∈ U, n) ∈ Nat.factoredNumbers P := by
          intro U hUC
          induction U using Finset.induction with
          | empty => simp [Nat.mem_factoredNumbers]
          | @insert a U ha ih =>
              rw [Finset.prod_insert ha]
              exact Nat.mul_mem_factoredNumbers
                (hCfac a (hUC (Finset.mem_insert_self a U)))
                (ih fun n hn ↦ hUC (Finset.mem_insert_of_mem hn))
        exact hprod S hSC
      have hnotdvd : ¬ p ∣ ∏ n ∈ S, n := by
        intro hpdvd
        exact hpP (Nat.mem_factoredNumbers'.mp hprod_fac p hp hpdvd)
      rw [Nat.factorization_eq_zero_of_not_dvd hnotdvd]
      exact Even.zero

/-! ## Packing square blocks in increasing order -/

/-- Prepending a nonempty square-product block creates one new square partial
product and preserves all square partial products of the tail. -/
lemma one_add_squarePartialProductCount_le_append
    (s a : List ℕ) (hs : s ≠ []) (hsq : IsSquare s.prod) :
    1 + squarePartialProductCount a ≤ squarePartialProductCount (s ++ a) := by
  let j : ℕ := s.length - 1
  let shifted : Finset ℕ := (squarePrefixIndices a).image fun i ↦ s.length + i
  have hspos : 0 < s.length := List.length_pos_of_ne_nil hs
  have hjlt : j < (s ++ a).length := by
    simp only [j, List.length_append]
    omega
  have hjmem : j ∈ squarePrefixIndices (s ++ a) := by
    rw [squarePrefixIndices, Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr hjlt, ?_⟩
    have hslen : j + 1 = s.length := by
      simp only [j]
      omega
    rw [hslen, List.take_left]
    exact hsq
  have hshift : shifted ⊆ squarePrefixIndices (s ++ a) := by
    intro k hk
    simp only [shifted, Finset.mem_image] at hk
    obtain ⟨i, hi, rfl⟩ := hk
    rw [squarePrefixIndices, Finset.mem_filter] at hi ⊢
    refine ⟨Finset.mem_range.mpr ?_, ?_⟩
    · simpa only [List.length_append] using Nat.add_lt_add_left
        (Finset.mem_range.mp hi.1) s.length
    · have htake : (s ++ a).take (s.length + i + 1) = s ++ a.take (i + 1) := by
        simpa [Nat.add_assoc] using
          (List.take_length_add_append (l₁ := s) (l₂ := a) (i + 1))
      rw [htake, List.prod_append]
      exact hsq.mul hi.2
  have hjnot : j ∉ shifted := by
    intro hj
    simp only [shifted, Finset.mem_image] at hj
    obtain ⟨i, -, hi⟩ := hj
    simp only [j] at hi
    omega
  have hsub : insert j shifted ⊆ squarePrefixIndices (s ++ a) := by
    intro k hk
    rw [Finset.mem_insert] at hk
    rcases hk with rfl | hk
    · exact hjmem
    · exact hshift hk
  calc
    1 + squarePartialProductCount a = (insert j shifted).card := by
      rw [Finset.card_insert_of_notMem hjnot]
      simp only [shifted, squarePartialProductCount]
      rw [Finset.card_image_of_injective _ (fun _ _ h ↦ Nat.add_left_cancel h)]
      omega
    _ ≤ (squarePrefixIndices (s ++ a)).card := Finset.card_le_card hsub
    _ = squarePartialProductCount (s ++ a) := rfl

/-- An ordered factored reservoir of size at least `(P.card + 1) * g` contains
an increasing subsequence with at least `g` square partial products. -/
lemma exists_many_square_partial_products_list
    (P : Finset ℕ) (L : List ℕ) (g : ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (hLsort : L.Pairwise (· < ·))
    (hLpos : ∀ n ∈ L, n ≠ 0)
    (hLfac : ∀ n ∈ L, n ∈ Nat.factoredNumbers P)
    (hlen : (P.card + 1) * g ≤ L.length) :
    ∃ a : List ℕ,
      a.Pairwise (· < ·) ∧
      (∀ n ∈ a, n ∈ L) ∧
      g ≤ squarePartialProductCount a := by
  induction g generalizing L with
  | zero =>
      exact ⟨[], by simp, by simp, by simp⟩
  | succ g ih =>
      let q := P.card + 1
      let head : List ℕ := L.take q
      let tail : List ℕ := L.drop q
      have hqL : q ≤ L.length := by
        simp only [Nat.mul_succ] at hlen
        omega
      have hheadlen : head.length = q := by simp [head, hqL]
      have hheadnodup : head.Nodup := (List.take_sublist q L).nodup hLsort.nodup
      let C : Finset ℕ := head.toFinset
      have hCcard : C.card = q := by
        simpa [C, hheadlen] using List.toFinset_card_of_nodup hheadnodup
      have hCpos : ∀ n ∈ C, n ≠ 0 := by
        intro n hn
        apply hLpos n
        exact List.mem_of_mem_take (by simpa [C] using hn)
      have hCfac : ∀ n ∈ C, n ∈ Nat.factoredNumbers P := by
        intro n hn
        apply hLfac n
        exact List.mem_of_mem_take (by simpa [C] using hn)
      have hPC : P.card < C.card := by simp [hCcard, q]
      obtain ⟨S, hSne, hSC, hSsq⟩ :=
        exists_nonempty_square_subproduct P C hP hCpos hCfac hPC
      let s : List ℕ := S.sort (· ≤ ·)
      have hsne : s ≠ [] := by
        intro hs
        have : S = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro n hn
          have : n ∈ s := by simpa [s] using hn
          simp [hs] at this
        exact hSne.ne_empty this
      have hssort : s.Pairwise (· < ·) := (Finset.sortedLT_sort S).pairwise
      have hsprod : IsSquare s.prod := by
        have hprod : s.prod = S.prod id := by
          calc
            s.prod = s.toFinset.prod id :=
              (by dsimp only [s]
                  simpa using
                (List.prod_toFinset id (Finset.sort_nodup S (· ≤ ·))).symm)
            _ = S.prod id := by simp [s]
        rw [hprod]
        exact hSsq
      have hsmemHead : ∀ n ∈ s, n ∈ head := by
        intro n hn
        have hnS : n ∈ S := by simpa [s] using hn
        have hnC := hSC hnS
        simpa [C] using hnC
      have htailSort : tail.Pairwise (· < ·) :=
        by simpa [tail] using (hLsort.drop (i := q))
      have htailPos : ∀ n ∈ tail, n ≠ 0 := by
        intro n hn
        exact hLpos n (List.mem_of_mem_drop hn)
      have htailFac : ∀ n ∈ tail, n ∈ Nat.factoredNumbers P := by
        intro n hn
        exact hLfac n (List.mem_of_mem_drop hn)
      have htailLen : q * g ≤ tail.length := by
        simp only [tail, List.length_drop, q]
        simp only [Nat.mul_succ] at hlen
        omega
      obtain ⟨a, hasort, hamem, hag⟩ :=
        ih tail htailSort htailPos htailFac (by simpa [q] using htailLen)
      have hcross : ∀ x ∈ s, ∀ y ∈ a, x < y := by
        have hsplit : ∀ x ∈ head, ∀ y ∈ tail, x < y := by
          have hpair := hLsort
          rw [← List.take_append_drop q L] at hpair
          exact (List.pairwise_append.mp hpair).2.2
        intro x hx y hy
        exact hsplit x (hsmemHead x hx) y (hamem y hy)
      refine ⟨s ++ a, ?_, ?_, ?_⟩
      · exact List.pairwise_append.mpr ⟨hssort, hasort, hcross⟩
      · intro n hn
        rw [List.mem_append] at hn
        rcases hn with hn | hn
        · exact List.mem_of_mem_take (hsmemHead n hn)
        · exact List.mem_of_mem_drop (hamem n hn)
      · have hcount := (Nat.add_le_add_left hag 1).trans
          (one_add_squarePartialProductCount_le_append s a hsne hsprod)
        simpa [Nat.add_comm] using hcount

/-! ## A reservoir of fixed-size products of small primes -/

/-- Products of `r` distinct primes at most `y`. -/
def primeProducts (y r : ℕ) : Finset ℕ :=
  (Nat.primesLE y).powersetCard r |>.image fun S ↦ S.prod id

private lemma product_of_primes_factors_toFinset {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) :
    (S.prod id).primeFactorsList.toFinset = S := by
  have hprod : (S.sort (· ≤ ·)).prod = S.prod id := by
    calc
      (S.sort (· ≤ ·)).prod = (S.sort (· ≤ ·)).toFinset.prod id := by
        simpa using (List.prod_toFinset id (S.sort_nodup (· ≤ ·))).symm
      _ = S.prod id := by rw [Finset.sort_toFinset]
  have hprime : ∀ p ∈ S.sort (· ≤ ·), p.Prime := by
    intro p hp
    exact hS p ((Finset.mem_sort (· ≤ ·)).mp hp)
  have hperm : List.Perm (S.sort (· ≤ ·)) (S.prod id).primeFactorsList :=
    Nat.primeFactorsList_unique hprod hprime
  exact (List.toFinset_eq_of_perm _ _ hperm).symm.trans (Finset.sort_toFinset _ _)

lemma prod_injective_on_primeSubsets (y : ℕ) :
    Set.InjOn (fun S : Finset ℕ ↦ S.prod id) (Nat.primesLE y).powerset := by
  intro A hA B hB hprod
  have hAprime : ∀ p ∈ A, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primesLE (Finset.mem_powerset.mp hA hp)
  have hBprime : ∀ p ∈ B, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primesLE (Finset.mem_powerset.mp hB hp)
  change A.prod id = B.prod id at hprod
  calc
    A = (A.prod id).primeFactorsList.toFinset :=
      (product_of_primes_factors_toFinset hAprime).symm
    _ = (B.prod id).primeFactorsList.toFinset := by rw [hprod]
    _ = B := product_of_primes_factors_toFinset hBprime

lemma card_primeProducts (y r : ℕ) :
    (primeProducts y r).card = (Nat.primeCounting y).choose r := by
  rw [primeProducts, Finset.card_image_iff.mpr]
  · rw [Finset.card_powersetCard, Nat.primesLE_card_eq_primeCounting]
  · apply (prod_injective_on_primeSubsets y).mono
    intro S hS
    exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hS).1

lemma primeProducts_pos {y r n : ℕ} (hn : n ∈ primeProducts y r) : n ≠ 0 := by
  rw [primeProducts, Finset.mem_image] at hn
  obtain ⟨S, hS, rfl⟩ := hn
  exact Finset.prod_ne_zero_iff.mpr fun p hp ↦
    (Nat.prime_of_mem_primesLE
      (Finset.mem_powersetCard.mp hS |>.1 hp)).ne_zero

lemma primeProducts_factored {y r n : ℕ} (hn : n ∈ primeProducts y r) :
    n ∈ Nat.factoredNumbers (Nat.primesLE y) := by
  rw [primeProducts, Finset.mem_image] at hn
  obtain ⟨S, hS, rfl⟩ := hn
  have hSP : S ⊆ Nat.primesLE y := (Finset.mem_powersetCard.mp hS).1
  have hprime : ∀ p ∈ S, p.Prime := fun p hp ↦
    Nat.prime_of_mem_primesLE (hSP hp)
  have hne : S.prod id ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp ↦
    (hprime p hp).ne_zero
  apply Nat.mem_factoredNumbers_of_primeFactors_subset hne
  intro p hp
  have hp' : p ∈ (S.prod id).primeFactorsList.toFinset := by
    exact List.mem_toFinset.mpr
      (Nat.mem_primeFactors_iff_mem_primeFactorsList.mp hp)
  rw [product_of_primes_factors_toFinset hprime] at hp'
  exact hSP hp'

lemma primeProducts_le_pow {y r n : ℕ} (hn : n ∈ primeProducts y r) : n ≤ y ^ r := by
  rw [primeProducts, Finset.mem_image] at hn
  obtain ⟨S, hS, rfl⟩ := hn
  have hsub : S ⊆ Nat.primesLE y := (Finset.mem_powersetCard.mp hS).1
  calc
    S.prod id ≤ S.prod (fun _ ↦ y) := by
      exact Finset.prod_le_prod (fun p hp ↦ Nat.zero_le p)
        (fun p hp ↦ Nat.le_of_mem_primesLE (hsub hp))
    _ = y ^ S.card := by simp
    _ = y ^ r := by rw [(Finset.mem_powersetCard.mp hS).2]

/-- Finite reduction: a binomially large prime-product reservoir gives `g`
square partial products below `y^r`. -/
lemma exists_many_square_partial_products_primeProducts
    (y r g : ℕ)
    (hsize : (Nat.primeCounting y + 1) * g ≤ (Nat.primeCounting y).choose r) :
    ∃ a : List ℕ,
      a.Pairwise (· < ·) ∧
      (∀ n ∈ a, 1 ≤ n ∧ n ≤ y ^ r) ∧
      g ≤ squarePartialProductCount a := by
  let P := Nat.primesLE y
  let B := primeProducts y r
  let L := B.sort (· ≤ ·)
  have hP : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primesLE hp
  have hLsort : L.Pairwise (· < ·) := (Finset.sortedLT_sort B).pairwise
  have hLpos : ∀ n ∈ L, n ≠ 0 := by
    intro n hn
    exact primeProducts_pos ((Finset.mem_sort (· ≤ ·)).mp hn)
  have hLfac : ∀ n ∈ L, n ∈ Nat.factoredNumbers P := by
    intro n hn
    exact primeProducts_factored ((Finset.mem_sort (· ≤ ·)).mp hn)
  have hlen : (P.card + 1) * g ≤ L.length := by
    simpa [P, B, L, card_primeProducts, Nat.primesLE_card_eq_primeCounting] using hsize
  obtain ⟨a, hasort, hamem, hag⟩ :=
    exists_many_square_partial_products_list P L g hP hLsort hLpos hLfac hlen
  refine ⟨a, hasort, ?_, hag⟩
  intro n hn
  have hnL := hamem n hn
  have hnB : n ∈ B := (Finset.mem_sort (· ≤ ·)).mp hnL
  exact ⟨Nat.one_le_iff_ne_zero.mpr (primeProducts_pos hnB), primeProducts_le_pow hnB⟩

/-! ## The reservoir is large enough -/

/-- A convenient explicit estimate ensuring that the number of `r`-element
prime subsets can be split into the required blocks. -/
lemma blocks_le_choose {m r : ℕ} (hr : 2 ≤ r)
    (hlinear : 2 * r ≤ m + 2)
    (hlarge : 2 ^ (r + 1) * r.factorial ≤ m) :
    (m + 1) * m ^ (r - 2) ≤ m.choose r := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
  have hmpos : 0 < m := by
    have : 0 < 2 ^ (d + 2 + 1) * (d + 2).factorial := by positivity
    omega
  have hlarge' : 2 ^ (d + 2 + 1) * (d + 2).factorial ≤ m := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hlarge
  have hmone : m + 1 ≤ 2 * m := by omega
  let z := m + 1 - (d + 2)
  have hmz : m ≤ 2 * z := by
    dsimp only [z]
    omega
  have hfactorial :
      (d + 2).factorial * ((m + 1) * m ^ d) ≤
        2 * (d + 2).factorial * m ^ (d + 1) := by
    calc
      (d + 2).factorial * ((m + 1) * m ^ d) ≤
          (d + 2).factorial * ((2 * m) * m ^ d) := by
            exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hmone)
      _ = 2 * (d + 2).factorial * m ^ (d + 1) := by
        rw [pow_succ]
        ring
  have hscaled :
      2 ^ (d + 2) * ((d + 2).factorial * ((m + 1) * m ^ d)) ≤
        m ^ (d + 2) := by
    calc
      2 ^ (d + 2) * ((d + 2).factorial * ((m + 1) * m ^ d)) ≤
          2 ^ (d + 2) * (2 * (d + 2).factorial * m ^ (d + 1)) :=
            Nat.mul_le_mul_left _ hfactorial
      _ = (2 ^ (d + 2 + 1) * (d + 2).factorial) * m ^ (d + 1) := by
        rw [pow_succ]
        ring
      _ ≤ m * m ^ (d + 1) := Nat.mul_le_mul_right _ hlarge'
      _ = m ^ (d + 2) := by
        rw [pow_succ]
        ring
  have hpow : m ^ (d + 2) ≤ 2 ^ (d + 2) * z ^ (d + 2) := by
    calc
      m ^ (d + 2) ≤ (2 * z) ^ (d + 2) := Nat.pow_le_pow_left hmz _
      _ = 2 ^ (d + 2) * z ^ (d + 2) := by rw [mul_pow]
  have htoz :
      (d + 2).factorial * ((m + 1) * m ^ d) ≤ z ^ (d + 2) := by
    exact Nat.le_of_mul_le_mul_left (hscaled.trans hpow) (by positivity)
  have hzdesc : z ^ (d + 2) ≤ m.descFactorial (d + 2) := by
    simpa [z] using Nat.pow_sub_le_descFactorial m (d + 2)
  have hcancel :
      (d + 2).factorial * ((m + 1) * m ^ d) ≤
        (d + 2).factorial * m.choose (d + 2) := by
    calc
      (d + 2).factorial * ((m + 1) * m ^ d) ≤ z ^ (d + 2) := htoz
      _ ≤ m.descFactorial (d + 2) := hzdesc
      _ = (d + 2).factorial * m.choose (d + 2) := by
        rw [Nat.descFactorial_eq_factorial_mul_choose]
  have hresult : (m + 1) * m ^ d ≤ m.choose (d + 2) :=
    Nat.le_of_mul_le_mul_left hcancel (by positivity)
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hresult

/-! ## A weak quantitative consequence of the prime number theorem -/

/-- Eventually the prime-counting function is at least half of its prime
number theorem main term. -/
lemma eventually_primeCounting_lower :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / (2 * Real.log n) ≤ (Nat.primeCounting n : ℝ) := by
  have hden : ∀ᶠ x : ℝ in atTop, x / Real.log x ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_ne_zero (by positivity) (Real.log_pos hx).ne'
  have hratio :
      Tendsto
        (fun x : ℝ ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x))
        atTop (nhds 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hden).mp pi_alt'
  have hclose :
      ∀ᶠ x : ℝ in atTop,
        |(Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x) - 1| < 1 / 2 :=
    hratio.eventually (Metric.ball_mem_nhds 1 (by norm_num))
  have hcloseNat := tendsto_natCast_atTop_atTop.eventually hclose
  filter_upwards [hcloseNat, eventually_ge_atTop 2] with n hnclose hn
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  have hmain : 0 < (n : ℝ) / Real.log n := div_pos (by positivity) (Real.log_pos hnreal)
  have hratioLower :
      (1 / 2 : ℝ) < (Nat.primeCounting n : ℝ) / ((n : ℝ) / Real.log n) := by
    have h := (abs_lt.mp hnclose).1
    simp only [Nat.floor_natCast] at h
    linarith
  have hmul :
      (1 / 2 : ℝ) * ((n : ℝ) / Real.log n) < (Nat.primeCounting n : ℝ) :=
    (lt_div_iff₀ hmain).mp hratioLower
  have heq :
      (n : ℝ) / (2 * Real.log n) =
        (1 / 2 : ℝ) * ((n : ℝ) / Real.log n) := by ring
  rw [heq]
  exact hmul.le

/-- For each fixed positive integer `Q`, the prime number theorem implies
`n^(Q-1) ≤ π(n)^Q` for all sufficiently large `n`. -/
lemma eventually_pow_le_primeCounting_pow (Q : ℕ) (hQ : 1 ≤ Q) :
    ∀ᶠ n : ℕ in atTop,
      n ^ (Q - 1) ≤ (Nat.primeCounting n) ^ Q := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hQ)
  have hexp : (0 : ℝ) < 1 / (Q : ℝ) := by positivity
  have hsmallReal :=
    (isLittleO_log_rpow_atTop hexp).bound (show 0 < (1 / 2 : ℝ) by norm_num)
  have hsmallNat := tendsto_natCast_atTop_atTop.eventually hsmallReal
  filter_upwards [eventually_primeCounting_lower, hsmallNat,
    eventually_ge_atTop 2] with n hpi hsmall hn
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos hnR
  have hrpownonneg : 0 ≤ (n : ℝ) ^ (1 / (Q : ℝ)) :=
    Real.rpow_nonneg hnpos.le _
  have hsmall' :
      Real.log (n : ℝ) ≤
        (1 / 2 : ℝ) * (n : ℝ) ^ (1 / (Q : ℝ)) := by
    have hsmallAbs :
        |Real.log (n : ℝ)| ≤
          (1 / 2 : ℝ) * |(n : ℝ) ^ (1 / (Q : ℝ))| := by
      simpa only [Real.norm_eq_abs] using hsmall
    simpa only [abs_of_pos hlogpos, abs_of_nonneg hrpownonneg] using hsmallAbs
  have hdenBound :
      2 * Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / (Q : ℝ)) := by
    linarith
  have hdenPow :
      (2 * Real.log (n : ℝ)) ^ Q ≤ (n : ℝ) := by
    calc
      (2 * Real.log (n : ℝ)) ^ Q ≤
          ((n : ℝ) ^ (1 / (Q : ℝ))) ^ Q := by gcongr
      _ = (n : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
        field_simp
        simp
  have hdenpos : 0 < 2 * Real.log (n : ℝ) := by positivity
  have hn_le :
      (n : ℝ) ≤ (Nat.primeCounting n : ℝ) * (2 * Real.log (n : ℝ)) :=
    (div_le_iff₀ hdenpos).mp hpi
  have hpow_le :
      (n : ℝ) ^ Q ≤
        ((Nat.primeCounting n : ℝ) * (2 * Real.log (n : ℝ))) ^ Q := by
    gcongr
  rw [mul_pow] at hpow_le
  have hpow_le' :
      (n : ℝ) ^ Q ≤ (Nat.primeCounting n : ℝ) ^ Q * n :=
    hpow_le.trans (mul_le_mul_of_nonneg_left hdenPow (by positivity))
  have hcancel :
      (n : ℝ) ^ (Q - 1) * n ≤ (Nat.primeCounting n : ℝ) ^ Q * n := by
    convert hpow_le' using 1
    rw [← pow_succ]
    congr 1
    omega
  have hreal :
      (n : ℝ) ^ (Q - 1) ≤ (Nat.primeCounting n : ℝ) ^ Q :=
    le_of_mul_le_mul_right hcancel hnpos
  exact_mod_cast hreal

/-- A fixed positive root tends to infinity. -/
lemma tendsto_nthRoot_atTop {r : ℕ} (hr : r ≠ 0) :
    Tendsto (Nat.nthRoot r) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨b ^ r, ?_⟩
  intro x hx
  exact (Nat.le_nthRoot_iff hr).mpr hx

/-- The elementary exponent calculation that turns the weak PNT estimate
into enough square blocks. -/
lemma primeCounting_block_growth {q y x : ℕ} (hq : 2 ≤ q)
    (hpi : y ^ (2 * q - 1) ≤ (Nat.primeCounting y) ^ (2 * q))
    (hybig : 2 ^ ((4 * q) * (q - 1)) < y)
    (hx : x < (y + 1) ^ (4 * q)) :
    x ^ (q - 1) <
      ((Nat.primeCounting y) ^ (4 * q - 2)) ^ q := by
  let e := (4 * q) * (q - 1)
  have htwopos : 0 < 2 ^ ((4 * q) * (q - 1)) := by positivity
  have hypos : 0 < y := by omega
  have hyone : 1 ≤ y := hypos
  have hyadd : y + 1 ≤ 2 * y := by omega
  have hxbase : x < (2 * y) ^ (4 * q) :=
    hx.trans_le (Nat.pow_le_pow_left hyadd _)
  have hxpow : x ^ (q - 1) < ((2 * y) ^ (4 * q)) ^ (q - 1) := by
    exact Nat.pow_lt_pow_left hxbase (by omega)
  have hxpow' : x ^ (q - 1) < (2 * y) ^ e := by
    simpa only [e, pow_mul] using hxpow
  have htwopow : (2 * y) ^ e < y ^ (e + 1) := by
    rw [mul_pow, pow_succ]
    simpa only [e, mul_comm] using
      Nat.mul_lt_mul_of_pos_right hybig (pow_pos hypos e)
  have hpipow := Nat.pow_le_pow_left hpi (2 * q - 1)
  have hexpLeft : (2 * q - 1) * (2 * q - 1) = e + 1 := by
    dsimp only [e]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hq
    have htwo : 2 * (2 + d) - 1 = 3 + 2 * d := by omega
    have hpred : 2 + d - 1 = 1 + d := by omega
    rw [htwo, hpred]
    ring
  have hexpRight : (2 * q) * (2 * q - 1) = (4 * q - 2) * q := by
    have hfourpred : 4 * q - 2 = 2 * (2 * q - 1) := by omega
    rw [hfourpred]
    ring
  have hgrowth : y ^ (e + 1) ≤
      ((Nat.primeCounting y) ^ (4 * q - 2)) ^ q := by
    rw [← pow_mul, ← hexpRight, pow_mul]
    rw [← hexpLeft, pow_mul]
    exact hpipow
  exact hxpow'.trans (htwopow.trans_le hgrowth)

/-- Integer-exponent form of the construction.  It is the bridge between
the finite square-block lemma and the final real-exponent statement. -/
lemma eventually_exists_count_pow_gt (q : ℕ) (hq : 2 ≤ q) :
    ∀ᶠ x : ℕ in atTop, ∃ a : List ℕ,
      IsAdmissible x a ∧
        x ^ (q - 1) < (squarePartialProductCount a) ^ q := by
  let r := 4 * q
  have hrpos : 0 < r := by simp only [r]; positivity
  have hrne : r ≠ 0 := hrpos.ne'
  have hrge : 2 ≤ r := by simp only [r]; omega
  have hQ : 1 ≤ 2 * q := by omega
  have hpi := eventually_pow_le_primeCounting_pow (2 * q) hQ
  have hlinear :
      ∀ᶠ y : ℕ in atTop, 2 * r ≤ Nat.primeCounting y :=
    Nat.tendsto_primeCounting.eventually (eventually_ge_atTop (2 * r))
  have hlarge :
      ∀ᶠ y : ℕ in atTop,
        2 ^ (r + 1) * r.factorial ≤ Nat.primeCounting y :=
    Nat.tendsto_primeCounting.eventually
      (eventually_ge_atTop (2 ^ (r + 1) * r.factorial))
  have hybig :
      ∀ᶠ y : ℕ in atTop, 2 ^ (r * (q - 1)) < y :=
    eventually_gt_atTop (2 ^ (r * (q - 1)))
  have heventY :
      ∀ᶠ y : ℕ in atTop,
        2 * r ≤ Nat.primeCounting y ∧
        2 ^ (r + 1) * r.factorial ≤ Nat.primeCounting y ∧
        y ^ (2 * q - 1) ≤ (Nat.primeCounting y) ^ (2 * q) ∧
        2 ^ (r * (q - 1)) < y := by
    filter_upwards [hlinear, hlarge, hpi, hybig] with y hlin hlarge' hpi' hybig'
    exact ⟨hlin, hlarge', hpi', hybig'⟩
  have hrootEvent := (tendsto_nthRoot_atTop hrne).eventually heventY
  filter_upwards [hrootEvent] with x hxevent
  let y := Nat.nthRoot r x
  let m := Nat.primeCounting y
  let g := m ^ (r - 2)
  have hlin : 2 * r ≤ m := by simpa only [y, m] using hxevent.1
  have hlarge' : 2 ^ (r + 1) * r.factorial ≤ m := by
    simpa only [y, m] using hxevent.2.1
  have hpi' : y ^ (2 * q - 1) ≤ m ^ (2 * q) := by
    simpa only [y, m] using hxevent.2.2.1
  have hybig' : 2 ^ (r * (q - 1)) < y := by
    simpa only [y] using hxevent.2.2.2
  have hsize : (m + 1) * g ≤ m.choose r := by
    apply blocks_le_choose hrge
    · omega
    · exact hlarge'
  obtain ⟨a, hasort, habound, hag⟩ :=
    exists_many_square_partial_products_primeProducts y r g
      (by simpa only [m] using hsize)
  have hyrx : y ^ r ≤ x := by
    exact Nat.pow_nthRoot_le (Or.inl hrne)
  have hxroot : x < (y + 1) ^ r := by
    exact Nat.lt_pow_nthRoot_add_one hrne x
  have hgrowth : x ^ (q - 1) < g ^ q := by
    apply primeCounting_block_growth hq
    · simpa only [m] using hpi'
    · simpa only [r] using hybig'
    · simpa only [r] using hxroot
  refine ⟨a, ⟨hasort, ?_⟩, hgrowth.trans_le ?_⟩
  · intro n hn
    exact ⟨(habound n hn).1, (habound n hn).2.trans hyrx⟩
  · exact Nat.pow_le_pow_left hag q

/-- Taking the positive `q`-th root of the integer-power estimate. -/
lemma rpow_one_sub_inv_lt_of_pow_lt {x c q : ℕ} (hq : 1 ≤ q)
    (hx : 1 < x) (hpow : x ^ (q - 1) < c ^ q) :
    (x : ℝ) ^ (1 - 1 / (q : ℝ)) < c := by
  have hxpos : (0 : ℝ) < x := by positivity
  have hqR : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hpowR : (x : ℝ) ^ (q - 1) < (c : ℝ) ^ q := by exact_mod_cast hpow
  have hexp :
      (1 - 1 / (q : ℝ)) * (q : ℝ) = ((q - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hq]
    field_simp
    ring
  by_contra hnot
  have hle : (c : ℝ) ≤ (x : ℝ) ^ (1 - 1 / (q : ℝ)) := le_of_not_gt hnot
  have hraise :
      (c : ℝ) ^ q ≤ ((x : ℝ) ^ (1 - 1 / (q : ℝ))) ^ q := by
    gcongr
  have heq :
      ((x : ℝ) ^ (1 - 1 / (q : ℝ))) ^ q = (x : ℝ) ^ (q - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le, hexp, Real.rpow_natCast]
  rw [heq] at hraise
  exact (not_lt_of_ge hraise) hpowR

/-! ## Resolution of Erdős Problem 437 -/

/-- Erdős Problem 437 has a positive answer: for every `ε > 0`, all
sufficiently large cutoffs have a strictly increasing sequence in `[1,x]`
with more than `x^(1-ε)` square partial products. -/
theorem erdos437 : PositiveAnswer := by
  intro ε hε
  obtain ⟨q : ℕ, hqbound⟩ := exists_nat_gt (max (2 : ℝ) (1 / ε))
  have htwoR : (2 : ℝ) < q := (le_max_left _ _).trans_lt hqbound
  have hq : 2 ≤ q := by exact_mod_cast htwoR.le
  have hqR : (0 : ℝ) < q := by positivity
  have hqinvBound : (1 : ℝ) / ε < q :=
    (le_max_right (2 : ℝ) (1 / ε)).trans_lt hqbound
  have hinv : (1 : ℝ) / q < ε := by
    rw [div_lt_iff₀ hqR]
    have h := (div_lt_iff₀ hε).mp hqinvBound
    simpa only [one_mul, mul_comm] using h
  have hconstruct := eventually_exists_count_pow_gt q hq
  filter_upwards [hconstruct, eventually_ge_atTop 2] with x hxconstruct hx
  obtain ⟨a, ha, hpow⟩ := hxconstruct
  refine ⟨a, ha, ?_⟩
  have hxR : (1 : ℝ) < x := by exact_mod_cast hx
  have hexponents : 1 - ε < 1 - 1 / (q : ℝ) := by linarith
  exact (Real.rpow_lt_rpow_of_exponent_lt hxR hexponents).trans
    (rpow_one_sub_inv_lt_of_pow_lt (by omega) hx hpow)

end Erdos437

#print axioms Erdos437.erdos437
