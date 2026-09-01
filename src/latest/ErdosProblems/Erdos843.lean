/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 843.
https://www.erdosproblems.com/forum/thread/843

Informal authors:
- David Conlon
- Jacob Fox
- Huy Tuan Pham

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos843.md
-/
import Mathlib
import ErdosProblems.Erdos186.CFP.GrowthLemmas
import ErdosProblems.Erdos186.CFP.Lev

/-!
# Erdős Problem 843

The squares are Ramsey `2`-complete: in every two-colouring of the positive
square numbers, every sufficiently large natural number is a sum of distinct
squares of one colour.

The mathematical proof is the square specialization of Conlon--Fox--Pham,
*Subset sums, completeness and colorings*, Theorem 1.2.  The elementary
ordinary-completeness part and the finite robust-block interface used in the
Ramsey concatenation are developed below.
-/

open scoped BigOperators

namespace Erdos843

/-- A natural number is a positive square. -/
def IsPositiveSquare (q : ℕ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ q = m ^ 2

/-- `n` is a sum of distinct positive square numbers, all with the same colour.

The finset consists of the square *values*, so distinctness has exactly its
usual mathematical meaning rather than merely meaning distinct roots. -/
def MonochromaticSquareSum (colour : ℕ → Fin 2) (n : ℕ) : Prop :=
  ∃ squares : Finset ℕ,
    (∀ q ∈ squares, IsPositiveSquare q) ∧
    (∃ i : Fin 2, ∀ q ∈ squares, colour q = i) ∧
    ∑ q ∈ squares, q = n

/-- The exact Ramsey `2`-completeness assertion in Problem 843. -/
def SquaresRamseyTwoComplete : Prop :=
  ∀ colour : ℕ → Fin 2, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    MonochromaticSquareSum colour n

/-! ## Finite subset-sum intervals -/

/-- Every natural in the inclusive interval `[L, U]` is a subset sum of `D`. -/
def Covers (D : Finset ℕ) (L U : ℕ) : Prop :=
  ∀ n : ℕ, L ≤ n → n ≤ U → n ∈ D.subsetSum

lemma Covers.mono {D E : Finset ℕ} {L U : ℕ}
    (h : Covers D L U) (hDE : D ⊆ E) : Covers E L U := by
  intro n hnL hnU
  exact Finset.subsetSum_mono hDE (h n hnL hnU)

/-- Adjoining a new element not exceeding the old interval length plus one
extends the represented interval by that element. -/
lemma Covers.insert {D : Finset ℕ} {L U a : ℕ}
    (hLU : L ≤ U) (h : Covers D L U) (haD : a ∉ D)
    (ha : a ≤ U - L + 1) : Covers (insert a D) L (U + a) := by
  intro n hnL hnTop
  by_cases hnU : n ≤ U
  · exact Finset.subsetSum_mono (Finset.subset_insert a D) (h n hnL hnU)
  · have hna : a ≤ n := by omega
    have hlow : L ≤ n - a := by omega
    have hhigh : n - a ≤ U := by omega
    obtain ⟨T, hTD, hTsum⟩ := Finset.mem_subsetSum_iff.mp (h (n - a) hlow hhigh)
    refine Finset.mem_subsetSum_iff.mpr ⟨{a} ∪ T, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_union, Finset.mem_singleton] at hx
      rcases hx with rfl | hx
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hTD hx)
    · have haT : a ∉ T := fun haT ↦ haD (hTD haT)
      rw [Finset.sum_union (Finset.disjoint_singleton_left.mpr haT)]
      simp [hTsum]
      omega

/-! ## Transport from Lev sumsets to distinct natural subset sums -/

/-- Integer casts of all subset sums of a natural finset. -/
def intSubsetSums (D : Finset ℕ) : Finset ℤ :=
  D.subsetSum.image Int.ofNat

@[simp] lemma card_intSubsetSums (D : Finset ℕ) :
    (intSubsetSums D).card = D.subsetSum.card := by
  exact Finset.card_image_of_injective D.subsetSum Int.ofNat_injective

@[simp] lemma zero_mem_intSubsetSums (D : Finset ℕ) :
    (0 : ℤ) ∈ intSubsetSums D := by
  exact Finset.mem_image.mpr ⟨0, Finset.zero_mem_subsetSum, rfl⟩

lemma cast_mem_intSubsetSums_of_mem {D : Finset ℕ} {q : ℕ} (hq : q ∈ D) :
    (q : ℤ) ∈ intSubsetSums D := by
  exact Finset.mem_image.mpr ⟨q, Finset.subset_subsetSum hq, rfl⟩

/-- All subset sums of a natural block lie between zero and the sum of the
whole block. -/
lemma intSubsetSums_subset_Icc (D : Finset ℕ) :
    intSubsetSums D ⊆ Finset.Icc 0 (∑ q ∈ D, q : ℕ) := by
  intro z hz
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨T, hTD, rfl⟩ := Finset.mem_subsetSum_iff.mp hn
  apply Finset.mem_Icc.mpr
  constructor
  · exact Int.natCast_nonneg _
  · have hle : (∑ q ∈ T, q) ≤ ∑ q ∈ D, q :=
      Finset.sum_le_sum_of_subset_of_nonneg hTD
        (fun _ _ _ ↦ Nat.zero_le _)
    exact Int.ofNat_le.mpr hle

/-- The standard quadratic lower bound for subset sums of distinct positive
integers, restated for their integer casts. -/
lemma choose_two_lt_card_intSubsetSums_of_pos {D : Finset ℕ}
    (hpos : ∀ q ∈ D, 0 < q) :
    (D.card + 1).choose 2 < (intSubsetSums D).card := by
  rw [card_intSubsetSums]
  exact Finset.card_succ_choose_two_lt_card_subsetSum_of_pos hpos

/-- A gcd-one natural block has a primitive integer subset-sum set.  The
proof uses only the zero and singleton subset sums, which is precisely the
primitivity check in the final Lev step of CFP Lemma 2.9. -/
lemma intSubsetSums_primitive_of_gcd_eq_one {D : Finset ℕ}
    (hgcd : D.gcd id = 1) :
    Erdos186.CFP.Lev.Primitive (intSubsetSums D) := by
  intro d hd
  by_contra h
  push Not at h
  have hdq : ∀ q ∈ D, d ∣ q := by
    intro q hq
    have hdivZ := h (q : ℤ) (cast_mem_intSubsetSums_of_mem hq)
      0 (zero_mem_intSubsetSums D)
    have hdivCast : (d : ℤ) ∣ (q : ℤ) := by simpa using hdivZ
    exact_mod_cast hdivCast
  have hdgcd : d ∣ D.gcd id := Finset.dvd_gcd_iff.mpr hdq
  rw [hgcd] at hdgcd
  have hdle : d ≤ 1 := Nat.le_of_dvd (by decide) hdgcd
  omega

/-- No prime divides every member of `D`. -/
def NoCommonPrimeDivisor (D : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ q ∈ D, ¬p ∣ q

lemma gcd_eq_one_of_noCommonPrimeDivisor {D : Finset ℕ}
    (hD : NoCommonPrimeDivisor D) : D.gcd id = 1 := by
  by_contra hgcd
  obtain ⟨p, hp, hpgcd⟩ := Nat.exists_prime_and_dvd hgcd
  obtain ⟨q, hq, hpq⟩ := hD p hp
  exact hpq (hpgcd.trans (Finset.gcd_dvd hq))

lemma intSubsetSums_primitive_of_noCommonPrimeDivisor {D : Finset ℕ}
    (hD : NoCommonPrimeDivisor D) :
    Erdos186.CFP.Lev.Primitive (intSubsetSums D) :=
  intSubsetSums_primitive_of_gcd_eq_one
    (gcd_eq_one_of_noCommonPrimeDivisor hD)

/-- Square values belonging to a finite root set. -/
def squareValues (roots : Finset ℕ) : Finset ℕ :=
  roots.image fun m ↦ m ^ 2

@[simp] lemma mem_squareValues {roots : Finset ℕ} {q : ℕ} :
    q ∈ squareValues roots ↔ ∃ m ∈ roots, m ^ 2 = q := by
  simp [squareValues, eq_comm]

@[simp] lemma card_squareValues (roots : Finset ℕ) :
    (squareValues roots).card = roots.card := by
  apply Finset.card_image_of_injective
  intro a b hab
  exact Nat.pow_left_injective (by decide : 2 ≠ 0) hab

lemma squareValues_are_positive_squares {roots : Finset ℕ}
    (hpos : ∀ m ∈ roots, 0 < m) :
    ∀ q ∈ squareValues roots, IsPositiveSquare q := by
  intro q hq
  obtain ⟨m, hm, rfl⟩ := mem_squareValues.mp hq
  exact ⟨m, hpos m hm, rfl⟩

/-- Squaring does not create a common prime divisor: for a prime, divisibility
of `m²` forces divisibility of `m`. -/
lemma noCommonPrimeDivisor_squareValues {roots : Finset ℕ}
    (hroots : NoCommonPrimeDivisor roots) :
    NoCommonPrimeDivisor (squareValues roots) := by
  intro p hp
  obtain ⟨m, hm, hpm⟩ := hroots p hp
  refine ⟨m ^ 2, Finset.mem_image.mpr ⟨m, hm, rfl⟩, ?_⟩
  intro hpSq
  exact hpm (hp.dvd_of_dvd_pow hpSq)

/-- Choosing one subset sum from each of pairwise disjoint natural blocks
and adding the choices still gives a subset sum of their union.  This is the
distinct-index bookkeeping needed when Lev's theorem is applied to CFP's
disjoint chunks. -/
lemma familySumset_intSubsetSums_mem_subsetSum
    {ℓ : ℕ} {D : Fin ℓ → Finset ℕ}
    (hdisj : (Set.univ : Set (Fin ℓ)).PairwiseDisjoint D)
    {z : ℤ}
    (hz : z ∈ Erdos186.CFP.Lev.familySumset
      (fun i ↦ intSubsetSums (D i))) :
    ∃ n : ℕ,
      n ∈ ((Finset.univ : Finset (Fin ℓ)).biUnion D).subsetSum ∧
      (n : ℤ) = z := by
  classical
  obtain ⟨f, hf, hsum⟩ :=
    Erdos186.CFP.Lev.mem_familySumset_iff.mp hz
  have hex : ∀ i : Fin ℓ, ∃ n : ℕ,
      n ∈ (D i).subsetSum ∧ (n : ℤ) = f i := by
    intro i
    obtain ⟨n, hn, hnf⟩ := Finset.mem_image.mp (hf i)
    exact ⟨n, hn, hnf⟩
  choose n hn hnf using hex
  have hsubsets : ∀ i : Fin ℓ, ∃ T : Finset ℕ,
      T ⊆ D i ∧ ∑ q ∈ T, q = n i := by
    intro i
    exact Finset.mem_subsetSum_iff.mp (hn i)
  choose T hTD hTsum using hsubsets
  have hTdisj : (Set.univ : Set (Fin ℓ)).PairwiseDisjoint T := by
    intro i _ j _ hij
    exact (hdisj (Set.mem_univ i) (Set.mem_univ j) hij).mono (hTD i) (hTD j)
  have hTdisjFinset :
      ((↑(Finset.univ : Finset (Fin ℓ))) : Set (Fin ℓ)).PairwiseDisjoint T := by
    simpa using hTdisj
  let U : Finset ℕ := (Finset.univ : Finset (Fin ℓ)).biUnion T
  have hUsub : U ⊆ (Finset.univ : Finset (Fin ℓ)).biUnion D := by
    intro q hq
    obtain ⟨i, _, hqi⟩ := Finset.mem_biUnion.mp hq
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hTD i hqi⟩
  have hUsum : ∑ q ∈ U, q = ∑ i, n i := by
    rw [show U = (Finset.univ : Finset (Fin ℓ)).biUnion T by rfl,
      Finset.sum_biUnion hTdisjFinset]
    apply Finset.sum_congr rfl
    intro i _
    exact hTsum i
  refine ⟨∑ i, n i, Finset.mem_subsetSum_iff.mpr ⟨U, hUsub, hUsum⟩, ?_⟩
  rw [Nat.cast_sum]
  calc
    ∑ i, (n i : ℤ) = ∑ i, f i := by
      apply Finset.sum_congr rfl
      intro i _
      exact hnf i
    _ = z := hsum

/-- Natural-number form of Lev's interval theorem for pairwise disjoint
blocks.  All hypotheses concern the integer subset-sum sets of the blocks;
the conclusion is an interval of genuine distinct natural subset sums of
their union. -/
lemma exists_cover_of_lev_chunks
    {ℓ q n : ℕ} (hℓ : 1 ≤ ℓ) (hq : 1 ≤ q) (hn : 3 ≤ n)
    (hlarge : 2 * ((q - 1 + (n - 2) - 1) / (n - 2)) ≤ ℓ)
    (D : Fin ℓ → Finset ℕ)
    (hdisj : (Set.univ : Set (Fin ℓ)).PairwiseDisjoint D)
    (hcard : ∀ i, n ≤ (intSubsetSums (D i)).card)
    (hbound : ∀ i, ∃ a : ℤ,
      intSubsetSums (D i) ⊆ Finset.Icc a (a + q))
    (hprim : ∀ i, Erdos186.CFP.Lev.Primitive (intSubsetSums (D i))) :
    ∃ a : ℕ, Covers ((Finset.univ : Finset (Fin ℓ)).biUnion D)
      a (a + ℓ * (n - 1)) := by
  obtain ⟨a, ha⟩ := Erdos186.CFP.Lev.lev_interval
    hℓ hq hn hlarge (fun i ↦ intSubsetSums (D i)) hcard hbound hprim
  have haa : a ∈ Finset.Icc a (a + (ℓ * (n - 1) : ℕ)) := by
    apply Finset.mem_Icc.mpr
    constructor
    · exact le_rfl
    · have hnonneg : (0 : ℤ) ≤ (ℓ * (n - 1) : ℕ) := Int.natCast_nonneg _
      omega
  obtain ⟨aNat, _, haNat⟩ :=
    familySumset_intSubsetSums_mem_subsetSum hdisj (ha haa)
  have ha_nonneg : 0 ≤ a := by
    rw [← haNat]
    exact Int.natCast_nonneg aNat
  have hcastA : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha_nonneg
  refine ⟨a.toNat, ?_⟩
  intro x hxlow hxhigh
  have hxlowZ : a ≤ (x : ℤ) := by
    rw [← hcastA]
    exact_mod_cast hxlow
  have hxhighZ : (x : ℤ) ≤ a + (ℓ * (n - 1) : ℕ) := by
    rw [← hcastA]
    exact_mod_cast hxhigh
  have hxI : (x : ℤ) ∈ Finset.Icc a (a + (ℓ * (n - 1) : ℕ)) :=
    Finset.mem_Icc.mpr ⟨hxlowZ, hxhighZ⟩
  obtain ⟨y, hy, hyx⟩ :=
    familySumset_intSubsetSums_mem_subsetSum hdisj (ha hxI)
  have hyEq : y = x := by exact_mod_cast hyx
  simpa [hyEq] using hy

/-! ## Quadratic finite differences -/

/-- The first finite difference of the square polynomial, over the integers
so that later signed sumsets and modular reductions require no truncation
side conditions. -/
def squareDelta (h t : ℤ) : ℤ :=
  (t + h) ^ 2 - t ^ 2

@[simp] lemma squareDelta_eq (h t : ℤ) :
    squareDelta h t = 2 * h * t + h ^ 2 := by
  simp only [squareDelta]
  ring

/-- A second finite difference of `t ↦ t²` is the constant `2hg`. -/
lemma squareDelta_second (h g t : ℤ) :
    squareDelta h (t + g) - squareDelta h t = 2 * h * g := by
  simp only [squareDelta_eq]
  ring

/-- The natural square difference used when a pair of positive square
summands is replaced by its gap. -/
lemma nat_square_sub_square {a b : ℕ} (_hab : a ≤ b) :
    b ^ 2 - a ^ 2 = (b - a) * (b + a) := by
  simpa [mul_comm] using Nat.sq_sub_sq b a

/-! ## Equal-gap configurations in dense blocks of odd roots -/

/-- The three odd roots in group `j` of a block with `G` groups.  All roots
lie between `6G+1` and `12G-1`, and consecutive groups are six apart. -/
def tripleRoot (G : ℕ) (j : Fin G) (r : Fin 3) : ℕ :=
  6 * G + 1 + 6 * j + 2 * r

/-- The roots selected from one three-element group. -/
def tripleFiber {G : ℕ} (V : Finset (Fin G × Fin 3)) (j : Fin G) :
    Finset (Fin 3) :=
  Finset.univ.filter fun r ↦ (j, r) ∈ V

/-- Groups in which at least two of the three roots were selected. -/
def richTripleGroups {G : ℕ} (V : Finset (Fin G × Fin 3)) : Finset (Fin G) :=
  Finset.univ.filter fun j ↦ 2 ≤ (tripleFiber V j).card

/-- The three possible pairs among positions `0,1,2`. -/
def pairLow : Fin 3 → Fin 3
  | 0 => 0
  | 1 => 1
  | 2 => 0

def pairHigh : Fin 3 → Fin 3
  | 0 => 1
  | 1 => 2
  | 2 => 2

/-- Groups containing both endpoints of the indicated pair type. -/
def pairGroups {G : ℕ} (V : Finset (Fin G × Fin 3)) (t : Fin 3) :
    Finset (Fin G) :=
  Finset.univ.filter fun j ↦
    (j, pairLow t) ∈ V ∧ (j, pairHigh t) ∈ V

lemma card_eq_sum_tripleFiber {G : ℕ} (V : Finset (Fin G × Fin 3)) :
    V.card = ∑ j : Fin G, (tripleFiber V j).card := by
  have hfiber : ∀ j : Fin G,
      (tripleFiber V j).card =
        (V.filter fun p : Fin G × Fin 3 ↦ p.1 = j).card := by
    intro j
    refine Finset.card_bij (fun r _ ↦ (j, r)) ?_ ?_ ?_
    · intro r hr
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hr).2, rfl⟩
    · intro r₁ _ r₂ _ h
      exact congrArg Prod.snd h
    · intro p hp
      have hp' := Finset.mem_filter.mp hp
      refine ⟨p.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · rw [show (j, p.2) = p by
          apply Prod.ext
          · exact hp'.2.symm
          · rfl]
        exact hp'.1
      · apply Prod.ext
        · exact hp'.2.symm
        · rfl
  symm
  simp_rw [hfiber]
  simpa using
    (Finset.sum_card_fiberwise_eq_card_filter V
      (Finset.univ : Finset (Fin G)) Prod.fst)

lemma tripleFiber_card_le_three {G : ℕ} (V : Finset (Fin G × Fin 3))
    (j : Fin G) : (tripleFiber V j).card ≤ 3 := by
  simpa [tripleFiber] using Finset.card_filter_le
    (Finset.univ : Finset (Fin 3)) (fun r ↦ (j, r) ∈ V)

/-- A set occupying more than one position per group has linearly many
groups in which two positions are occupied. -/
lemma card_le_groups_add_twice_rich {G : ℕ}
    (V : Finset (Fin G × Fin 3)) :
    V.card ≤ G + 2 * (richTripleGroups V).card := by
  rw [card_eq_sum_tripleFiber]
  calc
    ∑ j : Fin G, (tripleFiber V j).card ≤
        ∑ j : Fin G, (1 + if 2 ≤ (tripleFiber V j).card then 2 else 0) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : 2 ≤ (tripleFiber V j).card
      · simp only [hj, if_true]
        exact tripleFiber_card_le_three V j
      · simp only [hj, if_false]
        omega
    _ = G + 2 * (richTripleGroups V).card := by
      have hbool :
          (∑ j : Fin G, (if 2 ≤ (tripleFiber V j).card then 2 else 0)) =
            2 * (richTripleGroups V).card := by
        calc
          ∑ j : Fin G, (if 2 ≤ (tripleFiber V j).card then 2 else 0) =
              ∑ j ∈ richTripleGroups V, 2 := by
            rw [← Finset.sum_filter]
            rfl
          _ = 2 * (richTripleGroups V).card := by simp [mul_comm]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Nat.nsmul_eq_mul]
      rw [hbool]
      omega

lemma richTripleGroups_subset_pair_union {G : ℕ}
    (V : Finset (Fin G × Fin 3)) :
    richTripleGroups V ⊆
      pairGroups V 0 ∪ pairGroups V 1 ∪ pairGroups V 2 := by
  intro j hj
  have hj2 : 2 ≤ (tripleFiber V j).card :=
    (Finset.mem_filter.mp hj).2
  by_cases h0 : (j, (0 : Fin 3)) ∈ V
  · by_cases h1 : (j, (1 : Fin 3)) ∈ V
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_union.mpr
      left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa [pairLow, pairHigh] using And.intro h0 h1⟩
    · by_cases h2 : (j, (2 : Fin 3)) ∈ V
      · apply Finset.mem_union.mpr
        right
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          simpa [pairLow, pairHigh] using And.intro h0 h2⟩
      · have hfiber : tripleFiber V j = {0} := by
          ext r
          fin_cases r <;> simp [tripleFiber, h0, h1, h2]
        simp [hfiber] at hj2
  · by_cases h1 : (j, (1 : Fin 3)) ∈ V
    · by_cases h2 : (j, (2 : Fin 3)) ∈ V
      · apply Finset.mem_union.mpr
        left
        apply Finset.mem_union.mpr
        right
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          simpa [pairLow, pairHigh] using And.intro h1 h2⟩
      · have hfiber : tripleFiber V j = {1} := by
          ext r
          fin_cases r <;> simp [tripleFiber, h0, h1, h2]
        simp [hfiber] at hj2
    · by_cases h2 : (j, (2 : Fin 3)) ∈ V
      · have hfiber : tripleFiber V j = {2} := by
          ext r
          fin_cases r <;> simp [tripleFiber, h0, h1, h2]
        simp [hfiber] at hj2
      · have hfiber : tripleFiber V j = ∅ := by
          ext r
          fin_cases r <;> simp [tripleFiber, h0, h1, h2]
        simp [hfiber] at hj2

/-- If `V` contains at least `5G/4` of the `3G` indexed roots, one of the
three equal-gap pair types occurs in at least `G/24` groups. -/
lemma exists_many_pairGroups {G : ℕ} {V : Finset (Fin G × Fin 3)}
    (hdense : 5 * G ≤ 4 * V.card) :
    ∃ t : Fin 3, G ≤ 24 * (pairGroups V t).card := by
  have hrichCard : (richTripleGroups V).card ≤
      (pairGroups V 0).card + (pairGroups V 1).card +
        (pairGroups V 2).card := by
    calc
      (richTripleGroups V).card ≤
          (pairGroups V 0 ∪ pairGroups V 1 ∪ pairGroups V 2).card :=
        Finset.card_le_card (richTripleGroups_subset_pair_union V)
      _ ≤ (pairGroups V 0).card + (pairGroups V 1).card +
          (pairGroups V 2).card := by
        have h01 := Finset.card_union_le (pairGroups V 0) (pairGroups V 1)
        have h012 := Finset.card_union_le
          (pairGroups V 0 ∪ pairGroups V 1) (pairGroups V 2)
        omega
  have hG : G ≤ 8 * ((pairGroups V 0).card + (pairGroups V 1).card +
      (pairGroups V 2).card) := by
    have hvr := card_le_groups_add_twice_rich V
    omega
  by_cases h0 : G ≤ 24 * (pairGroups V 0).card
  · exact ⟨0, h0⟩
  by_cases h1 : G ≤ 24 * (pairGroups V 1).card
  · exact ⟨1, h1⟩
  refine ⟨2, ?_⟩
  omega

/-- Lower root and root gap of one of the three pair types. -/
def pairBase (G : ℕ) (t : Fin 3) (j : Fin G) : ℕ :=
  tripleRoot G j (pairLow t)

def pairGap : Fin 3 → ℕ
  | 0 => 2
  | 1 => 2
  | 2 => 4

lemma tripleRoot_pairHigh (G : ℕ) (t : Fin 3) (j : Fin G) :
    tripleRoot G j (pairHigh t) = pairBase G t j + pairGap t := by
  fin_cases t <;> simp [tripleRoot, pairBase, pairLow, pairHigh, pairGap]

lemma pairGap_pos (t : Fin 3) : 0 < pairGap t := by
  fin_cases t <;> simp [pairGap]

lemma pairGap_le_four (t : Fin 3) : pairGap t ≤ 4 := by
  fin_cases t <;> simp [pairGap]

lemma pairBase_lower {G : ℕ} (t : Fin 3) (j : Fin G) :
    6 * G + 1 ≤ pairBase G t j := by
  fin_cases t <;> simp [pairBase, tripleRoot, pairLow]
  all_goals omega

lemma pairBase_upper {G : ℕ} (t : Fin 3) (j : Fin G) :
    pairBase G t j < 2 * (6 * G + 1) := by
  have hj := j.isLt
  fin_cases t <;> simp [pairBase, tripleRoot, pairLow] <;> omega

/-- The integer encoded by a pair of equal-gap configurations.  The first
coordinate supplies a square and the second supplies a difference of two
squares. -/
def pairCode (G : ℕ) (t : Fin 3) (p : Fin G × Fin G) : ℕ :=
  (pairBase G t p.1) ^ 2 +
    2 * pairGap t * pairBase G t p.2 + (pairGap t) ^ 2

/-- Lexicographic domination for squares: changing the first group changes
the quadratic term by more than the full possible variation of the linear
second term. -/
lemma pairCode_injective (G : ℕ) (t : Fin 3) :
    Function.Injective (pairCode G t) := by
  rintro ⟨j, k⟩ ⟨j', k'⟩ h
  have hjG := j.isLt
  have hjG' := j'.isLt
  have hkG := k.isLt
  have hkG' := k'.isLt
  have hj : j.val = j'.val := by
    rcases lt_trichotomy j.val j'.val with hjj | hjj | hjj
    · fin_cases t <;>
        simp only [pairCode, pairBase, tripleRoot, pairLow, pairGap] at h <;>
          nlinarith
    · exact hjj
    · fin_cases t <;>
        simp only [pairCode, pairBase, tripleRoot, pairLow, pairGap] at h <;>
          nlinarith
  have hjFin : j = j' := Fin.ext hj
  subst j'
  have hk : k.val = k'.val := by
    fin_cases t <;>
      simp only [pairCode, pairBase, tripleRoot, pairLow, pairGap] at h <;>
        nlinarith
  exact Prod.ext rfl (Fin.ext hk)

/-- The positive and negative square shifts arising from indexed roots. -/
def signedRootSquares {G : ℕ} (V : Finset (Fin G × Fin 3)) : Finset ℤ :=
  (V.image fun p ↦ (tripleRoot G p.1 p.2 : ℤ) ^ 2) ∪
    (V.image fun p ↦ -((tripleRoot G p.1 p.2 : ℤ) ^ 2))

lemma pos_square_mem_signedRootSquares {G : ℕ} {V : Finset (Fin G × Fin 3)}
    {p : Fin G × Fin 3} (hp : p ∈ V) :
    (tripleRoot G p.1 p.2 : ℤ) ^ 2 ∈ signedRootSquares V := by
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)

lemma neg_square_mem_signedRootSquares {G : ℕ} {V : Finset (Fin G × Fin 3)}
    {p : Fin G × Fin 3} (hp : p ∈ V) :
    -((tripleRoot G p.1 p.2 : ℤ) ^ 2) ∈ signedRootSquares V := by
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)

/-- Every `pairCode` from two groups of the same occupied pair type is a
three-fold sum of signed selected squares. -/
lemma pairCode_mem_multifoldSumset {G : ℕ} {V : Finset (Fin G × Fin 3)}
    {t : Fin 3} {j k : Fin G}
    (hj : j ∈ pairGroups V t) (hk : k ∈ pairGroups V t) :
    (pairCode G t (j, k) : ℤ) ∈
      Erdos186.CFP.GrowthLemmas.multifoldSumset 3 (signedRootSquares V) := by
  have hj' := (Finset.mem_filter.mp hj).2
  have hk' := (Finset.mem_filter.mp hk).2
  apply Erdos186.CFP.GrowthLemmas.mem_multifoldSumset_iff.mpr
  let f : Fin 3 → ℤ := fun i ↦
    if i = 0 then (tripleRoot G j (pairLow t) : ℤ) ^ 2
    else if i = 1 then (tripleRoot G k (pairHigh t) : ℤ) ^ 2
    else -((tripleRoot G k (pairLow t) : ℤ) ^ 2)
  refine ⟨f, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact pos_square_mem_signedRootSquares hj'.1
    · exact pos_square_mem_signedRootSquares hk'.2
    · exact neg_square_mem_signedRootSquares hk'.1
  · rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [f, Fin.isValue, ↓reduceIte, Finset.univ_eq_empty,
      Finset.sum_empty, add_zero]
    rw [tripleRoot_pairHigh]
    simp only [pairBase]
    push_cast
    simp only [pairCode]
    simp only [pairBase]
    push_cast
    ring

/-- Square-specialized PET richness.  A `5/4`-dense indexed root set has a
three-fold signed-square sumset with quadratically many elements. -/
lemma card_multifold_signedRootSquares {G : ℕ}
    {V : Finset (Fin G × Fin 3)} (hdense : 5 * G ≤ 4 * V.card) :
    (G / 24) ^ 2 ≤
      (Erdos186.CFP.GrowthLemmas.multifoldSumset 3
        (signedRootSquares V)).card := by
  obtain ⟨t, ht⟩ := exists_many_pairGroups hdense
  let P := pairGroups V t
  let codes : Finset ℤ := (P.product P).image fun p ↦ (pairCode G t p : ℤ)
  have hcodeCard : codes.card = P.card ^ 2 := by
    dsimp only [codes]
    rw [Finset.card_image_of_injective]
    · simp [pow_two]
    · exact Int.ofNat_injective.comp (pairCode_injective G t)
  have hcodesub : codes ⊆
      Erdos186.CFP.GrowthLemmas.multifoldSumset 3 (signedRootSquares V) := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    have hp' := Finset.mem_product.mp hp
    exact pairCode_mem_multifoldSumset hp'.1 hp'.2
  have hdiv : G / 24 ≤ P.card := by
    dsimp [P]
    omega
  calc
    (G / 24) ^ 2 ≤ P.card ^ 2 := Nat.pow_le_pow_left hdiv 2
    _ = codes.card := hcodeCard.symm
    _ ≤ _ := Finset.card_le_card hcodesub

/-! ## From signed-square richness to subset-sum growth -/

lemma card_differenceFiber_neg (S : Finset ℤ) (a : ℤ) :
    (Erdos186.CFP.GrowthLemmas.differenceFiber S (-a)).card =
      (Erdos186.CFP.GrowthLemmas.differenceFiber S a).card := by
  refine Finset.card_bij (fun p _ ↦ (p.2, p.1)) ?_ ?_ ?_
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · have hprod := Finset.mem_product.mp hp'.1
      exact Finset.mem_product.mpr ⟨hprod.2, hprod.1⟩
    · dsimp
      omega
  · intro p _ q _ hpq
    exact Prod.ext (congrArg Prod.snd hpq) (congrArg Prod.fst hpq)
  · intro p hp
    refine ⟨(p.2, p.1), ?_, rfl⟩
    have hp' := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · have hprod := Finset.mem_product.mp hp'.1
      exact Finset.mem_product.mpr ⟨hprod.2, hprod.1⟩
    · dsimp
      omega

lemma card_boundary_neg (S : Finset ℤ) (a : ℤ) :
    (Erdos186.CFP.GrowthLemmas.boundary S (-a)).card =
      (Erdos186.CFP.GrowthLemmas.boundary S a).card := by
  have hneg :=
    Erdos186.CFP.GrowthLemmas.card_boundary_add_card_differenceFiber S (-a)
  have hpos :=
    Erdos186.CFP.GrowthLemmas.card_boundary_add_card_differenceFiber S a
  rw [card_differenceFiber_neg] at hneg
  omega

lemma intSubsetSums_mono {D E : Finset ℕ} (hDE : D ⊆ E) :
    intSubsetSums D ⊆ intSubsetSums E := by
  intro z hz
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
  exact Finset.mem_image.mpr ⟨n, Finset.subsetSum_mono hDE hn, rfl⟩

lemma translate_intSubsetSums_subset_insert {D : Finset ℕ} {q : ℕ}
    (hq : q ∉ D) :
    Erdos186.CFP.GrowthLemmas.translate (q : ℤ) (intSubsetSums D) ⊆
      intSubsetSums (insert q D) := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ :=
    Erdos186.CFP.GrowthLemmas.mem_translate_iff.mp hz
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨T, hTD, rfl⟩ := Finset.mem_subsetSum_iff.mp hn
  apply Finset.mem_image.mpr
  refine ⟨q + ∑ x ∈ T, x, ?_, by norm_cast⟩
  apply Finset.mem_subsetSum_iff.mpr
  refine ⟨insert q T, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hTD hx)
  · have hqT : q ∉ T := fun h ↦ hq (hTD h)
    rw [Finset.sum_insert hqT]

/-- Adding a new natural weight gains at least the boundary of the old
integer subset-sum set under the corresponding positive shift. -/
lemma card_intSubsetSums_insert_ge {D : Finset ℕ} {q : ℕ} (hq : q ∉ D) :
    (intSubsetSums D).card +
        (Erdos186.CFP.GrowthLemmas.boundary
          (intSubsetSums D) (q : ℤ)).card ≤
      (intSubsetSums (insert q D)).card := by
  let S := intSubsetSums D
  let T := Erdos186.CFP.GrowthLemmas.translate (q : ℤ) S
  let B := Erdos186.CFP.GrowthLemmas.boundary S (q : ℤ)
  have hdisj : Disjoint S B := by
    rw [Finset.disjoint_left]
    intro z hzS hzB
    exact (Finset.mem_sdiff.mp hzB).2 hzS
  have hSB : S ∪ B = S ∪ T := by
    ext z
    simp only [Finset.mem_union]
    constructor
    · rintro (hz | hz)
      · exact Or.inl hz
      · exact Or.inr (Finset.mem_sdiff.mp hz).1
    · rintro (hz | hz)
      · exact Or.inl hz
      · by_cases hzS : z ∈ S
        · exact Or.inl hzS
        · exact Or.inr (Finset.mem_sdiff.mpr ⟨hz, hzS⟩)
  have hsub : S ∪ T ⊆ intSubsetSums (insert q D) := by
    apply Finset.union_subset
    · exact intSubsetSums_mono (Finset.subset_insert q D)
    · exact translate_intSubsetSums_subset_insert hq
  calc
    S.card + B.card = (S ∪ B).card :=
      (Finset.card_union_of_disjoint hdisj).symm
    _ = (S ∪ T).card := by rw [hSB]
    _ ≤ (intSubsetSums (insert q D)).card := Finset.card_le_card hsub

/-- If the current subset-sum set has not yet reached half the quadratic
richness threshold, some square from a dense unused indexed set expands it
by at least one sixth of its present size. -/
lemma exists_square_with_large_boundary {G : ℕ}
    {V : Finset (Fin G × Fin 3)} (hdense : 5 * G ≤ 4 * V.card)
    (S : Finset ℤ) (hS : S.Nonempty)
    (hsmall : 2 * S.card ≤ (G / 24) ^ 2) :
    ∃ p ∈ V, S.card ≤ 6 *
      (Erdos186.CFP.GrowthLemmas.boundary S
      ((tripleRoot G p.1 p.2 : ℕ) ^ 2 : ℤ)).card := by
  have hScard : 0 < S.card := Finset.card_pos.mpr hS
  have hGpos : 0 < G := by
    by_contra hG
    have hG0 : G = 0 := Nat.eq_zero_of_not_pos hG
    subst G
    change 2 * S.card ≤ 0 at hsmall
    omega
  have hA : (signedRootSquares V).Nonempty := by
    have hV : V.Nonempty := by
      by_contra h
      simp only [Finset.not_nonempty_iff_eq_empty] at h
      rw [h] at hdense
      change 5 * G ≤ 0 at hdense
      omega
    obtain ⟨p, hp⟩ := hV
    exact ⟨(tripleRoot G p.1 p.2 : ℤ) ^ 2,
      pos_square_mem_signedRootSquares hp⟩
  have hcard : 2 * S.card ≤
      (Erdos186.CFP.GrowthLemmas.multifoldSumset 3
        (signedRootSquares V)).card :=
    hsmall.trans (card_multifold_signedRootSquares hdense)
  obtain ⟨a, ha, hboundary⟩ :=
    Erdos186.CFP.GrowthLemmas.exists_large_boundary_of_two_mul_card_le_multifoldSumset
      S (signedRootSquares V) 3 hS hA hcard
  rw [signedRootSquares, Finset.mem_union] at ha
  rcases ha with ha | ha
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨p, hp, by simpa using hboundary⟩
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    refine ⟨p, hp, ?_⟩
    rw [card_boundary_neg] at hboundary
    simpa using hboundary

/-! ## Greedy construction of one quadratically rich chunk -/

/-- Square values attached to a finite set of triple indices. -/
def indexedSquareValues {G : ℕ} (U : Finset (Fin G × Fin 3)) : Finset ℕ :=
  U.image fun p ↦ (tripleRoot G p.1 p.2) ^ 2

lemma tripleRoot_injective (G : ℕ) :
    Function.Injective (fun p : Fin G × Fin 3 ↦ tripleRoot G p.1 p.2) := by
  rintro ⟨j, r⟩ ⟨j', r'⟩ h
  have hr := r.isLt
  have hr' := r'.isLt
  simp only [tripleRoot] at h
  have hj : j.val = j'.val := by omega
  have hrv : r.val = r'.val := by omega
  exact Prod.ext (Fin.ext hj) (Fin.ext hrv)

lemma tripleRoot_lower {G : ℕ} (p : Fin G × Fin 3) :
    6 * G + 1 ≤ tripleRoot G p.1 p.2 := by
  simp only [tripleRoot]
  omega

lemma tripleRoot_upper {G : ℕ} (p : Fin G × Fin 3) :
    tripleRoot G p.1 p.2 < 2 * (6 * G + 1) := by
  have hj := p.1.isLt
  have hr := p.2.isLt
  simp only [tripleRoot]
  omega

lemma indexedSquareValues_injective (G : ℕ) :
    Function.Injective
      (fun p : Fin G × Fin 3 ↦ (tripleRoot G p.1 p.2) ^ 2) :=
  (Nat.pow_left_injective (by decide : 2 ≠ 0)).comp (tripleRoot_injective G)

@[simp] lemma card_indexedSquareValues {G : ℕ}
    (U : Finset (Fin G × Fin 3)) :
    (indexedSquareValues U).card = U.card := by
  exact Finset.card_image_of_injective U (indexedSquareValues_injective G)

lemma indexedSquareValues_mono {G : ℕ} {U W : Finset (Fin G × Fin 3)}
    (hUW : U ⊆ W) : indexedSquareValues U ⊆ indexedSquareValues W := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  exact Finset.mem_image.mpr ⟨p, hUW hp, rfl⟩

lemma indexedSquareValues_are_positive_squares {G : ℕ}
    {U : Finset (Fin G × Fin 3)} {q : ℕ}
    (hq : q ∈ indexedSquareValues U) : IsPositiveSquare q := by
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hq
  refine ⟨tripleRoot G p.1 p.2, ?_, rfl⟩
  have hlow := tripleRoot_lower p
  omega

lemma indexedSquareValues_filter_mem_eq {G : ℕ} (D : Finset ℕ)
    (hD : D ⊆ indexedSquareValues
      (Finset.univ : Finset (Fin G × Fin 3))) :
    indexedSquareValues
        ((Finset.univ : Finset (Fin G × Fin 3)).filter fun p ↦
          (tripleRoot G p.1 p.2) ^ 2 ∈ D) = D := by
  ext q
  constructor
  · intro hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact (Finset.mem_filter.mp hp).2
  · intro hq
    obtain ⟨p, _, hpq⟩ := Finset.mem_image.mp (hD hq)
    refine Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr
      ⟨Finset.mem_univ p, ?_⟩, hpq⟩
    rw [hpq]
    exact hq

@[simp] lemma indexedSquareValues_insert {G : ℕ}
    (p : Fin G × Fin 3) (U : Finset (Fin G × Fin 3)) :
    indexedSquareValues (insert p U) =
      insert ((tripleRoot G p.1 p.2) ^ 2) (indexedSquareValues U) := by
  simp [indexedSquareValues]

lemma square_not_mem_indexedSquareValues {G : ℕ}
    {p : Fin G × Fin 3} {U : Finset (Fin G × Fin 3)} (hp : p ∉ U) :
    (tripleRoot G p.1 p.2) ^ 2 ∉ indexedSquareValues U := by
  intro h
  obtain ⟨p', hp', heq⟩ := Finset.mem_image.mp h
  have hpp : p' = p := indexedSquareValues_injective G heq
  rw [hpp] at hp'
  exact hp hp'

/-- One greedy step.  While the target has not been reached, a new indexed
square can be adjoined so that the subset-sum cardinality grows by a factor
of at least `7/6`. -/
lemma exists_one_index_growth {G : ℕ}
    {D U : Finset (Fin G × Fin 3)}
    (hUD : U ⊆ D) (hremaining : 5 * G + 4 * U.card ≤ 4 * D.card)
    (hsmall : 2 * (intSubsetSums (indexedSquareValues U)).card ≤
      (G / 24) ^ 2) :
    ∃ p ∈ D \ U,
      7 * (intSubsetSums (indexedSquareValues U)).card ≤
        6 * (intSubsetSums (indexedSquareValues (insert p U))).card := by
  let V := D \ U
  have hVcard : V.card = D.card - U.card := by
    exact Finset.card_sdiff_of_subset hUD
  have hVdense : 5 * G ≤ 4 * V.card := by
    rw [hVcard]
    omega
  let S := intSubsetSums (indexedSquareValues U)
  have hS : S.Nonempty := ⟨0, zero_mem_intSubsetSums _⟩
  obtain ⟨p, hpV, hpBoundary⟩ :=
    exists_square_with_large_boundary hVdense S hS hsmall
  have hpU : p ∉ U := (Finset.mem_sdiff.mp hpV).2
  let q := (tripleRoot G p.1 p.2) ^ 2
  have hqU : q ∉ indexedSquareValues U :=
    square_not_mem_indexedSquareValues hpU
  have hcardGrow := card_intSubsetSums_insert_ge hqU
  rw [← indexedSquareValues_insert] at hcardGrow
  refine ⟨p, hpV, ?_⟩
  change 7 * S.card ≤
    6 * (intSubsetSums (indexedSquareValues (insert p U))).card
  change S.card ≤ 6 *
    (Erdos186.CFP.GrowthLemmas.boundary S (q : ℤ)).card at hpBoundary
  change S.card +
      (Erdos186.CFP.GrowthLemmas.boundary S (q : ℤ)).card ≤
    (intSubsetSums (indexedSquareValues (insert p U))).card at hcardGrow
  omega

/-- Iterate the one-step construction a prescribed number of times.  Either
the quadratic target is crossed, or the accumulated `7/6` gains give the
displayed division-free lower bound. -/
lemma exists_steps_index_growth {G steps : ℕ}
    {D U : Finset (Fin G × Fin 3)}
    (hUD : U ⊆ D)
    (hbudget : 5 * G + 4 * (U.card + steps) ≤ 4 * D.card) :
    ∃ W : Finset (Fin G × Fin 3),
      U ⊆ W ∧ W ⊆ D ∧ W.card ≤ U.card + steps ∧
      ((G / 24) ^ 2 <
          2 * (intSubsetSums (indexedSquareValues W)).card ∨
        (6 + steps) * (intSubsetSums (indexedSquareValues U)).card ≤
          6 * (intSubsetSums (indexedSquareValues W)).card) := by
  induction steps with
  | zero =>
      refine ⟨U, Finset.Subset.rfl, hUD, by simp, Or.inr ?_⟩
      simp
  | succ steps ih =>
      have hbudget' : 5 * G + 4 * (U.card + steps) ≤ 4 * D.card := by omega
      obtain ⟨W, hUW, hWD, hWcard, htarget | hgrow⟩ := ih hbudget'
      · exact ⟨W, hUW, hWD, by omega, Or.inl htarget⟩
      · by_cases htarget : (G / 24) ^ 2 <
            2 * (intSubsetSums (indexedSquareValues W)).card
        · exact ⟨W, hUW, hWD, by omega, Or.inl htarget⟩
        · have hsmall :
            2 * (intSubsetSums (indexedSquareValues W)).card ≤
              (G / 24) ^ 2 := Nat.le_of_not_gt htarget
          have hWbudget : 5 * G + 4 * W.card ≤ 4 * D.card := by omega
          obtain ⟨p, hp, hpGrow⟩ :=
            exists_one_index_growth hWD hWbudget hsmall
          let W' := insert p W
          have hpW : p ∉ W := (Finset.mem_sdiff.mp hp).2
          have hWW' : W ⊆ W' := Finset.subset_insert p W
          have hW'D : W' ⊆ D := by
            intro x hx
            rw [Finset.mem_insert] at hx
            rcases hx with rfl | hx
            · exact (Finset.mem_sdiff.mp hp).1
            · exact hWD hx
          have hbaseMono :
            (intSubsetSums (indexedSquareValues U)).card ≤
              (intSubsetSums (indexedSquareValues W)).card :=
            Finset.card_le_card (intSubsetSums_mono
              (indexedSquareValues_mono hUW))
          refine ⟨W', hUW.trans hWW', hW'D, ?_, Or.inr ?_⟩
          · simp only [W', Finset.card_insert_of_notMem hpW]
            omega
          · change (6 + steps.succ) *
              (intSubsetSums (indexedSquareValues U)).card ≤
              6 * (intSubsetSums (indexedSquareValues W')).card
            change 7 * (intSubsetSums (indexedSquareValues W)).card ≤
              6 * (intSubsetSums (indexedSquareValues W')).card at hpGrow
            calc
              (6 + steps.succ) *
                    (intSubsetSums (indexedSquareValues U)).card =
                  (6 + steps) *
                      (intSubsetSums (indexedSquareValues U)).card +
                    (intSubsetSums (indexedSquareValues U)).card := by
                simp only [Nat.succ_eq_add_one]
                ring
              _ ≤ 6 * (intSubsetSums (indexedSquareValues W)).card +
                    (intSubsetSums (indexedSquareValues W)).card :=
                Nat.add_le_add hgrow hbaseMono
              _ = 7 * (intSubsetSums (indexedSquareValues W)).card := by ring
              _ ≤ 6 * (intSubsetSums (indexedSquareValues W')).card := hpGrow

/-- Repeating six greedy insertions doubles the subset-sum cardinality unless
the quadratic target has already been crossed. -/
lemma exists_rounds_index_growth {G rounds : ℕ}
    {D : Finset (Fin G × Fin 3)}
    (hbudget : 5 * G + 24 * rounds ≤ 4 * D.card) :
    ∃ U : Finset (Fin G × Fin 3),
      U ⊆ D ∧ U.card ≤ 6 * rounds ∧
      ((G / 24) ^ 2 <
          2 * (intSubsetSums (indexedSquareValues U)).card ∨
        2 ^ rounds ≤ (intSubsetSums (indexedSquareValues U)).card) := by
  induction rounds with
  | zero =>
      refine ⟨∅, Finset.empty_subset _, by simp, Or.inr ?_⟩
      simp [indexedSquareValues, intSubsetSums]
  | succ rounds ih =>
      have hbudget' : 5 * G + 24 * rounds ≤ 4 * D.card := by omega
      obtain ⟨U, hUD, hUcard, htarget | hpow⟩ := ih hbudget'
      · exact ⟨U, hUD, by omega, Or.inl htarget⟩
      · have hsixBudget :
            5 * G + 4 * (U.card + 6) ≤ 4 * D.card := by omega
        obtain ⟨W, hUW, hWD, hWcard, htarget | hdouble⟩ :=
          exists_steps_index_growth hUD hsixBudget
        · exact ⟨W, hWD, by omega, Or.inl htarget⟩
        · refine ⟨W, hWD, by omega, Or.inr ?_⟩
          have htwice : 2 *
              (intSubsetSums (indexedSquareValues U)).card ≤
                (intSubsetSums (indexedSquareValues W)).card := by
            have hdouble' : 6 * (2 *
                (intSubsetSums (indexedSquareValues U)).card) ≤
                  6 * (intSubsetSums (indexedSquareValues W)).card := by
              calc
                6 * (2 * (intSubsetSums (indexedSquareValues U)).card) =
                    (6 + 6) *
                      (intSubsetSums (indexedSquareValues U)).card := by ring
                _ ≤ _ := hdouble
            exact Nat.le_of_mul_le_mul_left hdouble' (by norm_num)
          rw [pow_succ]
          simpa [mul_comm] using
            (Nat.mul_le_mul_left 2 hpow).trans htwice

/-- A concrete raw rich chunk inside every half-dense indexed block.  The scale
`G = 24·2^H` makes the power-growth calculation exact. -/
lemma exists_raw_rich_index_chunk (H : ℕ)
    {D : Finset (Fin (24 * 2 ^ H) × Fin 3)}
    (hD : 5 * (24 * 2 ^ H) + 48 * H ≤ 4 * D.card) :
    ∃ U : Finset (Fin (24 * 2 ^ H) × Fin 3),
      U ⊆ D ∧ U.card ≤ 12 * H ∧
      (2 ^ H) ^ 2 <
        2 * (intSubsetSums (indexedSquareValues U)).card := by
  let G := 24 * 2 ^ H
  have hbudget : 5 * G + 24 * (2 * H) ≤ 4 * D.card := by
    dsimp [G]
    omega
  obtain ⟨U, hUD, hUcard, htarget | hpow⟩ :=
    exists_rounds_index_growth hbudget
  · refine ⟨U, hUD, by omega, ?_⟩
    simpa [G] using htarget
  · refine ⟨U, hUD, by omega, ?_⟩
    have hsq : (2 ^ H) ^ 2 = 2 ^ (2 * H) := by
      rw [pow_two, ← pow_add]
      congr 1
      omega
    rw [hsq]
    have hpow' : 2 ^ (2 * H) ≤
        (intSubsetSums (indexedSquareValues U)).card := by
      exact hpow
    have hpos : 0 < (intSubsetSums (indexedSquareValues U)).card :=
      Finset.card_pos.mpr ⟨0, zero_mem_intSubsetSums _⟩
    omega

lemma pairRoots_coprime (G : ℕ) (t : Fin 3) (j : Fin G) :
    (tripleRoot G j (pairLow t)).Coprime
      (tripleRoot G j (pairHigh t)) := by
  rw [tripleRoot_pairHigh]
  change (pairBase G t j).Coprime (pairBase G t j + pairGap t)
  rw [Nat.coprime_self_add_right]
  fin_cases t
  · simp only [pairGap, pairBase, pairLow]
    rw [Nat.coprime_two_right]
    refine ⟨3 * G + 3 * j, ?_⟩
    simp [tripleRoot]
    ring
  · simp only [pairGap, pairBase, pairLow]
    rw [Nat.coprime_two_right]
    refine ⟨3 * G + 3 * j + 1, ?_⟩
    simp [tripleRoot]
    ring
  · simp only [pairGap, pairBase, pairLow]
    have hodd : Odd (tripleRoot G j 0) := by
      refine ⟨3 * G + 3 * j, ?_⟩
      simp [tripleRoot]
      ring
    have htwo : (tripleRoot G j 0).Coprime 2 :=
      Nat.coprime_two_right.mpr hodd
    simpa using htwo.pow 1 2

/-- A dense indexed block contains two selected roots whose values are
coprime; they are two odd roots at distance two or four in one triple. -/
lemma exists_coprime_pair_in_dense {G : ℕ}
    {D : Finset (Fin G × Fin 3)} (hG : 0 < G)
    (hdense : 5 * G ≤ 4 * D.card) :
    ∃ a b : Fin G × Fin 3,
      a ∈ D ∧ b ∈ D ∧
      (tripleRoot G a.1 a.2).Coprime (tripleRoot G b.1 b.2) := by
  obtain ⟨t, ht⟩ := exists_many_pairGroups hdense
  have hP : (pairGroups D t).Nonempty := by
    exact Finset.card_pos.mp (by omega)
  obtain ⟨j, hj⟩ := hP
  have hj' := (Finset.mem_filter.mp hj).2
  exact ⟨(j, pairLow t), (j, pairHigh t), hj'.1, hj'.2,
    pairRoots_coprime G t j⟩

/-- A rich chunk augmented by a coprime pair.  Hence its square values have
gcd one, which is exactly the primitivity hypothesis required by Lev. -/
lemma exists_rich_index_chunk (H : ℕ)
    {D : Finset (Fin (24 * 2 ^ H) × Fin 3)}
    (hD : 5 * (24 * 2 ^ H) + 48 * H ≤ 4 * D.card) :
    ∃ W : Finset (Fin (24 * 2 ^ H) × Fin 3),
      W ⊆ D ∧ W.card ≤ 12 * H + 2 ∧
      (2 ^ H) ^ 2 <
        2 * (intSubsetSums (indexedSquareValues W)).card ∧
      (indexedSquareValues W).gcd id = 1 := by
  obtain ⟨U, hUD, hUcard, hUrich⟩ := exists_raw_rich_index_chunk H hD
  have hG : 0 < 24 * 2 ^ H := by positivity
  have hdense : 5 * (24 * 2 ^ H) ≤ 4 * D.card := hD.trans' (by omega)
  obtain ⟨a, b, haD, hbD, hab⟩ :=
    exists_coprime_pair_in_dense hG hdense
  let W := insert a (insert b U)
  have hUW : U ⊆ W :=
    (Finset.subset_insert b U).trans (Finset.subset_insert a (insert b U))
  have hWD : W ⊆ D := by
    intro p hp
    simp only [W, Finset.mem_insert] at hp
    rcases hp with rfl | rfl | hp
    · exact haD
    · exact hbD
    · exact hUD hp
  have hWcard : W.card ≤ 12 * H + 2 := by
    calc
      W.card ≤ U.card + 2 := by
        dsimp [W]
        calc
          (insert a (insert b U)).card ≤ (insert b U).card + 1 :=
            Finset.card_insert_le a (insert b U)
          _ ≤ (U.card + 1) + 1 :=
            Nat.add_le_add_right (Finset.card_insert_le b U) 1
          _ = U.card + 2 := by omega
      _ ≤ 12 * H + 2 := Nat.add_le_add_right hUcard 2
  have hUvalues : indexedSquareValues U ⊆ indexedSquareValues W :=
    indexedSquareValues_mono hUW
  have hWrich : (2 ^ H) ^ 2 <
      2 * (intSubsetSums (indexedSquareValues W)).card := by
    exact hUrich.trans_le (Nat.mul_le_mul_left 2
      (Finset.card_le_card (intSubsetSums_mono hUvalues)))
  have haW : a ∈ W := Finset.mem_insert_self _ _
  have hbW : b ∈ W :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have haSq : (tripleRoot (24 * 2 ^ H) a.1 a.2) ^ 2 ∈
      indexedSquareValues W := Finset.mem_image.mpr ⟨a, haW, rfl⟩
  have hbSq : (tripleRoot (24 * 2 ^ H) b.1 b.2) ^ 2 ∈
      indexedSquareValues W := Finset.mem_image.mpr ⟨b, hbW, rfl⟩
  let g := (indexedSquareValues W).gcd id
  have hga : g ∣ (tripleRoot (24 * 2 ^ H) a.1 a.2) ^ 2 :=
    Finset.gcd_dvd haSq
  have hgb : g ∣ (tripleRoot (24 * 2 ^ H) b.1 b.2) ^ 2 :=
    Finset.gcd_dvd hbSq
  have hg : g = 1 := Nat.eq_one_of_dvd_coprimes (hab.pow 2 2) hga hgb
  exact ⟨W, hWD, hWcard, hWrich, hg⟩

/-- Iterating the chunk construction gives a pairwise-disjoint family.  The
single inequality in the hypothesis accounts for the worst-case `12H`
indices consumed by each earlier chunk. -/
lemma exists_disjoint_rich_chunks (H L : ℕ)
    {D : Finset (Fin (24 * 2 ^ H) × Fin 3)}
    (hbudget :
      5 * (24 * 2 ^ H) + (48 * H + 8) * L ≤ 4 * D.card) :
    ∃ U : Fin L → Finset (Fin (24 * 2 ^ H) × Fin 3),
      (Set.univ : Set (Fin L)).PairwiseDisjoint U ∧
      ∀ i : Fin L,
        U i ⊆ D ∧ (U i).card ≤ 12 * H + 2 ∧
        (2 ^ H) ^ 2 <
          2 * (intSubsetSums (indexedSquareValues (U i))).card ∧
        (indexedSquareValues (U i)).gcd id = 1 := by
  induction L generalizing D with
  | zero =>
      refine ⟨Fin.elim0, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ L ih =>
      have hfirst :
          5 * (24 * 2 ^ H) + 48 * H ≤ 4 * D.card := by
        have hcoef : 48 * H ≤ 48 * H + 8 := by omega
        have hmul : 48 * H + 8 ≤ (48 * H + 8) * (L + 1) := by
          nlinarith
        omega
      obtain ⟨U0, hU0D, hU0card, hU0rich, hU0gcd⟩ :=
        exists_rich_index_chunk H hfirst
      let D' := D \ U0
      have hD'card : D'.card = D.card - U0.card := by
        exact Finset.card_sdiff_of_subset hU0D
      have hrest :
          5 * (24 * 2 ^ H) + (48 * H + 8) * L ≤ 4 * D'.card := by
        rw [hD'card]
        have hused : 4 * U0.card ≤ 48 * H + 8 := by
          calc
            4 * U0.card ≤ 4 * (12 * H + 2) :=
              Nat.mul_le_mul_left 4 hU0card
            _ = 48 * H + 8 := by ring
        have hbudget' :
            5 * (24 * 2 ^ H) +
                ((48 * H + 8) * L + (48 * H + 8)) ≤
              4 * D.card := by
          calc
            5 * (24 * 2 ^ H) +
                  ((48 * H + 8) * L + (48 * H + 8)) =
                5 * (24 * 2 ^ H) + (48 * H + 8) * (L + 1) := by ring
            _ ≤ 4 * D.card := hbudget
        omega
      obtain ⟨R, hRdisj, hR⟩ := ih hrest
      let U : Fin (L + 1) → Finset (Fin (24 * 2 ^ H) × Fin 3) :=
        Fin.cases U0 R
      refine ⟨U, ?_, ?_⟩
      · intro i _ j _ hij
        rcases Fin.eq_zero_or_eq_succ i with hi | ⟨i', hi⟩
        · subst i
          rcases Fin.eq_zero_or_eq_succ j with hj | ⟨j', hj⟩
          · subst j
            exact (hij rfl).elim
          · subst j
            change Disjoint U0 (R j')
            rw [Finset.disjoint_left]
            intro x hx0 hxR
            have hxD' : x ∈ D' := (hR j').1 hxR
            exact (Finset.mem_sdiff.mp hxD').2 hx0
        · subst i
          rcases Fin.eq_zero_or_eq_succ j with hj | ⟨j', hj⟩
          · subst j
            change Disjoint (R i') U0
            symm
            rw [Finset.disjoint_left]
            intro x hx0 hxR
            have hxD' : x ∈ D' := (hR i').1 hxR
            exact (Finset.mem_sdiff.mp hxD').2 hx0
          · subst j
            change Disjoint (R i') (R j')
            apply hRdisj (Set.mem_univ i') (Set.mem_univ j')
            intro hij'
            exact hij (congrArg Fin.succ hij')
      · intro i
        refine Fin.cases ?_ (fun i' ↦ ?_) i
        · exact ⟨hU0D, hU0card, hU0rich, hU0gcd⟩
        · have hi := hR i'
          exact ⟨hi.1.trans Finset.sdiff_subset, hi.2⟩

/-! ## Turning rich chunks into a uniform interval -/

lemma pairwiseDisjoint_indexedSquareValues {G L : ℕ}
    {U : Fin L → Finset (Fin G × Fin 3)}
    (hU : (Set.univ : Set (Fin L)).PairwiseDisjoint U) :
    (Set.univ : Set (Fin L)).PairwiseDisjoint
      (fun i ↦ indexedSquareValues (U i)) := by
  intro i _ j _ hij
  change Disjoint (indexedSquareValues (U i))
    (indexedSquareValues (U j))
  rw [Finset.disjoint_left]
  intro q hqi hqj
  obtain ⟨pi, hpi, hpiq⟩ := Finset.mem_image.mp hqi
  obtain ⟨pj, hpj, hpjq⟩ := Finset.mem_image.mp hqj
  have hp : pi = pj := indexedSquareValues_injective G (hpiq.trans hpjq.symm)
  subst pj
  exact (Finset.disjoint_left.mp
    (hU (Set.mem_univ i) (Set.mem_univ j) hij)) hpi hpj

lemma indexedSquareValues_biUnion_subset {G L : ℕ}
    {U : Fin L → Finset (Fin G × Fin 3)}
    {D : Finset (Fin G × Fin 3)} (hU : ∀ i, U i ⊆ D) :
    (Finset.univ : Finset (Fin L)).biUnion
        (fun i ↦ indexedSquareValues (U i)) ⊆ indexedSquareValues D := by
  intro q hq
  obtain ⟨i, _, hqi⟩ := Finset.mem_biUnion.mp hq
  exact indexedSquareValues_mono (hU i) hqi

lemma sum_indexedSquareValues_le {G : ℕ} (U : Finset (Fin G × Fin 3)) :
    ∑ q ∈ indexedSquareValues U, q ≤
      U.card * (2 * (6 * G + 1)) ^ 2 := by
  calc
    ∑ q ∈ indexedSquareValues U, q ≤
        (indexedSquareValues U).card • (2 * (6 * G + 1)) ^ 2 := by
      apply Finset.sum_le_card_nsmul
      intro q hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      exact Nat.pow_le_pow_left (Nat.le_of_lt (tripleRoot_upper p)) 2
    _ = U.card * (2 * (6 * G + 1)) ^ 2 := by
      simp

lemma card_biUnion_indexedSquareValues_le {G L c : ℕ}
    (U : Fin L → Finset (Fin G × Fin 3))
    (hcard : ∀ i, (U i).card ≤ c) :
    ((Finset.univ : Finset (Fin L)).biUnion
      (fun i ↦ indexedSquareValues (U i))).card ≤ L * c := by
  calc
    ((Finset.univ : Finset (Fin L)).biUnion
        (fun i ↦ indexedSquareValues (U i))).card ≤
        ∑ i : Fin L, (indexedSquareValues (U i)).card :=
      Finset.card_biUnion_le
    _ = ∑ i : Fin L, (U i).card := by simp
    _ ≤ ∑ _i : Fin L, c := by
      apply Finset.sum_le_sum
      intro i _
      exact hcard i
    _ = L * c := by simp

/-- If every element of a disjoint remainder fits into the initial interval
length, adjoining the whole remainder extends the upper endpoint by its
total sum. -/
lemma Covers.union_left {C R : Finset ℕ} {a b : ℕ}
    (h : Covers C a b) (hab : a ≤ b) (hdisj : Disjoint R C)
    (hfit : ∀ q ∈ R, q ≤ b - a + 1) :
    Covers (R ∪ C) a (b + ∑ q ∈ R, q) := by
  induction R using Finset.induction_on with
  | empty => simpa using h
  | @insert q R hqR ih =>
      have hqC : q ∉ C := by
        intro hqC
        exact (Finset.disjoint_left.mp hdisj)
          (Finset.mem_insert_self q R) hqC
      have hRC : Disjoint R C :=
        hdisj.mono (Finset.subset_insert q R) (fun _ hx ↦ hx)
      have hqfit : q ≤ b - a + 1 := hfit q (Finset.mem_insert_self q R)
      have hRfit : ∀ x ∈ R, x ≤ b - a + 1 := by
        intro x hx
        exact hfit x (Finset.mem_insert_of_mem hx)
      have hi := ih hRC hRfit
      have hqRC : q ∉ R ∪ C := by simp [hqR, hqC]
      have hlen : q ≤ (b + ∑ x ∈ R, x) - a + 1 := by omega
      have hins := hi.insert (hab.trans (Nat.le_add_right b _)) hqRC hlen
      simpa [Finset.sum_insert hqR, Finset.insert_union,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hins

/-- The Lev interval extracted from the disjoint rich chunks.  The explicit
quantity `Q` is an upper bound for the sum of every chunk. -/
lemma exists_lev_cover_from_rich_chunks (H L : ℕ)
    {D : Finset (Fin (24 * 2 ^ H) × Fin 3)}
    (hbudget :
      5 * (24 * 2 ^ H) + (48 * H + 8) * L ≤ 4 * D.card)
    (hL : 1 ≤ L)
    (hn : 3 ≤ (2 ^ H) ^ 2 / 2 + 1)
    (hlarge :
      2 * (((12 * H + 2) *
          (2 * (6 * (24 * 2 ^ H) + 1)) ^ 2 - 1 +
          (((2 ^ H) ^ 2 / 2 + 1) - 2) - 1) /
          (((2 ^ H) ^ 2 / 2 + 1) - 2)) ≤ L) :
    ∃ C : Finset ℕ, ∃ a : ℕ,
      C ⊆ indexedSquareValues D ∧
      C.card ≤ L * (12 * H + 2) ∧
      a ≤ L * ((12 * H + 2) *
        (2 * (6 * (24 * 2 ^ H) + 1)) ^ 2) ∧
      Covers C a (a + L * (((2 ^ H) ^ 2 / 2 + 1) - 1)) := by
  let Q := (12 * H + 2) * (2 * (6 * (24 * 2 ^ H) + 1)) ^ 2
  let n := (2 ^ H) ^ 2 / 2 + 1
  obtain ⟨U, hUdisj, hU⟩ := exists_disjoint_rich_chunks H L hbudget
  let E : Fin L → Finset ℕ := fun i ↦ indexedSquareValues (U i)
  have hEdisj : (Set.univ : Set (Fin L)).PairwiseDisjoint E :=
    pairwiseDisjoint_indexedSquareValues hUdisj
  have hEcard : ∀ i, n ≤ (intSubsetSums (E i)).card := by
    intro i
    have hrich := (hU i).2.2.1
    dsimp [n, E]
    omega
  have hEbound : ∀ i, ∃ z : ℤ,
      intSubsetSums (E i) ⊆ Finset.Icc z (z + Q) := by
    intro i
    refine ⟨0, (intSubsetSums_subset_Icc (E i)).trans ?_⟩
    intro z hz
    rw [Finset.mem_Icc] at hz ⊢
    refine ⟨hz.1, hz.2.trans ?_⟩
    have hsum : ∑ q ∈ E i, q ≤ Q := by
      calc
        ∑ q ∈ E i, q ≤
            (U i).card * (2 * (6 * (24 * 2 ^ H) + 1)) ^ 2 :=
          sum_indexedSquareValues_le (U i)
        _ ≤ Q := by
          dsimp [Q]
          exact Nat.mul_le_mul_right _ (hU i).2.1
    norm_cast
    simpa using hsum
  have hEprim : ∀ i,
      Erdos186.CFP.Lev.Primitive (intSubsetSums (E i)) := by
    intro i
    exact intSubsetSums_primitive_of_gcd_eq_one (hU i).2.2.2
  obtain ⟨a, ha⟩ := exists_cover_of_lev_chunks hL (by
      dsimp [Q]
      exact Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by omega)
          (pow_ne_zero 2 (by positivity)))) hn
      (by simpa [Q, n] using hlarge)
    E hEdisj hEcard hEbound hEprim
  let C := (Finset.univ : Finset (Fin L)).biUnion E
  have hCD : C ⊆ indexedSquareValues D := by
    exact indexedSquareValues_biUnion_subset (fun i ↦ (hU i).1)
  have hCcard : C.card ≤ L * (12 * H + 2) := by
    exact card_biUnion_indexedSquareValues_le U (fun i ↦ (hU i).2.1)
  have haC : a ∈ C.subsetSum := ha a le_rfl (Nat.le_add_right _ _)
  obtain ⟨A, hAC, hAsum⟩ := Finset.mem_subsetSum_iff.mp haC
  have haSum : a ≤ ∑ q ∈ C, q := by
    rw [← hAsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg hAC
      (fun _ _ _ ↦ Nat.zero_le _)
  have hsumC : ∑ q ∈ C, q ≤ L * Q := by
    calc
      ∑ q ∈ C, q ≤ C.card * (2 * (6 * (24 * 2 ^ H) + 1)) ^ 2 := by
        apply Finset.sum_le_card_nsmul
        intro q hq
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp (hCD hq)
        have hpRoot := tripleRoot_upper p
        simpa [nsmul_eq_mul] using
          Nat.pow_le_pow_left (Nat.le_of_lt hpRoot) 2
      _ ≤ L * Q := by
        dsimp [Q]
        nlinarith
  refine ⟨C, a, hCD, hCcard, ?_, ?_⟩
  · exact haSum.trans hsumC
  · simpa [C, E, n] using ha

/-- A half-dense indexed block covers a common interval once the four
explicit numerical conditions needed by the chunk and Lev arguments hold. -/
lemma dense_indexedSquareValues_cover (H L : ℕ)
    {D : Finset (Fin (24 * 2 ^ H) × Fin 3)}
    (hdense : 3 * (24 * 2 ^ H) ≤ 2 * D.card)
    (hbudget : (48 * H + 8) * L ≤ 24 * 2 ^ H)
    (hL : 1 ≤ L)
    (hn : 3 ≤ (2 ^ H) ^ 2 / 2 + 1)
    (hlarge :
      2 * (((12 * H + 2) *
          (2 * (6 * (24 * 2 ^ H) + 1)) ^ 2 - 1 +
          (((2 ^ H) ^ 2 / 2 + 1) - 2) - 1) /
          (((2 ^ H) ^ 2 / 2 + 1) - 2)) ≤ L)
    (hfit :
      (2 * (6 * (24 * 2 ^ H) + 1)) ^ 2 ≤
        L * (((2 ^ H) ^ 2 / 2 + 1) - 1) + 1)
    (hmass :
      2 * (L * ((12 * H + 2) *
          (2 * (6 * (24 * 2 ^ H) + 1)) ^ 2)) ≤
        (24 * 2 ^ H) * (6 * (24 * 2 ^ H) + 1) ^ 2) :
    Covers (indexedSquareValues D)
      (L * ((12 * H + 2) *
        (2 * (6 * (24 * 2 ^ H) + 1)) ^ 2))
      ((24 * 2 ^ H) * (6 * (24 * 2 ^ H) + 1) ^ 2) := by
  let G := 24 * 2 ^ H
  let X := 6 * G + 1
  let M := (2 * X) ^ 2
  let c := 12 * H + 2
  let Q := c * M
  let n := (2 ^ H) ^ 2 / 2 + 1
  let W := L * (n - 1)
  have hchunkBudget : 5 * G + (48 * H + 8) * L ≤ 4 * D.card := by
    have h6G : 6 * G ≤ 4 * D.card := by
      dsimp [G] at hdense ⊢
      nlinarith
    dsimp [G] at hbudget ⊢
    omega
  obtain ⟨C, a, hCD, hCcard, ha, hcover⟩ :=
    exists_lev_cover_from_rich_chunks H L hchunkBudget hL hn hlarge
  have hsumD : D.card * X ^ 2 ≤ ∑ q ∈ indexedSquareValues D, q := by
    simpa using Finset.card_nsmul_le_sum (indexedSquareValues D) id (X ^ 2)
      (by
        intro q hq
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
        exact Nat.pow_le_pow_left (tripleRoot_lower p) 2)
  have hsumC : ∑ q ∈ C, q ≤ L * Q := by
    calc
      ∑ q ∈ C, q ≤ C.card • M := by
        apply Finset.sum_le_card_nsmul
        intro q hq
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp (hCD hq)
        dsimp [M, X, G]
        exact Nat.pow_le_pow_left
          (Nat.le_of_lt (tripleRoot_upper p)) 2
      _ = C.card * M := by simp
      _ ≤ (L * c) * M := Nat.mul_le_mul_right M hCcard
      _ = L * Q := by simp [Q]; ring
  let R := indexedSquareValues D \ C
  have hRC : Disjoint R C := Finset.sdiff_disjoint
  have hRfit : ∀ q ∈ R, q ≤ (a + W) - a + 1 := by
    intro q hq
    have hqD : q ∈ indexedSquareValues D := (Finset.mem_sdiff.mp hq).1
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hqD
    have hroot := tripleRoot_upper p
    have hsq : (tripleRoot (24 * 2 ^ H) p.1 p.2) ^ 2 ≤
        (2 * (6 * (24 * 2 ^ H) + 1)) ^ 2 :=
      Nat.pow_le_pow_left (Nat.le_of_lt hroot) 2
    dsimp [W, n]
    simpa using hsq.trans hfit
  have hext : Covers (R ∪ C) a (a + W + ∑ q ∈ R, q) := by
    exact Covers.union_left hcover (Nat.le_add_right _ _) hRC hRfit
  have hUnion : R ∪ C = indexedSquareValues D := by
    exact Finset.sdiff_union_of_subset hCD
  have hsumSplit :
      (∑ q ∈ R, q) + ∑ q ∈ C, q = ∑ q ∈ indexedSquareValues D, q := by
    exact Finset.sum_sdiff hCD
  have hdenseSq :
      (3 * G) * X ^ 2 ≤ (2 * D.card) * X ^ 2 :=
    Nat.mul_le_mul_right (X ^ 2) (by simpa [G] using hdense)
  have hcapacity : G * X ^ 2 + L * Q ≤ D.card * X ^ 2 := by
    have hmass' : 2 * (L * Q) ≤ G * X ^ 2 := by
      simpa [G, X, M, c, Q] using hmass
    nlinarith
  have hRlarge : G * X ^ 2 ≤ ∑ q ∈ R, q := by
    omega
  rw [hUnion] at hext
  intro z hzlo hzhi
  apply hext z
  · have ha' : a ≤ L * Q := by
      simpa [G, X, M, c, Q] using ha
    exact ha'.trans (by simpa [G, X, M, c, Q] using hzlo)
  · have hzhi' : z ≤ G * X ^ 2 := by
      simpa [G, X] using hzhi
    calc
      z ≤ G * X ^ 2 := hzhi'
      _ ≤ ∑ q ∈ R, q := hRlarge
      _ ≤ a + W + ∑ q ∈ R, q := Nat.le_add_left _ _

/-! ## Explicit numerical scales -/

/-- The large fixed shift absorbs all constants in the elementary estimates;
the variable term supplies the quadratic-versus-exponential domination. -/
def ramseyExponent (k : ℕ) : ℕ := 2 * k + 64

/-- Number of Lev chunks used at scale `k`. -/
def ramseyChunkCount (k : ℕ) : ℕ :=
  10000000 * (ramseyExponent k + 1)

def ramseyGroupCount (k : ℕ) : ℕ := 24 * 2 ^ ramseyExponent k

def ramseyRootFloor (k : ℕ) : ℕ := 6 * ramseyGroupCount k + 1

def ramseyChunkBound (k : ℕ) : ℕ :=
  (12 * ramseyExponent k + 2) * (2 * ramseyRootFloor k) ^ 2

def ramseyBlockLo (k : ℕ) : ℕ :=
  ramseyChunkCount k * ramseyChunkBound k

def ramseyBlockHi (k : ℕ) : ℕ :=
  ramseyGroupCount k * (ramseyRootFloor k) ^ 2

def ramseySquareBlock (k : ℕ) : Finset ℕ :=
  indexedSquareValues
    (Finset.univ : Finset (Fin (ramseyGroupCount k) × Fin 3))

lemma ramseyExponent_ge (k : ℕ) : 64 ≤ ramseyExponent k := by
  simp [ramseyExponent]

lemma billion_mul_scale_sq_le_pow (k : ℕ) :
    1000000000 * (2 * k + 67) ^ 2 ≤ 2 ^ (2 * k + 64) := by
  have hpow := Nat.two_mul_sq_add_one_le_two_pow_two_mul k
  have hscaled := Nat.mul_le_mul_left (2 ^ 64) hpow
  have hpoly :
      1000000000 * (2 * k + 67) ^ 2 ≤
        2 ^ 64 * (2 * k ^ 2 + 1) := by
    nlinarith
  calc
    1000000000 * (2 * k + 67) ^ 2 ≤
        2 ^ 64 * (2 * k ^ 2 + 1) := hpoly
    _ ≤ 2 ^ 64 * 2 ^ (2 * k) := hscaled
    _ = 2 ^ (2 * k + 64) := by rw [← pow_add]; congr 1; omega

lemma billion_mul_exponent_add_three_sq_le_pow (k : ℕ) :
    1000000000 * (ramseyExponent k + 3) ^ 2 ≤
      2 ^ ramseyExponent k := by
  simpa [ramseyExponent, Nat.add_assoc] using billion_mul_scale_sq_le_pow k

/-- A deliberately rounded bound for the sum of one rich chunk. -/
lemma ramseyChunkBound_le (H : ℕ) :
    (12 * H + 2) * (2 * (6 * (24 * 2 ^ H) + 1)) ^ 2 ≤
      1200000 * (H + 1) * (2 ^ H) ^ 2 := by
  let s := 2 ^ H
  have hs : 1 ≤ s := Nat.one_le_two_pow
  have hroot : 2 * (6 * (24 * s) + 1) ≤ 290 * s := by
    nlinarith
  have hsquare := Nat.pow_le_pow_left hroot 2
  have hcoeff : 12 * H + 2 ≤ 14 * (H + 1) := by omega
  calc
    (12 * H + 2) * (2 * (6 * (24 * 2 ^ H) + 1)) ^ 2 ≤
        14 * (H + 1) * (290 * 2 ^ H) ^ 2 := by
      dsimp [s] at hroot hsquare ⊢
      nlinarith
    _ ≤ 1200000 * (H + 1) * (2 ^ H) ^ 2 := by ring_nf; omega

lemma ramsey_lev_large (H : ℕ) (hH : 3 ≤ H) :
    2 * (((12 * H + 2) *
        (2 * (6 * (24 * 2 ^ H) + 1)) ^ 2 - 1 +
        (((2 ^ H) ^ 2 / 2 + 1) - 2) - 1) /
        (((2 ^ H) ^ 2 / 2 + 1) - 2)) ≤
      10000000 * (H + 1) := by
  let T := (2 ^ H) ^ 2
  let Q := (12 * H + 2) * (2 * (6 * (24 * 2 ^ H) + 1)) ^ 2
  let d := (T / 2 + 1) - 2
  have hpow8 : 8 ≤ 2 ^ H := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hH
  have hT8 : 8 ≤ T := by
    dsimp [T]
    nlinarith
  have hd : 0 < d := by dsimp [d]; omega
  have hTd : T ≤ 3 * d := by
    dsimp [d]
    omega
  have hQ : Q ≤ 1200000 * (H + 1) * T := by
    exact ramseyChunkBound_le H
  have hQD : Q ≤ 3600000 * (H + 1) * d := by
    have := Nat.mul_le_mul_left (1200000 * (H + 1)) hTd
    nlinarith
  have hdScale : d ≤ (H + 1) * d := by
    nlinarith
  have hnum : Q - 1 + d - 1 ≤ 5000000 * (H + 1) * d := by
    calc
      Q - 1 + d - 1 ≤ Q + d := by omega
      _ ≤ 3600000 * (H + 1) * d + (H + 1) * d :=
        Nat.add_le_add hQD hdScale
      _ ≤ 5000000 * (H + 1) * d := by nlinarith
  have hdiv : (Q - 1 + d - 1) / d ≤ 5000000 * (H + 1) := by
    apply (Nat.div_le_iff_le_mul hd).2
    calc
      Q - 1 + d - 1 ≤ 5000000 * (H + 1) * d := hnum
      _ ≤ (5000000 * (H + 1)) * d + d - 1 := by omega
  dsimp [Q, T, d] at hdiv ⊢
  nlinarith

lemma ramsey_chunk_budget (k : ℕ) :
    (48 * ramseyExponent k + 8) * ramseyChunkCount k ≤
      ramseyGroupCount k := by
  have hscale := billion_mul_exponent_add_three_sq_le_pow k
  unfold ramseyChunkCount ramseyGroupCount
  have hpoly :
      (48 * ramseyExponent k + 8) *
          (10000000 * (ramseyExponent k + 1)) ≤
        1000000000 * (ramseyExponent k + 3) ^ 2 := by
    nlinarith
  exact hpoly.trans (by nlinarith)

lemma ramsey_chunk_count_pos (k : ℕ) : 1 ≤ ramseyChunkCount k := by
  unfold ramseyChunkCount
  have := ramseyExponent_ge k
  nlinarith

lemma ramsey_chunk_card_at_least_three (k : ℕ) :
    3 ≤ (2 ^ ramseyExponent k) ^ 2 / 2 + 1 := by
  have hH := ramseyExponent_ge k
  have hpow8 : 8 ≤ 2 ^ ramseyExponent k := by
    have hmono := Nat.pow_le_pow_right (n := 2) (by omega)
      (show 3 ≤ ramseyExponent k by omega)
    norm_num at hmono ⊢
    exact hmono
  have hsquare : 4 ≤ (2 ^ ramseyExponent k) ^ 2 := by nlinarith
  have hhalf : 2 ≤ (2 ^ ramseyExponent k) ^ 2 / 2 :=
    (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  omega

lemma ramsey_extension_fits (k : ℕ) :
    (2 * (6 * ramseyGroupCount k + 1)) ^ 2 ≤
      ramseyChunkCount k *
          (((2 ^ ramseyExponent k) ^ 2 / 2 + 1) - 1) + 1 := by
  let H := ramseyExponent k
  let s := 2 ^ H
  let T := s ^ 2
  have hs : 1 ≤ s := Nat.one_le_two_pow
  have hroot : 2 * (6 * (24 * s) + 1) ≤ 290 * s := by
    nlinarith
  have hM : (2 * (6 * (24 * s) + 1)) ^ 2 ≤ 84100 * T := by
    have := Nat.pow_le_pow_left hroot 2
    dsimp [T]
    nlinarith
  have hhalf : T ≤ 3 * (T / 2) := by
    have hT : 2 ≤ T := by
      have hH := ramseyExponent_ge k
      dsimp [T, s]
      have hmono := Nat.pow_le_pow_right (n := 2) (by omega)
        (show 1 ≤ ramseyExponent k by omega)
      have : 2 ≤ 2 ^ ramseyExponent k := by
        norm_num at hmono ⊢
        exact hmono
      nlinarith
    have htwoS : 2 ∣ s := by
      dsimp [s, H]
      exact dvd_pow_self 2 (by
        have hH := ramseyExponent_ge k
        omega)
    have htwoT : 2 ∣ T := by
      dsimp [T]
      exact dvd_pow htwoS (by decide : 2 ≠ 0)
    have heq : 2 * (T / 2) = T := Nat.mul_div_cancel' htwoT
    nlinarith
  have hlarge : 84100 * T ≤
      10000000 * (H + 1) * (T / 2) := by
    have h1 := Nat.mul_le_mul_left 84100 hhalf
    have h2 : 252300 * (T / 2) ≤
        10000000 * (H + 1) * (T / 2) := by
      apply Nat.mul_le_mul_right
      nlinarith
    calc
      84100 * T ≤ 84100 * (3 * (T / 2)) := h1
      _ = 252300 * (T / 2) := by ring
      _ ≤ 10000000 * (H + 1) * (T / 2) := h2
  have hfinal := (hM.trans hlarge).trans
    (Nat.le_add_right (10000000 * (H + 1) * (T / 2)) 1)
  simpa [ramseyGroupCount, ramseyChunkCount, H, s, T] using hfinal

lemma ramsey_core_mass_small (k : ℕ) :
    2 * (ramseyChunkCount k * ramseyChunkBound k) ≤
      ramseyBlockHi k := by
  let H := ramseyExponent k
  let s := 2 ^ H
  let T := s ^ 2
  have hQ : ramseyChunkBound k ≤ 1200000 * (H + 1) * T := by
    simpa [ramseyChunkBound, ramseyRootFloor, ramseyGroupCount, H, s, T]
      using ramseyChunkBound_le H
  have hscale : 1000000000 * (H + 3) ^ 2 ≤ s := by
    simpa [H] using billion_mul_exponent_add_three_sq_le_pow k
  have hcoef :
      24000000000000 * (H + 1) ^ 2 ≤ 497664 * s := by
    calc
      24000000000000 * (H + 1) ^ 2 ≤
          497664 * (1000000000 * (H + 3) ^ 2) := by
        nlinarith
      _ ≤ 497664 * s := Nat.mul_le_mul_left 497664 hscale
  have hupper' :
      2 * (ramseyChunkCount k * ramseyChunkBound k) ≤
        (24000000000000 * (H + 1) ^ 2) * T := by
    calc
      2 * (ramseyChunkCount k * ramseyChunkBound k) =
          (2 * ramseyChunkCount k) * ramseyChunkBound k := by ring
      _ ≤ (2 * ramseyChunkCount k) *
          (1200000 * (H + 1) * T) :=
        Nat.mul_le_mul_left (2 * ramseyChunkCount k) hQ
      _ = (24000000000000 * (H + 1) ^ 2) * T := by
        simp [ramseyChunkCount, H]
        ring
  have hcoefT := Nat.mul_le_mul_right T hcoef
  have hlower : 497664 * s * T ≤ ramseyBlockHi k := by
    have hx : 144 * s ≤ 6 * (24 * s) + 1 := by omega
    have hx2 := Nat.pow_le_pow_left hx 2
    have hmul := Nat.mul_le_mul_left (24 * s) hx2
    calc
      497664 * s * T = 24 * s * (144 * s) ^ 2 := by
        dsimp [T]
        ring
      _ ≤ 24 * s * (6 * (24 * s) + 1) ^ 2 := hmul
      _ = ramseyBlockHi k := by
        simp [ramseyBlockHi, ramseyGroupCount, ramseyRootFloor, H, s]
  exact hupper'.trans (hcoefT.trans hlower)

lemma ramseyBlockLo_le_hi (k : ℕ) :
    ramseyBlockLo k ≤ ramseyBlockHi k := by
  have h := ramsey_core_mass_small k
  unfold ramseyBlockLo at ⊢
  omega

lemma ramseyBlockLo_succ_le_hi (k : ℕ) :
    ramseyBlockLo (k + 1) ≤ ramseyBlockHi k := by
  let H := ramseyExponent k
  let s := 2 ^ H
  let T := s ^ 2
  have hHsucc : ramseyExponent (k + 1) = H + 2 := by
    simp [ramseyExponent, H]
    omega
  have hsSucc : 2 ^ ramseyExponent (k + 1) = 4 * s := by
    rw [hHsucc, pow_add]
    norm_num [s, mul_comm]
  have hsSucc' : 2 ^ (H + 2) = 4 * s := by
    simpa only [hHsucc] using hsSucc
  have hQraw := ramseyChunkBound_le (ramseyExponent (k + 1))
  have hQ : ramseyChunkBound (k + 1) ≤
      1200000 * (H + 3) * (4 * s) ^ 2 := by
    unfold ramseyChunkBound ramseyRootFloor ramseyGroupCount
    rw [hHsucc, hsSucc']
    rw [hHsucc, hsSucc'] at hQraw
    exact hQraw
  have hupper : ramseyBlockLo (k + 1) ≤
      192000000000000 * (H + 3) ^ 2 * T := by
    calc
      ramseyBlockLo (k + 1) =
          ramseyChunkCount (k + 1) * ramseyChunkBound (k + 1) := rfl
      _ ≤ ramseyChunkCount (k + 1) *
          (1200000 * (H + 3) * (4 * s) ^ 2) :=
        Nat.mul_le_mul_left _ hQ
      _ = 192000000000000 * (H + 3) ^ 2 * T := by
        simp [ramseyChunkCount, hHsucc]
        dsimp [T]
        ring
  have hscale : 1000000000 * (H + 3) ^ 2 ≤ s := by
    simpa [H] using billion_mul_exponent_add_three_sq_le_pow k
  have hcoef :
      192000000000000 * (H + 3) ^ 2 ≤ 497664 * s := by
    calc
      192000000000000 * (H + 3) ^ 2 ≤
          497664 * (1000000000 * (H + 3) ^ 2) := by
        nlinarith
      _ ≤ 497664 * s := Nat.mul_le_mul_left 497664 hscale
  have hcoefT := Nat.mul_le_mul_right T hcoef
  have hlower : 497664 * s * T ≤ ramseyBlockHi k := by
    have hx : 144 * s ≤ 6 * (24 * s) + 1 := by omega
    have hx2 := Nat.pow_le_pow_left hx 2
    have hmul := Nat.mul_le_mul_left (24 * s) hx2
    calc
      497664 * s * T = 24 * s * (144 * s) ^ 2 := by
        dsimp [T]
        ring
      _ ≤ 24 * s * (6 * (24 * s) + 1) ^ 2 := hmul
      _ = ramseyBlockHi k := by
        simp [ramseyBlockHi, ramseyGroupCount, ramseyRootFloor, H, s]
  exact hupper.trans (hcoefT.trans hlower)

lemma ramseyBlockHi_unbounded (n : ℕ) :
    ∃ k : ℕ, n ≤ ramseyBlockHi k := by
  refine ⟨n, ?_⟩
  have hn : n ≤ 2 ^ n := (Nat.lt_two_pow_self (n := n)).le
  have hpow : 2 ^ n ≤ 2 ^ ramseyExponent n :=
    Nat.pow_le_pow_right (n := 2) (by omega) (by
      simp [ramseyExponent]
      omega)
  have hx : 1 ≤ (6 * (24 * 2 ^ ramseyExponent n) + 1) ^ 2 := by
    exact Nat.one_le_pow 2 (6 * (24 * 2 ^ ramseyExponent n) + 1)
      (by omega)
  calc
    n ≤ 2 ^ n := hn
    _ ≤ 2 ^ ramseyExponent n := hpow
    _ ≤ 24 * 2 ^ ramseyExponent n := by nlinarith
    _ ≤ 24 * 2 ^ ramseyExponent n *
        (6 * (24 * 2 ^ ramseyExponent n) + 1) ^ 2 := by
      simpa using Nat.mul_le_mul_left (24 * 2 ^ ramseyExponent n) hx
    _ = ramseyBlockHi n := rfl

/-- The numerical estimates specialized to one scale, packaged separately so
the later value-level robustness proof has no quantitative bookkeeping. -/
lemma ramsey_dense_index_cover (k : ℕ)
    {I : Finset (Fin (24 * 2 ^ ramseyExponent k) × Fin 3)}
    (hI : 3 * (24 * 2 ^ ramseyExponent k) ≤ 2 * I.card) :
    Covers (indexedSquareValues I) (ramseyBlockLo k) (ramseyBlockHi k) := by
  have hcover := dense_indexedSquareValues_cover
    (ramseyExponent k) (ramseyChunkCount k) hI
    (by simpa [ramseyGroupCount] using ramsey_chunk_budget k)
    (ramsey_chunk_count_pos k)
    (ramsey_chunk_card_at_least_three k)
    (by
      simpa [ramseyChunkCount] using
        ramsey_lev_large (ramseyExponent k) (by
          have := ramseyExponent_ge k
          omega))
    (by
      simpa [ramseyGroupCount] using ramsey_extension_fits k)
    (by
      simpa [ramseyBlockHi, ramseyBlockLo, ramseyChunkBound,
        ramseyRootFloor, ramseyGroupCount] using ramsey_core_mass_small k)
  simpa [ramseyBlockLo, ramseyBlockHi, ramseyChunkBound,
    ramseyRootFloor, ramseyGroupCount] using hcover

/-! ## Ordinary completeness of the positive squares -/

/-- The positive square values with roots at most `t`. -/
def squaresUpTo (t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 t).image fun m ↦ m ^ 2

@[simp] lemma mem_squaresUpTo {t q : ℕ} :
    q ∈ squaresUpTo t ↔ ∃ m : ℕ, 1 ≤ m ∧ m ≤ t ∧ m ^ 2 = q := by
  simp [squaresUpTo, and_assoc, eq_comm]

lemma square_succ_not_mem_squaresUpTo (t : ℕ) :
    (t + 1) ^ 2 ∉ squaresUpTo t := by
  rw [mem_squaresUpTo]
  rintro ⟨m, hm1, hmt, hm⟩
  have hsqrt : m = t + 1 := by
    exact Nat.pow_left_injective (by omega : 2 ≠ 0) hm
  omega

lemma squaresUpTo_succ (t : ℕ) :
    squaresUpTo (t + 1) = insert ((t + 1) ^ 2) (squaresUpTo t) := by
  ext q
  simp only [mem_squaresUpTo, Finset.mem_insert]
  constructor
  · rintro ⟨m, hm1, hmt, rfl⟩
    by_cases hm : m = t + 1
    · exact Or.inl (by rw [hm])
    · exact Or.inr ⟨m, hm1, by omega, rfl⟩
  · rintro (rfl | ⟨m, hm1, hmt, rfl⟩)
    · exact ⟨t + 1, by omega, le_rfl, rfl⟩
    · exact ⟨m, hm1, by omega, rfl⟩

/-- Right endpoint of the interval generated from the ten-square seed. -/
def squareCoverTop (t : ℕ) : ℕ :=
  256 + ∑ m ∈ Finset.Icc 11 t, m ^ 2

lemma squareCoverTop_ten : squareCoverTop 10 = 256 := by
  decide

lemma squareCoverTop_ge (t : ℕ) : 129 ≤ squareCoverTop t := by
  unfold squareCoverTop
  omega

lemma squareCoverTop_succ {t : ℕ} (ht : 10 ≤ t) :
    squareCoverTop (t + 1) = squareCoverTop t + (t + 1) ^ 2 := by
  simp only [squareCoverTop]
  rw [show Finset.Icc 11 (t + 1) = insert (t + 1) (Finset.Icc 11 t) by
    ext x
    simp
    omega]
  simp [show t + 1 ∉ Finset.Icc 11 t by simp]
  ac_rfl

/-- Bit-mask certificates for the 128 integers in the finite seed interval.
Bit `i` records use of the square `(i+1)^2`. -/
def squareSeedMask : ℕ → ℕ
  | 0 => 174
  | 1 => 122
  | 2 => 123
  | 3 => 285
  | 4 => 202
  | 5 => 180
  | 6 => 124
  | 7 => 125
  | 8 => 298
  | 9 => 182
  | 10 => 126
  | 11 => 127
  | 12 => 184
  | 13 => 185
  | 14 => 207
  | 15 => 327
  | 16 => 186
  | 17 => 187
  | 18 => 212
  | 19 => 213
  | 20 => 224
  | 21 => 188
  | 22 => 189
  | 23 => 215
  | 24 => 226
  | 25 => 190
  | 26 => 191
  | 27 => 311
  | 28 => 555
  | 29 => 218
  | 30 => 219
  | 31 => 335
  | 32 => 392
  | 33 => 230
  | 34 => 220
  | 35 => 221
  | 36 => 232
  | 37 => 233
  | 38 => 222
  | 39 => 223
  | 40 => 234
  | 41 => 235
  | 42 => 318
  | 43 => 319
  | 44 => 644
  | 45 => 236
  | 46 => 237
  | 47 => 347
  | 48 => 568
  | 49 => 238
  | 50 => 239
  | 51 => 348
  | 52 => 349
  | 53 => 360
  | 54 => 244
  | 55 => 245
  | 56 => 351
  | 57 => 362
  | 58 => 246
  | 59 => 247
  | 60 => 610
  | 61 => 248
  | 62 => 249
  | 63 => 365
  | 64 => 654
  | 65 => 250
  | 66 => 251
  | 67 => 367
  | 68 => 424
  | 69 => 425
  | 70 => 252
  | 71 => 253
  | 72 => 373
  | 73 => 427
  | 74 => 254
  | 75 => 255
  | 76 => 375
  | 77 => 428
  | 78 => 376
  | 79 => 377
  | 80 => 666
  | 81 => 430
  | 82 => 378
  | 83 => 379
  | 84 => 678
  | 85 => 458
  | 86 => 436
  | 87 => 380
  | 88 => 381
  | 89 => 670
  | 90 => 438
  | 91 => 382
  | 92 => 383
  | 93 => 440
  | 94 => 441
  | 95 => 463
  | 96 => 684
  | 97 => 442
  | 98 => 443
  | 99 => 468
  | 100 => 469
  | 101 => 480
  | 102 => 444
  | 103 => 445
  | 104 => 471
  | 105 => 482
  | 106 => 446
  | 107 => 447
  | 108 => 810
  | 109 => 694
  | 110 => 474
  | 111 => 475
  | 112 => 696
  | 113 => 697
  | 114 => 486
  | 115 => 476
  | 116 => 477
  | 117 => 488
  | 118 => 489
  | 119 => 478
  | 120 => 479
  | 121 => 490
  | 122 => 491
  | 123 => 727
  | 124 => 738
  | 125 => 702
  | 126 => 492
  | 127 => 493
  | _ => 0

def squareSeedWitness (n : ℕ) : Finset ℕ :=
  ((Finset.range 10).filter fun i ↦ (squareSeedMask (n - 129)).testBit i).image
    fun i ↦ (i + 1) ^ 2

lemma squareSeedWitness_subset (n : ℕ) :
    squareSeedWitness n ⊆ squaresUpTo 10 := by
  intro q hq
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
  have hi10 : i < 10 := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  apply mem_squaresUpTo.mpr
  exact ⟨i + 1, by omega, by omega, rfl⟩

/-! Splitting the finite calculation keeps every kernel normalization small. -/

lemma squareSeedWitness_sum_0 {n : ℕ} (hlo : 129 ≤ n) (hhi : n ≤ 144) :
    ∑ q ∈ squareSeedWitness n, q = n := by
  interval_cases n <;> decide

lemma squareSeedWitness_sum_1 {n : ℕ} (hlo : 145 ≤ n) (hhi : n ≤ 160) :
    ∑ q ∈ squareSeedWitness n, q = n := by
  interval_cases n <;> decide

lemma squareSeedWitness_sum_2 {n : ℕ} (hlo : 161 ≤ n) (hhi : n ≤ 176) :
    ∑ q ∈ squareSeedWitness n, q = n := by
  interval_cases n <;> decide

lemma squareSeedWitness_sum_3 {n : ℕ} (hlo : 177 ≤ n) (hhi : n ≤ 192) :
    ∑ q ∈ squareSeedWitness n, q = n := by
  interval_cases n <;> decide

lemma squareSeedWitness_sum_4 {n : ℕ} (hlo : 193 ≤ n) (hhi : n ≤ 208) :
    ∑ q ∈ squareSeedWitness n, q = n := by
  interval_cases n <;> decide

lemma squareSeedWitness_sum_5 {n : ℕ} (hlo : 209 ≤ n) (hhi : n ≤ 224) :
    ∑ q ∈ squareSeedWitness n, q = n := by
  interval_cases n <;> decide

lemma squareSeedWitness_sum_6 {n : ℕ} (hlo : 225 ≤ n) (hhi : n ≤ 240) :
    ∑ q ∈ squareSeedWitness n, q = n := by
  interval_cases n <;> decide

lemma squareSeedWitness_sum_7 {n : ℕ} (hlo : 241 ≤ n) (hhi : n ≤ 256) :
    ∑ q ∈ squareSeedWitness n, q = n := by
  interval_cases n <;> decide

/-- A kernel-checked finite certificate for the seed interval. -/
lemma squares_seed : Covers (squaresUpTo 10) 129 256 := by
  intro n hnL hnU
  apply Finset.mem_subsetSum_iff.mpr
  refine ⟨squareSeedWitness n, squareSeedWitness_subset n, ?_⟩
  by_cases h0 : n ≤ 144
  · exact squareSeedWitness_sum_0 (by omega) h0
  by_cases h1 : n ≤ 160
  · exact squareSeedWitness_sum_1 (by omega) h1
  by_cases h2 : n ≤ 176
  · exact squareSeedWitness_sum_2 (by omega) h2
  by_cases h3 : n ≤ 192
  · exact squareSeedWitness_sum_3 (by omega) h3
  by_cases h4 : n ≤ 208
  · exact squareSeedWitness_sum_4 (by omega) h4
  by_cases h5 : n ≤ 224
  · exact squareSeedWitness_sum_5 (by omega) h5
  by_cases h6 : n ≤ 240
  · exact squareSeedWitness_sum_6 (by omega) h6
  exact squareSeedWitness_sum_7 (by omega) hnU

lemma next_square_fits {t : ℕ} (ht : 10 ≤ t) :
    (t + 1) ^ 2 ≤ squareCoverTop t - 129 + 1 := by
  induction t, ht using Nat.le_induction with
  | base => norm_num [squareCoverTop]
  | succ t ht ih =>
      rw [squareCoverTop_succ ht]
      have htop : 129 ≤ squareCoverTop t := squareCoverTop_ge t
      have hdiff : (t + 2) ^ 2 ≤ (t + 1) ^ 2 + (t + 1) ^ 2 := by
        nlinarith
      have ih' : (t + 1) ^ 2 + 128 ≤ squareCoverTop t := by omega
      have hsum : (t + 2) ^ 2 + 128 ≤ squareCoverTop t + (t + 1) ^ 2 := by
        omega
      norm_num [Nat.add_assoc] at hsum ⊢
      omega

lemma squares_cover_interval {t : ℕ} (ht : 10 ≤ t) :
    Covers (squaresUpTo t) 129 (squareCoverTop t) := by
  induction t, ht using Nat.le_induction with
  | base => simpa [squareCoverTop_ten] using squares_seed
  | succ t ht ih =>
      rw [squaresUpTo_succ, squareCoverTop_succ ht]
      exact ih.insert (squareCoverTop_ge t)
        (square_succ_not_mem_squaresUpTo t) (next_square_fits ht)

lemma le_squareCoverTop_self {n : ℕ} (hn : 11 ≤ n) :
    n ≤ squareCoverTop n := by
  have hnmem : n ∈ Finset.Icc 11 n := by simp [hn]
  have hterm : n ^ 2 ≤ ∑ m ∈ Finset.Icc 11 n, m ^ 2 :=
    Finset.single_le_sum (f := fun m : ℕ ↦ m ^ 2)
      (fun _ _ ↦ Nat.zero_le _) hnmem
  have hnn : n ≤ n ^ 2 := by nlinarith
  simp only [squareCoverTop]
  omega

/-- Every natural number at least `129` is a sum of distinct positive square
values.  This is the ordinary-completeness input to the CFP theorem. -/
theorem squares_complete {n : ℕ} (hn : 129 ≤ n) :
    n ∈ (squaresUpTo n).subsetSum := by
  apply squares_cover_interval (by omega : 10 ≤ n) n hn
  exact le_squareCoverTop_self (by omega)

lemma squaresUpTo_are_positive_squares {t q : ℕ} (hq : q ∈ squaresUpTo t) :
    IsPositiveSquare q := by
  obtain ⟨m, hm1, _hmt, rfl⟩ := mem_squaresUpTo.mp hq
  exact ⟨m, hm1, rfl⟩

/-! ## The deterministic Ramsey-block interface -/

/-- A finite square block is robust on `[lo, hi]` if every subblock containing
at least half of its members already covers that interval by subset sums.

This is the exact deterministic conclusion used from the Conlon--Fox--Pham
robust-block lemma when the number of colours is two. -/
def RobustSquareBlock (block : Finset ℕ) (lo hi : ℕ) : Prop :=
  ∀ D : Finset ℕ, D ⊆ block → block.card ≤ 2 * D.card → Covers D lo hi

lemma robustSquareBlock_of_indexed_cover {G lo hi : ℕ}
    (hcover : ∀ I : Finset (Fin G × Fin 3),
      3 * G ≤ 2 * I.card → Covers (indexedSquareValues I) lo hi) :
    RobustSquareBlock
      (indexedSquareValues
        (Finset.univ : Finset (Fin G × Fin 3))) lo hi := by
  classical
  intro D hD hDcard
  let I : Finset (Fin G × Fin 3) :=
    Finset.univ.filter fun p ↦ (tripleRoot G p.1 p.2) ^ 2 ∈ D
  have hIvalues : indexedSquareValues I = D :=
    indexedSquareValues_filter_mem_eq D hD
  have hIcard : I.card = D.card := by
    rw [← card_indexedSquareValues I, hIvalues]
  have hblockCard :
      (indexedSquareValues
        (Finset.univ : Finset (Fin G × Fin 3))).card = 3 * G := by
    rw [card_indexedSquareValues]
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    ring
  have hdenseI : 3 * G ≤ 2 * I.card := by
    rw [hIcard]
    rw [hblockCard] at hDcard
    exact hDcard
  rw [← hIvalues]
  exact hcover I hdenseI

/-- The explicit triple blocks are robust: every subset containing at least
half of the square values covers the same scale-dependent interval. -/
lemma ramseySquareBlock_robust (k : ℕ) :
    RobustSquareBlock (ramseySquareBlock k)
      (ramseyBlockLo k) (ramseyBlockHi k) := by
  change RobustSquareBlock
    (indexedSquareValues
      (Finset.univ : Finset
        (Fin (24 * 2 ^ ramseyExponent k) × Fin 3)))
    (ramseyBlockLo k) (ramseyBlockHi k)
  apply robustSquareBlock_of_indexed_cover
  intro I hI
  exact ramsey_dense_index_cover k hI

/-- In every two-colouring of a finite set, one colour class contains at
least half of the set.  The conclusion is cross-multiplied, so it handles
odd cardinalities without a rounding convention. -/
lemma exists_large_colourClass (block : Finset ℕ) (colour : ℕ → Fin 2) :
    ∃ i : Fin 2,
      block.card ≤ 2 * (block.filter fun q ↦ colour q = i).card := by
  classical
  let red := block.filter fun q ↦ colour q = (0 : Fin 2)
  let blue := block.filter fun q ↦ colour q = (1 : Fin 2)
  have hunion : red ∪ blue = block := by
    ext q
    simp only [red, blue, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hq, _⟩ | ⟨hq, _⟩) <;> exact hq
    · intro hq
      have hc : colour q = 0 ∨ colour q = 1 := by
        by_cases h0 : colour q = 0
        · exact Or.inl h0
        · right
          apply Fin.ext
          have hlt := (colour q).isLt
          simp only [Fin.val_one]
          omega
      exact hc.elim (fun h0 ↦ Or.inl ⟨hq, h0⟩)
        (fun h1 ↦ Or.inr ⟨hq, h1⟩)
  have hdisjoint : Disjoint red blue := by
    rw [Finset.disjoint_left]
    intro q hred hblue
    have h0 : colour q = (0 : Fin 2) := (Finset.mem_filter.mp hred).2
    have h1 : colour q = (1 : Fin 2) := (Finset.mem_filter.mp hblue).2
    simp [h0] at h1
  have hcard : red.card + blue.card = block.card := by
    rw [← Finset.card_union_of_disjoint hdisjoint, hunion]
  by_cases hred : block.card ≤ 2 * red.card
  · exact ⟨0, by simpa [red] using hred⟩
  · refine ⟨1, ?_⟩
    have : block.card ≤ 2 * blue.card := by omega
    simpa [blue] using this

/-- Robustness converts the majority colour class into the local Ramsey
property required by `HasRamseySquareBlocks`. -/
lemma exists_monochromatic_cover_of_robust
    {block : Finset ℕ} {lo hi : ℕ}
    (hrobust : RobustSquareBlock block lo hi)
    (colour : ℕ → Fin 2) :
    ∃ i : Fin 2, ∃ D : Finset ℕ,
      D ⊆ block ∧ (∀ q ∈ D, colour q = i) ∧ Covers D lo hi := by
  obtain ⟨i, hi⟩ := exists_large_colourClass block colour
  let D := block.filter fun q ↦ colour q = i
  refine ⟨i, D, Finset.filter_subset _ _, ?_, hrobust D
    (Finset.filter_subset _ _) hi⟩
  intro q hq
  exact (Finset.mem_filter.mp hq).2

/-- A family of finite square blocks, with one target interval assigned to
each block, has the exact local Ramsey property needed for concatenation. -/
def HasRamseySquareBlocks (block : ℕ → Finset ℕ) (lo hi : ℕ → ℕ) : Prop :=
  (∀ k q, q ∈ block k → IsPositiveSquare q) ∧
  ∀ k (colour : ℕ → Fin 2),
    ∃ i : Fin 2, ∃ D : Finset ℕ,
      D ⊆ block k ∧
      (∀ q ∈ D, colour q = i) ∧
      Covers D (lo k) (hi k)

/-- The target intervals of a block family cover a tail of the naturals. -/
def BlockIntervalsCoverTail (lo hi : ℕ → ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ k : ℕ, lo k ≤ n ∧ n ≤ hi k

/-- A convenient sufficient condition for consecutive integer intervals to
cover a tail: the first interval is nonempty, successive intervals overlap or
are adjacent, and their right endpoints are unbounded. -/
def OverlappingUnboundedIntervals (lo hi : ℕ → ℕ) : Prop :=
  lo 0 ≤ hi 0 ∧
  (∀ k : ℕ, lo (k + 1) ≤ hi k + 1) ∧
  ∀ n : ℕ, ∃ k : ℕ, n ≤ hi k

/-- Pointwise robust blocks of positive squares furnish the local block
property used by the final concatenation theorem. -/
lemma hasRamseySquareBlocks_of_robust
    {block : ℕ → Finset ℕ} {lo hi : ℕ → ℕ}
    (hsquare : ∀ k q, q ∈ block k → IsPositiveSquare q)
    (hrobust : ∀ k, RobustSquareBlock (block k) (lo k) (hi k)) :
    HasRamseySquareBlocks block lo hi := by
  refine ⟨hsquare, ?_⟩
  intro k colour
  exact exists_monochromatic_cover_of_robust (hrobust k) colour

lemma blockIntervalsCoverTail_of_overlappingUnbounded
    {lo hi : ℕ → ℕ} (h : OverlappingUnboundedIntervals lo hi) :
    BlockIntervalsCoverTail lo hi := by
  refine ⟨lo 0, ?_⟩
  intro n hn
  let k := Nat.find (h.2.2 n)
  have hright : n ≤ hi k := Nat.find_spec (h.2.2 n)
  refine ⟨k, ?_, hright⟩
  by_cases hk : k = 0
  · simpa [hk] using hn
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    let j := k - 1
    have hkj : k = j + 1 := by
      dsimp [j]
      omega
    have hminimal : ¬n ≤ hi j := by
      intro hj
      have hjk : j < k := by dsimp [j]; omega
      exact (Nat.find_min (h.2.2 n) hjk) hj
    rw [hkj]
    exact (h.2.1 j).trans (by omega)

lemma monochromaticSquareSum_of_block
    {block D : Finset ℕ} {lo hi n : ℕ} {colour : ℕ → Fin 2} {i : Fin 2}
    (hblock : ∀ q ∈ block, IsPositiveSquare q)
    (hD : D ⊆ block) (hmono : ∀ q ∈ D, colour q = i)
    (hcover : Covers D lo hi) (hlo : lo ≤ n) (hhi : n ≤ hi) :
    MonochromaticSquareSum colour n := by
  obtain ⟨T, hTD, hsum⟩ :=
    Finset.mem_subsetSum_iff.mp (hcover n hlo hhi)
  refine ⟨T, ?_, ⟨i, ?_⟩, hsum⟩
  · intro q hq
    exact hblock q (hD (hTD hq))
  · intro q hq
    exact hmono q (hTD hq)

/-- Pure deterministic concatenation: robust monochromatic square blocks
whose intervals cover a tail imply the exact assertion of Problem 843. -/
theorem squaresRamseyTwoComplete_of_blocks
    {block : ℕ → Finset ℕ} {lo hi : ℕ → ℕ}
    (hblocks : HasRamseySquareBlocks block lo hi)
    (htail : BlockIntervalsCoverTail lo hi) :
    SquaresRamseyTwoComplete := by
  intro colour
  obtain ⟨N, hN⟩ := htail
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨k, hlo, hhi⟩ := hN n hn
  obtain ⟨i, D, hD, hmono, hcover⟩ := hblocks.2 k colour
  exact monochromaticSquareSum_of_block
    (fun q hq ↦ hblocks.1 k q hq) hD hmono hcover hlo hhi

/-- The exact deterministic endpoint for the analytic construction: a
sequence of robust positive-square blocks with overlapping unbounded target
intervals proves Problem 843. -/
theorem squaresRamseyTwoComplete_of_robust_blocks
    {block : ℕ → Finset ℕ} {lo hi : ℕ → ℕ}
    (hsquare : ∀ k q, q ∈ block k → IsPositiveSquare q)
    (hrobust : ∀ k, RobustSquareBlock (block k) (lo k) (hi k))
    (hoverlap : OverlappingUnboundedIntervals lo hi) :
    SquaresRamseyTwoComplete := by
  apply squaresRamseyTwoComplete_of_blocks
    (hasRamseySquareBlocks_of_robust hsquare hrobust)
  exact blockIntervalsCoverTail_of_overlappingUnbounded hoverlap

/-- Every member of a family of full indexed blocks is a positive square. -/
lemma indexedFullBlocks_are_positive_squares (G : ℕ → ℕ) (k q : ℕ)
    (hq : q ∈ indexedSquareValues
      (Finset.univ : Finset (Fin (G k) × Fin 3))) : IsPositiveSquare q :=
  indexedSquareValues_are_positive_squares hq

lemma ramseyBlockIntervals_overlappingUnbounded :
    OverlappingUnboundedIntervals ramseyBlockLo ramseyBlockHi := by
  refine ⟨ramseyBlockLo_le_hi 0, ?_, ramseyBlockHi_unbounded⟩
  intro k
  exact (ramseyBlockLo_succ_le_hi k).trans (Nat.le_add_right _ 1)

/-- Resolution of Erdős Problem 843: in every two-colouring of the positive
square values, every sufficiently large natural number is a sum of distinct
squares of one colour. -/
theorem erdos_843 : (∀ colour : ℕ → Fin 2, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
  Erdos843.MonochromaticSquareSum colour n) := by
  apply squaresRamseyTwoComplete_of_robust_blocks
    (block := fun k ↦ indexedSquareValues
      (Finset.univ : Finset (Fin (ramseyGroupCount k) × Fin 3)))
    (lo := ramseyBlockLo) (hi := ramseyBlockHi)
  · exact indexedFullBlocks_are_positive_squares ramseyGroupCount
  · intro k
    exact ramseySquareBlock_robust k
  · exact ramseyBlockIntervals_overlappingUnbounded

#print axioms erdos_843

end Erdos843
