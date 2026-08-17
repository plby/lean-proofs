/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos874.RestrictedGrowth

/-!
# Popular pair sums for Erdős Problem 874

This file formalizes the elementary counting bridge in Proposition 4 of
Deshouillers--Freiman (1995).  Given `B = {b₀ < ... < b_(L-1)}`, we count
the pairs `bᵢ + b_(i+d+1)` with `i < L-u` and `d < u`.  There are exactly
`(L-u)u` such pairs, while at most `(u+1)/2` of them have the same sum.

The constants as printed in the paper have a small numerical defect.  The
formal proof repairs it by taking the even width `u = 2 floor (L/500)` and
the representation reserve `v = 2 floor (L/10^6) + 1`.  This proves the
intended exact inequality `99 L < 50 |S|`.  Every popular sum has more than
`v` distinct two-element representations, and `S+S` is contained in the
fourth restricted layer once `2 ≤ v`.
-/

open scoped BigOperators Pointwise

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Pair sums having more than `v` two-element representations in `B`. -/
def popularPairSums (B : Finset ℤ) (v : ℕ) : Finset ℤ :=
  (restrictedSumset 2 B).filter fun z ↦ v < (pairRepresentations B z).card

lemma mem_popularPairSums {B : Finset ℤ} {v : ℕ} {z : ℤ} :
    z ∈ popularPairSums B v ↔
      z ∈ restrictedSumset 2 B ∧ v < (pairRepresentations B z).card := by
  simp [popularPairSums]

lemma popularPairSums_pair_rich (B : Finset ℤ) (v : ℕ) :
    ∀ z ∈ popularPairSums B v, v < (pairRepresentations B z).card := by
  intro z hz
  exact (mem_popularPairSums.mp hz).2

/-- If a pair sum has more than two representations, one of its representing
pairs avoids any prescribed representing pair of another sum. -/
theorem add_popularPairSums_subset_restrictedSumset_four
    {B : Finset ℤ} {v : ℕ} (hv : 2 ≤ v) :
    popularPairSums B v + popularPairSums B v ⊆ restrictedSumset 4 B := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
  have hxrich := popularPairSums_pair_rich B v x hx
  obtain ⟨P, hPrep⟩ := Finset.card_pos.mp
    (by omega : 0 < (pairRepresentations B x).card)
  obtain ⟨hPB, hPcard, hPsum⟩ := mem_pairRepresentations.mp hPrep
  have hP_lt : P.card < (pairRepresentations B y).card := by
    rw [hPcard]
    exact hv.trans_lt (popularPairSums_pair_rich B v y hy)
  obtain ⟨Q, hQrep, hQP⟩ := exists_pairRepresentation_disjoint hP_lt
  obtain ⟨hQB, hQcard, hQsum⟩ := mem_pairRepresentations.mp hQrep
  apply mem_restrictedSumset.mpr
  refine ⟨P ∪ Q, Finset.union_subset hPB hQB, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hQP.symm, hPcard, hQcard]
  · rw [Finset.sum_union hQP.symm, hPsum, hQsum]

/-- Every restricted two-sum is an ordinary two-fold sum. -/
lemma restrictedSumset_two_subset_add_self (B : Finset ℤ) :
    restrictedSumset 2 B ⊆ B + B := by
  intro z hz
  obtain ⟨P, hPB, hPcard, hPsum⟩ := mem_restrictedSumset.mp hz
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hPcard
  rw [show ∑ a ∈ {x, y}, a = x + y by simp [hxy]] at hPsum
  rw [← hPsum]
  exact Finset.mem_add.mpr ⟨x, hPB (by simp), y, hPB (by simp), rfl⟩

/-- The DF Proposition 3.3 estimate also controls the restricted two-layer. -/
lemma card_restrictedSumset_two_le_three_mul_add_four
    {B : Finset ℤ} (hB : 2 ≤ B.card) :
    (restrictedSumset 2 B).card ≤
      3 * B.card + (restrictedSumset 4 B).card := by
  exact (Finset.card_le_card (restrictedSumset_two_subset_add_self B)).trans
    (card_add_self_le_three_mul_add_card_restrictedSumset_four hB)

/-- Erasing one ground-set element destroys at most one representation of a
fixed pair sum. -/
lemma card_pairRepresentations_le_erase_add_one
    (B : Finset ℤ) (z b : ℤ) :
    (pairRepresentations B z).card ≤
      (pairRepresentations (B.erase b) z).card + 1 := by
  let R := pairRepresentations B z
  let R₀ := R.filter fun P ↦ b ∉ P
  let R₁ := R.filter fun P ↦ b ∈ P
  have hR₀ : R₀ ⊆ pairRepresentations (B.erase b) z := by
    intro P hP
    have hP' := Finset.mem_filter.mp hP
    obtain ⟨hPB, hPcard, hPsum⟩ := mem_pairRepresentations.mp hP'.1
    exact mem_pairRepresentations.mpr
      ⟨fun x hx ↦ Finset.mem_erase.mpr ⟨by
          rintro rfl
          exact hP'.2 hx, hPB hx⟩,
        hPcard, hPsum⟩
  have hR₀card : R₀.card ≤ (pairRepresentations (B.erase b) z).card :=
    Finset.card_le_card hR₀
  have hR₁card : R₁.card ≤ 1 := by
    exact card_pairRepresentations_filter_mem_le_one B z b
  have hpartition : R₀.card + R₁.card = R.card := by
    simpa [R₀, R₁] using
      (Finset.card_filter_add_card_filter_not (s := R) fun P ↦ b ∉ P)
  dsimp [R, R₀, R₁] at hR₀card hR₁card hpartition ⊢
  omega

/-! ## The short-index pair family -/

/-- The parameter set for the `(L-u)u` short-index pairs. -/
abbrev NearIndex (B : Finset ℤ) (u : ℕ) := Fin (B.card - u) × Fin u

/-- The unordered pair with sorted indices `i` and `i+d+1`. -/
def nearIndexPair (B : Finset ℤ) (u : ℕ) (hu : u ≤ B.card)
    (p : NearIndex B u) : Finset ℤ :=
  let e : Fin B.card ↪o ℤ := B.orderEmbOfFin rfl
  {e ⟨p.1, by omega⟩, e ⟨p.1 + p.2 + 1, by omega⟩}

private lemma nearIndexPair_indices_lt (B : Finset ℤ) (u : ℕ)
    (_hu : u ≤ B.card) (p : NearIndex B u) :
    (p.1 : ℕ) < p.1 + p.2 + 1 := by omega

lemma nearIndexPair_card (B : Finset ℤ) (u : ℕ) (hu : u ≤ B.card)
    (p : NearIndex B u) :
    (nearIndexPair B u hu p).card = 2 := by
  rw [nearIndexPair, Finset.card_pair]
  intro h
  have hinj := (B.orderEmbOfFin rfl).injective h
  have hinj' := congrArg Fin.val hinj
  have hlt := nearIndexPair_indices_lt B u hu p
  exact (Nat.ne_of_lt hlt) hinj'

lemma nearIndexPair_subset (B : Finset ℤ) (u : ℕ) (hu : u ≤ B.card)
    (p : NearIndex B u) :
    nearIndexPair B u hu p ⊆ B := by
  intro x hx
  simp only [nearIndexPair, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact B.orderEmbOfFin_mem rfl _
  · exact B.orderEmbOfFin_mem rfl _

lemma nearIndexPair_injective (B : Finset ℤ) (u : ℕ) (hu : u ≤ B.card) :
    Function.Injective (nearIndexPair B u hu) := by
  intro p q hpq
  let e : Fin B.card ↪o ℤ := B.orderEmbOfFin rfl
  let pi : Fin B.card := ⟨p.1, by omega⟩
  let pj : Fin B.card := ⟨p.1 + p.2 + 1, by omega⟩
  let qi : Fin B.card := ⟨q.1, by omega⟩
  let qj : Fin B.card := ⟨q.1 + q.2 + 1, by omega⟩
  have hpilt : pi < pj := by
    exact_mod_cast nearIndexPair_indices_lt B u hu p
  have hqilt : qi < qj := by
    exact_mod_cast nearIndexPair_indices_lt B u hu q
  have hpq' : ({e pi, e pj} : Finset ℤ) = {e qi, e qj} := by
    simpa [nearIndexPair, e, pi, pj, qi, qj] using hpq
  have hpi : e pi ∈ ({e qi, e qj} : Finset ℤ) := by
    rw [← hpq']
    simp
  have hpj : e pj ∈ ({e qi, e qj} : Finset ℤ) := by
    rw [← hpq']
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hpi hpj
  have hi : pi = qi := by
    rcases hpi with hpi | hpi
    · exact e.injective hpi
    · have hpqj : pi = qj := e.injective hpi
      rcases hpj with hpj | hpj
      · have hpjqi : pj = qi := e.injective hpj
        omega
      · have : pj = qj := e.injective hpj
        omega
  have hj : pj = qj := by
    rcases hpj with hpj | hpj
    · have : pj = qi := e.injective hpj
      omega
    · exact e.injective hpj
  apply Prod.ext
  · exact Fin.ext (by
      simpa [pi, qi] using congrArg Fin.val hi)
  · apply Fin.ext_iff.mpr
    have hi' := congrArg Fin.val hi
    have hj' := congrArg Fin.val hj
    dsimp [pi, pj, qi, qj] at hi' hj'
    omega

/-- The concrete family of short-index unordered pairs. -/
def nearIndexPairs (B : Finset ℤ) (u : ℕ) (hu : u ≤ B.card) :
    Finset (Finset ℤ) :=
  Finset.univ.image (nearIndexPair B u hu)

lemma card_nearIndexPairs (B : Finset ℤ) (u : ℕ) (hu : u ≤ B.card) :
    (nearIndexPairs B u hu).card = (B.card - u) * u := by
  rw [nearIndexPairs, Finset.card_image_of_injective _
    (nearIndexPair_injective B u hu)]
  simp

lemma mem_nearIndexPairs_pairRepresentation
    {B : Finset ℤ} {u : ℕ} (hu : u ≤ B.card)
    {P : Finset ℤ} (hP : P ∈ nearIndexPairs B u hu) :
    P ∈ pairRepresentations B (∑ x ∈ P, x) := by
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hP
  exact mem_pairRepresentations.mpr
    ⟨nearIndexPair_subset B u hu p, nearIndexPair_card B u hu p, rfl⟩

/-! ## A finite popularity-counting lemma -/

/-- The members of `T` whose two-element sum is `z`. -/
def pairSumFiber (T : Finset (Finset ℤ)) (z : ℤ) : Finset (Finset ℤ) :=
  T.filter fun P ↦ (∑ x ∈ P, x) = z

lemma mem_pairSumFiber {T : Finset (Finset ℤ)} {P : Finset ℤ} {z : ℤ} :
    P ∈ pairSumFiber T z ↔ P ∈ T ∧ (∑ x ∈ P, x) = z := by
  simp [pairSumFiber]

/-- Counting form of the popularity argument.  The first term accounts for
popular values, using the uniform fiber bound `w`; the second accounts for
the remaining restricted pair sums, each of which has at most `v`
representations in all of `B`. -/
theorem card_pairFamily_le_popular_mul_add_twoLayer_mul
    {B : Finset ℤ} {T : Finset (Finset ℤ)} {v w : ℕ}
    (hT : ∀ P ∈ T, P ∈ pairRepresentations B (∑ x ∈ P, x))
    (hfiber : ∀ z : ℤ, (pairSumFiber T z).card ≤ w) :
    T.card ≤ (popularPairSums B v).card * w +
      (restrictedSumset 2 B).card * v := by
  let S := popularPairSums B v
  let U := (restrictedSumset 2 B).filter fun z ↦ z ∉ S
  let Tp := T.filter fun P ↦ (∑ x ∈ P, x) ∈ S
  let Tu := T.filter fun P ↦ (∑ x ∈ P, x) ∉ S
  have hTpCover : Tp ⊆ S.biUnion (pairSumFiber T) := by
    intro P hP
    have hP' := Finset.mem_filter.mp hP
    exact Finset.mem_biUnion.mpr
      ⟨∑ x ∈ P, x, hP'.2, mem_pairSumFiber.mpr ⟨hP'.1, rfl⟩⟩
  have hTpCard : Tp.card ≤ S.card * w := by
    calc
      Tp.card ≤ (S.biUnion (pairSumFiber T)).card := Finset.card_le_card hTpCover
      _ ≤ ∑ z ∈ S, (pairSumFiber T z).card := Finset.card_biUnion_le
      _ ≤ ∑ _z ∈ S, w := Finset.sum_le_sum fun z _ ↦ hfiber z
      _ = S.card * w := by simp
  have hTuCover : Tu ⊆ U.biUnion (pairSumFiber T) := by
    intro P hP
    have hP' := Finset.mem_filter.mp hP
    have hPrep := hT P hP'.1
    have hzmem : (∑ x ∈ P, x) ∈ restrictedSumset 2 B :=
      mem_restrictedSumset.mpr
        ⟨P, (mem_pairRepresentations.mp hPrep).1,
          (mem_pairRepresentations.mp hPrep).2.1, rfl⟩
    exact Finset.mem_biUnion.mpr
      ⟨∑ x ∈ P, x, Finset.mem_filter.mpr ⟨hzmem, hP'.2⟩,
        mem_pairSumFiber.mpr ⟨hP'.1, rfl⟩⟩
  have hUfiber : ∀ z ∈ U, (pairSumFiber T z).card ≤ v := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    have hrepr : (pairRepresentations B z).card ≤ v := by
      by_contra h
      have hvlt : v < (pairRepresentations B z).card := by omega
      exact hz'.2 (mem_popularPairSums.mpr ⟨hz'.1, hvlt⟩)
    apply (Finset.card_le_card ?_).trans hrepr
    intro P hP
    have hPT := (mem_pairSumFiber.mp hP).1
    have hsum := (mem_pairSumFiber.mp hP).2
    simpa [hsum] using hT P hPT
  have hTuCard : Tu.card ≤ U.card * v := by
    calc
      Tu.card ≤ (U.biUnion (pairSumFiber T)).card := Finset.card_le_card hTuCover
      _ ≤ ∑ z ∈ U, (pairSumFiber T z).card := Finset.card_biUnion_le
      _ ≤ ∑ _z ∈ U, v := Finset.sum_le_sum hUfiber
      _ = U.card * v := by simp
  have hUcard : U.card ≤ (restrictedSumset 2 B).card :=
    Finset.card_filter_le _ _
  have hUcardMul : U.card * v ≤ (restrictedSumset 2 B).card * v :=
    Nat.mul_le_mul_right v hUcard
  have hpartition : Tp.card + Tu.card = T.card := by
    exact Finset.card_filter_add_card_filter_not _
  dsimp [S, U, Tp, Tu] at hTpCard hTuCard hUcardMul hpartition ⊢
  omega

/-! ## Exact numerical constants -/

lemma dfPopular_numeric
    {L q h D S : ℕ} (hL : 100000000 ≤ L)
    (hqLower : L < 500 * (q + 1)) (hqUpper : 500 * q ≤ L)
    (hh : 1000000 * h ≤ L) (hD : 5 * D ≤ 44 * L)
    (hcount : (L - 2 * q) * (2 * q) ≤ S * q + D * (2 * h + 1)) :
    99 * L < 50 * S := by
  by_contra hnot
  have hS : 50 * S ≤ 99 * L := by omega
  have hqpos : 0 < q := by omega
  have h2q : 2 * q ≤ L := by omega
  have hD9 : D ≤ 9 * L := by omega
  have hDv : D * (2 * h + 1) ≤ 9 * L * (2 * h + 1) := by
    exact Nat.mul_le_mul_right (2 * h + 1) hD9
  have hhL : 1000000 * (L * h) ≤ L * L := by
    nlinarith [Nat.mul_le_mul_left L hh]
  have hSq : 50 * (S * q) ≤ 99 * (L * q) := by
    nlinarith [Nat.mul_le_mul_right q hS]
  have hsub : L - 2 * q + 2 * q = L := Nat.sub_add_cancel h2q
  nlinarith

/-- The representation reserve used in the corrected DF95 counting bridge.
The extra `+1` allows one element of `B` to be reserved later. -/
def dfPairMultiplicity (B : Finset ℤ) : ℕ :=
  2 * (B.card / 1000000) + 1

/-- The explicit set of popular pair sums used by the DF95 engine. -/
def dfPopularPairSums (B : Finset ℤ) : Finset ℤ :=
  popularPairSums B (dfPairMultiplicity B)

lemma dfPopularPairSums_pair_rich (B : Finset ℤ) :
    ∀ z ∈ dfPopularPairSums B,
      dfPairMultiplicity B < (pairRepresentations B z).card := by
  exact popularPairSums_pair_rich B (dfPairMultiplicity B)

/-- Even after reserving one ground-set element, a DF-popular sum retains
more than `2 floor(|B|/10^6)` representations. -/
theorem dfPopularPairSums_pair_rich_erase
    {B : Finset ℤ} {z b : ℤ} (hz : z ∈ dfPopularPairSums B) :
    2 * (B.card / 1000000) <
      (pairRepresentations (B.erase b) z).card := by
  have hrich := dfPopularPairSums_pair_rich B z hz
  have herase := card_pairRepresentations_le_erase_add_one B z b
  dsimp [dfPairMultiplicity] at hrich
  omega

/-- The sum of two DF-popular pair sums is a genuine four-element sum. -/
theorem add_dfPopularPairSums_subset_four
    {B : Finset ℤ} (hB : 1000000 ≤ B.card) :
    dfPopularPairSums B + dfPopularPairSums B ⊆ restrictedSumset 4 B := by
  apply add_popularPairSums_subset_restrictedSumset_four
  dsimp [dfPairMultiplicity]
  omega

end

end Erdos874
