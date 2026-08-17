/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos144.HarmonicOctaves
import ErdosProblems.Erdos144.HarmonicRegularity

/-!
# Largest-coordinate fibres in the harmonic energy estimate

This file supplies the concrete pieces of the largest-differing-coordinate
decomposition which are independent of the final reindexing of the finite
expectation.  The key point is that, after the lower pair-state profile and
the unequal local state pair are fixed, the balancing coordinate is unique.
In the harmonic model the selections of its preceding coordinate `M` and of
the forced coordinate therefore cost at most `1 / M^2`.

The second part defines the eight-adic octave contributions and proves the
two estimates required by `HarmonicOctaves.octave_contribution_sum_le`.
-/

open scoped BigOperators

namespace Erdos144.HarmonicDecomposition

noncomputable section

attribute [local instance] Classical.propDecidable

open HarmonicBlocks HarmonicOctaves

/-! ## Exact harmonic deletion identities -/

/-- Removing a selected coordinate changes its harmonic Bernoulli weight by
the odds ratio `1/(n-1)`.  This is the exact identity used when the forced
largest coordinate is deleted from a collision witness. -/
theorem harmonic_weight_eq_inv_pred_mul_weight_erase
    {I S : Finset ℕ} {n : ℕ} (hnI : n ∈ I) (hnS : n ∈ S)
    (hn : 1 < n) :
    Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) S =
      (1 / ((n : ℝ) - 1)) *
        Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) (S.erase n) := by
  have hnerase : n ∉ S.erase n := by simp
  have hdiff : I \ (S.erase n) = insert n (I \ S) := by
    ext i
    by_cases hin : i = n
    · subst i
      simp [hnI, hnS]
    · simp [hin]
  rw [Erdos697.Bernoulli.weight, Erdos697.Bernoulli.weight,
    ← Finset.mul_prod_erase S (fun i ↦ 1 / (i : ℝ)) hnS, hdiff]
  have hnDiff : n ∉ I \ S := by simp [hnS]
  rw [Finset.prod_insert hnDiff]
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  field_simp [hn1]

/-- Normalized deletion identity.  Besides the odds ratio, deleting the
forced selected coordinate removes one factor `9` from the state-space
normalization. -/
theorem harmonic_normalized_weight_eq_erase
    {I S : Finset ℕ} {n : ℕ} (hnI : n ∈ I) (hnS : n ∈ S)
    (hn : 1 < n) :
    Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) S /
        (9 : ℝ) ^ S.card =
      (1 / (9 * ((n : ℝ) - 1))) *
        (Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) (S.erase n) /
          (9 : ℝ) ^ (S.erase n).card) := by
  rw [harmonic_weight_eq_inv_pred_mul_weight_erase hnI hnS hn]
  have hcard : S.card = (S.erase n).card + 1 := by
    rw [Finset.card_erase_of_mem hnS]
    have : 0 < S.card := Finset.card_pos.mpr ⟨n, hnS⟩
    omega
  rw [hcard, pow_succ]
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  field_simp [hn1]

/-- The total harmonic Bernoulli mass of subsets containing `M` is exactly
the one-coordinate inclusion probability `1/M`. -/
theorem sum_harmonic_weight_filter_mem_eq
    {I : Finset ℕ} {M : ℕ} (hMI : M ∈ I) :
    (∑ S ∈ I.powerset.filter (fun S ↦ M ∈ S),
      Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) S) =
      1 / (M : ℝ) := by
  have hmarg := Erdos144.HarmonicRegularity.prob_inter_eq I {M}
    (fun S : Finset ℕ ↦ M ∈ S) (by simpa using hMI)
  have hmarg' : HarmonicProb.prob I (fun T ↦ M ∈ T) =
      HarmonicProb.prob {M} (fun T ↦ M ∈ T) := by
    simpa only [Finset.mem_inter, Finset.mem_singleton, and_true] using hmarg
  calc
    (∑ S ∈ I.powerset.filter (fun S ↦ M ∈ S),
        Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) S) =
        HarmonicProb.prob I (fun S ↦ M ∈ S) := by
      rfl
    _ = HarmonicProb.prob {M} (fun S ↦ M ∈ S) := hmarg'
    _ = 1 / (M : ℝ) := by
      have hevent : ({M} : Finset ℕ).powerset.filter (fun S ↦ M ∈ S) =
          {{M}} := by
        ext T
        simp only [Finset.mem_filter, Finset.mem_powerset,
          Finset.mem_singleton]
        constructor
        · rintro ⟨hsub, hmem⟩
          apply Finset.Subset.antisymm hsub
          intro x hx
          have hxM : x = M := Finset.mem_singleton.mp hx
          subst x
          exact hmem
        · intro hT
          subst T
          exact ⟨Finset.Subset.rfl, Finset.mem_singleton_self M⟩
      rw [HarmonicProb.prob, hevent]
      simp [HarmonicProb.weight, HarmonicProb.param,
        Erdos697.Bernoulli.weight]

/-! ## Ordered collision witnesses -/

/-- Ordered distinct state pairs in one signed-value fibre, with the common
signed value retained as an index.  Retaining the fibre index makes the
cardinality computation a direct `Finset.card_sigma` calculation. -/
def orderedCollisionWitnesses (S : Finset ℕ) :
    Finset (Σ z : ℤ,
      {q // q ∈ ((signedStates S).filter fun a ↦ signedValue S a = z).offDiag}) :=
  (signedStates S).image (signedValue S) |>.sigma fun z ↦
    ((signedStates S).filter fun a ↦ signedValue S a = z).offDiag.attach

private theorem nat_sq_eq_self_add_two_mul_choose_two (m : ℕ) :
    m ^ 2 = m + 2 * m.choose 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        m.succ ^ 2 = m ^ 2 + 2 * m + 1 := by
          simp only [Nat.succ_eq_add_one]
          ring
        _ = (m + 2 * m.choose 2) + 2 * m + 1 := by rw [ih]
        _ = m.succ + 2 * m.succ.choose 2 := by
          rw [show (2 : ℕ) = Nat.succ 1 by rfl, Nat.choose_succ_succ,
            Nat.choose_one_right]
          simp only [Nat.succ_eq_add_one]
          ring

private theorem offDiag_card_eq_two_mul_choose_two
    {α : Type*} [DecidableEq α] (A : Finset α) :
    A.offDiag.card = 2 * A.card.choose 2 := by
  rw [Finset.offDiag_card]
  have h := nat_sq_eq_self_add_two_mul_choose_two A.card
  simp only [pow_two] at h
  omega

/-- `offDiagonalSignedEnergy` is literally the number of ordered collision
witnesses. -/
theorem orderedCollisionWitnesses_card (S : Finset ℕ) :
    (orderedCollisionWitnesses S).card = offDiagonalSignedEnergy S := by
  rw [orderedCollisionWitnesses, Finset.card_sigma]
  simp_rw [Finset.card_attach, offDiag_card_eq_two_mul_choose_two]
  rw [← Finset.mul_sum]
  rfl

/-- All ordered collision witnesses over subsets in a supplied event. -/
def eventCollisionWitnesses (I : Finset ℕ) (Good : Finset ℕ → Prop)
    [DecidablePred Good] :
    Finset (Σ S : Finset ℕ,
      {w // w ∈ orderedCollisionWitnesses S}) :=
  (I.powerset.filter Good).sigma fun S ↦
    (orderedCollisionWitnesses S).attach

theorem eventCollisionWitness_set_subset
    {I : Finset ℕ} {Good : Finset ℕ → Prop} [DecidablePred Good]
    {w : Σ S : Finset ℕ, {u // u ∈ orderedCollisionWitnesses S}}
    (hw : w ∈ eventCollisionWitnesses I Good) :
    w.1 ⊆ I := by
  rw [eventCollisionWitnesses, Finset.mem_sigma] at hw
  exact Finset.mem_powerset.mp (Finset.mem_filter.mp hw.1).1

theorem eventCollisionWitness_good
    {I : Finset ℕ} {Good : Finset ℕ → Prop} [DecidablePred Good]
    {w : Σ S : Finset ℕ, {u // u ∈ orderedCollisionWitnesses S}}
    (hw : w ∈ eventCollisionWitnesses I Good) :
    Good w.1 := by
  rw [eventCollisionWitnesses, Finset.mem_sigma] at hw
  exact (Finset.mem_filter.mp hw.1).2

/-- Left ternary state carried by an ordered collision witness. -/
def collisionWitnessLeft {S : Finset ℕ}
    (w : Σ z : ℤ,
      {q // q ∈ ((signedStates S).filter fun a ↦ signedValue S a = z).offDiag}) :
    ↑S → Fin 3 :=
  w.2.val.1

/-- Right ternary state carried by an ordered collision witness. -/
def collisionWitnessRight {S : Finset ℕ}
    (w : Σ z : ℤ,
      {q // q ∈ ((signedStates S).filter fun a ↦ signedValue S a = z).offDiag}) :
    ↑S → Fin 3 :=
  w.2.val.2

theorem collisionWitnessLeft_ne_right {S : Finset ℕ}
    (w : Σ z : ℤ,
      {q // q ∈ ((signedStates S).filter fun a ↦ signedValue S a = z).offDiag}) :
    collisionWitnessLeft w ≠ collisionWitnessRight w := by
  have hw := w.2.property
  simpa [collisionWitnessLeft, collisionWitnessRight] using
    (Finset.mem_offDiag.mp hw).2.2

theorem collisionWitness_signedValue_eq {S : Finset ℕ}
    (w : Σ z : ℤ,
      {q // q ∈ ((signedStates S).filter fun a ↦ signedValue S a = z).offDiag}) :
    signedValue S (collisionWitnessLeft w) =
      signedValue S (collisionWitnessRight w) := by
  have hw := w.2.property
  have hleft := Finset.mem_filter.mp (Finset.mem_offDiag.mp hw).1
  have hright := Finset.mem_filter.mp (Finset.mem_offDiag.mp hw).2.1
  exact hleft.2.trans hright.2.symm

/-- Exact expansion of the normalized off-diagonal expectation as a sum
over ordered balanced state-pair witnesses.  This is the starting point of
the largest-coordinate reindexing. -/
theorem normalizedOffDiagonalExpectation_eq_witness_sum
    (I : Finset ℕ) (Good : Finset ℕ → Prop) [DecidablePred Good] :
    normalizedOffDiagonalExpectation I Good =
      ∑ w ∈ eventCollisionWitnesses I Good,
        Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) w.1 /
          (9 : ℝ) ^ w.1.card := by
  calc
    normalizedOffDiagonalExpectation I Good =
        ∑ S ∈ I.powerset.filter Good,
          ∑ _w ∈ (orderedCollisionWitnesses S).attach,
            Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) S /
              (9 : ℝ) ^ S.card := by
      rw [normalizedOffDiagonalExpectation]
      rw [Finset.sum_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro S hS
      by_cases hGood : Good S
      · simp only [hGood, if_true]
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_attach]
        rw [orderedCollisionWitnesses_card]
        push_cast
        ring
      · simp [hGood]
    _ = ∑ w ∈ eventCollisionWitnesses I Good,
          Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) w.1 /
            (9 : ℝ) ^ w.1.card := by
      rw [eventCollisionWitnesses, Finset.sum_sigma]

/-! ## The forced balancing coordinate -/

/-- Candidate values of the largest differing coordinate after its unequal
local state pair and the contribution of all the other coordinates have
been fixed. -/
def forcedCoordinates (B : Finset ℕ) (x y : Fin 3) (z : ℤ) : Finset ℕ :=
  B.filter fun n ↦ signedTerm n x - signedTerm n y = z

theorem mem_forcedCoordinates_iff {B : Finset ℕ} {x y : Fin 3}
    {z : ℤ} {n : ℕ} :
    n ∈ forcedCoordinates B x y z ↔
      n ∈ B ∧ signedTerm n x - signedTerm n y = z := by
  simp [forcedCoordinates]

/-- The balancing equation has at most one possible coordinate for a fixed
unequal ordered pair of local ternary states. -/
theorem forcedCoordinates_card_le_one {B : Finset ℕ} {x y : Fin 3}
    (hxy : x ≠ y) (z : ℤ) :
    (forcedCoordinates B x y z).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro n hn m hm
  have hn' := (mem_forcedCoordinates_iff.mp hn).2
  have hm' := (mem_forcedCoordinates_iff.mp hm).2
  exact signedTerm_difference_injective hxy (hn'.trans hm'.symm)

/-- A harmonic sum over one forced-coordinate fibre is no larger than the
largest allowed summand.  This is the analytic content of uniqueness. -/
theorem harmonic_forcedCoordinates_sum_le
    {B : Finset ℕ} {M : ℕ} (hM : 0 < M)
    {x y : Fin 3} (hxy : x ≠ y) (z : ℤ)
    (hbelow : ∀ n ∈ B, M ≤ n) :
    (∑ n ∈ forcedCoordinates B x y z, 1 / (n : ℝ)) ≤
      1 / (M : ℝ) := by
  have hnonneg : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
  calc
    (∑ n ∈ forcedCoordinates B x y z, 1 / (n : ℝ)) ≤
        ∑ _n ∈ forcedCoordinates B x y z, 1 / (M : ℝ) := by
      gcongr with n hn
      have hnB := (mem_forcedCoordinates_iff.mp hn).1
      exact hbelow n hnB
    _ = ((forcedCoordinates B x y z).card : ℝ) * (1 / (M : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1 * (1 / (M : ℝ)) := by
      gcongr
      exact_mod_cast forcedCoordinates_card_le_one hxy z
    _ = 1 / (M : ℝ) := one_mul _

/-- Selecting the preceding coordinate `M` and the uniquely forced later
coordinate costs at most `1/M²` in the harmonic product measure. -/
theorem harmonic_two_selection_fibre_le_reciprocal_sq
    {B : Finset ℕ} {M : ℕ} (hM : 0 < M)
    {x y : Fin 3} (hxy : x ≠ y) (z : ℤ)
    (hbelow : ∀ n ∈ B, M ≤ n) :
    (1 / (M : ℝ)) *
        (∑ n ∈ forcedCoordinates B x y z, 1 / (n : ℝ)) ≤
      1 / (M : ℝ) ^ 2 := by
  calc
    (1 / (M : ℝ)) *
          (∑ n ∈ forcedCoordinates B x y z, 1 / (n : ℝ)) ≤
        (1 / (M : ℝ)) * (1 / (M : ℝ)) := by
      gcongr
      exact harmonic_forcedCoordinates_sum_le hM hxy z hbelow
    _ = 1 / (M : ℝ) ^ 2 := by ring

/-! ## Deterministic predecessor and diagonal tail -/

/-- Selected coordinates strictly below `n`. -/
def selectedBelow {S : Finset ℕ} (n : ↑S) : Finset ↑S :=
  Finset.univ.filter fun i ↦ i < n

theorem mem_selectedBelow_iff {S : Finset ℕ} {n i : ↑S} :
    i ∈ selectedBelow n ↔ i < n := by
  simp [selectedBelow]

/-- At a positive coordinate, the three signed local values are distinct. -/
theorem signedTerm_injective_of_pos {n : ℕ} (hn : 0 < n) :
    Function.Injective (signedTerm n) := by
  intro x y hxy
  fin_cases x <;> fin_cases y <;> simp_all [signedTerm] <;> omega

/-- A balanced non-diagonal pair has a selected coordinate below its
largest differing coordinate. -/
theorem selectedBelow_largestDifferingCoordinate_nonempty
    {S : Finset ℕ} {a b : (↑S → Fin 3)} (hab : a ≠ b)
    (hbal : signedValue S a = signedValue S b)
    (hpos : ∀ n ∈ S, 0 < n) :
    (selectedBelow (largestDifferingCoordinate a b hab)).Nonempty := by
  let L := largestDifferingCoordinate a b hab
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have hnotbelow : ∀ i : ↑S, ¬ i < L := by
    intro i hi
    have : i ∈ selectedBelow L := (mem_selectedBelow_iff).2 hi
    rw [hempty] at this
    simpa using this
  have heq_of_ne : ∀ i : ↑S, i ≠ L → a i = b i := by
    intro i hiL
    have hLi : L < i := lt_of_le_of_ne (not_lt.mp (hnotbelow i))
      (Ne.symm hiL)
    exact eq_above_largestDifferingCoordinate hab hLi
  have hsum :
      signedTerm L.1 (a L) - signedTerm L.1 (b L) = 0 := by
    have hzero :
        (∑ i : ↑S, (signedTerm i.1 (a i) - signedTerm i.1 (b i))) = 0 := by
      rw [Finset.sum_sub_distrib]
      simpa [signedValue] using sub_eq_zero.mpr hbal
    have hsplit := Finset.sum_erase_add
      (s := (Finset.univ : Finset ↑S))
      (f := fun i ↦ signedTerm i.1 (a i) - signedTerm i.1 (b i))
      (Finset.mem_univ L)
    have herase :
        (∑ i ∈ (Finset.univ : Finset ↑S).erase L,
          (signedTerm i.1 (a i) - signedTerm i.1 (b i))) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hiL : i ≠ L := (Finset.mem_erase.mp hi).1
      rw [heq_of_ne i hiL, sub_self]
    rw [herase, zero_add] at hsplit
    linarith
  have hterm : signedTerm L.1 (a L) = signedTerm L.1 (b L) :=
    sub_eq_zero.mp hsum
  have hLpos : 0 < L.1 := hpos L.1 L.2
  exact largestDifferingCoordinate_ne hab
    (signedTerm_injective_of_pos hLpos hterm)

/-- The greatest selected coordinate below the largest differing coordinate. -/
def precedingSelectedCoordinate {S : Finset ℕ} {a b : (↑S → Fin 3)}
    (hab : a ≠ b) (hbal : signedValue S a = signedValue S b)
    (hpos : ∀ n ∈ S, 0 < n) : ↑S :=
  (selectedBelow (largestDifferingCoordinate a b hab)).max'
    (selectedBelow_largestDifferingCoordinate_nonempty hab hbal hpos)

theorem precedingSelectedCoordinate_lt_largest {S : Finset ℕ}
    {a b : (↑S → Fin 3)} (hab : a ≠ b)
    (hbal : signedValue S a = signedValue S b)
    (hpos : ∀ n ∈ S, 0 < n) :
    precedingSelectedCoordinate hab hbal hpos <
      largestDifferingCoordinate a b hab := by
  exact mem_selectedBelow_iff.mp <|
    Finset.max'_mem _ _

/-- There is no selected coordinate strictly between the predecessor `M`
and the largest differing coordinate. -/
theorem no_selected_between_predecessor_and_largest {S : Finset ℕ}
    {a b : (↑S → Fin 3)} (hab : a ≠ b)
    (hbal : signedValue S a = signedValue S b)
    (hpos : ∀ n ∈ S, 0 < n) {i : ↑S}
    (hMi : precedingSelectedCoordinate hab hbal hpos < i)
    (hiL : i < largestDifferingCoordinate a b hab) : False := by
  let L := largestDifferingCoordinate a b hab
  let M := precedingSelectedCoordinate hab hbal hpos
  have hiMem : i ∈ selectedBelow L := mem_selectedBelow_iff.mpr hiL
  have hiM : i ≤ M := Finset.le_max' _ _ hiMem
  exact (not_le_of_gt hMi) hiM

/-- Selected coordinates strictly above `n`.  For the largest differing
coordinate, the two ternary states agree on this entire set. -/
def selectedAbove {S : Finset ℕ} (n : ↑S) : Finset ℕ :=
  S.filter fun i ↦ n.1 < i

theorem mem_selectedAbove_iff {S : Finset ℕ} {n : ↑S} {i : ℕ} :
    i ∈ selectedAbove n ↔ i ∈ S ∧ n.1 < i := by
  simp [selectedAbove]

theorem equal_on_selectedAbove_largest {S : Finset ℕ}
    {a b : (↑S → Fin 3)} (hab : a ≠ b) {i : ℕ}
    (hi : i ∈ selectedAbove (largestDifferingCoordinate a b hab)) :
    a ⟨i, (mem_selectedAbove_iff.mp hi).1⟩ =
      b ⟨i, (mem_selectedAbove_iff.mp hi).1⟩ := by
  apply eq_above_largestDifferingCoordinate hab
  exact (mem_selectedAbove_iff.mp hi).2

/-- An eight-adic tail starting above the predecessor consists only of the
largest differing coordinate and coordinates above it. -/
theorem regularTail_subset_largest_insert_selectedAbove
    {S : Finset ℕ} {a b : (↑S → Fin 3)} (hab : a ≠ b)
    (hbal : signedValue S a = signedValue S b)
    (hpos : ∀ n ∈ S, 0 < n) {D r : ℕ}
    (hMupper : (precedingSelectedCoordinate hab hbal hpos).1 ≤ D / 8 ^ r) :
    S ∩ Finset.Ioc (D / 8 ^ r) D ⊆
      insert (largestDifferingCoordinate a b hab).1
        (selectedAbove (largestDifferingCoordinate a b hab)) := by
  intro i hi
  rcases Finset.mem_inter.mp hi with ⟨hiS, hiIoc⟩
  have hiIoc' := Finset.mem_Ioc.mp hiIoc
  have hMi : (precedingSelectedCoordinate hab hbal hpos).1 < i :=
    lt_of_le_of_lt hMupper hiIoc'.1
  by_cases hiL : i = (largestDifferingCoordinate a b hab).1
  · simp [hiL]
  have hnotlt : ¬ i < (largestDifferingCoordinate a b hab).1 := by
    intro hiLt
    exact no_selected_between_predecessor_and_largest hab hbal hpos
      (i := ⟨i, hiS⟩) hMi hiLt
  have hLlt : (largestDifferingCoordinate a b hab).1 < i :=
    lt_of_le_of_ne (Nat.le_of_not_gt hnotlt) (Ne.symm hiL)
  simp [selectedAbove, hiS, hLlt]

/-- The tail count in `OctaveRegular` gives the exact number of diagonal
selected coordinates used in the high-octave estimate. -/
theorem two_mul_sub_le_one_add_selectedAbove_card
    {S : Finset ℕ} {a b : (↑S → Fin 3)} (hab : a ≠ b)
    (hbal : signedValue S a = signedValue S b)
    (hpos : ∀ n ∈ S, 0 < n) {D R s r : ℕ}
    (hregular : OctaveRegular D R s S)
    (hr : r ∈ Finset.Icc s R)
    (hMupper : (precedingSelectedCoordinate hab hbal hpos).1 ≤ D / 8 ^ r) :
    2 * (r - s) ≤
      1 + (selectedAbove (largestDifferingCoordinate a b hab)).card := by
  have htail := hregular r hr
  have hsub := regularTail_subset_largest_insert_selectedAbove
    hab hbal hpos hMupper
  have hcard := Finset.card_le_card hsub
  have hins :
      (insert (largestDifferingCoordinate a b hab).1
        (selectedAbove (largestDifferingCoordinate a b hab))).card ≤
        1 + (selectedAbove
          (largestDifferingCoordinate a b hab)).card := by
    have := Finset.card_insert_le
      (largestDifferingCoordinate a b hab).1
      (selectedAbove (largestDifferingCoordinate a b hab))
    omega
  omega

/-- The elementary conversion from the tail-cardinality inequality to the
normalized diagonal-state factor. -/
theorem diagonal_factor_le {q k : ℕ} (hq : 2 * k ≤ 1 + q) :
    (2 / 3 : ℝ) * (1 / (3 : ℝ) ^ q) ≤
      2 * (1 / (9 : ℝ) ^ k) := by
  have hp : (3 : ℝ) ^ (2 * k) ≤ (3 : ℝ) ^ (q + 1) := by
    apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
    simpa [add_comm] using hq
  have hinv : 1 / (3 : ℝ) ^ (q + 1) ≤
      1 / (3 : ℝ) ^ (2 * k) :=
    one_div_le_one_div_of_le (by positivity) hp
  calc
    (2 / 3 : ℝ) * (1 / (3 : ℝ) ^ q) =
        2 * (1 / (3 : ℝ) ^ (q + 1)) := by
      rw [pow_succ]
      field_simp
    _ ≤ 2 * (1 / (3 : ℝ) ^ (2 * k)) := by gcongr
    _ = 2 * (1 / (9 : ℝ) ^ k) := by
      rw [show 2 * k = k * 2 by omega, pow_mul]
      congr 2
      rw [show (9 : ℝ) = 3 * 3 by norm_num, mul_pow]
      ring

/-- Concrete high-octave diagonal factor obtained from `OctaveRegular`. -/
theorem regular_diagonal_factor_le
    {S : Finset ℕ} {a b : (↑S → Fin 3)} (hab : a ≠ b)
    (hbal : signedValue S a = signedValue S b)
    (hpos : ∀ n ∈ S, 0 < n) {D R s r : ℕ}
    (hregular : OctaveRegular D R s S)
    (hr : r ∈ Finset.Icc s R)
    (hMupper : (precedingSelectedCoordinate hab hbal hpos).1 ≤ D / 8 ^ r) :
    (2 / 3 : ℝ) *
        (1 / (3 : ℝ) ^
          (selectedAbove (largestDifferingCoordinate a b hab)).card) ≤
      2 * (1 / (9 : ℝ) ^ (r - s)) := by
  exact diagonal_factor_le <|
    two_mul_sub_le_one_add_selectedAbove_card hab hbal hpos hregular hr hMupper

/-! ## Eight-adic octave sums -/

/-- The `r`-th octave, with endpoint conventions chosen so the octaves are
pairwise disjoint and telescope from `D` downwards. -/
def octave (D r : ℕ) : Finset ℕ :=
  Finset.Ioc (D / 8 ^ (r + 1)) (D / 8 ^ r)

theorem octave_card_real_le (D r : ℕ) :
    ((octave D r).card : ℝ) ≤ (D : ℝ) / (8 : ℝ) ^ r := by
  rw [octave, Nat.card_Ioc]
  have hnat : D / 8 ^ r - D / 8 ^ (r + 1) ≤ D / 8 ^ r :=
    Nat.sub_le _ _
  have hcast :
      ((D / 8 ^ r - D / 8 ^ (r + 1) : ℕ) : ℝ) ≤
        (D / 8 ^ r : ℕ) := by exact_mod_cast hnat
  refine hcast.trans ?_
  have hpR : (0 : ℝ) < (8 : ℝ) ^ r := by positivity
  apply (le_div_iff₀ hpR).2
  norm_cast
  exact Nat.div_mul_le_self D (8 ^ r)

theorem reciprocal_sq_le_octave_bound {D r M : ℕ} (hD : 0 < D)
    (hM : M ∈ octave D r) :
    1 / (M : ℝ) ^ 2 ≤ (((8 : ℝ) ^ (r + 1) / D) ^ 2) := by
  have hlow : D / 8 ^ (r + 1) < M := (Finset.mem_Ioc.mp hM).1
  have hpNat : 0 < 8 ^ (r + 1) := by positivity
  have hDle : D < M * 8 ^ (r + 1) :=
    (Nat.div_lt_iff_lt_mul hpNat).mp hlow
  have hMpos : 0 < M := by
    by_contra hMz
    have : M = 0 := Nat.eq_zero_of_not_pos hMz
    simp [this] at hDle
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hmain : (D : ℝ) ≤ M * (8 : ℝ) ^ (r + 1) := by
    exact_mod_cast hDle.le
  have hinv : 1 / (M : ℝ) ≤ (8 : ℝ) ^ (r + 1) / D := by
    rw [div_le_div_iff₀ hMR hDR]
    simpa [mul_comm] using hmain
  calc
    1 / (M : ℝ) ^ 2 = (1 / (M : ℝ)) ^ 2 := by ring
    _ ≤ ((8 : ℝ) ^ (r + 1) / D) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).2 hinv

/-- Concrete reciprocal-square mass bound for one harmonic octave. -/
theorem octave_reciprocalSquare_sum_le {D : ℕ} (r : ℕ) (hD : 0 < D) :
    (∑ M ∈ octave D r, 1 / (M : ℝ) ^ 2) ≤
      64 * (8 : ℝ) ^ r / D := by
  exact reciprocalSquare_octave_sum_le r hD
    (octave_card_real_le D r)
    (fun M hM ↦ reciprocal_sq_le_octave_bound hD hM)

/-- The crude contribution before the regularity cutoff. -/
def lowContribution (D r : ℕ) : ℝ :=
  (2 / 3 : ℝ) * ∑ M ∈ octave D r, 1 / (M : ℝ) ^ 2

/-- The contribution in octave `s+k`, where regularity supplies at least
`2k-1` diagonal selected coordinates above the largest differing one. -/
def highContribution (D s k : ℕ) : ℝ :=
  2 * (9 : ℝ) ^ (-(k : ℤ)) *
    ∑ M ∈ octave D (s + k), 1 / (M : ℝ) ^ 2

theorem lowContribution_le {D s r : ℕ} (hD : 0 < D) (_hr : r < s) :
    lowContribution D r ≤
      (128 / 3 : ℝ) * (8 : ℝ) ^ r / D := by
  unfold lowContribution
  calc
    (2 / 3 : ℝ) * ∑ M ∈ octave D r, 1 / (M : ℝ) ^ 2 ≤
        (2 / 3 : ℝ) * (64 * (8 : ℝ) ^ r / D) := by
      gcongr
      exact octave_reciprocalSquare_sum_le r hD
    _ = (128 / 3 : ℝ) * (8 : ℝ) ^ r / D := by ring

theorem highContribution_le {D s N k : ℕ} (hD : 0 < D) (_hk : k < N) :
    highContribution D s k ≤
      128 * (8 : ℝ) ^ s / D * ((8 : ℝ) / 9) ^ k := by
  unfold highContribution
  have h9 : (9 : ℝ) ^ (-(k : ℤ)) = 1 / (9 : ℝ) ^ k := by
    rw [zpow_neg, zpow_natCast]
    simp [one_div]
  rw [h9]
  calc
    2 * (1 / (9 : ℝ) ^ k) *
          ∑ M ∈ octave D (s + k), 1 / (M : ℝ) ^ 2 ≤
        2 * (1 / (9 : ℝ) ^ k) *
          (64 * (8 : ℝ) ^ (s + k) / D) := by
      gcongr
      exact octave_reciprocalSquare_sum_le (s + k) hD
    _ = 128 * (8 : ℝ) ^ s / D * ((8 : ℝ) / 9) ^ k := by
      rw [pow_add, div_pow]
      field_simp
      ring

/-- Once the expectation has been reindexed into its concrete low and high
octave contributions, all remaining analytic estimates are discharged. -/
theorem normalizedOffDiagonalExpectation_le_of_concrete_decomposition
    {I : Finset ℕ} {Good : Finset ℕ → Prop}
    {D s N : ℕ} (hD : 0 < D)
    (hdecomp : normalizedOffDiagonalExpectation I Good ≤
      (∑ r ∈ Finset.range s, lowContribution D r) +
        ∑ k ∈ Finset.range N, highContribution D s k) :
    normalizedOffDiagonalExpectation I Good ≤
      1200 * (8 : ℝ) ^ s / D := by
  exact normalizedOffDiagonalExpectation_le_of_octave_decomposition hD hdecomp
    (fun r hr ↦ lowContribution_le hD hr)
    (fun k hk ↦ highContribution_le hD hk)

end

end Erdos144.HarmonicDecomposition
