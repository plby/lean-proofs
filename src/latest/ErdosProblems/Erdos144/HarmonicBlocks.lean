/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos697.Erdos697Bernoulli
import ErdosProblems.Erdos448.Basic

/-!
# Deterministic block step for the harmonic random-set argument

This file isolates the additive bookkeeping in the Maier--Tenenbaum
global-to-local iteration.  A positive difference already represented by two
disjoint subsets of an exposed set is killed by selecting the fresh pair
`{n, n + m}`.  The fresh-pair encoding is injective, so the corresponding
two-point Bernoulli events can subsequently be summed without overlap.

No asymptotic or analytic estimate is used here.
-/

open scoped BigOperators

namespace Erdos144.HarmonicBlocks

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A finite set has two different subsets with the same sum. -/
def HasSubsetSumCollision (S : Finset ℕ) : Prop :=
  ∃ A B : Finset ℕ,
    A ⊆ S ∧ B ⊆ S ∧ A ≠ B ∧ A.sum id = B.sum id

/-- A positive signed difference represented by disjoint subsets of `S`. -/
def RepresentsPositiveDifference (S : Finset ℕ) (m : ℕ) : Prop :=
  ∃ A B : Finset ℕ,
    A ⊆ S ∧ B ⊆ S ∧ Disjoint A B ∧
      A.Nonempty ∧ B.Nonempty ∧ A.sum id = B.sum id + m

/-- A signed difference representation allowing a one-sided state.  After
the fresh-pair step both final subsets are automatically nonempty. -/
def RepresentsDifference (S : Finset ℕ) (m : ℕ) : Prop :=
  ∃ A B : Finset ℕ,
    A ⊆ S ∧ B ⊆ S ∧ Disjoint A B ∧ A.sum id = B.sum id + m

/-- The unordered two-point set used to kill a represented difference. -/
def freshPair (m n : ℕ) : Finset ℕ := {n, n + m}

@[simp] theorem mem_freshPair {m n x : ℕ} :
    x ∈ freshPair m n ↔ x = n ∨ x = n + m := by
  simp [freshPair]

theorem freshPair_card {m n : ℕ} (hm : 0 < m) :
    (freshPair m n).card = 2 := by
  have hne : n ≠ n + m := by omega
  rw [freshPair, Finset.card_insert_of_notMem]
  · simp
  · simpa using hne

/-- A positive pair `{n,n+m}` remembers both `n` and `m`.  This is the
disjointness input when the probabilities of exact fresh-pair events are
summed. -/
theorem freshPair_eq_iff {m n m' n' : ℕ} (hm : 0 < m) (hm' : 0 < m') :
    freshPair m n = freshPair m' n' ↔ n = n' ∧ m = m' := by
  constructor
  · intro h
    have hn : n = n' ∨ n = n' + m' := by
      have : n ∈ freshPair m' n' := by
        rw [← h]
        simp [freshPair]
      simpa [freshPair] using this
    have hnm : n + m = n' ∨ n + m = n' + m' := by
      have : n + m ∈ freshPair m' n' := by
        rw [← h]
        simp [freshPair]
      simpa [freshPair] using this
    omega
  · rintro ⟨rfl, rfl⟩
    rfl

theorem freshPair_injective_on_positive :
    Set.InjOn (fun q : ℕ × ℕ ↦ freshPair q.1 q.2)
      {q | 0 < q.1} := by
  intro a ha b hb hab
  exact Prod.ext (freshPair_eq_iff ha hb |>.mp hab).2
    (freshPair_eq_iff ha hb |>.mp hab).1

/-- Subset-sum collisions persist after enlarging the ambient set. -/
theorem HasSubsetSumCollision.mono {S T : Finset ℕ}
    (hST : S ⊆ T) (hS : HasSubsetSumCollision S) :
    HasSubsetSumCollision T := by
  rcases hS with ⟨A, B, hAS, hBS, hne, hsum⟩
  exact ⟨A, B, hAS.trans hST, hBS.trans hST, hne, hsum⟩

/-- The deterministic one-step mechanism in the global-to-local argument.

If `m` is represented by `A,B ⊆ S` as `sum A = sum B + m`, and the
two fresh points `n,n+m` are outside `S`, then adjoining them produces the
collision `A ∪ {n}` and `B ∪ {n+m}`. -/
theorem collision_of_representedDifference_and_freshPair
    {S : Finset ℕ} {m n : ℕ}
    (hm : 0 < m) (hrep : RepresentsPositiveDifference S m)
    (hn : n ∉ S) (hnm : n + m ∉ S) :
    HasSubsetSumCollision (S ∪ freshPair m n) := by
  rcases hrep with ⟨A, B, hAS, hBS, hdisj, hAne, hBne, hsum⟩
  refine ⟨insert n A, insert (n + m) B, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_union]
    rcases Finset.mem_insert.mp hx with rfl | hxA
    · exact Or.inr (by simp [freshPair])
    · exact Or.inl (hAS hxA)
  · intro x hx
    rw [Finset.mem_union]
    rcases Finset.mem_insert.mp hx with rfl | hxB
    · exact Or.inr (by simp [freshPair])
    · exact Or.inl (hBS hxB)
  · intro heq
    have hnmem : n ∈ insert (n + m) B := by
      rw [← heq]
      simp
    rw [Finset.mem_insert] at hnmem
    rcases hnmem with hbad | hnB
    · omega
    · exact hn (hBS hnB)
  · have hnA : n ∉ A := fun h ↦ hn (hAS h)
    have hnmB : n + m ∉ B := fun h ↦ hnm (hBS h)
    rw [Finset.sum_insert hnA, Finset.sum_insert hnmB]
    simp only [id_eq]
    change n + A.sum id = (n + m) + B.sum id
    omega

/-- Fresh-pair extension for the relaxed, possibly one-sided difference
representation. -/
theorem collision_of_difference_and_freshPair
    {S : Finset ℕ} {m n : ℕ}
    (hm : 0 < m) (hrep : RepresentsDifference S m)
    (hn : n ∉ S) (hnm : n + m ∉ S) :
    HasSubsetSumCollision (S ∪ freshPair m n) := by
  rcases hrep with ⟨A, B, hAS, hBS, hdisj, hsum⟩
  refine ⟨insert n A, insert (n + m) B, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_union]
    rcases Finset.mem_insert.mp hx with rfl | hxA
    · exact Or.inr (by simp [freshPair])
    · exact Or.inl (hAS hxA)
  · intro x hx
    rw [Finset.mem_union]
    rcases Finset.mem_insert.mp hx with rfl | hxB
    · exact Or.inr (by simp [freshPair])
    · exact Or.inl (hBS hxB)
  · intro heq
    have hnmem : n ∈ insert (n + m) B := by
      rw [← heq]
      simp
    rw [Finset.mem_insert] at hnmem
    rcases hnmem with hbad | hnB
    · omega
    · exact hn (hBS hnB)
  · have hnA : n ∉ A := fun h ↦ hn (hAS h)
    have hnmB : n + m ∉ B := fun h ↦ hnm (hBS h)
    rw [Finset.sum_insert hnA, Finset.sum_insert hnmB]
    simp only [id_eq]
    change n + A.sum id = (n + m) + B.sum id
    omega

/-- A version convenient after conditioning: the fresh exposed part need
only contain the required pair. -/
theorem collision_of_representedDifference_of_freshPair_subset
    {S U : Finset ℕ} {m n : ℕ}
    (hm : 0 < m) (hrep : RepresentsPositiveDifference S m)
    (hdisj : Disjoint S U) (hpair : freshPair m n ⊆ U) :
    HasSubsetSumCollision (S ∪ U) := by
  have hnU : n ∈ U := hpair (by simp [freshPair])
  have hnmU : n + m ∈ U := hpair (by simp [freshPair])
  have hnS : n ∉ S := fun hnS ↦ Finset.disjoint_left.mp hdisj hnS hnU
  have hnmS : n + m ∉ S :=
    fun hnmS ↦ Finset.disjoint_left.mp hdisj hnmS hnmU
  apply HasSubsetSumCollision.mono (S := S ∪ freshPair m n)
    (T := S ∪ U)
  · exact Finset.union_subset_union_right hpair
  · exact collision_of_representedDifference_and_freshPair hm hrep hnS hnmS

/-! ## Ternary signed states and their energy -/

/-- The signed contribution of coordinate `i`: state `0` omits it, state
`1` puts it on the left, and state `2` puts it on the right. -/
def signedTerm (i : ℕ) (a : Fin 3) : ℤ :=
  if a = 1 then (i : ℤ) else if a = 2 then -(i : ℤ) else 0

/-- Signed sum attached to a ternary state on `S`. -/
def signedValue (S : Finset ℕ) (a : (↑S → Fin 3)) : ℤ :=
  ∑ i, signedTerm i.1 (a i)

/-- Coordinates of a ternary state carrying a specified value, returned as
a finset of ordinary natural numbers. -/
def stateSupport (S : Finset ℕ) (a : (↑S → Fin 3)) (v : Fin 3) :
    Finset ℕ :=
  (S.attach.filter fun i ↦ a i = v).image Subtype.val

theorem mem_stateSupport_iff {S : Finset ℕ} {a : (↑S → Fin 3)}
    {v : Fin 3} {i : ℕ} :
    i ∈ stateSupport S a v ↔ ∃ hi : i ∈ S, a ⟨i, hi⟩ = v := by
  simp [stateSupport]

theorem stateSupport_subset (S : Finset ℕ) (a : (↑S → Fin 3))
    (v : Fin 3) : stateSupport S a v ⊆ S := by
  intro i hi
  exact (mem_stateSupport_iff.mp hi).choose

theorem stateSupport_disjoint_one_two (S : Finset ℕ)
    (a : (↑S → Fin 3)) :
    Disjoint (stateSupport S a 1) (stateSupport S a 2) := by
  rw [Finset.disjoint_left]
  intro i hi1 hi2
  rcases mem_stateSupport_iff.mp hi1 with ⟨hiS, h1⟩
  rcases mem_stateSupport_iff.mp hi2 with ⟨hiS', h2⟩
  have heq : (⟨i, hiS⟩ : ↑S) = ⟨i, hiS'⟩ := Subtype.ext rfl
  rw [← heq] at h2
  omega

/-- Integer-valued sum of one support. -/
def stateSupportValue (S : Finset ℕ) (a : (↑S → Fin 3))
    (v : Fin 3) : ℤ :=
  ∑ i ∈ stateSupport S a v, (i : ℤ)

theorem stateSupportValue_eq (S : Finset ℕ) (a : (↑S → Fin 3))
    (v : Fin 3) :
    stateSupportValue S a v = ∑ i, if a i = v then (i.1 : ℤ) else 0 := by
  rw [stateSupportValue, stateSupport, Finset.sum_image]
  · simp [Finset.sum_filter]
  · intro i _ j _ hij
    exact Subtype.ext hij

theorem signedValue_eq_supportValues (S : Finset ℕ)
    (a : (↑S → Fin 3)) :
    signedValue S a = stateSupportValue S a 1 - stateSupportValue S a 2 := by
  rw [stateSupportValue_eq, stateSupportValue_eq, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  generalize hx : a i = x
  fin_cases x <;> simp [signedTerm]

theorem stateSupportValue_eq_natCast (S : Finset ℕ)
    (a : (↑S → Fin 3)) (v : Fin 3) :
    stateSupportValue S a v =
      ((stateSupport S a v).sum id : ℕ) := by
  simp [stateSupportValue]

/-- Every natural-valued ternary signed sum supplies the relaxed disjoint
difference representation used by the fresh-pair step. -/
theorem representsDifference_of_signedValue_eq_nat
    {S : Finset ℕ} {a : (↑S → Fin 3)} {m : ℕ}
    (hval : signedValue S a = (m : ℤ)) :
    RepresentsDifference S m := by
  refine ⟨stateSupport S a 1, stateSupport S a 2,
    stateSupport_subset S a 1, stateSupport_subset S a 2,
    stateSupport_disjoint_one_two S a, ?_⟩
  have hsupport := signedValue_eq_supportValues S a
  rw [stateSupportValue_eq_natCast, stateSupportValue_eq_natCast, hval] at hsupport
  have hnat : (stateSupport S a 1).sum id =
      m + (stateSupport S a 2).sum id := by
    exact_mod_cast (sub_eq_iff_eq_add.mp hsupport.symm)
  simpa [add_comm] using hnat

/-- A state is proper when both a left and a right coordinate occur. -/
def IsProperState {S : Finset ℕ} (a : (↑S → Fin 3)) : Prop :=
  (∃ i, a i = 1) ∧ ∃ i, a i = 2

/-- All proper ternary states. -/
def properSignedStates (S : Finset ℕ) : Finset (↑S → Fin 3) :=
  Finset.univ.filter IsProperState

/-- All ternary states.  One-sided states are retained: they also represent
positive differences and become genuine two-sided collisions after the
fresh-pair step. -/
def signedStates (S : Finset ℕ) : Finset (↑S → Fin 3) :=
  Finset.univ

/-- All differences represented by nonempty disjoint left and right
subsets of `S`. -/
def signedDifferenceSet (S : Finset ℕ) : Finset ℤ :=
  (properSignedStates S).image (signedValue S)

/-- Collision energy of the signed-sum map on proper ternary states. -/
def signedDifferenceEnergy (S : Finset ℕ) : ℕ :=
  Erdos448.occupiedBinEnergy (properSignedStates S) (signedValue S)

/-- Difference image of the full ternary cube. -/
def fullSignedDifferenceSet (S : Finset ℕ) : Finset ℤ :=
  (signedStates S).image (signedValue S)

/-- Energy of the signed-sum map on the full ternary cube. -/
def fullSignedDifferenceEnergy (S : Finset ℕ) : ℕ :=
  Erdos448.occupiedBinEnergy (signedStates S) (signedValue S)

@[simp] theorem signedStates_card (S : Finset ℕ) :
    (signedStates S).card = 3 ^ S.card := by
  simp [signedStates]

/-- The exact finite Cauchy--Schwarz inequality at the heart of the global
difference lemma.  The separate state-counting estimate supplies the lower
bound on the left; the normalized-energy argument supplies the upper bound
on the final factor. -/
theorem properState_card_sq_le_difference_card_mul_energy (S : Finset ℕ) :
    (properSignedStates S).card ^ 2 ≤
      (signedDifferenceSet S).card * signedDifferenceEnergy S := by
  exact Erdos448.card_sq_le_card_image_mul_occupiedBinEnergy
    (properSignedStates S) (signedValue S)

/-- Cauchy--Schwarz on the full ternary cube, with its cardinality already
evaluated as `3^|S|`. -/
theorem ternary_cube_sq_le_fullDifference_card_mul_energy (S : Finset ℕ) :
    (3 ^ S.card) ^ 2 ≤
      (fullSignedDifferenceSet S).card * fullSignedDifferenceEnergy S := by
  simpa [fullSignedDifferenceSet, fullSignedDifferenceEnergy] using
    (Erdos448.card_sq_le_card_image_mul_occupiedBinEnergy
      (signedStates S) (signedValue S))

/-- Membership of a nonnegative integer in the full signed image gives the
concrete disjoint-subset representation consumed by the fresh-pair step. -/
theorem representsDifference_of_nat_mem_fullSignedDifferenceSet
    {S : Finset ℕ} {m : ℕ} (hm : (m : ℤ) ∈ fullSignedDifferenceSet S) :
    RepresentsDifference S m := by
  rw [fullSignedDifferenceSet, Finset.mem_image] at hm
  rcases hm with ⟨a, _ha, hval⟩
  exact representsDifference_of_signedValue_eq_nat hval

/-- Cancellation form of the Cauchy--Schwarz step.  An upper bound for the
energy normalized by the square of the ternary-cube size immediately gives
a lower bound for the number of represented differences. -/
theorem fullDifference_card_lower_of_energy (S : Finset ℕ) (D ξ : ℕ)
    (henergy : D * fullSignedDifferenceEnergy S ≤
      ξ * (3 ^ S.card) ^ 2) :
    D ≤ ξ * (fullSignedDifferenceSet S).card := by
  have hcs := ternary_cube_sq_le_fullDifference_card_mul_energy S
  have hmul : D * (3 ^ S.card) ^ 2 ≤
      (ξ * (fullSignedDifferenceSet S).card) * (3 ^ S.card) ^ 2 := by
    calc
      D * (3 ^ S.card) ^ 2 ≤
          D * ((fullSignedDifferenceSet S).card *
            fullSignedDifferenceEnergy S) := Nat.mul_le_mul_left D hcs
      _ = (fullSignedDifferenceSet S).card *
          (D * fullSignedDifferenceEnergy S) := by ring
      _ ≤ (fullSignedDifferenceSet S).card *
          (ξ * (3 ^ S.card) ^ 2) :=
            Nat.mul_le_mul_left _ henergy
      _ = (ξ * (fullSignedDifferenceSet S).card) *
          (3 ^ S.card) ^ 2 := by ring
  exact Nat.le_of_mul_le_mul_right hmul (by positivity)

@[simp] theorem signedTerm_zero (i : ℕ) : signedTerm i 0 = 0 := by
  simp [signedTerm]

@[simp] theorem signedTerm_one (i : ℕ) : signedTerm i 1 = i := by
  simp [signedTerm]

@[simp] theorem signedTerm_two (i : ℕ) : signedTerm i 2 = -(i : ℤ) := by
  simp [signedTerm]

/-- Proper signed differences are symmetric. -/
def swapSign (a : Fin 3) : Fin 3 :=
  if a = 1 then 2 else if a = 2 then 1 else 0

@[simp] theorem swapSign_zero : swapSign 0 = 0 := by simp [swapSign]
@[simp] theorem swapSign_one : swapSign 1 = 2 := by simp [swapSign]
@[simp] theorem swapSign_two : swapSign 2 = 1 := by simp [swapSign]

theorem swapSign_involutive : Function.Involutive swapSign := by
  intro a
  fin_cases a <;> simp

theorem signedTerm_swapSign (i : ℕ) (a : Fin 3) :
    signedTerm i (swapSign a) = -signedTerm i a := by
  fin_cases a <;> simp

theorem signedValue_swapSign (S : Finset ℕ) (a : (↑S → Fin 3)) :
    signedValue S (fun i ↦ swapSign (a i)) = -signedValue S a := by
  simp only [signedValue, signedTerm_swapSign, Finset.sum_neg_distrib]

theorem isProperState_swapSign_iff {S : Finset ℕ} (a : (↑S → Fin 3)) :
    IsProperState (fun i ↦ swapSign (a i)) ↔ IsProperState a := by
  constructor
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    refine ⟨⟨j, ?_⟩, ⟨i, ?_⟩⟩
    · have := congrArg swapSign hj
      simpa [swapSign_involutive (a j)] using this
    · have := congrArg swapSign hi
      simpa [swapSign_involutive (a i)] using this
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    refine ⟨⟨j, ?_⟩, ⟨i, ?_⟩⟩ <;> simp [hi, hj]

/-- If a represented difference occurs, its negative occurs too. -/
theorem neg_mem_signedDifferenceSet_of_mem {S : Finset ℕ} {z : ℤ}
    (hz : z ∈ signedDifferenceSet S) :
    -z ∈ signedDifferenceSet S := by
  rw [signedDifferenceSet, Finset.mem_image] at hz ⊢
  rcases hz with ⟨a, ha, hval⟩
  refine ⟨fun i ↦ swapSign (a i), ?_, ?_⟩
  · rw [properSignedStates, Finset.mem_filter] at ha ⊢
    exact ⟨Finset.mem_univ _, (isProperState_swapSign_iff a).2 ha.2⟩
  · rw [signedValue_swapSign, hval]

theorem neg_mem_signedDifferenceSet_iff {S : Finset ℕ} {z : ℤ} :
    -z ∈ signedDifferenceSet S ↔ z ∈ signedDifferenceSet S := by
  constructor
  · intro hz
    simpa using neg_mem_signedDifferenceSet_of_mem hz
  · exact neg_mem_signedDifferenceSet_of_mem

/-! ## Exact harmonic interval product -/

/-- The nonselection factors of the harmonic Bernoulli model telescope
exactly on an integer interval. -/
theorem harmonic_nonselection_product_Ioc (a b : ℕ)
    (ha : 0 < a) (hab : a ≤ b) :
    (∏ i ∈ Finset.Ioc a b, (1 - 1 / (i : ℝ))) = (a : ℝ) / b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction k with
  | zero => simp [ha.ne']
  | succ k ih =>
      rw [show a + (k + 1) = (a + k) + 1 by omega]
      rw [Finset.prod_Ioc_succ_top (Nat.le_add_right a k), ih]
      have haR : (0 : ℝ) < a := by exact_mod_cast ha
      have hakR : (0 : ℝ) < a + k := by positivity
      have haksR : (0 : ℝ) < a + (k + 1) := by positivity
      field_simp
      norm_num

/-- Exact mass of a two-point fresh-pair event in a harmonic interval.
The formula makes the lower bound in the one-step iteration an elementary
rational inequality. -/
theorem harmonic_weight_freshPair (a b m n : ℕ)
    (ha : 0 < a) (han : a < n) (hm : 0 < m) (hnmb : n + m ≤ b) :
    Erdos697.Bernoulli.weight (Finset.Ioc a b)
        (fun i ↦ 1 / (i : ℝ)) (freshPair m n) =
      (a : ℝ) /
        ((b : ℝ) * ((n : ℝ) - 1) * ((n + m : ℝ) - 1)) := by
  have hnpos : 0 < n := lt_trans ha han
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnmR : (0 : ℝ) < n + m := by positivity
  have hnm_ne : n ≠ n + m := by omega
  have hpair : freshPair m n ⊆ Finset.Ioc a b := by
    intro x hx
    rw [mem_freshPair] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact Finset.mem_Ioc.mpr ⟨han, le_trans (Nat.le_add_right n m) hnmb⟩
    · rw [hx]
      exact Finset.mem_Ioc.mpr ⟨han.trans_le (Nat.le_add_right n m), hnmb⟩
  have hselected :
      (∏ i ∈ freshPair m n, (1 / (i : ℝ))) =
        (1 / (n : ℝ)) * (1 / (n + m : ℝ)) := by
    simpa [freshPair] using
      (Finset.prod_pair (a := n) (b := n + m)
        (f := fun i : ℕ ↦ (1 / (i : ℝ))) hnm_ne)
  have homitted :
      (∏ i ∈ freshPair m n, (1 - 1 / (i : ℝ))) =
        (1 - 1 / (n : ℝ)) * (1 - 1 / (n + m : ℝ)) := by
    simpa [freshPair] using
      (Finset.prod_pair (a := n) (b := n + m)
        (f := fun i : ℕ ↦ (1 - 1 / (i : ℝ))) hnm_ne)
  have hsplit := Finset.prod_sdiff
    (s₁ := freshPair m n) (s₂ := Finset.Ioc a b)
    (f := fun i ↦ (1 - 1 / (i : ℝ))) hpair
  rw [homitted, harmonic_nonselection_product_Ioc a b ha
    (han.le.trans (Nat.le_add_right n m) |>.trans hnmb)] at hsplit
  rw [Erdos697.Bernoulli.weight, hselected]
  have hbpos : (0 : ℝ) < b := by
    exact_mod_cast lt_of_lt_of_le (lt_trans ha han) (le_trans (Nat.le_add_right n m) hnmb)
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℕ) < n := lt_of_le_of_lt ha han
    exact sub_ne_zero.mpr (by exact_mod_cast this.ne')
  have hnm1 : (n + m : ℝ) - 1 ≠ 0 := by
    have : (1 : ℕ) < n + m := lt_of_lt_of_le (lt_of_le_of_lt ha han)
      (Nat.le_add_right n m)
    exact sub_ne_zero.mpr (by exact_mod_cast this.ne')
  field_simp at hsplit ⊢
  nlinarith

/-! ## The abstract bad-mass recurrence -/

/-- Closed form of the affine recurrence used after splitting histories into
regular and irregular ones.  Keeping it abstract avoids mixing the finite
Bernoulli bookkeeping with the later choice of scales. -/
theorem affine_recurrence_bound {b : ℕ → ℝ} {q δ : ℝ}
    (_hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hstep : ∀ j, b (j + 1) ≤ (1 - q) * b j + q * δ) :
    ∀ j, b j ≤ (1 - q) ^ j * b 0 + (1 - (1 - q) ^ j) * δ := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      calc
        b (j + 1) ≤ (1 - q) * b j + q * δ := hstep j
        _ ≤ (1 - q) *
              ((1 - q) ^ j * b 0 + (1 - (1 - q) ^ j) * δ) + q * δ := by
            gcongr
        _ = (1 - q) ^ (j + 1) * b 0 +
              (1 - (1 - q) ^ (j + 1)) * δ := by
            rw [pow_succ]
            ring

/-- A convenient coarser form: if the initial bad mass is at most one and
the irregular mass is nonnegative, then only a geometric term and `δ`
remain. -/
theorem affine_recurrence_bound_one {b : ℕ → ℝ} {q δ : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hδ0 : 0 ≤ δ) (hb0 : b 0 ≤ 1)
    (hstep : ∀ j, b (j + 1) ≤ (1 - q) * b j + q * δ) (j : ℕ) :
    b j ≤ (1 - q) ^ j + δ := by
  have hr0 : 0 ≤ 1 - q := by linarith
  have hr1 : 1 - q ≤ 1 := by linarith
  calc
    b j ≤ (1 - q) ^ j * b 0 + (1 - (1 - q) ^ j) * δ :=
      affine_recurrence_bound hq0 hq1 hstep j
    _ ≤ (1 - q) ^ j * 1 + (1 - (1 - q) ^ j) * δ := by
      gcongr
    _ ≤ (1 - q) ^ j + δ := by
      have hp0 : 0 ≤ (1 - q) ^ j := pow_nonneg hr0 _
      have hp1 : (1 - q) ^ j ≤ 1 := by
        exact pow_le_one₀ hr0 hr1
      nlinarith

end

end Erdos144.HarmonicBlocks
