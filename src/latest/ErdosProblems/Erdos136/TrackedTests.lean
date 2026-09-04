/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos136.ConflictCounts
import ErdosProblems.Erdos136.AuxConcentration

/-!
# Tracked tests in the Joos--Mubayi construction

This file contains the finite, deterministic bookkeeping behind the
one-, two-, and three-uniform tests used in the proof of Erdős Problem 136.
The probabilistic retention argument is responsible only for numerical
bounds on the host totals.  The definitions and identities below are exact.
-/

namespace Erdos136

open Finset

noncomputable section

variable {V : Type*} [DecidableEq V]

attribute [local instance] Classical.propDecidable

/-! ## Indicator tests and their exact finite totals -/

/-- The indicator weight of a finite family of `j`-sets. -/
def indicatorWeight (F : Finset (Hypergraph V)) : TestWeight V :=
  fun S => if S ∈ F then 1 else 0

@[simp] theorem indicatorWeight_apply (F : Finset (Hypergraph V))
    (S : Hypergraph V) :
    indicatorWeight F S = if S ∈ F then 1 else 0 := rfl

theorem indicatorWeight_nonneg (F : Finset (Hypergraph V)) (S : Hypergraph V) :
    0 ≤ indicatorWeight F S := by
  unfold indicatorWeight
  split <;> norm_num

/-- Summing an indicator test over `A` counts the members of `F` which are
`j`-subsets of `A`. -/
theorem testTotal_indicatorWeight (F : Finset (Hypergraph V))
    (A : Hypergraph V) (j : ℕ) :
    testTotal (indicatorWeight F) A j =
      (((A.powersetCard j).filter (· ∈ F)).card : ℝ) := by
  simp [testTotal, indicatorWeight, Finset.card_filter]

/-- The rooted extension of an indicator test is the corresponding filtered
cardinality. -/
theorem testExtension_indicatorWeight (F : Finset (Hypergraph V))
    (A : Hypergraph V) (j : ℕ) (root : Hypergraph V) :
    testExtension (indicatorWeight F) A j root =
      ((((A.powersetCard j).filter (root ⊆ ·)).filter (· ∈ F)).card : ℝ) := by
  simp [testExtension, indicatorWeight, Finset.card_filter]

/-- A family of matching `j`-sets gives a genuine `j`-uniform test. -/
theorem indicatorWeight_isTestFunction {H : Hypergraph V}
    {F : Finset (Hypergraph V)} {j ell : ℕ} (hell : 1 ≤ ell)
    (hF : ∀ S ∈ F, S.card = j ∧ IsMatching H S) :
    IsTestFunction H j ell (indicatorWeight F) := by
  refine ⟨indicatorWeight_nonneg F, ?_, ?_, ?_⟩
  · intro S
    by_cases hSF : S ∈ F
    · simp [indicatorWeight, hSF, hell]
    · simp [indicatorWeight, hSF]
  · intro S hcard
    by_cases hSF : S ∈ F
    · exact (hcard (hF S hSF).1).elim
    · simp [indicatorWeight, hSF]
  · intro S hmatch
    by_cases hSF : S ∈ F
    · exact (hmatch (hF S hSF).2).elim
    · simp [indicatorWeight, hSF]

/-! ## The one-uniform leave-degree test -/

/-- Number of graph-edge vertices in an auxiliary edge which are incident
with `x`.  For a triangle support it is either zero or two. -/
def graphIncidence {n k : ℕ} (x : Fin n) (e : Finset (AuxVertex n k)) : ℕ :=
  (Finset.univ.filter fun y : Fin n =>
    y ≠ x ∧ Sum.inl s(x, y) ∈ e).card

/-- The one-uniform Joos--Mubayi weight `w_x`.  It vanishes off singleton
matchings in the host, as required by `IsTestFunction`. -/
def leaveDegreeWeight {n k : ℕ} (H : Hypergraph (AuxVertex n k))
    (x : Fin n) : TestWeight (AuxVertex n k) :=
  fun S => if IsMatching H S ∧ S.card = 1 then
    ∑ e ∈ S, (graphIncidence x e : ℝ)
  else 0

theorem graphIncidence_le (n k : ℕ) (x : Fin n)
    (e : Finset (AuxVertex n k)) : graphIncidence x e ≤ n := by
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem leaveDegreeWeight_nonneg {n k : ℕ}
    (H : Hypergraph (AuxVertex n k)) (x : Fin n) (S : Hypergraph (AuxVertex n k)) :
    0 ≤ leaveDegreeWeight H x S := by
  simp only [leaveDegreeWeight]
  split_ifs
  · positivity
  · exact le_rfl

/-- On a subfamily of the host, the one-uniform test total is exactly the
sum of the selected incidences. -/
theorem testTotal_leaveDegreeWeight {n k : ℕ}
    (H A : Hypergraph (AuxVertex n k)) (hAH : A ⊆ H) (x : Fin n) :
    testTotal (leaveDegreeWeight H x) A 1 =
      ∑ e ∈ A, (graphIncidence x e : ℝ) := by
  simp only [testTotal, leaveDegreeWeight, Finset.powersetCard_one]
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro e heA
  have hsingleton : IsMatching H {e} :=
    isMatching_singleton_iff.2 (hAH heA)
  simp [hsingleton]

/-- The leave-degree weight is a genuine one-uniform test whenever the
explicit palette constant `ell` dominates every host incidence. -/
theorem leaveDegreeWeight_isTestFunction {n k ell : ℕ}
    (H : Hypergraph (AuxVertex n k)) (x : Fin n)
    (hinc : ∀ e ∈ H, graphIncidence x e ≤ ell) :
    IsTestFunction H 1 ell (leaveDegreeWeight H x) := by
  refine ⟨leaveDegreeWeight_nonneg H x, ?_, ?_, ?_⟩
  · intro S
    simp only [leaveDegreeWeight]
    split_ifs with h
    · obtain ⟨e, rfl⟩ := Finset.card_eq_one.mp h.2
      simp only [Finset.sum_singleton]
      exact_mod_cast hinc e (isMatching_singleton_iff.mp h.1)
    · exact_mod_cast (Nat.zero_le ell)
  · intro S hcard
    simp [leaveDegreeWeight, hcard]
  · intro S hmatch
    simp [leaveDegreeWeight, hmatch]

/-! ## A finite slot model for the two- and three-uniform tests -/

/-- A `CrossSlotSystem` packages the exact finite double count used for P5.
A slot has a two-edge owner.  It may be covered by host edges; adjoining a
covering edge produces the corresponding three-edge extension. -/
structure CrossSlotSystem (V Q : Type*) [DecidableEq V] [DecidableEq Q]
    (H : Hypergraph V) where
  slots : Finset Q
  owner : Q → Hypergraph V
  covers : Q → Finset V → Prop
  coverKey : Q → V
  owner_card : ∀ q ∈ slots, (owner q).card = 2
  owner_matching : ∀ q ∈ slots, IsMatching H (owner q)
  covers_mem : ∀ q ∈ slots, ∀ e, covers q e → e ∈ H
  covers_fresh : ∀ q ∈ slots, ∀ e, covers q e → e ∉ owner q
  covers_disjoint : ∀ q ∈ slots, ∀ e, covers q e →
    ∀ f ∈ owner q, Disjoint e f
  covers_key_mem : ∀ q ∈ slots, ∀ e, covers q e → coverKey q ∈ e

namespace CrossSlotSystem

variable {Q : Type*} [DecidableEq Q] {H : Hypergraph V}

/-- Restrict a slot system to a decidable subfamily.  This is used to split
the cross tests according to the two multiplicities `j_x,j_y ∈ {1,2}`. -/
def restrict (T : CrossSlotSystem V Q H) (P : Q → Prop) :
    CrossSlotSystem V Q H where
  slots := T.slots.filter P
  owner := T.owner
  covers := T.covers
  coverKey := T.coverKey
  owner_card := by
    intro q hq
    exact T.owner_card q (Finset.mem_filter.mp hq).1
  owner_matching := by
    intro q hq
    exact T.owner_matching q (Finset.mem_filter.mp hq).1
  covers_mem := by
    intro q hq e he
    exact T.covers_mem q (Finset.mem_filter.mp hq).1 e he
  covers_fresh := by
    intro q hq e he
    exact T.covers_fresh q (Finset.mem_filter.mp hq).1 e he
  covers_disjoint := by
    intro q hq e he f hf
    exact T.covers_disjoint q (Finset.mem_filter.mp hq).1 e he f hf
  covers_key_mem := by
    intro q hq e he
    exact T.covers_key_mem q (Finset.mem_filter.mp hq).1 e he

@[simp] theorem mem_restrict_slots {T : CrossSlotSystem V Q H}
    {P : Q → Prop} {q : Q} :
    q ∈ (T.restrict P).slots ↔ q ∈ T.slots ∧ P q := by
  simp [restrict]

/-- The finite set of slot/cover pairs. -/
def coverPairs (T : CrossSlotSystem V Q H) :
    Finset (Q × Finset V) :=
  (T.slots ×ˢ H).filter fun qe => T.covers qe.1 qe.2

/-- The owner of a slot/cover pair after its covering edge is adjoined. -/
def extendedOwner (T : CrossSlotSystem V Q H) (qe : Q × Finset V) :
    Hypergraph V := insert qe.2 (T.owner qe.1)

/-- The two-uniform weight counts slots with the prescribed owner. -/
def pairWeight (T : CrossSlotSystem V Q H) : TestWeight V :=
  fun S => ((T.slots.filter fun q => T.owner q = S).card : ℝ)

/-- The three-uniform weight counts covered slots with the prescribed
extended owner.  Multiplicity is retained, which makes the bookkeeping
identity literally true even when several slots have the same owner. -/
def tripleWeight (T : CrossSlotSystem V Q H) : TestWeight V :=
  fun S => ((T.coverPairs.filter fun qe => T.extendedOwner qe = S).card : ℝ)

theorem pairWeight_nonneg (T : CrossSlotSystem V Q H) (S : Hypergraph V) :
    0 ≤ T.pairWeight S := by
  unfold pairWeight
  positivity

theorem tripleWeight_nonneg (T : CrossSlotSystem V Q H) (S : Hypergraph V) :
    0 ≤ T.tripleWeight S := by
  unfold tripleWeight
  positivity

theorem mem_coverPairs_iff {T : CrossSlotSystem V Q H}
    {q : Q} {e : Finset V} :
    (q, e) ∈ T.coverPairs ↔ q ∈ T.slots ∧ e ∈ H ∧ T.covers q e := by
  simp [coverPairs, and_assoc]

theorem extendedOwner_card {T : CrossSlotSystem V Q H}
    {qe : Q × Finset V} (hqe : qe ∈ T.coverPairs) :
    (T.extendedOwner qe).card = 3 := by
  rcases qe with ⟨q, e⟩
  rw [extendedOwner, Finset.card_insert_of_notMem]
  · rw [T.owner_card q (mem_coverPairs_iff.mp hqe).1]
  · exact T.covers_fresh q (mem_coverPairs_iff.mp hqe).1 e
      (mem_coverPairs_iff.mp hqe).2.2

theorem extendedOwner_matching {T : CrossSlotSystem V Q H}
    {qe : Q × Finset V} (hqe : qe ∈ T.coverPairs) :
    IsMatching H (T.extendedOwner qe) := by
  rcases qe with ⟨q, e⟩
  rw [extendedOwner, isMatching_insert_iff]
  have hmem := mem_coverPairs_iff.mp hqe
  exact ⟨hmem.2.1, T.owner_matching q hmem.1,
    fun f hf hne => T.covers_disjoint q hmem.1 e hmem.2.2 f hf⟩

/-- Exact total of the pair test: every selected owner contributes once for
each slot in its fibre. -/
theorem testTotal_pairWeight (T : CrossSlotSystem V Q H)
    (M : Hypergraph V) :
    testTotal T.pairWeight M 2 =
      ((T.slots.filter fun q => T.owner q ∈ M.powersetCard 2).card : ℝ) := by
  rw [testTotal]
  change (∑ S ∈ M.powersetCard 2,
      ((T.slots.filter fun q => T.owner q = S).card : ℝ)) = _
  exact_mod_cast Finset.sum_card_fiberwise_eq_card_filter
    T.slots (M.powersetCard 2) T.owner

/-- Exact rooted extension count for the pair test. -/
theorem testExtension_pairWeight (T : CrossSlotSystem V Q H)
    (M : Hypergraph V) (root : Hypergraph V) :
    testExtension T.pairWeight M 2 root =
      ((T.slots.filter fun q =>
        T.owner q ∈ (M.powersetCard 2).filter (root ⊆ ·)).card : ℝ) := by
  rw [testExtension]
  change (∑ S ∈ (M.powersetCard 2).filter (root ⊆ ·),
      ((T.slots.filter fun q => T.owner q = S).card : ℝ)) = _
  exact_mod_cast Finset.sum_card_fiberwise_eq_card_filter
    T.slots ((M.powersetCard 2).filter (root ⊆ ·)) T.owner

/-- Exact total of the triple test. -/
theorem testTotal_tripleWeight (T : CrossSlotSystem V Q H)
    (M : Hypergraph V) :
    testTotal T.tripleWeight M 3 =
      ((T.coverPairs.filter fun qe =>
        T.extendedOwner qe ∈ M.powersetCard 3).card : ℝ) := by
  rw [testTotal]
  change (∑ S ∈ M.powersetCard 3,
      ((T.coverPairs.filter fun qe => T.extendedOwner qe = S).card : ℝ)) = _
  exact_mod_cast Finset.sum_card_fiberwise_eq_card_filter
    T.coverPairs (M.powersetCard 3) T.extendedOwner

/-- Exact rooted extension count for the triple test. -/
theorem testExtension_tripleWeight (T : CrossSlotSystem V Q H)
    (M : Hypergraph V) (root : Hypergraph V) :
    testExtension T.tripleWeight M 3 root =
      ((T.coverPairs.filter fun qe =>
        T.extendedOwner qe ∈ (M.powersetCard 3).filter (root ⊆ ·)).card : ℝ) := by
  rw [testExtension]
  change (∑ S ∈ (M.powersetCard 3).filter (root ⊆ ·),
      ((T.coverPairs.filter fun qe => T.extendedOwner qe = S).card : ℝ)) = _
  exact_mod_cast Finset.sum_card_fiberwise_eq_card_filter
    T.coverPairs ((M.powersetCard 3).filter (root ⊆ ·)) T.extendedOwner

/-- A pointwise fibre bound is exactly what is needed for the two-uniform
slot weight to take values in `[0,ell]`. -/
theorem pairWeight_isTestFunction (T : CrossSlotSystem V Q H) {ell : ℕ}
    (hfiber : ∀ S, (T.slots.filter fun q => T.owner q = S).card ≤ ell) :
    IsTestFunction H 2 ell T.pairWeight := by
  refine ⟨T.pairWeight_nonneg, ?_, ?_, ?_⟩
  · intro S
    unfold pairWeight
    exact_mod_cast hfiber S
  · intro S hcard
    rw [pairWeight]
    suffices (T.slots.filter fun q => T.owner q = S) = ∅ by simp [this]
    rw [Finset.filter_eq_empty_iff]
    intro q hq heq
    exact hcard (heq ▸ T.owner_card q hq)
  · intro S hmatch
    rw [pairWeight]
    suffices (T.slots.filter fun q => T.owner q = S) = ∅ by simp [this]
    rw [Finset.filter_eq_empty_iff]
    intro q hq heq
    exact hmatch (heq ▸ T.owner_matching q hq)

/-- The analogous fibre bound for the three-uniform extension weight. -/
theorem tripleWeight_isTestFunction (T : CrossSlotSystem V Q H) {ell : ℕ}
    (hfiber : ∀ S,
      (T.coverPairs.filter fun qe => T.extendedOwner qe = S).card ≤ ell) :
    IsTestFunction H 3 ell T.tripleWeight := by
  refine ⟨T.tripleWeight_nonneg, ?_, ?_, ?_⟩
  · intro S
    unfold tripleWeight
    exact_mod_cast hfiber S
  · intro S hcard
    rw [tripleWeight]
    suffices (T.coverPairs.filter fun qe => T.extendedOwner qe = S) = ∅ by
      simp [this]
    rw [Finset.filter_eq_empty_iff]
    intro qe hqe heq
    exact hcard (heq ▸ T.extendedOwner_card hqe)
  · intro S hmatch
    rw [tripleWeight]
    suffices (T.coverPairs.filter fun qe => T.extendedOwner qe = S) = ∅ by
      simp [this]
    rw [Finset.filter_eq_empty_iff]
    intro qe hqe heq
    exact hmatch (heq ▸ T.extendedOwner_matching hqe)

/-- Explicit finite inequalities sufficient for trackability of the
two-uniform slot test.  The exact total and extension cardinalities are the
preceding `testTotal_pairWeight` and `testExtension_pairWeight` lemmas. -/
theorem pairWeight_isTrackable_of_bounds (T : CrossSlotSystem V Q H)
    (C : ConflictSystem V) (ell : ℕ) (d eta : ℝ)
    (hfiber : ∀ S, (T.slots.filter fun q => T.owner q = S).card ≤ ell)
    (htotal : Real.rpow d (2 + eta) ≤ testTotal T.pairWeight H 2)
    (hext : ∀ j', 1 ≤ j' → j' < 2 → ∀ root, root ⊆ H → root.card = j' →
      testExtension T.pairWeight H 2 root ≤
        testTotal T.pairWeight H 2 / Real.rpow d ((j' : ℝ) + eta))
    (hlink : ∀ S ∈ H.powersetCard 2, 0 < T.pairWeight S →
      ∀ e ∈ S, ∀ f ∈ S, e ≠ f → ∀ r, 1 ≤ r → r < ell →
        (((conflictLinkLayer C e r) ∩
          conflictLinkLayer C f r).card : ℝ) ≤ Real.rpow d ((r : ℝ) - eta))
    (hconf : ∀ S ∈ H.powersetCard 2,
      (∃ c ∈ C, c ⊆ S) → T.pairWeight S = 0) :
    IsTrackable H C 2 ell d eta T.pairWeight := by
  exact ⟨T.pairWeight_isTestFunction hfiber, htotal, hext, hlink, hconf⟩

/-- Explicit finite inequalities sufficient for trackability of the
three-uniform extension test. -/
theorem tripleWeight_isTrackable_of_bounds (T : CrossSlotSystem V Q H)
    (C : ConflictSystem V) (ell : ℕ) (d eta : ℝ)
    (hfiber : ∀ S,
      (T.coverPairs.filter fun qe => T.extendedOwner qe = S).card ≤ ell)
    (htotal : Real.rpow d (3 + eta) ≤ testTotal T.tripleWeight H 3)
    (hext : ∀ j', 1 ≤ j' → j' < 3 → ∀ root, root ⊆ H → root.card = j' →
      testExtension T.tripleWeight H 3 root ≤
        testTotal T.tripleWeight H 3 / Real.rpow d ((j' : ℝ) + eta))
    (hlink : ∀ S ∈ H.powersetCard 3, 0 < T.tripleWeight S →
      ∀ e ∈ S, ∀ f ∈ S, e ≠ f → ∀ r, 1 ≤ r → r < ell →
        (((conflictLinkLayer C e r) ∩
          conflictLinkLayer C f r).card : ℝ) ≤ Real.rpow d ((r : ℝ) - eta))
    (hconf : ∀ S ∈ H.powersetCard 3,
      (∃ c ∈ C, c ⊆ S) → T.tripleWeight S = 0) :
    IsTrackable H C 3 ell d eta T.tripleWeight := by
  exact ⟨T.tripleWeight_isTestFunction hfiber, htotal, hext, hlink, hconf⟩

/-- The exact link-intersection number appearing in (W3). -/
def linkIntersectionNumber (C : ConflictSystem V) (e f : Finset V)
    (r : ℕ) : ℕ :=
  ((conflictLinkLayer C e r) ∩ conflictLinkLayer C f r).card

@[simp] theorem linkIntersectionNumber_eq (C : ConflictSystem V)
    (e f : Finset V) (r : ℕ) :
    linkIntersectionNumber C e f r =
      ((conflictLinkLayer C e r) ∩ conflictLinkLayer C f r).card := rfl

/-- A common link is no larger than the conflict degree of either root. -/
theorem linkIntersectionNumber_le_degree (C : ConflictSystem V)
    (e f : Finset V) (r : ℕ) :
    linkIntersectionNumber C e f r ≤ degree C e := by
  calc
    linkIntersectionNumber C e f r ≤ (conflictLinkLayer C e r).card :=
      Finset.card_le_card Finset.inter_subset_left
    _ ≤ (conflictLink C e).card := by
      exact Finset.card_filter_le _ _
    _ ≤ (C.filter fun c => e ∈ c).card := by
      exact Finset.card_image_le
    _ = degree C e := rfl

/-- At most `4n` ordered pairs meet one of two fixed vertices.  This is the
finite four-way charge used in the common-link path count. -/
theorem card_orderedPairs_meeting_two_vertices (n : ℕ) (u v : Fin n) :
    (Finset.univ.filter fun q : Fin n × Fin n =>
      q.1 = u ∨ q.1 = v ∨ q.2 = u ∨ q.2 = v).card ≤ 4 * n := by
  let U : Finset (Fin n) := Finset.univ
  let A : Finset (Fin n × Fin n) := {u} ×ˢ U
  let B : Finset (Fin n × Fin n) := {v} ×ˢ U
  let C : Finset (Fin n × Fin n) := U ×ˢ {u}
  let D : Finset (Fin n × Fin n) := U ×ˢ {v}
  have hsub : (Finset.univ.filter fun q : Fin n × Fin n =>
      q.1 = u ∨ q.1 = v ∨ q.2 = u ∨ q.2 = v) ⊆
      ((A ∪ B) ∪ C) ∪ D := by
    intro q hq
    rcases q with ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    rcases hq with h | h | h | h
    · subst a; simp [A, U]
    · subst a; simp [B, U]
    · subst b; simp [C, U]
    · subst b; simp [D, U]
  calc
    (Finset.univ.filter fun q : Fin n × Fin n =>
        q.1 = u ∨ q.1 = v ∨ q.2 = u ∨ q.2 = v).card ≤
        (((A ∪ B) ∪ C) ∪ D).card := Finset.card_le_card hsub
    _ ≤ ((A ∪ B) ∪ C).card + D.card := Finset.card_union_le _ _
    _ ≤ ((A ∪ B).card + C.card) + D.card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ ((A.card + B.card) + C.card) + D.card :=
      Nat.add_le_add_right (Nat.add_le_add_right
        (Finset.card_union_le _ _) _) _
    _ = 4 * n := by simp [A, B, C, D, U]; omega

/-- An unordered edge has at most its two orientations. -/
theorem card_orderedPairs_with_sym2_eq (n : ℕ) (u v : Fin n) :
    (Finset.univ.filter fun q : Fin n × Fin n =>
      s(q.1, q.2) = s(u, v)).card ≤ 2 := by
  calc
    (Finset.univ.filter fun q : Fin n × Fin n =>
        s(q.1, q.2) = s(u, v)).card ≤ ({(u, v), (v, u)} :
          Finset (Fin n × Fin n)).card := by
      apply Finset.card_le_card
      intro q hq
      rcases q with ⟨a, b⟩
      have heq := (Finset.mem_filter.mp hq).2
      change s(a, b) = s(u, v) at heq
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨hqu, hqv⟩ | ⟨hqv, hqu⟩
      · subst a; subst b; simp
      · subst a; subst b; simp
    _ ≤ 2 := by
      exact (Finset.card_insert_le (u, v) {(v, u)}).trans (by simp)

/-- Concrete geometric common-link estimate obtained from the local
paint-fibre conflict-degree charge. -/
theorem alternatingCycle_commonThreeLink_le_of_maxCodegree {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (L : ℕ) (hcodeg : MaxCodegreeLE (auxiliaryHypergraph candidates R) 2 L)
    (e f : Finset (AuxVertex n k)) :
    ((conflictLinkLayer (alternatingCycleConflicts candidates R) e 3) ∩
      conflictLinkLayer (alternatingCycleConflicts candidates R) f 3).card ≤
        512 * n * n * k * L * L * L := by
  exact (linkIntersectionNumber_le_degree
    (alternatingCycleConflicts candidates R) e f 3).trans
      (alternatingCycleConflict_degree_le_of_maxCodegree
        candidates R L hcodeg e)

/-- A four-uniform conflict system has no link layer except layer three. -/
theorem conflictLinkLayer_eq_empty_of_uniform_four
    (C : ConflictSystem V) (hfour : ∀ c ∈ C, c.card = 4)
    (e : Finset V) {r : ℕ} (hr : r ≠ 3) :
    conflictLinkLayer C e r = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro s hs
  have hdata := mem_conflictLinkLayer.mp hs
  rcases hdata.1 with ⟨c, hc, he, rfl⟩
  have herase : (c.erase e).card = 3 := by
    rw [Finset.card_erase_of_mem he, hfour c hc]
  exact hr (by omega)

/-- For the four-uniform alternating-cycle conflict system, checking W3 at
the common three-link is sufficient: every other link layer is empty. -/
theorem alternatingCycle_w3_of_three_bound {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {j ell : ℕ} (d eta : ℝ) (hd : 0 ≤ d)
    (w : TestWeight (AuxVertex n k))
    (hthree : ∀ S ∈ (auxiliaryHypergraph candidates R).powersetCard j,
      0 < w S → ∀ e ∈ S, ∀ f ∈ S, e ≠ f →
        (((conflictLinkLayer (alternatingCycleConflicts candidates R) e 3) ∩
          conflictLinkLayer (alternatingCycleConflicts candidates R) f 3).card : ℝ) ≤
            Real.rpow d (3 - eta)) :
    ∀ S ∈ (auxiliaryHypergraph candidates R).powersetCard j,
      0 < w S → ∀ e ∈ S, ∀ f ∈ S, e ≠ f →
        ∀ r, 1 ≤ r → r < ell →
          (((conflictLinkLayer (alternatingCycleConflicts candidates R) e r) ∩
            conflictLinkLayer (alternatingCycleConflicts candidates R) f r).card : ℝ) ≤
              Real.rpow d ((r : ℝ) - eta) := by
  intro S hSH hwS e he f hf hef r hr1 hrell
  by_cases hr : r = 3
  · subst r
    simpa only [Nat.cast_ofNat] using hthree S hSH hwS e he f hf hef
  · have hempty := conflictLinkLayer_eq_empty_of_uniform_four
      (alternatingCycleConflicts candidates R)
      (fun _ hc => alternatingCycleConflicts_uniform candidates R hc) e hr
    rw [hempty]
    simp only [Finset.empty_inter, Finset.card_empty, Nat.cast_zero]
    exact Real.rpow_nonneg hd _

/-- Matching-supported tests only need the common-link estimate for
disjoint roots.  Positivity of a test function forces its argument to be a
matching, which supplies the disjointness required by the geometric charge. -/
theorem alternatingCycle_w3_of_disjoint_three_bound {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {j ell : ℕ} (d eta : ℝ) (hd : 0 ≤ d)
    (w : TestWeight (AuxVertex n k))
    (htest : IsTestFunction (auxiliaryHypergraph candidates R) j ell w)
    (hthree : ∀ e f : Finset (AuxVertex n k), Disjoint e f →
      (((conflictLinkLayer (alternatingCycleConflicts candidates R) e 3) ∩
        conflictLinkLayer (alternatingCycleConflicts candidates R) f 3).card : ℝ) ≤
          Real.rpow d (3 - eta)) :
    ∀ S ∈ (auxiliaryHypergraph candidates R).powersetCard j,
      0 < w S → ∀ e ∈ S, ∀ f ∈ S, e ≠ f →
        ∀ r, 1 ≤ r → r < ell →
          (((conflictLinkLayer (alternatingCycleConflicts candidates R) e r) ∩
            conflictLinkLayer (alternatingCycleConflicts candidates R) f r).card : ℝ) ≤
              Real.rpow d ((r : ℝ) - eta) := by
  apply alternatingCycle_w3_of_three_bound candidates R d eta hd w
  intro S hSH hwS e he f hf hef
  apply hthree e f
  have hmatching : IsMatching (auxiliaryHypergraph candidates R) S := by
    by_contra hnot
    have hzero := htest.2.2.2 S hnot
    linarith
  exact hmatching.2 he hf hef

/-- Polynomial form of the disjoint-root W3 adapter. -/
theorem alternatingCycle_w3_of_disjoint_polynomial_bound {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {j ell : ℕ} (d eta K : ℝ) (hd : 0 ≤ d)
    (w : TestWeight (AuxVertex n k))
    (htest : IsTestFunction (auxiliaryHypergraph candidates R) j ell w)
    (hpoly : ∀ e f : Finset (AuxVertex n k), Disjoint e f →
      (((conflictLinkLayer (alternatingCycleConflicts candidates R) e 3) ∩
        conflictLinkLayer (alternatingCycleConflicts candidates R) f 3).card : ℝ) ≤
          K * (n : ℝ) ^ 8)
    (hthreshold : K * (n : ℝ) ^ 8 ≤ Real.rpow d (3 - eta)) :
    ∀ S ∈ (auxiliaryHypergraph candidates R).powersetCard j,
      0 < w S → ∀ e ∈ S, ∀ f ∈ S, e ≠ f →
        ∀ r, 1 ≤ r → r < ell →
          (((conflictLinkLayer (alternatingCycleConflicts candidates R) e r) ∩
            conflictLinkLayer (alternatingCycleConflicts candidates R) f r).card : ℝ) ≤
              Real.rpow d ((r : ℝ) - eta) := by
  apply alternatingCycle_w3_of_disjoint_three_bound
    candidates R d eta hd w htest
  intro e f hdisj
  exact (hpoly e f hdisj).trans hthreshold

/-- Application-scale W3 bound from the explicit common-link charge. -/
theorem alternatingCycle_w3_of_commonLink_n8 {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (hk : k ≤ n) {j ell : ℕ} (d eta : ℝ) (hd : 0 ≤ d)
    (w : TestWeight (AuxVertex n k))
    (htest : IsTestFunction (auxiliaryHypergraph candidates R) j ell w)
    (hthreshold : ((566231040 * n ^ 8 : ℕ) : ℝ) ≤
      Real.rpow d (3 - eta)) :
    ∀ S ∈ (auxiliaryHypergraph candidates R).powersetCard j,
      0 < w S → ∀ e ∈ S, ∀ f ∈ S, e ≠ f →
        ∀ r, 1 ≤ r → r < ell →
          (((conflictLinkLayer (alternatingCycleConflicts candidates R) e r) ∩
            conflictLinkLayer (alternatingCycleConflicts candidates R) f r).card : ℝ) ≤
              Real.rpow d ((r : ℝ) - eta) := by
  apply alternatingCycle_w3_of_disjoint_three_bound
    candidates R d eta hd w htest
  intro e f hdisj
  have hlink := alternatingCycle_commonThreeLink_le_disjoint_n8
    candidates R e f hdisj hk
  exact (by exact_mod_cast hlink :
    (((conflictLinkLayer (alternatingCycleConflicts candidates R) e 3) ∩
      conflictLinkLayer (alternatingCycleConflicts candidates R) f 3).card : ℝ) ≤
        ((566231040 * n ^ 8 : ℕ) : ℝ)).trans hthreshold

/-- Concrete polynomial-to-threshold bridge for W3.  The geometric charge
may be supplied as `K n⁸`; this theorem performs the exact comparison with
the conflict-free-matching threshold `d^(3-η)` and eliminates all other
link layers by four-uniformity. -/
theorem alternatingCycle_w3_of_polynomial_bound {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {j ell : ℕ} (d eta K : ℝ) (hd : 0 ≤ d)
    (w : TestWeight (AuxVertex n k))
    (hpoly : ∀ S ∈ (auxiliaryHypergraph candidates R).powersetCard j,
      0 < w S → ∀ e ∈ S, ∀ f ∈ S, e ≠ f →
        (((conflictLinkLayer (alternatingCycleConflicts candidates R) e 3) ∩
          conflictLinkLayer (alternatingCycleConflicts candidates R) f 3).card : ℝ) ≤
            K * (n : ℝ) ^ 8)
    (hthreshold : K * (n : ℝ) ^ 8 ≤ Real.rpow d (3 - eta)) :
    ∀ S ∈ (auxiliaryHypergraph candidates R).powersetCard j,
      0 < w S → ∀ e ∈ S, ∀ f ∈ S, e ≠ f →
        ∀ r, 1 ≤ r → r < ell →
          (((conflictLinkLayer (alternatingCycleConflicts candidates R) e r) ∩
            conflictLinkLayer (alternatingCycleConflicts candidates R) f r).card : ℝ) ≤
              Real.rpow d ((r : ℝ) - eta) := by
  apply alternatingCycle_w3_of_three_bound candidates R d eta hd w
  intro S hSH hwS e he f hf hef
  exact (hpoly S hSH hwS e he f hf hef).trans hthreshold

/-- Fully concrete W3 bridge from the host pair-codegree estimate.  No
test-specific geometric link hypothesis remains downstream. -/
theorem alternatingCycle_w3_of_maxCodegree {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (L : ℕ) (hcodeg : MaxCodegreeLE (auxiliaryHypergraph candidates R) 2 L)
    {j ell : ℕ} (d eta : ℝ) (hd : 0 ≤ d)
    (w : TestWeight (AuxVertex n k))
    (hthreshold : ((512 * n * n * k * L * L * L : ℕ) : ℝ) ≤
      Real.rpow d (3 - eta)) :
    ∀ S ∈ (auxiliaryHypergraph candidates R).powersetCard j,
      0 < w S → ∀ e ∈ S, ∀ f ∈ S, e ≠ f →
        ∀ r, 1 ≤ r → r < ell →
          (((conflictLinkLayer (alternatingCycleConflicts candidates R) e r) ∩
            conflictLinkLayer (alternatingCycleConflicts candidates R) f r).card : ℝ) ≤
              Real.rpow d ((r : ℝ) - eta) := by
  apply alternatingCycle_w3_of_three_bound candidates R d eta hd w
  intro S hSH hwS e he f hf hef
  have hlink := alternatingCycle_commonThreeLink_le_of_maxCodegree
    candidates R L hcodeg e f
  exact (by exact_mod_cast hlink :
    (((conflictLinkLayer (alternatingCycleConflicts candidates R) e 3) ∩
      conflictLinkLayer (alternatingCycleConflicts candidates R) f 3).card : ℝ) ≤
        ((512 * n * n * k * L * L * L : ℕ) : ℝ)).trans hthreshold

/-- Pair-test trackability from concrete host estimates; W3 is discharged
by the host pair-codegree bound and the local alternating-cycle charge. -/
theorem pairWeight_isTrackable_of_maxCodegree_bounds
    {n k : ℕ} {Q : Type*} [DecidableEq Q]
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (T : CrossSlotSystem (AuxVertex n k) Q (auxiliaryHypergraph candidates R))
    (ell L : ℕ) (d eta : ℝ) (hd : 0 ≤ d)
    (hcodeg : MaxCodegreeLE (auxiliaryHypergraph candidates R) 2 L)
    (hthreshold : ((512 * n * n * k * L * L * L : ℕ) : ℝ) ≤
      Real.rpow d (3 - eta))
    (hfiber : ∀ S, (T.slots.filter fun q => T.owner q = S).card ≤ ell)
    (htotal : Real.rpow d (2 + eta) ≤
      testTotal T.pairWeight (auxiliaryHypergraph candidates R) 2)
    (hext : ∀ j', 1 ≤ j' → j' < 2 → ∀ root,
      root ⊆ auxiliaryHypergraph candidates R → root.card = j' →
      testExtension T.pairWeight (auxiliaryHypergraph candidates R) 2 root ≤
        testTotal T.pairWeight (auxiliaryHypergraph candidates R) 2 /
          Real.rpow d ((j' : ℝ) + eta))
    (hconf : ∀ S ∈ (auxiliaryHypergraph candidates R).powersetCard 2,
      (∃ c ∈ alternatingCycleConflicts candidates R, c ⊆ S) →
        T.pairWeight S = 0) :
    IsTrackable (auxiliaryHypergraph candidates R)
      (alternatingCycleConflicts candidates R) 2 ell d eta T.pairWeight := by
  apply T.pairWeight_isTrackable_of_bounds
    (alternatingCycleConflicts candidates R) ell d eta hfiber htotal hext
  · exact alternatingCycle_w3_of_maxCodegree
      candidates R L hcodeg d eta hd T.pairWeight hthreshold
  · exact hconf

/-- Triple-test analogue of `pairWeight_isTrackable_of_host_bounds`. -/
theorem tripleWeight_isTrackable_of_maxCodegree_bounds
    {n k : ℕ} {Q : Type*} [DecidableEq Q]
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (T : CrossSlotSystem (AuxVertex n k) Q (auxiliaryHypergraph candidates R))
    (ell L : ℕ) (d eta : ℝ) (hd : 0 ≤ d)
    (hcodeg : MaxCodegreeLE (auxiliaryHypergraph candidates R) 2 L)
    (hthreshold : ((512 * n * n * k * L * L * L : ℕ) : ℝ) ≤
      Real.rpow d (3 - eta))
    (hfiber : ∀ S,
      (T.coverPairs.filter fun qe => T.extendedOwner qe = S).card ≤ ell)
    (htotal : Real.rpow d (3 + eta) ≤
      testTotal T.tripleWeight (auxiliaryHypergraph candidates R) 3)
    (hext : ∀ j', 1 ≤ j' → j' < 3 → ∀ root,
      root ⊆ auxiliaryHypergraph candidates R → root.card = j' →
      testExtension T.tripleWeight (auxiliaryHypergraph candidates R) 3 root ≤
        testTotal T.tripleWeight (auxiliaryHypergraph candidates R) 3 /
          Real.rpow d ((j' : ℝ) + eta))
    (hconf : ∀ S ∈ (auxiliaryHypergraph candidates R).powersetCard 3,
      (∃ c ∈ alternatingCycleConflicts candidates R, c ⊆ S) →
        T.tripleWeight S = 0) :
    IsTrackable (auxiliaryHypergraph candidates R)
      (alternatingCycleConflicts candidates R) 3 ell d eta T.tripleWeight := by
  apply T.tripleWeight_isTrackable_of_bounds
    (alternatingCycleConflicts candidates R) ell d eta hfiber htotal hext
  · exact alternatingCycle_w3_of_maxCodegree
      candidates R L hcodeg d eta hd T.tripleWeight hthreshold
  · exact hconf

/-- Application-scale pair-test trackability using the sharp common-link
charge `566231040 n⁸`. -/
theorem pairWeight_isTrackable_of_host_bounds
    {n k : ℕ} {Q : Type*} [DecidableEq Q]
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (T : CrossSlotSystem (AuxVertex n k) Q (auxiliaryHypergraph candidates R))
    (ell : ℕ) (d eta : ℝ) (hd : 0 ≤ d) (hk : k ≤ n)
    (hthreshold : ((566231040 * n ^ 8 : ℕ) : ℝ) ≤
      Real.rpow d (3 - eta))
    (hfiber : ∀ S, (T.slots.filter fun q => T.owner q = S).card ≤ ell)
    (htotal : Real.rpow d (2 + eta) ≤
      testTotal T.pairWeight (auxiliaryHypergraph candidates R) 2)
    (hext : ∀ j', 1 ≤ j' → j' < 2 → ∀ root,
      root ⊆ auxiliaryHypergraph candidates R → root.card = j' →
      testExtension T.pairWeight (auxiliaryHypergraph candidates R) 2 root ≤
        testTotal T.pairWeight (auxiliaryHypergraph candidates R) 2 /
          Real.rpow d ((j' : ℝ) + eta))
    (hconf : ∀ S ∈ (auxiliaryHypergraph candidates R).powersetCard 2,
      (∃ c ∈ alternatingCycleConflicts candidates R, c ⊆ S) →
        T.pairWeight S = 0) :
    IsTrackable (auxiliaryHypergraph candidates R)
      (alternatingCycleConflicts candidates R) 2 ell d eta T.pairWeight := by
  apply T.pairWeight_isTrackable_of_bounds
    (alternatingCycleConflicts candidates R) ell d eta hfiber htotal hext
  · exact alternatingCycle_w3_of_commonLink_n8 candidates R hk d eta hd
      T.pairWeight (T.pairWeight_isTestFunction hfiber) hthreshold
  · exact hconf

/-- Application-scale triple-test analogue. -/
theorem tripleWeight_isTrackable_of_host_bounds
    {n k : ℕ} {Q : Type*} [DecidableEq Q]
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (T : CrossSlotSystem (AuxVertex n k) Q (auxiliaryHypergraph candidates R))
    (ell : ℕ) (d eta : ℝ) (hd : 0 ≤ d) (hk : k ≤ n)
    (hthreshold : ((566231040 * n ^ 8 : ℕ) : ℝ) ≤
      Real.rpow d (3 - eta))
    (hfiber : ∀ S,
      (T.coverPairs.filter fun qe => T.extendedOwner qe = S).card ≤ ell)
    (htotal : Real.rpow d (3 + eta) ≤
      testTotal T.tripleWeight (auxiliaryHypergraph candidates R) 3)
    (hext : ∀ j', 1 ≤ j' → j' < 3 → ∀ root,
      root ⊆ auxiliaryHypergraph candidates R → root.card = j' →
      testExtension T.tripleWeight (auxiliaryHypergraph candidates R) 3 root ≤
        testTotal T.tripleWeight (auxiliaryHypergraph candidates R) 3 /
          Real.rpow d ((j' : ℝ) + eta))
    (hconf : ∀ S ∈ (auxiliaryHypergraph candidates R).powersetCard 3,
      (∃ c ∈ alternatingCycleConflicts candidates R, c ⊆ S) →
        T.tripleWeight S = 0) :
    IsTrackable (auxiliaryHypergraph candidates R)
      (alternatingCycleConflicts candidates R) 3 ell d eta T.tripleWeight := by
  apply T.tripleWeight_isTrackable_of_bounds
    (alternatingCycleConflicts candidates R) ell d eta hfiber htotal hext
  · exact alternatingCycle_w3_of_commonLink_n8 candidates R hk d eta hd
      T.tripleWeight (T.tripleWeight_isTestFunction hfiber) hthreshold
  · exact hconf

/-- Slots whose two-edge owner is selected. -/
def selectedSlots (T : CrossSlotSystem V Q H) (M : Hypergraph V) : Finset Q :=
  T.slots.filter fun q => T.owner q ⊆ M

/-- Selected slots covered by a third selected host edge. -/
def coveredSlots (T : CrossSlotSystem V Q H) (M : Hypergraph V) : Finset Q :=
  T.selectedSlots M |>.filter fun q => ∃ e ∈ M, T.covers q e

/-- Selected slots whose cross edge remains uncovered. -/
def uncoveredSlots (T : CrossSlotSystem V Q H) (M : Hypergraph V) : Finset Q :=
  T.selectedSlots M |>.filter fun q => ∀ e ∈ M, ¬T.covers q e

@[simp] theorem mem_selectedSlots {T : CrossSlotSystem V Q H}
    {M : Hypergraph V} {q : Q} :
    q ∈ T.selectedSlots M ↔ q ∈ T.slots ∧ T.owner q ⊆ M := by
  simp [selectedSlots]

@[simp] theorem mem_uncoveredSlots {T : CrossSlotSystem V Q H}
    {M : Hypergraph V} {q : Q} :
    q ∈ T.uncoveredSlots M ↔
      q ∈ T.slots ∧ T.owner q ⊆ M ∧ ∀ e ∈ M, ¬T.covers q e := by
  simp [uncoveredSlots, and_assoc]

theorem covers_unique_in_matching (T : CrossSlotSystem V Q H)
    {M : Hypergraph V} (hM : PairwiseDisjoint M) {q : Q} (hq : q ∈ T.slots)
    {e f : Finset V} (heM : e ∈ M) (hfM : f ∈ M)
    (he : T.covers q e) (hf : T.covers q f) : e = f := by
  by_contra hef
  have hd := hM heM hfM hef
  exact Finset.disjoint_left.mp hd (T.covers_key_mem q hq e he)
    (T.covers_key_mem q hq f hf)

theorem pairTotal_eq_selectedSlots (T : CrossSlotSystem V Q H)
    (M : Hypergraph V) :
    testTotal T.pairWeight M 2 = (T.selectedSlots M).card := by
  rw [T.testTotal_pairWeight]
  have heq :
      T.slots.filter (fun q => T.owner q ∈ M.powersetCard 2) =
        T.selectedSlots M := by
    ext q
    by_cases hq : q ∈ T.slots
    · simp [selectedSlots, hq, Finset.mem_powersetCard, T.owner_card q hq]
    · simp [selectedSlots, hq]
  rw [heq]

theorem tripleTotal_eq_coveredSlots (T : CrossSlotSystem V Q H)
    {M : Hypergraph V} (hM : IsMatching H M) :
    testTotal T.tripleWeight M 3 = (T.coveredSlots M).card := by
  rw [T.testTotal_tripleWeight]
  let P := T.coverPairs.filter fun qe => T.extendedOwner qe ∈ M.powersetCard 3
  have hcard : P.card = (T.coveredSlots M).card := by
    apply Finset.card_bij (fun qe _ => qe.1)
    · intro qe hqe
      rcases qe with ⟨q, e⟩
      have hP := Finset.mem_filter.mp hqe
      have hcp := mem_coverPairs_iff.mp hP.1
      have hsub := (Finset.mem_powersetCard.mp hP.2).1
      have howner : T.owner q ⊆ M := by
        exact (Finset.subset_insert e (T.owner q)).trans hsub
      have heM : e ∈ M := hsub (Finset.mem_insert_self e (T.owner q))
      simp only [coveredSlots, selectedSlots, Finset.mem_filter]
      exact ⟨⟨hcp.1, howner⟩, e, heM, hcp.2.2⟩
    · intro qe hqe rf hrf heq
      rcases qe with ⟨q, e⟩
      rcases rf with ⟨r, f⟩
      have hP := Finset.mem_filter.mp hqe
      have hP' := Finset.mem_filter.mp hrf
      have hcp := mem_coverPairs_iff.mp hP.1
      have hcp' := mem_coverPairs_iff.mp hP'.1
      have hsub := (Finset.mem_powersetCard.mp hP.2).1
      have hsub' := (Finset.mem_powersetCard.mp hP'.2).1
      have heM : e ∈ M := hsub (Finset.mem_insert_self e (T.owner q))
      have hfM : f ∈ M := hsub' (Finset.mem_insert_self f (T.owner r))
      rcases heq with rfl
      have hef := T.covers_unique_in_matching hM.2 hcp.1 heM hfM
        hcp.2.2 hcp'.2.2
      subst f
      rfl
    · intro q hq
      simp only [coveredSlots, selectedSlots, Finset.mem_filter] at hq
      obtain ⟨⟨hqslot, howner⟩, e, heM, hcover⟩ := hq
      refine ⟨(q, e), ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨mem_coverPairs_iff.mpr
        ⟨hqslot, hM.1 heM, hcover⟩, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩⟩
      · intro f hf
        simp only [extendedOwner, Finset.mem_insert] at hf
        rcases hf with rfl | hf
        · exact heM
        · exact howner hf
      · exact T.extendedOwner_card
          (mem_coverPairs_iff.mpr ⟨hqslot, hM.1 heM, hcover⟩)
  exact_mod_cast hcard

theorem card_selectedSlots_eq_card_covered_add_uncovered
    (T : CrossSlotSystem V Q H) (M : Hypergraph V) :
    (T.selectedSlots M).card =
      (T.coveredSlots M).card + (T.uncoveredSlots M).card := by
  have hunion : T.coveredSlots M ∪ T.uncoveredSlots M = T.selectedSlots M := by
    classical
    ext q
    simp only [coveredSlots, uncoveredSlots, Finset.mem_union, Finset.mem_filter]
    by_cases hq : q ∈ T.selectedSlots M
    · simp only [hq, true_and, iff_true]
      by_cases hc : ∃ e ∈ M, T.covers q e
      · exact Or.inl hc
      · right
        intro e heM hec
        exact hc ⟨e, heM, hec⟩
    · simp [hq]
  have hdisj : Disjoint (T.coveredSlots M) (T.uncoveredSlots M) := by
    rw [Finset.disjoint_left]
    intro q hc hu
    simp only [coveredSlots, Finset.mem_filter] at hc
    simp only [uncoveredSlots, Finset.mem_filter] at hu
    obtain ⟨e, heM, hec⟩ := hc.2
    exact hu.2 e heM hec
  rw [← hunion, Finset.card_union_of_disjoint hdisj]

/-- Exact pair-minus-triple identity.  This is the deterministic content of
the Joos--Mubayi P5 subtraction. -/
theorem pairTotal_sub_tripleTotal_eq_uncovered (T : CrossSlotSystem V Q H)
    {M : Hypergraph V} (hM : IsMatching H M) :
    testTotal T.pairWeight M 2 - testTotal T.tripleWeight M 3 =
      (T.uncoveredSlots M).card := by
  rw [T.pairTotal_eq_selectedSlots, T.tripleTotal_eq_coveredSlots hM]
  have hcard := T.card_selectedSlots_eq_card_covered_add_uncovered M
  have hcardR : ((T.selectedSlots M).card : ℝ) =
      (T.coveredSlots M).card + (T.uncoveredSlots M).card := by
    exact_mod_cast hcard
  linarith

end CrossSlotSystem

/-! ## Exact leave-degree bookkeeping -/

/-- Neighbours of `x` whose graph-edge vertex occurs in one auxiliary edge. -/
def incidentNeighbours {n k : ℕ} (x : Fin n)
    (e : Finset (AuxVertex n k)) : Finset (Fin n) :=
  Finset.univ.filter fun y => y ≠ x ∧ Sum.inl s(x, y) ∈ e

@[simp] theorem card_incidentNeighbours {n k : ℕ} (x : Fin n)
    (e : Finset (AuxVertex n k)) :
    (incidentNeighbours x e).card = graphIncidence x e := rfl

/-- All graph neighbours covered at `x` by an auxiliary family. -/
def selectedNeighbours {n k : ℕ} (M : Hypergraph (AuxVertex n k))
    (x : Fin n) : Finset (Fin n) :=
  M.biUnion (incidentNeighbours x)

theorem incidentNeighbours_disjoint_of_aux_disjoint {n k : ℕ}
    {x : Fin n} {e f : Finset (AuxVertex n k)} (hef : Disjoint e f) :
    Disjoint (incidentNeighbours x e) (incidentNeighbours x f) := by
  rw [Finset.disjoint_left]
  intro y hye hyf
  have he : Sum.inl s(x, y) ∈ e := (Finset.mem_filter.mp hye).2.2
  have hf : Sum.inl s(x, y) ∈ f := (Finset.mem_filter.mp hyf).2.2
  exact Finset.disjoint_left.mp hef he hf

/-- Since a matching has disjoint auxiliary supports, its selected graph
neighbours are counted without multiplicity. -/
theorem card_selectedNeighbours_eq_sum_graphIncidence {n k : ℕ}
    {H M : Hypergraph (AuxVertex n k)} (hM : IsMatching H M) (x : Fin n) :
    (selectedNeighbours M x).card = ∑ e ∈ M, graphIncidence x e := by
  rw [selectedNeighbours, Finset.card_biUnion]
  · rfl
  · intro e he f hf hef
    exact incidentNeighbours_disjoint_of_aux_disjoint (hM.2 he hf hef)

theorem mem_selectedNeighbours_iff {n k : ℕ}
    {M : Hypergraph (AuxVertex n k)} {x y : Fin n} :
    y ∈ selectedNeighbours M x ↔
      ∃ e ∈ M, y ≠ x ∧ Sum.inl s(x, y) ∈ e := by
  simp [selectedNeighbours, incidentNeighbours]

/-- A neighbour is selected by the auxiliary matching exactly when its
graph edge receives an old colour. -/
theorem mem_selectedNeighbours_iff_inducedColor_ne_none {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {MH : Hypergraph (AuxVertex n k)}
    (hmatch : IsMatching (auxiliaryHypergraph candidates R) MH)
    {x y : Fin n} (hyx : y ≠ x) :
    y ∈ selectedNeighbours MH x ↔
      inducedColor (blocksOfAuxFamily candidates R MH hmatch.1) x y ≠ none := by
  let BM := blocksOfAuxFamily candidates R MH hmatch.1
  have hBM : IsAuxMatching R BM :=
    blocksOfAuxFamily_isAuxMatching candidates R MH hmatch
  have hsupp := blocksOfAuxFamily_supports candidates R MH hmatch.1
  constructor
  · intro hy
    obtain ⟨e, heM, -, hexy⟩ := mem_selectedNeighbours_iff.mp hy
    have heimage : e ∈ BM.image TriangleBlock.auxSupport := by
      rw [hsupp]
      exact heM
    obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp heimage
    have hgraph : s(x, y) ∈ b.graphEdges := by
      have : Sum.inl s(x, y) ∈ b.auxSupport := hbe ▸ hexy
      simp only [TriangleBlock.auxSupport, Finset.mem_union,
        Finset.mem_image] at this
      rcases this with ⟨g, hg, hgeq⟩ | ⟨z, hz, hzeq⟩
      · exact Sum.inl.inj hgeq ▸ hg
      · cases hzeq
    obtain ⟨c, hc⟩ := b.support_has_color hgraph
    rw [Option.ne_none_iff_exists]
    exact ⟨c, ((inducedColor_eq_some_iff hBM).2 ⟨b, hb, hc⟩).symm⟩
  · intro hold
    rw [Option.ne_none_iff_exists] at hold
    obtain ⟨c, hc⟩ := hold
    obtain ⟨b, hb, hp⟩ := (inducedColor_eq_some_iff hBM).1 hc.symm
    rw [mem_selectedNeighbours_iff]
    refine ⟨b.auxSupport, ?_, hyx, b.paints_graph_mem hp⟩
    rw [← hsupp]
    exact Finset.mem_image.2 ⟨b, hb, rfl⟩

/-- Exact P4 identity: uncoloured neighbours plus the one-uniform selected
incidence total is `n-1`. -/
theorem leaveDegree_add_testTotal {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {MH : Hypergraph (AuxVertex n k)}
    (hmatch : IsMatching (auxiliaryHypergraph candidates R) MH) (x : Fin n) :
    (leaveDegree (inducedColor
        (blocksOfAuxFamily candidates R MH hmatch.1)) x : ℝ) +
      testTotal (leaveDegreeWeight (auxiliaryHypergraph candidates R) x) MH 1 =
        (n - 1 : ℕ) := by
  rw [testTotal_leaveDegreeWeight _ _ hmatch.1]
  have hcard := card_selectedNeighbours_eq_sum_graphIncidence hmatch x
  have hpartition :
      leaveDegree (inducedColor
        (blocksOfAuxFamily candidates R MH hmatch.1)) x +
        (selectedNeighbours MH x).card = n - 1 := by
    let all : Finset (Fin n) := Finset.univ.filter fun y => y ≠ x
    have hallcard : all.card = n - 1 := by
      rw [show all = Finset.univ.erase x by ext y; simp [all]]
      simp
    have hleave :
        Finset.univ.filter (fun y => y ≠ x ∧
          inducedColor (blocksOfAuxFamily candidates R MH hmatch.1) x y = none) =
          all \ selectedNeighbours MH x := by
      ext y
      by_cases hyx : y = x
      · subst y
        simp [all, selectedNeighbours, incidentNeighbours]
      · have hsel := mem_selectedNeighbours_iff_inducedColor_ne_none
          candidates R hmatch (x := x) (y := y) hyx
        simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
          true_and, all]
        rw [hsel]
        simp [hyx]
    have hsubset : selectedNeighbours MH x ⊆ all := by
      intro y hy
      obtain ⟨e, heM, hyx, hexy⟩ := mem_selectedNeighbours_iff.mp hy
      simp [all, hyx]
    have hcardle := Finset.card_le_card hsubset
    rw [leaveDegree, hleave, Finset.card_sdiff_of_subset hsubset, hallcard]
    omega
  have hcardR :
      (∑ e ∈ MH, (graphIncidence x e : ℝ)) =
        ((selectedNeighbours MH x).card : ℝ) := by
    exact_mod_cast hcard.symm
  rw [hcardR]
  exact_mod_cast hpartition

theorem leaveDegree_eq_sub_testTotal {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {MH : Hypergraph (AuxVertex n k)}
    (hmatch : IsMatching (auxiliaryHypergraph candidates R) MH) (x : Fin n) :
    (leaveDegree (inducedColor
        (blocksOfAuxFamily candidates R MH hmatch.1)) x : ℝ) =
      (n - 1 : ℕ) -
        testTotal (leaveDegreeWeight (auxiliaryHypergraph candidates R) x) MH 1 := by
  linarith [leaveDegree_add_testTotal candidates R hmatch x]

/-! ## Concrete Joos--Mubayi cross slots -/

/-- A cross slot remembers its two ordered auxiliary owner edges and the
canonically oriented graph edge whose absence is counted in P5. -/
structure JMCCrossSlot (n k : ℕ) where
  xEdge : Finset (AuxVertex n k)
  yEdge : Finset (AuxVertex n k)
  cross : Fin n × Fin n
  deriving DecidableEq, Fintype

namespace JMCCrossSlot

variable {n k : ℕ}

/-- The unordered two-edge owner of a concrete cross slot. -/
def owner (q : JMCCrossSlot n k) : Hypergraph (AuxVertex n k) :=
  {q.xEdge, q.yEdge}

/-- The auxiliary vertex representing the graph edge of the slot. -/
def key (q : JMCCrossSlot n k) : AuxVertex n k :=
  Sum.inl s(q.cross.1, q.cross.2)

end JMCCrossSlot

/-- The exact finite predicate defining the two-uniform families
`P_{j_x,j_y}` before they are split according to the two multiplicities.
The split itself is obtained by filtering with `paintMultiplicity` below. -/
def IsJMCCrossSlot {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (x y : Fin n) (q : JMCCrossSlot n k) : Prop :=
  q.xEdge ≠ q.yEdge ∧
  q.cross.1 ≠ q.cross.2 ∧
  JMCCrossSlot.key q ∉ vertexFinset q.owner ∧
  IsMatching (auxiliaryHypergraph candidates R) q.owner ∧
  ∃ bx ∈ candidates, Eligible R bx ∧ bx.auxSupport = q.xEdge ∧
    ∃ bY ∈ candidates, Eligible R bY ∧ bY.auxSupport = q.yEdge ∧
      ∃ c, (bx.Paints x q.cross.1 c ∧ bY.Paints y q.cross.2 c) ∨
        (bx.Paints x q.cross.2 c ∧ bY.Paints y q.cross.1 c)

/-- All concrete cross slots for the ordered base edge `xy`. -/
def jmcCrossSlots {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (x y : Fin n) : Finset (JMCCrossSlot n k) :=
  Finset.univ.filter (IsJMCCrossSlot candidates R x y)

@[simp] theorem mem_jmcCrossSlots {n k : ℕ}
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {x y : Fin n} {q : JMCCrossSlot n k} :
    q ∈ jmcCrossSlots candidates R x y ↔
      IsJMCCrossSlot candidates R x y q := by
  simp [jmcCrossSlots]

/-- A third auxiliary edge covers a slot precisely when it contains the
slot's cross graph edge and can be adjoined to its owner matching. -/
def JMCCovers {n k : ℕ}
  (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (q : JMCCrossSlot n k) (e : Finset (AuxVertex n k)) : Prop :=
  JMCCrossSlot.key q ∈ e ∧
    e ∉ q.owner ∧
    IsMatching (auxiliaryHypergraph candidates R) (insert e q.owner)

/-- The concrete two- and three-uniform slot system for an ordered base edge. -/
def jmcCrossSlotSystem {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (x y : Fin n) :
    CrossSlotSystem (AuxVertex n k) (JMCCrossSlot n k)
      (auxiliaryHypergraph candidates R) where
  slots := jmcCrossSlots candidates R x y
  owner := JMCCrossSlot.owner
  covers := JMCCovers candidates R
  coverKey := JMCCrossSlot.key
  owner_card := by
    intro q hq
    have hslot := (Finset.mem_filter.mp hq).2
    simp [JMCCrossSlot.owner, hslot.1]
  owner_matching := by
    intro q hq
    exact (Finset.mem_filter.mp hq).2.2.2.2.1
  covers_mem := by
    intro q hq e he
    exact (isMatching_insert_iff.mp he.2.2).1
  covers_fresh := by
    intro q hq e he
    exact he.2.1
  covers_disjoint := by
    intro q hq e he f hf
    exact (isMatching_insert_iff.mp he.2.2).2.2 f hf (by
      intro hfe
      subst f
      exact he.2.1 hf)
  covers_key_mem := by
    intro q hq e he
    exact he.1

/-- Number of edges of `b` incident with `x` and painted `c`.  For a
triangle block this belongs to `{0,1,2}`. -/
def paintMultiplicity {n k : ℕ} (b : TriangleBlock n k)
    (x : Fin n) (c : Fin k) : ℕ :=
  (Finset.univ.filter fun z => z ≠ x ∧ b.Paints x z c).card

/-- The three possible roles of a colour at a rooted block: the repeated
colour at its apex (multiplicity two), the repeated colour at an unmarked
leaf, or the singleton colour at an unmarked endpoint. -/
inductive JMCPaintRole
  | repeatedApex
  | repeatedLeaf
  | singletonLeaf
  deriving DecidableEq

instance : Fintype JMCPaintRole where
  elems := {.repeatedApex, .repeatedLeaf, .singletonLeaf}
  complete r := by cases r <;> simp

def JMCPaintRole.multiplicity : JMCPaintRole → ℕ
  | .repeatedApex => 2
  | .repeatedLeaf => 1
  | .singletonLeaf => 1

/-- A rooted block and colour have the indicated geometric role. -/
def HasJMCPaintRole {n k : ℕ} (b : TriangleBlock n k)
    (x : Fin n) (c : Fin k) : JMCPaintRole → Prop
  | .repeatedApex => c = b.repeated ∧ x = b.apex
  | .repeatedLeaf => c = b.repeated ∧ (x = b.left ∨ x = b.right)
  | .singletonLeaf => c = b.singleton ∧ (x = b.left ∨ x = b.right)

/-- Every painted rooted edge has exactly one of the three roles.  In
particular, multiplicity one explicitly includes both repeated-unmarked and
singleton-unmarked arms. -/
theorem exists_paintRole_of_paints {n k : ℕ} (b : TriangleBlock n k)
    {x z : Fin n} {c : Fin k} (h : b.Paints x z c) :
    ∃ r, HasJMCPaintRole b x c r := by
  rcases h with ⟨he, rfl⟩ | ⟨he, rfl⟩
  · rcases he with he | he <;> rw [Sym2.eq_iff] at he
    · rcases he with ⟨hx, -⟩ | ⟨hx, -⟩
      · exact ⟨.repeatedApex, rfl, hx⟩
      · exact ⟨.repeatedLeaf, rfl, Or.inl hx⟩
    · rcases he with ⟨hx, -⟩ | ⟨hx, -⟩
      · exact ⟨.repeatedApex, rfl, hx⟩
      · exact ⟨.repeatedLeaf, rfl, Or.inr hx⟩
  · rw [Sym2.eq_iff] at he
    rcases he with ⟨hx, -⟩ | ⟨hx, -⟩
    · exact ⟨.singletonLeaf, rfl, Or.inl hx⟩
    · exact ⟨.singletonLeaf, rfl, Or.inr hx⟩

/-- The role names recover the numerical multiplicities: the repeated
apex contributes two arms, while each kind of unmarked leaf contributes
one. -/
theorem paintMultiplicity_eq_role {n k : ℕ} (b : TriangleBlock n k)
    (x : Fin n) (c : Fin k) (r : JMCPaintRole)
    (h : HasJMCPaintRole b x c r) :
    paintMultiplicity b x c = r.multiplicity := by
  cases r with
  | repeatedApex =>
      rcases h with ⟨rfl, rfl⟩
      unfold paintMultiplicity
      rw [show (Finset.univ.filter fun z : Fin n =>
          z ≠ b.apex ∧ b.Paints b.apex z b.repeated) =
          {b.left, b.right} by
        ext z
        simp only [ne_eq, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
        rintro (rfl | rfl)
        · exact b.apex_ne_left.symm
        · exact b.apex_ne_right.symm]
      simp [JMCPaintRole.multiplicity, b.left_ne_right]
  | repeatedLeaf =>
      rcases h with ⟨rfl, rfl | rfl⟩
      · unfold paintMultiplicity
        rw [show (Finset.univ.filter fun z : Fin n =>
            z ≠ b.left ∧ b.Paints b.left z b.repeated) = {b.apex} by
          ext z
          simp only [ne_eq, mem_filter, mem_univ, true_and, mem_singleton]
          rintro rfl
          exact b.apex_ne_left]
        rfl
      · unfold paintMultiplicity
        rw [show (Finset.univ.filter fun z : Fin n =>
            z ≠ b.right ∧ b.Paints b.right z b.repeated) = {b.apex} by
          ext z
          simp only [ne_eq, mem_filter, mem_univ, true_and, mem_singleton]
          rintro rfl
          exact b.apex_ne_right]
        rfl
  | singletonLeaf =>
      rcases h with ⟨rfl, rfl | rfl⟩
      · unfold paintMultiplicity
        rw [show (Finset.univ.filter fun z : Fin n =>
            z ≠ b.left ∧ b.Paints b.left z b.singleton) = {b.right} by
          ext z
          simp only [ne_eq, mem_filter, mem_univ, true_and, mem_singleton]
          rintro rfl
          exact b.left_ne_right.symm]
        rfl
      · unfold paintMultiplicity
        rw [show (Finset.univ.filter fun z : Fin n =>
            z ≠ b.right ∧ b.Paints b.right z b.singleton) = {b.left} by
          ext z
          simp only [ne_eq, mem_filter, mem_univ, true_and, mem_singleton]
          rintro rfl
          exact b.left_ne_right]
        rfl

/-- The role-refined version of the nine pair families. -/
def HasJMCRolePair {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (x y : Fin n) (rx ry : JMCPaintRole) (q : JMCCrossSlot n k) : Prop :=
  ∃ bx ∈ candidates, Eligible R bx ∧ bx.auxSupport = q.xEdge ∧
    ∃ bY ∈ candidates, Eligible R bY ∧ bY.auxSupport = q.yEdge ∧
      bx ≠ bY ∧ ∃ c, HasJMCPaintRole bx x c rx ∧ HasJMCPaintRole bY y c ry ∧
        ((bx.Paints x q.cross.1 c ∧ bY.Paints y q.cross.2 c) ∨
          (bx.Paints x q.cross.2 c ∧ bY.Paints y q.cross.1 c))

def jmcRoleSlotSystem {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (x y : Fin n) (rx ry : JMCPaintRole) :
    CrossSlotSystem (AuxVertex n k) (JMCCrossSlot n k)
      (auxiliaryHypergraph candidates R) :=
  (jmcCrossSlotSystem candidates R x y).restrict
    (HasJMCRolePair candidates R x y rx ry)

/-- Exact selected-pair count for each of the nine role-pair families. -/
theorem jmcRole_pairTotal {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (x y : Fin n) (rx ry : JMCPaintRole)
    (M : Hypergraph (AuxVertex n k)) :
    testTotal (jmcRoleSlotSystem candidates R x y rx ry).pairWeight M 2 =
      (((jmcRoleSlotSystem candidates R x y rx ry).slots.filter
        fun q => (jmcRoleSlotSystem candidates R x y rx ry).owner q ∈
          M.powersetCard 2).card : ℝ) := by
  exact CrossSlotSystem.testTotal_pairWeight
    (jmcRoleSlotSystem candidates R x y rx ry) M

/-- Exact rooted extension count for a role-pair family. -/
theorem jmcRole_pairExtension {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (x y : Fin n) (rx ry : JMCPaintRole)
    (M : Hypergraph (AuxVertex n k)) (root : Hypergraph (AuxVertex n k)) :
    testExtension (jmcRoleSlotSystem candidates R x y rx ry).pairWeight M 2 root =
      (((jmcRoleSlotSystem candidates R x y rx ry).slots.filter
        fun q => (jmcRoleSlotSystem candidates R x y rx ry).owner q ∈
          (M.powersetCard 2).filter (root ⊆ ·)).card : ℝ) := by
  exact CrossSlotSystem.testExtension_pairWeight
    (jmcRoleSlotSystem candidates R x y rx ry) M root

/-- Exact selected-triple count for a role-pair cover family. -/
theorem jmcRole_tripleTotal {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (x y : Fin n) (rx ry : JMCPaintRole)
    (M : Hypergraph (AuxVertex n k)) :
    testTotal (jmcRoleSlotSystem candidates R x y rx ry).tripleWeight M 3 =
      (((jmcRoleSlotSystem candidates R x y rx ry).coverPairs.filter
        fun qe => CrossSlotSystem.extendedOwner
          (jmcRoleSlotSystem candidates R x y rx ry) qe ∈
            M.powersetCard 3).card : ℝ) := by
  exact CrossSlotSystem.testTotal_tripleWeight
    (jmcRoleSlotSystem candidates R x y rx ry) M

/-- Exact rooted extension count for a role-pair cover family. -/
theorem jmcRole_tripleExtension {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (x y : Fin n) (rx ry : JMCPaintRole)
    (M : Hypergraph (AuxVertex n k)) (root : Hypergraph (AuxVertex n k)) :
    testExtension (jmcRoleSlotSystem candidates R x y rx ry).tripleWeight M 3 root =
      (((jmcRoleSlotSystem candidates R x y rx ry).coverPairs.filter
        fun qe => CrossSlotSystem.extendedOwner
          (jmcRoleSlotSystem candidates R x y rx ry) qe ∈
            (M.powersetCard 3).filter (root ⊆ ·)).card : ℝ) := by
  exact CrossSlotSystem.testExtension_tripleWeight
    (jmcRoleSlotSystem candidates R x y rx ry) M root

/-- The `j_x,j_y` subfamily from the paper.  The witnesses record that the
common colour occurs exactly `j_x` times at `x` in the first owner block and
exactly `j_y` times at `y` in the second. -/
def HasJMCMultiplicity {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (x y : Fin n) (jx jy : ℕ) (q : JMCCrossSlot n k) : Prop :=
  ∃ bx ∈ candidates, Eligible R bx ∧ bx.auxSupport = q.xEdge ∧
    ∃ bY ∈ candidates, Eligible R bY ∧ bY.auxSupport = q.yEdge ∧
      bx ≠ bY ∧ ∃ c, paintMultiplicity bx x c = jx ∧
        paintMultiplicity bY y c = jy ∧
          ((bx.Paints x q.cross.1 c ∧ bY.Paints y q.cross.2 c) ∨
            (bx.Paints x q.cross.2 c ∧ bY.Paints y q.cross.1 c))

/-- Every geometric role pair lies in the corresponding numerical
multiplicity family.  Thus multiplicity one contains both repeated-leaf and
singleton-leaf arms, including every mixed ordered pair of those roles. -/
theorem HasJMCRolePair.toMultiplicity {n k : ℕ}
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {x y : Fin n} {rx ry : JMCPaintRole} {q : JMCCrossSlot n k}
    (h : HasJMCRolePair candidates R x y rx ry q) :
    HasJMCMultiplicity candidates R x y rx.multiplicity ry.multiplicity q := by
  rcases h with
    ⟨bx, hbxc, hbxE, hbxs, bY, hbYc, hbYE, hbYs, hbne, c,
      hrx, hry, hpaint⟩
  exact ⟨bx, hbxc, hbxE, hbxs, bY, hbYc, hbYE, hbYs, hbne, c,
    paintMultiplicity_eq_role bx x c rx hrx,
    paintMultiplicity_eq_role bY y c ry hry, hpaint⟩

/-- The concrete slot system restricted to the multiplicity pair
`(j_x,j_y)`. -/
def jmcMultiplicitySlotSystem {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (x y : Fin n) (jx jy : ℕ) :
    CrossSlotSystem (AuxVertex n k) (JMCCrossSlot n k)
      (auxiliaryHypergraph candidates R) :=
  (jmcCrossSlotSystem candidates R x y).restrict
    (HasJMCMultiplicity candidates R x y jx jy)

/-- The role-refined slots embed in the matching multiplicity family. -/
theorem jmcRole_slots_subset_multiplicity_slots {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (x y : Fin n) (rx ry : JMCPaintRole) :
    (jmcRoleSlotSystem candidates R x y rx ry).slots ⊆
      (jmcMultiplicitySlotSystem candidates R x y
        rx.multiplicity ry.multiplicity).slots := by
  intro q hq
  obtain ⟨hbase, hrole⟩ := CrossSlotSystem.mem_restrict_slots.mp hq
  exact CrossSlotSystem.mem_restrict_slots.mpr
    ⟨hbase, HasJMCRolePair.toMultiplicity hrole⟩

/-- Exact selected-pair count for the `j_x,j_y` family. -/
theorem jmcMultiplicity_pairTotal {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (x y : Fin n) (jx jy : ℕ)
    (M : Hypergraph (AuxVertex n k)) :
    testTotal (jmcMultiplicitySlotSystem candidates R x y jx jy).pairWeight M 2 =
      (((jmcMultiplicitySlotSystem candidates R x y jx jy).slots.filter
        fun q => (jmcMultiplicitySlotSystem candidates R x y jx jy).owner q ∈
          M.powersetCard 2).card : ℝ) := by
  exact CrossSlotSystem.testTotal_pairWeight
    (jmcMultiplicitySlotSystem candidates R x y jx jy) M

/-- Exact one-root/two-root extension count for the pair family. -/
theorem jmcMultiplicity_pairExtension {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (x y : Fin n) (jx jy : ℕ)
    (M : Hypergraph (AuxVertex n k)) (root : Hypergraph (AuxVertex n k)) :
    testExtension
        (jmcMultiplicitySlotSystem candidates R x y jx jy).pairWeight M 2 root =
      (((jmcMultiplicitySlotSystem candidates R x y jx jy).slots.filter
        fun q => (jmcMultiplicitySlotSystem candidates R x y jx jy).owner q ∈
          (M.powersetCard 2).filter (root ⊆ ·)).card : ℝ) := by
  exact CrossSlotSystem.testExtension_pairWeight
    (jmcMultiplicitySlotSystem candidates R x y jx jy) M root

/-- Exact selected-triple count for the `j_x,j_y` extension family. -/
theorem jmcMultiplicity_tripleTotal {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (x y : Fin n) (jx jy : ℕ)
    (M : Hypergraph (AuxVertex n k)) :
    testTotal (jmcMultiplicitySlotSystem candidates R x y jx jy).tripleWeight M 3 =
      (((jmcMultiplicitySlotSystem candidates R x y jx jy).coverPairs.filter
        fun qe => CrossSlotSystem.extendedOwner
          (jmcMultiplicitySlotSystem candidates R x y jx jy) qe ∈
            M.powersetCard 3).card : ℝ) := by
  exact CrossSlotSystem.testTotal_tripleWeight
    (jmcMultiplicitySlotSystem candidates R x y jx jy) M

/-- Exact one- or two-root extension count for the triple family. -/
theorem jmcMultiplicity_tripleExtension {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (x y : Fin n) (jx jy : ℕ)
    (M : Hypergraph (AuxVertex n k)) (root : Hypergraph (AuxVertex n k)) :
    testExtension
        (jmcMultiplicitySlotSystem candidates R x y jx jy).tripleWeight M 3 root =
      (((jmcMultiplicitySlotSystem candidates R x y jx jy).coverPairs.filter
        fun qe => CrossSlotSystem.extendedOwner
          (jmcMultiplicitySlotSystem candidates R x y jx jy) qe ∈
            (M.powersetCard 3).filter (root ⊆ ·)).card : ℝ) := by
  exact CrossSlotSystem.testExtension_tripleWeight
    (jmcMultiplicitySlotSystem candidates R x y jx jy) M root

/-! ## Terminal estimates imply P4 and P5 -/

/-- Deterministic P5 domination required of a family of concrete slot
systems.  The next theorem supplies the complete analytic adapter once this
finite injection has been established. -/
def CrossObstructionsControlledBySlots {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (T : Fin n → Fin n →
      CrossSlotSystem (AuxVertex n k) (JMCCrossSlot n k)
        (auxiliaryHypergraph candidates R)) : Prop :=
  ∀ MH, (hmatch : IsMatching (auxiliaryHypergraph candidates R) MH) →
    ∀ x y, x ≠ y →
      ((crossObstructions (inducedColor
        (blocksOfAuxFamily candidates R MH hmatch.1)) x y).card : ℝ) ≤
        testTotal (T x y).pairWeight MH 2 -
          testTotal (T x y).tripleWeight MH 3

/-- The explicit numerical host bounds used after the CFM terminal
estimates.  No asymptotic notation is hidden here. -/
structure TrackedHostBounds {n k : ℕ}
    (B : ℕ) (candidates : Finset (TriangleBlock n k))
    (R : RetainedLabels n k)
    (T : Fin n → Fin n →
      CrossSlotSystem (AuxVertex n k) (JMCCrossSlot n k)
        (auxiliaryHypergraph candidates R))
    (d err : ℝ) where
  leave : ∀ x,
    (n - 1 : ℕ) -
      (1 - err) * Real.rpow d (-1 : ℝ) *
        testTotal (leaveDegreeWeight (auxiliaryHypergraph candidates R) x)
          (auxiliaryHypergraph candidates R) 1 ≤ B
  cross : ∀ x y, x ≠ y →
    (1 + err) * Real.rpow d (-2 : ℝ) *
        testTotal (T x y).pairWeight (auxiliaryHypergraph candidates R) 2 -
      (1 - err) * Real.rpow d (-3 : ℝ) *
        testTotal (T x y).tripleWeight (auxiliaryHypergraph candidates R) 3 ≤ B

/-- Exact terminal-estimate adapter.  The index maps identify the 1-, 2-,
and 3-uniform Joos--Mubayi tests inside an arbitrary finite test family. -/
theorem testsControlLeave_of_trackedBounds {n k B : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {ι : Type} (d eta : ℝ) (j : ι → ℕ)
    (w : ι → TestWeight (AuxVertex n k))
    (T : Fin n → Fin n →
      CrossSlotSystem (AuxVertex n k) (JMCCrossSlot n k)
        (auxiliaryHypergraph candidates R))
    (leaveIndex : Fin n → ι) (pairIndex tripleIndex : Fin n → Fin n → ι)
    (hjLeave : ∀ x, j (leaveIndex x) = 1)
    (hwLeave : ∀ x, w (leaveIndex x) =
      leaveDegreeWeight (auxiliaryHypergraph candidates R) x)
    (hjPair : ∀ x y, j (pairIndex x y) = 2)
    (hwPair : ∀ x y, w (pairIndex x y) = (T x y).pairWeight)
    (hjTriple : ∀ x y, j (tripleIndex x y) = 3)
    (hwTriple : ∀ x y, w (tripleIndex x y) = (T x y).tripleWeight)
    (hslots : CrossObstructionsControlledBySlots candidates R T)
    (hbounds : TrackedHostBounds B candidates R T d
      (Real.rpow d (-(eta ^ 3)))) :
    TestsControlLeave B candidates R d eta j w := by
  intro MH hmatch hest
  let BM := blocksOfAuxFamily candidates R MH hmatch.1
  constructor
  · intro x
    have hterminal := (hest (leaveIndex x)).1
    rw [hjLeave x, hwLeave x] at hterminal
    norm_num only [Nat.cast_ofNat] at hterminal
    have hb := hbounds.leave x
    have hexact := leaveDegree_eq_sub_testTotal candidates R hmatch x
    have hreal :
        (leaveDegree (inducedColor BM) x : ℝ) ≤ (B : ℝ) := by
      dsimp [BM]
      rw [hexact]
      exact le_trans (sub_le_sub_left hterminal _) hb
    exact_mod_cast hreal
  · intro x y hxy
    have hp := (hest (pairIndex x y)).2
    have ht := (hest (tripleIndex x y)).1
    rw [hjPair x y, hwPair x y] at hp
    rw [hjTriple x y, hwTriple x y] at ht
    norm_num only [Nat.cast_ofNat] at hp ht
    have hb := hbounds.cross x y hxy
    have hobs := hslots MH hmatch x y hxy
    have hreal : ((crossObstructions (inducedColor BM) x y).card : ℝ) ≤
        (B : ℝ) := by
      dsimp [BM] at hobs ⊢
      calc
        ((crossObstructions (inducedColor
            (blocksOfAuxFamily candidates R MH hmatch.1)) x y).card : ℝ) ≤
            testTotal (T x y).pairWeight MH 2 -
              testTotal (T x y).tripleWeight MH 3 := hobs
        _ ≤ (1 + Real.rpow d (-(eta ^ 3))) * Real.rpow d (-2 : ℝ) *
              testTotal (T x y).pairWeight
                (auxiliaryHypergraph candidates R) 2 -
            (1 - Real.rpow d (-(eta ^ 3))) * Real.rpow d (-3 : ℝ) *
              testTotal (T x y).tripleWeight
                (auxiliaryHypergraph candidates R) 3 := sub_le_sub hp ht
        _ ≤ B := hb
    exact_mod_cast hreal

/-! ## The concrete P5 injection -/

theorem blocksOfAuxFamily_member_spec {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {MH : Hypergraph (AuxVertex n k)} (hsub : MH ⊆ auxiliaryHypergraph candidates R)
    {b : TriangleBlock n k}
    (hb : b ∈ blocksOfAuxFamily candidates R MH hsub) :
    b ∈ candidates ∧ Eligible R b ∧ b.auxSupport ∈ MH := by
  unfold blocksOfAuxFamily at hb
  obtain ⟨e, heattach, heq⟩ := Finset.mem_image.mp hb
  rcases e with ⟨e, heM⟩
  dsimp at heq
  subst b
  have hspec := blockOfAuxEdge_spec candidates R e (hsub heM)
  refine ⟨hspec.1, hspec.2.1, ?_⟩
  simpa only [blockOfAuxEdge_support] using heM

/-- Every concrete cross obstruction gives an uncovered tracked slot.  The
slot retains the ordered obstruction pair, which will make the resulting
map injective. -/
theorem exists_uncovered_jmcSlot_of_crossObstruction {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {MH : Hypergraph (AuxVertex n k)}
    (hmatch : IsMatching (auxiliaryHypergraph candidates R) MH)
    {x y : Fin n} (hxy : x ≠ y)
    {p : Fin n × Fin n}
    (hp : p ∈ crossObstructions (inducedColor
      (blocksOfAuxFamily candidates R MH hmatch.1)) x y) :
    ∃ q ∈ (jmcCrossSlotSystem candidates R x y).uncoveredSlots MH,
      q.cross = p := by
  let BM := blocksOfAuxFamily candidates R MH hmatch.1
  have hBM : IsAuxMatching R BM :=
    blocksOfAuxFamily_isAuxMatching candidates R MH hmatch
  have hobs := (Finset.mem_filter.mp hp).2
  rcases hobs with
    ⟨hp12, hp1x, hp1y, hp2x, hp2y, hleave, c,
      (⟨hx, hy⟩ | ⟨hx, hy⟩)⟩
  · obtain ⟨bx, hbx, hpaintx⟩ := (inducedColor_eq_some_iff hBM).1 hx
    obtain ⟨bY, hbY, hpainty⟩ := (inducedColor_eq_some_iff hBM).1 hy
    have hbxspec := blocksOfAuxFamily_member_spec candidates R hmatch.1 hbx
    have hbYspec := blocksOfAuxFamily_member_spec candidates R hmatch.1 hbY
    have hD : FourDistinct x p.1 y p.2 := by
      unfold FourDistinct
      exact ⟨hp1x.symm, hxy, hp2x.symm, hp1y, ne_of_lt hp12,
        hp2y.symm⟩
    have hbne : bx ≠ bY := by
      intro heq
      subst bY
      exact bx.no_disjoint_painted_edges hD hpaintx hpainty
    have hsne : bx.auxSupport ≠ bY.auxSupport :=
      auxSupports_ne_of_blocks_ne hBM hbx hbY hbne
    let q : JMCCrossSlot n k :=
      ⟨bx.auxSupport, bY.auxSupport, p⟩
    have howner : q.owner ⊆ MH := by
      intro e he
      simp only [q, JMCCrossSlot.owner, Finset.mem_insert,
        Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact hbxspec.2.2
      · exact hbYspec.2.2
    have hownermatch :
        IsMatching (auxiliaryHypergraph candidates R) q.owner :=
      hmatch.mono howner
    have hkeyfresh : q.key ∉ vertexFinset q.owner := by
      intro hkeyOwner
      obtain ⟨e, heowner, hkeye⟩ := mem_vertexFinset.mp hkeyOwner
      have hsel : p.2 ∈ selectedNeighbours MH p.1 :=
        mem_selectedNeighbours_iff.mpr
          ⟨e, howner heowner, ne_of_gt hp12, by
            simpa [q, JMCCrossSlot.key] using hkeye⟩
      have hne := (mem_selectedNeighbours_iff_inducedColor_ne_none
        candidates R hmatch (ne_of_gt hp12)).1 hsel
      exact hne hleave
    have hqslot : q ∈ jmcCrossSlots candidates R x y := by
      apply mem_jmcCrossSlots.mpr
      refine ⟨hsne, ne_of_lt hp12, hkeyfresh, hownermatch, bx, hbxspec.1,
        hbxspec.2.1, rfl, bY, hbYspec.1, hbYspec.2.1, rfl, c, ?_⟩
      exact Or.inl ⟨hpaintx, hpainty⟩
    have huncovered : q ∈
        (jmcCrossSlotSystem candidates R x y).uncoveredSlots MH := by
      apply CrossSlotSystem.mem_uncoveredSlots.mpr
      refine ⟨hqslot, howner, ?_⟩
      intro e heM hecover
      have hkey : Sum.inl s(p.1, p.2) ∈ e := hecover.1
      have hsel : p.2 ∈ selectedNeighbours MH p.1 :=
        mem_selectedNeighbours_iff.mpr
          ⟨e, heM, ne_of_gt hp12, hkey⟩
      have hne := (mem_selectedNeighbours_iff_inducedColor_ne_none
        candidates R hmatch (ne_of_gt hp12)).1 hsel
      exact hne hleave
    exact ⟨q, huncovered, rfl⟩
  · obtain ⟨bx, hbx, hpaintx⟩ := (inducedColor_eq_some_iff hBM).1 hx
    obtain ⟨bY, hbY, hpainty⟩ := (inducedColor_eq_some_iff hBM).1 hy
    have hbxspec := blocksOfAuxFamily_member_spec candidates R hmatch.1 hbx
    have hbYspec := blocksOfAuxFamily_member_spec candidates R hmatch.1 hbY
    have hD : FourDistinct x p.2 y p.1 := by
      unfold FourDistinct
      exact ⟨hp2x.symm, hxy, hp1x.symm, hp2y, (ne_of_lt hp12).symm,
        hp1y.symm⟩
    have hbne : bx ≠ bY := by
      intro heq
      subst bY
      exact bx.no_disjoint_painted_edges hD hpaintx hpainty
    have hsne : bx.auxSupport ≠ bY.auxSupport :=
      auxSupports_ne_of_blocks_ne hBM hbx hbY hbne
    let q : JMCCrossSlot n k :=
      ⟨bx.auxSupport, bY.auxSupport, p⟩
    have howner : q.owner ⊆ MH := by
      intro e he
      simp only [q, JMCCrossSlot.owner, Finset.mem_insert,
        Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact hbxspec.2.2
      · exact hbYspec.2.2
    have hownermatch :
        IsMatching (auxiliaryHypergraph candidates R) q.owner :=
      hmatch.mono howner
    have hkeyfresh : q.key ∉ vertexFinset q.owner := by
      intro hkeyOwner
      obtain ⟨e, heowner, hkeye⟩ := mem_vertexFinset.mp hkeyOwner
      have hsel : p.2 ∈ selectedNeighbours MH p.1 :=
        mem_selectedNeighbours_iff.mpr
          ⟨e, howner heowner, ne_of_gt hp12, by
            simpa [q, JMCCrossSlot.key] using hkeye⟩
      have hne := (mem_selectedNeighbours_iff_inducedColor_ne_none
        candidates R hmatch (ne_of_gt hp12)).1 hsel
      exact hne hleave
    have hqslot : q ∈ jmcCrossSlots candidates R x y := by
      apply mem_jmcCrossSlots.mpr
      refine ⟨hsne, ne_of_lt hp12, hkeyfresh, hownermatch, bx, hbxspec.1,
        hbxspec.2.1, rfl, bY, hbYspec.1, hbYspec.2.1, rfl, c, ?_⟩
      exact Or.inr ⟨hpaintx, hpainty⟩
    have huncovered : q ∈
        (jmcCrossSlotSystem candidates R x y).uncoveredSlots MH := by
      apply CrossSlotSystem.mem_uncoveredSlots.mpr
      refine ⟨hqslot, howner, ?_⟩
      intro e heM hecover
      have hkey : Sum.inl s(p.1, p.2) ∈ e := hecover.1
      have hsel : p.2 ∈ selectedNeighbours MH p.1 :=
        mem_selectedNeighbours_iff.mpr
          ⟨e, heM, ne_of_gt hp12, hkey⟩
      have hne := (mem_selectedNeighbours_iff_inducedColor_ne_none
        candidates R hmatch (ne_of_gt hp12)).1 hsel
      exact hne hleave
    exact ⟨q, huncovered, rfl⟩

/-- Every obstruction belongs to one of the nine explicit role-pair
families, including both multiplicity-one roles and all mixed arms. -/
theorem exists_rolePair_uncovered_of_crossObstruction {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {MH : Hypergraph (AuxVertex n k)}
    (hmatch : IsMatching (auxiliaryHypergraph candidates R) MH)
    {x y : Fin n} (hxy : x ≠ y) {p : Fin n × Fin n}
    (hp : p ∈ crossObstructions (inducedColor
      (blocksOfAuxFamily candidates R MH hmatch.1)) x y) :
    ∃ rx ry q,
      q ∈ (jmcRoleSlotSystem candidates R x y rx ry).uncoveredSlots MH ∧
      q.cross = p := by
  obtain ⟨q, hq, hcross⟩ :=
    exists_uncovered_jmcSlot_of_crossObstruction candidates R hmatch hxy hp
  have hdata := CrossSlotSystem.mem_uncoveredSlots.mp hq
  have hslot := mem_jmcCrossSlots.mp hdata.1
  rcases hslot with
    ⟨hsne, hcrossne, hkeyfresh, hownerMatch, bx, hbxc, hbxE, hbxs,
      bY, hbYc, hbYE, hbYs, c, hpaint⟩
  have hbne : bx ≠ bY := by
    intro h
    apply hsne
    rw [← hbxs, ← hbYs, h]
  rcases hpaint with hpaint | hpaint
  · obtain ⟨rx, hrx⟩ := exists_paintRole_of_paints bx hpaint.1
    obtain ⟨ry, hry⟩ := exists_paintRole_of_paints bY hpaint.2
    refine ⟨rx, ry, q, ?_, hcross⟩
    apply CrossSlotSystem.mem_uncoveredSlots.mpr
    refine ⟨CrossSlotSystem.mem_restrict_slots.mpr ⟨hdata.1, ?_⟩,
      hdata.2.1, hdata.2.2⟩
    exact ⟨bx, hbxc, hbxE, hbxs, bY, hbYc, hbYE, hbYs, hbne, c,
      hrx, hry, Or.inl hpaint⟩
  · obtain ⟨rx, hrx⟩ := exists_paintRole_of_paints bx hpaint.1
    obtain ⟨ry, hry⟩ := exists_paintRole_of_paints bY hpaint.2
    refine ⟨rx, ry, q, ?_, hcross⟩
    apply CrossSlotSystem.mem_uncoveredSlots.mpr
    refine ⟨CrossSlotSystem.mem_restrict_slots.mpr ⟨hdata.1, ?_⟩,
      hdata.2.1, hdata.2.2⟩
    exact ⟨bx, hbxc, hbxE, hbxs, bY, hbYc, hbYE, hbYs, hbne, c,
      hrx, hry, Or.inr hpaint⟩

/-- A role tag paired with its concrete slot. -/
structure JMCRoleTaggedSlot (n k : ℕ) where
  xRole : JMCPaintRole
  yRole : JMCPaintRole
  slot : JMCCrossSlot n k
  deriving DecidableEq, Fintype

/-- Disjoint union of the nine uncovered role-pair families. -/
def allRoleUncoveredSlots {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (x y : Fin n) (M : Hypergraph (AuxVertex n k)) :
    Finset (JMCRoleTaggedSlot n k) :=
  Finset.univ.filter fun z =>
    z.slot ∈
      (jmcRoleSlotSystem candidates R x y z.xRole z.yRole).uncoveredSlots M

/-- The tagged union is equivalent to the dependent sum of the nine
role-pair subfamilies. -/
def allRoleUncoveredEquiv {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (x y : Fin n) (M : Hypergraph (AuxVertex n k)) :
    {z // z ∈ allRoleUncoveredSlots candidates R x y M} ≃
      Σ rx : JMCPaintRole, Σ ry : JMCPaintRole,
        {q // q ∈ (jmcRoleSlotSystem candidates R x y rx ry).uncoveredSlots M} where
  toFun z := ⟨z.1.xRole, z.1.yRole, z.1.slot, by
    simpa only [allRoleUncoveredSlots, Finset.mem_filter, Finset.mem_univ,
      true_and] using z.2⟩
  invFun z := ⟨⟨z.1, z.2.1, z.2.2.1⟩, by
    simp only [allRoleUncoveredSlots, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact z.2.2.2⟩
  left_inv z := by rcases z with ⟨⟨rx, ry, q⟩, hz⟩; rfl
  right_inv z := by rcases z with ⟨rx, ry, q, hq⟩; rfl

theorem allRoleUncoveredSlots_card {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (x y : Fin n) (M : Hypergraph (AuxVertex n k)) :
    (allRoleUncoveredSlots candidates R x y M).card =
      ∑ rx : JMCPaintRole, ∑ ry : JMCPaintRole,
        ((jmcRoleSlotSystem candidates R x y rx ry).uncoveredSlots M).card := by
  rw [← Fintype.card_coe,
    Fintype.card_congr (allRoleUncoveredEquiv candidates R x y M)]
  simp only [Fintype.card_sigma, Fintype.card_coe]

/-- A canonical role-tagged uncovered slot for each obstruction. -/
def roleObstructionSlot {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {MH : Hypergraph (AuxVertex n k)}
    (hmatch : IsMatching (auxiliaryHypergraph candidates R) MH)
    (x y : Fin n) (hxy : x ≠ y) (p : Fin n × Fin n) :
    JMCRoleTaggedSlot n k := by
  classical
  let old := inducedColor (blocksOfAuxFamily candidates R MH hmatch.1)
  exact if hp : p ∈ crossObstructions old x y then
    let h := exists_rolePair_uncovered_of_crossObstruction
      candidates R hmatch hxy hp
    ⟨Classical.choose h, Classical.choose (Classical.choose_spec h),
      Classical.choose (Classical.choose_spec (Classical.choose_spec h))⟩
  else ⟨.repeatedApex, .repeatedApex, ⟨∅, ∅, p⟩⟩

theorem roleObstructionSlot_spec {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {MH : Hypergraph (AuxVertex n k)}
    (hmatch : IsMatching (auxiliaryHypergraph candidates R) MH)
    {x y : Fin n} (hxy : x ≠ y) {p : Fin n × Fin n}
    (hp : p ∈ crossObstructions (inducedColor
      (blocksOfAuxFamily candidates R MH hmatch.1)) x y) :
    roleObstructionSlot candidates R hmatch x y hxy p ∈
        allRoleUncoveredSlots candidates R x y MH ∧
      (roleObstructionSlot candidates R hmatch x y hxy p).slot.cross = p := by
  classical
  unfold roleObstructionSlot
  simp only [dif_pos hp]
  let h := exists_rolePair_uncovered_of_crossObstruction
    candidates R hmatch hxy hp
  constructor
  · simp only [allRoleUncoveredSlots, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec h))).1
  · exact (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec h))).2

/-- Final role-complete P5 injection. -/
theorem crossObstructions_card_le_allRoleUncovered {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {MH : Hypergraph (AuxVertex n k)}
    (hmatch : IsMatching (auxiliaryHypergraph candidates R) MH)
    {x y : Fin n} (hxy : x ≠ y) :
    (crossObstructions (inducedColor
      (blocksOfAuxFamily candidates R MH hmatch.1)) x y).card ≤
        (allRoleUncoveredSlots candidates R x y MH).card := by
  let F := roleObstructionSlot candidates R hmatch x y hxy
  apply Finset.card_le_card_of_injOn F
  · intro p hp
    exact (roleObstructionSlot_spec candidates R hmatch hxy hp).1
  · intro p hp q hq heq
    have hc := congrArg (fun z : JMCRoleTaggedSlot n k => z.slot.cross) heq
    rw [(roleObstructionSlot_spec candidates R hmatch hxy hp).2,
      (roleObstructionSlot_spec candidates R hmatch hxy hq).2] at hc
    exact hc

/-- Real-valued P5 domination by the sum of the nine role-refined pair
minus triple statistics.  This is the form consumed by the terminal CFM
estimates. -/
theorem crossObstructions_cast_le_sum_roleTests {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {MH : Hypergraph (AuxVertex n k)}
    (hmatch : IsMatching (auxiliaryHypergraph candidates R) MH)
    {x y : Fin n} (hxy : x ≠ y) :
    ((crossObstructions (inducedColor
      (blocksOfAuxFamily candidates R MH hmatch.1)) x y).card : ℝ) ≤
      ∑ rx : JMCPaintRole, ∑ ry : JMCPaintRole,
        (testTotal (jmcRoleSlotSystem candidates R x y rx ry).pairWeight MH 2 -
          testTotal (jmcRoleSlotSystem candidates R x y rx ry).tripleWeight MH 3) := by
  calc
    ((crossObstructions (inducedColor
        (blocksOfAuxFamily candidates R MH hmatch.1)) x y).card : ℝ) ≤
        ((allRoleUncoveredSlots candidates R x y MH).card : ℝ) := by
      exact_mod_cast crossObstructions_card_le_allRoleUncovered
        candidates R hmatch hxy
    _ = ∑ rx : JMCPaintRole, ∑ ry : JMCPaintRole,
        (((jmcRoleSlotSystem candidates R x y rx ry).uncoveredSlots MH).card : ℝ) := by
      rw [allRoleUncoveredSlots_card]
      simp only [Nat.cast_sum]
    _ = ∑ rx : JMCPaintRole, ∑ ry : JMCPaintRole,
        (testTotal (jmcRoleSlotSystem candidates R x y rx ry).pairWeight MH 2 -
          testTotal (jmcRoleSlotSystem candidates R x y rx ry).tripleWeight MH 3) := by
      apply Finset.sum_congr rfl
      intro rx hrx
      apply Finset.sum_congr rfl
      intro ry hry
      exact (CrossSlotSystem.pairTotal_sub_tripleTotal_eq_uncovered
        (jmcRoleSlotSystem candidates R x y rx ry) hmatch).symm

/-- A canonical uncovered slot chosen for each obstruction. -/
def crossObstructionSlot {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {MH : Hypergraph (AuxVertex n k)}
    (hmatch : IsMatching (auxiliaryHypergraph candidates R) MH)
    (x y : Fin n) (hxy : x ≠ y) (p : Fin n × Fin n) :
    JMCCrossSlot n k := by
  classical
  let old := inducedColor (blocksOfAuxFamily candidates R MH hmatch.1)
  exact if hp : p ∈ crossObstructions old x y then
    Classical.choose
      (exists_uncovered_jmcSlot_of_crossObstruction candidates R hmatch hxy hp)
  else ⟨∅, ∅, p⟩

theorem crossObstructionSlot_spec {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {MH : Hypergraph (AuxVertex n k)}
    (hmatch : IsMatching (auxiliaryHypergraph candidates R) MH)
    {x y : Fin n} (hxy : x ≠ y) {p : Fin n × Fin n}
    (hp : p ∈ crossObstructions (inducedColor
      (blocksOfAuxFamily candidates R MH hmatch.1)) x y) :
    crossObstructionSlot candidates R hmatch x y hxy p ∈
        (jmcCrossSlotSystem candidates R x y).uncoveredSlots MH ∧
      (crossObstructionSlot candidates R hmatch x y hxy p).cross = p := by
  classical
  unfold crossObstructionSlot
  simp only [dif_pos hp]
  exact Classical.choose_spec
    (exists_uncovered_jmcSlot_of_crossObstruction candidates R hmatch hxy hp)

theorem crossObstructions_card_le_uncoveredSlots {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {MH : Hypergraph (AuxVertex n k)}
    (hmatch : IsMatching (auxiliaryHypergraph candidates R) MH)
    {x y : Fin n} (hxy : x ≠ y) :
    (crossObstructions (inducedColor
      (blocksOfAuxFamily candidates R MH hmatch.1)) x y).card ≤
        ((jmcCrossSlotSystem candidates R x y).uncoveredSlots MH).card := by
  let F := crossObstructionSlot candidates R hmatch x y hxy
  apply Finset.card_le_card_of_injOn F
  · intro p hp
    exact (crossObstructionSlot_spec candidates R hmatch hxy hp).1
  · intro p hp q hq heq
    have hc := congrArg JMCCrossSlot.cross heq
    rw [(crossObstructionSlot_spec candidates R hmatch hxy hp).2,
      (crossObstructionSlot_spec candidates R hmatch hxy hq).2] at hc
    exact hc

theorem jmcCrossObstructionsControlled {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k) :
    CrossObstructionsControlledBySlots candidates R
      (jmcCrossSlotSystem candidates R) := by
  intro MH hmatch x y hxy
  have hcard := crossObstructions_card_le_uncoveredSlots
    candidates R hmatch hxy
  have hid := CrossSlotSystem.pairTotal_sub_tripleTotal_eq_uncovered
    (jmcCrossSlotSystem candidates R x y) hmatch
  rw [hid]
  exact_mod_cast hcard

/-! ## The complete finite family of tracked tests -/

/-- An ordered pair of distinct roots.  Making distinctness part of the
finite index type prevents the conflict-free matching theorem from asking
for spurious diagonal pair and triple tests. -/
structure JMCDistinctRootPair (n : ℕ) where
  x : Fin n
  y : Fin n
  x_ne_y : x ≠ y
  deriving DecidableEq, Fintype

/-- One of the nine role refinements over an ordered pair of distinct
roots. -/
structure JMCRolePairIndex (n : ℕ) extends JMCDistinctRootPair n where
  leftRole : JMCPaintRole
  rightRole : JMCPaintRole
  deriving DecidableEq, Fintype

def JMCDistinctRootPair.withRoles {n : ℕ} (p : JMCDistinctRootPair n)
    (leftRole rightRole : JMCPaintRole) : JMCRolePairIndex n where
  toJMCDistinctRootPair := p
  leftRole := leftRole
  rightRole := rightRole

/-! ### The concentration/tracked-test role bridge -/

/-- The role names used by the retention calculation and by the tracked
slot system are canonically identical. -/
def auxRootRoleEquiv : AuxConcentration.RootRole ≃ JMCPaintRole where
  toFun
    | .repeatedApex => .repeatedApex
    | .repeatedLeaf => .repeatedLeaf
    | .singletonLeaf => .singletonLeaf
  invFun
    | .repeatedApex => .repeatedApex
    | .repeatedLeaf => .repeatedLeaf
    | .singletonLeaf => .singletonLeaf
  left_inv r := by cases r <;> rfl
  right_inv r := by cases r <;> rfl

@[simp] theorem auxRootRoleEquiv_repeatedApex :
    auxRootRoleEquiv AuxConcentration.RootRole.repeatedApex =
      JMCPaintRole.repeatedApex := rfl

@[simp] theorem auxRootRoleEquiv_repeatedLeaf :
    auxRootRoleEquiv AuxConcentration.RootRole.repeatedLeaf =
      JMCPaintRole.repeatedLeaf := rfl

@[simp] theorem auxRootRoleEquiv_singletonLeaf :
    auxRootRoleEquiv AuxConcentration.RootRole.singletonLeaf =
      JMCPaintRole.singletonLeaf := rfl

@[simp] theorem auxRootRoleEquiv_multiplicity
    (r : AuxConcentration.RootRole) :
    (auxRootRoleEquiv r).multiplicity = r.multiplicity := by
  cases r <;> rfl

@[simp] theorem auxRoleFits_iff_hasJMCPaintRole {n k : ℕ}
    (r : AuxConcentration.RootRole) (b : TriangleBlock n k)
    (x : Fin n) (c : Fin k) :
    AuxConcentration.RoleFits r b x c ↔
      HasJMCPaintRole b x c (auxRootRoleEquiv r) := by
  cases r <;> simp [AuxConcentration.RoleFits, HasJMCPaintRole, eq_comm]

/-- The proof-carrying role-pair family concentrated in
`AuxConcentration` is exactly the proof-carrying family tracked by the
conflict-free matching theorem. -/
def auxPairRoleIndexEquiv (n : ℕ) :
    AuxConcentration.PairRoleIndex n ≃ JMCRolePairIndex n where
  toFun a :=
    { toJMCDistinctRootPair :=
        { x := a.x, y := a.y, x_ne_y := a.x_ne_y }
      leftRole := auxRootRoleEquiv a.leftRole
      rightRole := auxRootRoleEquiv a.rightRole }
  invFun a :=
    { x := a.x, y := a.y, x_ne_y := a.x_ne_y
      leftRole := auxRootRoleEquiv.symm a.leftRole
      rightRole := auxRootRoleEquiv.symm a.rightRole }
  left_inv a := by
    rcases a with ⟨x, y, hxy, rx, ry⟩
    cases rx <;> cases ry <;> rfl
  right_inv a := by
    rcases a with ⟨⟨x, y, hxy⟩, rx, ry⟩
    cases rx <;> cases ry <;> rfl

@[simp] theorem auxPairRoleIndexEquiv_x {n : ℕ}
    (a : AuxConcentration.PairRoleIndex n) :
    (auxPairRoleIndexEquiv n a).x = a.x := rfl

@[simp] theorem auxPairRoleIndexEquiv_y {n : ℕ}
    (a : AuxConcentration.PairRoleIndex n) :
    (auxPairRoleIndexEquiv n a).y = a.y := rfl

@[simp] theorem auxPairRoleIndexEquiv_leftRole {n : ℕ}
    (a : AuxConcentration.PairRoleIndex n) :
    (auxPairRoleIndexEquiv n a).leftRole = auxRootRoleEquiv a.leftRole := rfl

@[simp] theorem auxPairRoleIndexEquiv_rightRole {n : ℕ}
    (a : AuxConcentration.PairRoleIndex n) :
    (auxPairRoleIndexEquiv n a).rightRole = auxRootRoleEquiv a.rightRole := rfl

@[simp] theorem auxPairRoleIndexEquiv_symm_x {n : ℕ}
    (a : JMCRolePairIndex n) :
    ((auxPairRoleIndexEquiv n).symm a).x = a.x := by
  rcases a with ⟨⟨x, y, hxy⟩, rx, ry⟩
  cases rx <;> cases ry <;> rfl

@[simp] theorem auxPairRoleIndexEquiv_symm_y {n : ℕ}
    (a : JMCRolePairIndex n) :
    ((auxPairRoleIndexEquiv n).symm a).y = a.y := by
  rcases a with ⟨⟨x, y, hxy⟩, rx, ry⟩
  cases rx <;> cases ry <;> rfl

@[simp] theorem auxPairRoleIndexEquiv_symm_leftRole {n : ℕ}
    (a : JMCRolePairIndex n) :
    auxRootRoleEquiv ((auxPairRoleIndexEquiv n).symm a).leftRole =
      a.leftRole := by
  rcases a with ⟨⟨x, y, hxy⟩, rx, ry⟩
  cases rx <;> cases ry <;> rfl

@[simp] theorem auxPairRoleIndexEquiv_symm_rightRole {n : ℕ}
    (a : JMCRolePairIndex n) :
    auxRootRoleEquiv ((auxPairRoleIndexEquiv n).symm a).rightRole =
      a.rightRole := by
  rcases a with ⟨⟨x, y, hxy⟩, rx, ry⟩
  cases rx <;> cases ry <;> rfl

/-- A canonical endpoint painted in the prescribed role. -/
def jmcRoleNeighbor {n k : ℕ} (b : TriangleBlock n k) (x : Fin n) :
    JMCPaintRole → Fin n
  | .repeatedApex => b.left
  | .repeatedLeaf => b.apex
  | .singletonLeaf => if x = b.left then b.right else b.left

theorem paints_jmcRoleNeighbor {n k : ℕ} (b : TriangleBlock n k)
    (x : Fin n) (c : Fin k) (r : JMCPaintRole)
    (h : HasJMCPaintRole b x c r) :
    b.Paints x (jmcRoleNeighbor b x r) c := by
  cases r with
  | repeatedApex =>
      rcases h with ⟨rfl, rfl⟩
      simp [jmcRoleNeighbor, TriangleBlock.Paints]
  | repeatedLeaf =>
      rcases h with ⟨rfl, rfl | rfl⟩ <;>
        simp [jmcRoleNeighbor, TriangleBlock.Paints]
  | singletonLeaf =>
      rcases h with ⟨rfl, rfl | rfl⟩
      · simp [jmcRoleNeighbor, TriangleBlock.Paints,
          b.left_ne_right]
      · simp [jmcRoleNeighbor, TriangleBlock.Paints,
          b.left_ne_right]

theorem auxRoleFits_colour_unique {n k : ℕ}
    (r : AuxConcentration.RootRole) (b : TriangleBlock n k)
    (x : Fin n) {c d : Fin k}
    (hc : AuxConcentration.RoleFits r b x c)
    (hd : AuxConcentration.RoleFits r b x d) : c = d := by
  cases r with
  | repeatedApex => exact hc.1.symm.trans hd.1
  | repeatedLeaf => exact hc.1.symm.trans hd.1
  | singletonLeaf => exact hc.1.symm.trans hd.1

@[simp] theorem mem_auxPairRoleWitnesses_iff {n k : ℕ}
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {a : AuxConcentration.PairRoleIndex n}
    {w : AuxConcentration.PairWitness n k} :
    w ∈ AuxConcentration.pairRoleWitnesses candidates R a ↔
      AuxConcentration.PairWitness.Geometry candidates a.toPairTestIndex w ∧
        w.leftRole = a.leftRole ∧ w.rightRole = a.rightRole ∧
          AuxConcentration.PairWitness.RetentionValid R w := by
  simp [AuxConcentration.pairRoleWitnesses,
    AuxConcentration.geometricRoleWitnesses,
    AuxConcentration.geometricWitnesses, and_assoc]

/-- Forget a concentrated common-colour witness to one concrete cross
slot, choosing canonically one painted endpoint on each side. -/
def auxPairWitnessToSlot {n k : ℕ}
    (a : AuxConcentration.PairRoleIndex n)
    (w : AuxConcentration.PairWitness n k) : JMCCrossSlot n k where
  xEdge := w.leftBlock.auxSupport
  yEdge := w.rightBlock.auxSupport
  cross :=
    (jmcRoleNeighbor w.leftBlock a.x (auxRootRoleEquiv a.leftRole),
      jmcRoleNeighbor w.rightBlock a.y (auxRootRoleEquiv a.rightRole))

/-- The witness generates a trackable slot exactly when its canonical cross
edge is off-diagonal and its key is fresh from both owner edges. -/
def AuxPairWitnessKeyFresh {n k : ℕ}
    (a : AuxConcentration.PairRoleIndex n)
    (w : AuxConcentration.PairWitness n k) : Prop :=
  (auxPairWitnessToSlot a w).cross.1 ≠
      (auxPairWitnessToSlot a w).cross.2 ∧
    (auxPairWitnessToSlot a w).key ∉
      vertexFinset (auxPairWitnessToSlot a w).owner

def freshPairRoleWitnesses {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (a : AuxConcentration.PairRoleIndex n) :
    Finset (AuxConcentration.PairWitness n k) :=
  (AuxConcentration.pairRoleWitnesses candidates R a).filter
    (AuxPairWitnessKeyFresh a)

def freshPairRoleWitnessWeight {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (a : AuxConcentration.PairRoleIndex n) (Q : Hypergraph (AuxVertex n k)) : ℝ :=
  ((freshPairRoleWitnesses candidates R a).filter fun w ↦
    w.support = Q).card

theorem jmcRoleNeighbor_mem_blockVertices {n k : ℕ}
    (b : TriangleBlock n k) (x : Fin n) (r : JMCPaintRole) :
    jmcRoleNeighbor b x r ∈ AuxConcentration.blockVertices b := by
  cases r with
  | repeatedApex => simp [jmcRoleNeighbor, AuxConcentration.blockVertices]
  | repeatedLeaf => simp [jmcRoleNeighbor, AuxConcentration.blockVertices]
  | singletonLeaf =>
      by_cases hx : x = b.left <;>
        simp [jmcRoleNeighbor, AuxConcentration.blockVertices, hx]

theorem graphAuxMem_endpoints_mem_blockVertices {n k : ℕ}
    (b : TriangleBlock n k) (u v : Fin n)
    (h : Sum.inl s(u, v) ∈ b.auxSupport) :
    u ∈ AuxConcentration.blockVertices b ∧
      v ∈ AuxConcentration.blockVertices b := by
  simp only [TriangleBlock.auxSupport, Finset.mem_union,
    Finset.mem_image] at h
  rcases h with ⟨e, he, hinj⟩ | ⟨z, hz, hcontra⟩
  · have hes : e = s(u, v) := Sum.inl.inj hinj
    subst e
    simp only [TriangleBlock.graphEdges, Finset.mem_insert,
      Finset.mem_singleton] at he
    simp [AuxConcentration.blockVertices] at he ⊢
    aesop
  · cases hcontra

theorem not_disjoint_blockVertices_of_not_keyFresh {n k : ℕ}
    (a : AuxConcentration.PairRoleIndex n)
    (w : AuxConcentration.PairWitness n k)
    (hbad : ¬ AuxPairWitnessKeyFresh a w) :
    ¬ Disjoint (AuxConcentration.blockVertices w.leftBlock)
      (AuxConcentration.blockVertices w.rightBlock) := by
  intro hdisj
  apply hbad
  constructor
  · intro heq
    have heq' :
        jmcRoleNeighbor w.leftBlock a.x (auxRootRoleEquiv a.leftRole) =
          jmcRoleNeighbor w.rightBlock a.y (auxRootRoleEquiv a.rightRole) := by
      simpa [auxPairWitnessToSlot] using heq
    exact (Finset.disjoint_left.mp hdisj)
      (jmcRoleNeighbor_mem_blockVertices w.leftBlock a.x
        (auxRootRoleEquiv a.leftRole))
      (heq'.symm ▸ jmcRoleNeighbor_mem_blockVertices w.rightBlock a.y
        (auxRootRoleEquiv a.rightRole))
  · intro hkey
    obtain ⟨e, heowner, hkeye⟩ := mem_vertexFinset.mp hkey
    simp only [auxPairWitnessToSlot, JMCCrossSlot.owner,
      Finset.mem_insert, Finset.mem_singleton] at heowner
    rcases heowner with rfl | rfl
    · have hv :=
        (graphAuxMem_endpoints_mem_blockVertices w.leftBlock _ _ hkeye).2
      exact (Finset.disjoint_left.mp hdisj) hv
        (jmcRoleNeighbor_mem_blockVertices w.rightBlock a.y
          (auxRootRoleEquiv a.rightRole))
    · have hu :=
        (graphAuxMem_endpoints_mem_blockVertices w.rightBlock _ _ hkeye).1
      exact (Finset.disjoint_left.mp hdisj)
        (jmcRoleNeighbor_mem_blockVertices w.leftBlock a.x
          (auxRootRoleEquiv a.leftRole)) hu

theorem pairRoleWitness_mem_overlapping_of_not_fresh {n k : ℕ}
    {R : RetainedLabels n k} {a : AuxConcentration.PairRoleIndex n}
    {w : AuxConcentration.PairWitness n k}
    (hw : w ∈ AuxConcentration.pairRoleWitnesses
      (AuxConcentration.allTriangleBlocks n k) R a)
    (hbad : ¬ AuxPairWitnessKeyFresh a w) :
    w ∈ AuxConcentration.overlappingRoleWitnesses (k := k) a := by
  have hdata := mem_auxPairRoleWitnesses_iff.mp hw
  simp only [AuxConcentration.overlappingRoleWitnesses,
    AuxConcentration.geometricRoleWitnesses, Finset.mem_filter]
  refine ⟨⟨?_, hdata.2.1, hdata.2.2.1⟩,
    not_disjoint_blockVertices_of_not_keyFresh a w hbad⟩
  simpa [AuxConcentration.geometricWitnesses] using hdata.1

/-- At most the explicitly counted overlapping-witness remainder is lost
when key freshness is imposed. -/
theorem pairRoleWitnesses_card_le_fresh_add_overlap {n k : ℕ}
    (R : RetainedLabels n k) (a : AuxConcentration.PairRoleIndex n) :
    (AuxConcentration.pairRoleWitnesses
        (AuxConcentration.allTriangleBlocks n k) R a).card ≤
      (freshPairRoleWitnesses
        (AuxConcentration.allTriangleBlocks n k) R a).card +
        (AuxConcentration.overlappingRoleWitnesses (k := k) a).card := by
  let W := AuxConcentration.pairRoleWitnesses
    (AuxConcentration.allTriangleBlocks n k) R a
  let F := freshPairRoleWitnesses
    (AuxConcentration.allTriangleBlocks n k) R a
  let O := AuxConcentration.overlappingRoleWitnesses (k := k) a
  have hsub : W ⊆ F ∪ O := by
    intro w hw
    by_cases hfresh : AuxPairWitnessKeyFresh a w
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hw, hfresh⟩)
    · exact Finset.mem_union_right _
        (pairRoleWitness_mem_overlapping_of_not_fresh hw hfresh)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le F O)

theorem pairRoleWitnesses_card_le_fresh_add_n6 {n k : ℕ}
    (R : RetainedLabels n k) (a : AuxConcentration.PairRoleIndex n)
    (hk : k ≤ n) :
    (AuxConcentration.pairRoleWitnesses
        (AuxConcentration.allTriangleBlocks n k) R a).card ≤
      (freshPairRoleWitnesses
        (AuxConcentration.allTriangleBlocks n k) R a).card + 9 * n ^ 6 := by
  refine (pairRoleWitnesses_card_le_fresh_add_overlap R a).trans ?_
  apply Nat.add_le_add_left
  exact (AuxConcentration.card_overlappingRoleWitnesses_le a a.x_ne_y).trans <| by
    calc
      9 * n ^ 3 * k ^ 3 ≤ 9 * n ^ 3 * n ^ 3 := by gcongr
      _ = 9 * n ^ 6 := by ring

theorem auxPairWitness_left_eligible {n k : ℕ}
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {a : AuxConcentration.PairRoleIndex n}
    {w : AuxConcentration.PairWitness n k}
    (hw : w ∈ AuxConcentration.pairRoleWitnesses candidates R a) :
    Eligible R w.leftBlock := by
  have hret := (mem_auxPairRoleWitnesses_iff.mp hw).2.2.2
  constructor
  · intro z hz
    apply hret.1
    exact Finset.mem_union_left _ hz
  · intro hz
    exact (Finset.disjoint_left.mp hret.2)
      (by simp [AuxConcentration.PairWitness.negativeLabels]) hz

theorem auxPairWitness_right_eligible {n k : ℕ}
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {a : AuxConcentration.PairRoleIndex n}
    {w : AuxConcentration.PairWitness n k}
    (hw : w ∈ AuxConcentration.pairRoleWitnesses candidates R a) :
    Eligible R w.rightBlock := by
  have hret := (mem_auxPairRoleWitnesses_iff.mp hw).2.2.2
  constructor
  · intro z hz
    apply hret.1
    exact Finset.mem_union_right _ hz
  · intro hz
    exact (Finset.disjoint_left.mp hret.2)
      (by simp [AuxConcentration.PairWitness.negativeLabels]) hz

theorem auxPairWitness_left_mem_host {n k : ℕ}
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {a : AuxConcentration.PairRoleIndex n}
    {w : AuxConcentration.PairWitness n k}
    (hw : w ∈ AuxConcentration.pairRoleWitnesses candidates R a) :
    w.leftBlock.auxSupport ∈ auxiliaryHypergraph candidates R := by
  have hdata := mem_auxPairRoleWitnesses_iff.mp hw
  rw [auxiliaryHypergraph]
  exact Finset.mem_image.mpr ⟨w.leftBlock,
    Finset.mem_filter.mpr ⟨hdata.1.2.1, auxPairWitness_left_eligible hw⟩, rfl⟩

theorem auxPairWitness_right_mem_host {n k : ℕ}
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {a : AuxConcentration.PairRoleIndex n}
    {w : AuxConcentration.PairWitness n k}
    (hw : w ∈ AuxConcentration.pairRoleWitnesses candidates R a) :
    w.rightBlock.auxSupport ∈ auxiliaryHypergraph candidates R := by
  have hdata := mem_auxPairRoleWitnesses_iff.mp hw
  rw [auxiliaryHypergraph]
  exact Finset.mem_image.mpr ⟨w.rightBlock,
    Finset.mem_filter.mpr ⟨hdata.1.2.2.1, auxPairWitness_right_eligible hw⟩, rfl⟩

theorem auxPairWitness_left_rootLabel_mem {n k : ℕ}
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {a : AuxConcentration.PairRoleIndex n}
    {w : AuxConcentration.PairWitness n k}
    (hw : w ∈ AuxConcentration.pairRoleWitnesses candidates R a) :
    Sum.inr (a.x, w.common) ∈ w.leftBlock.auxSupport := by
  have hfit := (mem_auxPairRoleWitnesses_iff.mp hw).1.2.2.2.2.2.2.2.1
  have hjmc := (auxRoleFits_iff_hasJMCPaintRole _ _ _ _).mp (by
    simpa [AuxConcentration.PairRoleIndex.toPairTestIndex,
      (mem_auxPairRoleWitnesses_iff.mp hw).2.1] using hfit)
  exact w.leftBlock.paints_label_mem
    (paints_jmcRoleNeighbor w.leftBlock a.x w.common _ hjmc)

theorem auxPairWitness_right_rootLabel_mem {n k : ℕ}
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {a : AuxConcentration.PairRoleIndex n}
    {w : AuxConcentration.PairWitness n k}
    (hw : w ∈ AuxConcentration.pairRoleWitnesses candidates R a) :
    Sum.inr (a.y, w.common) ∈ w.rightBlock.auxSupport := by
  have hfit := (mem_auxPairRoleWitnesses_iff.mp hw).1.2.2.2.2.2.2.2.2
  have hjmc := (auxRoleFits_iff_hasJMCPaintRole _ _ _ _).mp (by
    simpa [AuxConcentration.PairRoleIndex.toPairTestIndex,
      (mem_auxPairRoleWitnesses_iff.mp hw).2.2.1] using hfit)
  exact w.rightBlock.paints_label_mem
    (paints_jmcRoleNeighbor w.rightBlock a.y w.common _ hjmc)

theorem pairRoleWitness_common_eq_of_leftSupport_eq {n k : ℕ}
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {a : AuxConcentration.PairRoleIndex n}
    {w z : AuxConcentration.PairWitness n k}
    (hw : w ∈ AuxConcentration.pairRoleWitnesses candidates R a)
    (hz : z ∈ AuxConcentration.pairRoleWitnesses candidates R a)
    (hsupport : w.leftBlock.auxSupport = z.leftBlock.auxSupport) :
    w.common = z.common := by
  have hblock := AuxConcentration.auxSupport_injective hsupport
  have hwdata := mem_auxPairRoleWitnesses_iff.mp hw
  have hzdata := mem_auxPairRoleWitnesses_iff.mp hz
  have hwfit := hwdata.1.2.2.2.2.2.2.2.1
  have hzfit := hzdata.1.2.2.2.2.2.2.2.1
  have hzfit' : AuxConcentration.RoleFits w.leftRole w.leftBlock
      a.x z.common := by
    simpa [AuxConcentration.PairRoleIndex.toPairTestIndex, hblock,
      hwdata.2.1.trans hzdata.2.1.symm] using hzfit
  exact auxRoleFits_colour_unique w.leftRole w.leftBlock a.x hwfit hzfit'

theorem pairRoleWitness_common_eq_of_rightSupport_eq {n k : ℕ}
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {a : AuxConcentration.PairRoleIndex n}
    {w z : AuxConcentration.PairWitness n k}
    (hw : w ∈ AuxConcentration.pairRoleWitnesses candidates R a)
    (hz : z ∈ AuxConcentration.pairRoleWitnesses candidates R a)
    (hsupport : w.rightBlock.auxSupport = z.rightBlock.auxSupport) :
    w.common = z.common := by
  have hblock := AuxConcentration.auxSupport_injective hsupport
  have hwdata := mem_auxPairRoleWitnesses_iff.mp hw
  have hzdata := mem_auxPairRoleWitnesses_iff.mp hz
  have hwfit := hwdata.1.2.2.2.2.2.2.2.2
  have hzfit := hzdata.1.2.2.2.2.2.2.2.2
  have hzfit' : AuxConcentration.RoleFits w.rightRole w.rightBlock
      a.y z.common := by
    simpa [AuxConcentration.PairRoleIndex.toPairTestIndex, hblock,
      hwdata.2.2.1.trans hzdata.2.2.1.symm] using hzfit
  exact auxRoleFits_colour_unique w.rightRole w.rightBlock a.y hwfit hzfit'

theorem auxPairWitnessToSlot_mem {n k : ℕ}
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {a : AuxConcentration.PairRoleIndex n}
    {w : AuxConcentration.PairWitness n k}
    (hw : w ∈ AuxConcentration.pairRoleWitnesses candidates R a)
    (hfresh : AuxPairWitnessKeyFresh a w) :
    auxPairWitnessToSlot a w ∈
      (jmcRoleSlotSystem candidates R a.x a.y
        (auxRootRoleEquiv a.leftRole)
        (auxRootRoleEquiv a.rightRole)).slots := by
  have hdata := mem_auxPairRoleWitnesses_iff.mp hw
  rcases hdata with
    ⟨⟨hxy, hleftC, hrightC, hblocks, hdisj, hleftMult, hrightMult,
        hleftRole, hrightRole⟩,
      hleftEq, hrightEq, hret⟩
  rw [hleftEq] at hleftRole
  rw [hrightEq] at hrightRole
  have hleftJMC : HasJMCPaintRole w.leftBlock a.x w.common
      (auxRootRoleEquiv a.leftRole) :=
    (auxRoleFits_iff_hasJMCPaintRole _ _ _ _).mp hleftRole
  have hrightJMC : HasJMCPaintRole w.rightBlock a.y w.common
      (auxRootRoleEquiv a.rightRole) :=
    (auxRoleFits_iff_hasJMCPaintRole _ _ _ _).mp hrightRole
  have hleftPaint := paints_jmcRoleNeighbor w.leftBlock a.x w.common
    (auxRootRoleEquiv a.leftRole) hleftJMC
  have hrightPaint := paints_jmcRoleNeighbor w.rightBlock a.y w.common
    (auxRootRoleEquiv a.rightRole) hrightJMC
  have hleftE := auxPairWitness_left_eligible hw
  have hrightE := auxPairWitness_right_eligible hw
  have hleftH : w.leftBlock.auxSupport ∈
      auxiliaryHypergraph candidates R := by
    rw [auxiliaryHypergraph]
    exact Finset.mem_image.mpr
      ⟨w.leftBlock, Finset.mem_filter.mpr ⟨hleftC, hleftE⟩, rfl⟩
  have hrightH : w.rightBlock.auxSupport ∈
      auxiliaryHypergraph candidates R := by
    rw [auxiliaryHypergraph]
    exact Finset.mem_image.mpr
      ⟨w.rightBlock, Finset.mem_filter.mpr ⟨hrightC, hrightE⟩, rfl⟩
  have hsupports : w.leftBlock.auxSupport ≠ w.rightBlock.auxSupport := by
    intro heq
    exact hblocks (AuxConcentration.auxSupport_injective heq)
  have hmatching : IsMatching (auxiliaryHypergraph candidates R)
      (auxPairWitnessToSlot a w).owner := by
    rw [JMCCrossSlot.owner, isMatching_insert_iff]
    refine ⟨hleftH, isMatching_singleton_iff.mpr hrightH, ?_⟩
    intro f hf hne
    rw [Finset.mem_singleton] at hf
    subst f
    exact hdisj
  apply CrossSlotSystem.mem_restrict_slots.mpr
  constructor
  · change auxPairWitnessToSlot a w ∈ jmcCrossSlots candidates R a.x a.y
    rw [mem_jmcCrossSlots]
    refine ⟨hsupports, hfresh.1, hfresh.2, hmatching,
      w.leftBlock, hleftC, hleftE, rfl,
      w.rightBlock, hrightC, hrightE, rfl, w.common, ?_⟩
    exact Or.inl ⟨hleftPaint, hrightPaint⟩
  · refine ⟨w.leftBlock, hleftC, hleftE, rfl,
      w.rightBlock, hrightC, hrightE, rfl, hblocks, w.common,
      hleftJMC, hrightJMC, ?_⟩
    exact Or.inl ⟨hleftPaint, hrightPaint⟩

theorem auxPairWitnessToSlot_injectiveOn {n k : ℕ}
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    (a : AuxConcentration.PairRoleIndex n) :
    ∀ ⦃w⦄, w ∈ freshPairRoleWitnesses candidates R a →
      ∀ ⦃z⦄, z ∈ freshPairRoleWitnesses candidates R a →
        auxPairWitnessToSlot a w = auxPairWitnessToSlot a z → w = z := by
  intro w hw z hz heq
  have hw := (Finset.mem_filter.mp hw).1
  have hz := (Finset.mem_filter.mp hz).1
  have hwdata := mem_auxPairRoleWitnesses_iff.mp hw
  have hzdata := mem_auxPairRoleWitnesses_iff.mp hz
  have hleftSupport := congrArg JMCCrossSlot.xEdge heq
  have hrightSupport := congrArg JMCCrossSlot.yEdge heq
  have hleftBlock : w.leftBlock = z.leftBlock :=
    AuxConcentration.auxSupport_injective hleftSupport
  have hrightBlock : w.rightBlock = z.rightBlock :=
    AuxConcentration.auxSupport_injective hrightSupport
  have hleftRole : w.leftRole = z.leftRole :=
    hwdata.2.1.trans hzdata.2.1.symm
  have hrightRole : w.rightRole = z.rightRole :=
    hwdata.2.2.1.trans hzdata.2.2.1.symm
  have hwfit := hwdata.1.2.2.2.2.2.2.2.1
  have hzfit := hzdata.1.2.2.2.2.2.2.2.1
  have hzfit' : AuxConcentration.RoleFits w.leftRole w.leftBlock
      a.x z.common := by
    simpa [AuxConcentration.PairRoleIndex.toPairTestIndex,
      hleftBlock, hleftRole] using hzfit
  have hcommon : w.common = z.common :=
    auxRoleFits_colour_unique w.leftRole w.leftBlock a.x hwfit hzfit'
  cases w
  cases z
  simp_all

/-- Concentration of common-colour role witnesses gives a literal lower
bound for the corresponding tracked two-uniform host total.  The map is an
injection, not merely an asymptotic comparison. -/
theorem pairRoleWitnesses_card_le_jmcRole_pairTotal {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (a : AuxConcentration.PairRoleIndex n) :
    ((freshPairRoleWitnesses candidates R a).card : ℝ) ≤
      testTotal
        (jmcRoleSlotSystem candidates R a.x a.y
          (auxRootRoleEquiv a.leftRole)
          (auxRootRoleEquiv a.rightRole)).pairWeight
        (auxiliaryHypergraph candidates R) 2 := by
  rw [jmcRole_pairTotal]
  exact_mod_cast Finset.card_le_card_of_injOn
    (auxPairWitnessToSlot a) (by
      intro w hw
      have hraw := (Finset.mem_filter.mp hw).1
      have hmem := auxPairWitnessToSlot_mem hraw (Finset.mem_filter.mp hw).2
      refine Finset.mem_filter.mpr ⟨hmem, ?_⟩
      exact Finset.mem_powersetCard.mpr
        ⟨((jmcRoleSlotSystem candidates R a.x a.y
            (auxRootRoleEquiv a.leftRole)
            (auxRootRoleEquiv a.rightRole)).owner_matching _ hmem).1,
          (jmcRoleSlotSystem candidates R a.x a.y
            (auxRootRoleEquiv a.leftRole)
            (auxRootRoleEquiv a.rightRole)).owner_card _ hmem⟩)
    (fun w hw z hz heq ↦ auxPairWitnessToSlot_injectiveOn a hw hz heq)

/-- A role-witness concentration window transfers to a sharp lower bound
for the fresh tracked pair test, losing only the explicit overlapping
remainder. -/
theorem jmcRole_pairTotal_lower_of_pairRoleWitnessesNear {n k : ℕ}
    (R : RetainedLabels n k)
    (target error : AuxConcentration.PairRoleIndex n → ℝ)
    (hnear : AuxConcentration.PairRoleWitnessesNear
      (AuxConcentration.allTriangleBlocks n k) R target error)
    (a : AuxConcentration.PairRoleIndex n) (hk : k ≤ n) :
    target a - error a - 9 * (n : ℝ) ^ 6 <
      testTotal
        (jmcRoleSlotSystem (AuxConcentration.allTriangleBlocks n k) R
          a.x a.y (auxRootRoleEquiv a.leftRole)
          (auxRootRoleEquiv a.rightRole)).pairWeight
        (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R) 2 := by
  have hwindow := hnear a a.x_ne_y
  have hlower : target a - error a <
      ((AuxConcentration.pairRoleWitnesses
        (AuxConcentration.allTriangleBlocks n k) R a).card : ℝ) := by
    have habs := (abs_lt.mp hwindow).1
    linarith
  have hcardNat := pairRoleWitnesses_card_le_fresh_add_n6 R a hk
  have hcard :
      ((AuxConcentration.pairRoleWitnesses
        (AuxConcentration.allTriangleBlocks n k) R a).card : ℝ) ≤
      ((freshPairRoleWitnesses
        (AuxConcentration.allTriangleBlocks n k) R a).card : ℝ) +
        9 * (n : ℝ) ^ 6 := by
    exact_mod_cast hcardNat
  have hpair := pairRoleWitnesses_card_le_jmcRole_pairTotal
    (AuxConcentration.allTriangleBlocks n k) R a
  linarith

theorem universalRetainedHostEstimates_jmcRole_pairTotal_lower {n k : ℕ}
    {q : ℝ} {R : RetainedLabels n k}
    (hhost : AuxConcentration.UniversalRetainedHostEstimates q R)
    (a : AuxConcentration.PairRoleIndex n) (hk : k ≤ n) :
    AuxConcentration.pairRoleTarget k q a -
        (AuxConcentration.universalPairRoleDeviation n a +
          AuxConcentration.universalPairRoleMeanError n a) -
        9 * (n : ℝ) ^ 6 <
      testTotal
        (jmcRoleSlotSystem (AuxConcentration.allTriangleBlocks n k) R
          a.x a.y (auxRootRoleEquiv a.leftRole)
          (auxRootRoleEquiv a.rightRole)).pairWeight
        (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R) 2 := by
  exact jmcRole_pairTotal_lower_of_pairRoleWitnessesNear R
    (AuxConcentration.pairRoleTarget k q)
    (fun a ↦ AuxConcentration.universalPairRoleDeviation n a +
      AuxConcentration.universalPairRoleMeanError n a)
    hhost.2.2.1 a hk

/-- A tracked role slot determines its underlying retained common-colour
witness, together with the two oriented painted endpoints. -/
def SlotFitsAuxPairWitness {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (a : AuxConcentration.PairRoleIndex n) (q : JMCCrossSlot n k)
    (w : AuxConcentration.PairWitness n k) : Prop :=
  w ∈ AuxConcentration.pairRoleWitnesses candidates R a ∧
    w.leftBlock.auxSupport = q.xEdge ∧
    w.rightBlock.auxSupport = q.yEdge ∧
    ((w.leftBlock.Paints a.x q.cross.1 w.common ∧
        w.rightBlock.Paints a.y q.cross.2 w.common) ∨
      (w.leftBlock.Paints a.x q.cross.2 w.common ∧
        w.rightBlock.Paints a.y q.cross.1 w.common))

theorem exists_slotFitsAuxPairWitness_of_mem {n k : ℕ}
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    (a : AuxConcentration.PairRoleIndex n) {q : JMCCrossSlot n k}
    (hq : q ∈ (jmcRoleSlotSystem candidates R a.x a.y
      (auxRootRoleEquiv a.leftRole)
      (auxRootRoleEquiv a.rightRole)).slots) :
    ∃ w, SlotFitsAuxPairWitness candidates R a q w := by
  have hparts := CrossSlotSystem.mem_restrict_slots.mp hq
  have hbase := mem_jmcCrossSlots.mp hparts.1
  rcases hbase with
    ⟨hsupportNe, hcrossNe, hkeyFresh, hownerMatch, bx0, hbx0c,
      hbx0E, hbx0s, bY0, hbY0c, hbY0E, hbY0s, c0, hpaint0⟩
  rcases hparts.2 with
    ⟨bx, hbxc, hbxE, hbxs, bY, hbYc, hbYE, hbYs, hbne, c,
      hleftRole, hrightRole, hpaint⟩
  have hsupportNe : bx.auxSupport ≠ bY.auxSupport := by
    intro heq
    exact hbne (AuxConcentration.auxSupport_injective heq)
  have hbxOwner : bx.auxSupport ∈ q.owner := by
    rw [hbxs]
    simp [JMCCrossSlot.owner]
  have hbYOwner : bY.auxSupport ∈ q.owner := by
    rw [hbYs]
    simp [JMCCrossSlot.owner]
  have hdisj : Disjoint bx.auxSupport bY.auxSupport :=
    hownerMatch.2 hbxOwner hbYOwner hsupportNe
  have hleftFit : AuxConcentration.RoleFits a.leftRole bx a.x c :=
    (auxRoleFits_iff_hasJMCPaintRole _ _ _ _).mpr hleftRole
  have hrightFit : AuxConcentration.RoleFits a.rightRole bY a.y c :=
    (auxRoleFits_iff_hasJMCPaintRole _ _ _ _).mpr hrightRole
  have hret : AuxConcentration.PairWitness.RetentionValid R
      ⟨c, bx, bY, a.leftRole, a.rightRole⟩ := by
    constructor
    · intro z hz
      simp only [AuxConcentration.PairWitness.positiveLabels,
        Finset.mem_union] at hz
      rcases hz with hz | hz
      · exact hbxE.1 hz
      · exact hbYE.1 hz
    · rw [Finset.disjoint_left]
      intro z hz hzr
      simp only [AuxConcentration.PairWitness.negativeLabels,
        Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hbxE.2 hzr
      · exact hbYE.2 hzr
  let w : AuxConcentration.PairWitness n k :=
    ⟨c, bx, bY, a.leftRole, a.rightRole⟩
  refine ⟨w, ?_⟩
  refine ⟨mem_auxPairRoleWitnesses_iff.mpr ⟨?_, rfl, rfl, hret⟩,
    hbxs, hbYs, hpaint⟩
  exact ⟨a.x_ne_y, hbxc, hbYc, hbne, hdisj,
    a.leftRole.multiplicityIndex_val_add_one.symm,
    a.rightRole.multiplicityIndex_val_add_one.symm, hleftFit, hrightFit⟩

theorem slotFitsAuxPairWitness_unique {n k : ℕ}
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    (a : AuxConcentration.PairRoleIndex n) (q : JMCCrossSlot n k)
    {w z : AuxConcentration.PairWitness n k}
    (hw : SlotFitsAuxPairWitness candidates R a q w)
    (hz : SlotFitsAuxPairWitness candidates R a q z) : w = z := by
  have hwdata := mem_auxPairRoleWitnesses_iff.mp hw.1
  have hzdata := mem_auxPairRoleWitnesses_iff.mp hz.1
  have hleftBlock : w.leftBlock = z.leftBlock :=
    AuxConcentration.auxSupport_injective (hw.2.1.trans hz.2.1.symm)
  have hrightBlock : w.rightBlock = z.rightBlock :=
    AuxConcentration.auxSupport_injective (hw.2.2.1.trans hz.2.2.1.symm)
  have hleftRole : w.leftRole = z.leftRole :=
    hwdata.2.1.trans hzdata.2.1.symm
  have hrightRole : w.rightRole = z.rightRole :=
    hwdata.2.2.1.trans hzdata.2.2.1.symm
  have hwfit := hwdata.1.2.2.2.2.2.2.2.1
  have hzfit := hzdata.1.2.2.2.2.2.2.2.1
  have hzfit' : AuxConcentration.RoleFits w.leftRole w.leftBlock
      a.x z.common := by
    simpa [AuxConcentration.PairRoleIndex.toPairTestIndex,
      hleftBlock, hleftRole] using hzfit
  have hcommon : w.common = z.common :=
    auxRoleFits_colour_unique w.leftRole w.leftBlock a.x hwfit hzfit'
  cases w
  cases z
  simp_all

/-- The finite subtype of fresh tracked slots for one role pair. -/
abbrev JMCRoleSlot {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (a : AuxConcentration.PairRoleIndex n) :=
  {q // q ∈ (jmcRoleSlotSystem candidates R a.x a.y
    (auxRootRoleEquiv a.leftRole)
    (auxRootRoleEquiv a.rightRole)).slots}

noncomputable def jmcRoleSlotWitness {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (a : AuxConcentration.PairRoleIndex n)
    (q : JMCRoleSlot candidates R a) : AuxConcentration.PairWitness n k :=
  Classical.choose (exists_slotFitsAuxPairWitness_of_mem a q.2)

theorem jmcRoleSlotWitness_spec {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (a : AuxConcentration.PairRoleIndex n)
    (q : JMCRoleSlot candidates R a) :
    SlotFitsAuxPairWitness candidates R a q.1
      (jmcRoleSlotWitness candidates R a q) :=
  Classical.choose_spec (exists_slotFitsAuxPairWitness_of_mem a q.2)

theorem jmcRoleSlotWitness_fiber_card_le_eight {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (a : AuxConcentration.PairRoleIndex n)
    (w : AuxConcentration.PairWitness n k) :
    ((Finset.univ : Finset (JMCRoleSlot candidates R a)).filter fun q ↦
      jmcRoleSlotWitness candidates R a q = w).card ≤ 8 := by
  let A := w.leftPaintedNeighbors a
  let B := w.rightPaintedNeighbors a
  let P : Finset (Fin n × Fin n) := (A ×ˢ B) ∪ (B ×ˢ A)
  let F := (Finset.univ : Finset (JMCRoleSlot candidates R a)).filter fun q ↦
    jmcRoleSlotWitness candidates R a q = w
  change F.card ≤ 8
  by_cases hFempty : F = ∅
  · simp [hFempty]
  obtain ⟨q0, hq0⟩ := Finset.nonempty_iff_ne_empty.mpr hFempty
  have hq0eq := (Finset.mem_filter.mp hq0).2
  have hq0spec := jmcRoleSlotWitness_spec candidates R a q0
  have hw : w ∈ AuxConcentration.pairRoleWitnesses candidates R a := by
    rw [hq0eq] at hq0spec
    exact hq0spec.1
  have hmap : ∀ q ∈ F, q.1.cross ∈ P := by
    intro q hq
    have heq := (Finset.mem_filter.mp hq).2
    have hs := jmcRoleSlotWitness_spec candidates R a q
    rw [heq] at hs
    rcases hs.2.2.2 with hp | hp
    · apply Finset.mem_union_left
      exact Finset.mem_product.mpr
        ⟨(AuxConcentration.mem_paintedNeighbors_iff
            w.leftBlock a.x q.1.cross.1 w.common).mpr
            ⟨(w.leftBlock.paints_ne hp.1).symm, hp.1⟩,
          (AuxConcentration.mem_paintedNeighbors_iff
            w.rightBlock a.y q.1.cross.2 w.common).mpr
            ⟨(w.rightBlock.paints_ne hp.2).symm, hp.2⟩⟩
    · apply Finset.mem_union_right
      exact Finset.mem_product.mpr
        ⟨(AuxConcentration.mem_paintedNeighbors_iff
            w.rightBlock a.y q.1.cross.1 w.common).mpr
            ⟨(w.rightBlock.paints_ne hp.2).symm, hp.2⟩,
          (AuxConcentration.mem_paintedNeighbors_iff
            w.leftBlock a.x q.1.cross.2 w.common).mpr
            ⟨(w.leftBlock.paints_ne hp.1).symm, hp.1⟩⟩
  have hinj : ∀ q ∈ F, ∀ r ∈ F, q.1.cross = r.1.cross → q = r := by
    intro q hq r hr hcross
    have hqw := (Finset.mem_filter.mp hq).2
    have hrw := (Finset.mem_filter.mp hr).2
    have hqs := jmcRoleSlotWitness_spec candidates R a q
    have hrs := jmcRoleSlotWitness_spec candidates R a r
    rw [hqw] at hqs
    rw [hrw] at hrs
    apply Subtype.ext
    rcases q with ⟨⟨qx, qy, qc⟩, hqmem⟩
    rcases r with ⟨⟨rx, ry, rc⟩, hrmem⟩
    simp only at hcross hqs hrs ⊢
    have hx : qx = rx := hqs.2.1.symm.trans hrs.2.1
    have hy : qy = ry := hqs.2.2.1.symm.trans hrs.2.2.1
    subst rx
    subst ry
    exact congrArg (JMCCrossSlot.mk qx qy) hcross
  have hcardFP : F.card ≤ P.card :=
    Finset.card_le_card_of_injOn (fun q ↦ q.1.cross) hmap hinj
  have hgeom : w ∈ AuxConcentration.geometricRoleWitnesses candidates a :=
    (Finset.mem_filter.mp hw).1
  have hA := w.leftPaintedNeighbors_card_of_mem_geometricRoleWitnesses a hgeom
  have hB := w.rightPaintedNeighbors_card_of_mem_geometricRoleWitnesses a hgeom
  calc
    F.card ≤ P.card := hcardFP
    _ ≤ (A ×ˢ B).card + (B ×ˢ A).card := Finset.card_union_le _ _
    _ = 2 * (a.leftRole.multiplicity * a.rightRole.multiplicity) := by
      simp [A, B, hA, hB]
      ring
    _ ≤ 8 := by
      cases a.leftRole <;> cases a.rightRole <;>
        norm_num [AuxConcentration.RootRole.multiplicity]

/-- Once the unordered two-edge support is fixed, a role witness has only
the two possible left/right orientations. -/
theorem pairRoleWitness_support_fiber_card_le_two {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (a : AuxConcentration.PairRoleIndex n)
    (S : Hypergraph (AuxVertex n k)) :
    ((AuxConcentration.pairRoleWitnesses candidates R a).filter fun w ↦
      w.support = S).card ≤ 2 := by
  let F := (AuxConcentration.pairRoleWitnesses candidates R a).filter fun w ↦
    w.support = S
  by_cases hF : F = ∅
  · simp [F, hF]
  obtain ⟨w₀, hw₀⟩ := Finset.nonempty_iff_ne_empty.mpr hF
  have hw₀mem := (Finset.mem_filter.mp hw₀).1
  have hw₀support := (Finset.mem_filter.mp hw₀).2
  have hw₀data := mem_auxPairRoleWitnesses_iff.mp hw₀mem
  have hsupportNe : w₀.leftBlock.auxSupport ≠ w₀.rightBlock.auxSupport := by
    intro h
    exact hw₀data.1.2.2.2.1 (AuxConcentration.auxSupport_injective h)
  have hScard : S.card = 2 := by
    rw [← hw₀support]
    simp [AuxConcentration.PairWitness.support, hsupportNe]
  have hmap : ∀ w ∈ F, w.leftBlock.auxSupport ∈ S := by
    intro w hw
    have hs := (Finset.mem_filter.mp hw).2
    rw [← hs]
    simp [AuxConcentration.PairWitness.support]
  have hinj : ∀ w ∈ F, ∀ z ∈ F,
      w.leftBlock.auxSupport = z.leftBlock.auxSupport → w = z := by
    intro w hw z hz hleftSupport
    have hwmem := (Finset.mem_filter.mp hw).1
    have hzmem := (Finset.mem_filter.mp hz).1
    have hwsupport := (Finset.mem_filter.mp hw).2
    have hzsupport := (Finset.mem_filter.mp hz).2
    have hwdata := mem_auxPairRoleWitnesses_iff.mp hwmem
    have hzdata := mem_auxPairRoleWitnesses_iff.mp hzmem
    have hleftBlock : w.leftBlock = z.leftBlock :=
      AuxConcentration.auxSupport_injective hleftSupport
    have hrightMem : w.rightBlock.auxSupport ∈ z.support := by
      rw [hzsupport, ← hwsupport]
      simp [AuxConcentration.PairWitness.support]
    simp only [AuxConcentration.PairWitness.support, Finset.mem_insert,
      Finset.mem_singleton] at hrightMem
    have hrightSupport : w.rightBlock.auxSupport = z.rightBlock.auxSupport := by
      rcases hrightMem with hbad | hright
      · exfalso
        apply hwdata.1.2.2.2.1
        apply AuxConcentration.auxSupport_injective
        exact (hbad.trans hleftSupport.symm).symm
      · exact hright
    have hrightBlock : w.rightBlock = z.rightBlock :=
      AuxConcentration.auxSupport_injective hrightSupport
    have hleftRole : w.leftRole = z.leftRole :=
      hwdata.2.1.trans hzdata.2.1.symm
    have hrightRole : w.rightRole = z.rightRole :=
      hwdata.2.2.1.trans hzdata.2.2.1.symm
    have hwfit := hwdata.1.2.2.2.2.2.2.2.1
    have hzfit := hzdata.1.2.2.2.2.2.2.2.1
    have hzfit' : AuxConcentration.RoleFits w.leftRole w.leftBlock
        a.x z.common := by
      simpa [AuxConcentration.PairRoleIndex.toPairTestIndex,
        hleftBlock, hleftRole] using hzfit
    have hcommon : w.common = z.common :=
      auxRoleFits_colour_unique w.leftRole w.leftBlock a.x hwfit hzfit'
    cases w
    cases z
    simp_all
  calc
    F.card ≤ S.card :=
      Finset.card_le_card_of_injOn (fun w ↦ w.leftBlock.auxSupport) hmap hinj
    _ = 2 := hScard

/-- At a fixed host edge there are at most two orientations of a role
witness.  In either orientation the opposite block is charged injectively
to one host-degree fibre; the common colour is forced by the fixed block
and its prescribed role. -/
theorem pairRoleWitness_support_incidence_card_le_two_mul_degree {n k D : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (hmax : MaxDegreeLE (auxiliaryHypergraph candidates R) D)
    (a : AuxConcentration.PairRoleIndex n)
    (e : Finset (AuxVertex n k)) :
    ((AuxConcentration.pairRoleWitnesses candidates R a).filter fun w ↦
      e ∈ w.support).card ≤ 2 * D := by
  let W := AuxConcentration.pairRoleWitnesses candidates R a
  let F := W.filter fun w ↦ e ∈ w.support
  let FL := W.filter fun w ↦ w.leftBlock.auxSupport = e
  let FR := W.filter fun w ↦ w.rightBlock.auxSupport = e
  have hsub : F ⊆ FL ∪ FR := by
    intro w hw
    have hwW := (Finset.mem_filter.mp hw).1
    have hew := (Finset.mem_filter.mp hw).2
    simp only [AuxConcentration.PairWitness.support, Finset.mem_insert,
      Finset.mem_singleton] at hew
    rcases hew with hew | hew
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hwW, hew.symm⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hwW, hew.symm⟩)
  have hFL : FL.card ≤ D := by
    by_cases hFLempty : FL = ∅
    · simp [hFLempty]
    obtain ⟨w₀, hw₀⟩ := Finset.nonempty_iff_ne_empty.mpr hFLempty
    have hw₀W := (Finset.mem_filter.mp hw₀).1
    have hw₀left := (Finset.mem_filter.mp hw₀).2
    let G := (auxiliaryHypergraph candidates R).filter fun f ↦
      Sum.inr (a.y, w₀.common) ∈ f
    have hmap : ∀ w ∈ FL, w.rightBlock.auxSupport ∈ G := by
      intro w hw
      have hwW := (Finset.mem_filter.mp hw).1
      have hwleft := (Finset.mem_filter.mp hw).2
      have hc : w.common = w₀.common :=
        pairRoleWitness_common_eq_of_leftSupport_eq hwW hw₀W
          (hwleft.trans hw₀left.symm)
      exact Finset.mem_filter.mpr
        ⟨auxPairWitness_right_mem_host hwW, by
          simpa [hc] using auxPairWitness_right_rootLabel_mem hwW⟩
    have hinj : ∀ w ∈ FL, ∀ z ∈ FL,
        w.rightBlock.auxSupport = z.rightBlock.auxSupport → w = z := by
      intro w hw z hz hrightSupport
      have hwW := (Finset.mem_filter.mp hw).1
      have hzW := (Finset.mem_filter.mp hz).1
      have hwleft := (Finset.mem_filter.mp hw).2
      have hzleft := (Finset.mem_filter.mp hz).2
      have hleftBlock := AuxConcentration.auxSupport_injective
        (hwleft.trans hzleft.symm)
      have hrightBlock := AuxConcentration.auxSupport_injective hrightSupport
      have hcommon := pairRoleWitness_common_eq_of_leftSupport_eq hwW hzW
        (hwleft.trans hzleft.symm)
      have hwdata := mem_auxPairRoleWitnesses_iff.mp hwW
      have hzdata := mem_auxPairRoleWitnesses_iff.mp hzW
      have hleftRole := hwdata.2.1.trans hzdata.2.1.symm
      have hrightRole := hwdata.2.2.1.trans hzdata.2.2.1.symm
      cases w
      cases z
      simp_all
    calc
      FL.card ≤ G.card :=
        Finset.card_le_card_of_injOn (fun w ↦ w.rightBlock.auxSupport) hmap hinj
      _ = degree (auxiliaryHypergraph candidates R)
          (Sum.inr (a.y, w₀.common)) := rfl
      _ ≤ D := hmax _
  have hFR : FR.card ≤ D := by
    by_cases hFRempty : FR = ∅
    · simp [hFRempty]
    obtain ⟨w₀, hw₀⟩ := Finset.nonempty_iff_ne_empty.mpr hFRempty
    have hw₀W := (Finset.mem_filter.mp hw₀).1
    have hw₀right := (Finset.mem_filter.mp hw₀).2
    let G := (auxiliaryHypergraph candidates R).filter fun f ↦
      Sum.inr (a.x, w₀.common) ∈ f
    have hmap : ∀ w ∈ FR, w.leftBlock.auxSupport ∈ G := by
      intro w hw
      have hwW := (Finset.mem_filter.mp hw).1
      have hwright := (Finset.mem_filter.mp hw).2
      have hc : w.common = w₀.common :=
        pairRoleWitness_common_eq_of_rightSupport_eq hwW hw₀W
          (hwright.trans hw₀right.symm)
      exact Finset.mem_filter.mpr
        ⟨auxPairWitness_left_mem_host hwW, by
          simpa [hc] using auxPairWitness_left_rootLabel_mem hwW⟩
    have hinj : ∀ w ∈ FR, ∀ z ∈ FR,
        w.leftBlock.auxSupport = z.leftBlock.auxSupport → w = z := by
      intro w hw z hz hleftSupport
      have hwW := (Finset.mem_filter.mp hw).1
      have hzW := (Finset.mem_filter.mp hz).1
      have hwright := (Finset.mem_filter.mp hw).2
      have hzright := (Finset.mem_filter.mp hz).2
      have hleftBlock := AuxConcentration.auxSupport_injective hleftSupport
      have hrightBlock := AuxConcentration.auxSupport_injective
        (hwright.trans hzright.symm)
      have hcommon := pairRoleWitness_common_eq_of_rightSupport_eq hwW hzW
        (hwright.trans hzright.symm)
      have hwdata := mem_auxPairRoleWitnesses_iff.mp hwW
      have hzdata := mem_auxPairRoleWitnesses_iff.mp hzW
      have hleftRole := hwdata.2.1.trans hzdata.2.1.symm
      have hrightRole := hwdata.2.2.1.trans hzdata.2.2.1.symm
      cases w
      cases z
      simp_all
    calc
      FR.card ≤ G.card :=
        Finset.card_le_card_of_injOn (fun w ↦ w.leftBlock.auxSupport) hmap hinj
      _ = degree (auxiliaryHypergraph candidates R)
          (Sum.inr (a.x, w₀.common)) := rfl
      _ ≤ D := hmax _
  calc
    F.card ≤ (FL ∪ FR).card := Finset.card_le_card hsub
    _ ≤ FL.card + FR.card := Finset.card_union_le _ _
    _ ≤ D + D := Nat.add_le_add hFL hFR
    _ = 2 * D := by omega

/-- Every two-edge owner carries at most sixteen oriented slots: two block
orientations times the eight endpoint orientations of one role witness. -/
theorem jmcRole_pairFiber_card_le_sixteen {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (a : AuxConcentration.PairRoleIndex n)
    (S : Hypergraph (AuxVertex n k)) :
    ((jmcRoleSlotSystem candidates R a.x a.y
        (auxRootRoleEquiv a.leftRole)
        (auxRootRoleEquiv a.rightRole)).slots.filter fun q ↦
      (jmcRoleSlotSystem candidates R a.x a.y
        (auxRootRoleEquiv a.leftRole)
        (auxRootRoleEquiv a.rightRole)).owner q = S).card ≤ 16 := by
  let T := jmcRoleSlotSystem candidates R a.x a.y
    (auxRootRoleEquiv a.leftRole) (auxRootRoleEquiv a.rightRole)
  let F : Finset (JMCRoleSlot candidates R a) :=
    T.slots.attach.filter fun q ↦ T.owner q.1 = S
  let W := (AuxConcentration.pairRoleWitnesses candidates R a).filter fun w ↦
    w.support = S
  let f := jmcRoleSlotWitness candidates R a
  have hcardTF : (T.slots.filter fun q ↦ T.owner q = S).card = F.card := by
    apply Finset.card_bij
      (fun q hq ↦ ⟨q, (Finset.mem_filter.mp hq).1⟩)
    · intro q hq
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_attach _ _, (Finset.mem_filter.mp hq).2⟩
    · intro q hq r hr heq
      exact congrArg Subtype.val heq
    · intro q hq
      refine ⟨q.1, Finset.mem_filter.mpr
        ⟨q.2, (Finset.mem_filter.mp hq).2⟩, ?_⟩
      exact Subtype.ext rfl
  have hrange : ∀ q ∈ F, f q ∈ W := by
    intro q hq
    have howner := (Finset.mem_filter.mp hq).2
    have hs := jmcRoleSlotWitness_spec candidates R a q
    apply Finset.mem_filter.mpr
    refine ⟨hs.1, ?_⟩
    rw [AuxConcentration.PairWitness.support, hs.2.1, hs.2.2.1]
    exact howner
  have hcount := Finset.sum_card_fiberwise_eq_card_filter F W f
  have hfilter : F.filter (fun q ↦ f q ∈ W) = F := by
    apply Finset.filter_eq_self.mpr
    exact hrange
  rw [hfilter] at hcount
  have hfiber : ∀ w ∈ W, (F.filter fun q ↦ f q = w).card ≤ 8 := by
    intro w hw
    apply (Finset.card_le_card ?_).trans
      (jmcRoleSlotWitness_fiber_card_le_eight candidates R a w)
    intro q hq
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ q, (Finset.mem_filter.mp hq).2⟩
  have hW : W.card ≤ 2 := by
    exact pairRoleWitness_support_fiber_card_le_two candidates R a S
  rw [hcardTF]
  calc
    F.card = ∑ w ∈ W, (F.filter fun q ↦ f q = w).card := hcount.symm
    _ ≤ ∑ _w ∈ W, 8 := Finset.sum_le_sum hfiber
    _ = W.card * 8 := by simp
    _ ≤ 2 * 8 := Nat.mul_le_mul_right 8 hW
    _ = 16 := by norm_num

/-- A fixed host edge belongs to at most `16 D` role-slot owners when every
auxiliary vertex has host degree at most `D`. -/
theorem jmcRole_pairOwnerIncidence_card_le_sixteen_mul_degree {n k D : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (hmax : MaxDegreeLE (auxiliaryHypergraph candidates R) D)
    (a : AuxConcentration.PairRoleIndex n)
    (e : Finset (AuxVertex n k)) :
    ((jmcRoleSlotSystem candidates R a.x a.y
        (auxRootRoleEquiv a.leftRole)
        (auxRootRoleEquiv a.rightRole)).slots.filter fun q ↦
      e ∈ (jmcRoleSlotSystem candidates R a.x a.y
        (auxRootRoleEquiv a.leftRole)
        (auxRootRoleEquiv a.rightRole)).owner q).card ≤ 16 * D := by
  let T := jmcRoleSlotSystem candidates R a.x a.y
    (auxRootRoleEquiv a.leftRole) (auxRootRoleEquiv a.rightRole)
  let F : Finset (JMCRoleSlot candidates R a) :=
    T.slots.attach.filter fun q ↦ e ∈ T.owner q.1
  let W := (AuxConcentration.pairRoleWitnesses candidates R a).filter fun w ↦
    e ∈ w.support
  let f := jmcRoleSlotWitness candidates R a
  have hcardTF : (T.slots.filter fun q ↦ e ∈ T.owner q).card = F.card := by
    apply Finset.card_bij
      (fun q hq ↦ ⟨q, (Finset.mem_filter.mp hq).1⟩)
    · intro q hq
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_attach _ _, (Finset.mem_filter.mp hq).2⟩
    · intro q hq r hr heq
      exact congrArg Subtype.val heq
    · intro q hq
      refine ⟨q.1, Finset.mem_filter.mpr
        ⟨q.2, (Finset.mem_filter.mp hq).2⟩, Subtype.ext rfl⟩
  have hrange : ∀ q ∈ F, f q ∈ W := by
    intro q hq
    have heowner := (Finset.mem_filter.mp hq).2
    have hs := jmcRoleSlotWitness_spec candidates R a q
    apply Finset.mem_filter.mpr
    refine ⟨hs.1, ?_⟩
    rw [AuxConcentration.PairWitness.support, hs.2.1, hs.2.2.1]
    exact heowner
  have hcount := Finset.sum_card_fiberwise_eq_card_filter F W f
  have hfilter : F.filter (fun q ↦ f q ∈ W) = F := by
    apply Finset.filter_eq_self.mpr
    exact hrange
  rw [hfilter] at hcount
  have hfiber : ∀ w ∈ W, (F.filter fun q ↦ f q = w).card ≤ 8 := by
    intro w hw
    apply (Finset.card_le_card ?_).trans
      (jmcRoleSlotWitness_fiber_card_le_eight candidates R a w)
    intro q hq
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ q, (Finset.mem_filter.mp hq).2⟩
  have hW : W.card ≤ 2 * D :=
    pairRoleWitness_support_incidence_card_le_two_mul_degree
      candidates R hmax a e
  rw [hcardTF]
  calc
    F.card = ∑ w ∈ W, (F.filter fun q ↦ f q = w).card := hcount.symm
    _ ≤ ∑ _w ∈ W, 8 := Finset.sum_le_sum hfiber
    _ = W.card * 8 := by simp
    _ ≤ (2 * D) * 8 := Nat.mul_le_mul_right 8 hW
    _ = 16 * D := by ring

theorem jmcRole_pairExtension_le_sixteen_mul_degree {n k D : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (hmax : MaxDegreeLE (auxiliaryHypergraph candidates R) D)
    (a : AuxConcentration.PairRoleIndex n)
    (root : Hypergraph (AuxVertex n k)) (hroot : root.card = 1) :
    testExtension
        (jmcRoleSlotSystem candidates R a.x a.y
          (auxRootRoleEquiv a.leftRole)
          (auxRootRoleEquiv a.rightRole)).pairWeight
        (auxiliaryHypergraph candidates R) 2 root ≤ (16 * D : ℕ) := by
  obtain ⟨e, rfl⟩ := Finset.card_eq_one.mp hroot
  let T := jmcRoleSlotSystem candidates R a.x a.y
    (auxRootRoleEquiv a.leftRole) (auxRootRoleEquiv a.rightRole)
  rw [CrossSlotSystem.testExtension_pairWeight]
  have hcard :
      (T.slots.filter fun q ↦ T.owner q ∈
        ((auxiliaryHypergraph candidates R).powersetCard 2).filter
          ({e} ⊆ ·)).card ≤
        (T.slots.filter fun q ↦ e ∈ T.owner q).card := by
    apply Finset.card_le_card
    intro q hq
    have hslot := (Finset.mem_filter.mp hq).1
    have hfamily := (Finset.mem_filter.mp hq).2
    have hsub := (Finset.mem_filter.mp hfamily).2
    exact Finset.mem_filter.mpr ⟨hslot, hsub (by simp)⟩
  exact_mod_cast hcard.trans
    (jmcRole_pairOwnerIncidence_card_le_sixteen_mul_degree
      candidates R hmax a e)

def PairWitnessPaintsCross {n k : ℕ}
    (a : AuxConcentration.PairRoleIndex n) (p : Fin n × Fin n)
    (w : AuxConcentration.PairWitness n k) : Prop :=
  (w.leftBlock.Paints a.x p.1 w.common ∧
      w.rightBlock.Paints a.y p.2 w.common) ∨
    (w.leftBlock.Paints a.x p.2 w.common ∧
      w.rightBlock.Paints a.y p.1 w.common)

/-- For a fixed common colour and ordered cross pair, the two block supports
lie in one of two products of local paint fibres. -/
theorem pairRoleWitness_paintsCross_common_fiber_card_le {n k L : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (hpaint : ∀ p : OrientedPaint n k,
      (paintFiber (auxiliaryHypergraph candidates R) p).card ≤ L)
    (a : AuxConcentration.PairRoleIndex n) (p : Fin n × Fin n)
    (c : Fin k) :
    ((AuxConcentration.pairRoleWitnesses candidates R a).filter fun w ↦
      w.common = c ∧ PairWitnessPaintsCross a p w).card ≤ 2 * L ^ 2 := by
  let H := auxiliaryHypergraph candidates R
  let A := paintFiber H ⟨a.x, p.1, c⟩ ×ˢ paintFiber H ⟨a.y, p.2, c⟩
  let B := paintFiber H ⟨a.x, p.2, c⟩ ×ˢ paintFiber H ⟨a.y, p.1, c⟩
  let F := (AuxConcentration.pairRoleWitnesses candidates R a).filter fun w ↦
    w.common = c ∧ PairWitnessPaintsCross a p w
  have hmap : ∀ w ∈ F, (w.leftBlock.auxSupport, w.rightBlock.auxSupport) ∈
      A ∪ B := by
    intro w hw
    have hwW := (Finset.mem_filter.mp hw).1
    have hwcond := (Finset.mem_filter.mp hw).2
    rcases hwcond.2 with hp | hp
    · apply Finset.mem_union_left
      apply Finset.mem_product.mpr
      exact ⟨auxSupport_mem_paintFiber (auxPairWitness_left_mem_host hwW)
          (by simpa [hwcond.1] using hp.1),
        auxSupport_mem_paintFiber (auxPairWitness_right_mem_host hwW)
          (by simpa [hwcond.1] using hp.2)⟩
    · apply Finset.mem_union_right
      apply Finset.mem_product.mpr
      exact ⟨auxSupport_mem_paintFiber (auxPairWitness_left_mem_host hwW)
          (by simpa [hwcond.1] using hp.1),
        auxSupport_mem_paintFiber (auxPairWitness_right_mem_host hwW)
          (by simpa [hwcond.1] using hp.2)⟩
  have hinj : ∀ w ∈ F, ∀ z ∈ F,
      (w.leftBlock.auxSupport, w.rightBlock.auxSupport) =
        (z.leftBlock.auxSupport, z.rightBlock.auxSupport) → w = z := by
    intro w hw z hz hs
    have hwW := (Finset.mem_filter.mp hw).1
    have hzW := (Finset.mem_filter.mp hz).1
    have hleftBlock := AuxConcentration.auxSupport_injective
      (congrArg Prod.fst hs)
    have hrightBlock := AuxConcentration.auxSupport_injective
      (congrArg Prod.snd hs)
    have hcommon := (Finset.mem_filter.mp hw).2.1.trans
      (Finset.mem_filter.mp hz).2.1.symm
    have hwdata := mem_auxPairRoleWitnesses_iff.mp hwW
    have hzdata := mem_auxPairRoleWitnesses_iff.mp hzW
    have hleftRole := hwdata.2.1.trans hzdata.2.1.symm
    have hrightRole := hwdata.2.2.1.trans hzdata.2.2.1.symm
    cases w
    cases z
    simp_all
  calc
    F.card ≤ (A ∪ B).card := Finset.card_le_card_of_injOn
      (fun w ↦ (w.leftBlock.auxSupport, w.rightBlock.auxSupport)) hmap hinj
    _ ≤ A.card + B.card := Finset.card_union_le _ _
    _ ≤ L * L + L * L := by
      apply Nat.add_le_add <;>
        simpa [A, B] using Nat.mul_le_mul
          (hpaint _) (hpaint _)
    _ = 2 * L ^ 2 := by ring

theorem pairRoleWitness_paintsCross_card_le {n k L : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (hpaint : ∀ p : OrientedPaint n k,
      (paintFiber (auxiliaryHypergraph candidates R) p).card ≤ L)
    (a : AuxConcentration.PairRoleIndex n) (p : Fin n × Fin n) :
    ((AuxConcentration.pairRoleWitnesses candidates R a).filter
      (PairWitnessPaintsCross a p)).card ≤ k * (2 * L ^ 2) := by
  let F := (AuxConcentration.pairRoleWitnesses candidates R a).filter
    (PairWitnessPaintsCross a p)
  let C : Finset (Fin k) := Finset.univ
  have hcount := Finset.sum_card_fiberwise_eq_card_filter F C
    AuxConcentration.PairWitness.common
  have hfilter : F.filter (fun w ↦ w.common ∈ C) = F := by
    simp [C]
  rw [hfilter] at hcount
  have hfiber : ∀ c ∈ C,
      (F.filter fun w ↦ w.common = c).card ≤ 2 * L ^ 2 := by
    intro c hc
    apply (Finset.card_le_card ?_).trans
      (pairRoleWitness_paintsCross_common_fiber_card_le
        candidates R hpaint a p c)
    intro w hw
    have hwF := (Finset.mem_filter.mp hw).1
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hwF).1,
        (Finset.mem_filter.mp hw).2, (Finset.mem_filter.mp hwF).2⟩
  calc
    F.card = ∑ c ∈ C, (F.filter fun w ↦ w.common = c).card := hcount.symm
    _ ≤ ∑ _c ∈ C, 2 * L ^ 2 := Finset.sum_le_sum hfiber
    _ = k * (2 * L ^ 2) := by simp [C]

theorem jmcRole_crossPairFiber_card_le {n k L : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (hpaint : ∀ p : OrientedPaint n k,
      (paintFiber (auxiliaryHypergraph candidates R) p).card ≤ L)
    (a : AuxConcentration.PairRoleIndex n) (p : Fin n × Fin n) :
    ((jmcRoleSlotSystem candidates R a.x a.y
        (auxRootRoleEquiv a.leftRole)
        (auxRootRoleEquiv a.rightRole)).slots.filter fun q ↦
      q.cross = p).card ≤ 16 * k * L ^ 2 := by
  let T := jmcRoleSlotSystem candidates R a.x a.y
    (auxRootRoleEquiv a.leftRole) (auxRootRoleEquiv a.rightRole)
  let F : Finset (JMCRoleSlot candidates R a) :=
    T.slots.attach.filter fun q ↦ q.1.cross = p
  let W := (AuxConcentration.pairRoleWitnesses candidates R a).filter
    (PairWitnessPaintsCross a p)
  let f := jmcRoleSlotWitness candidates R a
  have hcardTF : (T.slots.filter fun q ↦ q.cross = p).card = F.card := by
    apply Finset.card_bij
      (fun q hq ↦ ⟨q, (Finset.mem_filter.mp hq).1⟩)
    · intro q hq
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_attach _ _, (Finset.mem_filter.mp hq).2⟩
    · intro q hq r hr heq
      exact congrArg Subtype.val heq
    · intro q hq
      refine ⟨q.1, Finset.mem_filter.mpr
        ⟨q.2, (Finset.mem_filter.mp hq).2⟩, Subtype.ext rfl⟩
  have hrange : ∀ q ∈ F, f q ∈ W := by
    intro q hq
    have hcross := (Finset.mem_filter.mp hq).2
    have hs := jmcRoleSlotWitness_spec candidates R a q
    exact Finset.mem_filter.mpr ⟨hs.1, by
      simpa [PairWitnessPaintsCross, hcross] using hs.2.2.2⟩
  have hcount := Finset.sum_card_fiberwise_eq_card_filter F W f
  have hfilter : F.filter (fun q ↦ f q ∈ W) = F := by
    apply Finset.filter_eq_self.mpr
    exact hrange
  rw [hfilter] at hcount
  have hfiber : ∀ w ∈ W, (F.filter fun q ↦ f q = w).card ≤ 8 := by
    intro w hw
    apply (Finset.card_le_card ?_).trans
      (jmcRoleSlotWitness_fiber_card_le_eight candidates R a w)
    intro q hq
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ q, (Finset.mem_filter.mp hq).2⟩
  have hW : W.card ≤ k * (2 * L ^ 2) :=
    pairRoleWitness_paintsCross_card_le candidates R hpaint a p
  rw [hcardTF]
  calc
    F.card = ∑ w ∈ W, (F.filter fun q ↦ f q = w).card := hcount.symm
    _ ≤ ∑ _w ∈ W, 8 := Finset.sum_le_sum hfiber
    _ = W.card * 8 := by simp
    _ ≤ (k * (2 * L ^ 2)) * 8 := Nat.mul_le_mul_right 8 hW
    _ = 16 * k * L ^ 2 := by ring

theorem jmcRole_graphKeyFiber_card_le {n k L : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (hpaint : ∀ p : OrientedPaint n k,
      (paintFiber (auxiliaryHypergraph candidates R) p).card ≤ L)
    (a : AuxConcentration.PairRoleIndex n) (u v : Fin n) :
    ((jmcRoleSlotSystem candidates R a.x a.y
        (auxRootRoleEquiv a.leftRole)
        (auxRootRoleEquiv a.rightRole)).slots.filter fun q ↦
      q.key = Sum.inl s(u, v)).card ≤ 32 * k * L ^ 2 := by
  let T := jmcRoleSlotSystem candidates R a.x a.y
    (auxRootRoleEquiv a.leftRole) (auxRootRoleEquiv a.rightRole)
  let F := T.slots.filter fun q ↦ q.key = Sum.inl s(u, v)
  let P := (Finset.univ : Finset (Fin n × Fin n)).filter fun p ↦
    s(p.1, p.2) = s(u, v)
  have hrange : ∀ q ∈ F, q.cross ∈ P := by
    intro q hq
    have hkey := (Finset.mem_filter.mp hq).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact Sum.inl.inj hkey
  have hcount := Finset.sum_card_fiberwise_eq_card_filter F P JMCCrossSlot.cross
  have hfilter : F.filter (fun q ↦ q.cross ∈ P) = F := by
    apply Finset.filter_eq_self.mpr
    exact hrange
  rw [hfilter] at hcount
  have hfiber : ∀ p ∈ P, (F.filter fun q ↦ q.cross = p).card ≤
      16 * k * L ^ 2 := by
    intro p hp
    apply (Finset.card_le_card ?_).trans
      (jmcRole_crossPairFiber_card_le candidates R hpaint a p)
    intro q hq
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1,
        (Finset.mem_filter.mp hq).2⟩
  have hP : P.card ≤ 2 :=
    CrossSlotSystem.card_orderedPairs_with_sym2_eq n u v
  calc
    F.card = ∑ p ∈ P, (F.filter fun q ↦ q.cross = p).card := hcount.symm
    _ ≤ ∑ _p ∈ P, 16 * k * L ^ 2 := Finset.sum_le_sum hfiber
    _ = P.card * (16 * k * L ^ 2) := by simp
    _ ≤ 2 * (16 * k * L ^ 2) := Nat.mul_le_mul_right _ hP
    _ = 32 * k * L ^ 2 := by ring

/-- A fixed auxiliary host edge contains eight auxiliary vertices, and only
its graph-edge vertices can be cross keys. -/
theorem jmcRole_coverKeyIncidence_card_le {n k L : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (hpaint : ∀ p : OrientedPaint n k,
      (paintFiber (auxiliaryHypergraph candidates R) p).card ≤ L)
    (a : AuxConcentration.PairRoleIndex n)
    {e : Finset (AuxVertex n k)} (he : e ∈ auxiliaryHypergraph candidates R) :
    ((jmcRoleSlotSystem candidates R a.x a.y
        (auxRootRoleEquiv a.leftRole)
        (auxRootRoleEquiv a.rightRole)).slots.filter fun q ↦
      q.key ∈ e).card ≤ 256 * k * L ^ 2 := by
  let T := jmcRoleSlotSystem candidates R a.x a.y
    (auxRootRoleEquiv a.leftRole) (auxRootRoleEquiv a.rightRole)
  let F := T.slots.filter fun q ↦ q.key ∈ e
  have hcount := Finset.sum_card_fiberwise_eq_card_filter F e JMCCrossSlot.key
  have hfilter : F.filter (fun q ↦ q.key ∈ e) = F := by
    apply Finset.filter_eq_self.mpr
    intro q hq
    exact (Finset.mem_filter.mp hq).2
  rw [hfilter] at hcount
  have hfiber : ∀ z ∈ e, (F.filter fun q ↦ q.key = z).card ≤
      32 * k * L ^ 2 := by
    intro z hz
    rcases z with s | label
    · induction s using Sym2.inductionOn with
      | _ u v =>
          apply (Finset.card_le_card ?_).trans
            (jmcRole_graphKeyFiber_card_le candidates R hpaint a u v)
          intro q hq
          exact Finset.mem_filter.mpr
            ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1,
              (Finset.mem_filter.mp hq).2⟩
    · have hempty : (F.filter fun q ↦ q.key = Sum.inr label) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro q hq
        have hcontra :
            (Sum.inl s(q.cross.1, q.cross.2) : AuxVertex n k) =
              Sum.inr label := by
          simpa [JMCCrossSlot.key] using (Finset.mem_filter.mp hq).2
        exact Sum.inl_ne_inr hcontra
      simp [hempty]
  have hecard : e.card = 8 := auxiliaryHypergraph_uniform candidates R he
  calc
    F.card = ∑ z ∈ e, (F.filter fun q ↦ q.key = z).card := hcount.symm
    _ ≤ ∑ _z ∈ e, 32 * k * L ^ 2 := Finset.sum_le_sum hfiber
    _ = e.card * (32 * k * L ^ 2) := by simp
    _ = 256 * k * L ^ 2 := by rw [hecard]; ring

theorem CrossSlotSystem.coverEdges_card_le_degree {V Q : Type*}
    [DecidableEq V] [DecidableEq Q] {H : Hypergraph V}
    (T : CrossSlotSystem V Q H) {q : Q} (hq : q ∈ T.slots) :
    (H.filter (T.covers q)).card ≤ degree H (T.coverKey q) := by
  apply Finset.card_le_card
  intro e he
  have hcover := (Finset.mem_filter.mp he).2
  exact Finset.mem_filter.mpr
    ⟨T.covers_mem q hq e hcover, T.covers_key_mem q hq e hcover⟩

/-- Triple-test extensions through one fixed root edge split into the case
where that edge is the cover and the case where it is one of the two owner
edges. -/
theorem jmcRole_tripleRootOne_card_le {n k D L : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (hmax : MaxDegreeLE (auxiliaryHypergraph candidates R) D)
    (hpaint : ∀ p : OrientedPaint n k,
      (paintFiber (auxiliaryHypergraph candidates R) p).card ≤ L)
    (a : AuxConcentration.PairRoleIndex n)
    (e : Finset (AuxVertex n k)) :
    ((jmcRoleSlotSystem candidates R a.x a.y
        (auxRootRoleEquiv a.leftRole)
        (auxRootRoleEquiv a.rightRole)).coverPairs.filter fun qe ↦
      e ∈ CrossSlotSystem.extendedOwner
        (jmcRoleSlotSystem candidates R a.x a.y
          (auxRootRoleEquiv a.leftRole)
          (auxRootRoleEquiv a.rightRole)) qe).card ≤
      16 * D ^ 2 + 256 * k * L ^ 2 := by
  let T := jmcRoleSlotSystem candidates R a.x a.y
    (auxRootRoleEquiv a.leftRole) (auxRootRoleEquiv a.rightRole)
  let F := T.coverPairs.filter fun qe ↦ e ∈ T.extendedOwner qe
  let A := T.coverPairs.filter fun qe ↦ qe.2 = e
  let B := T.coverPairs.filter fun qe ↦ e ∈ T.owner qe.1
  have hsub : F ⊆ A ∪ B := by
    intro qe hqe
    have hpair := (Finset.mem_filter.mp hqe).1
    have hext := (Finset.mem_filter.mp hqe).2
    simp only [CrossSlotSystem.extendedOwner, Finset.mem_insert] at hext
    rcases hext with heq | heowner
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hpair, heq.symm⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hpair, heowner⟩)
  have hA : A.card ≤ 256 * k * L ^ 2 := by
    by_cases heH : e ∈ auxiliaryHypergraph candidates R
    · apply (Finset.card_le_card_of_injOn Prod.fst ?_ ?_).trans
        (jmcRole_coverKeyIncidence_card_le candidates R hpaint a heH)
      · intro qe hqe
        have hpair := (Finset.mem_filter.mp hqe).1
        have heq := (Finset.mem_filter.mp hqe).2
        have hcp := CrossSlotSystem.mem_coverPairs_iff.mp hpair
        exact Finset.mem_filter.mpr ⟨hcp.1, by
          rw [← heq]
          exact T.covers_key_mem qe.1 hcp.1 qe.2 hcp.2.2⟩
      · intro qe hqe rf hrf hfirst
        apply Prod.ext hfirst
        exact (Finset.mem_filter.mp hqe).2.trans
          (Finset.mem_filter.mp hrf).2.symm
    · have hAempty : A = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro qe hqe
        have hpair := (Finset.mem_filter.mp hqe).1
        have heq := (Finset.mem_filter.mp hqe).2
        exact heH (heq ▸ (CrossSlotSystem.mem_coverPairs_iff.mp hpair).2.1)
      simp [hAempty]
  let Qe := T.slots.filter fun q ↦ e ∈ T.owner q
  have hB : B.card ≤ 16 * D ^ 2 := by
    have hrange : ∀ qe ∈ B, qe.1 ∈ Qe := by
      intro qe hqe
      have hpair := (Finset.mem_filter.mp hqe).1
      have heowner := (Finset.mem_filter.mp hqe).2
      exact Finset.mem_filter.mpr
        ⟨(CrossSlotSystem.mem_coverPairs_iff.mp hpair).1, heowner⟩
    have hcount := Finset.sum_card_fiberwise_eq_card_filter B Qe Prod.fst
    have hfilter : B.filter (fun qe ↦ qe.1 ∈ Qe) = B := by
      apply Finset.filter_eq_self.mpr
      exact hrange
    rw [hfilter] at hcount
    have hfiber : ∀ q ∈ Qe, (B.filter fun qe ↦ qe.1 = q).card ≤ D := by
      intro q hq
      have hqslot := (Finset.mem_filter.mp hq).1
      apply (Finset.card_le_card_of_injOn Prod.snd ?_ ?_).trans
        ((T.coverEdges_card_le_degree hqslot).trans (hmax _))
      · intro qe hqe
        have hpair := (Finset.mem_filter.mp (Finset.mem_filter.mp hqe).1).1
        have hfirst := (Finset.mem_filter.mp hqe).2
        have hcp := CrossSlotSystem.mem_coverPairs_iff.mp hpair
        exact Finset.mem_filter.mpr ⟨hcp.2.1, by simpa [hfirst] using hcp.2.2⟩
      · intro qe hqe rf hrf hsecond
        apply Prod.ext
        · exact (Finset.mem_filter.mp hqe).2.trans
            (Finset.mem_filter.mp hrf).2.symm
        · exact hsecond
    have hQe : Qe.card ≤ 16 * D :=
      jmcRole_pairOwnerIncidence_card_le_sixteen_mul_degree
        candidates R hmax a e
    calc
      B.card = ∑ q ∈ Qe, (B.filter fun qe ↦ qe.1 = q).card := hcount.symm
      _ ≤ ∑ _q ∈ Qe, D := Finset.sum_le_sum hfiber
      _ = Qe.card * D := by simp
      _ ≤ (16 * D) * D := Nat.mul_le_mul_right D hQe
      _ = 16 * D ^ 2 := by ring
  calc
    F.card ≤ (A ∪ B).card := Finset.card_le_card hsub
    _ ≤ A.card + B.card := Finset.card_union_le _ _
    _ ≤ 256 * k * L ^ 2 + 16 * D ^ 2 := Nat.add_le_add hA hB
    _ = 16 * D ^ 2 + 256 * k * L ^ 2 := by omega

/-- With two distinct root edges, either one is the unique cover edge or
both form the complete two-edge owner. -/
theorem jmcRole_tripleRootTwo_card_le {n k D : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (hmax : MaxDegreeLE (auxiliaryHypergraph candidates R) D)
    (a : AuxConcentration.PairRoleIndex n)
    (e f : Finset (AuxVertex n k)) (hef : e ≠ f) :
    ((jmcRoleSlotSystem candidates R a.x a.y
        (auxRootRoleEquiv a.leftRole)
        (auxRootRoleEquiv a.rightRole)).coverPairs.filter fun qe ↦
      e ∈ CrossSlotSystem.extendedOwner
          (jmcRoleSlotSystem candidates R a.x a.y
            (auxRootRoleEquiv a.leftRole)
            (auxRootRoleEquiv a.rightRole)) qe ∧
        f ∈ CrossSlotSystem.extendedOwner
          (jmcRoleSlotSystem candidates R a.x a.y
            (auxRootRoleEquiv a.leftRole)
            (auxRootRoleEquiv a.rightRole)) qe).card ≤ 48 * D := by
  let T := jmcRoleSlotSystem candidates R a.x a.y
    (auxRootRoleEquiv a.leftRole) (auxRootRoleEquiv a.rightRole)
  let F := T.coverPairs.filter fun qe ↦
    e ∈ T.extendedOwner qe ∧ f ∈ T.extendedOwner qe
  let A := T.coverPairs.filter fun qe ↦ qe.2 = e ∧ f ∈ T.owner qe.1
  let B := T.coverPairs.filter fun qe ↦ qe.2 = f ∧ e ∈ T.owner qe.1
  let C := T.coverPairs.filter fun qe ↦
    e ∈ T.owner qe.1 ∧ f ∈ T.owner qe.1
  have hsub : F ⊆ (A ∪ B) ∪ C := by
    intro qe hqe
    have hpair := (Finset.mem_filter.mp hqe).1
    have hext := (Finset.mem_filter.mp hqe).2
    simp only [CrossSlotSystem.extendedOwner, Finset.mem_insert] at hext
    rcases hext.1 with hecover | heowner
    · rcases hext.2 with hfcover | hfowner
      · exact (hef (hecover.trans hfcover.symm)).elim
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hpair, hecover.symm, hfowner⟩))
    · rcases hext.2 with hfcover | hfowner
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hpair, hfcover.symm, heowner⟩))
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hpair, heowner, hfowner⟩)
  have hA : A.card ≤ 16 * D := by
    apply (Finset.card_le_card_of_injOn Prod.fst ?_ ?_).trans
      (jmcRole_pairOwnerIncidence_card_le_sixteen_mul_degree
        candidates R hmax a f)
    · intro qe hqe
      have hpair := (Finset.mem_filter.mp hqe).1
      exact Finset.mem_filter.mpr
        ⟨(CrossSlotSystem.mem_coverPairs_iff.mp hpair).1,
          (Finset.mem_filter.mp hqe).2.2⟩
    · intro qe hqe rf hrf hfirst
      apply Prod.ext hfirst
      exact (Finset.mem_filter.mp hqe).2.1.trans
        (Finset.mem_filter.mp hrf).2.1.symm
  have hB : B.card ≤ 16 * D := by
    apply (Finset.card_le_card_of_injOn Prod.fst ?_ ?_).trans
      (jmcRole_pairOwnerIncidence_card_le_sixteen_mul_degree
        candidates R hmax a e)
    · intro qe hqe
      have hpair := (Finset.mem_filter.mp hqe).1
      exact Finset.mem_filter.mpr
        ⟨(CrossSlotSystem.mem_coverPairs_iff.mp hpair).1,
          (Finset.mem_filter.mp hqe).2.2⟩
    · intro qe hqe rf hrf hfirst
      apply Prod.ext hfirst
      exact (Finset.mem_filter.mp hqe).2.1.trans
        (Finset.mem_filter.mp hrf).2.1.symm
  let Qef := T.slots.filter fun q ↦ T.owner q = {e, f}
  have hC : C.card ≤ 16 * D := by
    have hrange : ∀ qe ∈ C, qe.1 ∈ Qef := by
      intro qe hqe
      have hpair := (Finset.mem_filter.mp hqe).1
      have heowner := (Finset.mem_filter.mp hqe).2.1
      have hfowner := (Finset.mem_filter.mp hqe).2.2
      have hcp := CrossSlotSystem.mem_coverPairs_iff.mp hpair
      have hsubpair : ({e, f} : Hypergraph (AuxVertex n k)) ⊆ T.owner qe.1 := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact heowner
        · exact hfowner
      have hpaircard : ({e, f} : Hypergraph (AuxVertex n k)).card = 2 := by
        simp [hef]
      have hownerEq : T.owner qe.1 = {e, f} := by
        symm
        apply Finset.eq_of_subset_of_card_le hsubpair
        rw [T.owner_card qe.1 hcp.1, hpaircard]
      exact Finset.mem_filter.mpr ⟨hcp.1, hownerEq⟩
    have hcount := Finset.sum_card_fiberwise_eq_card_filter C Qef Prod.fst
    have hfilter : C.filter (fun qe ↦ qe.1 ∈ Qef) = C := by
      apply Finset.filter_eq_self.mpr
      exact hrange
    rw [hfilter] at hcount
    have hfiber : ∀ q ∈ Qef, (C.filter fun qe ↦ qe.1 = q).card ≤ D := by
      intro q hq
      have hqslot := (Finset.mem_filter.mp hq).1
      apply (Finset.card_le_card_of_injOn Prod.snd ?_ ?_).trans
        ((T.coverEdges_card_le_degree hqslot).trans (hmax _))
      · intro qe hqe
        have hpair := (Finset.mem_filter.mp (Finset.mem_filter.mp hqe).1).1
        have hfirst := (Finset.mem_filter.mp hqe).2
        have hcp := CrossSlotSystem.mem_coverPairs_iff.mp hpair
        exact Finset.mem_filter.mpr ⟨hcp.2.1, by simpa [hfirst] using hcp.2.2⟩
      · intro qe hqe rf hrf hsecond
        apply Prod.ext
        · exact (Finset.mem_filter.mp hqe).2.trans
            (Finset.mem_filter.mp hrf).2.symm
        · exact hsecond
    have hQef : Qef.card ≤ 16 :=
      jmcRole_pairFiber_card_le_sixteen candidates R a {e, f}
    calc
      C.card = ∑ q ∈ Qef, (C.filter fun qe ↦ qe.1 = q).card := hcount.symm
      _ ≤ ∑ _q ∈ Qef, D := Finset.sum_le_sum hfiber
      _ = Qef.card * D := by simp
      _ ≤ 16 * D := Nat.mul_le_mul_right D hQef
  calc
    F.card ≤ ((A ∪ B) ∪ C).card := Finset.card_le_card hsub
    _ ≤ (A ∪ B).card + C.card := Finset.card_union_le _ _
    _ ≤ (A.card + B.card) + C.card := Nat.add_le_add_right
      (Finset.card_union_le _ _) _
    _ ≤ (16 * D + 16 * D) + 16 * D := by omega
    _ = 48 * D := by ring

theorem jmcRole_tripleExtension_rootOne_le {n k D L : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (hmax : MaxDegreeLE (auxiliaryHypergraph candidates R) D)
    (hpaint : ∀ p : OrientedPaint n k,
      (paintFiber (auxiliaryHypergraph candidates R) p).card ≤ L)
    (a : AuxConcentration.PairRoleIndex n)
    (root : Hypergraph (AuxVertex n k)) (hroot : root.card = 1) :
    testExtension
        (jmcRoleSlotSystem candidates R a.x a.y
          (auxRootRoleEquiv a.leftRole)
          (auxRootRoleEquiv a.rightRole)).tripleWeight
        (auxiliaryHypergraph candidates R) 3 root ≤
      (16 * D ^ 2 + 256 * k * L ^ 2 : ℕ) := by
  obtain ⟨e, rfl⟩ := Finset.card_eq_one.mp hroot
  let T := jmcRoleSlotSystem candidates R a.x a.y
    (auxRootRoleEquiv a.leftRole) (auxRootRoleEquiv a.rightRole)
  rw [CrossSlotSystem.testExtension_tripleWeight]
  have hcard :
      (T.coverPairs.filter fun qe ↦ T.extendedOwner qe ∈
        ((auxiliaryHypergraph candidates R).powersetCard 3).filter
          ({e} ⊆ ·)).card ≤
        (T.coverPairs.filter fun qe ↦ e ∈ T.extendedOwner qe).card := by
    apply Finset.card_le_card
    intro qe hqe
    have hpair := (Finset.mem_filter.mp hqe).1
    have hfamily := (Finset.mem_filter.mp hqe).2
    have hsub := (Finset.mem_filter.mp hfamily).2
    exact Finset.mem_filter.mpr ⟨hpair, hsub (by simp)⟩
  exact_mod_cast hcard.trans
    (jmcRole_tripleRootOne_card_le candidates R hmax hpaint a e)

theorem jmcRole_tripleExtension_rootTwo_le {n k D : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (hmax : MaxDegreeLE (auxiliaryHypergraph candidates R) D)
    (a : AuxConcentration.PairRoleIndex n)
    (root : Hypergraph (AuxVertex n k)) (hroot : root.card = 2) :
    testExtension
        (jmcRoleSlotSystem candidates R a.x a.y
          (auxRootRoleEquiv a.leftRole)
          (auxRootRoleEquiv a.rightRole)).tripleWeight
        (auxiliaryHypergraph candidates R) 3 root ≤ (48 * D : ℕ) := by
  obtain ⟨e, f, hef, rfl⟩ := Finset.card_eq_two.mp hroot
  let T := jmcRoleSlotSystem candidates R a.x a.y
    (auxRootRoleEquiv a.leftRole) (auxRootRoleEquiv a.rightRole)
  rw [CrossSlotSystem.testExtension_tripleWeight]
  have hcard :
      (T.coverPairs.filter fun qe ↦ T.extendedOwner qe ∈
        ((auxiliaryHypergraph candidates R).powersetCard 3).filter
          ({e, f} ⊆ ·)).card ≤
        (T.coverPairs.filter fun qe ↦
          e ∈ T.extendedOwner qe ∧ f ∈ T.extendedOwner qe).card := by
    apply Finset.card_le_card
    intro qe hqe
    have hpair := (Finset.mem_filter.mp hqe).1
    have hfamily := (Finset.mem_filter.mp hqe).2
    have hsub := (Finset.mem_filter.mp hfamily).2
    exact Finset.mem_filter.mpr ⟨hpair, hsub (by simp), hsub (by simp)⟩
  exact_mod_cast hcard.trans
    (jmcRole_tripleRootTwo_card_le candidates R hmax a e f hef)

/-- A fixed three-edge extended owner has three choices for its cover edge;
after removing that edge its remaining slot is controlled by the pair
fibre. -/
theorem CrossSlotSystem.tripleFiber_card_le_three_mul {V Q : Type*}
    [DecidableEq V] [DecidableEq Q] {H : Hypergraph V}
    (T : CrossSlotSystem V Q H) (c : ℕ)
    (hpair : ∀ S, (T.slots.filter fun q ↦ T.owner q = S).card ≤ c)
    (S : Hypergraph V) :
    (T.coverPairs.filter fun qe ↦ T.extendedOwner qe = S).card ≤ 3 * c := by
  let F := T.coverPairs.filter fun qe ↦ T.extendedOwner qe = S
  by_cases hF : F = ∅
  · simp [F, hF]
  obtain ⟨qe₀, hqe₀⟩ := Finset.nonempty_iff_ne_empty.mpr hF
  have hqe₀pair := (Finset.mem_filter.mp hqe₀).1
  have hqe₀owner := (Finset.mem_filter.mp hqe₀).2
  have hScard : S.card = 3 := by
    rw [← hqe₀owner]
    exact T.extendedOwner_card hqe₀pair
  have hrange : ∀ qe ∈ F, qe.2 ∈ S := by
    intro qe hqe
    have heq := (Finset.mem_filter.mp hqe).2
    rw [← heq]
    exact Finset.mem_insert_self _ _
  have hcount := Finset.sum_card_fiberwise_eq_card_filter F S Prod.snd
  have hfilter : F.filter (fun qe ↦ qe.2 ∈ S) = F := by
    apply Finset.filter_eq_self.mpr
    exact hrange
  rw [hfilter] at hcount
  have hfiber : ∀ e ∈ S, (F.filter fun qe ↦ qe.2 = e).card ≤ c := by
    intro e he
    apply (Finset.card_le_card_of_injOn Prod.fst ?_ ?_).trans
      (hpair (S.erase e))
    · intro qe hqe
      have hqF := (Finset.mem_filter.mp hqe).1
      have heqe := (Finset.mem_filter.mp hqe).2
      have hqpair := (Finset.mem_filter.mp hqF).1
      have howner := (Finset.mem_filter.mp hqF).2
      have hcp := CrossSlotSystem.mem_coverPairs_iff.mp hqpair
      apply Finset.mem_filter.mpr
      refine ⟨hcp.1, ?_⟩
      subst e
      rw [← howner, CrossSlotSystem.extendedOwner]
      simp [T.covers_fresh qe.1 hcp.1 qe.2 hcp.2.2]
    · intro qe hqe rf hrf hfirst
      apply Prod.ext hfirst
      exact (Finset.mem_filter.mp hqe).2.trans
        (Finset.mem_filter.mp hrf).2.symm
  calc
    F.card = ∑ e ∈ S, (F.filter fun qe ↦ qe.2 = e).card := hcount.symm
    _ ≤ ∑ _e ∈ S, c := Finset.sum_le_sum hfiber
    _ = S.card * c := by simp
    _ = 3 * c := by rw [hScard]

theorem jmcRole_tripleFiber_card_le_fortyEight {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (a : AuxConcentration.PairRoleIndex n)
    (S : Hypergraph (AuxVertex n k)) :
    ((jmcRoleSlotSystem candidates R a.x a.y
        (auxRootRoleEquiv a.leftRole)
        (auxRootRoleEquiv a.rightRole)).coverPairs.filter fun qe ↦
      CrossSlotSystem.extendedOwner
        (jmcRoleSlotSystem candidates R a.x a.y
          (auxRootRoleEquiv a.leftRole)
          (auxRootRoleEquiv a.rightRole)) qe = S).card ≤ 48 := by
  exact (CrossSlotSystem.tripleFiber_card_le_three_mul
    (jmcRoleSlotSystem candidates R a.x a.y
      (auxRootRoleEquiv a.leftRole)
      (auxRootRoleEquiv a.rightRole)) 16
    (jmcRole_pairFiber_card_le_sixteen candidates R a) S).trans_eq (by norm_num)

/-- Every retained common-colour witness generates at most eight oriented
fresh slots (two orientations and at most two painted neighbours on each
side). -/
theorem jmcRole_pairTotal_le_eight_mul_pairRoleWitnesses_card {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (a : AuxConcentration.PairRoleIndex n) :
    testTotal
        (jmcRoleSlotSystem candidates R a.x a.y
          (auxRootRoleEquiv a.leftRole)
          (auxRootRoleEquiv a.rightRole)).pairWeight
        (auxiliaryHypergraph candidates R) 2 ≤
      8 * ((AuxConcentration.pairRoleWitnesses candidates R a).card : ℝ) := by
  let T := jmcRoleSlotSystem candidates R a.x a.y
    (auxRootRoleEquiv a.leftRole) (auxRootRoleEquiv a.rightRole)
  let W := AuxConcentration.pairRoleWitnesses candidates R a
  let f := jmcRoleSlotWitness candidates R a
  have hrange :
      (Finset.univ : Finset (JMCRoleSlot candidates R a)).filter
          (fun q ↦ f q ∈ W) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro q hq
    exact (jmcRoleSlotWitness_spec candidates R a q).1
  have hcount := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (JMCRoleSlot candidates R a)) W f
  rw [hrange] at hcount
  have hsum : T.slots.card =
      ∑ w ∈ W, ((Finset.univ : Finset (JMCRoleSlot candidates R a)).filter
        fun q ↦ f q = w).card := by
    rw [hcount]
    simp [T, JMCRoleSlot]
  have hcardNat : T.slots.card ≤ 8 * W.card := by
    rw [hsum]
    calc
      ∑ w ∈ W, ((Finset.univ : Finset (JMCRoleSlot candidates R a)).filter
          fun q ↦ f q = w).card ≤
          ∑ _w ∈ W, 8 := by
        exact Finset.sum_le_sum fun w hw ↦
          jmcRoleSlotWitness_fiber_card_le_eight candidates R a w
      _ = 8 * W.card := by simp [Nat.mul_comm]
  rw [CrossSlotSystem.testTotal_pairWeight]
  have hfilter :
      T.slots.filter (fun q ↦ T.owner q ∈
        (auxiliaryHypergraph candidates R).powersetCard 2) = T.slots := by
    apply Finset.filter_eq_self.mpr
    intro q hq
    exact Finset.mem_powersetCard.mpr
      ⟨(T.owner_matching q hq).1, T.owner_card q hq⟩
  rw [hfilter]
  exact_mod_cast hcardNat

/-- Pointwise fibre version of the preceding fresh-witness injection. -/
theorem freshPairRoleWitnessWeight_le_jmcRole_pairWeight {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (a : AuxConcentration.PairRoleIndex n)
    (Q : Hypergraph (AuxVertex n k)) :
    freshPairRoleWitnessWeight candidates R a Q ≤
      (jmcRoleSlotSystem candidates R a.x a.y
        (auxRootRoleEquiv a.leftRole)
        (auxRootRoleEquiv a.rightRole)).pairWeight Q := by
  unfold freshPairRoleWitnessWeight CrossSlotSystem.pairWeight
  exact_mod_cast Finset.card_le_card_of_injOn
    (auxPairWitnessToSlot a) (by
      intro w hw
      have hpair := Finset.mem_filter.mp hw
      have hfresh := Finset.mem_filter.mp hpair.1
      refine Finset.mem_filter.mpr
        ⟨auxPairWitnessToSlot_mem hfresh.1 hfresh.2, ?_⟩
      change (auxPairWitnessToSlot a w).owner = Q
      simpa [auxPairWitnessToSlot, JMCCrossSlot.owner,
        AuxConcentration.PairWitness.support] using hpair.2)
    (fun w hw z hz heq ↦
      auxPairWitnessToSlot_injectiveOn a
        (Finset.mem_filter.mp hw).1 (Finset.mem_filter.mp hz).1 heq)

namespace CrossSlotSystem

variable {Q : Type*} [DecidableEq Q] {H : Hypergraph V}

/-- The covering edges above one fixed two-edge slot. -/
def coverEdgeFiber (T : CrossSlotSystem V Q H) (q : Q) : Finset (Q × Finset V) :=
  (H.filter (T.covers q)).image fun e ↦ (q, e)

theorem coverPairs_eq_biUnion_coverEdgeFiber (T : CrossSlotSystem V Q H) :
    T.coverPairs = T.slots.biUnion T.coverEdgeFiber := by
  ext qe
  rcases qe with ⟨q, e⟩
  simp [coverPairs, coverEdgeFiber, and_assoc]

theorem coverEdgeFiber_pairwiseDisjoint (T : CrossSlotSystem V Q H) :
    (T.slots : Set Q).PairwiseDisjoint T.coverEdgeFiber := by
  intro q hq r hr hqr
  change Disjoint (T.coverEdgeFiber q) (T.coverEdgeFiber r)
  rw [Finset.disjoint_left]
  intro qe hqmem hrmem
  obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hqmem
  obtain ⟨f, hf, hfq⟩ := Finset.mem_image.mp hrmem
  have hfirst := congrArg Prod.fst (heq.trans hfq.symm)
  exact hqr hfirst

theorem card_coverPairs_eq_sum_coverEdges (T : CrossSlotSystem V Q H) :
    T.coverPairs.card =
      ∑ q ∈ T.slots, (H.filter (T.covers q)).card := by
  rw [coverPairs_eq_biUnion_coverEdgeFiber,
    Finset.card_biUnion (coverEdgeFiber_pairwiseDisjoint T)]
  apply Finset.sum_congr rfl
  intro q hq
  exact Finset.card_image_of_injective _ (fun _ _ h ↦ Prod.mk.inj h |>.2)

theorem testTotal_pairWeight_host_eq_card (T : CrossSlotSystem V Q H) :
    testTotal T.pairWeight H 2 = (T.slots.card : ℝ) := by
  rw [testTotal_pairWeight]
  rw [show T.slots.filter (fun q ↦ T.owner q ∈ H.powersetCard 2) =
      T.slots by
    apply Finset.filter_eq_self.mpr
    intro q hq
    exact Finset.mem_powersetCard.mpr
      ⟨(T.owner_matching q hq).1, T.owner_card q hq⟩]

theorem testTotal_tripleWeight_host_eq_card (T : CrossSlotSystem V Q H) :
    testTotal T.tripleWeight H 3 = (T.coverPairs.card : ℝ) := by
  rw [testTotal_tripleWeight]
  rw [show T.coverPairs.filter (fun qe ↦
      T.extendedOwner qe ∈ H.powersetCard 3) = T.coverPairs by
    apply Finset.filter_eq_self.mpr
    intro qe hqe
    exact Finset.mem_powersetCard.mpr
      ⟨(T.extendedOwner_matching hqe).1, T.extendedOwner_card hqe⟩]

/-- If every slot has at least `m` available covering host edges, then the
three-uniform host total is at least `m` times the two-uniform host total.
This is the deterministic cancellation input used by P5. -/
theorem coverLower_mul_pairTotal_le_tripleTotal
    (T : CrossSlotSystem V Q H) (m : ℕ)
    (hcover : ∀ q ∈ T.slots, m ≤ (H.filter (T.covers q)).card) :
    (m : ℝ) * testTotal T.pairWeight H 2 ≤
      testTotal T.tripleWeight H 3 := by
  rw [testTotal_pairWeight_host_eq_card,
    testTotal_tripleWeight_host_eq_card, card_coverPairs_eq_sum_coverEdges]
  norm_num only [Nat.cast_sum, Nat.cast_mul]
  exact_mod_cast show m * T.slots.card ≤
      ∑ q ∈ T.slots, (H.filter (T.covers q)).card by
    calc
      m * T.slots.card = ∑ _q ∈ T.slots, m := by simp [Nat.mul_comm]
      _ ≤ ∑ q ∈ T.slots, (H.filter (T.covers q)).card := by
        exact Finset.sum_le_sum fun q hq ↦ hcover q hq

end CrossSlotSystem

/-! ### Available-cover lower bounds

The key-freshness clause in `IsJMCCrossSlot` is exactly what makes the
following estimate true.  Among the host edges through the cross key, an
edge can fail to cover the slot only by meeting one of the sixteen vertices
in its two disjoint eight-vertex owner edges.  Each such exceptional family
is a pair-codegree fibre. -/

/-- Host edges through the key and one specified owner vertex. -/
def jmcKeyVertexFiber {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (q : JMCCrossSlot n k) (v : AuxVertex n k) :
    Hypergraph (AuxVertex n k) :=
  (auxiliaryHypergraph candidates R).filter fun e ↦ q.key ∈ e ∧ v ∈ e

theorem card_jmcKeyVertexFiber_le {n k L : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (hcodeg : MaxCodegreeLE (auxiliaryHypergraph candidates R) 2 L)
    (q : JMCCrossSlot n k) {v : AuxVertex n k}
    (hv : v ∈ vertexFinset q.owner) (hfresh : q.key ∉ vertexFinset q.owner) :
    (jmcKeyVertexFiber candidates R q v).card ≤ L := by
  have hne : q.key ≠ v := by
    intro h
    exact hfresh (h ▸ hv)
  calc
    (jmcKeyVertexFiber candidates R q v).card =
        codegree (auxiliaryHypergraph candidates R) {q.key, v} := by
      congr 1
      ext e
      simp only [jmcKeyVertexFiber, codegree, Finset.mem_filter,
        Finset.insert_subset_iff, Finset.singleton_subset_iff]
    _ ≤ L := hcodeg _ (by simp [hne])

theorem card_vertexFinset_jmcRole_owner_le_sixteen {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {x y : Fin n} {rx ry : JMCPaintRole} {q : JMCCrossSlot n k}
    (hq : q ∈ (jmcRoleSlotSystem candidates R x y rx ry).slots) :
    (vertexFinset q.owner).card ≤ 16 := by
  have hmatch :=
    (jmcRoleSlotSystem candidates R x y rx ry).owner_matching q hq
  have hxmem : q.xEdge ∈ auxiliaryHypergraph candidates R := by
    apply hmatch.1
    change q.xEdge ∈ q.owner
    exact Finset.mem_insert_self _ _
  have hymem : q.yEdge ∈ auxiliaryHypergraph candidates R := by
    apply hmatch.1
    change q.yEdge ∈ q.owner
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hxcard := auxiliaryHypergraph_uniform candidates R hxmem
  have hycard := auxiliaryHypergraph_uniform candidates R hymem
  rw [show vertexFinset q.owner = q.xEdge ∪ q.yEdge by
    simp [vertexFinset, JMCCrossSlot.owner]]
  calc
    (q.xEdge ∪ q.yEdge).card ≤ q.xEdge.card + q.yEdge.card :=
      Finset.card_union_le _ _
    _ = 16 := by omega

/-- A fresh role slot has all but at most `16 * L` of the host edges
through its cross key available as covers. -/
theorem jmcRole_cover_card_add_le_degree {n k L : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (hcodeg : MaxCodegreeLE (auxiliaryHypergraph candidates R) 2 L)
    {x y : Fin n} {rx ry : JMCPaintRole} {q : JMCCrossSlot n k}
    (hq : q ∈ (jmcRoleSlotSystem candidates R x y rx ry).slots) :
    degree (auxiliaryHypergraph candidates R) q.key ≤
      ((auxiliaryHypergraph candidates R).filter
        ((jmcRoleSlotSystem candidates R x y rx ry).covers q)).card + 16 * L := by
  let H := auxiliaryHypergraph candidates R
  let T := jmcRoleSlotSystem candidates R x y rx ry
  let U := vertexFinset q.owner
  let D := H.filter fun e ↦ q.key ∈ e
  let B := U.biUnion fun v ↦ jmcKeyVertexFiber candidates R q v
  let C := H.filter (T.covers q)
  have hfresh : q.key ∉ U := by
    have hbase := (CrossSlotSystem.mem_restrict_slots.mp hq).1
    exact (mem_jmcCrossSlots.mp hbase).2.2.1
  have hmatch := T.owner_matching q hq
  have hsub : D ⊆ C ∪ B := by
    intro e he
    have heD := Finset.mem_filter.mp he
    by_cases hdisj : Disjoint e U
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨heD.1, heD.2, ?_, ?_⟩
      · intro heowner
        exact hfresh (mem_vertexFinset.mpr ⟨e, heowner, heD.2⟩)
      · rw [isMatching_insert_iff]
        refine ⟨heD.1, hmatch, ?_⟩
        intro f hf hne
        exact Finset.disjoint_of_subset_right
          (by exact edge_subset_vertexFinset hf) hdisj
    · apply Finset.mem_union_right
      obtain ⟨v, hve, hvU⟩ := not_disjoint_iff.mp hdisj
      apply Finset.mem_biUnion.mpr
      refine ⟨v, hvU, ?_⟩
      exact Finset.mem_filter.mpr ⟨heD.1, heD.2, hve⟩
  have hB : B.card ≤ 16 * L := by
    calc
      B.card ≤ U.card * L := Finset.card_biUnion_le_card_mul _ _ _
        (fun v hv ↦ card_jmcKeyVertexFiber_le candidates R hcodeg q hv hfresh)
      _ ≤ 16 * L := Nat.mul_le_mul_right L
        (card_vertexFinset_jmcRole_owner_le_sixteen candidates R hq)
  change D.card ≤ C.card + 16 * L
  calc
    D.card ≤ (C ∪ B).card := Finset.card_le_card hsub
    _ ≤ C.card + B.card := Finset.card_union_le _ _
    _ ≤ C.card + 16 * L := Nat.add_le_add_left hB _

theorem jmcRole_cover_lower {n k L m : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (hcodeg : MaxCodegreeLE (auxiliaryHypergraph candidates R) 2 L)
    {x y : Fin n} {rx ry : JMCPaintRole}
    (hdegree : ∀ q ∈ (jmcRoleSlotSystem candidates R x y rx ry).slots,
      m + 16 * L ≤ degree (auxiliaryHypergraph candidates R) q.key) :
    ∀ q ∈ (jmcRoleSlotSystem candidates R x y rx ry).slots,
      m ≤ ((auxiliaryHypergraph candidates R).filter
        ((jmcRoleSlotSystem candidates R x y rx ry).covers q)).card := by
  intro q hq
  have hbad := jmcRole_cover_card_add_le_degree candidates R hcodeg hq
  have hdeg := hdegree q hq
  omega

theorem jmcRole_coverLower_mul_pairTotal_le_tripleTotal {n k L m : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (hcodeg : MaxCodegreeLE (auxiliaryHypergraph candidates R) 2 L)
    {x y : Fin n} {rx ry : JMCPaintRole}
    (hdegree : ∀ q ∈ (jmcRoleSlotSystem candidates R x y rx ry).slots,
      m + 16 * L ≤ degree (auxiliaryHypergraph candidates R) q.key) :
    (m : ℝ) * testTotal
        (jmcRoleSlotSystem candidates R x y rx ry).pairWeight
        (auxiliaryHypergraph candidates R) 2 ≤
      testTotal (jmcRoleSlotSystem candidates R x y rx ry).tripleWeight
        (auxiliaryHypergraph candidates R) 3 := by
  exact CrossSlotSystem.coverLower_mul_pairTotal_le_tripleTotal _ m
    (jmcRole_cover_lower candidates R hcodeg hdegree)

theorem jmcRole_key_active {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {x y : Fin n} {rx ry : JMCPaintRole} {q : JMCCrossSlot n k}
    (hq : q ∈ (jmcRoleSlotSystem candidates R x y rx ry).slots) :
    AuxConcentration.ActiveAuxVertex R q.key := by
  have hbase := (CrossSlotSystem.mem_restrict_slots.mp hq).1
  have hne := (mem_jmcCrossSlots.mp hbase).2.1
  simpa [JMCCrossSlot.key, AuxConcentration.ActiveAuxVertex,
    Sym2.mk_isDiag_iff] using hne

/-- Universal host concentration and the ambient `6n²` codegree bound
give a completely explicit cover lower bound. -/
theorem jmcRole_coverLower_mul_pairTotal_le_tripleTotal_of_host
    {n k m : ℕ} {qprob : ℝ} {R : RetainedLabels n k}
    (hhost : AuxConcentration.UniversalRetainedHostEstimates qprob R)
    (hk : k ≤ n)
    (hgap : AuxConcentration.universalHostDegreeError n k qprob <
      AuxConcentration.universalHostDegree n k qprob)
    (hcoverScale : ((m + 16 * (6 * n ^ 2) : ℕ) : ℝ) ≤
      AuxConcentration.universalHostDegree n k qprob -
        AuxConcentration.universalHostDegreeError n k qprob)
    {x y : Fin n} {rx ry : JMCPaintRole} :
    (m : ℝ) * testTotal
        (jmcRoleSlotSystem (AuxConcentration.allTriangleBlocks n k) R
          x y rx ry).pairWeight
        (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R) 2 ≤
      testTotal
        (jmcRoleSlotSystem (AuxConcentration.allTriangleBlocks n k) R
          x y rx ry).tripleWeight
        (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R) 3 := by
  apply jmcRole_coverLower_mul_pairTotal_le_tripleTotal _ R
    (AuxConcentration.universal_auxiliary_maxCodegree hk R)
  intro slot hslot
  have hactive := jmcRole_key_active
    (AuxConcentration.allTriangleBlocks n k) R hslot
  have hmem :=
    (AuxConcentration.mem_vertexFinset_iff_active_of_universalRetainedHostEstimates
      hhost hgap slot.key).2 hactive
  have hlower := hhost.2.2.2.1 slot.key hmem |>.1
  have hreal : ((m + 16 * (6 * n ^ 2) : ℕ) : ℝ) ≤
      (degree
        (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R)
        slot.key : ℝ) := hcoverScale.trans hlower.le
  exact_mod_cast hreal

/-- The retained role-witness window directly discharges W1 for a tracked
pair test once the displayed numerical lower bound is available. -/
theorem jmcRole_pairTotal_W1_of_host {n k : ℕ}
    {qprob d eta : ℝ} {R : RetainedLabels n k}
    (hhost : AuxConcentration.UniversalRetainedHostEstimates qprob R)
    (hk : k ≤ n) (a : JMCRolePairIndex n)
    (hscale : Real.rpow d (2 + eta) ≤
      AuxConcentration.pairRoleTarget k qprob
          ((auxPairRoleIndexEquiv n).symm a) -
        (AuxConcentration.universalPairRoleDeviation n
            ((auxPairRoleIndexEquiv n).symm a) +
          AuxConcentration.universalPairRoleMeanError n
            ((auxPairRoleIndexEquiv n).symm a)) -
        9 * (n : ℝ) ^ 6) :
    Real.rpow d (2 + eta) ≤
      testTotal
        (jmcRoleSlotSystem (AuxConcentration.allTriangleBlocks n k) R
          a.x a.y a.leftRole a.rightRole).pairWeight
        (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R) 2 := by
  let b := (auxPairRoleIndexEquiv n).symm a
  have hlower := universalRetainedHostEstimates_jmcRole_pairTotal_lower
    hhost b hk
  simpa [b] using hscale.trans hlower.le

/-- Combining the fresh-key cover subtraction with the pair-witness lower
window discharges W1 for the corresponding tracked triple test. -/
theorem jmcRole_tripleTotal_W1_of_host {n k m : ℕ}
    {qprob d eta : ℝ} {R : RetainedLabels n k}
    (hhost : AuxConcentration.UniversalRetainedHostEstimates qprob R)
    (hk : k ≤ n)
    (hgap : AuxConcentration.universalHostDegreeError n k qprob <
      AuxConcentration.universalHostDegree n k qprob)
    (hcoverScale : ((m + 16 * (6 * n ^ 2) : ℕ) : ℝ) ≤
      AuxConcentration.universalHostDegree n k qprob -
        AuxConcentration.universalHostDegreeError n k qprob)
    (a : JMCRolePairIndex n)
    (hscale : Real.rpow d (3 + eta) ≤ (m : ℝ) *
      (AuxConcentration.pairRoleTarget k qprob
          ((auxPairRoleIndexEquiv n).symm a) -
        (AuxConcentration.universalPairRoleDeviation n
            ((auxPairRoleIndexEquiv n).symm a) +
          AuxConcentration.universalPairRoleMeanError n
            ((auxPairRoleIndexEquiv n).symm a)) -
        9 * (n : ℝ) ^ 6)) :
    Real.rpow d (3 + eta) ≤
      testTotal
        (jmcRoleSlotSystem (AuxConcentration.allTriangleBlocks n k) R
          a.x a.y a.leftRole a.rightRole).tripleWeight
        (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R) 3 := by
  let b := (auxPairRoleIndexEquiv n).symm a
  have hp := universalRetainedHostEstimates_jmcRole_pairTotal_lower
    hhost b hk
  have hc := jmcRole_coverLower_mul_pairTotal_le_tripleTotal_of_host
    hhost hk hgap hcoverScale
    (x := b.x) (y := b.y)
    (rx := auxRootRoleEquiv b.leftRole)
    (ry := auxRootRoleEquiv b.rightRole)
  simpa [b] using hscale.trans ((mul_le_mul_of_nonneg_left hp.le
    (Nat.cast_nonneg m)).trans hc)

/-- Every auxiliary triangle block uses at most three graph-edge vertices
incident with a fixed root.  This fixed bound is what the one-uniform test
needs; the ambient `n`-bound is far too coarse for a fixed `ell`. -/
theorem graphIncidence_le_three_of_mem_auxiliaryHypergraph {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (x : Fin n) {e : Finset (AuxVertex n k)}
    (he : e ∈ auxiliaryHypergraph candidates R) :
    graphIncidence x e ≤ 3 := by
  rw [auxiliaryHypergraph, Finset.mem_image] at he
  obtain ⟨b, hb, rfl⟩ := he
  calc
    graphIncidence x b.auxSupport ≤
        (AuxConcentration.blockVertices b).card := by
      apply Finset.card_le_card
      intro y hy
      have hkey := (Finset.mem_filter.mp hy).2.2
      exact (graphAuxMem_endpoints_mem_blockVertices b x y hkey).2
    _ = 3 := by simp [AuxConcentration.blockVertices,
      b.apex_ne_left, b.apex_ne_right, b.left_ne_right]

/-- A four-edge alternating-cycle conflict cannot be contained in a family
of at most three host edges. -/
theorem no_alternatingCycleConflict_subset_of_card_le_three {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {S : Hypergraph (AuxVertex n k)} (hS : S.card ≤ 3) :
    ¬ ∃ c ∈ alternatingCycleConflicts candidates R, c ⊆ S := by
  rintro ⟨c, hc, hsub⟩
  have hc4 := alternatingCycleConflicts_uniform candidates R hc
  have hcard := Finset.card_le_card hsub
  omega

/-- Complete trackability adapter for the leave-degree test.  Only W1 is
numerical; W2 is empty at uniformity one, W3 has no distinct root pair, and
W4 follows from four-uniformity of the conflicts. -/
theorem leaveDegreeWeight_isTrackable_of_total {n k ell : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (d eta : ℝ) (hell : 3 ≤ ell) (x : Fin n)
    (htotal : Real.rpow d (1 + eta) ≤
      testTotal (leaveDegreeWeight (auxiliaryHypergraph candidates R) x)
        (auxiliaryHypergraph candidates R) 1) :
    IsTrackable (auxiliaryHypergraph candidates R)
      (alternatingCycleConflicts candidates R) 1 ell d eta
      (leaveDegreeWeight (auxiliaryHypergraph candidates R) x) := by
  refine ⟨leaveDegreeWeight_isTestFunction _ x
      (fun e he ↦ (graphIncidence_le_three_of_mem_auxiliaryHypergraph
        candidates R x he).trans hell), (by simpa using htotal), ?_, ?_, ?_⟩
  · intro j' hj' hj'lt
    omega
  · intro S hS hw e he f hf hef
    have hcard := (Finset.mem_powersetCard.mp hS).2
    obtain ⟨g, rfl⟩ := Finset.card_eq_one.mp hcard
    simp at he hf
    exact (hef (he.trans hf.symm)).elim
  · intro S hS hconf
    exact (no_alternatingCycleConflict_subset_of_card_le_three
      candidates R (by
        rw [(Finset.mem_powersetCard.mp hS).2]
        omega) hconf).elim

theorem jmcRole_pairWeight_conflict_vanishes {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (a : JMCRolePairIndex n) (S : Hypergraph (AuxVertex n k))
    (hS : S ∈ (auxiliaryHypergraph candidates R).powersetCard 2)
    (hconf : ∃ c ∈ alternatingCycleConflicts candidates R, c ⊆ S) :
    (jmcRoleSlotSystem candidates R a.x a.y a.leftRole a.rightRole).pairWeight S = 0 := by
  exact (no_alternatingCycleConflict_subset_of_card_le_three candidates R
    (by rw [(Finset.mem_powersetCard.mp hS).2]; omega) hconf).elim

theorem jmcRole_tripleWeight_conflict_vanishes {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (a : JMCRolePairIndex n) (S : Hypergraph (AuxVertex n k))
    (hS : S ∈ (auxiliaryHypergraph candidates R).powersetCard 3)
    (hconf : ∃ c ∈ alternatingCycleConflicts candidates R, c ⊆ S) :
    (jmcRoleSlotSystem candidates R a.x a.y a.leftRole a.rightRole).tripleWeight S = 0 := by
  exact (no_alternatingCycleConflict_subset_of_card_le_three candidates R
    (by rw [(Finset.mem_powersetCard.mp hS).2]) hconf).elim

inductive JMCTrackedIndex (n : ℕ)
  | leave : Fin n → JMCTrackedIndex n
  | pairRole : JMCRolePairIndex n → JMCTrackedIndex n
  | tripleRole : JMCRolePairIndex n → JMCTrackedIndex n
  deriving DecidableEq, Fintype

def jmcTestUniformity {n : ℕ} : JMCTrackedIndex n → ℕ
  | .leave _ => 1
  | .pairRole _ => 2
  | .tripleRole _ => 3

def jmcTestWeight {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k) :
    JMCTrackedIndex n → TestWeight (AuxVertex n k)
  | .leave x => leaveDegreeWeight (auxiliaryHypergraph candidates R) x
  | .pairRole a =>
      (jmcRoleSlotSystem candidates R a.x a.y a.leftRole a.rightRole).pairWeight
  | .tripleRole a =>
      (jmcRoleSlotSystem candidates R a.x a.y a.leftRole a.rightRole).tripleWeight

@[simp] theorem jmcTestUniformity_leave {n : ℕ} (x : Fin n) :
    jmcTestUniformity (JMCTrackedIndex.leave x) = 1 := rfl

@[simp] theorem jmcTestUniformity_pairRole {n : ℕ} (a : JMCRolePairIndex n) :
    jmcTestUniformity (JMCTrackedIndex.pairRole a) = 2 := rfl

@[simp] theorem jmcTestUniformity_tripleRole {n : ℕ} (a : JMCRolePairIndex n) :
    jmcTestUniformity (JMCTrackedIndex.tripleRole a) = 3 := rfl

@[simp] theorem jmcTestWeight_leave {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (x : Fin n) :
    jmcTestWeight candidates R (JMCTrackedIndex.leave x) =
      leaveDegreeWeight (auxiliaryHypergraph candidates R) x := rfl

@[simp] theorem jmcTestWeight_pairRole {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (a : JMCRolePairIndex n) :
    jmcTestWeight candidates R (JMCTrackedIndex.pairRole a) =
      (jmcRoleSlotSystem candidates R a.x a.y a.leftRole a.rightRole).pairWeight := rfl

@[simp] theorem jmcTestWeight_tripleRole {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (a : JMCRolePairIndex n) :
    jmcTestWeight candidates R (JMCTrackedIndex.tripleRole a) =
      (jmcRoleSlotSystem candidates R a.x a.y a.leftRole a.rightRole).tripleWeight := rfl

/-- A canonical integral ceiling for the common retained-host degree. -/
def jmcHostDegreeCeil (n k : ℕ) (qprob : ℝ) : ℕ :=
  ⌈AuxConcentration.universalHostDegree n k qprob⌉₊

theorem universalRetainedHostEstimates_maxDegreeLE {n k : ℕ}
    {qprob : ℝ} {R : RetainedLabels n k}
    (hhost : AuxConcentration.UniversalRetainedHostEstimates qprob R) :
    MaxDegreeLE
      (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R)
      (jmcHostDegreeCeil n k qprob) := by
  intro v
  by_cases hv : v ∈ vertexFinset
      (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R)
  · have hupper := (hhost.2.2.2.1 v hv).2
    have hceil : AuxConcentration.universalHostDegree n k qprob ≤
        (jmcHostDegreeCeil n k qprob : ℝ) := by
      exact Nat.le_ceil _
    exact_mod_cast hupper.trans hceil
  · rw [degree_eq_zero_of_not_mem_vertexFinset hv]
    exact Nat.zero_le _

/-- The remaining finite rooted-count data for the role tests.  Host totals,
cover cancellation, W3 and W4 are discharged by the consumer theorem below;
this structure isolates only the owner fibres and W2 extensions. -/
structure JMCRoleLocalTrackabilityBounds {n k ell : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (d eta : ℝ) where
  pairFiber : ∀ a : JMCRolePairIndex n, ∀ S,
    ((jmcRoleSlotSystem candidates R a.x a.y a.leftRole a.rightRole).slots.filter
      fun slot ↦ slot.owner = S).card ≤ ell
  pairExtension : ∀ a : JMCRolePairIndex n, ∀ j', 1 ≤ j' → j' < 2 →
    ∀ root, root ⊆ auxiliaryHypergraph candidates R → root.card = j' →
      testExtension
          (jmcRoleSlotSystem candidates R a.x a.y
            a.leftRole a.rightRole).pairWeight
          (auxiliaryHypergraph candidates R) 2 root ≤
        testTotal
            (jmcRoleSlotSystem candidates R a.x a.y
              a.leftRole a.rightRole).pairWeight
            (auxiliaryHypergraph candidates R) 2 /
          Real.rpow d ((j' : ℝ) + eta)
  tripleFiber : ∀ a : JMCRolePairIndex n, ∀ S,
    ((jmcRoleSlotSystem candidates R a.x a.y a.leftRole a.rightRole).coverPairs.filter
      fun qe ↦ CrossSlotSystem.extendedOwner
        (jmcRoleSlotSystem candidates R a.x a.y a.leftRole a.rightRole) qe = S).card ≤ ell
  tripleExtension : ∀ a : JMCRolePairIndex n, ∀ j', 1 ≤ j' → j' < 3 →
    ∀ root, root ⊆ auxiliaryHypergraph candidates R → root.card = j' →
      testExtension
          (jmcRoleSlotSystem candidates R a.x a.y
            a.leftRole a.rightRole).tripleWeight
          (auxiliaryHypergraph candidates R) 3 root ≤
        testTotal
            (jmcRoleSlotSystem candidates R a.x a.y
              a.leftRole a.rightRole).tripleWeight
            (auxiliaryHypergraph candidates R) 3 /
          Real.rpow d ((j' : ℝ) + eta)

/-- The local role-test bounds are forced by the retained-host degree and
paint-fibre estimates.  Only the three displayed scalar comparisons remain;
they contain no finite-family or test-extension hypotheses. -/
theorem jmcRoleLocalTrackabilityBounds_of_host {n k ell m : ℕ}
    {qprob d eta : ℝ} {R : RetainedLabels n k}
    (hhost : AuxConcentration.UniversalRetainedHostEstimates qprob R)
    (hk : k ≤ n) (hd : 0 ≤ d) (hell : 48 ≤ ell)
    (hgap : AuxConcentration.universalHostDegreeError n k qprob <
      AuxConcentration.universalHostDegree n k qprob)
    (hcoverScale : ((m + 16 * (6 * n ^ 2) : ℕ) : ℝ) ≤
      AuxConcentration.universalHostDegree n k qprob -
        AuxConcentration.universalHostDegreeError n k qprob)
    (hpairExtension : ∀ a : JMCRolePairIndex n,
      ((16 * jmcHostDegreeCeil n k qprob : ℕ) : ℝ) ≤
        (AuxConcentration.pairRoleTarget k qprob
            ((auxPairRoleIndexEquiv n).symm a) -
          (AuxConcentration.universalPairRoleDeviation n
              ((auxPairRoleIndexEquiv n).symm a) +
            AuxConcentration.universalPairRoleMeanError n
              ((auxPairRoleIndexEquiv n).symm a)) -
          9 * (n : ℝ) ^ 6) / Real.rpow d (1 + eta))
    (htripleExtensionOne : ∀ a : JMCRolePairIndex n,
      ((16 * (jmcHostDegreeCeil n k qprob) ^ 2 +
          256 * k * (6 * n ^ 2) ^ 2 : ℕ) : ℝ) ≤
        ((m : ℝ) *
          (AuxConcentration.pairRoleTarget k qprob
              ((auxPairRoleIndexEquiv n).symm a) -
            (AuxConcentration.universalPairRoleDeviation n
                ((auxPairRoleIndexEquiv n).symm a) +
              AuxConcentration.universalPairRoleMeanError n
                ((auxPairRoleIndexEquiv n).symm a)) -
            9 * (n : ℝ) ^ 6)) / Real.rpow d (1 + eta))
    (htripleExtensionTwo : ∀ a : JMCRolePairIndex n,
      ((48 * jmcHostDegreeCeil n k qprob : ℕ) : ℝ) ≤
        ((m : ℝ) *
          (AuxConcentration.pairRoleTarget k qprob
              ((auxPairRoleIndexEquiv n).symm a) -
            (AuxConcentration.universalPairRoleDeviation n
                ((auxPairRoleIndexEquiv n).symm a) +
              AuxConcentration.universalPairRoleMeanError n
                ((auxPairRoleIndexEquiv n).symm a)) -
            9 * (n : ℝ) ^ 6)) / Real.rpow d (2 + eta)) :
    JMCRoleLocalTrackabilityBounds (ell := ell)
      (AuxConcentration.allTriangleBlocks n k) R d eta := by
  let D := jmcHostDegreeCeil n k qprob
  let L := 6 * n ^ 2
  have hmax : MaxDegreeLE
      (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R) D := by
    simpa [D] using universalRetainedHostEstimates_maxDegreeLE hhost
  have hpaint : ∀ p : OrientedPaint n k,
      (paintFiber
        (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R) p).card ≤ L := by
    intro p
    exact paintFiber_card_le_of_maxCodegree
      (AuxConcentration.universal_auxiliary_maxCodegree hk R) p
  constructor
  · intro a S
    let b := (auxPairRoleIndexEquiv n).symm a
    have hb := jmcRole_pairFiber_card_le_sixteen
      (AuxConcentration.allTriangleBlocks n k) R b S
    have hb' :
        ((jmcRoleSlotSystem (AuxConcentration.allTriangleBlocks n k) R
          a.x a.y a.leftRole a.rightRole).slots.filter fun q ↦
            (jmcRoleSlotSystem (AuxConcentration.allTriangleBlocks n k) R
              a.x a.y a.leftRole a.rightRole).owner q = S).card ≤ 16 := by
      simpa [b] using hb
    exact hb'.trans (by omega)
  · intro a j' hj' hj'lt root hrootH hroot
    have hj'one : j' = 1 := by omega
    have hrootOne : root.card = 1 := hroot.trans hj'one
    let b := (auxPairRoleIndexEquiv n).symm a
    have hfinite := jmcRole_pairExtension_le_sixteen_mul_degree
      (AuxConcentration.allTriangleBlocks n k) R hmax b root hrootOne
    have hlower := universalRetainedHostEstimates_jmcRole_pairTotal_lower
      hhost b hk
    have hdiv :
        (AuxConcentration.pairRoleTarget k qprob
            ((auxPairRoleIndexEquiv n).symm a) -
          (AuxConcentration.universalPairRoleDeviation n
              ((auxPairRoleIndexEquiv n).symm a) +
            AuxConcentration.universalPairRoleMeanError n
              ((auxPairRoleIndexEquiv n).symm a)) -
          9 * (n : ℝ) ^ 6) / Real.rpow d (1 + eta) ≤
        testTotal
          (jmcRoleSlotSystem (AuxConcentration.allTriangleBlocks n k) R
            a.x a.y a.leftRole a.rightRole).pairWeight
          (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R) 2 /
            Real.rpow d (1 + eta) :=
      div_le_div_of_nonneg_right (by simpa [b] using hlower.le)
        (Real.rpow_nonneg hd _)
    have hfinite' :
        testExtension
          (jmcRoleSlotSystem (AuxConcentration.allTriangleBlocks n k) R
            a.x a.y a.leftRole a.rightRole).pairWeight
          (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R)
          2 root ≤ ((16 * D : ℕ) : ℝ) := by
      simpa [b] using hfinite
    have hscalar : ((16 * D : ℕ) : ℝ) ≤
        testTotal
          (jmcRoleSlotSystem (AuxConcentration.allTriangleBlocks n k) R
            a.x a.y a.leftRole a.rightRole).pairWeight
          (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R) 2 /
            Real.rpow d ((j' : ℝ) + eta) := by
      calc
        ((16 * D : ℕ) : ℝ) ≤
            (AuxConcentration.pairRoleTarget k qprob
                ((auxPairRoleIndexEquiv n).symm a) -
              (AuxConcentration.universalPairRoleDeviation n
                  ((auxPairRoleIndexEquiv n).symm a) +
                AuxConcentration.universalPairRoleMeanError n
                  ((auxPairRoleIndexEquiv n).symm a)) -
              9 * (n : ℝ) ^ 6) / Real.rpow d (1 + eta) := by
          simpa [D] using hpairExtension a
        _ ≤ _ := by simpa [hj'one] using hdiv
    exact hfinite'.trans hscalar
  · intro a S
    let b := (auxPairRoleIndexEquiv n).symm a
    have hb := jmcRole_tripleFiber_card_le_fortyEight
      (AuxConcentration.allTriangleBlocks n k) R b S
    have hb' :
        ((jmcRoleSlotSystem (AuxConcentration.allTriangleBlocks n k) R
          a.x a.y a.leftRole a.rightRole).coverPairs.filter fun qe ↦
            CrossSlotSystem.extendedOwner
              (jmcRoleSlotSystem (AuxConcentration.allTriangleBlocks n k) R
                a.x a.y a.leftRole a.rightRole) qe = S).card ≤ 48 := by
      simpa [b] using hb
    exact hb'.trans hell
  · intro a j' hj' hj'lt root hrootH hroot
    let b := (auxPairRoleIndexEquiv n).symm a
    have hp := universalRetainedHostEstimates_jmcRole_pairTotal_lower
      hhost b hk
    have hc := jmcRole_coverLower_mul_pairTotal_le_tripleTotal_of_host
      hhost hk hgap hcoverScale
      (x := b.x) (y := b.y)
      (rx := auxRootRoleEquiv b.leftRole)
      (ry := auxRootRoleEquiv b.rightRole)
    have hactual :
        (m : ℝ) *
          (AuxConcentration.pairRoleTarget k qprob
              ((auxPairRoleIndexEquiv n).symm a) -
            (AuxConcentration.universalPairRoleDeviation n
                ((auxPairRoleIndexEquiv n).symm a) +
              AuxConcentration.universalPairRoleMeanError n
                ((auxPairRoleIndexEquiv n).symm a)) -
            9 * (n : ℝ) ^ 6) ≤
          testTotal
            (jmcRoleSlotSystem (AuxConcentration.allTriangleBlocks n k) R
              a.x a.y a.leftRole a.rightRole).tripleWeight
            (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R) 3 := by
      simpa [b] using (mul_le_mul_of_nonneg_left hp.le
        (Nat.cast_nonneg m)).trans hc
    rcases (show j' = 1 ∨ j' = 2 by omega) with hjone | hjtwo
    · have hfinite := jmcRole_tripleExtension_rootOne_le
        (AuxConcentration.allTriangleBlocks n k) R hmax hpaint b root
          (hroot.trans hjone)
      have hdiv :
          ((m : ℝ) *
            (AuxConcentration.pairRoleTarget k qprob
                ((auxPairRoleIndexEquiv n).symm a) -
              (AuxConcentration.universalPairRoleDeviation n
                  ((auxPairRoleIndexEquiv n).symm a) +
                AuxConcentration.universalPairRoleMeanError n
                  ((auxPairRoleIndexEquiv n).symm a)) -
              9 * (n : ℝ) ^ 6)) / Real.rpow d (1 + eta) ≤
          testTotal
            (jmcRoleSlotSystem (AuxConcentration.allTriangleBlocks n k) R
              a.x a.y a.leftRole a.rightRole).tripleWeight
            (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R) 3 /
              Real.rpow d (1 + eta) :=
        div_le_div_of_nonneg_right hactual (Real.rpow_nonneg hd _)
      have hfinite' :
          testExtension
            (jmcRoleSlotSystem (AuxConcentration.allTriangleBlocks n k) R
              a.x a.y a.leftRole a.rightRole).tripleWeight
            (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R)
            3 root ≤ ((16 * D ^ 2 + 256 * k * L ^ 2 : ℕ) : ℝ) := by
        simpa [b] using hfinite
      have hscalar : ((16 * D ^ 2 + 256 * k * L ^ 2 : ℕ) : ℝ) ≤
          testTotal
            (jmcRoleSlotSystem (AuxConcentration.allTriangleBlocks n k) R
              a.x a.y a.leftRole a.rightRole).tripleWeight
            (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R) 3 /
              Real.rpow d ((j' : ℝ) + eta) := by
        calc
          ((16 * D ^ 2 + 256 * k * L ^ 2 : ℕ) : ℝ) ≤
              ((m : ℝ) *
                (AuxConcentration.pairRoleTarget k qprob
                    ((auxPairRoleIndexEquiv n).symm a) -
                  (AuxConcentration.universalPairRoleDeviation n
                      ((auxPairRoleIndexEquiv n).symm a) +
                    AuxConcentration.universalPairRoleMeanError n
                      ((auxPairRoleIndexEquiv n).symm a)) -
                  9 * (n : ℝ) ^ 6)) / Real.rpow d (1 + eta) := by
            simpa [D, L] using htripleExtensionOne a
          _ ≤ _ := by simpa [hjone] using hdiv
      exact hfinite'.trans hscalar
    · have hfinite := jmcRole_tripleExtension_rootTwo_le
        (AuxConcentration.allTriangleBlocks n k) R hmax b root
          (hroot.trans hjtwo)
      have hdiv :
          ((m : ℝ) *
            (AuxConcentration.pairRoleTarget k qprob
                ((auxPairRoleIndexEquiv n).symm a) -
              (AuxConcentration.universalPairRoleDeviation n
                  ((auxPairRoleIndexEquiv n).symm a) +
                AuxConcentration.universalPairRoleMeanError n
                  ((auxPairRoleIndexEquiv n).symm a)) -
              9 * (n : ℝ) ^ 6)) / Real.rpow d (2 + eta) ≤
          testTotal
            (jmcRoleSlotSystem (AuxConcentration.allTriangleBlocks n k) R
              a.x a.y a.leftRole a.rightRole).tripleWeight
            (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R) 3 /
              Real.rpow d (2 + eta) :=
        div_le_div_of_nonneg_right hactual (Real.rpow_nonneg hd _)
      have hfinite' :
          testExtension
            (jmcRoleSlotSystem (AuxConcentration.allTriangleBlocks n k) R
              a.x a.y a.leftRole a.rightRole).tripleWeight
            (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R)
            3 root ≤ ((48 * D : ℕ) : ℝ) := by
        simpa [b] using hfinite
      have hscalar : ((48 * D : ℕ) : ℝ) ≤
          testTotal
            (jmcRoleSlotSystem (AuxConcentration.allTriangleBlocks n k) R
              a.x a.y a.leftRole a.rightRole).tripleWeight
            (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R) 3 /
              Real.rpow d ((j' : ℝ) + eta) := by
        calc
          ((48 * D : ℕ) : ℝ) ≤
              ((m : ℝ) *
                (AuxConcentration.pairRoleTarget k qprob
                    ((auxPairRoleIndexEquiv n).symm a) -
                  (AuxConcentration.universalPairRoleDeviation n
                      ((auxPairRoleIndexEquiv n).symm a) +
                    AuxConcentration.universalPairRoleMeanError n
                      ((auxPairRoleIndexEquiv n).symm a)) -
                  9 * (n : ℝ) ^ 6)) / Real.rpow d (2 + eta) := by
            simpa [D] using htripleExtensionTwo a
          _ ≤ _ := by simpa [hjtwo] using hdiv
      exact hfinite'.trans hscalar

/-- Consumer-facing all-tests adapter.  Universal retained-host estimates
supply both role W1 bounds and, through the fresh off-diagonal key, the
pair-to-triple cover cancellation.  The common-link estimate supplies W3,
and four-uniformity supplies W4. -/
theorem all_jmcTestWeight_isTrackable_of_host {n k ell m : ℕ}
    {qprob d eta : ℝ} {R : RetainedLabels n k}
    (hhost : AuxConcentration.UniversalRetainedHostEstimates qprob R)
    (hk : k ≤ n) (hd : 0 ≤ d) (hell : 48 ≤ ell)
    (hgap : AuxConcentration.universalHostDegreeError n k qprob <
      AuxConcentration.universalHostDegree n k qprob)
    (hcoverScale : ((m + 16 * (6 * n ^ 2) : ℕ) : ℝ) ≤
      AuxConcentration.universalHostDegree n k qprob -
        AuxConcentration.universalHostDegreeError n k qprob)
    (hW3 : ((566231040 * n ^ 8 : ℕ) : ℝ) ≤
      Real.rpow d (3 - eta))
    (hleave : ∀ x : Fin n, Real.rpow d (1 + eta) ≤
      testTotal
        (leaveDegreeWeight
          (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R) x)
        (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R) 1)
    (hpair : ∀ a : JMCRolePairIndex n, Real.rpow d (2 + eta) ≤
      AuxConcentration.pairRoleTarget k qprob
          ((auxPairRoleIndexEquiv n).symm a) -
        (AuxConcentration.universalPairRoleDeviation n
            ((auxPairRoleIndexEquiv n).symm a) +
          AuxConcentration.universalPairRoleMeanError n
            ((auxPairRoleIndexEquiv n).symm a)) -
        9 * (n : ℝ) ^ 6)
    (htriple : ∀ a : JMCRolePairIndex n, Real.rpow d (3 + eta) ≤
      (m : ℝ) *
        (AuxConcentration.pairRoleTarget k qprob
            ((auxPairRoleIndexEquiv n).symm a) -
          (AuxConcentration.universalPairRoleDeviation n
              ((auxPairRoleIndexEquiv n).symm a) +
            AuxConcentration.universalPairRoleMeanError n
              ((auxPairRoleIndexEquiv n).symm a)) -
          9 * (n : ℝ) ^ 6))
    (hpairExtension : ∀ a : JMCRolePairIndex n,
      ((16 * jmcHostDegreeCeil n k qprob : ℕ) : ℝ) ≤
        (AuxConcentration.pairRoleTarget k qprob
            ((auxPairRoleIndexEquiv n).symm a) -
          (AuxConcentration.universalPairRoleDeviation n
              ((auxPairRoleIndexEquiv n).symm a) +
            AuxConcentration.universalPairRoleMeanError n
              ((auxPairRoleIndexEquiv n).symm a)) -
          9 * (n : ℝ) ^ 6) / Real.rpow d (1 + eta))
    (htripleExtensionOne : ∀ a : JMCRolePairIndex n,
      ((16 * (jmcHostDegreeCeil n k qprob) ^ 2 +
          256 * k * (6 * n ^ 2) ^ 2 : ℕ) : ℝ) ≤
        ((m : ℝ) *
          (AuxConcentration.pairRoleTarget k qprob
              ((auxPairRoleIndexEquiv n).symm a) -
            (AuxConcentration.universalPairRoleDeviation n
                ((auxPairRoleIndexEquiv n).symm a) +
              AuxConcentration.universalPairRoleMeanError n
                ((auxPairRoleIndexEquiv n).symm a)) -
            9 * (n : ℝ) ^ 6)) / Real.rpow d (1 + eta))
    (htripleExtensionTwo : ∀ a : JMCRolePairIndex n,
      ((48 * jmcHostDegreeCeil n k qprob : ℕ) : ℝ) ≤
        ((m : ℝ) *
          (AuxConcentration.pairRoleTarget k qprob
              ((auxPairRoleIndexEquiv n).symm a) -
            (AuxConcentration.universalPairRoleDeviation n
                ((auxPairRoleIndexEquiv n).symm a) +
              AuxConcentration.universalPairRoleMeanError n
                ((auxPairRoleIndexEquiv n).symm a)) -
            9 * (n : ℝ) ^ 6)) / Real.rpow d (2 + eta)) :
    ∀ i : JMCTrackedIndex n,
      IsTrackable
        (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R)
        (alternatingCycleConflicts
          (AuxConcentration.allTriangleBlocks n k) R)
        (jmcTestUniformity i) ell d eta
        (jmcTestWeight (AuxConcentration.allTriangleBlocks n k) R i) := by
  have hlocal := jmcRoleLocalTrackabilityBounds_of_host hhost hk hd hell
    hgap hcoverScale hpairExtension
    htripleExtensionOne htripleExtensionTwo
  have hell3 : 3 ≤ ell := by omega
  intro i
  cases i with
  | leave x =>
      exact leaveDegreeWeight_isTrackable_of_total _ R d eta hell3 x (hleave x)
  | pairRole a =>
      apply CrossSlotSystem.pairWeight_isTrackable_of_host_bounds
        _ R _ ell d eta hd hk hW3
        (hlocal.pairFiber a)
        (jmcRole_pairTotal_W1_of_host hhost hk a (hpair a))
        (hlocal.pairExtension a)
      intro S hS hconf
      exact jmcRole_pairWeight_conflict_vanishes _ R a S hS hconf
  | tripleRole a =>
      apply CrossSlotSystem.tripleWeight_isTrackable_of_host_bounds
        _ R _ ell d eta hd hk hW3
        (hlocal.tripleFiber a)
        (jmcRole_tripleTotal_W1_of_host hhost hk hgap hcoverScale a (htriple a))
        (hlocal.tripleExtension a)
      intro S hS hconf
      exact jmcRole_tripleWeight_conflict_vanishes _ R a S hS hconf

/-- The inverse witness map also gives a uniform tracked-pair upper bound:
each retained role witness has at most eight oriented slots. -/
theorem jmcRole_pairTotal_upper_of_host {n k : ℕ}
    {qprob : ℝ} {R : RetainedLabels n k}
    (hhost : AuxConcentration.UniversalRetainedHostEstimates qprob R)
    (a : AuxConcentration.PairRoleIndex n) :
    testTotal
        (jmcRoleSlotSystem (AuxConcentration.allTriangleBlocks n k) R
          a.x a.y (auxRootRoleEquiv a.leftRole)
          (auxRootRoleEquiv a.rightRole)).pairWeight
        (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R) 2 ≤
      8 * (AuxConcentration.pairRoleTarget k qprob a +
        (AuxConcentration.universalPairRoleDeviation n a +
          AuxConcentration.universalPairRoleMeanError n a)) := by
  have hraw := jmcRole_pairTotal_le_eight_mul_pairRoleWitnesses_card
    (AuxConcentration.allTriangleBlocks n k) R a
  have hwindow := hhost.2.2.1 a a.x_ne_y
  have hupper :
      ((AuxConcentration.pairRoleWitnesses
        (AuxConcentration.allTriangleBlocks n k) R a).card : ℝ) ≤
        AuxConcentration.pairRoleTarget k qprob a +
          (AuxConcentration.universalPairRoleDeviation n a +
            AuxConcentration.universalPairRoleMeanError n a) := by
    rw [abs_lt] at hwindow
    linarith [hwindow.2]
  exact hraw.trans (mul_le_mul_of_nonneg_left hupper (by norm_num))

/-- Host residual bounds for the corrected nine-family role split. -/
structure RoleTrackedHostBounds {n k : ℕ}
    (B : ℕ) (candidates : Finset (TriangleBlock n k))
    (R : RetainedLabels n k) (d err : ℝ) where
  leave : ∀ x,
    (n - 1 : ℕ) - (1 - err) * Real.rpow d (-1 : ℝ) *
      testTotal (leaveDegreeWeight (auxiliaryHypergraph candidates R) x)
        (auxiliaryHypergraph candidates R) 1 ≤ B
  cross : ∀ a : JMCDistinctRootPair n,
    (∑ rx : JMCPaintRole, ∑ ry : JMCPaintRole,
      ((1 + err) * Real.rpow d (-2 : ℝ) *
          testTotal (jmcRoleSlotSystem candidates R a.x a.y rx ry).pairWeight
            (auxiliaryHypergraph candidates R) 2 -
        (1 - err) * Real.rpow d (-3 : ℝ) *
          testTotal (jmcRoleSlotSystem candidates R a.x a.y rx ry).tripleWeight
            (auxiliaryHypergraph candidates R) 3)) ≤ B

/-- Concentration plus fresh-key cover cancellation reduce every role
residual to a closed scalar inequality.  This is the consumer adapter used
to discharge `RoleTrackedHostBounds`; no unproved combinatorial estimate is
hidden in its conclusion. -/
theorem roleTrackedHostBounds_of_universalHost {n k m B : ℕ}
    {qprob d err : ℝ} {R : RetainedLabels n k}
    (hhost : AuxConcentration.UniversalRetainedHostEstimates qprob R)
    (hk : k ≤ n) (hd : 0 ≤ d) (herr : err ≤ 1)
    (hgap : AuxConcentration.universalHostDegreeError n k qprob <
      AuxConcentration.universalHostDegree n k qprob)
    (hcoverScale : ((m + 16 * (6 * n ^ 2) : ℕ) : ℝ) ≤
      AuxConcentration.universalHostDegree n k qprob -
        AuxConcentration.universalHostDegreeError n k qprob)
    (hleave : ∀ x : Fin n,
      (n - 1 : ℕ) - (1 - err) * Real.rpow d (-1 : ℝ) *
        testTotal
          (leaveDegreeWeight
            (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R) x)
          (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R) 1 ≤ B)
    (hcoeff : ∀ (a : JMCDistinctRootPair n) (rx ry : JMCPaintRole),
      0 ≤
        (1 + err) * Real.rpow d (-2 : ℝ) -
          (1 - err) * Real.rpow d (-3 : ℝ) * (m : ℝ))
    (hcross : ∀ a : JMCDistinctRootPair n,
      (∑ rx : JMCPaintRole, ∑ ry : JMCPaintRole,
        let b := (auxPairRoleIndexEquiv n).symm (a.withRoles rx ry)
        (((1 + err) * Real.rpow d (-2 : ℝ) -
              (1 - err) * Real.rpow d (-3 : ℝ) * (m : ℝ)) *
          (8 * (AuxConcentration.pairRoleTarget k qprob b +
            (AuxConcentration.universalPairRoleDeviation n b +
              AuxConcentration.universalPairRoleMeanError n b))))) ≤ B) :
    RoleTrackedHostBounds B
      (AuxConcentration.allTriangleBlocks n k) R d err := by
  constructor
  · exact hleave
  · intro a
    apply le_trans (Finset.sum_le_sum fun rx _ ↦
      Finset.sum_le_sum fun ry _ ↦ ?_) (hcross a)
    let b := (auxPairRoleIndexEquiv n).symm (a.withRoles rx ry)
    let P := testTotal
      (jmcRoleSlotSystem (AuxConcentration.allTriangleBlocks n k) R
        a.x a.y rx ry).pairWeight
      (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R) 2
    let T := testTotal
      (jmcRoleSlotSystem (AuxConcentration.allTriangleBlocks n k) R
        a.x a.y rx ry).tripleWeight
      (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R) 3
    let U := 8 * (AuxConcentration.pairRoleTarget k qprob b +
      (AuxConcentration.universalPairRoleDeviation n b +
        AuxConcentration.universalPairRoleMeanError n b))
    let A := (1 + err) * Real.rpow d (-2 : ℝ)
    let C := (1 - err) * Real.rpow d (-3 : ℝ)
    let K := A - C * (m : ℝ)
    have hp : P ≤ U := by
      have hu := jmcRole_pairTotal_upper_of_host hhost b
      simpa [b, P, U, JMCDistinctRootPair.withRoles] using hu
    have ht : (m : ℝ) * P ≤ T := by
      have hc := jmcRole_coverLower_mul_pairTotal_le_tripleTotal_of_host
        hhost hk hgap hcoverScale
        (x := b.x) (y := b.y)
        (rx := auxRootRoleEquiv b.leftRole)
        (ry := auxRootRoleEquiv b.rightRole)
      simpa [b, P, T, JMCDistinctRootPair.withRoles] using hc
    have hC : 0 ≤ C := by
      dsimp [C]
      exact mul_nonneg (sub_nonneg.mpr herr) (Real.rpow_nonneg hd _)
    have hK : 0 ≤ K := by
      simpa [K, A, C] using hcoeff a rx ry
    change A * P - C * T ≤ K * U
    calc
      A * P - C * T ≤ A * P - C * ((m : ℝ) * P) :=
        sub_le_sub_left (mul_le_mul_of_nonneg_left ht hC) _
      _ = K * P := by simp [K]; ring
      _ ≤ K * U := mul_le_mul_of_nonneg_left hp hK

/-- The role-complete terminal-estimate adapter.  Every singleton or mixed
P5 arm is controlled by its own pair/triple test and the nine residuals are
summed before applying the natural leave bound. -/
theorem jmcRoleTestsControlLeave_of_trackedBounds {n k B : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (d eta : ℝ)
    (hbounds : RoleTrackedHostBounds B candidates R d
      (Real.rpow d (-(eta ^ 3)))) :
    TestsControlLeave B candidates R d eta jmcTestUniformity
      (jmcTestWeight candidates R) := by
  intro MH hmatch hest
  let BM := blocksOfAuxFamily candidates R MH hmatch.1
  constructor
  · intro x
    have hterminal := (hest (JMCTrackedIndex.leave x)).1
    rw [jmcTestUniformity_leave, jmcTestWeight_leave] at hterminal
    norm_num only [Nat.cast_ofNat] at hterminal
    have hb := hbounds.leave x
    have hexact := leaveDegree_eq_sub_testTotal candidates R hmatch x
    have hreal : (leaveDegree (inducedColor BM) x : ℝ) ≤ (B : ℝ) := by
      dsimp [BM]
      rw [hexact]
      exact le_trans (sub_le_sub_left hterminal _) hb
    exact_mod_cast hreal
  · intro x y hxy
    have hterminal :
        (∑ rx : JMCPaintRole, ∑ ry : JMCPaintRole,
          (testTotal (jmcRoleSlotSystem candidates R x y rx ry).pairWeight MH 2 -
            testTotal (jmcRoleSlotSystem candidates R x y rx ry).tripleWeight MH 3)) ≤
          ∑ rx : JMCPaintRole, ∑ ry : JMCPaintRole,
            ((1 + Real.rpow d (-(eta ^ 3))) * Real.rpow d (-2 : ℝ) *
                testTotal (jmcRoleSlotSystem candidates R x y rx ry).pairWeight
                  (auxiliaryHypergraph candidates R) 2 -
              (1 - Real.rpow d (-(eta ^ 3))) * Real.rpow d (-3 : ℝ) *
                testTotal (jmcRoleSlotSystem candidates R x y rx ry).tripleWeight
                  (auxiliaryHypergraph candidates R) 3) := by
      apply Finset.sum_le_sum
      intro rx hrx
      apply Finset.sum_le_sum
      intro ry hry
      let a : JMCRolePairIndex n :=
        (JMCDistinctRootPair.mk x y hxy).withRoles rx ry
      have hp := (hest (JMCTrackedIndex.pairRole a)).2
      have ht := (hest (JMCTrackedIndex.tripleRole a)).1
      rw [jmcTestUniformity_pairRole, jmcTestWeight_pairRole] at hp
      rw [jmcTestUniformity_tripleRole, jmcTestWeight_tripleRole] at ht
      change
        testTotal (jmcRoleSlotSystem candidates R x y rx ry).pairWeight MH 2 ≤
          (1 + Real.rpow d (-(eta ^ 3))) * Real.rpow d (-2 : ℝ) *
            testTotal (jmcRoleSlotSystem candidates R x y rx ry).pairWeight
              (auxiliaryHypergraph candidates R) 2 at hp
      change
        (1 - Real.rpow d (-(eta ^ 3))) * Real.rpow d (-3 : ℝ) *
            testTotal (jmcRoleSlotSystem candidates R x y rx ry).tripleWeight
              (auxiliaryHypergraph candidates R) 3 ≤
          testTotal (jmcRoleSlotSystem candidates R x y rx ry).tripleWeight MH 3 at ht
      exact sub_le_sub hp ht
    have hobs := crossObstructions_cast_le_sum_roleTests
      candidates R hmatch hxy
    have hb := hbounds.cross (JMCDistinctRootPair.mk x y hxy)
    have hreal : ((crossObstructions (inducedColor BM) x y).card : ℝ) ≤
        (B : ℝ) := by
      dsimp [BM] at hobs ⊢
      exact hobs.trans (hterminal.trans hb)
    exact_mod_cast hreal

end

end Erdos136
