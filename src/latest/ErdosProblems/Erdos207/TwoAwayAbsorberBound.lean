/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FamilyTwoAwayWeight
import ErdosProblems.Erdos207.RootedThreatWellSpread

/-!
# Two-away extension bounds for absorber-induced forbidden families

For a fixed proposed triangle `U`, the configurations which can delete a
second triangle split into orders at least five and order four.  The first
part is injected into the fixed-size absorber-induced families and is
controlled by A2.  The order-four part is simply a triangle sharing a pair
with `U`.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- A two-away witness coming from an Erdős configuration of order at least
five, expressed by membership in the corresponding indexed outside family. -/
def IsIndexedTwoAwayThreatWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) (U : TripleOn V)
    (z : TwoAwayThreatWitness V
      (absorberErdosForbiddenConfigurationsOn q B) U) : Prop :=
  z.1.1 ∈ absorberInducedConfigurationsOn q (z.1.1.card + 2) B

abbrev IndexedTwoAwayThreatWitness
    (V : Type*) [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) (U : TripleOn V) :=
  {z : TwoAwayThreatWitness V
      (absorberErdosForbiddenConfigurationsOn q B) U //
    IsIndexedTwoAwayThreatWitness q B U z}

noncomputable instance instDecidablePredIsIndexedTwoAwayThreatWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) (U : TripleOn V) :
    DecidablePred (IsIndexedTwoAwayThreatWitness q B U) :=
  Classical.decPred _

lemma indexedTwoAwayThreat_order_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : TripleOn V}
    (z : IndexedTwoAwayThreatWitness V q B U) :
    z.1.1.1.card + 2 ∈ Icc 3 q := by
  have hnonempty :=
    (mem_absorberErdosForbiddenConfigurationsOn_iff.mp z.1.2.1).1
  obtain ⟨hScard, r, hr5, hrq, E, hE, hEout⟩ :=
    mem_absorberInducedConfigurationsOn_iff.mp z.2
  have hSsubE : z.1.1.1 ⊆ E := by
    intro T hTS
    exact (mem_sdiff.mp (by rw [hEout]; exact hTS)).1
  have hc := card_le_card hSsubE
  rw [hE.1.1] at hc
  apply mem_Icc.mpr
  constructor
  · rw [nonempty_iff_ne_empty] at hnonempty
    have hpos := card_pos.mpr (nonempty_iff_ne_empty.mpr hnonempty)
    omega
  · omega

/-- The indexed order and its fixed-size two-away witness. -/
abbrev IndexedTwoAwayThreatCode
    (V : Type*) [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) (U : TripleOn V) :=
  Σ j : IndexedThreatOrder q,
    FamilyTwoAwayWitness (absorberInducedConfigurationsOn q j.1 B) U

def indexedTwoAwayThreatCode
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : TripleOn V}
    (z : IndexedTwoAwayThreatWitness V q B U) :
    IndexedTwoAwayThreatCode V q B U :=
  ⟨⟨z.1.1.1.card + 2, indexedTwoAwayThreat_order_mem z⟩,
    { family := z.1.1.1
      family_mem := z.2
      fixed_mem := z.1.2.2.2.1
      missing := z.1.1.2
      missing_mem := z.1.2.2.1
      missing_ne := z.1.2.2.2.2 }⟩

lemma indexedTwoAwayThreatCode_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : TripleOn V} :
    Function.Injective
      (indexedTwoAwayThreatCode :
        IndexedTwoAwayThreatWitness V q B U →
          IndexedTwoAwayThreatCode V q B U) := by
  intro z w hzw
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun c ↦ c.2.family) hzw
  · exact congrArg (fun c ↦ c.2.missing) hzw

def indexedTwoAwayThreatCodeWeight
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : TripleOn V}
    (p : TripleOn V → ℝ≥0) (A : TripleSystemOn V)
    (c : IndexedTwoAwayThreatCode V q B U) : ℝ≥0 :=
  if A ⊆ familyTwoAwayRemainder c.2 then
    setWeight p (familyTwoAwayRemainder c.2 \ A)
  else 0

theorem indexedTwoAwayThreat_weight_le_code
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : TripleOn V}
    (p : TripleOn V → ℝ≥0) (A : TripleSystemOn V) :
    (∑ z : IndexedTwoAwayThreatWitness V q B U,
      if A ⊆ twoAwayThreatRemainder z.1 then
        setWeight p (twoAwayThreatRemainder z.1 \ A)
      else 0) ≤
      ∑ c : IndexedTwoAwayThreatCode V q B U,
        indexedTwoAwayThreatCodeWeight p A c := by
  apply sum_le_sum_of_injective_code indexedTwoAwayThreatCode
    indexedTwoAwayThreatCode_injective
  intro z
  rfl

theorem sum_indexedTwoAwayThreatCodeWeight_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : TripleOn V}
    (p : TripleOn V → ℝ≥0) (A : TripleSystemOn V) :
    (∑ c : IndexedTwoAwayThreatCode V q B U,
      indexedTwoAwayThreatCodeWeight p A c) =
      ∑ j : IndexedThreatOrder q,
        extensionWeight
          (fun z : FamilyTwoAwayWitness
            (absorberInducedConfigurationsOn q j.1 B) U ↦
              familyTwoAwayRemainder z)
          p A := by
  unfold IndexedTwoAwayThreatCode
  rw [Fintype.sum_sigma]
  rfl

lemma card_indexedThreatOrder_le (q : ℕ) :
    Fintype.card (IndexedThreatOrder q) ≤ q + 1 := by
  change Fintype.card ↥(Icc 3 q) ≤ q + 1
  rw [Fintype.card_coe]
  calc
    (Icc 3 q).card ≤ (range (q + 1)).card := by
      apply card_le_card
      intro j hj
      simp only [mem_Icc] at hj
      simp
      omega
    _ = q + 1 := card_range _

/-- Uniformize the two-away estimate for one indexed outside-size class. -/
theorem extensionWeight_familyTwoAway_absorberInduced_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V} {U : TripleOn V}
    (hA2 : HasAbsorberLocalization q M H X B)
    (A : TripleSystemOn V) (j : IndexedThreatOrder q) :
    extensionWeight
        (fun z : FamilyTwoAwayWitness
          (absorberInducedConfigurationsOn q j.1 B) U ↦
            familyTwoAwayRemainder z)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) A ≤
      ((q * (Fintype.card V + 1) *
        refinedIndexedAbsorberBudget q M H X B : ℕ) : ℝ≥0) := by
  have htwo := extensionWeight_familyTwoAway_le_enlargedRoot
    (G := absorberInducedConfigurationsOn q j.1 B) (U := U)
    (m := j.1 - 2) absorberInducedConfigurationsOn_fixed_card A
  have hbase := extensionWeight_indexed_insert_le_refinedBudget
    hA2 U A j
  have hjq : j.1 - 2 ≤ q := by
    have := (mem_Icc.mp j.2).2
    omega
  calc
    extensionWeight
        (fun z : FamilyTwoAwayWitness
          (absorberInducedConfigurationsOn q j.1 B) U ↦
            familyTwoAwayRemainder z)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) A ≤
      (((j.1 - 2) * (Fintype.card V + 1) : ℕ) : ℝ≥0) *
        extensionWeight
          (fun S : absorberInducedConfigurationsOn q j.1 B ↦ S.1)
          (constantTripleWeight
            ((Fintype.card V + 1 : ℝ≥0)⁻¹)) (insert U A) := htwo
    _ ≤ (((j.1 - 2) * (Fintype.card V + 1) : ℕ) : ℝ≥0) *
        (refinedIndexedAbsorberBudget q M H X B : ℕ) := by
      simpa only [mul_comm] using mul_le_mul_left hbase
        (((j.1 - 2) * (Fintype.card V + 1) : ℕ) : ℝ≥0)
    _ ≤ ((q * (Fintype.card V + 1) *
        refinedIndexedAbsorberBudget q M H X B : ℕ) : ℝ≥0) := by
      exact_mod_cast Nat.mul_le_mul_right
        (refinedIndexedAbsorberBudget q M H X B)
        (Nat.mul_le_mul_right (Fintype.card V + 1) hjq)

/-- The order-at-least-five two-away witnesses have linear ambient extension
weight.  The extra factor `|V|+1` is exactly the price of designating the
second missing triangle. -/
theorem extensionWeight_indexedTwoAwayThreat_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V} {U : TripleOn V}
    (hA2 : HasAbsorberLocalization q M H X B)
    (A : TripleSystemOn V) :
    extensionWeight
        (fun z : IndexedTwoAwayThreatWitness V q B U ↦
          twoAwayThreatRemainder z.1)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) A ≤
      (((q + 1) * q * (Fintype.card V + 1) *
        refinedIndexedAbsorberBudget q M H X B : ℕ) : ℝ≥0) := by
  rw [show extensionWeight
      (fun z : IndexedTwoAwayThreatWitness V q B U ↦
        twoAwayThreatRemainder z.1)
      (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) A =
      ∑ z : IndexedTwoAwayThreatWitness V q B U,
        if A ⊆ twoAwayThreatRemainder z.1 then
          setWeight
            (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹))
            (twoAwayThreatRemainder z.1 \ A)
        else 0 by rfl]
  calc
    (∑ z : IndexedTwoAwayThreatWitness V q B U,
        if A ⊆ twoAwayThreatRemainder z.1 then
          setWeight
            (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹))
            (twoAwayThreatRemainder z.1 \ A)
        else 0) ≤
      ∑ c : IndexedTwoAwayThreatCode V q B U,
        indexedTwoAwayThreatCodeWeight
          (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) A c :=
      indexedTwoAwayThreat_weight_le_code _ _
    _ = ∑ j : IndexedThreatOrder q,
        extensionWeight
          (fun z : FamilyTwoAwayWitness
            (absorberInducedConfigurationsOn q j.1 B) U ↦
              familyTwoAwayRemainder z)
          (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) A :=
      sum_indexedTwoAwayThreatCodeWeight_eq _ _
    _ ≤ ∑ _j : IndexedThreatOrder q,
        ((q * (Fintype.card V + 1) *
          refinedIndexedAbsorberBudget q M H X B : ℕ) : ℝ≥0) := by
      apply sum_le_sum
      intro j _hj
      exact extensionWeight_familyTwoAway_absorberInduced_le hA2 A j
    _ ≤ ((q + 1 : ℕ) : ℝ≥0) *
        ((q * (Fintype.card V + 1) *
          refinedIndexedAbsorberBudget q M H X B : ℕ) : ℝ≥0) := by
      rw [sum_const, nsmul_eq_mul]
      rw [card_univ]
      have hcard : (Fintype.card (IndexedThreatOrder q) : ℝ≥0) ≤
          ((q + 1 : ℕ) : ℝ≥0) := by
        exact_mod_cast card_indexedThreatOrder_le q
      simpa only [mul_comm] using mul_le_mul_left
        hcard
        ((q * (Fintype.card V + 1) *
          refinedIndexedAbsorberBudget q M H X B : ℕ) : ℝ≥0)
    _ = (((q + 1) * q * (Fintype.card V + 1) *
        refinedIndexedAbsorberBudget q M H X B : ℕ) : ℝ≥0) := by
      push_cast
      ring

/-! ## Order-four two-away witnesses -/

abbrev FourTwoAwayThreatWitness
    (V : Type*) [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) (U : TripleOn V) :=
  {z : TwoAwayThreatWitness V
      (absorberErdosForbiddenConfigurationsOn q B) U //
    ¬ IsIndexedTwoAwayThreatWitness q B U z}

lemma fourTwoAwayThreat_order_four_data
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : TripleOn V}
    (z : FourTwoAwayThreatWitness V q B U) :
    ∃ E : TripleSystemOn V,
      IsErdosConfigOn 4 E ∧ E \ B = z.1.1.1 := by
  obtain ⟨_hne, r, hr4, hrq, E, hE, _hEpacking, hEout⟩ :=
    mem_absorberErdosForbiddenConfigurationsOn_iff.mp z.1.2.1
  have hr : r = 4 := by
    by_contra hrne
    have hr5 : 5 ≤ r := by omega
    apply z.2
    apply mem_absorberInducedConfigurationsOn_iff.mpr
    exact ⟨by omega, r, hr5, hrq, E, hE, hEout⟩
  subst r
  exact ⟨E, hE, hEout⟩

/-- In order four, the outside family containing the two designated
triangles is exactly that pair. -/
lemma fourTwoAwayThreat_family_eq_pair
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : TripleOn V}
    (z : FourTwoAwayThreatWitness V q B U) :
    z.1.1.1 = {z.1.1.2, U} := by
  obtain ⟨E, hE, hEout⟩ := fourTwoAwayThreat_order_four_data z
  have hCsubE : z.1.1.1 ⊆ E := by
    rw [← hEout]
    exact sdiff_subset
  have hCcard : z.1.1.1.card ≤ 2 := by
    have := card_le_card hCsubE
    rw [hE.1.1] at this
    omega
  have hpairsub : ({z.1.1.2, U} : TripleSystemOn V) ⊆ z.1.1.1 := by
    intro T hT
    simp only [mem_insert, mem_singleton] at hT
    rcases hT with rfl | rfl
    · exact z.1.2.2.1
    · exact z.1.2.2.2.1
  have hpaircard : ({z.1.1.2, U} : TripleSystemOn V).card = 2 := by
    exact card_pair z.1.2.2.2.2
  have heq : ({z.1.1.2, U} : TripleSystemOn V) = z.1.1.1 :=
    eq_of_subset_of_card_le hpairsub (by omega)
  exact heq.symm

lemma fourTwoAwayThreat_remainder_eq_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : TripleOn V}
    (z : FourTwoAwayThreatWitness V q B U) :
    twoAwayThreatRemainder z.1 = ∅ := by
  rw [twoAwayThreatRemainder, fourTwoAwayThreat_family_eq_pair z]
  simp [z.1.2.2.2.2]

lemma fourTwoAwayThreat_missing_shares_pair
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : TripleOn V}
    (z : FourTwoAwayThreatWitness V q B U) :
    z.1.1.2 ∈ triplesSharingPair U := by
  obtain ⟨E, hE, hEout⟩ := fourTwoAwayThreat_order_four_data z
  have hCsubE : z.1.1.1 ⊆ E := by
    rw [← hEout]
    exact sdiff_subset
  apply mem_triplesSharingPair_iff.mpr
  exact four_erdos_pair_inter_card hE
    (hCsubE z.1.2.2.2.1) (hCsubE z.1.2.2.1)
      z.1.2.2.2.2.symm

def fourTwoAwayThreatCode
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : TripleOn V}
    (z : FourTwoAwayThreatWitness V q B U) :
    {T : TripleOn V // T ∈ triplesSharingPair U} :=
  ⟨z.1.1.2, fourTwoAwayThreat_missing_shares_pair z⟩

lemma fourTwoAwayThreatCode_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : TripleOn V} :
    Function.Injective
      (fourTwoAwayThreatCode : FourTwoAwayThreatWitness V q B U →
        {T : TripleOn V // T ∈ triplesSharingPair U}) := by
  intro z w hzw
  have hmissing : z.1.1.2 = w.1.1.2 := congrArg Subtype.val hzw
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · rw [fourTwoAwayThreat_family_eq_pair z,
      fourTwoAwayThreat_family_eq_pair w, hmissing]
  · exact hmissing

noncomputable def fourTwoAwayThreatEmbedding
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : TripleOn V} :
    FourTwoAwayThreatWitness V q B U ↪
      {T : TripleOn V // T ∈ triplesSharingPair U} :=
  ⟨fourTwoAwayThreatCode, fourTwoAwayThreatCode_injective⟩

lemma card_fourTwoAwayThreatWitness_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : TripleOn V} :
    Fintype.card (FourTwoAwayThreatWitness V q B U) ≤
      3 * Fintype.card V := by
  calc
    Fintype.card (FourTwoAwayThreatWitness V q B U) ≤
        Fintype.card {T : TripleOn V // T ∈ triplesSharingPair U} :=
      Fintype.card_le_of_embedding fourTwoAwayThreatEmbedding
    _ = (triplesSharingPair U).card := Fintype.card_coe _
    _ ≤ 3 * Fintype.card V := card_triplesSharingPair_le V U

/-- Order-four two-away extension weight is at most `3|V|`; its remainder
is empty, so no probabilistic weight is lost. -/
theorem extensionWeight_fourTwoAwayThreat_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : TripleOn V}
    (A : TripleSystemOn V) :
    extensionWeight
        (fun z : FourTwoAwayThreatWitness V q B U ↦
          twoAwayThreatRemainder z.1)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) A ≤
      ((3 * Fintype.card V : ℕ) : ℝ≥0) := by
  unfold extensionWeight
  simp_rw [fourTwoAwayThreat_remainder_eq_empty]
  by_cases hA : A = ∅
  · subst A
    have hcard :
        (Fintype.card (FourTwoAwayThreatWitness V q B U) : ℝ≥0) ≤
          ((3 * Fintype.card V : ℕ) : ℝ≥0) := by
      exact_mod_cast card_fourTwoAwayThreatWitness_le
    simpa [setWeight] using hcard
  · have hnsub : ¬ A ⊆ (∅ : TripleSystemOn V) := by
      intro hsub
      exact hA (subset_empty.mp hsub)
    simp [hnsub]

/-! ## Recombination -/

theorem extensionWeight_twoAway_eq_indexed_add_four
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : TripleOn V}
    (p : TripleOn V → ℝ≥0) (A : TripleSystemOn V) :
    extensionWeight
        (fun z : TwoAwayThreatWitness V
            (absorberErdosForbiddenConfigurationsOn q B) U ↦
          twoAwayThreatRemainder z)
        p A =
      extensionWeight
        (fun z : IndexedTwoAwayThreatWitness V q B U ↦
          twoAwayThreatRemainder z.1)
        p A +
      extensionWeight
        (fun z : FourTwoAwayThreatWitness V q B U ↦
          twoAwayThreatRemainder z.1)
        p A := by
  classical
  unfold extensionWeight
  symm
  simpa using Fintype.sum_subtype_add_sum_subtype
    (IsIndexedTwoAwayThreatWitness q B U)
    (fun z ↦ if A ⊆ twoAwayThreatRemainder z then
      setWeight p (twoAwayThreatRemainder z \ A) else 0)

noncomputable def twoAwayThreatExtensionCoefficient
    {V : Type*} [Fintype V] [DecidableEq V]
    (q M : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) : ℕ :=
  (q + 1) * q * (Fintype.card V + 1) *
      refinedIndexedAbsorberBudget q M H X B +
    3 * Fintype.card V

/-- A2 supplies the complete extension bound for every fixed proposed
triangle's two-away deletion family. -/
theorem absorberTwoAwayThreatRemainder_hasExtensionBound
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V} {U : TripleOn V}
    (hA2 : HasAbsorberLocalization q M H X B) :
    HasExtensionBound
      (fun z : TwoAwayThreatWitness V
          (absorberErdosForbiddenConfigurationsOn q B) U ↦
        twoAwayThreatRemainder z)
      (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹))
      (twoAwayThreatExtensionCoefficient q M H X B : ℕ) := by
  intro A
  rw [extensionWeight_twoAway_eq_indexed_add_four]
  calc
    extensionWeight
        (fun z : IndexedTwoAwayThreatWitness V q B U ↦
          twoAwayThreatRemainder z.1)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) A +
      extensionWeight
        (fun z : FourTwoAwayThreatWitness V q B U ↦
          twoAwayThreatRemainder z.1)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) A ≤
      (((q + 1) * q * (Fintype.card V + 1) *
          refinedIndexedAbsorberBudget q M H X B : ℕ) : ℝ≥0) +
        ((3 * Fintype.card V : ℕ) : ℝ≥0) :=
      add_le_add (extensionWeight_indexedTwoAwayThreat_le hA2 A)
        (extensionWeight_fourTwoAwayThreat_le A)
    _ = (twoAwayThreatExtensionCoefficient q M H X B : ℕ) := by
      simp [twoAwayThreatExtensionCoefficient]

end

end Erdos207
