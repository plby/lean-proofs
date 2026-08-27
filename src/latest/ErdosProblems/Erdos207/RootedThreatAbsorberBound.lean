/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PairTriangleCount
import ErdosProblems.Erdos207.RootedThreatWeight

/-!
# Rooted absorber-threat extension bounds

This file converts the refined indexed A2 estimate into the extension bound
needed by the rooted-threat moment argument.  A high-order witness is encoded
by its designated triangle through the fixed pair, its indexed outside size,
and its outside configuration.  The encoding is injective.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

/-- Rooted witnesses whose outside configuration has a realization of order
at least five and hence belongs to the indexed A2 family. -/
def IsIndexedRootedThreatWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) (u v : V)
    (z : RootedThreatWitness V
      (absorberErdosForbiddenConfigurationsOn q B) u v) : Prop :=
  z.1.1 ∈ absorberInducedConfigurationsOn q (z.1.1.card + 2) B

abbrev IndexedRootedThreatWitness
    (V : Type*) [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) (u v : V) :=
  {z : RootedThreatWitness V
      (absorberErdosForbiddenConfigurationsOn q B) u v //
    IsIndexedRootedThreatWitness q B u v z}

noncomputable instance instDecidablePredIsIndexedRootedThreatWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) (u v : V) :
    DecidablePred (IsIndexedRootedThreatWitness q B u v) :=
  Classical.decPred _

/-- The finite interval of possible indexed outside-size parameters. -/
abbrev IndexedThreatOrder (q : ℕ) := {j : ℕ // j ∈ Icc 3 q}

/-- Injective ambient code for indexed rooted witnesses. -/
abbrev IndexedRootedThreatCode
    (V : Type*) [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) (u v : V) :=
  Σ T : universeTriplesThroughPair u v,
    Σ j : IndexedThreatOrder q,
      {S : TripleSystemOn V //
        S ∈ absorberInducedConfigurationsOn q j.1 B}

lemma indexedRootedThreat_order_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {u v : V}
    (z : IndexedRootedThreatWitness V q B u v) :
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

def indexedRootedThreatCode
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {u v : V}
    (z : IndexedRootedThreatWitness V q B u v) :
    IndexedRootedThreatCode V q B u v :=
  ⟨⟨z.1.1.2, mem_universeTriplesThroughPair_iff.mpr
      ⟨z.1.2.2.2.1, z.1.2.2.2.2⟩⟩,
    ⟨⟨z.1.1.1.card + 2, indexedRootedThreat_order_mem z⟩,
      ⟨z.1.1.1, z.2⟩⟩⟩

lemma indexedRootedThreatCode_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {u v : V} :
    Function.Injective
      (indexedRootedThreatCode :
        IndexedRootedThreatWitness V q B u v →
          IndexedRootedThreatCode V q B u v) := by
  intro z w hzw
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun c ↦ c.2.2.1) hzw
  · exact congrArg (fun c ↦ c.1.1) hzw

lemma rootedThreatRemainder_sdiff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {u v : V}
    (z : RootedThreatWitness V F u v) (A : TripleSystemOn V) :
    rootedThreatRemainder z \ A = z.1.1 \ insert z.1.2 A := by
  ext T
  simp only [rootedThreatRemainder, mem_sdiff, mem_erase, mem_insert]
  tauto

lemma insert_root_subset_of_remainder
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {u v : V}
    (z : RootedThreatWitness V F u v) {A : TripleSystemOn V}
    (hA : A ⊆ rootedThreatRemainder z) :
    insert z.1.2 A ⊆ z.1.1 := by
  intro T hT
  rw [mem_insert] at hT
  rcases hT with rfl | hTA
  · exact z.2.2.1
  · exact (mem_erase.mp (hA hTA)).2

/-- A finite injective code dominates the corresponding nonnegative sum. -/
lemma sum_le_sum_of_injective_code
    {I J : Type*} [Fintype I] [Fintype J]
    (e : I → J) (he : Function.Injective e)
    (f : I → ℝ≥0) (g : J → ℝ≥0)
    (hfg : ∀ i, f i ≤ g (e i)) :
    ∑ i, f i ≤ ∑ j, g j := by
  classical
  calc
    ∑ i, f i ≤ ∑ i, g (e i) := by
      apply sum_le_sum
      intro i _hi
      exact hfg i
    _ = ∑ j ∈ (univ : Finset I).image e, g j := by
      symm
      apply sum_image
      intro x _hx y _hy hxy
      exact he hxy
    _ ≤ ∑ j ∈ (univ : Finset J), g j := by
      apply sum_le_sum_of_subset
      intro j _hj
      exact mem_univ j
    _ = ∑ j, g j := rfl

def indexedRootedThreatCodeWeight
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {u v : V}
    (p : TripleOn V → ℝ≥0) (A : TripleSystemOn V)
    (c : IndexedRootedThreatCode V q B u v) : ℝ≥0 :=
  if insert c.1.1 A ⊆ c.2.2.1 then
    setWeight p (c.2.2.1 \ insert c.1.1 A)
  else 0

theorem indexedRootedThreat_weight_le_code
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {u v : V}
    (p : TripleOn V → ℝ≥0) (A : TripleSystemOn V) :
    (∑ z : IndexedRootedThreatWitness V q B u v,
      if A ⊆ rootedThreatRemainder z.1 then
        setWeight p (rootedThreatRemainder z.1 \ A)
      else 0) ≤
      ∑ c : IndexedRootedThreatCode V q B u v,
        indexedRootedThreatCodeWeight p A c := by
  apply sum_le_sum_of_injective_code indexedRootedThreatCode
    indexedRootedThreatCode_injective
  intro z
  by_cases hA : A ⊆ rootedThreatRemainder z.1
  · rw [if_pos hA]
    change setWeight p (rootedThreatRemainder z.1 \ A) ≤
      if insert z.1.1.2 A ⊆ z.1.1.1 then
        setWeight p (z.1.1.1 \ insert z.1.1.2 A) else 0
    rw [if_pos (insert_root_subset_of_remainder z.1 hA)]
    rw [rootedThreatRemainder_sdiff]
  · simp [hA, indexedRootedThreatCodeWeight]

theorem sum_indexedRootedThreatCodeWeight_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {u v : V}
    (p : TripleOn V → ℝ≥0) (A : TripleSystemOn V) :
    (∑ c : IndexedRootedThreatCode V q B u v,
      indexedRootedThreatCodeWeight p A c) =
      ∑ T : universeTriplesThroughPair u v,
        ∑ j : IndexedThreatOrder q,
          extensionWeight
            (fun S : absorberInducedConfigurationsOn q j.1 B ↦ S.1)
            p (insert T.1 A) := by
  unfold IndexedRootedThreatCode
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro T _hT
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro j _hj
  rfl

/-- Ambient-order-free bound supplied by the refined A2 split for one
nonempty indexed outside root. -/
noncomputable def refinedIndexedAbsorberBudget
    {V : Type*} [Fintype V] [DecidableEq V]
    (q M : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) : ℕ :=
  (q + 1) * 2 ^ M * (2 ^ (q ^ 3) * (q + 1)) +
    ((graphSupportFinset H \ X).card + 1) * (q + 1) *
      (B.card + 1) ^ q * (2 ^ (q ^ 3) * (q + 1))

theorem extensionWeight_indexed_insert_le_refinedBudget
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V}
    (hA2 : HasAbsorberLocalization q M H X B)
    (T : TripleOn V) (A : TripleSystemOn V)
    (j : IndexedThreatOrder q) :
    extensionWeight
        (fun S : absorberInducedConfigurationsOn q j.1 B ↦ S.1)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹))
        (insert T A) ≤
      (refinedIndexedAbsorberBudget q M H X B : ℕ) := by
  have hj2 : 2 ≤ j.1 := by
    have hj3 := (mem_Icc.mp j.2).1
    omega
  have hroot_nonempty : 1 ≤ (insert T A).card := by
    exact card_pos.mpr (by simp)
  by_cases hrootq : (insert T A).card ≤ q
  · obtain ⟨L, _hLB, _hLM, hweight⟩ :=
      exists_local_bank_extensionWeight_absorberInduced_le_refined_budget
        hA2 hrootq hj2 hroot_nonempty
    simpa only [refinedIndexedAbsorberBudget, Nat.cast_add] using hweight
  · have hzero :
        extensionWeight
            (fun S : absorberInducedConfigurationsOn q j.1 B ↦ S.1)
            (constantTripleWeight
              ((Fintype.card V + 1 : ℝ≥0)⁻¹)) (insert T A) = 0 := by
      unfold extensionWeight
      apply sum_eq_zero
      intro S _hS
      have hnsub : ¬ insert T A ⊆ S.1 := by
        intro hsub
        have hc := card_le_card hsub
        have hScard :=
          (mem_absorberInducedConfigurationsOn_iff.mp S.2).1
        have hjq := (mem_Icc.mp j.2).2
        exact hrootq (by omega)
      simp [hnsub]
    rw [hzero]
    exact zero_le

/-- The indexed (order at least five) portion of the rooted witness family
has linear ambient extension weight. -/
theorem extensionWeight_indexedRootedThreat_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V} {u v : V}
    (hA2 : HasAbsorberLocalization q M H X B) (huv : u ≠ v)
    (A : TripleSystemOn V) :
    extensionWeight
        (fun z : IndexedRootedThreatWitness V q B u v ↦
          rootedThreatRemainder z.1)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) A ≤
      ((Fintype.card V * (q + 1) *
        refinedIndexedAbsorberBudget q M H X B : ℕ) : ℝ≥0) := by
  let p : TripleOn V → ℝ≥0 :=
    constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)
  have horder : Fintype.card (IndexedThreatOrder q) ≤ q + 1 := by
    dsimp only [IndexedThreatOrder]
    rw [Fintype.card_coe]
    rw [Nat.card_Icc]
    omega
  calc
    extensionWeight
        (fun z : IndexedRootedThreatWitness V q B u v ↦
          rootedThreatRemainder z.1) p A =
      ∑ z : IndexedRootedThreatWitness V q B u v,
        if A ⊆ rootedThreatRemainder z.1 then
          setWeight p (rootedThreatRemainder z.1 \ A) else 0 := rfl
    _ ≤ ∑ c : IndexedRootedThreatCode V q B u v,
        indexedRootedThreatCodeWeight p A c :=
      indexedRootedThreat_weight_le_code p A
    _ = ∑ T : universeTriplesThroughPair u v,
        ∑ j : IndexedThreatOrder q,
          extensionWeight
            (fun S : absorberInducedConfigurationsOn q j.1 B ↦ S.1)
            p (insert T.1 A) :=
      sum_indexedRootedThreatCodeWeight_eq p A
    _ ≤ ∑ _T : universeTriplesThroughPair u v,
        ∑ _j : IndexedThreatOrder q,
          (refinedIndexedAbsorberBudget q M H X B : ℝ≥0) := by
      apply sum_le_sum
      intro T _hT
      apply sum_le_sum
      intro j _hj
      exact extensionWeight_indexed_insert_le_refinedBudget hA2 T.1 A j
    _ = ((Fintype.card (universeTriplesThroughPair u v) *
        Fintype.card (IndexedThreatOrder q) *
          refinedIndexedAbsorberBudget q M H X B : ℕ) : ℝ≥0) := by
      simp only [sum_const, card_univ, Nat.cast_mul, nsmul_eq_mul]
      ring
    _ ≤ ((Fintype.card V * (q + 1) *
        refinedIndexedAbsorberBudget q M H X B : ℕ) : ℝ≥0) := by
      exact_mod_cast Nat.mul_le_mul
        (Nat.mul_le_mul
          (by
            simpa only [Fintype.card_coe] using
              card_universeTriplesThroughPair_le V huv)
          horder)
        (le_refl (refinedIndexedAbsorberBudget q M H X B))

end Erdos207
