/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PairExactBankWeightedBound
import ErdosProblems.Erdos207.TwoAwayAbsorberBound
import ErdosProblems.Erdos207.FiniteSpanCounting

/-!
# Ambient-independent pair-local two-away bound

The order-four witnesses are pair-sharing and therefore absent from the
genuinely two-away fixed-pair family.  Every remaining witness is split by
its order and its exact intersection with the fixed absorber bank.  The
single-class estimate then gives a coefficient depending on `q` and `B`, but
not on the number of ambient padding vertices.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Exact active codes for one indexed outside-size class. -/
abbrev PairInducedExactActiveCode
    (V : Type*) [Fintype V] [DecidableEq V]
    (q j : ℕ) (B : TripleSystemOn V) (U : TripleOn V) (P : PairOn V)
    (A : TripleSystemOn V) :=
  Σ r : (Icc 5 q : Finset ℕ), Σ K : subsetsUpToCard B q,
    ActivePairFamilyTwoAwayWitness
      (exactBankOutsideExtensions r.1 j B (insert U A) K.1) U P A

/-- Choose one witnessing Erdős configuration and record its exact bank
intersection.  The active witness itself is retained, so this coding is
injective even if a family has more than one realization. -/
noncomputable def pairInducedExactActiveCode
    {V : Type*} [Fintype V] [DecidableEq V]
    {q j : ℕ} {B : TripleSystemOn V} {U : TripleOn V} {P : PairOn V}
    {A : TripleSystemOn V}
    (z : ActivePairFamilyTwoAwayWitness
      (absorberInducedConfigurationsOn q j B) U P A) :
    PairInducedExactActiveCode V q j B U P A := by
  classical
  let hdata := mem_absorberInducedConfigurationsOn_iff.mp z.1.1.family_mem
  let r := Classical.choose hdata.2
  let hrdata := Classical.choose_spec hdata.2
  let E := Classical.choose hrdata.2.2
  let hEdata := Classical.choose_spec hrdata.2.2
  let K : TripleSystemOn V := E ∩ B
  have hKq : K.card ≤ q := by
    calc
      K.card ≤ E.card := card_le_card inter_subset_left
      _ = r - 2 := hEdata.1.1.1
      _ ≤ q := by omega
  have hKmem : K ∈ subsetsUpToCard B q :=
    mem_subsetsUpToCard_iff.mpr ⟨inter_subset_right, hKq⟩
  have hroot : insert U A ⊆ z.1.1.family := by
    intro T hT
    rw [mem_insert] at hT
    rcases hT with rfl | hTA
    · exact z.1.1.fixed_mem
    · exact mem_of_mem_erase (mem_of_mem_erase (z.2 hTA))
  have hexact : z.1.1.family ∈
    exactBankOutsideExtensions r j B (insert U A) K := by
    apply mem_exactBankOutsideExtensions_iff.mpr
    exact ⟨hdata.1, hroot, E, hEdata.1, hEdata.2, rfl⟩
  let w : FamilyTwoAwayWitness
      (exactBankOutsideExtensions r j B (insert U A) K) U :=
    { family := z.1.1.family
      family_mem := hexact
      fixed_mem := z.1.1.fixed_mem
      missing := z.1.1.missing
      missing_mem := z.1.1.missing_mem
      missing_ne := z.1.1.missing_ne }
  let pw : PairFamilyTwoAwayWitness
      (exactBankOutsideExtensions r j B (insert U A) K) U P :=
    ⟨w, z.1.2⟩
  refine ⟨⟨r, mem_Icc.mpr ⟨hrdata.1, hrdata.2.1⟩⟩,
    ⟨K, hKmem⟩, ⟨pw, ?_⟩⟩
  change A ⊆ (z.1.1.family.erase z.1.1.missing).erase U
  exact z.2

@[simp]
lemma pairInducedExactActiveCode_family
    {V : Type*} [Fintype V] [DecidableEq V]
    {q j : ℕ} {B : TripleSystemOn V} {U : TripleOn V} {P : PairOn V}
    {A : TripleSystemOn V}
    (z : ActivePairFamilyTwoAwayWitness
      (absorberInducedConfigurationsOn q j B) U P A) :
    (pairInducedExactActiveCode z).2.2.1.1.family = z.1.1.family := by
  classical
  unfold pairInducedExactActiveCode
  rfl

@[simp]
lemma pairInducedExactActiveCode_missing
    {V : Type*} [Fintype V] [DecidableEq V]
    {q j : ℕ} {B : TripleSystemOn V} {U : TripleOn V} {P : PairOn V}
    {A : TripleSystemOn V}
    (z : ActivePairFamilyTwoAwayWitness
      (absorberInducedConfigurationsOn q j B) U P A) :
    (pairInducedExactActiveCode z).2.2.1.1.missing = z.1.1.missing := by
  classical
  unfold pairInducedExactActiveCode
  rfl

lemma pairInducedExactActiveCode_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {q j : ℕ} {B : TripleSystemOn V} {U : TripleOn V} {P : PairOn V}
    {A : TripleSystemOn V} :
    Function.Injective
      (pairInducedExactActiveCode :
        ActivePairFamilyTwoAwayWitness
          (absorberInducedConfigurationsOn q j B) U P A →
        PairInducedExactActiveCode V q j B U P A) := by
  intro z w hzw
  have hfamily := congrArg (fun c ↦ c.2.2.1.1.family) hzw
  rw [pairInducedExactActiveCode_family,
    pairInducedExactActiveCode_family] at hfamily
  have hmissing := congrArg (fun c ↦ c.2.2.1.1.missing) hzw
  rw [pairInducedExactActiveCode_missing,
    pairInducedExactActiveCode_missing] at hmissing
  apply Subtype.ext
  exact pairFamilyTwoAwayWitness_ext hfamily hmissing

lemma card_activePair_absorberInduced_le_exact_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    {q j : ℕ} {B : TripleSystemOn V} {U : TripleOn V} {P : PairOn V}
    (A : TripleSystemOn V) :
    Fintype.card (ActivePairFamilyTwoAwayWitness
        (absorberInducedConfigurationsOn q j B) U P A) ≤
      ∑ r : (Icc 5 q : Finset ℕ), ∑ K : subsetsUpToCard B q,
        Fintype.card (ActivePairFamilyTwoAwayWitness
          (exactBankOutsideExtensions r.1 j B (insert U A) K.1) U P A) := by
  calc
    Fintype.card (ActivePairFamilyTwoAwayWitness
        (absorberInducedConfigurationsOn q j B) U P A) ≤
      Fintype.card (PairInducedExactActiveCode V q j B U P A) :=
        Fintype.card_le_of_injective pairInducedExactActiveCode
          pairInducedExactActiveCode_injective
    _ = ∑ r : (Icc 5 q : Finset ℕ), ∑ K : subsetsUpToCard B q,
        Fintype.card (ActivePairFamilyTwoAwayWitness
          (exactBankOutsideExtensions r.1 j B (insert U A) K.1) U P A) := by
      simp [PairInducedExactActiveCode]

/-- The exact-bank coefficient for one indexed outside-size class. -/
noncomputable def pairExactBankExtensionCoefficient
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) : ℕ :=
  ∑ r : (Icc 5 q : Finset ℕ), ∑ _K : subsetsUpToCard B q,
    2 ^ (r.1 ^ 3) * (r.1 + 1)

/-- One indexed outside-size class has ambient-independent pair-local
two-away extension weight. -/
theorem extensionWeight_pairFamily_absorberInduced_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : TripleOn V} {P : PairOn V}
    (A : TripleSystemOn V) (j : IndexedThreatOrder q) :
    extensionWeight
        (fun z : PairFamilyTwoAwayWitness
            (absorberInducedConfigurationsOn q j.1 B) U P ↦
          pairFamilyTwoAwayRemainder z)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) A ≤
      (pairExactBankExtensionCoefficient q B : ℕ) := by
  classical
  let G := absorberInducedConfigurationsOn q j.1 B
  let p : ℝ≥0 := (Fintype.card V + 1 : ℝ≥0)⁻¹
  change extensionWeight
      (fun z : PairFamilyTwoAwayWitness G U P ↦
        pairFamilyTwoAwayRemainder z) (constantTripleWeight p) A ≤ _
  rw [extensionWeight_pairFamilyTwoAway_eq
    (m := j.1 - 2) absorberInducedConfigurationsOn_fixed_card]
  by_cases hactive : IsEmpty (ActivePairFamilyTwoAwayWitness G U P A)
  · have hzero : Fintype.card
        (ActivePairFamilyTwoAwayWitness G U P A) = 0 := Fintype.card_eq_zero
    simp [hzero]
  · let : Nonempty (ActivePairFamilyTwoAwayWitness G U P A) :=
      not_isEmpty_iff.mp hactive
    let z : ActivePairFamilyTwoAwayWitness G U P A :=
      Classical.choice inferInstance
    have hj4 : 4 ≤ j.1 := by
      have htwo : 1 < z.1.1.family.card := by
        exact one_lt_card.mpr
          ⟨U, z.1.1.fixed_mem, z.1.1.missing,
            z.1.1.missing_mem, z.1.1.missing_ne.symm⟩
      rw [absorberInducedConfigurationsOn_fixed_card
        z.1.1.family z.1.1.family_mem] at htwo
      omega
    have hcard := card_activePair_absorberInduced_le_exact_sum
      (q := q) (j := j.1) (B := B) (U := U) (P := P) A
    have hcast :
        (Fintype.card (ActivePairFamilyTwoAwayWitness G U P A) : ℝ≥0) ≤
          (∑ r : (Icc 5 q : Finset ℕ), ∑ K : subsetsUpToCard B q,
            Fintype.card (ActivePairFamilyTwoAwayWitness
              (exactBankOutsideExtensions r.1 j.1 B (insert U A) K.1)
                U P A) : ℕ) := by
      exact_mod_cast hcard
    calc
      (Fintype.card (ActivePairFamilyTwoAwayWitness G U P A) : ℝ≥0) *
          p ^ (j.1 - 2 - 2 - A.card) ≤
        ((∑ r : (Icc 5 q : Finset ℕ), ∑ K : subsetsUpToCard B q,
            Fintype.card (ActivePairFamilyTwoAwayWitness
              (exactBankOutsideExtensions r.1 j.1 B (insert U A) K.1)
                U P A) : ℕ) : ℝ≥0) *
          p ^ (j.1 - 2 - 2 - A.card) := by
            simpa only [mul_comm] using
              mul_le_mul_right hcast (p ^ (j.1 - 2 - 2 - A.card))
      _ = ∑ r : (Icc 5 q : Finset ℕ), ∑ K : subsetsUpToCard B q,
          (Fintype.card (ActivePairFamilyTwoAwayWitness
            (exactBankOutsideExtensions r.1 j.1 B (insert U A) K.1)
              U P A) : ℝ≥0) * p ^ (j.1 - 2 - 2 - A.card) := by
        simp only [Nat.cast_sum, sum_mul]
      _ = ∑ r : (Icc 5 q : Finset ℕ), ∑ K : subsetsUpToCard B q,
          extensionWeight
            (fun z : PairFamilyTwoAwayWitness
                (exactBankOutsideExtensions r.1 j.1 B (insert U A) K.1)
                  U P ↦ pairFamilyTwoAwayRemainder z)
            (constantTripleWeight p) A := by
        apply sum_congr rfl
        intro r _hr
        apply sum_congr rfl
        intro K _hK
        symm
        exact extensionWeight_pairFamilyTwoAway_eq
          exactBankOutsideExtensions_fixed_card p A
      _ ≤ ∑ r : (Icc 5 q : Finset ℕ), ∑ _K : subsetsUpToCard B q,
          (2 ^ (r.1 ^ 3) * (r.1 + 1) : ℕ) := by
        simp only [Nat.cast_sum]
        apply sum_le_sum
        intro r _hr
        apply sum_le_sum
        intro K _hK
        exact extensionWeight_pairFamily_exactBank_le_constant A
          (mem_Icc.mp r.2).1 hj4
      _ = (pairExactBankExtensionCoefficient q B : ℕ) := by
        simp [pairExactBankExtensionCoefficient]

/-- All genuinely pair-local witnesses are in the indexed (order at least
five) branch. -/
lemma pairTwoAwayThreat_isIndexed
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : TripleOn V} {P : PairOn V}
    (z : PairTwoAwayThreatWitness V
      (absorberErdosForbiddenConfigurationsOn q B) U P) :
    IsIndexedTwoAwayThreatWitness q B U z.1 := by
  by_contra hnot
  let w : FourTwoAwayThreatWitness V q B U := ⟨z.1, hnot⟩
  exact z.2.2 (fourTwoAwayThreat_missing_shares_pair w)

abbrev PairIndexedTwoAwayThreatCode
    (V : Type*) [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) (U : TripleOn V) (P : PairOn V) :=
  Σ j : IndexedThreatOrder q,
    PairFamilyTwoAwayWitness (absorberInducedConfigurationsOn q j.1 B) U P

def pairIndexedTwoAwayThreatCode
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : TripleOn V} {P : PairOn V}
    (z : PairTwoAwayThreatWitness V
      (absorberErdosForbiddenConfigurationsOn q B) U P) :
    PairIndexedTwoAwayThreatCode V q B U P :=
  let zi : IndexedTwoAwayThreatWitness V q B U :=
    ⟨z.1, pairTwoAwayThreat_isIndexed z⟩
  let c := indexedTwoAwayThreatCode zi
  ⟨c.1, ⟨c.2, z.2⟩⟩

lemma pairIndexedTwoAwayThreatCode_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : TripleOn V} {P : PairOn V} :
    Function.Injective
      (pairIndexedTwoAwayThreatCode :
        PairTwoAwayThreatWitness V
          (absorberErdosForbiddenConfigurationsOn q B) U P →
        PairIndexedTwoAwayThreatCode V q B U P) := by
  intro z w hzw
  have hfamily : z.1.1.1 = w.1.1.1 :=
    congrArg (fun c ↦ c.2.1.family) hzw
  have hmissing : z.1.1.2 = w.1.1.2 :=
    congrArg (fun c ↦ c.2.1.missing) hzw
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact hfamily
  · exact hmissing

def pairIndexedTwoAwayThreatCodeWeight
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : TripleOn V} {P : PairOn V}
    (p : TripleOn V → ℝ≥0) (A : TripleSystemOn V)
    (c : PairIndexedTwoAwayThreatCode V q B U P) : ℝ≥0 :=
  if A ⊆ pairFamilyTwoAwayRemainder c.2 then
    setWeight p (pairFamilyTwoAwayRemainder c.2 \ A)
  else 0

lemma pairTwoAwayThreat_weight_le_indexedCode
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : TripleOn V} {P : PairOn V}
    (p : TripleOn V → ℝ≥0) (A : TripleSystemOn V) :
    extensionWeight
        (fun z : PairTwoAwayThreatWitness V
            (absorberErdosForbiddenConfigurationsOn q B) U P ↦
          pairTwoAwayThreatRemainder z) p A ≤
      ∑ c : PairIndexedTwoAwayThreatCode V q B U P,
        pairIndexedTwoAwayThreatCodeWeight p A c := by
  apply sum_le_sum_of_injective_code pairIndexedTwoAwayThreatCode
    pairIndexedTwoAwayThreatCode_injective
  intro z
  rfl

lemma sum_pairIndexedTwoAwayThreatCodeWeight_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : TripleOn V} {P : PairOn V}
    (p : TripleOn V → ℝ≥0) (A : TripleSystemOn V) :
    (∑ c : PairIndexedTwoAwayThreatCode V q B U P,
      pairIndexedTwoAwayThreatCodeWeight p A c) =
      ∑ j : IndexedThreatOrder q,
        extensionWeight
          (fun z : PairFamilyTwoAwayWitness
              (absorberInducedConfigurationsOn q j.1 B) U P ↦
            pairFamilyTwoAwayRemainder z) p A := by
  unfold PairIndexedTwoAwayThreatCode
  rw [Fintype.sum_sigma]
  rfl

noncomputable def pairTwoAwayThreatExtensionCoefficient
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) : ℕ :=
  (q + 1) * pairExactBankExtensionCoefficient q B

/-- The required local extension bound.  Its coefficient contains no ambient
cardinality factor. -/
theorem absorberPairTwoAwayThreatRemainder_hasExtensionBound
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : TripleOn V} {P : PairOn V} :
    HasExtensionBound
      (fun z : PairTwoAwayThreatWitness V
          (absorberErdosForbiddenConfigurationsOn q B) U P ↦
        pairTwoAwayThreatRemainder z)
      (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹))
      (pairTwoAwayThreatExtensionCoefficient q B : ℕ) := by
  intro A
  calc
    extensionWeight
        (fun z : PairTwoAwayThreatWitness V
            (absorberErdosForbiddenConfigurationsOn q B) U P ↦
          pairTwoAwayThreatRemainder z)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) A ≤
      ∑ c : PairIndexedTwoAwayThreatCode V q B U P,
        pairIndexedTwoAwayThreatCodeWeight
          (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) A c :=
      pairTwoAwayThreat_weight_le_indexedCode _ _
    _ = ∑ j : IndexedThreatOrder q,
        extensionWeight
          (fun z : PairFamilyTwoAwayWitness
              (absorberInducedConfigurationsOn q j.1 B) U P ↦
            pairFamilyTwoAwayRemainder z)
          (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) A :=
      sum_pairIndexedTwoAwayThreatCodeWeight_eq _ _
    _ ≤ ∑ _j : IndexedThreatOrder q,
        (pairExactBankExtensionCoefficient q B : ℕ) := by
      simp only [Nat.cast_sum]
      apply sum_le_sum
      intro j _hj
      exact extensionWeight_pairFamily_absorberInduced_le A j
    _ = (Fintype.card (IndexedThreatOrder q) : ℝ≥0) *
        (pairExactBankExtensionCoefficient q B : ℕ) := by
      rw [sum_const, nsmul_eq_mul, card_univ]
      norm_cast
    _ ≤ ((q + 1 : ℕ) : ℝ≥0) *
        (pairExactBankExtensionCoefficient q B : ℕ) := by
      have hcard : (Fintype.card (IndexedThreatOrder q) : ℝ≥0) ≤
          ((q + 1 : ℕ) : ℝ≥0) := by
        exact_mod_cast card_indexedThreatOrder_le q
      simpa only [mul_comm] using mul_le_mul_right hcard
        (pairExactBankExtensionCoefficient q B : ℕ)
    _ = (pairTwoAwayThreatExtensionCoefficient q B : ℕ) := by
      simp [pairTwoAwayThreatExtensionCoefficient]

end

end Erdos207
