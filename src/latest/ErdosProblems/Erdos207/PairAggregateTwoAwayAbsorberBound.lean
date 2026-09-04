/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PairAggregateTwoAwayWeight
import ErdosProblems.Erdos207.PairTwoAwayAbsorberBound

/-!
# Aggregate fixed-pair two-away bound for an absorber

The exact-bank quadratic estimate is summed over the finitely many minimal
configuration orders and exact intersections with the absorber bank.  The
resulting coefficient depends on the fixed cutoff and bank, but not on the
ambient padding set.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Exact active codes for aggregate pair witnesses in one indexed outside
size. -/
abbrev AggregatePairInducedExactActiveCode
    (V : Type*) [Fintype V] [DecidableEq V]
    (q j : ℕ) (B : TripleSystemOn V) (P : PairOn V)
    (A : TripleSystemOn V) :=
  Σ r : (Icc 5 q : Finset ℕ), Σ K : subsetsUpToCard B q,
    ActiveAggregatePairFamilyTwoAwayWitness
      (exactBankOutsideExtensions r.1 j B A K.1) P A

/-- Choose a witnessing minimal configuration and remember its exact bank
intersection. -/
noncomputable def aggregatePairInducedExactActiveCode
    {V : Type*} [Fintype V] [DecidableEq V]
    {q j : ℕ} {B : TripleSystemOn V} {P : PairOn V}
    {A : TripleSystemOn V}
    (z : ActiveAggregatePairFamilyTwoAwayWitness
      (absorberInducedConfigurationsOn q j B) P A) :
    AggregatePairInducedExactActiveCode V q j B P A := by
  classical
  let hdata := mem_absorberInducedConfigurationsOn_iff.mp
    z.1.2.1.family_mem
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
  have hroot : A ⊆ z.1.2.1.family := by
    intro T hTA
    exact mem_of_mem_erase (mem_of_mem_erase (z.2 hTA))
  have hexact : z.1.2.1.family ∈
      exactBankOutsideExtensions r j B A K := by
    apply mem_exactBankOutsideExtensions_iff.mpr
    exact ⟨hdata.1, hroot, E, hEdata.1, hEdata.2, rfl⟩
  let w : FamilyTwoAwayWitness
      (exactBankOutsideExtensions r j B A K) z.1.1 :=
    { family := z.1.2.1.family
      family_mem := hexact
      fixed_mem := z.1.2.1.fixed_mem
      missing := z.1.2.1.missing
      missing_mem := z.1.2.1.missing_mem
      missing_ne := z.1.2.1.missing_ne }
  let pw : PairFamilyTwoAwayWitness
      (exactBankOutsideExtensions r j B A K) z.1.1 P :=
    ⟨w, z.1.2.2⟩
  let aw : AggregatePairFamilyTwoAwayWitness
      (exactBankOutsideExtensions r j B A K) P := ⟨z.1.1, pw⟩
  refine ⟨⟨r, mem_Icc.mpr ⟨hrdata.1, hrdata.2.1⟩⟩,
    ⟨K, hKmem⟩, ⟨aw, ?_⟩⟩
  change A ⊆ (z.1.2.1.family.erase z.1.2.1.missing).erase z.1.1
  exact z.2

@[simp]
lemma aggregatePairInducedExactActiveCode_selector
    {V : Type*} [Fintype V] [DecidableEq V]
    {q j : ℕ} {B : TripleSystemOn V} {P : PairOn V}
    {A : TripleSystemOn V}
    (z : ActiveAggregatePairFamilyTwoAwayWitness
      (absorberInducedConfigurationsOn q j B) P A) :
    (aggregatePairInducedExactActiveCode z).2.2.1.1 = z.1.1 := by
  classical
  unfold aggregatePairInducedExactActiveCode
  rfl

@[simp]
lemma aggregatePairInducedExactActiveCode_family
    {V : Type*} [Fintype V] [DecidableEq V]
    {q j : ℕ} {B : TripleSystemOn V} {P : PairOn V}
    {A : TripleSystemOn V}
    (z : ActiveAggregatePairFamilyTwoAwayWitness
      (absorberInducedConfigurationsOn q j B) P A) :
    (aggregatePairInducedExactActiveCode z).2.2.1.2.1.family =
      z.1.2.1.family := by
  classical
  unfold aggregatePairInducedExactActiveCode
  rfl

@[simp]
lemma aggregatePairInducedExactActiveCode_missing
    {V : Type*} [Fintype V] [DecidableEq V]
    {q j : ℕ} {B : TripleSystemOn V} {P : PairOn V}
    {A : TripleSystemOn V}
    (z : ActiveAggregatePairFamilyTwoAwayWitness
      (absorberInducedConfigurationsOn q j B) P A) :
    (aggregatePairInducedExactActiveCode z).2.2.1.2.1.missing =
      z.1.2.1.missing := by
  classical
  unfold aggregatePairInducedExactActiveCode
  rfl

lemma aggregatePairInducedExactActiveCode_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {q j : ℕ} {B : TripleSystemOn V} {P : PairOn V}
    {A : TripleSystemOn V} :
    Function.Injective
      (aggregatePairInducedExactActiveCode :
        ActiveAggregatePairFamilyTwoAwayWitness
          (absorberInducedConfigurationsOn q j B) P A →
        AggregatePairInducedExactActiveCode V q j B P A) := by
  intro z w hzw
  have hselector := congrArg (fun c ↦ c.2.2.1.1) hzw
  rw [aggregatePairInducedExactActiveCode_selector,
    aggregatePairInducedExactActiveCode_selector] at hselector
  have hfamily := congrArg (fun c ↦ c.2.2.1.2.1.family) hzw
  rw [aggregatePairInducedExactActiveCode_family,
    aggregatePairInducedExactActiveCode_family] at hfamily
  have hmissing := congrArg (fun c ↦ c.2.2.1.2.1.missing) hzw
  rw [aggregatePairInducedExactActiveCode_missing,
    aggregatePairInducedExactActiveCode_missing] at hmissing
  apply Subtype.ext
  exact aggregatePairFamilyTwoAwayWitness_ext hselector hfamily hmissing

lemma card_activeAggregatePair_absorberInduced_le_exact_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    {q j : ℕ} {B : TripleSystemOn V} {P : PairOn V}
    (A : TripleSystemOn V) :
    Fintype.card (ActiveAggregatePairFamilyTwoAwayWitness
        (absorberInducedConfigurationsOn q j B) P A) ≤
      ∑ r : (Icc 5 q : Finset ℕ), ∑ K : subsetsUpToCard B q,
        Fintype.card (ActiveAggregatePairFamilyTwoAwayWitness
          (exactBankOutsideExtensions r.1 j B A K.1) P A) := by
  calc
    Fintype.card (ActiveAggregatePairFamilyTwoAwayWitness
        (absorberInducedConfigurationsOn q j B) P A) ≤
      Fintype.card (AggregatePairInducedExactActiveCode V q j B P A) :=
        Fintype.card_le_of_injective aggregatePairInducedExactActiveCode
          aggregatePairInducedExactActiveCode_injective
    _ = ∑ r : (Icc 5 q : Finset ℕ), ∑ K : subsetsUpToCard B q,
        Fintype.card (ActiveAggregatePairFamilyTwoAwayWitness
          (exactBankOutsideExtensions r.1 j B A K.1) P A) := by
      simp [AggregatePairInducedExactActiveCode]

/-- Ambient-independent coefficient multiplying the quadratic scale for one
indexed outside size. -/
noncomputable def aggregatePairExactBankExtensionCoefficient
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (B : TripleSystemOn V) : ℕ :=
  ∑ r : (Icc 5 q : Finset ℕ), ∑ _K : subsetsUpToCard B q,
    (j - 2) * (2 ^ (r.1 ^ 3) * (r.1 + 1))

/-- Aggregate pair extension weight for one indexed outside size. -/
theorem extensionWeight_aggregatePairFamily_absorberInduced_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {P : PairOn V}
    (A : TripleSystemOn V) (j : IndexedThreatOrder q) :
    extensionWeight
        (fun z : AggregatePairFamilyTwoAwayWitness
            (absorberInducedConfigurationsOn q j.1 B) P ↦
          aggregatePairFamilyTwoAwayRemainder z)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) A ≤
      (aggregatePairExactBankExtensionCoefficient q j.1 B : ℕ) *
        (Fintype.card V + 1 : ℝ≥0) ^ 2 := by
  classical
  let G := absorberInducedConfigurationsOn q j.1 B
  let p : ℝ≥0 := (Fintype.card V + 1 : ℝ≥0)⁻¹
  change extensionWeight
      (fun z : AggregatePairFamilyTwoAwayWitness G P ↦
        aggregatePairFamilyTwoAwayRemainder z) (constantTripleWeight p) A ≤ _
  rw [extensionWeight_aggregatePairFamilyTwoAway_eq
    (m := j.1 - 2) absorberInducedConfigurationsOn_fixed_card]
  by_cases hactive : IsEmpty
      (ActiveAggregatePairFamilyTwoAwayWitness G P A)
  · have hzero : Fintype.card
        (ActiveAggregatePairFamilyTwoAwayWitness G P A) = 0 :=
      Fintype.card_eq_zero
    simp [hzero]
  · let : Nonempty (ActiveAggregatePairFamilyTwoAwayWitness G P A) :=
      not_isEmpty_iff.mp hactive
    let z : ActiveAggregatePairFamilyTwoAwayWitness G P A :=
      Classical.choice inferInstance
    have hj2 : 2 ≤ j.1 := by
      have htwo : 1 < z.1.2.1.family.card := one_lt_card.mpr
        ⟨z.1.1, z.1.2.1.fixed_mem, z.1.2.1.missing,
          z.1.2.1.missing_mem, z.1.2.1.missing_ne.symm⟩
      rw [absorberInducedConfigurationsOn_fixed_card
        z.1.2.1.family z.1.2.1.family_mem] at htwo
      omega
    have hcard := card_activeAggregatePair_absorberInduced_le_exact_sum
      (q := q) (j := j.1) (B := B) (P := P) A
    have hcast :
        (Fintype.card
          (ActiveAggregatePairFamilyTwoAwayWitness G P A) : ℝ≥0) ≤
          (∑ r : (Icc 5 q : Finset ℕ), ∑ K : subsetsUpToCard B q,
            Fintype.card (ActiveAggregatePairFamilyTwoAwayWitness
              (exactBankOutsideExtensions r.1 j.1 B A K.1) P A) : ℕ) := by
      exact_mod_cast hcard
    calc
      (Fintype.card
          (ActiveAggregatePairFamilyTwoAwayWitness G P A) : ℝ≥0) *
          p ^ (j.1 - 2 - 2 - A.card) ≤
        ((∑ r : (Icc 5 q : Finset ℕ), ∑ K : subsetsUpToCard B q,
            Fintype.card (ActiveAggregatePairFamilyTwoAwayWitness
              (exactBankOutsideExtensions r.1 j.1 B A K.1) P A) : ℕ) :
            ℝ≥0) * p ^ (j.1 - 2 - 2 - A.card) := by
          simpa only [mul_comm] using
            mul_le_mul_right hcast (p ^ (j.1 - 2 - 2 - A.card))
      _ = ∑ r : (Icc 5 q : Finset ℕ), ∑ K : subsetsUpToCard B q,
          (Fintype.card (ActiveAggregatePairFamilyTwoAwayWitness
            (exactBankOutsideExtensions r.1 j.1 B A K.1) P A) : ℝ≥0) *
              p ^ (j.1 - 2 - 2 - A.card) := by
        simp only [Nat.cast_sum, sum_mul]
      _ = ∑ r : (Icc 5 q : Finset ℕ), ∑ K : subsetsUpToCard B q,
          extensionWeight
            (fun z : AggregatePairFamilyTwoAwayWitness
                (exactBankOutsideExtensions r.1 j.1 B A K.1) P ↦
              aggregatePairFamilyTwoAwayRemainder z)
            (constantTripleWeight p) A := by
        apply sum_congr rfl
        intro r _hr
        apply sum_congr rfl
        intro K _hK
        symm
        exact extensionWeight_aggregatePairFamilyTwoAway_eq
          exactBankOutsideExtensions_fixed_card p A
      _ ≤ ∑ r : (Icc 5 q : Finset ℕ), ∑ _K : subsetsUpToCard B q,
          ((j.1 - 2) * (2 ^ (r.1 ^ 3) * (r.1 + 1)) : ℕ) *
            (Fintype.card V + 1 : ℝ≥0) ^ 2 := by
        apply sum_le_sum
        intro r _hr
        apply sum_le_sum
        intro K _hK
        exact extensionWeight_aggregatePairFamily_exactBank_le_quadratic
          A (mem_Icc.mp r.2).1 hj2
      _ = (aggregatePairExactBankExtensionCoefficient q j.1 B : ℕ) *
          (Fintype.card V + 1 : ℝ≥0) ^ 2 := by
        simp [aggregatePairExactBankExtensionCoefficient, sum_mul, mul_assoc]

/-- Actual pair-local two-away witnesses, now with the selector varying. -/
abbrev AggregatePairTwoAwayThreatWitness
    (V : Type*) [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : PairOn V) :=
  Σ U : TripleOn V, PairTwoAwayThreatWitness V F U P

def aggregatePairTwoAwayThreatRemainder
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P : PairOn V}
    (z : AggregatePairTwoAwayThreatWitness V F P) : TripleSystemOn V :=
  pairTwoAwayThreatRemainder z.2

abbrev AggregatePairIndexedTwoAwayThreatCode
    (V : Type*) [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) (P : PairOn V) :=
  Σ j : IndexedThreatOrder q,
    AggregatePairFamilyTwoAwayWitness
      (absorberInducedConfigurationsOn q j.1 B) P

def aggregatePairIndexedTwoAwayThreatCode
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {P : PairOn V}
    (z : AggregatePairTwoAwayThreatWitness V
      (absorberErdosForbiddenConfigurationsOn q B) P) :
    AggregatePairIndexedTwoAwayThreatCode V q B P :=
  let c := pairIndexedTwoAwayThreatCode z.2
  ⟨c.1, ⟨z.1, c.2⟩⟩

@[simp]
lemma aggregatePairIndexedTwoAwayThreatCode_selector
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {P : PairOn V}
    (z : AggregatePairTwoAwayThreatWitness V
      (absorberErdosForbiddenConfigurationsOn q B) P) :
    (aggregatePairIndexedTwoAwayThreatCode z).2.1 = z.1 := by
  rfl

@[simp]
lemma aggregatePairIndexedTwoAwayThreatCode_family
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {P : PairOn V}
    (z : AggregatePairTwoAwayThreatWitness V
      (absorberErdosForbiddenConfigurationsOn q B) P) :
    (aggregatePairIndexedTwoAwayThreatCode z).2.2.1.family =
      z.2.1.1.1 := by
  rfl

@[simp]
lemma aggregatePairIndexedTwoAwayThreatCode_missing
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {P : PairOn V}
    (z : AggregatePairTwoAwayThreatWitness V
      (absorberErdosForbiddenConfigurationsOn q B) P) :
    (aggregatePairIndexedTwoAwayThreatCode z).2.2.1.missing =
      z.2.1.1.2 := by
  rfl

lemma aggregatePairIndexedTwoAwayThreatCode_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {P : PairOn V} :
    Function.Injective
      (aggregatePairIndexedTwoAwayThreatCode :
        AggregatePairTwoAwayThreatWitness V
          (absorberErdosForbiddenConfigurationsOn q B) P →
        AggregatePairIndexedTwoAwayThreatCode V q B P) := by
  intro z w hzw
  have hselector := congrArg (fun c ↦ c.2.1) hzw
  rw [aggregatePairIndexedTwoAwayThreatCode_selector,
    aggregatePairIndexedTwoAwayThreatCode_selector] at hselector
  have hfamily := congrArg (fun c ↦ c.2.2.1.family) hzw
  rw [aggregatePairIndexedTwoAwayThreatCode_family,
    aggregatePairIndexedTwoAwayThreatCode_family] at hfamily
  have hmissing := congrArg (fun c ↦ c.2.2.1.missing) hzw
  rw [aggregatePairIndexedTwoAwayThreatCode_missing,
    aggregatePairIndexedTwoAwayThreatCode_missing] at hmissing
  rcases z with ⟨U, z⟩
  rcases w with ⟨W, w⟩
  dsimp only at hselector hfamily hmissing ⊢
  subst W
  have hpair : z = w := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hfamily hmissing
  subst w
  rfl

def aggregatePairIndexedTwoAwayThreatCodeWeight
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {P : PairOn V}
    (p : TripleOn V → ℝ≥0) (A : TripleSystemOn V)
    (c : AggregatePairIndexedTwoAwayThreatCode V q B P) : ℝ≥0 :=
  if A ⊆ aggregatePairFamilyTwoAwayRemainder c.2 then
    setWeight p (aggregatePairFamilyTwoAwayRemainder c.2 \ A)
  else 0

lemma aggregatePairTwoAwayThreat_weight_le_indexedCode
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {P : PairOn V}
    (p : TripleOn V → ℝ≥0) (A : TripleSystemOn V) :
    extensionWeight
        (fun z : AggregatePairTwoAwayThreatWitness V
            (absorberErdosForbiddenConfigurationsOn q B) P ↦
          aggregatePairTwoAwayThreatRemainder z) p A ≤
      ∑ c : AggregatePairIndexedTwoAwayThreatCode V q B P,
        aggregatePairIndexedTwoAwayThreatCodeWeight p A c := by
  apply sum_le_sum_of_injective_code aggregatePairIndexedTwoAwayThreatCode
    aggregatePairIndexedTwoAwayThreatCode_injective
  intro z
  rfl

lemma sum_aggregatePairIndexedTwoAwayThreatCodeWeight_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {P : PairOn V}
    (p : TripleOn V → ℝ≥0) (A : TripleSystemOn V) :
    (∑ c : AggregatePairIndexedTwoAwayThreatCode V q B P,
      aggregatePairIndexedTwoAwayThreatCodeWeight p A c) =
      ∑ j : IndexedThreatOrder q,
        extensionWeight
          (fun z : AggregatePairFamilyTwoAwayWitness
              (absorberInducedConfigurationsOn q j.1 B) P ↦
            aggregatePairFamilyTwoAwayRemainder z) p A := by
  unfold AggregatePairIndexedTwoAwayThreatCode
  rw [Fintype.sum_sigma]
  rfl

noncomputable def aggregatePairTwoAwayThreatExtensionCoefficient
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) : ℕ :=
  ∑ j : IndexedThreatOrder q,
    aggregatePairExactBankExtensionCoefficient q j.1 B

/-- The actual aggregate threat system has an extension coefficient equal
to a fixed constant times the square of the ambient scale. -/
theorem absorberAggregatePairTwoAwayThreatRemainder_hasExtensionBound
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {P : PairOn V} :
    HasExtensionBound
      (fun z : AggregatePairTwoAwayThreatWitness V
          (absorberErdosForbiddenConfigurationsOn q B) P ↦
        aggregatePairTwoAwayThreatRemainder z)
      (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹))
      ((aggregatePairTwoAwayThreatExtensionCoefficient q B : ℕ) *
        (Fintype.card V + 1 : ℝ≥0) ^ 2) := by
  intro A
  calc
    extensionWeight
        (fun z : AggregatePairTwoAwayThreatWitness V
            (absorberErdosForbiddenConfigurationsOn q B) P ↦
          aggregatePairTwoAwayThreatRemainder z)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) A ≤
      ∑ c : AggregatePairIndexedTwoAwayThreatCode V q B P,
        aggregatePairIndexedTwoAwayThreatCodeWeight
          (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) A c :=
      aggregatePairTwoAwayThreat_weight_le_indexedCode _ _
    _ = ∑ j : IndexedThreatOrder q,
        extensionWeight
          (fun z : AggregatePairFamilyTwoAwayWitness
              (absorberInducedConfigurationsOn q j.1 B) P ↦
            aggregatePairFamilyTwoAwayRemainder z)
          (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) A :=
      sum_aggregatePairIndexedTwoAwayThreatCodeWeight_eq _ _
    _ ≤ ∑ j : IndexedThreatOrder q,
        (aggregatePairExactBankExtensionCoefficient q j.1 B : ℕ) *
          (Fintype.card V + 1 : ℝ≥0) ^ 2 := by
      apply sum_le_sum
      intro j _hj
      exact extensionWeight_aggregatePairFamily_absorberInduced_le A j
    _ = (aggregatePairTwoAwayThreatExtensionCoefficient q B : ℕ) *
        (Fintype.card V + 1 : ℝ≥0) ^ 2 := by
      simp [aggregatePairTwoAwayThreatExtensionCoefficient, sum_mul]

end

end Erdos207
