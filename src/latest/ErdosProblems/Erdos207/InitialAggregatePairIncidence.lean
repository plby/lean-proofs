/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PairAggregateTwoAwayAbsorberBound
import ErdosProblems.Erdos207.PairAggregateTwoAwayThreatWeight

/-!
# Linear initial aggregate pair incidence

At the empty chosen family, an aggregate two-away witness has only its two
designated outside triangles.  In an exact bank class, fixing the triangle
through the tracked pair leaves an `r - 3`-triangle root of an Erdős
configuration.  Minimality forces that root to span all `r` vertices, so the
last triangle has only constantly many choices.  This removes the spurious
quadratic ambient factor from the generic extension-weight bound at time zero.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- At outside size four and empty planted root, fixing one outside triangle
leaves only a constant number of exact-bank completions. -/
lemma card_exactBankOutsideExtensionsThrough_four_empty_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} {B K : TripleSystemOn V} {T : TripleOn V}
    (hr : 5 ≤ r) :
    (exactBankOutsideExtensionsThrough r 4 B ∅ K T).card ≤ 2 ^ (r ^ 3) := by
  classical
  by_cases hne : (exactBankOutsideExtensionsThrough r 4 B ∅ K T).Nonempty
  · obtain ⟨S, hS⟩ := hne
    obtain ⟨hSexact, hTS, _hTempty⟩ :=
      mem_exactBankOutsideExtensionsThrough_iff.mp hS
    obtain ⟨hScard, _hemptyS, E, hE, hEout, hEin⟩ :=
      mem_exactBankOutsideExtensions_iff.mp hSexact
    have hTnotB : T ∉ B := by
      have hTdiff : T ∈ E \ B := by simpa only [hEout] using hTS
      exact (mem_sdiff.mp hTdiff).2
    have hTK : T ∉ K := by
      intro hTK
      apply hTnotB
      have hKsubB : K ⊆ B := by
        rw [← hEin]
        exact inter_subset_right
      exact hKsubB hTK
    have hKcard : K.card = r - 4 := by
      have hcardE := card_sdiff_add_card_inter E B
      rw [hEout, hEin, hScard, hE.1.1] at hcardE
      omega
    let R : TripleSystemOn V := insert T ∅ ∪ K
    have hRcard : R.card = r - 3 := by
      dsimp only [R]
      simp only [insert_empty_eq, singleton_union]
      rw [card_insert_of_notMem hTK, hKcard]
      omega
    have hRsubE : R ⊆ E := by
      intro U hU
      rcases mem_union.mp hU with hUT | hUK
      · have hUT' : U = T := by simpa using hUT
        subst U
        have hTdiff : T ∈ E \ B := by simpa only [hEout] using hTS
        exact (mem_sdiff.mp hTdiff).1
      · have hUinter : U ∈ E ∩ B := by simpa only [hEin] using hUK
        exact (mem_inter.mp hUinter).1
    have hRtwo : 2 ≤ R.card := by rw [hRcard]; omega
    have hRsmall : R.card ≤ r - 3 := by rw [hRcard]
    have hRspanLower : r ≤ (verticesOn R).card := by
      have hs := IsErdosConfig.subset_span hE hRsubE hRtwo hRsmall
      rw [hRcard] at hs
      omega
    have hRspanUpper : (verticesOn R).card ≤ r := by
      calc
        (verticesOn R).card ≤ (verticesOn E).card :=
          card_le_card (verticesOn_mono hRsubE)
        _ = r := IsErdosConfig.vertices_card_eq hE hr
    have hRspan : (verticesOn R).card = r := Nat.le_antisymm hRspanUpper hRspanLower
    calc
      (exactBankOutsideExtensionsThrough r 4 B ∅ K T).card ≤
          2 ^ (r ^ 3) *
            ((r - (verticesOn (insert T ∅ ∪ K)).card + 1) *
              (((univ \ verticesOn (insert T ∅ ∪ K) : Finset V).card + 1) ^
                (r - (verticesOn (insert T ∅ ∪ K)).card))) :=
        card_exactBankOutsideExtensionsThrough_le hr
      _ = 2 ^ (r ^ 3) := by
        change 2 ^ (r ^ 3) *
          ((r - (verticesOn R).card + 1) *
            (((univ \ verticesOn R : Finset V).card + 1) ^
              (r - (verticesOn R).card))) = _
        rw [hRspan]
        simp
  · rw [not_nonempty_iff_eq_empty.mp hne]
    simp

/-- The ambient-independent coefficient in the linear time-zero aggregate
incidence bound. -/
noncomputable def initialAggregatePairTwoAwayCoefficient
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) : ℕ :=
  ∑ r : (Icc 5 q : Finset ℕ), ∑ _K : subsetsUpToCard B q,
    2 * 2 ^ (r.1 ^ 3)

/-- For outside size four, the empty-root aggregate witness family is only
linear in the ambient order. -/
lemma card_activeAggregatePair_absorberInduced_four_empty_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} (P : PairOn V) :
    Fintype.card (ActiveAggregatePairFamilyTwoAwayWitness
        (absorberInducedConfigurationsOn q 4 B) P ∅) ≤
      initialAggregatePairTwoAwayCoefficient q B * Fintype.card V := by
  classical
  apply (card_activeAggregatePair_absorberInduced_le_exact_sum
    (q := q) (j := 4) (B := B) (P := P) ∅).trans
  calc
    (∑ r : (Icc 5 q : Finset ℕ), ∑ K : subsetsUpToCard B q,
        Fintype.card (ActiveAggregatePairFamilyTwoAwayWitness
          (exactBankOutsideExtensions r.1 4 B ∅ K.1) P ∅)) ≤
      ∑ r : (Icc 5 q : Finset ℕ), ∑ _K : subsetsUpToCard B q,
        2 * 2 ^ (r.1 ^ 3) * Fintype.card V := by
      apply sum_le_sum
      intro r _hr
      apply sum_le_sum
      intro K _hK
      have hactive := card_activeAggregatePairExact_le
        (r := r.1) (j := 4) (B := B) (K := K.1) (P := P) ∅
      calc
        Fintype.card (ActiveAggregatePairFamilyTwoAwayWitness
            (exactBankOutsideExtensions r.1 4 B ∅ K.1) P ∅) ≤
          (4 - 2) * ∑ T : universeTriplesContainingPair P.1,
            (exactBankOutsideExtensionsThrough r.1 4 B ∅ K.1 T.1).card :=
          hactive
        _ ≤ 2 * ∑ _T : universeTriplesContainingPair P.1,
            2 ^ (r.1 ^ 3) := by
          gcongr
          exact card_exactBankOutsideExtensionsThrough_four_empty_le
            (mem_Icc.mp r.2).1
        _ = 2 * (universeTriplesContainingPair P.1).card *
            2 ^ (r.1 ^ 3) := by simp [mul_assoc]
        _ ≤ 2 * Fintype.card V * 2 ^ (r.1 ^ 3) := by
          gcongr
          exact card_universeTriplesContainingPair_le V P.1 P.2
        _ = 2 * 2 ^ (r.1 ^ 3) * Fintype.card V := by ring
    _ = initialAggregatePairTwoAwayCoefficient q B * Fintype.card V := by
      unfold initialAggregatePairTwoAwayCoefficient
      simp only [sum_mul]

lemma setWeight_zero_eq
    {W : Type*} [DecidableEq W] (S : Finset W) :
    setWeight (fun _ : W ↦ (0 : ℝ≥0)) S = if S = ∅ then 1 else 0 := by
  classical
  by_cases h : S = ∅ <;> simp [setWeight, h]

lemma selectedCount_empty_eq_extensionWeight_zero
    {W I : Type*} [DecidableEq W] [Fintype I]
    (F : I → Finset W) :
    selectedCount F ∅ =
      extensionWeight F (fun _ ↦ (0 : ℝ≥0)) ∅ := by
  classical
  unfold selectedCount extensionWeight
  apply sum_congr rfl
  intro i _hi
  by_cases h : F i = ∅ <;> simp [h, setWeight]

/-- Under zero point weights, every aggregate indexed code vanishes except
the outside-size-four class. -/
lemma sum_aggregatePairIndexedTwoAwayThreatCodeWeight_zero_empty_le_four
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} (P : PairOn V) (hq : 4 ≤ q) :
    (∑ c : AggregatePairIndexedTwoAwayThreatCode V q B P,
      aggregatePairIndexedTwoAwayThreatCodeWeight
        (constantTripleWeight 0) ∅ c) ≤
      Fintype.card (ActiveAggregatePairFamilyTwoAwayWitness
        (absorberInducedConfigurationsOn q 4 B) P ∅) := by
  classical
  let j4 : IndexedThreatOrder q := ⟨4, mem_Icc.mpr ⟨by omega, hq⟩⟩
  rw [sum_aggregatePairIndexedTwoAwayThreatCodeWeight_eq]
  rw [Finset.sum_eq_single j4]
  · rw [extensionWeight_aggregatePairFamilyTwoAway_eq
      (m := 4 - 2) absorberInducedConfigurationsOn_fixed_card]
    simp
  · intro j _hj hjne
    rw [extensionWeight_aggregatePairFamilyTwoAway_eq
      (m := j.1 - 2) absorberInducedConfigurationsOn_fixed_card]
    by_cases hj3 : j.1 = 3
    · have hempty : IsEmpty (ActiveAggregatePairFamilyTwoAwayWitness
          (absorberInducedConfigurationsOn q j.1 B) P ∅) := by
        constructor
        intro z
        have htwo : 1 < z.1.2.1.family.card := one_lt_card.mpr
          ⟨z.1.1, z.1.2.1.fixed_mem, z.1.2.1.missing,
            z.1.2.1.missing_mem, z.1.2.1.missing_ne.symm⟩
        rw [absorberInducedConfigurationsOn_fixed_card
          z.1.2.1.family z.1.2.1.family_mem, hj3] at htwo
        omega
      letI := hempty
      simp
    · have hj5 : 5 ≤ j.1 := by
        have hjlower := (mem_Icc.mp j.2).1
        have hjnot4 : j.1 ≠ 4 := by
          intro h
          apply hjne
          apply Subtype.ext
          simpa [j4] using h
        omega
      have hexp : j.1 - 2 - 2 ≠ 0 := by omega
      simp only [card_empty, Nat.sub_zero]
      rw [zero_pow hexp, mul_zero]
  · simp

/-- The exact time-zero aggregate pair count is bounded linearly in the
ambient order. -/
lemma selectedCount_aggregatePairTwoAway_empty_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} (P : PairOn V) (hq : 4 ≤ q) :
    selectedCount
        (fun z : AggregatePairTwoAwayThreatWitness V
            (absorberErdosForbiddenConfigurationsOn q B) P ↦
          aggregatePairTwoAwayThreatRemainder z) ∅ ≤
      initialAggregatePairTwoAwayCoefficient q B * Fintype.card V := by
  rw [selectedCount_empty_eq_extensionWeight_zero]
  calc
    extensionWeight
        (fun z : AggregatePairTwoAwayThreatWitness V
            (absorberErdosForbiddenConfigurationsOn q B) P ↦
          aggregatePairTwoAwayThreatRemainder z)
        (constantTripleWeight 0) ∅ ≤
      ∑ c : AggregatePairIndexedTwoAwayThreatCode V q B P,
        aggregatePairIndexedTwoAwayThreatCodeWeight
          (constantTripleWeight 0) ∅ c :=
      aggregatePairTwoAwayThreat_weight_le_indexedCode _ _
    _ ≤ Fintype.card (ActiveAggregatePairFamilyTwoAwayWitness
        (absorberInducedConfigurationsOn q 4 B) P ∅) :=
      sum_aggregatePairIndexedTwoAwayThreatCodeWeight_zero_empty_le_four P hq
    _ ≤ initialAggregatePairTwoAwayCoefficient q B * Fintype.card V := by
      exact_mod_cast card_activeAggregatePair_absorberInduced_four_empty_le P

/-- Linear deterministic pair-star incidence cutoff for the empty absorber
state. -/
theorem hasPairStarTwoAwayIncidenceCutoff_absorber_of_chosen_empty_linear
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {S : GreedyStateOn V}
    (hq : 4 ≤ q) (hchosen : S.chosen = ∅) :
    HasPairStarTwoAwayIncidenceCutoff
      (absorberErdosForbiddenConfigurationsOn q B)
      (initialAggregatePairTwoAwayCoefficient q B * Fintype.card V) S := by
  intro P hPcard
  let P' : PairOn V := ⟨P, hPcard⟩
  have hcount := pairStarAvailableTwoAwayIncidences_le_selectedCount
    (absorberErdosForbiddenConfigurationsOn q B) S P'
  have hext : selectedCount
        (fun z : AggregatePairTwoAwayThreatWitness V
            (absorberErdosForbiddenConfigurationsOn q B) P' ↦
          aggregatePairTwoAwayThreatRemainder z) S.chosen ≤
      (initialAggregatePairTwoAwayCoefficient q B * Fintype.card V : ℕ) := by
    rw [hchosen]
    simpa only [Nat.cast_mul] using
      selectedCount_aggregatePairTwoAway_empty_le (B := B) P' hq
  exact_mod_cast hcount.trans hext

end

end Erdos207
