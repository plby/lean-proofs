/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PairSharingCount
import ErdosProblems.Erdos207.RootedThreatAbsorberBound

/-!
# Order-four rooted absorber threats

The indexed absorber argument begins at order five.  The only remaining
minimal configurations have two triples on at most four vertices.  Hence the
two triples share a pair, leaving only linearly many possible second triples.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

/-- The complementary, necessarily order-four, rooted witness family. -/
abbrev FourRootedThreatWitness
    (V : Type*) [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) (u v : V) :=
  {z : RootedThreatWitness V
      (absorberErdosForbiddenConfigurationsOn q B) u v //
    ¬ IsIndexedRootedThreatWitness q B u v z}

/-- The order-four branch is empty: two triples on at most four vertices
share a pair, whereas every configuration retained in the absorber-induced
forbidden family is a packing. -/
lemma fourRootedThreatWitness_isEmpty
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {u v : V}
    (z : FourRootedThreatWitness V q B u v) : False := by
  obtain ⟨_ne, r, hr4, _hrq, E, hE, hEpacking, hEout⟩ :=
    mem_absorberErdosForbiddenConfigurationsOn_iff.mp z.1.2.1
  have hr : r = 4 := by
    by_contra hrne
    apply z.2
    apply mem_absorberInducedConfigurationsOn_iff.mpr
    exact ⟨by omega, r, by omega, by assumption, E, hE, hEout⟩
  subst r
  exact hEpacking.no_four_config ⟨E, Subset.rfl, hE.1⟩

instance instIsEmptyFourRootedThreatWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {u v : V} :
    IsEmpty (FourRootedThreatWitness V q B u v) :=
  ⟨fourRootedThreatWitness_isEmpty⟩

lemma fourRootedThreat_order_four_data
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {u v : V}
    (z : FourRootedThreatWitness V q B u v) :
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

lemma fourRootedThreat_remainder_card_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {u v : V}
    (z : FourRootedThreatWitness V q B u v) :
    (rootedThreatRemainder z.1).card ≤ 1 := by
  obtain ⟨E, hE, hEout⟩ := fourRootedThreat_order_four_data z
  have hSsubE : z.1.1.1 ⊆ E := by
    rw [← hEout]
    exact sdiff_subset
  have hScard := card_le_card hSsubE
  have hEcard := hE.1.1
  rw [rootedThreatRemainder, card_erase_of_mem z.1.2.2.1]
  omega

lemma four_erdos_pair_inter_card
    {V : Type*} [DecidableEq V] {E : TripleSystemOn V}
    (hE : IsErdosConfigOn 4 E) {T U : TripleOn V}
    (hTE : T ∈ E) (hUE : U ∈ E) (hTU : T ≠ U) :
    2 ≤ (T.1 ∩ U.1).card := by
  have hpair : ({T, U} : TripleSystemOn V) ⊆ E := by
    intro W hW
    simp only [mem_insert, mem_singleton] at hW
    rcases hW with rfl | rfl
    · exact hTE
    · exact hUE
  have hspan := card_le_card (verticesOn_mono hpair)
  have hEspan := hE.1.2
  have hvertices :
      verticesOn ({T, U} : TripleSystemOn V) = T.1 ∪ U.1 := by
    simp [verticesOn]
  rw [hvertices] at hspan
  have hunion : (T.1 ∪ U.1).card ≤ 4 := hspan.trans hEspan
  have hcount := card_union_add_card_inter T.1 U.1
  have hTcard := T.2
  have hUcard := U.2
  omega

lemma fourRootedThreat_remainder_shares_pair
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {u v : V}
    (z : FourRootedThreatWitness V q B u v)
    {U : TripleOn V} (hU : U ∈ rootedThreatRemainder z.1) :
    U ∈ triplesSharingPair z.1.1.2 := by
  obtain ⟨E, hE, hEout⟩ := fourRootedThreat_order_four_data z
  have hSsubE : z.1.1.1 ⊆ E := by
    rw [← hEout]
    exact sdiff_subset
  have hUerase := mem_erase.mp hU
  apply mem_triplesSharingPair_iff.mpr
  exact four_erdos_pair_inter_card hE
    (hSsubE z.1.2.2.1) (hSsubE hUerase.2) hUerase.1.symm

/-- A uniform finite code for a possible second triple. -/
noncomputable def sharingPairEmbedding
    (V : Type*) [Fintype V] [DecidableEq V] (T : TripleOn V) :
    {U : TripleOn V // U ∈ triplesSharingPair T} ↪ Fin 3 × V := by
  classical
  exact (Function.Embedding.nonempty_of_card_le (by
    simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin] using
      card_triplesSharingPair_le V T)).some

/-- Code consisting of the designated rooted triple and, if present, the
encoded unique remainder triple. -/
abbrev FourRootedThreatCode
    (V : Type*) [Fintype V] [DecidableEq V] (u v : V) :=
  universeTriplesThroughPair u v × Option (Fin 3 × V)

noncomputable def fourRootedThreatCode
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {u v : V}
    (z : FourRootedThreatWitness V q B u v) :
    FourRootedThreatCode V u v :=
  (⟨z.1.1.2, mem_universeTriplesThroughPair_iff.mpr
      ⟨z.1.2.2.2.1, z.1.2.2.2.2⟩⟩,
    if h : (rootedThreatRemainder z.1).Nonempty then
      some (sharingPairEmbedding V z.1.1.2
        ⟨h.choose, fourRootedThreat_remainder_shares_pair z h.choose_spec⟩)
    else none)

lemma sharingPairEmbedding_eq_of_root_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {T W U X : TripleOn V}
    (hTW : T = W) (hU : U ∈ triplesSharingPair T)
    (hX : X ∈ triplesSharingPair W)
    (hcode : sharingPairEmbedding V T ⟨U, hU⟩ =
      sharingPairEmbedding V W ⟨X, hX⟩) :
    U = X := by
  subst W
  exact congrArg Subtype.val
    ((sharingPairEmbedding V T).injective hcode)

lemma fourRootedThreatCode_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {u v : V} :
    Function.Injective
      (fourRootedThreatCode : FourRootedThreatWitness V q B u v →
        FourRootedThreatCode V u v) := by
  classical
  intro z w hzw
  have hT : z.1.1.2 = w.1.1.2 :=
    congrArg (fun c ↦ c.1.1) hzw
  have hopen : (fourRootedThreatCode z).2 =
      (fourRootedThreatCode w).2 := congrArg Prod.snd hzw
  have hzcard := fourRootedThreat_remainder_card_le_one z
  have hwcard := fourRootedThreat_remainder_card_le_one w
  have hrem : rootedThreatRemainder z.1 = rootedThreatRemainder w.1 := by
    by_cases hz : (rootedThreatRemainder z.1).Nonempty
    · by_cases hw : (rootedThreatRemainder w.1).Nonempty
      · simp only [fourRootedThreatCode, hz, hw, dite_true,
          Option.some.injEq] at hopen
        have hchoose : hz.choose = hw.choose := by
          exact sharingPairEmbedding_eq_of_root_eq hT
            (fourRootedThreat_remainder_shares_pair z hz.choose_spec)
            (fourRootedThreat_remainder_shares_pair w hw.choose_spec) hopen
        ext U
        constructor
        · intro hUz
          have := (card_le_one.mp hzcard) U hUz hz.choose hz.choose_spec
          rw [this, hchoose]
          exact hw.choose_spec
        · intro hUw
          have := (card_le_one.mp hwcard) U hUw hw.choose hw.choose_spec
          rw [this, ← hchoose]
          exact hz.choose_spec
      · simp only [fourRootedThreatCode, hz, hw, dite_true, dite_false] at hopen
        exact (Option.some_ne_none _ hopen).elim
    · have hzempty : rootedThreatRemainder z.1 = ∅ :=
        not_nonempty_iff_eq_empty.mp hz
      by_cases hw : (rootedThreatRemainder w.1).Nonempty
      · simp only [fourRootedThreatCode, hz, hw, dite_true, dite_false] at hopen
        exact (Option.some_ne_none _ hopen.symm).elim
      · have hwempty : rootedThreatRemainder w.1 = ∅ :=
          not_nonempty_iff_eq_empty.mp hw
        exact hzempty.trans hwempty.symm
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · calc
      z.1.1.1 = insert z.1.1.2 (rootedThreatRemainder z.1) :=
        (insert_erase z.1.2.2.1).symm
      _ = insert w.1.1.2 (rootedThreatRemainder w.1) := by
        rw [hT, hrem]
      _ = w.1.1.1 := insert_erase w.1.2.2.1
  · exact hT

lemma finset_eq_singleton_choose_of_card_le_one
    {α : Type*} [DecidableEq α] {S : Finset α}
    (hS : S.Nonempty) (hcard : S.card ≤ 1) :
    S = {hS.choose} := by
  ext x
  constructor
  · intro hx
    have hxeq := (card_le_one.mp hcard) x hx hS.choose hS.choose_spec
    simpa only [mem_singleton] using hxeq
  · intro hx
    have hxeq : x = hS.choose := by
      simpa only [mem_singleton] using hx
    simpa only [hxeq] using hS.choose_spec

/-- A code weight which remembers exactly the one code compatible with a
nonempty singleton root, while using the constant point weight for the empty
root. -/
noncomputable def fourRootedThreatCodeWeight
    {V : Type*} [Fintype V] [DecidableEq V] {u v : V}
    (p : ℝ≥0) (A : TripleSystemOn V)
    (c : FourRootedThreatCode V u v) : ℝ≥0 :=
  if A = ∅ then
    match c.2 with
    | none => 1
    | some _ => p
  else if ∃ U : {U : TripleOn V // U ∈ triplesSharingPair c.1.1},
      A = {U.1} ∧
        c.2 = some (sharingPairEmbedding V c.1.1 U) then 1 else 0

theorem fourRootedThreat_weight_le_code
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {u v : V}
    (p : ℝ≥0) (A : TripleSystemOn V) :
    extensionWeight
        (fun z : FourRootedThreatWitness V q B u v ↦
          rootedThreatRemainder z.1)
        (constantTripleWeight p) A ≤
      ∑ c : FourRootedThreatCode V u v,
        fourRootedThreatCodeWeight p A c := by
  classical
  apply sum_le_sum_of_injective_code fourRootedThreatCode
    fourRootedThreatCode_injective
  intro z
  by_cases hsub : A ⊆ rootedThreatRemainder z.1
  · rw [if_pos hsub]
    by_cases hA : A = ∅
    · subst A
      by_cases hrem : (rootedThreatRemainder z.1).Nonempty
      · have hremEq := finset_eq_singleton_choose_of_card_le_one hrem
          (fourRootedThreat_remainder_card_le_one z)
        have hleft :
            setWeight (constantTripleWeight p)
              (rootedThreatRemainder z.1 \ ∅) = p := by
          rw [hremEq]
          simp [setWeight, constantTripleWeight]
        rw [hleft]
        unfold fourRootedThreatCodeWeight fourRootedThreatCode
        simp only [if_true, hrem, dite_true]
        exact le_rfl
      · have hremEq : rootedThreatRemainder z.1 = ∅ :=
          not_nonempty_iff_eq_empty.mp hrem
        simp [fourRootedThreatCodeWeight, fourRootedThreatCode,
          hrem, hremEq, setWeight]
    · have hAnonempty : A.Nonempty := nonempty_iff_ne_empty.mpr hA
      have hrem : (rootedThreatRemainder z.1).Nonempty :=
        hAnonempty.mono hsub
      have hremEq := finset_eq_singleton_choose_of_card_le_one hrem
        (fourRootedThreat_remainder_card_le_one z)
      have hAEq : A = {hrem.choose} := by
        ext W
        constructor
        · intro hWA
          have hWrem : W ∈ rootedThreatRemainder z.1 := hsub hWA
          have hWeq := (card_le_one.mp
            (fourRootedThreat_remainder_card_le_one z))
              W hWrem hrem.choose hrem.choose_spec
          simpa only [mem_singleton] using hWeq
        · intro hW
          have hWeq : W = hrem.choose := by
            simpa only [mem_singleton] using hW
          obtain ⟨Y, hYA⟩ := hAnonempty
          have hYrem : Y ∈ rootedThreatRemainder z.1 := hsub hYA
          have hYeq := (card_le_one.mp
            (fourRootedThreat_remainder_card_le_one z))
              Y hYrem hrem.choose hrem.choose_spec
          simpa only [hWeq, ← hYeq] using hYA
      have hdiff : rootedThreatRemainder z.1 \ A = ∅ := by
        apply sdiff_eq_empty_iff_subset.mpr
        intro W hW
        rw [hAEq, mem_singleton]
        exact (card_le_one.mp (fourRootedThreat_remainder_card_le_one z))
          W hW hrem.choose hrem.choose_spec
      rw [hdiff]
      simp only [setWeight, prod_empty]
      unfold fourRootedThreatCodeWeight
      rw [if_neg hA]
      rw [if_pos (by
        refine ⟨⟨hrem.choose,
          fourRootedThreat_remainder_shares_pair z hrem.choose_spec⟩,
          hAEq, ?_⟩
        simp [fourRootedThreatCode, hrem]
        congr)]
  · simp [hsub]

lemma card_mul_inv_add_one_le_one (n : ℕ) :
    (n : ℝ≥0) * (((n + 1 : ℕ) : ℝ≥0)⁻¹) ≤ 1 := by
  have hpos : (0 : ℝ≥0) < ((n + 1 : ℕ) : ℝ≥0) := by positivity
  apply (mul_inv_le_iff₀ hpos).2
  exact_mod_cast (show n ≤ 1 * (n + 1) by omega)

theorem sum_fourRootedThreatCodeWeight_fiber_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {u v : V} (T : universeTriplesThroughPair u v)
    (A : TripleSystemOn V) :
    (∑ o : Option (Fin 3 × V),
      fourRootedThreatCodeWeight
        ((Fintype.card V + 1 : ℝ≥0)⁻¹) A (T, o)) ≤ 4 := by
  classical
  let p : ℝ≥0 := (Fintype.card V + 1 : ℝ≥0)⁻¹
  by_cases hA : A = ∅
  · subst A
    simp only [fourRootedThreatCodeWeight, if_pos rfl,
      Fintype.sum_option]
    have hnp : (Fintype.card V : ℝ≥0) * p ≤ 1 := by
      dsimp only [p]
      simpa only [Nat.cast_add, Nat.cast_one] using
        card_mul_inv_add_one_le_one (Fintype.card V)
    calc
      1 + ∑ _x : Fin 3 × V, p =
          1 + (3 : ℝ≥0) * ((Fintype.card V : ℝ≥0) * p) := by
        simp only [sum_const, card_univ, Fintype.card_prod,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
        ring
      _ ≤ 1 + (3 : ℝ≥0) * 1 := by gcongr
      _ = 4 := by norm_num
  · by_cases hex : ∃ U : {U : TripleOn V // U ∈ triplesSharingPair T.1},
        A = {U.1}
    · obtain ⟨U₀, hAU₀⟩ := hex
      have hpredicate : ∀ o : Option (Fin 3 × V),
          (∃ U : {U : TripleOn V // U ∈ triplesSharingPair T.1},
            A = {U.1} ∧
              o = some (sharingPairEmbedding V T.1 U)) ↔
            o = some (sharingPairEmbedding V T.1 U₀) := by
        intro o
        constructor
        · rintro ⟨U, hAU, ho⟩
          have hval : U.1 = U₀.1 := by
            have hs : ({U.1} : TripleSystemOn V) = {U₀.1} :=
              hAU.symm.trans hAU₀
            simpa only [singleton_inj] using hs
          have hU : U = U₀ := Subtype.ext hval
          simpa only [hU] using ho
        · intro ho
          exact ⟨U₀, hAU₀, ho⟩
      simp only [fourRootedThreatCodeWeight, hA, if_false]
      simp_rw [hpredicate]
      simp
    · have hpredicate : ∀ o : Option (Fin 3 × V),
          ¬ ∃ U : {U : TripleOn V // U ∈ triplesSharingPair T.1},
            A = {U.1} ∧
              o = some (sharingPairEmbedding V T.1 U) := by
        intro o h
        exact hex ⟨h.choose, h.choose_spec.1⟩
      simp [fourRootedThreatCodeWeight, hA, hpredicate]

/-- The order-four portion has a linear extension bound. -/
theorem extensionWeight_fourRootedThreat_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {u v : V}
    (huv : u ≠ v) (A : TripleSystemOn V) :
    extensionWeight
        (fun z : FourRootedThreatWitness V q B u v ↦
          rootedThreatRemainder z.1)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) A ≤
      ((Fintype.card V * 4 : ℕ) : ℝ≥0) := by
  calc
    extensionWeight
        (fun z : FourRootedThreatWitness V q B u v ↦
          rootedThreatRemainder z.1)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) A ≤
      ∑ c : FourRootedThreatCode V u v,
        fourRootedThreatCodeWeight
          ((Fintype.card V + 1 : ℝ≥0)⁻¹) A c :=
      fourRootedThreat_weight_le_code _ A
    _ = ∑ T : universeTriplesThroughPair u v,
        ∑ o : Option (Fin 3 × V),
          fourRootedThreatCodeWeight
            ((Fintype.card V + 1 : ℝ≥0)⁻¹) A (T, o) := by
      rw [Fintype.sum_prod_type]
    _ ≤ ∑ _T : universeTriplesThroughPair u v, (4 : ℝ≥0) := by
      apply sum_le_sum
      intro T _hT
      exact sum_fourRootedThreatCodeWeight_fiber_le T A
    _ = ((Fintype.card (universeTriplesThroughPair u v) * 4 : ℕ) : ℝ≥0) := by
      simp only [sum_const, card_univ, nsmul_eq_mul, Nat.cast_mul]
      norm_num
    _ ≤ ((Fintype.card V * 4 : ℕ) : ℝ≥0) := by
      exact_mod_cast Nat.mul_le_mul_right 4 (by
        simpa only [Fintype.card_coe] using
          card_universeTriplesThroughPair_le V huv)

end Erdos207
