/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RootedThreatFourBound
import ErdosProblems.Erdos207.VortexPairWeight

/-!
# Order-four rooted-threat weights in a vortex

The unique remainder of an order-four rooted witness shares a pair with its
designated triangle.  A point-weighted version of the finite code therefore
reduces the empty-root extension sum to a weighted pair star.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Since the packing-filtered forbidden family has no order-four member,
its order-four rooted extension weight is identically zero for every point
weight and every planted root. -/
theorem fourRootedThreatRemainder_hasExtensionBound_zero
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (B : TripleSystemOn V) (p : TripleOn V → ℝ≥0) {u v : V} :
    HasExtensionBound
      (fun z : FourRootedThreatWitness V q B u v ↦
        rootedThreatRemainder z.1)
      p 0 := by
  intro A
  unfold extensionWeight
  have hzero :
      (∑ z : FourRootedThreatWitness V q B u v,
        if A ⊆ rootedThreatRemainder z.1 then
          setWeight p (rootedThreatRemainder z.1 \ A) else 0) = 0 := by
    apply sum_eq_zero
    intro z _hz
    exact (fourRootedThreatWitness_isEmpty z).elim
  rw [hzero]

/-- Point-weighted code weight for an order-four rooted witness. -/
def fourRootedThreatPointCodeWeight
    {V : Type*} [Fintype V] [DecidableEq V] {u v : V}
    (p : TripleOn V → ℝ≥0) (A : TripleSystemOn V)
    (c : FourRootedThreatCode V u v) : ℝ≥0 :=
  if A = ∅ then
    match c.2 with
    | none => 1
    | some x =>
        ∑ U : {U : TripleOn V // U ∈ triplesSharingPair c.1.1},
          if sharingPairEmbedding V c.1.1 U = x then p U.1 else 0
  else if ∃ U : {U : TripleOn V // U ∈ triplesSharingPair c.1.1},
      A = {U.1} ∧
        c.2 = some (sharingPairEmbedding V c.1.1 U) then 1 else 0

/-- The injective order-four code dominates the point-weighted extension
sum. -/
theorem fourRootedThreat_pointWeight_le_code
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {u v : V}
    (p : TripleOn V → ℝ≥0) (A : TripleSystemOn V) :
    extensionWeight
        (fun z : FourRootedThreatWitness V q B u v ↦
          rootedThreatRemainder z.1)
        p A ≤
      ∑ c : FourRootedThreatCode V u v,
        fourRootedThreatPointCodeWeight p A c := by
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
            setWeight p (rootedThreatRemainder z.1 \ ∅) = p hrem.choose := by
          calc
            setWeight p (rootedThreatRemainder z.1 \ ∅) =
                setWeight p {hrem.choose} := by
              congr 1
              simpa only [sdiff_empty] using hremEq
            _ = p hrem.choose := by
              simp only [setWeight, prod_singleton]
        rw [hleft]
        unfold fourRootedThreatPointCodeWeight fourRootedThreatCode
        simp only [if_true, hrem, dite_true]
        let U : {U : TripleOn V // U ∈ triplesSharingPair z.1.1.2} :=
          ⟨hrem.choose,
            fourRootedThreat_remainder_shares_pair z hrem.choose_spec⟩
        have hsum :
            (∑ X : {X : TripleOn V // X ∈ triplesSharingPair z.1.1.2},
              if sharingPairEmbedding V z.1.1.2 X =
                  sharingPairEmbedding V z.1.1.2 U then p X.1 else 0) =
              p U.1 := by
          rw [Finset.sum_eq_single U]
          · simp
          · intro X hX hXne
            have hne : sharingPairEmbedding V z.1.1.2 X ≠
                sharingPairEmbedding V z.1.1.2 U := by
              intro heq
              exact hXne ((sharingPairEmbedding V z.1.1.2).injective heq)
            simp [hne]
          · simp
        have hcode : sharingPairEmbedding V z.1.1.2 U =
            sharingPairEmbedding V z.1.1.2
              ⟨hrem.choose,
                fourRootedThreat_remainder_shares_pair z hrem.choose_spec⟩ := by
          congr
        rw [← hcode, hsum]
      · have hremEq : rootedThreatRemainder z.1 = ∅ :=
          not_nonempty_iff_eq_empty.mp hrem
        simp [fourRootedThreatPointCodeWeight, fourRootedThreatCode,
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
      unfold fourRootedThreatPointCodeWeight
      rw [if_neg hA]
      rw [if_pos (by
        refine ⟨⟨hrem.choose,
          fourRootedThreat_remainder_shares_pair z hrem.choose_spec⟩,
          hAEq, ?_⟩
        simp [fourRootedThreatCode, hrem]
        congr)]
  · simp [hsub]

/-- One fixed designated triangle contributes one empty-remainder code plus
the vortex weight of its pair-sharing remainder choices. -/
theorem sum_fourRootedThreatPointCodeWeight_fiber_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (c : ℝ≥0)
    {u v : V} (T : universeTriplesThroughPair u v)
    (A : TripleSystemOn V) :
    (∑ o : Option (Fin 3 × V),
      fourRootedThreatPointCodeWeight
        (vortexTripleWeight W c) A (T, o)) ≤
      1 + 3 * ((ell + 1 : ℕ) * c) := by
  classical
  by_cases hA : A = ∅
  · subst A
    simp only [fourRootedThreatPointCodeWeight, if_pos rfl,
      Fintype.sum_option]
    calc
      (1 : ℝ≥0) + (∑ x : Fin 3 × V,
          ∑ U : {U : TripleOn V // U ∈ triplesSharingPair T.1},
            if sharingPairEmbedding V T.1 U = x then
              vortexTripleWeight W c U.1 else 0) =
          (1 : ℝ≥0) + (∑ U : {U : TripleOn V // U ∈ triplesSharingPair T.1},
            ∑ x : Fin 3 × V,
              if sharingPairEmbedding V T.1 U = x then
                vortexTripleWeight W c U.1 else 0) := by
        congr 1
        exact Finset.sum_comm
      _ = (1 : ℝ≥0) +
          (∑ U : {U : TripleOn V // U ∈ triplesSharingPair T.1},
            vortexTripleWeight W c U.1) := by
        congr 1
        apply sum_congr rfl
        intro U hU
        simp
      _ = (1 : ℝ≥0) + ∑ U ∈ triplesSharingPair T.1,
          vortexTripleWeight W c U := by
        congr 1
        exact (Finset.sum_subtype (triplesSharingPair T.1)
          (fun U ↦ by simp) (vortexTripleWeight W c)).symm
      _ ≤ 1 + 3 * ((ell + 1 : ℕ) * c) := by
        gcongr
        exact sum_vortexTripleWeight_triplesSharingPair_le W c T.1
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
      simp only [fourRootedThreatPointCodeWeight, hA, if_false]
      simp_rw [hpredicate]
      simp
    · have hpredicate : ∀ o : Option (Fin 3 × V),
          ¬ ∃ U : {U : TripleOn V // U ∈ triplesSharingPair T.1},
            A = {U.1} ∧
              o = some (sharingPairEmbedding V T.1 U) := by
        intro o h
        exact hex ⟨h.choose, h.choose_spec.1⟩
      simp [fourRootedThreatPointCodeWeight, hA, hpredicate]

/-- Uniform all-root extension bound for the order-four rooted family under
vortex point weights. -/
theorem fourRootedThreatRemainder_hasExtensionBound_vortex
    {V : Type*} [Fintype V] [DecidableEq V] {ell q : ℕ}
    (W : Vortex V ell) (B : TripleSystemOn V) (c : ℝ≥0)
    {u v : V} (huv : u ≠ v) :
    HasExtensionBound
      (fun z : FourRootedThreatWitness V q B u v ↦
        rootedThreatRemainder z.1)
      (vortexTripleWeight W c)
      ((Fintype.card V : ℝ≥0) *
        (1 + 3 * ((ell + 1 : ℕ) * c))) := by
  intro A
  calc
    extensionWeight
        (fun z : FourRootedThreatWitness V q B u v ↦
          rootedThreatRemainder z.1)
        (vortexTripleWeight W c) A ≤
      ∑ code : FourRootedThreatCode V u v,
        fourRootedThreatPointCodeWeight (vortexTripleWeight W c) A code :=
      fourRootedThreat_pointWeight_le_code _ A
    _ = ∑ T : universeTriplesThroughPair u v,
        ∑ o : Option (Fin 3 × V),
          fourRootedThreatPointCodeWeight
            (vortexTripleWeight W c) A (T, o) := by
      rw [Fintype.sum_prod_type]
    _ ≤ ∑ _T : universeTriplesThroughPair u v,
        (1 + 3 * ((ell + 1 : ℕ) * c)) := by
      apply sum_le_sum
      intro T hT
      exact sum_fourRootedThreatPointCodeWeight_fiber_le W c T A
    _ = (Fintype.card (universeTriplesThroughPair u v) : ℝ≥0) *
        (1 + 3 * ((ell + 1 : ℕ) * c)) := by
      rw [sum_const, card_univ]
      simp only [nsmul_eq_mul]
    _ ≤ (Fintype.card V : ℝ≥0) *
        (1 + 3 * ((ell + 1 : ℕ) * c)) := by
      gcongr
      exact_mod_cast (by
        simpa only [Fintype.card_coe] using
          card_universeTriplesThroughPair_le V huv)

end

end Erdos207
