/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Claim 2.2 and the resulting exclusion of all small rigid separations. -/

import ErdosProblems.Erdos717.ClaimTwo

open Function Set
open SimpleGraph

namespace Erdos717
namespace ThomasWollanMassed
namespace MassedCounterexample

variable {k : ℕ}

/-- Claim 2.2: a lexicographically minimal massed counterexample has no
rigid separation whose order is exactly `|X|`. -/
theorem noRigidSeparationEqual_of_lexMinimal
    (C : MassedCounterexample k) (hlex : C.IsLexMinimal) :
    ∀ s : Erdos718.Separation C.G,
      C.IsRigidSeparation s → s.separator.card = C.X.card → False := by
  classical
  have hbelow := noRigidSeparationBelow_of_lexMinimal C hlex
  intro s hsRigid hsOrder
  have hXleft : C.X ⊆ s.left := hsRigid.1
  let A : Set (s.left : Set C.V) := {x | (x : C.V) ∈ C.X}
  let B : Set (s.left : Set C.V) :=
    {x | (x : C.V) ∈ s.separator}
  let H := C.G.induce (s.left : Set C.V)
  obtain ⟨P₀, T, hP₀, hTcover, hcard, _hmax, hTmin⟩ :=
    Erdos718.finite_pathHypergraph_minmax H A B
  have hTsep : Erdos599.Countable.Separates H A B T :=
    Erdos599.Countable.isCover_pathHypergraph_iff.mp hTcover
  by_cases hlarge : C.X.card ≤ T.ncard
  · have hall : ∀ U, Erdos599.Countable.Separates H A B U →
        C.X.card ≤ U.ncard := by
      intro U hUsep
      exact hlarge.trans (hTmin U
        (Erdos599.Countable.isCover_pathHypergraph_iff.mpr hUsep))
    obtain ⟨P⟩ := Erdos718.exists_abLinkage_of_forall_separator_ncard_ge
      H A B C.X.card hall
    let PG : Erdos718.ABLinkage C.G (C.X : Set C.V)
        (s.separator : Set C.V) C.X.card :=
      Erdos718.ABLinkage.liftInduce P
    let PG' : Erdos718.ABLinkage C.G (C.X : Set C.V)
        (s.right : Set C.V) C.X.card := {
      left := PG.left
      right := PG.right
      path := PG.path
      left_mem := PG.left_mem
      right_mem := fun i => (Finset.mem_inter.mp (PG.right_mem i)).2
      isPath := PG.isPath
      disjoint := PG.disjoint
    }
    have PG'' : Erdos718.ABLinkage C.G (C.X : Set C.V)
        (s.right : Set C.V) (C.X : Set C.V).ncard := by
      simpa only [Set.ncard_coe_finset] using PG'
    have hlinked := isLinkedSet_of_full_abLinkage_to_linked_right
      s (C.X : Set C.V) C.X.finite_toSet hXleft PG'' hsRigid.2.2
    exact C.not_linked hlinked
  · have hTsmall : T.ncard < C.X.card := Nat.lt_of_not_ge hlarge
    obtain ⟨t₀, hAtLeft, hBtRight, ht₀Card⟩ :=
      exists_separation_of_path_separator_with_sides hTsep
    have hOldRight : ∀ x : (s.left : Set C.V),
        (x : C.V) ∈ s.separator → x ∈ t₀.right := by
      intro x hx
      exact hBtRight hx
    let t := separationInduceLeftToTorso s t₀ hOldRight
    have htCard : t.separator.card = T.ncard := by
      simpa only [t, separationInduceLeftToTorso_separator] using ht₀Card
    have htSmall : t.separator.card < C.X.card := by
      rw [htCard]
      exact hTsmall
    let Y : Set (t.right : Set (s.left : Set C.V)) :=
      (rightSeparator t : Set (t.right : Set (s.left : Set C.V)))
    let D : Set (t.right : Set (s.left : Set C.V)) :=
      {x | ((x : (s.left : Set C.V)) : C.V) ∈ s.separator}
    let K := (leftTorso s).induce (t.right : Set (s.left : Set C.V))
    have hcutLower : ∀ U, Erdos599.Countable.Separates K Y D U →
        t.separator.card ≤ U.ncard := by
      intro U hUsep
      obtain ⟨u, hYuLeft, hDuRight, huCard⟩ :=
        exists_separation_of_path_separator_with_sides hUsep
      have hYfin : rightSeparator t ⊆ u.left := by
        intro x hx
        exact hYuLeft hx
      let qT := composeRight t u hYfin
      let qH : Erdos718.Separation H :=
        separationOfLE (fun _ _ h => Or.inl h) qT
      have hAq : A ⊆ (qH.left : Set (s.left : Set C.V)) := by
        intro a ha
        have haT : a ∈ t.left := by
          change a ∈ t₀.left
          exact hAtLeft ha
        by_cases haR : a ∈ t.right
        · let aR : (t.right : Set (s.left : Set C.V)) := ⟨a, haR⟩
          have haY : aR ∈ rightSeparator t := by
            rw [mem_rightSeparator]
            exact Finset.mem_inter.mpr ⟨haT, haR⟩
          exact Finset.mem_union.mpr (Or.inr
            (Finset.mem_map.mpr ⟨aR, hYfin haY, rfl⟩))
        · exact Finset.mem_union.mpr (Or.inl
            (Finset.mem_sdiff.mpr ⟨haT, haR⟩))
      have hBq : B ⊆ (qH.right : Set (s.left : Set C.V)) := by
        intro b hb
        have hbR : b ∈ t.right := by
          change b ∈ t₀.right
          exact hOldRight b hb
        let bR : (t.right : Set (s.left : Set C.V)) := ⟨b, hbR⟩
        have hbD : bR ∈ D := hb
        exact Finset.mem_map.mpr ⟨bR, hDuRight hbD, rfl⟩
      have hqSep : Erdos599.Countable.Separates H A B
          (qH.separator : Set (s.left : Set C.V)) :=
        separation_separator_separates_of_subsets qH hAq hBq
      have hmin := hTmin (qH.separator : Set (s.left : Set C.V))
        (Erdos599.Countable.isCover_pathHypergraph_iff.mpr hqSep)
      have hqCard : qH.separator.card = u.separator.card := by
        exact composeRight_separator_card t u hYfin
      rw [Set.ncard_coe_finset, hqCard, huCard] at hmin
      rw [htCard]
      exact hmin
    obtain ⟨P⟩ := Erdos718.exists_abLinkage_of_forall_separator_ncard_ge
      K Y D t.separator.card hcutLower
    have hDlinked : Erdos718.IsLinkedSet (K.induce D) Set.univ := by
      apply isLinkedSet_of_pairwise_adj
      intro x _hx y _hy hxy
      change (leftTorso s).Adj
        ((x : (t.right : Set (s.left : Set C.V))) : (s.left : Set C.V))
        ((y : (t.right : Set (s.left : Set C.V))) : (s.left : Set C.V))
      apply Or.inr
      refine ⟨x.property, y.property, ?_⟩
      intro h
      apply hxy
      exact Subtype.ext (Subtype.ext h)
    have hYcard : Y.ncard = t.separator.card := by
      simp only [Y, Set.ncard_coe_finset, rightSeparator_card]
    let P' : Erdos718.ABLinkage K Y D Y.ncard := by
      rw [hYcard]
      exact P
    have hYlinked : Erdos718.IsLinkedSet K Y :=
      isLinkedSet_of_full_abLinkage_to_linked_target
        (Set.toFinite Y) P' hDlinked
    have hleft : Erdos718.IsLinkedSet
        ((leftTorso s).induce (t.right : Set (s.left : Set C.V)))
        {a : (t.right : Set (s.left : Set C.V)) |
          (a : (s.left : Set C.V)) ∈ (t.separator : Set _)} := by
      have hset : Y =
          {a : (t.right : Set (s.left : Set C.V)) |
            (a : (s.left : Set C.V)) ∈ (t.separator : Set _)} := by
        ext a
        exact mem_rightSeparator t a
      rw [← hset]
      exact hYlinked
    have hOldTorsoRight : ∀ x : (s.left : Set C.V),
        (x : C.V) ∈ s.separator → x ∈ t.right := by
      intro x hx
      change x ∈ t₀.right
      exact hOldRight x hx
    let q := composeNestedRight s t hOldTorsoRight
    have hXq : C.X ⊆ q.left := by
      intro x hx
      have hxL : x ∈ s.left := hXleft hx
      let x' : (s.left : Set C.V) := ⟨x, hxL⟩
      have hxA : x' ∈ A := hx
      have hxt : x' ∈ t.left := by
        change x' ∈ t₀.left
        exact hAtLeft hxA
      exact Finset.mem_map.mpr ⟨x', hxt, rfl⟩
    have hqStrictRight : (q.right \ q.left).Nonempty := by
      obtain ⟨x, hx⟩ := hsRigid.2.1
      refine ⟨x, ?_⟩
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_union_left _ (Finset.mem_sdiff.mp hx).1, ?_⟩
      intro hxqL
      rw [composeNestedRight_left, Finset.mem_map] at hxqL
      obtain ⟨z, _hz, hzx⟩ := hxqL
      change (z : C.V) = x at hzx
      exact (Finset.mem_sdiff.mp hx).2 (hzx ▸ z.property)
    have hlinkedExpanded := isLinkedSet_induce_expandedLeftRegion
      s (t.right : Set (s.left : Set C.V))
        (t.separator : Set (s.left : Set C.V))
        (fun _ hx => (Finset.mem_inter.mp hx).2) hleft hsRigid.2.2
    have hregion := expandedLeftRegion_eq_composeNestedRight
      s t hOldTorsoRight
    rw [hregion] at hlinkedExpanded
    have htarget :
        {z : (q.right : Set C.V) |
          (z : C.V) ∈ liftLeftSet s
            (t.separator : Set (s.left : Set C.V))} =
        (rightSeparator q : Set (q.right : Set C.V)) := by
      ext z
      change ((z : C.V) ∈ liftLeftSet s
          (t.separator : Set (s.left : Set C.V))) ↔
        z ∈ rightSeparator q
      rw [mem_rightSeparator]
      change ((z : C.V) ∈ liftLeftSet s
          (t.separator : Set (s.left : Set C.V))) ↔
        (z : C.V) ∈ q.separator
      rw [show q.separator =
        t.separator.map (Function.Embedding.subtype _) by
          exact composeNestedRight_separator s t hOldTorsoRight]
      simp only [liftLeftSet, Finset.mem_map]
      constructor <;> rintro ⟨y, hy, hyz⟩ <;> exact ⟨y, hy, hyz⟩
    have hqLinked : Erdos718.IsLinkedSet
        (C.G.induce (q.right : Set C.V))
        (rightSeparator q : Set (q.right : Set C.V)) := by
      rw [← htarget]
      exact hlinkedExpanded
    have hqRigid : C.IsRigidSeparation q :=
      ⟨hXq, hqStrictRight, hqLinked⟩
    have hqOrder : q.separator.card < C.X.card := by
      rw [composeNestedRight_separator_card]
      exact htSmall
    exact hbelow q hqRigid hqOrder

/-- Claims 2.1 and 2.2 together exclude every rigid separation of order at
most `|X|`. -/
theorem hasNoSmallRigidSeparation_of_lexMinimal
    (C : MassedCounterexample k) (hlex : C.IsLexMinimal) :
    C.HasNoSmallRigidSeparation := by
  intro s hs
  by_contra hnot
  have hle : s.separator.card ≤ C.X.card := Nat.le_of_not_gt hnot
  rcases hle.lt_or_eq with hlt | heq
  · exact noRigidSeparationBelow_of_lexMinimal C hlex s hs hlt
  · exact noRigidSeparationEqual_of_lexMinimal C hlex s hs heq

end MassedCounterexample
end ThomasWollanMassed
end Erdos717
