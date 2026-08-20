/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Claims 2.1 and 2.2 of the Thomas--Wollan minimal-pair argument. -/

import ErdosProblems.Erdos717.NestedTorso

open Function Set
open SimpleGraph

namespace Erdos717
namespace ThomasWollanMassed

namespace MassedCounterexample

variable {k : ℕ}

/-- Claim 2.1: no rigid separation has order strictly below `|X|`. -/
def HasNoRigidSeparationBelow (C : MassedCounterexample k) : Prop :=
  ∀ s : Erdos718.Separation C.G,
    C.IsRigidSeparation s → s.separator.card < C.X.card → False

theorem noRigidSeparationBelow_of_lexMinimal
    (C : MassedCounterexample k) (hlex : C.IsLexMinimal) :
    C.HasNoRigidSeparationBelow := by
  classical
  intro witness hwitness hwitnessOrder
  let P : ℕ → Prop := fun n =>
    ∃ s : Erdos718.Separation C.G,
      C.IsRigidSeparation s ∧ s.separator.card < C.X.card ∧
        s.left.card = n
  have hP : ∃ n, P n :=
    ⟨witness.left.card, witness, hwitness, hwitnessOrder, rfl⟩
  let n₀ := Nat.find hP
  obtain ⟨s, hsRigid, hsOrder, hsCard⟩ := Nat.find_spec hP
  have hsMinimal : ∀ q : Erdos718.Separation C.G,
      C.IsRigidSeparation q → q.separator.card < C.X.card →
      s.left.card ≤ q.left.card := by
    intro q hq hqOrder
    have := Nat.find_min' hP ⟨q, hq, hqOrder, rfl⟩
    rwa [hsCard]
  have hXleft : C.X ⊆ s.left := hsRigid.1
  let Xl := restrictFinset (s.left : Set C.V) C.X hXleft
  have hXlcard : Xl.card = C.X.card :=
    card_restrictFinset _ _ _
  have hrightBound : incidentEdges C.G (s.right \ s.left) ≤
      8 * k * (s.right \ s.left).card :=
    C.massed.2 s hXleft hsOrder
  have htorsoFirst : 8 * k *
        (Fintype.card (s.left : Set C.V) - Xl.card) <
      incidentEdges (leftTorso s) (Finset.univ \ Xl) := by
    exact leftTorso_first_mass s C.X hXleft k C.massed.1 hrightBound
  have htorsoNotMassed : ¬IsEightKMassed (leftTorso s) Xl k := by
    intro htorsoMassed
    have htorsoNotLinked : ¬Erdos718.IsLinkedSet
        (leftTorso s) (Xl : Set (s.left : Set C.V)) := by
      intro htorsoLinked
      apply C.not_linked
      intro I _ terminal hterminal
      have hterminalLeft : Set.range terminal ⊆ (s.left : Set C.V) :=
        hterminal.trans (fun _ hx => hXleft hx)
      let terminalL := terminalIntoSet (s.left : Set C.V)
        terminal hterminalLeft
      have hterminalXl : Set.range terminalL ⊆
          (Xl : Set (s.left : Set C.V)) := by
        rintro _ ⟨z, rfl⟩
        exact (mem_restrictFinset (s.left : Set C.V) C.X hXleft _).2
          (hterminal ⟨z, rfl⟩)
      obtain ⟨LL⟩ := htorsoLinked I terminalL hterminalXl
      obtain ⟨LG⟩ := nonempty_pairLinkage_of_leftTorso_of_linked_right
        s (Xl : Set (s.left : Set C.V)) terminalL ⟨LL⟩ hsRigid.2.2
      have hset : liftLeftSet s (Xl : Set (s.left : Set C.V)) =
          (C.X : Set C.V) := by
        ext x
        constructor
        · rintro ⟨y, hy, hyx⟩
          have hy' : y ∈ Xl := hy
          have hyC : (y : C.V) ∈ C.X :=
            (mem_restrictFinset (s.left : Set C.V) C.X hXleft y).1 hy'
          rwa [hyx] at hyC
        · intro hx
          let y : (s.left : Set C.V) := ⟨x, hXleft hx⟩
          exact ⟨y, (mem_restrictFinset _ _ _ y).2 hx, rfl⟩
      have hterm : leftTerminalToGraph s terminalL = terminal := by
        apply Function.Embedding.ext
        intro z
        rfl
      exact ⟨by simpa only [hset, hterm] using LG⟩
    let D : MassedCounterexample k := {
      V := (s.left : Set C.V)
      fintypeV := inferInstance
      decEqV := inferInstance
      G := leftTorso s
      decAdj := inferInstance
      X := Xl
      card_le := by rw [hXlcard]; exact C.card_le
      massed := htorsoMassed
      not_linked := htorsoNotLinked
    }
    have hleftLt : s.left.card < Fintype.card C.V := by
      have hstrictPos : 0 < (s.right \ s.left).card :=
        Finset.card_pos.mpr hsRigid.2.1
      have hsum := card_left_add_card_strictRight s
      omega
    have hvertices := (hlex D).1
    change Fintype.card C.V ≤ Fintype.card (s.left : Set C.V) at hvertices
    have hleftCard : Fintype.card (s.left : Set C.V) = s.left.card := by simp
    rw [hleftCard] at hvertices
    exact (Nat.not_le_of_lt hleftLt) hvertices
  have hbad : ∃ t : Erdos718.Separation (leftTorso s),
      ViolatesSecondFor (leftTorso s) Xl k t := by
    by_contra hnone
    apply htorsoNotMassed
    refine ⟨htorsoFirst, ?_⟩
    intro t hX horder
    by_contra hbound
    apply hnone
    exact ⟨t, hX, horder, Nat.lt_of_not_ge hbound⟩
  obtain ⟨t, htBad, htMinimal⟩ :=
    exists_minimal_violatesSecondFor (leftTorso s) Xl k hbad
  have htMassed := isEightKMassed_induce_right_of_minimal_violationFor
    (leftTorso s) Xl k t htBad htMinimal
  have htLinked : Erdos718.IsLinkedSet
      ((leftTorso s).induce (t.right : Set (s.left : Set C.V)))
      (rightSeparator t : Set (t.right : Set (s.left : Set C.V))) := by
    by_contra hnot
    let D : MassedCounterexample k := {
      V := (t.right : Set (s.left : Set C.V))
      fintypeV := inferInstance
      decEqV := inferInstance
      G := (leftTorso s).induce (t.right : Set (s.left : Set C.V))
      decAdj := inferInstance
      X := rightSeparator t
      card_le := by
        rw [rightSeparator_card]
        exact htBad.2.1.le.trans (by rw [hXlcard]; exact C.card_le)
      massed := htMassed
      not_linked := hnot
    }
    have htLeftStrict : (t.left \ t.right).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      have hleftSub : t.left ⊆ t.right := by
        intro x hxL
        by_contra hxR
        have hx : x ∈ t.left \ t.right :=
          Finset.mem_sdiff.mpr ⟨hxL, hxR⟩
        simpa [hempty] using hx
      have hXsep : Xl ⊆ t.separator := by
        intro x hx
        exact Finset.mem_inter.mpr ⟨htBad.1 hx, hleftSub (htBad.1 hx)⟩
      exact (Nat.not_le_of_lt htBad.2.1) (Finset.card_le_card hXsep)
    have htRightLt : t.right.card < Fintype.card (s.left : Set C.V) := by
      have hproper : t.right ⊂
          (Finset.univ : Finset (s.left : Set C.V)) := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
        intro heq
        obtain ⟨x, hx⟩ := htLeftStrict
        exact (Finset.mem_sdiff.mp hx).2 (heq ▸ Finset.mem_univ x)
      simpa using Finset.card_lt_card hproper
    have hsLeftLt : Fintype.card (s.left : Set C.V) < Fintype.card C.V := by
      have hstrictPos : 0 < (s.right \ s.left).card :=
        Finset.card_pos.mpr hsRigid.2.1
      have hsum := card_left_add_card_strictRight s
      rw [show Fintype.card (s.left : Set C.V) = s.left.card by simp]
      omega
    have hvertices := (hlex D).1
    change Fintype.card C.V ≤
      Fintype.card (t.right : Set (s.left : Set C.V)) at hvertices
    have hcard : Fintype.card (t.right : Set (s.left : Set C.V)) =
        t.right.card := by simp
    rw [hcard] at hvertices
    exact (Nat.not_le_of_lt (htRightLt.trans hsLeftLt)) hvertices
  by_cases hSleft : ∀ x : (s.left : Set C.V),
      (x : C.V) ∈ s.separator → x ∈ t.left
  · let q := composeNestedLeft s t hSleft
    have hXq : C.X ⊆ q.left := by
      intro x hx
      have hxL : x ∈ s.left := hXleft hx
      let x' : (s.left : Set C.V) := ⟨x, hxL⟩
      have hxXl : x' ∈ Xl := (mem_restrictFinset _ _ _ x').2 hx
      have hxt : x' ∈ t.left := htBad.1 hxXl
      exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_map.mpr ⟨x', hxt, rfl⟩))
    have hqOrder : q.separator.card < C.X.card := by
      rw [composeNestedLeft_separator_card]
      rw [← hXlcard]
      exact htBad.2.1
    have hRdisjoint : ∀ x ∈ (t.right \ t.left),
        (x : C.V) ∉ s.separator := by
      intro x hx hxSep
      exact (Finset.mem_sdiff.mp hx).2 (hSleft x hxSep)
    have hcountTorso : incidentEdges (leftTorso s) (t.right \ t.left) =
        incidentEdges (C.G.induce (s.left : Set C.V))
          (t.right \ t.left) :=
      incidentEdges_leftTorso_eq_induce_left s (t.right \ t.left) hRdisjoint
    have hcountCompose : incidentEdges C.G (q.right \ q.left) =
        incidentEdges (C.G.induce (s.left : Set C.V))
          (t.right \ t.left) := by
      exact incidentEdges_composeNestedLeft s t hSleft
    have hqCard : (q.right \ q.left).card =
        (t.right \ t.left).card := by
      rw [composeNestedLeft_strictRight, Finset.card_map]
    have hqDense : 8 * k * (q.right \ q.left).card <
        incidentEdges C.G (q.right \ q.left) := by
      rw [hqCard, hcountCompose, ← hcountTorso]
      exact htBad.2.2
    have hbound := C.massed.2 q hXq hqOrder
    exact (Nat.not_lt_of_ge hbound) hqDense
  · have hSright : ∀ x : (s.left : Set C.V),
        (x : C.V) ∈ s.separator → x ∈ t.right := by
      push Not at hSleft
      obtain ⟨x₀, hx₀Sep, hx₀NotLeft⟩ := hSleft
      have hx₀Right : x₀ ∈ t.right :=
        (t.mem_left_or_mem_right x₀).resolve_left hx₀NotLeft
      intro y hySep
      by_contra hyRight
      have hyLeft : y ∈ t.left :=
        (t.mem_left_or_mem_right y).resolve_right hyRight
      have hyne : y ≠ x₀ := by
        intro h
        subst y
        exact hx₀NotLeft hyLeft
      have hadj : (leftTorso s).Adj y x₀ :=
        Or.inr ⟨hySep, hx₀Sep, hyne⟩
      exact t.not_adj hyLeft hyRight hx₀Right hx₀NotLeft hadj
    let q := composeNestedRight s t hSright
    have hXq : C.X ⊆ q.left := by
      intro x hx
      have hxL : x ∈ s.left := hXleft hx
      let x' : (s.left : Set C.V) := ⟨x, hxL⟩
      have hxXl : x' ∈ Xl := (mem_restrictFinset _ _ _ x').2 hx
      have hxt : x' ∈ t.left := htBad.1 hxXl
      exact Finset.mem_map.mpr ⟨x', hxt, rfl⟩
    have hqOrder : q.separator.card < C.X.card := by
      rw [composeNestedRight_separator_card]
      simpa only [hXlcard] using htBad.2.1
    have htStrictRight : (t.right \ t.left).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      have hdense := htBad.2.2
      rw [hempty, incidentEdges_empty] at hdense
      simp at hdense
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
    have htLinked' : Erdos718.IsLinkedSet
        ((leftTorso s).induce (t.right : Set (s.left : Set C.V)))
        {a : (t.right : Set (s.left : Set C.V)) |
          (a : (s.left : Set C.V)) ∈ (t.separator : Set _)} := by
      have hset : (rightSeparator t : Set
          (t.right : Set (s.left : Set C.V))) =
          {a : (t.right : Set (s.left : Set C.V)) |
            (a : (s.left : Set C.V)) ∈ (t.separator : Set _)} := by
        ext a
        exact mem_rightSeparator t a
      rw [← hset]
      exact htLinked
    have hlinkedExpanded := isLinkedSet_induce_expandedLeftRegion
      s (t.right : Set (s.left : Set C.V))
        (t.separator : Set (s.left : Set C.V))
        (fun _ hx => (Finset.mem_inter.mp hx).2) htLinked' hsRigid.2.2
    have hregion := expandedLeftRegion_eq_composeNestedRight s t hSright
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
          exact composeNestedRight_separator s t hSright]
      simp only [liftLeftSet, Finset.mem_map]
      constructor
      · rintro ⟨y, hy, hyz⟩
        exact ⟨y, hy, hyz⟩
      · rintro ⟨y, hy, hyz⟩
        exact ⟨y, hy, hyz⟩
    have hqLinked : Erdos718.IsLinkedSet
        (C.G.induce (q.right : Set C.V))
        (rightSeparator q : Set (q.right : Set C.V)) := by
      rw [← htarget]
      exact hlinkedExpanded
    have hqRigid : C.IsRigidSeparation q :=
      ⟨hXq, hqStrictRight, hqLinked⟩
    have htLeftLt : t.left.card < s.left.card := by
      have hproper : t.left ⊂
          (Finset.univ : Finset (s.left : Set C.V)) := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
        intro heq
        obtain ⟨x, hx⟩ := htStrictRight
        exact (Finset.mem_sdiff.mp hx).2 (heq ▸ Finset.mem_univ x)
      simpa using Finset.card_lt_card hproper
    have hqLeftCard : q.left.card = t.left.card := by
      rw [composeNestedRight_left, Finset.card_map]
    have hmin := hsMinimal q hqRigid hqOrder
    rw [hqLeftCard] at hmin
    exact (Nat.not_le_of_lt htLeftLt) hmin

end MassedCounterexample
end ThomasWollanMassed
end Erdos717
