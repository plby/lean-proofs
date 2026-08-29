/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeLinkClosureInvariants
import ErdosProblems.Erdos599.FullQuotientWave
import ErdosProblems.Erdos599.SafeLinkArrowPair
import ErdosProblems.Erdos599.Ladder

/-!
# The full dependent Section 6 closure

The terminal-suffix quotient is sufficient for roof transport, but it loses
components which are needed for the path-provenance assertion in Proposition
6.3.  This file runs the dependent closing construction with the literal full
quotient of Definition 2.29 at every successor.  Thus an old stage survives
componentwise at every later stage.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath
open Alternating

universe u

namespace DWeb

variable {V : Type u} (G : DWeb V)

/-! ## Transport by the full quotient -/

/-- A fixed choice of the full quotient component wave. -/
noncomputable def fullQuotientWave
    (hNoEnter : G.NoEdgeEnters G.source) (X : Set V) (W : G.Wave) :
    (G.quotient X).Wave :=
  ⟨Classical.choose
      (G.exists_sourceRootedFullQuotientWave hNoEnter W.2),
    (Classical.choose_spec
      (G.exists_sourceRootedFullQuotientWave hNoEnter W.2)).1⟩

theorem vertexSet_fullQuotientWave
    (hNoEnter : G.NoEdgeEnters G.source) (X : Set V) (W : G.Wave) :
    (G.quotient X).vertexSet (G.fullQuotientWave hNoEnter X W).1 =
      (G.vertexSet W.1 ∪ X) \ G.strictRoof X :=
  (Classical.choose_spec
    (G.exists_sourceRootedFullQuotientWave hNoEnter W.2)).2.2.1

theorem familyEdges_fullQuotientWave
    (hNoEnter : G.NoEdgeEnters G.source) (X : Set V) (W : G.Wave) :
    familyEdges (G.fullQuotientWave hNoEnter X W).1 =
      PathFilterComponents.quotientWarpEdges G X W.1 :=
  (Classical.choose_spec
    (G.exists_sourceRootedFullQuotientWave hNoEnter W.2)).2.2.2.1

theorem terminalFrontiers_subset_fullQuotientWave
    (hNoEnter : G.NoEdgeEnters G.source) (X : Set V) (W : G.Wave) :
    (G.terminalFrontier W.1 \ G.strictRoof X) ∪
        (G.essential X \ G.vertexSet W.1) ⊆
      (G.quotient X).terminalFrontier
        (G.fullQuotientWave hNoEnter X W).1 :=
  (Classical.choose_spec
    (G.exists_sourceRootedFullQuotientWave hNoEnter W.2)).2.2.2.2

/-- A wave in `G / X`, fully transported to `G / Y` for `X ⊆ Y`. -/
def fullWaveToLargerQuotient
    (hNoEnter : G.NoEdgeEnters G.source)
    {X Y : Set V} (hXY : X ⊆ Y) (W : (G.quotient X).Wave) :
    (G.quotient Y).Wave := by
  let H := G.quotient X
  let Z : (H.quotient Y).Wave :=
    H.fullQuotientWave hNoEnter.quotient Y W
  have heq : H.quotient Y = G.quotient Y := by
    calc
      H.quotient Y = G.quotient (X ∪ Y) :=
        G.quotient_quotient_eq_union X Y hNoEnter
      _ = G.quotient Y := by rw [Set.union_eq_right.mpr hXY]
  exact heq ▸ Z

theorem vertexSet_fullWaveToLargerQuotient
    (hNoEnter : G.NoEdgeEnters G.source)
    {X Y : Set V} (hXY : X ⊆ Y) (W : (G.quotient X).Wave) :
    (G.quotient Y).vertexSet
        (G.fullWaveToLargerQuotient hNoEnter hXY W).1 =
      ((G.quotient X).vertexSet W.1 ∪ Y) \
        (G.quotient X).strictRoof Y := by
  let H := G.quotient X
  let Z : (H.quotient Y).Wave :=
    H.fullQuotientWave hNoEnter.quotient Y W
  have heq : H.quotient Y = G.quotient Y := by
    calc
      H.quotient Y = G.quotient (X ∪ Y) :=
        G.quotient_quotient_eq_union X Y hNoEnter
      _ = G.quotient Y := by rw [Set.union_eq_right.mpr hXY]
  have htransport :
      G.fullWaveToLargerQuotient hNoEnter hXY W = heq ▸ Z := by
    apply Subtype.ext
    rfl
  rw [htransport, DWeb.vertexSet_castWebWave heq Z]
  exact H.vertexSet_fullQuotientWave hNoEnter.quotient Y W

theorem familyEdges_castWebWave {H K : DWeb V} (h : H = K)
    (W : H.Wave) :
    familyEdges (h ▸ W).1 = familyEdges W.1 := by
  cases h
  rfl

theorem familyEdges_fullWaveToLargerQuotient
    (hNoEnter : G.NoEdgeEnters G.source)
    {X Y : Set V} (hXY : X ⊆ Y) (W : (G.quotient X).Wave) :
    familyEdges (G.fullWaveToLargerQuotient hNoEnter hXY W).1 =
      PathFilterComponents.quotientWarpEdges (G.quotient X) Y W.1 := by
  let H := G.quotient X
  let Z : (H.quotient Y).Wave :=
    H.fullQuotientWave hNoEnter.quotient Y W
  have heq : H.quotient Y = G.quotient Y := by
    calc
      H.quotient Y = G.quotient (X ∪ Y) :=
        G.quotient_quotient_eq_union X Y hNoEnter
      _ = G.quotient Y := by rw [Set.union_eq_right.mpr hXY]
  have htransport :
      G.fullWaveToLargerQuotient hNoEnter hXY W = heq ▸ Z := by
    apply Subtype.ext
    rfl
  rw [htransport, DWeb.familyEdges_castWebWave heq Z]
  exact H.familyEdges_fullQuotientWave hNoEnter.quotient Y W

/-! ## The full dependent recursion -/

/-- The old full accumulator in the successor quotient. -/
def sectionSixFullAccumOldInNext
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V)
    (s : G.SectionSixAccumStage) :
    (G.quotient (G.sectionSixAccumNextCarrier F K Y Q T s)).Wave :=
  G.fullWaveToLargerQuotient hNoEnter
    (G.sectionSixAccumStage_carrier_subset_next F K Y Q T s) s.wave

/-- The successor is a maximal wave extending the fully transported old
accumulator. -/
noncomputable def sectionSixFullAccumNext
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V)
    (s : G.SectionSixAccumStage) : G.SectionSixAccumStage := by
  let X' := G.sectionSixAccumNextCarrier F K Y Q T s
  let old : (G.quotient X').Wave :=
    G.sectionSixFullAccumOldInNext hNoEnter F K Y Q T s
  let next : (G.quotient X').Wave := Classical.choose
    ((G.quotient X').exists_maximal_wave_extending old)
  exact { carrier := X', wave := next }

@[simp]
theorem sectionSixFullAccumNext_carrier
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V)
    (s : G.SectionSixAccumStage) :
    (G.sectionSixFullAccumNext hNoEnter F K Y Q T s).carrier =
      G.sectionSixAccumNextCarrier F K Y Q T s :=
  rfl

theorem sectionSixFullAccumOldInNext_le_next
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V)
    (s : G.SectionSixAccumStage) :
    G.sectionSixFullAccumOldInNext hNoEnter F K Y Q T s ≤
      (G.sectionSixFullAccumNext hNoEnter F K Y Q T s).wave := by
  change (G.sectionSixFullAccumOldInNext hNoEnter F K Y Q T s) ≤
    Classical.choose ((G.quotient
      (G.sectionSixAccumNextCarrier F K Y Q T s)).exists_maximal_wave_extending
        (G.sectionSixFullAccumOldInNext hNoEnter F K Y Q T s))
  exact (Classical.choose_spec ((G.quotient
    (G.sectionSixAccumNextCarrier F K Y Q T s)).exists_maximal_wave_extending
      (G.sectionSixFullAccumOldInNext hNoEnter F K Y Q T s))).1

theorem sectionSixFullAccumNext_isMax
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V)
    (s : G.SectionSixAccumStage) :
    IsMax (G.sectionSixFullAccumNext hNoEnter F K Y Q T s).wave := by
  change IsMax (Classical.choose ((G.quotient
    (G.sectionSixAccumNextCarrier F K Y Q T s)).exists_maximal_wave_extending
      (G.sectionSixFullAccumOldInNext hNoEnter F K Y Q T s)))
  exact (Classical.choose_spec ((G.quotient
    (G.sectionSixAccumNextCarrier F K Y Q T s)).exists_maximal_wave_extending
      (G.sectionSixFullAccumOldInNext hNoEnter F K Y Q T s))).2

theorem sectionSixFullAccumNext_roofs_every_wave
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V)
    (s : G.SectionSixAccumStage)
    (W : (G.quotient
      (G.sectionSixAccumNextCarrier F K Y Q T s)).Wave) :
    (G.quotient (G.sectionSixAccumNextCarrier F K Y Q T s)).RoofLE W.1
      (G.sectionSixFullAccumNext hNoEnter F K Y Q T s).wave.1 :=
  (G.quotient (G.sectionSixAccumNextCarrier F K Y Q T s)).roofLE_of_isMax
    (G.sectionSixFullAccumNext_isMax hNoEnter F K Y Q T s) W

/-- The source-faithful full accumulated recursion. -/
def sectionSixFullAccumStage
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) :
    ℕ → G.SectionSixAccumStage
  | 0 => { carrier := F y, wave := SafeLink.maximalQuotientWave G (F y) }
  | n + 1 => G.sectionSixFullAccumNext hNoEnter F K Y Q T
      (sectionSixFullAccumStage hNoEnter F K Y Q T y n)

@[simp]
theorem sectionSixFullAccumStage_zero_carrier
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) :
    (G.sectionSixFullAccumStage hNoEnter F K Y Q T y 0).carrier = F y :=
  rfl

@[simp]
theorem sectionSixFullAccumStage_succ_carrier
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ) :
    (G.sectionSixFullAccumStage hNoEnter F K Y Q T y (n + 1)).carrier =
      G.sectionSixAccumNextCarrier F K Y Q T
        (G.sectionSixFullAccumStage hNoEnter F K Y Q T y n) :=
  rfl

theorem sectionSixFullAccumStage_carrier_subset_succ
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ) :
    (G.sectionSixFullAccumStage hNoEnter F K Y Q T y n).carrier ⊆
      (G.sectionSixFullAccumStage hNoEnter F K Y Q T y (n + 1)).carrier := by
  rw [G.sectionSixFullAccumStage_succ_carrier]
  exact G.sectionSixAccumStage_carrier_subset_next F K Y Q T _

theorem sectionSixFullAccumStage_carrier_mono
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) :
    Monotone (fun n ↦
      (G.sectionSixFullAccumStage hNoEnter F K Y Q T y n).carrier) := by
  apply monotone_nat_of_le_succ
  exact G.sectionSixFullAccumStage_carrier_subset_succ
    hNoEnter F K Y Q T y

/-- The raw union of the full dependent commitment sets. -/
def sectionSixFullAccumClosure
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) : Set V :=
  ⋃ n, (G.sectionSixFullAccumStage hNoEnter F K Y Q T y n).carrier

theorem sectionSixFullAccumStage_carrier_subset_closure
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ) :
    (G.sectionSixFullAccumStage hNoEnter F K Y Q T y n).carrier ⊆
      G.sectionSixFullAccumClosure hNoEnter F K Y Q T y :=
  Set.subset_iUnion (fun i : ℕ ↦
    (G.sectionSixFullAccumStage hNoEnter F K Y Q T y i).carrier) n

theorem sectionSixFullAccumStage_carrier_countable
    (hNoEnter : G.NoEdgeEnters G.source)
    {F K : V → Set V} {Y Q T : Set V} {y : V}
    (hF : ∀ z, (F z).Finite) (hK : ∀ t, (K t).Countable) :
    ∀ n,
      (G.sectionSixFullAccumStage hNoEnter F K Y Q T y n).carrier.Countable
  | 0 => (hF y).countable
  | n + 1 => by
      rw [G.sectionSixFullAccumStage_succ_carrier]
      apply G.closingStep_countable
      · exact G.isWarp_sectionSixAccumStageLift _
      · exact sectionSixFullAccumStage_carrier_countable
          hNoEnter hF hK n
      · exact hF
      · exact hK

theorem sectionSixFullAccumClosure_countable
    (hNoEnter : G.NoEdgeEnters G.source)
    {F K : V → Set V} {Y Q T : Set V} {y : V}
    (hF : ∀ z, (F z).Finite) (hK : ∀ t, (K t).Countable) :
    (G.sectionSixFullAccumClosure hNoEnter F K Y Q T y).Countable := by
  apply Set.countable_iUnion
  exact G.sectionSixFullAccumStage_carrier_countable hNoEnter hF hK

theorem sectionSixFullAccumStage_carrier_subset_offRoot
    (a : V) (hNoEnter : (G.delete {a}).NoEdgeEnters (G.delete {a}).source)
    (F K : V → Set V) (Y Q T : Set V) (y : V)
    (hF : ∀ z, F z ⊆ T \ {a}) (hK : ∀ t, K t ⊆ T \ {a}) :
    ∀ n, ((G.delete {a}).sectionSixFullAccumStage hNoEnter
      F K Y Q T y n).carrier ⊆ T \ {a}
  | 0 => by simpa using hF y
  | n + 1 => by
      rw [(G.delete {a}).sectionSixFullAccumStage_succ_carrier]
      intro x hx
      change x ∈ (G.delete {a}).closingStep
        (fun _ ↦ (G.delete {a}).sectionSixAccumStageLift
          ((G.delete {a}).sectionSixFullAccumStage
            hNoEnter F K Y Q T y n))
        F K Y Q T
        ((G.delete {a}).sectionSixFullAccumStage
          hNoEnter F K Y Q T y n).carrier at hx
      simp only [closingStep, Set.mem_union] at hx
      rcases hx with ((hxOld | hxF) | hxK) | hxMeet
      · exact sectionSixFullAccumStage_carrier_subset_offRoot
          a hNoEnter F K Y Q T y hF hK n hxOld
      · simp only [Set.mem_iUnion] at hxF
        obtain ⟨z, _hz, hxFz⟩ := hxF
        exact hF z hxFz
      · simp only [Set.mem_iUnion] at hxK
        obtain ⟨t, _ht, hxKt⟩ := hxK
        exact hK t hxKt
      · refine ⟨hxMeet.2, ?_⟩
        intro hxa
        subst x
        have haVertex : a ∈ (G.delete {a}).vertexSet
            ((G.delete {a}).sectionSixAccumStageLift
              ((G.delete {a}).sectionSixFullAccumStage
                hNoEnter F K Y Q T y n)) := by
          rw [meetingVertexSet] at hxMeet
          obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hxMeet.1
          obtain ⟨hpMeeting, hap⟩ := Set.mem_iUnion.mp hp
          exact ⟨p, hpMeeting.1, hap⟩
        exact G.root_not_mem_vertexSet_sectionSixLift a
          ((sectionSixFullAccumStage_carrier_subset_offRoot
            a hNoEnter F K Y Q T y hF hK n).trans
              (by intro v hv; simpa using hv.2))
          ((G.delete {a}).sectionSixFullAccumStage
            hNoEnter F K Y Q T y n).wave.2 haVertex

theorem sectionSixFullAccumClosure_subset_offRoot
    (a : V) (hNoEnter : (G.delete {a}).NoEdgeEnters (G.delete {a}).source)
    (F K : V → Set V) (Y Q T : Set V) (y : V)
    (hF : ∀ z, F z ⊆ T \ {a}) (hK : ∀ t, K t ⊆ T \ {a}) :
    (G.delete {a}).sectionSixFullAccumClosure hNoEnter F K Y Q T y ⊆
      T \ {a} := by
  intro x hx
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
  exact G.sectionSixFullAccumStage_carrier_subset_offRoot
    a hNoEnter F K Y Q T y hF hK n hxn

theorem sectionSixFullAccum_F_subset_succ
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ) {z : V}
    (hz : z ∈ Y ∩ G.meetingVertexSet
      (G.sectionSixAccumStageLift
        (G.sectionSixFullAccumStage hNoEnter F K Y Q T y n))
      (G.sectionSixFullAccumStage hNoEnter F K Y Q T y n).carrier) :
    F z ⊆
      (G.sectionSixFullAccumStage hNoEnter F K Y Q T y (n + 1)).carrier := by
  intro x hx
  rw [G.sectionSixFullAccumStage_succ_carrier]
  exact Or.inl (Or.inl (Or.inr
    (Set.mem_iUnion_of_mem z (Set.mem_iUnion_of_mem hz hx))))

theorem sectionSixFullAccum_F_subset_closure
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ) {z : V}
    (hz : z ∈ Y ∩ G.meetingVertexSet
      (G.sectionSixAccumStageLift
        (G.sectionSixFullAccumStage hNoEnter F K Y Q T y n))
      (G.sectionSixFullAccumStage hNoEnter F K Y Q T y n).carrier) :
    F z ⊆ G.sectionSixFullAccumClosure hNoEnter F K Y Q T y :=
  (G.sectionSixFullAccum_F_subset_succ
    hNoEnter F K Y Q T y n hz).trans
      (G.sectionSixFullAccumStage_carrier_subset_closure
        hNoEnter F K Y Q T y (n + 1))

theorem sectionSixFullAccum_K_subset_succ
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ) {t : V}
    (ht : t ∈
      (G.sectionSixFullAccumStage hNoEnter F K Y Q T y n).carrier \ Q) :
    K t ⊆
      (G.sectionSixFullAccumStage hNoEnter F K Y Q T y (n + 1)).carrier := by
  intro x hx
  rw [G.sectionSixFullAccumStage_succ_carrier]
  exact Or.inl (Or.inr
    (Set.mem_iUnion_of_mem t (Set.mem_iUnion_of_mem ht hx)))

theorem sectionSixFullAccum_meetingTree_subset_closure
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ) :
    G.meetingVertexSet
        (G.sectionSixAccumStageLift
          (G.sectionSixFullAccumStage hNoEnter F K Y Q T y n))
        (G.sectionSixFullAccumStage hNoEnter F K Y Q T y n).carrier ∩ T ⊆
      G.sectionSixFullAccumClosure hNoEnter F K Y Q T y := by
  intro x hx
  apply G.sectionSixFullAccumStage_carrier_subset_closure
    hNoEnter F K Y Q T y (n + 1)
  rw [G.sectionSixFullAccumStage_succ_carrier]
  exact Or.inr hx

/-! ## The common quotient and final arrow -/

def sectionSixFullAccumCommonStage
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ) :
    (G.quotient
      (G.sectionSixFullAccumClosure hNoEnter F K Y Q T y)).Wave :=
  G.fullWaveToLargerQuotient hNoEnter
    (G.sectionSixFullAccumStage_carrier_subset_closure
      hNoEnter F K Y Q T y n)
    (G.sectionSixFullAccumStage hNoEnter F K Y Q T y n).wave

def sectionSixFullAccumCommonWave
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) :
    (G.quotient
      (G.sectionSixFullAccumClosure hNoEnter F K Y Q T y)).Wave :=
  (G.quotient
    (G.sectionSixFullAccumClosure hNoEnter F K Y Q T y)).omegaArrow
      (G.sectionSixFullAccumCommonStage hNoEnter F K Y Q T y)

theorem sectionSixFullAccumCommonStage_roofLE
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ) :
    let H := G.quotient
      (G.sectionSixFullAccumClosure hNoEnter F K Y Q T y)
    H.RoofLE
      (G.sectionSixFullAccumCommonStage hNoEnter F K Y Q T y n).1
      (G.sectionSixFullAccumCommonWave hNoEnter F K Y Q T y).1 := by
  exact DWeb.roofLE_omegaArrow
    (G.quotient (G.sectionSixFullAccumClosure hNoEnter F K Y Q T y))
    (G.sectionSixFullAccumCommonStage hNoEnter F K Y Q T y) n

/-- Consecutive common-quotient stages are componentwise support-cofinal.
This is the formal content of the "note" in the proof of Proposition 6.3:
the full quotient keeps every surviving old component, and the successor
wave forward-extends the full quotient at the successor carrier. -/
theorem sectionSixFullAccumCommonStage_supportCofinal_succ
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ) :
    let X := G.sectionSixFullAccumClosure hNoEnter F K Y Q T y
    let C := G.sectionSixFullAccumCommonStage hNoEnter F K Y Q T y
    (G.quotient X).SupportCofinal (C n).1 (C (n + 1)).1 := by
  dsimp only
  let s := G.sectionSixFullAccumStage hNoEnter F K Y Q T y n
  let Xn := s.carrier
  let Xnext := G.sectionSixAccumNextCarrier F K Y Q T s
  let X := G.sectionSixFullAccumClosure hNoEnter F K Y Q T y
  let old := G.sectionSixFullAccumOldInNext hNoEnter F K Y Q T s
  let next := G.sectionSixFullAccumNext hNoEnter F K Y Q T s
  let Cn := G.sectionSixFullAccumCommonStage hNoEnter F K Y Q T y n
  let Cnext := G.sectionSixFullAccumCommonStage
    hNoEnter F K Y Q T y (n + 1)
  have hXnNext : Xn ⊆ Xnext :=
    G.sectionSixAccumStage_carrier_subset_next F K Y Q T s
  have hXnX : Xn ⊆ X :=
    G.sectionSixFullAccumStage_carrier_subset_closure
      hNoEnter F K Y Q T y n
  have hXnextX : Xnext ⊆ X := by
    intro v hv
    apply Set.mem_iUnion_of_mem (n + 1)
    change v ∈ Xnext
    exact hv
  have hOldNext : old ≤ next.wave :=
    G.sectionSixFullAccumOldInNext_le_next hNoEnter F K Y Q T s
  apply (G.quotient X).supportCofinal_of_vertexSet_familyEdges Cnext.2.1
  · intro v hv
    change v ∈ (G.quotient X).vertexSet Cn.1 at hv
    rw [show Cn = G.fullWaveToLargerQuotient hNoEnter hXnX s.wave by rfl,
      G.vertexSet_fullWaveToLargerQuotient hNoEnter hXnX s.wave] at hv
    rw [show Cnext = G.fullWaveToLargerQuotient hNoEnter hXnextX next.wave by rfl,
      G.vertexSet_fullWaveToLargerQuotient hNoEnter hXnextX next.wave]
    have hvNotNext : v ∉ (G.quotient Xn).strictRoof Xnext := by
      intro hvStrict
      exact hv.2 (SafeLink.strictRoof_mono
        (G.quotient Xn) hXnextX hvStrict)
    have hvNotFinal : v ∉ (G.quotient Xnext).strictRoof X := by
      rw [G.strictRoof_quotient_eq_strictRoof_union,
        Set.union_eq_right.mpr hXnextX,
        ← Set.union_eq_right.mpr hXnX,
        ← G.strictRoof_quotient_eq_strictRoof_union]
      exact hv.2
    refine ⟨?_, hvNotFinal⟩
    rcases hv.1 with hvStage | hvX
    · have hvOld : v ∈ (G.quotient Xnext).vertexSet old.1 := by
        rw [show old = G.fullWaveToLargerQuotient hNoEnter hXnNext s.wave by rfl,
          G.vertexSet_fullWaveToLargerQuotient hNoEnter hXnNext s.wave]
        exact ⟨Or.inl hvStage, hvNotNext⟩
      obtain ⟨p, hpOld, hvp⟩ := hvOld
      obtain ⟨q, hqNext, hpq⟩ := hOldNext.1 p hpOld
      exact Or.inl ⟨q, hqNext,
        (G.quotient Xnext).support_mono_of_extends hpq hvp⟩
    · exact Or.inr hvX
  · intro e he
    change e ∈ familyEdges Cn.1 at he
    change e ∈ familyEdges Cnext.1
    rw [show Cn = G.fullWaveToLargerQuotient hNoEnter hXnX s.wave by rfl,
      G.familyEdges_fullWaveToLargerQuotient hNoEnter hXnX s.wave] at he
    rw [show Cnext = G.fullWaveToLargerQuotient hNoEnter hXnextX next.wave by rfl,
      G.familyEdges_fullWaveToLargerQuotient hNoEnter hXnextX next.wave]
    have heOldGraph : ((G.quotient Xn).quotient Xnext).graph.Adj e.1 e.2 := by
      rcases he.2 with ⟨heHn, he1, he2, he2X⟩
      exact ⟨heHn,
        fun hs ↦ he1 (SafeLink.strictRoof_mono
          (G.quotient Xn) hXnextX hs),
        fun hs ↦ he2 (SafeLink.strictRoof_mono
          (G.quotient Xn) hXnextX hs),
        fun hs ↦ he2X (hXnextX hs)⟩
    have heOld : e ∈ familyEdges old.1 := by
      rw [show old = G.fullWaveToLargerQuotient hNoEnter hXnNext s.wave by rfl,
        G.familyEdges_fullWaveToLargerQuotient hNoEnter hXnNext s.wave]
      exact ⟨he.1, heOldGraph⟩
    have heNext : e ∈ familyEdges next.wave.1 := by
      simp only [familyEdges, Set.mem_iUnion] at heOld ⊢
      obtain ⟨p, hpOld, hep⟩ := heOld
      obtain ⟨q, hqNext, hpq⟩ := hOldNext.1 p hpOld
      exact ⟨q, hqNext,
        _root_.Erdos599.DirectedPath.Path.edgeSet_mono_of_extends
          hpq hep⟩
    refine ⟨heNext, ?_⟩
    have hEqN : (G.quotient Xn).quotient X = G.quotient X := by
      calc
        (G.quotient Xn).quotient X = G.quotient (Xn ∪ X) :=
          G.quotient_quotient_eq_union Xn X hNoEnter
        _ = G.quotient X := by rw [Set.union_eq_right.mpr hXnX]
    have hEqNext : (G.quotient Xnext).quotient X = G.quotient X := by
      calc
        (G.quotient Xnext).quotient X = G.quotient (Xnext ∪ X) :=
          G.quotient_quotient_eq_union Xnext X hNoEnter
        _ = G.quotient X := by rw [Set.union_eq_right.mpr hXnextX]
    have heFinal : (G.quotient X).graph.Adj e.1 e.2 := by
      rw [← hEqN]
      exact he.2
    rw [hEqNext]
    exact heFinal

private theorem walk_edgeSet_lift_fullClosure
    {D E : Digraph V} (hDE : ∀ {x y}, D.Adj x y → E.Adj x y) :
    ∀ {a b : V} (w : Walk D a b), (w.lift hDE).edgeSet = w.edgeSet
  | _, _, .nil => rfl
  | _, _, .cons h p => by
      simp [Walk.lift, Walk.edgeSet_cons,
        walk_edgeSet_lift_fullClosure hDE p]

private theorem finitePath_edgeSet_lift_fullClosure
    {D E : Digraph V} (hDE : ∀ {x y}, D.Adj x y → E.Adj x y)
    (p : FinitePath D) : (p.lift hDE).edgeSet = p.edgeSet :=
  walk_edgeSet_lift_fullClosure hDE p.walk

private theorem walk_support_eq_singleton_fullClosure
    {D : Digraph V} {a b : V} (w : Walk D a b)
    (hw : w.IsPath) (h : a = b) : w.support = [a] := by
  induction w with
  | nil => rfl
  | @cons a b c e p ih =>
      have hn : a ∉ p.support := (List.nodup_cons.1 hw).1
      exact (hn (h ▸ p.end_mem_support)).elim

/-- A component of a full quotient which contains an uncommitted vertex is
contained in one path of the wave before quotienting. -/
theorem exists_old_path_supporting_fullWaveToLargerQuotient_of_not_mem
    (hNoEnter : G.NoEdgeEnters G.source)
    {X Y : Set V} (hXY : X ⊆ Y) (W : (G.quotient X).Wave)
    {p : (G.quotient Y).DPath}
    (hp : p ∈ (G.fullWaveToLargerQuotient hNoEnter hXY W).1)
    {z : V} (hzp : z ∈ p.support) (hzY : z ∉ Y) :
    ∃ q ∈ W.1, p.support ⊆ q.support := by
  let H := G.quotient X
  have hgraph : ∀ {u v : V}, (G.quotient Y).graph.Adj u v → H.graph.Adj u v := by
    intro u v huv
    exact ⟨huv.1,
      fun hu ↦ huv.2.1 (SafeLink.strictRoof_mono G hXY hu),
      fun hv ↦ huv.2.2.1 (SafeLink.strictRoof_mono G hXY hv),
      fun hv ↦ huv.2.2.2 (hXY hv)⟩
  have hfamily : familyEdges
      (G.fullWaveToLargerQuotient hNoEnter hXY W).1 =
      PathFilterComponents.quotientWarpEdges H Y W.1 :=
    G.familyEdges_fullWaveToLargerQuotient hNoEnter hXY W
  rcases p with f | r
  · let rf : FinitePath H.graph := f.lift hgraph
    change z ∈ f.support at hzp
    have hrfEdges : rf.edgeSet ⊆ familyEdges W.1 := by
      intro e he
      have hef : e ∈ f.edgeSet := by
        rw [← finitePath_edgeSet_lift_fullClosure hgraph f]
        exact he
      have heFamily : e ∈ familyEdges
          (G.fullWaveToLargerQuotient hNoEnter hXY W).1 := by
        simp only [familyEdges, Set.mem_iUnion]
        exact ⟨Sum.inl f, hp, hef⟩
      rw [hfamily] at heFamily
      exact heFamily.1
    by_cases hends : rf.start = rf.finish
    · have hsupport : rf.walk.support = [rf.start] :=
        walk_support_eq_singleton_fullClosure rf.walk rf.isPath hends
      have hzStart : z = rf.start := by
        have hzrf : z ∈ rf.support := by
          simpa only [rf, FinitePath.support_lift] using hzp
        change z ∈ rf.walk.support at hzrf
        rw [hsupport] at hzrf
        simpa using hzrf
      have hzVertex : z ∈ H.vertexSet W.1 := by
        have hzFull : z ∈ (G.quotient Y).vertexSet
            (G.fullWaveToLargerQuotient hNoEnter hXY W).1 :=
          ⟨Sum.inl f, hp, hzp⟩
        rw [G.vertexSet_fullWaveToLargerQuotient hNoEnter hXY W] at hzFull
        exact hzFull.1.resolve_right hzY
      obtain ⟨q, hqW, hzq⟩ := hzVertex
      refine ⟨q, hqW, ?_⟩
      intro v hv
      change v ∈ f.support at hv
      have hvrf : v ∈ rf.support := by
        simpa only [rf, FinitePath.support_lift] using hv
      change v ∈ rf.walk.support at hvrf
      rw [hsupport] at hvrf
      have hvz : v = z := by simpa [hzStart] using hvrf
      exact hvz ▸ hzq
    · obtain ⟨q, hqW, hrfq⟩ :=
        SwitchingCore.finitePath_isFragmentOf_of_edgeSet_subset_familyEdges
          W.2.1 rf hends hrfEdges
      refine ⟨q, hqW, ?_⟩
      intro v hv
      change v ∈ f.support at hv
      apply hrfq.1
      change v ∈ rf.support
      rw [show rf.support = f.support from FinitePath.support_lift hgraph f]
      exact hv
  · have hedgeW (n : ℕ) : (r n, r (n + 1)) ∈ familyEdges W.1 := by
      have heFamily : (r n, r (n + 1)) ∈ familyEdges
          (G.fullWaveToLargerQuotient hNoEnter hXY W).1 := by
        simp only [familyEdges, Set.mem_iUnion]
        exact ⟨Sum.inr r, hp, ⟨n, rfl⟩⟩
      rw [hfamily] at heFamily
      exact heFamily.1
    obtain ⟨q, hqW, heq⟩ := by
      simpa only [familyEdges, Set.mem_iUnion] using hedgeW 0
    have hr0q : r 0 ∈ q.support :=
      (q.edgeSet_subset_support_prod heq).1
    refine ⟨q, hqW, ?_⟩
    rintro v ⟨n, rfl⟩
    induction n with
    | zero => exact hr0q
    | succ n ih =>
        have he := hedgeW n
        simp only [familyEdges, Set.mem_iUnion] at he
        obtain ⟨s, hsW, hrs⟩ := he
        have hrns : r n ∈ s.support :=
          (s.edgeSet_subset_support_prod hrs).1
        have hrnexts : r (n + 1) ∈ s.support :=
          (s.edgeSet_subset_support_prod hrs).2
        have hsq : s = q :=
          DWeb.IsWarp.eq_of_mem_support W.2.1 hsW hqW hrns ih
        exact hsq ▸ hrnexts

/-- Pair provenance from one full common stage to its genuine dependent
stage. -/
theorem exists_sectionSixFullAccumStage_path_containing_pair_of_commonStage
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ)
    {p : (G.quotient
      (G.sectionSixFullAccumClosure hNoEnter F K Y Q T y)).DPath}
    (hp : p ∈ (G.sectionSixFullAccumCommonStage
      hNoEnter F K Y Q T y n).1)
    {x z : V} (hxp : x ∈ p.support) (hzp : z ∈ p.support)
    (hz : z ∉ G.sectionSixFullAccumClosure hNoEnter F K Y Q T y) :
    ∃ q ∈ (G.sectionSixFullAccumStage
        hNoEnter F K Y Q T y n).wave.1,
      x ∈ q.support ∧ z ∈ q.support := by
  obtain ⟨q, hq, hpq⟩ :=
    G.exists_old_path_supporting_fullWaveToLargerQuotient_of_not_mem
      hNoEnter
      (G.sectionSixFullAccumStage_carrier_subset_closure
        hNoEnter F K Y Q T y n)
      (G.sectionSixFullAccumStage hNoEnter F K Y Q T y n).wave
      hp hzp hz
  exact ⟨q, hq, hpq hxp, hpq hzp⟩

theorem exists_later_sectionSixFullAccumStage_path_containing_pair
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V)
    (k : ℕ)
    {p : (G.quotient
      (G.sectionSixFullAccumClosure hNoEnter F K Y Q T y)).DPath}
    (hp : p ∈ (G.sectionSixFullAccumCommonWave
      hNoEnter F K Y Q T y).1)
    {x z : V} (hxp : x ∈ p.support) (hzp : z ∈ p.support)
    (hz : z ∉ G.sectionSixFullAccumClosure hNoEnter F K Y Q T y) :
    ∃ m, k ≤ m ∧
      ∃ q ∈ (G.sectionSixFullAccumStage hNoEnter F K Y Q T y m).wave.1,
        x ∈ q.support ∧ z ∈ q.support := by
  let X := G.sectionSixFullAccumClosure hNoEnter F K Y Q T y
  let H := G.quotient X
  let C := G.sectionSixFullAccumCommonStage hNoEnter F K Y Q T y
  obtain ⟨m, hkm, q, hqC, hxq, hzq⟩ :=
    H.exists_later_input_path_containing_pair_of_supportCofinal C
      (G.sectionSixFullAccumCommonStage_supportCofinal_succ
        hNoEnter F K Y Q T y) k hp hxp hzp
  obtain ⟨r, hr, hxr, hzr⟩ :=
    G.exists_sectionSixFullAccumStage_path_containing_pair_of_commonStage
      hNoEnter F K Y Q T y m hqC hxq hzq hz
  exact ⟨m, hkm, r, hr, hxr, hzr⟩

/-- Exact path provenance consumed by the boundary and tree closing
clauses. -/
theorem sectionSixFullAccum_path_provenance
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) :
    let X := G.sectionSixFullAccumClosure hNoEnter F K Y Q T y
    let H := G.quotient X
    let M := G.sectionSixFullAccumCommonWave hNoEnter F K Y Q T y
    ∀ p ∈ H.essentialWarpPart M.1, ∀ x ∈ p.support, x ∈ X →
      ∀ z ∈ p.support, z ∉ X →
        ∃ n, ∃ q ∈
          (G.sectionSixFullAccumStage hNoEnter F K Y Q T y n).wave.1,
            (q.support ∩
              (G.sectionSixFullAccumStage
                hNoEnter F K Y Q T y n).carrier).Nonempty ∧
            z ∈ q.support := by
  dsimp only
  intro p hp x hxp hxX z hzp hzX
  obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hxX
  obtain ⟨m, hkm, q, hq, hxq, hzq⟩ :=
    G.exists_later_sectionSixFullAccumStage_path_containing_pair
      hNoEnter F K Y Q T y k hp.1 hxp hzp hzX
  refine ⟨m, q, hq, ?_, hzq⟩
  exact ⟨x, hxq,
    G.sectionSixFullAccumStage_carrier_mono
      hNoEnter F K Y Q T y hkm hxk⟩

theorem exists_sectionSixFullAccumStage_path_meeting_of_mem_closure_essential
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) {z : V}
    (hzX : z ∈ G.sectionSixFullAccumClosure hNoEnter F K Y Q T y)
    (hzEss : z ∈ G.essential
      (G.sectionSixFullAccumClosure hNoEnter F K Y Q T y)) :
    ∃ n, ∃ p ∈
      (G.sectionSixFullAccumStage hNoEnter F K Y Q T y n).wave.1,
        (p.support ∩
          (G.sectionSixFullAccumStage
            hNoEnter F K Y Q T y n).carrier).Nonempty ∧
        z ∈ p.support := by
  let X := G.sectionSixFullAccumClosure hNoEnter F K Y Q T y
  obtain ⟨k, hzk⟩ := Set.mem_iUnion.mp hzX
  let s := G.sectionSixFullAccumStage hNoEnter F K Y Q T y k
  let Xnext := G.sectionSixAccumNextCarrier F K Y Q T s
  let old := G.sectionSixFullAccumOldInNext hNoEnter F K Y Q T s
  let next := G.sectionSixFullAccumNext hNoEnter F K Y Q T s
  have hzCarrier : z ∈ s.carrier := hzk
  have hzNext : z ∈ Xnext :=
    G.sectionSixAccumStage_carrier_subset_next F K Y Q T s hzCarrier
  have hNextX : Xnext ⊆ X := by
    intro v hv
    apply Set.mem_iUnion_of_mem (k + 1)
    change v ∈ Xnext
    exact hv
  have hzEssNext : z ∈ G.essential Xnext :=
    G.essential_of_mem_of_subset_of_essential hNextX hzNext hzEss
  have hzEssQ : z ∈ (G.quotient s.carrier).essential Xnext :=
    G.quotient_essential_of_essential_larger hNoEnter
      (G.sectionSixAccumStage_carrier_subset_next F K Y Q T s)
      hzEssNext
  have hzOldVertex : z ∈ (G.quotient Xnext).vertexSet old.1 := by
    rw [show old = G.fullWaveToLargerQuotient hNoEnter
      (G.sectionSixAccumStage_carrier_subset_next F K Y Q T s) s.wave by rfl,
      G.vertexSet_fullWaveToLargerQuotient hNoEnter
        (G.sectionSixAccumStage_carrier_subset_next F K Y Q T s) s.wave]
    exact ⟨Or.inr hzNext, fun hs ↦ hs.2 hzEssQ⟩
  obtain ⟨p, hpOld, hzp⟩ := hzOldVertex
  obtain ⟨q, hqNext, hpq⟩ :=
    (G.sectionSixFullAccumOldInNext_le_next
      hNoEnter F K Y Q T s).1 p hpOld
  have hzq : z ∈ q.support :=
    (G.quotient Xnext).support_mono_of_extends hpq hzp
  refine ⟨k + 1, q, ?_, ?_, hzq⟩
  · change q ∈ next.wave.1
    exact hqNext
  · change (q.support ∩ Xnext).Nonempty
    exact ⟨z, hzq, hzNext⟩

theorem sectionSixFullAccum_F_subset_closure_of_stage_path
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y z : V)
    (hzY : z ∈ Y)
    (hstage : ∃ n, ∃ p ∈
      (G.sectionSixFullAccumStage hNoEnter F K Y Q T y n).wave.1,
        (p.support ∩
          (G.sectionSixFullAccumStage
            hNoEnter F K Y Q T y n).carrier).Nonempty ∧
        z ∈ p.support) :
    F z ⊆ G.sectionSixFullAccumClosure hNoEnter F K Y Q T y := by
  obtain ⟨n, p, hp, hpMeet, hzp⟩ := hstage
  let s := G.sectionSixFullAccumStage hNoEnter F K Y Q T y n
  let p' : G.DPath := G.liftQuotientPath s.carrier p
  have hp' : p' ∈ G.sectionSixAccumStageLift s := ⟨p, hp, rfl⟩
  have hp'Meet : (p'.support ∩ s.carrier).Nonempty := by
    simpa only [p', G.support_liftQuotientPath] using hpMeet
  have hzp' : z ∈ p'.support := by
    simpa only [p', G.support_liftQuotientPath] using hzp
  apply G.sectionSixFullAccum_F_subset_closure hNoEnter F K Y Q T y n
  refine ⟨hzY, ?_⟩
  exact Set.mem_iUnion_of_mem p'
    (Set.mem_iUnion_of_mem ⟨hp', hp'Meet⟩ hzp')

theorem sectionSixFullAccum_mem_closure_of_stage_path
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y z : V)
    (hzT : z ∈ T)
    (hstage : ∃ n, ∃ p ∈
      (G.sectionSixFullAccumStage hNoEnter F K Y Q T y n).wave.1,
        (p.support ∩
          (G.sectionSixFullAccumStage
            hNoEnter F K Y Q T y n).carrier).Nonempty ∧
        z ∈ p.support) :
    z ∈ G.sectionSixFullAccumClosure hNoEnter F K Y Q T y := by
  obtain ⟨n, p, hp, hpMeet, hzp⟩ := hstage
  let s := G.sectionSixFullAccumStage hNoEnter F K Y Q T y n
  let p' : G.DPath := G.liftQuotientPath s.carrier p
  have hp' : p' ∈ G.sectionSixAccumStageLift s := ⟨p, hp, rfl⟩
  have hp'Meet : (p'.support ∩ s.carrier).Nonempty := by
    simpa only [p', G.support_liftQuotientPath] using hpMeet
  have hzp' : z ∈ p'.support := by
    simpa only [p', G.support_liftQuotientPath] using hzp
  apply G.sectionSixFullAccum_meetingTree_subset_closure
    hNoEnter F K Y Q T y n
  refine ⟨?_, hzT⟩
  exact Set.mem_iUnion_of_mem p'
    (Set.mem_iUnion_of_mem ⟨hp', hp'Meet⟩ hzp')

theorem sectionSixFullAccum_F_subset_closure_of_mem_essential
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y z : V)
    (hzY : z ∈ Y)
    (hzX : z ∈ G.sectionSixFullAccumClosure hNoEnter F K Y Q T y)
    (hzEss : z ∈ G.essential
      (G.sectionSixFullAccumClosure hNoEnter F K Y Q T y)) :
    F z ⊆ G.sectionSixFullAccumClosure hNoEnter F K Y Q T y := by
  apply G.sectionSixFullAccum_F_subset_closure_of_stage_path
    hNoEnter F K Y Q T y z hzY
  exact G.exists_sectionSixFullAccumStage_path_meeting_of_mem_closure_essential
    hNoEnter F K Y Q T y hzX hzEss

/-- Proposition 6.3(b) for the full dependent closure. -/
theorem sectionSixFullAccum_boundary_closed
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) :
    let X := G.sectionSixFullAccumClosure hNoEnter F K Y Q T y
    let H := G.quotient X
    let M := G.sectionSixFullAccumCommonWave hNoEnter F K Y Q T y
    ∀ z ∈ Y, z ∈ H.vertexSet (H.essentialMeetingPaths M.1 X) →
      F z ⊆ X := by
  dsimp only
  intro z hzY hzVertex
  let X := G.sectionSixFullAccumClosure hNoEnter F K Y Q T y
  let H := G.quotient X
  let M := G.sectionSixFullAccumCommonWave hNoEnter F K Y Q T y
  obtain ⟨p, hpMeeting, hzp⟩ := hzVertex
  obtain ⟨hpEssential, hpMeet⟩ := hpMeeting
  obtain ⟨x, hxp, hxX⟩ := hpMeet
  by_cases hzX : z ∈ X
  · have hzEss : z ∈ G.essential X :=
      G.essential_closure_of_mem_wave_support_mem_closure
        hNoEnter M.2 hpEssential.1 hzp hzX
    exact G.sectionSixFullAccum_F_subset_closure_of_mem_essential
      hNoEnter F K Y Q T y z hzY hzX hzEss
  · apply G.sectionSixFullAccum_F_subset_closure_of_stage_path
      hNoEnter F K Y Q T y z hzY
    exact G.sectionSixFullAccum_path_provenance
      hNoEnter F K Y Q T y p hpEssential x hxp hxX z hzp hzX

/-- Proposition 6.3(d) for the full dependent closure. -/
theorem sectionSixFullAccum_meeting_tree_closed
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) :
    let X := G.sectionSixFullAccumClosure hNoEnter F K Y Q T y
    let H := G.quotient X
    let M := G.sectionSixFullAccumCommonWave hNoEnter F K Y Q T y
    H.vertexSet (H.essentialMeetingPaths M.1 X) ∩ T ⊆ X := by
  dsimp only
  intro z hz
  let X := G.sectionSixFullAccumClosure hNoEnter F K Y Q T y
  let H := G.quotient X
  let M := G.sectionSixFullAccumCommonWave hNoEnter F K Y Q T y
  by_cases hzX : z ∈ X
  · exact hzX
  · obtain ⟨p, hpMeeting, hzp⟩ := hz.1
    obtain ⟨hpEssential, hpMeet⟩ := hpMeeting
    obtain ⟨x, hxp, hxX⟩ := hpMeet
    apply G.sectionSixFullAccum_mem_closure_of_stage_path
      hNoEnter F K Y Q T y z hz.2
    exact G.sectionSixFullAccum_path_provenance
      hNoEnter F K Y Q T y p hpEssential x hxp hxX z hzp hzX

end DWeb

end Erdos599
