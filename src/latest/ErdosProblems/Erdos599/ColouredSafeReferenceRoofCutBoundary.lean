/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeReferenceRoofCut
import ErdosProblems.Erdos599.ColouredSafeStageRoofCutBoundary

/-!
# Rooted boundary from complete erased incidences in a reference roof cut

The signed balance comparison retains each old local-reference initial and
the exposed source. Every new terminal lies on the cutting frontier or is
the original finite endpoint. Reusing the existing rooted-component filter
then discards reentry roots without losing any required local-reference root.
-/

noncomputable section

namespace Erdos599.ColouredSafeReferenceRoofCut

open Set DirectedPath Alternating
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence
open Alternating.SwitchingCore Alternating.SwitchingCore.RelationalInterval
open ColouredSafeStageRoofCutBoundary

universe u

variable {V : Type u} {Gamma : DWeb V} {G : Set Gamma.DPath} {s : V}

def terminalDefect (A : Occurrence G s) (x : V) : Int :=
  match A.terminal? with
  | none => 0
  | some t => propInt (x = t)

theorem terminalDefect_eq_one_iff (A : Occurrence G s) (x : V) :
    terminalDefect A x = 1 ↔ A.terminal? = some x := by
  cases A with
  | infinite Q => simp [terminalDefect, CurrentSafeOccurrence.terminal?]
  | finite t Q => simp [terminalDefect, CurrentSafeOccurrence.terminal?, propInt, eq_comm]

private theorem terminalDefect_zero_or_one (A : Occurrence G s) (x : V) :
    terminalDefect A x = 0 ∨ terminalDefect A x = 1 := by
  cases A with
  | infinite Q => simp [terminalDefect, CurrentSafeOccurrence.terminal?]
  | finite t Q =>
    by_cases hxt : x = t <;> simp [terminalDefect, CurrentSafeOccurrence.terminal?, propInt, hxt]

private theorem terminalDefect_zero (A : Occurrence G s) {x : V}
    (hne : ∀ t, A.terminal? = some t → x ≠ t) : terminalDefect A x = 0 := by
  rcases terminalDefect_zero_or_one A x with h | h
  · exact h
  · exact False.elim (hne x ((terminalDefect_eq_one_iff A x).mp h) rfl)

private theorem balance_le_one (E : Set (V × V)) (x : V) : edgeBalance E x ≤ 1 := by
  classical
  by_cases hout : HasOutgoing E x <;> by_cases hin : HasIncoming E x <;>
    simp [edgeBalance, propInt, hout, hin]

private theorem propInt_nonnegative (P : Prop) : 0 ≤ propInt P := by
  classical
  by_cases h : P <;> simp [propInt, h]

theorem edgeBalance_forward_sub_backward (hG : Gamma.IsWarp G)
    (A : Occurrence G s) (hA : Valid A) (x : V) :
    edgeBalance A.forwardEdges x - edgeBalance A.backwardEdges x =
      propInt (x = s) - terminalDefect A x := by
  obtain ⟨W, hW, _hWfinite, hforward⟩ := hA
  cases A with
  | infinite Q hQ hfirst =>
    have h := (Q.retypeForward hforward).edgeBalance_forward_sub_backward hW hG x
    change edgeBalance Q.forwardEdges x - edgeBalance Q.backwardEdges x =
      propInt (x = Q.vertex 0) at h
    simpa only [CurrentSafeOccurrence.forwardEdges, CurrentSafeOccurrence.backwardEdges,
      terminalDefect, CurrentSafeOccurrence.terminal?, hfirst, sub_zero] using h
  | finite t Q hQ hfirst hlast =>
    have h := (Q.retypeForward hforward).edgeBalance_forward_sub_backward hW hG x
    change edgeBalance Q.forwardEdges x - edgeBalance Q.backwardEdges x =
      propInt (x = Q.vertex 0) - propInt (x = Q.vertex (Fin.last Q.length)) at h
    simpa only [CurrentSafeOccurrence.forwardEdges, CurrentSafeOccurrence.backwardEdges,
      terminalDefect, CurrentSafeOccurrence.terminal?, hfirst, hlast] using h

theorem balance_lower (hG : Gamma.IsWarp G) (A : Occurrence G s) (hA : Valid A)
    {K : Set Gamma.DPath} (hK : Gamma.IsWarp K)
    (hKE : familyEdges K ⊆ familyEdges G) {T : Set V} {x : V}
    (hxStrict : x ∈ Gamma.strictRoof T)
    (hin : ∀ y, (y, x) ∈ A.backwardEdges → (y, x) ∈ familyEdges K)
    (hout : ∀ y, (x, y) ∈ A.backwardEdges → (x, y) ∈ familyEdges K) :
    edgeBalance (familyEdges K) x + propInt (x = s) - terminalDefect A x ≤
      edgeBalance (edges A K T) x := by
  have hglobal := edgeBalance_forward_sub_backward hG A hA x
  obtain ⟨W, hW, _hWfinite, hforward⟩ := hA
  have hback : edgeBalance (backwardEdges A K) x = edgeBalance A.backwardEdges x := by
    have hin' : HasIncoming (backwardEdges A K) x ↔ HasIncoming A.backwardEdges x :=
      ⟨fun ⟨y, hy⟩ ↦ ⟨y, hy.1⟩, fun ⟨y, hy⟩ ↦ ⟨y, hy, hin y hy⟩⟩
    have hout' : HasOutgoing (backwardEdges A K) x ↔ HasOutgoing A.backwardEdges x :=
      ⟨fun ⟨y, hy⟩ ↦ ⟨y, hy.1⟩, fun ⟨y, hy⟩ ↦ ⟨y, hy, hout y hy⟩⟩
    simp only [edgeBalance, hin', hout']
  have hforwardLe : edgeBalance A.forwardEdges x ≤ edgeBalance (forwardEdges A T) x := by
    have hout' : HasOutgoing (forwardEdges A T) x ↔ HasOutgoing A.forwardEdges x :=
      ⟨fun ⟨y, hy⟩ ↦ ⟨y, hy.1⟩, fun ⟨y, hy⟩ ↦ ⟨y, hy, hxStrict⟩⟩
    have hin' : HasIncoming (forwardEdges A T) x → HasIncoming A.forwardEdges x :=
      fun ⟨y, hy⟩ ↦ ⟨y, hy.1⟩
    classical
    by_cases hgo : HasOutgoing A.forwardEdges x <;>
      by_cases hgi : HasIncoming A.forwardEdges x <;>
        by_cases hli : HasIncoming (forwardEdges A T) x <;>
          simp [edgeBalance, propInt, hout', hgo, hgi, hli] at *
  have hbalance : edgeBalance (edges A K T) x = edgeBalance (familyEdges K) x +
      edgeBalance (forwardEdges A T) x - edgeBalance (backwardEdges A K) x :=
    edgeBalance_eq_of_incidence hW hK (fun _ he ↦ he.2)
      (fun _ he ↦ hforward he.1) (incoming_removed A hKE) (outgoing_removed A hKE) x
  rw [hback] at hbalance
  omega

theorem balance_eq_reference_off_occurrence (A : Occurrence G s)
    (K : Set Gamma.DPath) (T : Set V) {x : V} (hx : x ∉ A.vertexSet) :
    edgeBalance (edges A K T) x = edgeBalance (familyEdges K) x := by
  have hf : ∀ edge ∈ A.forwardEdges, edge.1 ∈ A.vertexSet ∧ edge.2 ∈ A.vertexSet := by
    intro edge he
    cases A with
    | infinite Q => exact Q.forwardEdges_endpoints_mem_vertexSet he
    | finite t Q => exact Q.forwardEdges_endpoints_mem_vertexSet he
  have hb : ∀ edge ∈ A.backwardEdges, edge.1 ∈ A.vertexSet ∧ edge.2 ∈ A.vertexSet := by
    intro edge he
    cases A with
    | infinite Q => exact Q.backwardEdges_endpoints_mem_vertexSet he
    | finite t Q => exact Q.backwardEdges_endpoints_mem_vertexSet he
  have hout : HasOutgoing (edges A K T) x ↔ HasOutgoing (familyEdges K) x := by
    constructor
    · rintro ⟨y, hy | hy⟩
      · exact ⟨y, hy.1⟩
      · exact False.elim (hx (hf _ hy.1).1)
    · rintro ⟨y, hy⟩
      exact ⟨y, Or.inl ⟨hy, fun h ↦ hx (hb _ h.1).1⟩⟩
  have hin : HasIncoming (edges A K T) x ↔ HasIncoming (familyEdges K) x := by
    constructor
    · rintro ⟨y, hy | hy⟩
      · exact ⟨y, hy.1⟩
      · exact False.elim (hx (hf _ hy.1).2)
    · rintro ⟨y, hy⟩
      exact ⟨y, Or.inl ⟨hy, fun h ↦ hx (hb _ h.1).2⟩⟩
  simp only [edgeBalance, hout, hin]

theorem exists_rooted_finiteWarp (hG : Gamma.IsWarp G) (A : Occurrence G s)
    (hA : Valid A) (K : Set Gamma.DPath) (hK : Gamma.IsWarp K)
    (hKfinite : Gamma.HasFiniteCharacter K) (hKE : familyEdges K ⊆ familyEdges G)
    (hKI : Gamma.initialSet K ⊆ Gamma.initialSet G)
    (T : Set V) (hessential : Gamma.essential T = T)
    (hKT : Gamma.terminalFrontier K ⊆ T) (hKRoof : Gamma.vertexSet K ⊆ Gamma.roof T)
    (hfrontier : ∀ x ∈ Gamma.vertexSet K, x ∈ T → x ∈ Gamma.terminalFrontier K)
    (hlower : ∀ x ∈ A.vertexSet, x ∈ Gamma.strictRoof T →
      edgeBalance (familyEdges K) x + propInt (x = s) - terminalDefect A x ≤
        edgeBalance (edges A K T) x)
    (hterminalOff : ∀ t, A.terminal? = some t → t ∉ Gamma.vertexSet K)
    (hsStrict : s ∈ Gamma.strictRoof T) (hsOff : s ∉ Gamma.vertexSet K)
    (hsTerminal : ∀ t, A.terminal? = some t → s ≠ t) :
    ∃ P : Set Gamma.DPath, Gamma.IsWarp P ∧ Gamma.HasFiniteCharacter P ∧
      Gamma.initialSet P = Gamma.initialSet K ∪ {s} ∧
      Gamma.terminalFrontier P ⊆ T ∪ {x | A.terminal? = some x} ∧
      Gamma.vertexSet P ⊆ Gamma.roof T ∧
      Gamma.vertexSet P ⊆ Gamma.vertexSet K ∪ A.vertexSet ∧
      familyEdges P ⊆ edges A K T := by
  obtain ⟨U, hU, hUfinite, hUE, hUI, hURoof, hUCarrier⟩ :=
    exists_finiteWarp_roofed hG A hA K hK hKfinite hKE hKI T hessential hKT hKRoof
  have hnonneg : ∀ x ∉ T, 0 ≤ edgeBalance (familyEdges K) x := by
    intro x hx
    have hnot : edgeBalance (familyEdges K) x ≠ -1 := by
      intro hneg
      exact hx (hKT ((mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one
        hK hKfinite).2 (Or.inr hneg)))
    classical
    by_cases ho : HasOutgoing (familyEdges K) x <;>
      by_cases hi : HasIncoming (familyEdges K) x <;>
        simp [edgeBalance, propInt, ho, hi] at hnot ⊢
  have hterminal : Gamma.terminalFrontier U ⊆ T ∪ {x | A.terminal? = some x} := by
    intro x hx
    by_cases hxT : x ∈ T
    · exact Or.inl hxT
    right
    rcases (mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one
      hU hUfinite).1 hx with hxIso | hxBalance
    · have hxIsoK : x ∈ isolatedVertices K := hUI ▸ hxIso
      exact False.elim (hxT (hKT ⟨Gamma.trivialPath x, hxIsoK, by simp⟩))
    have hxA : x ∈ A.vertexSet := by
      by_contra hxNot
      rw [hUE, balance_eq_reference_off_occurrence A K T hxNot] at hxBalance
      have hn := hnonneg x hxT
      omega
    have hxU : x ∈ Gamma.vertexSet U := by
      obtain ⟨p, hp, hpx⟩ := hx
      exact ⟨p, hp, Gamma.terminal_mem_support hpx⟩
    have hxStrict : x ∈ Gamma.strictRoof T :=
      ⟨hURoof hxU, fun hxE ↦ hxT (Gamma.essential_subset T hxE)⟩
    have hl := hlower x hxA hxStrict
    have hn := hnonneg x hxT
    have hs := propInt_nonnegative (x = s)
    rw [← hUE, hxBalance] at hl
    rcases terminalDefect_zero_or_one A x with hzero | hone
    · omega
    · exact (terminalDefect_eq_one_iff A x).mp hone
  have hold : Gamma.initialSet K ⊆ Gamma.initialSet U := by
    intro x hx
    rcases (mem_initialSet_iff_isolated_or_edgeBalance_eq_one hK hKfinite).1 hx with
      hxIso | hxBalance
    · exact (mem_initialSet_iff_isolated_or_edgeBalance_eq_one hU hUfinite).2
        (Or.inl (hUI.symm ▸ hxIso))
    apply (mem_initialSet_iff_isolated_or_edgeBalance_eq_one hU hUfinite).2
    right
    rw [hUE]
    by_cases hxA : x ∈ A.vertexSet
    · have hxK : x ∈ Gamma.vertexSet K := by
        obtain ⟨p, hp, hpx⟩ := hx
        exact ⟨p, hp, hpx ▸ p.initial_mem_support⟩
      have hxNotT : x ∉ T := by
        intro hxT
        have ht := hfrontier x hxK hxT
        rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp hK] at ht
        exact ht.2 (edgeBalance_eq_one_iff.mp hxBalance).1
      have hxStrict : x ∈ Gamma.strictRoof T :=
        ⟨hKRoof hxK, fun hxE ↦ hxNotT (Gamma.essential_subset T hxE)⟩
      have hdefect : terminalDefect A x = 0 := terminalDefect_zero A (by
        intro t ht hxt
        exact hterminalOff t ht (hxt ▸ hxK))
      have hl := hlower x hxA hxStrict
      have hu := balance_le_one (edges A K T) x
      have hs := propInt_nonnegative (x = s)
      rw [hxBalance, hdefect] at hl
      omega
    · rw [balance_eq_reference_off_occurrence A K T hxA]
      exact hxBalance
  have hsource : s ∈ Gamma.initialSet U := by
    have hreference : edgeBalance (familyEdges K) s = 0 := by
      have hout : ¬HasOutgoing (familyEdges K) s :=
        fun ⟨y, hsy⟩ ↦ hsOff (familyEdges_subset_vertexSet_prod K hsy).1
      have hin : ¬HasIncoming (familyEdges K) s :=
        fun ⟨y, hys⟩ ↦ hsOff (familyEdges_subset_vertexSet_prod K hys).2
      simp [edgeBalance, propInt, hout, hin]
    have hl := hlower s A.source_mem_vertexSet hsStrict
    have hdefect := terminalDefect_zero A hsTerminal
    have hu := balance_le_one (edges A K T) s
    have hs : propInt (s = s) = 1 := by simp [propInt]
    rw [hreference, hdefect, hs] at hl
    apply (mem_initialSet_iff_isolated_or_edgeBalance_eq_one hU hUfinite).2
    right
    rw [hUE]
    omega
  let I : Set V := Gamma.initialSet K ∪ {s}
  have hI : I ⊆ Gamma.initialSet U := by
    rintro x (hx | hx)
    · exact hold hx
    · exact hx ▸ hsource
  refine ⟨rootedPruning U I, rootedPruning_isWarp hU I,
    rootedPruning_finiteCharacter hUfinite I, rootedPruning_initialSet_eq hI,
    (rootedPruning_terminalFrontier_subset U I).trans hterminal,
    (rootedPruning_vertexSet_subset U I).trans hURoof,
    (rootedPruning_vertexSet_subset U I).trans hUCarrier, ?_⟩
  exact (rootedPruning_familyEdges_subset U I).trans (le_of_eq hUE)

#print axioms edgeBalance_forward_sub_backward
#print axioms balance_lower
#print axioms exists_rooted_finiteWarp

end Erdos599.ColouredSafeReferenceRoofCut
