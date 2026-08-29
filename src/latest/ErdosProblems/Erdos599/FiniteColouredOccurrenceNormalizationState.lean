/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceNormalizationInterval
import ErdosProblems.Erdos599.FiniteColouredOccurrenceTerminalStep

/-!
# Prefix states inside one fixed safe occurrence word

This is the state needed by the root-tight normalization argument.  Unlike
`SafePrefixState`, it has no reverse-reachability side condition.  Every
chosen edge is required to lie in one fixed finite total word, and every
visited reference interval is anchored at the lower endpoint of that total
word's full removed interval.
-/

noncomputable section

namespace Erdos599.Alternating.FiniteColouredOccurrenceWord

open Set DirectedPath SwitchingCore.RelationalInterval

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

/-- A genuinely constructed safe prefix of a fixed finite total word. -/
structure FixedSafePrefixState
    (total : FiniteColouredOccurrenceWord W Y) where
  word : FiniteColouredOccurrenceWord W Y
  safe : word.IsIntervalSafe
  first_eq : word.vertex 0 = total.vertex 0
  forward_subset : word.forwardEdges ⊆ total.forwardEdges
  backward_subset : word.backwardEdges ⊆ total.backwardEdges
  phase : (word.forwardEdges = ∅ ∧
      word.vertex (Fin.last word.length) = total.vertex 0) ∨
    HasOutgoing word.backwardEdges (word.vertex (Fin.last word.length))
  intervals : ∀ p : FinitePath Gamma.graph, (Sum.inl p : Gamma.DPath) ∈ Y →
    word.backwardEdges ∩ p.edgeSet = ∅ ∨
      Nonempty (FullAnchoredPriorInterval p total.backwardEdges
        word.backwardEdges word.forwardEdges)

def FixedSafePrefixState.initial
    (total : FiniteColouredOccurrenceWord W Y) :
    FixedSafePrefixState total where
  word := emptyAt (total.vertex 0)
  safe := emptyAt_isIntervalSafe _
  first_eq := rfl
  forward_subset := by simp
  backward_subset := by simp
  phase := Or.inl ⟨emptyAt_forwardEdges _, rfl⟩
  intervals := by
    intro p hp
    left
    simp

theorem FixedSafePrefixState.current_totalBackward_incoming_imp_prefix
    (hY : Gamma.IsWarp Y) (hYfin : Gamma.HasFiniteCharacter Y)
    {total : FiniteColouredOccurrenceWord W Y}
    (S : FixedSafePrefixState total)
    (hback : HasOutgoing S.word.backwardEdges
      (S.word.vertex (Fin.last S.word.length)))
    (htotalIn : HasIncoming total.backwardEdges
      (S.word.vertex (Fin.last S.word.length))) :
    HasIncoming S.word.backwardEdges
      (S.word.vertex (Fin.last S.word.length)) := by
  let a := S.word.vertex (Fin.last S.word.length)
  obtain ⟨b, hab⟩ := hback
  have habY := S.word.backwardEdges_subset_familyEdges hab
  simp only [familyEdges, Set.mem_iUnion] at habY
  obtain ⟨owner, hownerY, habOwner⟩ := habY
  obtain ⟨p, hpEq⟩ := hYfin hownerY
  subst owner
  rcases S.intervals p hownerY with hempty | hprior
  · have : (a, b) ∈ S.word.backwardEdges ∩ p.edgeSet := ⟨hab, habOwner⟩
    exact False.elim (by simpa [hempty] using this)
  · let A := hprior.some
    obtain ⟨z, hza⟩ := htotalIn
    have hzaY := total.backwardEdges_subset_familyEdges hza
    simp only [familyEdges, Set.mem_iUnion] at hzaY
    obtain ⟨q, hqY, hzaQ⟩ := hzaY
    have haP : a ∈ p.support :=
      (p.edgeSet_subset_support_prod habOwner).1
    have haQ : a ∈ q.support := (q.edgeSet_subset_support_prod hzaQ).2
    have hqEq : q = .inl p :=
      DWeb.IsWarp.eq_of_mem_support hY hqY hownerY haQ haP
    subst q
    have hzaFull : (z, a) ∈ A.full.edgeSet := by
      rw [← A.total_removed_eq]
      exact ⟨hza, hzaQ⟩
    have haNeStart : a ≠ A.prior.start := by
      intro ha
      have hfull : A.full.start = a := A.same_start.symm.trans ha.symm
      exact FinitePath.no_incoming_edge_at_start A.full z (hfull ▸ hzaFull)
    have habPrior : (a, b) ∈ A.prior.edgeSet := by
      rw [← A.prefix_removed_eq]
      exact ⟨hab, habOwner⟩
    have haPrior : a ∈ A.prior.support :=
      (A.prior.edgeSet_subset_support_prod habPrior).1
    obtain ⟨x, hxa⟩ :=
      FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
        A.prior haPrior haNeStart
    exact ⟨x, by
      have : (x, a) ∈ S.word.backwardEdges ∩ p.edgeSet := by
        rw [A.prefix_removed_eq]
        exact hxa
      exact this.1⟩

/-- Unless the normalization has already reached the fixed terminal, its
chronological endpoint has an outgoing edge in the total forward relation.
This is the key progress fact: it is derived from the two exact word balances
and the full-lower anchoring, not stored as a continuation oracle. -/
theorem FixedSafePrefixState.current_eq_totalFinish_or_hasTotalForward
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {total : FiniteColouredOccurrenceWord W Y}
    (S : FixedSafePrefixState total)
    (hstartOff : total.vertex 0 ∉ Gamma.vertexSet Y)
    (hfinishOff : total.vertex (Fin.last total.length) ∉ Gamma.vertexSet Y) :
    S.word.vertex (Fin.last S.word.length) =
        total.vertex (Fin.last total.length) ∨
      HasOutgoing total.forwardEdges
        (S.word.vertex (Fin.last S.word.length)) := by
  classical
  let s := total.vertex 0
  let t := total.vertex (Fin.last total.length)
  let a := S.word.vertex (Fin.last S.word.length)
  change s ∉ Gamma.vertexSet Y at hstartOff
  change t ∉ Gamma.vertexSet Y at hfinishOff
  by_cases hat : a = t
  · exact Or.inl hat
  right
  have htotalBalance := total.edgeBalance_forward_sub_backward hW hY a
  change edgeBalance total.forwardEdges a - edgeBalance total.backwardEdges a =
    propInt (a = s) - propInt (a = t) at htotalBalance
  rcases S.phase with hzero | hback
  · have has : a = s := hzero.2
    have hst : s ≠ t := fun h ↦ hat (has.trans h)
    have hRout : ¬HasOutgoing total.backwardEdges a := by
      rintro ⟨b, hab⟩
      exact hstartOff (has.symm ▸
        (familyEdges_subset_vertexSet_prod Y
          (total.backwardEdges_subset_familyEdges hab)).1)
    have hRin : ¬HasIncoming total.backwardEdges a := by
      rintro ⟨b, hba⟩
      exact hstartOff (has.symm ▸
        (familyEdges_subset_vertexSet_prod Y
          (total.backwardEdges_subset_familyEdges hba)).2)
    have hRbalance : edgeBalance total.backwardEdges a = 0 := by
      simp [edgeBalance, hRout, hRin]
    have hdelta : edgeBalance total.forwardEdges a -
        edgeBalance total.backwardEdges a = 1 := by
      simpa [propInt, has, hst] using htotalBalance
    have hFb : edgeBalance total.forwardEdges a = 1 := by
      rw [hRbalance] at hdelta
      omega
    exact (edgeBalance_eq_one_iff.mp hFb).1
  · have haY : a ∈ Gamma.vertexSet Y := by
      obtain ⟨b, hab⟩ := hback
      exact (familyEdges_subset_vertexSet_prod Y
        (S.word.backwardEdges_subset_familyEdges hab)).1
    have has : a ≠ s := fun h ↦ hstartOff (h.symm ▸ haY)
    have hat' : a ≠ t := hat
    have htotalOutR : HasOutgoing total.backwardEdges a := by
      obtain ⟨b, hab⟩ := hback
      exact ⟨b, S.backward_subset hab⟩
    by_cases htotalInR : HasIncoming total.backwardEdges a
    · have hprefixInR :=
        S.current_totalBackward_incoming_imp_prefix hY hYfin hback htotalInR
      have hprefixNoOutF : ¬HasOutgoing S.word.forwardEdges a :=
        S.safe.no_forward_outgoing_at_backward_exit hW hY hYfin
          (by simpa only [S.first_eq] using hstartOff) hback
      have hprefixBalance := S.word.edgeBalance_forward_sub_backward hW hY a
      change edgeBalance S.word.forwardEdges a -
        edgeBalance S.word.backwardEdges a =
          propInt (a = S.word.vertex 0) - propInt (a = a) at hprefixBalance
      have haFirst : a ≠ S.word.vertex 0 :=
        fun h ↦ has (h.trans S.first_eq)
      have hprefixDelta : edgeBalance S.word.forwardEdges a -
          edgeBalance S.word.backwardEdges a = -1 := by
        simpa [propInt, haFirst] using hprefixBalance
      have hprefixInF : HasIncoming S.word.forwardEdges a := by
        by_contra hno
        have hFb : edgeBalance S.word.forwardEdges a = 0 := by
          simp [edgeBalance, hprefixNoOutF, hno]
        have hRb : edgeBalance S.word.backwardEdges a = 0 := by
          have hback' : HasOutgoing S.word.backwardEdges a := hback
          have hprefixInR' : HasIncoming S.word.backwardEdges a := hprefixInR
          simp [edgeBalance, hback', hprefixInR']
        rw [hFb, hRb] at hprefixDelta
        omega
      have htotalInF : HasIncoming total.forwardEdges a := by
        obtain ⟨x, hxa⟩ := hprefixInF
        exact ⟨x, S.forward_subset hxa⟩
      by_contra hnoOut
      have hFb : edgeBalance total.forwardEdges a = -1 := by
        have hnoOut' : ¬HasOutgoing total.forwardEdges a := hnoOut
        simp [edgeBalance, propInt, hnoOut', htotalInF]
      have hRb : edgeBalance total.backwardEdges a = 0 := by
        simp [edgeBalance, htotalOutR, htotalInR]
      have hdelta : edgeBalance total.forwardEdges a -
          edgeBalance total.backwardEdges a = 0 := by
        simpa [propInt, has, hat'] using htotalBalance
      rw [hFb, hRb] at hdelta
      omega
    · have hRb : edgeBalance total.backwardEdges a = 1 :=
        edgeBalance_eq_one_iff.mpr ⟨htotalOutR, htotalInR⟩
      have hFb : edgeBalance total.forwardEdges a = 1 := by
        have hdelta : edgeBalance total.forwardEdges a -
            edgeBalance total.backwardEdges a = 0 := by
          simpa [propInt, has, hat'] using htotalBalance
        rw [hRb] at hdelta
        omega
      exact (edgeBalance_eq_one_iff.mp hFb).1

#print axioms FixedSafePrefixState.current_totalBackward_incoming_imp_prefix
#print axioms FixedSafePrefixState.current_eq_totalFinish_or_hasTotalForward

end Erdos599.Alternating.FiniteColouredOccurrenceWord
