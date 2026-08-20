/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Gluing disjoint terminal arms to a linkage in a target set. -/

import ErdosProblems.Erdos717.ContractRigidity

open Function Set
open SimpleGraph

namespace Erdos717
namespace ThomasWollanMassed

universe u v

variable {V : Type u} {ι : Type v}

/-- Two simple paths with only their common endpoint in common concatenate
to a simple path. -/
lemma Walk.IsPath.append_of_inter_eq_endpoint {G : SimpleGraph V}
    {a b c : V} {p : G.Walk a b} {q : G.Walk b c}
    (hp : p.IsPath) (hq : q.IsPath)
    (hinter : ∀ x, x ∈ p.support → x ∈ q.support → x = b) :
    (p.append q).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, List.nodup_append]
  have hpN : p.support.Nodup := (Walk.isPath_def p).mp hp
  have hqN : q.support.Nodup := (Walk.isPath_def q).mp hq
  refine ⟨hpN, hqN.tail, ?_⟩
  intro x hxp y hyq hxy
  subst y
  have hxq : x ∈ q.support := List.mem_of_mem_tail hyq
  have hxb : x = b := hinter x hxp hxq
  subst x
  rw [q.support_eq_cons] at hqN
  exact (List.nodup_cons.mp hqN).1 hyq

/-! ### Truncating a path at its first target vertex -/

/-- The first index along `p` whose vertex lies in `B`. -/
noncomputable def firstHitIndex {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (B : Set V) (hb : b ∈ B) : ℕ := by
  classical
  let witness : ∃ n, n ≤ p.length ∧ p.getVert n ∈ B :=
    ⟨p.length, le_rfl, by simpa using hb⟩
  exact Nat.find witness

lemma firstHitIndex_spec {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (B : Set V) (hb : b ∈ B) :
    firstHitIndex p B hb ≤ p.length ∧
      p.getVert (firstHitIndex p B hb) ∈ B := by
  classical
  let witness : ∃ n, n ≤ p.length ∧ p.getVert n ∈ B :=
    ⟨p.length, le_rfl, by simpa using hb⟩
  simpa only [firstHitIndex] using Nat.find_spec witness

/-- The prefix ending at the first target vertex. -/
noncomputable def takeFirstHit {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (B : Set V) (hb : b ∈ B) :
    G.Walk a (p.getVert (firstHitIndex p B hb)) :=
  p.take (firstHitIndex p B hb)

lemma support_takeFirstHit_subset {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (B : Set V) (hb : b ∈ B) :
    ∀ x, x ∈ (takeFirstHit p B hb).support → x ∈ p.support := by
  intro x hx
  rw [takeFirstHit, Walk.support_take] at hx
  exact List.mem_of_mem_take hx

lemma takeFirstHit_meets_target_only_at_end [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (B : Set V) (hb : b ∈ B) {x : V}
    (hx : x ∈ (takeFirstHit p B hb).support) (hxB : x ∈ B) :
    x = p.getVert (firstHitIndex p B hb) := by
  classical
  let witness : ∃ n, n ≤ p.length ∧ p.getVert n ∈ B :=
    ⟨p.length, le_rfl, by simpa using hb⟩
  have hxFull : x ∈ p.support := support_takeFirstHit_subset p B hb x hx
  have hidxLt : p.support.idxOf x < firstHitIndex p B hb + 1 := by
    rw [takeFirstHit, Walk.support_take,
      List.mem_take_iff_idxOf_lt hxFull] at hx
    exact hx
  have hidxLe : p.support.idxOf x ≤ p.length := by
    have := List.idxOf_lt_length_of_mem hxFull
    rw [Walk.length_support] at this
    omega
  have hmin : firstHitIndex p B hb ≤ p.support.idxOf x := by
    simpa only [firstHitIndex] using
      Nat.find_min' witness ⟨hidxLe, by
        rwa [p.getVert_support_idxOf hxFull]⟩
  have heq : p.support.idxOf x = firstHitIndex p B hb := by omega
  rw [← p.getVert_support_idxOf hxFull, heq]

lemma isPath_takeFirstHit [DecidableEq V] {G : SimpleGraph V} {a b : V}
    {p : G.Walk a b} (hp : p.IsPath) (B : Set V) (hb : b ∈ B) :
    (takeFirstHit p B hb).IsPath := by
  exact hp.take _

/-- Terminal-disjoint arms from a prescribed terminal embedding to distinct
anchors in a target set.  Apart from its anchor, each arm stays outside the
target. -/
structure TerminalArms (G : SimpleGraph V) (B : Set V)
    (terminal : Sum ι ι ↪ V) where
  anchor : Sum ι ι ↪ V
  anchor_mem : Set.range anchor ⊆ B
  path : ∀ z, G.Walk (terminal z) (anchor z)
  isPath : ∀ z, (path z).IsPath
  disjoint : Pairwise fun z w =>
    Disjoint {x | x ∈ (path z).support} {x | x ∈ (path w).support}
  meets_target_only_at_anchor : ∀ z x,
    x ∈ (path z).support → x ∈ B → x = anchor z

namespace TerminalArms

/-- A fully disjoint family of `A`–`B` paths, with one source for every
terminal, yields terminal arms after truncation at the first target hit. -/
noncomputable def ofABLinkage {W : Type} [Fintype W] [DecidableEq W]
    [Fintype ι] {G : SimpleGraph W} {B : Set W}
    {terminal : Sum ι ι ↪ W}
    (P : Erdos718.ABLinkage G (Set.range terminal) B
      (Fintype.card (Sum ι ι))) : TerminalArms G B terminal := by
  classical
  let leftMap : Fin (Fintype.card (Sum ι ι)) →
      (Set.range terminal : Set W) := fun i => ⟨P.left i, P.left_mem i⟩
  have hleftInj : Function.Injective leftMap := by
    intro i j hij
    by_contra hne
    have hval : P.left i = P.left j := congrArg Subtype.val hij
    have hjmem : P.left i ∈ (P.path j).support := by
      rw [hval]
      exact (P.path j).start_mem_support
    exact (Set.disjoint_left.mp (P.disjoint hne)
      (P.path i).start_mem_support hjmem).elim
  have hcardRange : Fintype.card (Set.range terminal : Set W) =
      Fintype.card (Sum ι ι) := by
    rw [Set.fintypeCard_eq_ncard, Set.ncard_range_of_injective terminal.injective]
    exact Nat.card_eq_fintype_card
  have hleftBij : Function.Bijective leftMap :=
    (Fintype.bijective_iff_injective_and_card leftMap).mpr
      ⟨hleftInj, by simp [hcardRange]⟩
  let leftEquiv : Fin (Fintype.card (Sum ι ι)) ≃
      (Set.range terminal : Set W) := Equiv.ofBijective leftMap hleftBij
  let index (z : Sum ι ι) : Fin (Fintype.card (Sum ι ι)) :=
    leftEquiv.symm ⟨terminal z, ⟨z, rfl⟩⟩
  have hleft (z : Sum ι ι) : P.left (index z) = terminal z := by
    have h := leftEquiv.apply_symm_apply ⟨terminal z, ⟨z, rfl⟩⟩
    exact congrArg Subtype.val h
  have hindexInj : Function.Injective index := by
    intro z w hzw
    apply terminal.injective
    rw [← hleft z, ← hleft w, hzw]
  let anchor (z : Sum ι ι) : W :=
    (P.path (index z)).getVert
      (firstHitIndex (P.path (index z)) B (P.right_mem (index z)))
  have hanchorMem (z : Sum ι ι) : anchor z ∈ B := by
    exact (firstHitIndex_spec (P.path (index z)) B
      (P.right_mem (index z))).2
  have hanchorInj : Function.Injective anchor := by
    intro z w hzw
    by_contra hne
    have hidxne : index z ≠ index w := fun h => hne (hindexInj h)
    have hzSupp : anchor z ∈ (P.path (index z)).support := by
      exact (P.path (index z)).getVert_mem_support _
    have hwSupp : anchor w ∈ (P.path (index w)).support := by
      exact (P.path (index w)).getVert_mem_support _
    exact (Set.disjoint_left.mp (P.disjoint hidxne) hzSupp
      (by rwa [hzw] at hzSupp ⊢)).elim
  let anchorEmb : Sum ι ι ↪ W := ⟨anchor, hanchorInj⟩
  refine {
    anchor := anchorEmb
    anchor_mem := fun _ ⟨z, hz⟩ => hz ▸ hanchorMem z
    path := fun z => (takeFirstHit (P.path (index z)) B
      (P.right_mem (index z))).copy (hleft z) rfl
    isPath := fun z => by
      simpa only [Walk.isPath_copy] using isPath_takeFirstHit
        (P.isPath (index z)) B (P.right_mem (index z))
    disjoint := ?_
    meets_target_only_at_anchor := ?_
  }
  · intro z w hzw
    apply Set.disjoint_left.mpr
    intro x hxz hxw
    have hxz₀ : x ∈ (takeFirstHit (P.path (index z)) B
        (P.right_mem (index z))).support := by
      simpa only [Set.mem_setOf_eq, Walk.support_copy] using hxz
    have hxw₀ : x ∈ (takeFirstHit (P.path (index w)) B
        (P.right_mem (index w))).support := by
      simpa only [Set.mem_setOf_eq, Walk.support_copy] using hxw
    have hxz' : x ∈ (P.path (index z)).support := by
      apply support_takeFirstHit_subset (P.path (index z)) B
        (P.right_mem (index z)) x
      exact hxz₀
    have hxw' : x ∈ (P.path (index w)).support := by
      apply support_takeFirstHit_subset (P.path (index w)) B
        (P.right_mem (index w)) x
      exact hxw₀
    exact (Set.disjoint_left.mp (P.disjoint (hindexInj.ne hzw)) hxz' hxw').elim
  · intro z x hx hxB
    change x = anchor z
    exact takeFirstHit_meets_target_only_at_end (P.path (index z)) B
      (P.right_mem (index z)) (by simpa only [Walk.support_copy] using hx) hxB

/-- Glue terminal arms to a linkage between their anchors in the target
set. -/
noncomputable def glue [Fintype ι] {G : SimpleGraph V} {B : Set V}
    {terminal : Sum ι ι ↪ V} (A : TerminalArms G B terminal)
    (L : Erdos718.PairLinkage (G.induce B)
      {x : B | (x : V) ∈ Set.range A.anchor}
      (terminalIntoSet B A.anchor A.anchor_mem)) :
    Erdos718.PairLinkage G (Set.range terminal) terminal := by
  let M : Erdos718.PairLinkage G (Set.range A.anchor) A.anchor :=
    Erdos718.PairLinkage.liftInduce A.anchor_mem L
  let q (i : ι) :=
    ((A.path (.inl i)).append (M.path i)).append
      (A.path (.inr i)).reverse
  have hMsubset (i : ι) {x : V} (hx : x ∈ (M.path i).support) : x ∈ B := by
    exact Erdos718.PairLinkage.support_liftInduce_subset
      A.anchor_mem L i (by simpa only [M] using hx)
  have harm_terminal (z w : Sum ι ι)
      (h : terminal w ∈ (A.path z).support) : w = z := by
    by_contra hwz
    have hw := (A.path w).start_mem_support
    exact (Set.disjoint_left.mp (A.disjoint hwz) hw h).elim
  have hcentral_anchor (i : ι) (z : Sum ι ι)
      (hz : A.anchor z ∈ (M.path i).support) :
      z = .inl i ∨ z = .inr i := by
    by_contra h
    push_neg at h
    have hinterior : A.anchor z ∈
        Erdos718.walkInteriorSet (M.path i) := ⟨hz,
      fun heq => h.1 (A.anchor.injective heq),
      fun heq => h.2 (A.anchor.injective heq)⟩
    exact (Set.disjoint_left.mp (M.avoids i) hinterior ⟨z, rfl⟩).elim
  have hleft_middle (i : ι) :
      ((A.path (.inl i)).append (M.path i)).IsPath := by
    apply Walk.IsPath.append_of_inter_eq_endpoint
      (A.isPath (.inl i)) (M.isPath i)
    intro x hxA hxM
    exact A.meets_target_only_at_anchor (.inl i) x hxA (hMsubset i hxM)
  have hwhole (i : ι) : (q i).IsPath := by
    apply Walk.IsPath.append_of_inter_eq_endpoint (hleft_middle i)
      (A.isPath (.inr i)).reverse
    intro x hxLM hxR
    rw [Walk.support_append] at hxLM
    rw [Walk.support_reverse] at hxR
    have hxR' : x ∈ (A.path (.inr i)).support := by
      simpa using hxR
    have hxCases : x ∈ (A.path (.inl i)).support ∨
        x ∈ (M.path i).support := by
      exact (List.mem_append.mp hxLM).imp_right List.mem_of_mem_tail
    rcases hxCases with hxLeft | hxMiddle
    · have hne : (Sum.inl i : Sum ι ι) ≠ Sum.inr i := Sum.inl_ne_inr
      exact (Set.disjoint_left.mp (A.disjoint hne) hxLeft hxR').elim
    · exact A.meets_target_only_at_anchor (.inr i) x hxR'
        (hMsubset i hxMiddle)
  refine {
    path := q
    isPath := hwhole
    avoids := ?_
    disjoint := ?_
  }
  · intro i
    rw [Set.disjoint_left]
    intro x hx hterminal
    rcases hx with ⟨hxsupp, hxstart, hxend⟩
    simp only [q, Walk.support_append, Walk.support_reverse,
      List.mem_append] at hxsupp
    rcases hxsupp with (hxLeft | hxMiddle) | hxRight
    · rcases hterminal with ⟨z, hz⟩
      have hzmem : terminal z ∈ (A.path (.inl i)).support := by
        simpa [hz] using hxLeft
      have hzEq := harm_terminal (.inl i) z hzmem
      subst z
      exact hxstart hz.symm
    · have hxMiddle' : x ∈ (M.path i).support :=
        List.mem_of_mem_tail hxMiddle
      rcases hterminal with ⟨z, hz⟩
      have hzArm : x ∈ (A.path z).support := by
        rw [← hz]
        exact (A.path z).start_mem_support
      have hxAnchor : x = A.anchor z :=
        A.meets_target_only_at_anchor z x hzArm (hMsubset i hxMiddle')
      have hzCentral : A.anchor z ∈ (M.path i).support := by
        rwa [← hxAnchor]
      rcases hcentral_anchor i z hzCentral with rfl | rfl
      · exact hxstart hz.symm
      · exact hxend hz.symm
    · have hxRight' : x ∈ (A.path (.inr i)).support := by
        have : x ∈ (A.path (.inr i)).support.reverse :=
          List.mem_of_mem_tail hxRight
        simpa using this
      rcases hterminal with ⟨z, hz⟩
      have hzmem : terminal z ∈ (A.path (.inr i)).support := by
        simpa [hz] using hxRight'
      have hzEq := harm_terminal (.inr i) z hzmem
      subst z
      exact hxend hz.symm
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    simp only [q, Walk.support_append, Walk.support_reverse,
      List.mem_append] at hxi hxj
    have split (r : ι) (h :
        (x ∈ (A.path (.inl r)).support ∨
          x ∈ (M.path r).support.tail) ∨
          x ∈ (A.path (.inr r)).support.reverse.tail) :
        x ∈ (A.path (.inl r)).support ∨
          x ∈ (M.path r).support ∨ x ∈ (A.path (.inr r)).support := by
      rcases h with (h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (List.mem_of_mem_tail h))
      · exact Or.inr (Or.inr (by
          have : x ∈ (A.path (.inr r)).support.reverse :=
            List.mem_of_mem_tail h
          simpa using this))
    rcases split i hxi with hiL | hiM | hiR <;>
      rcases split j hxj with hjL | hjM | hjR
    · exact (Set.disjoint_left.mp (A.disjoint (fun h =>
        hij (Sum.inl.inj h))) hiL hjL).elim
    · have hiA := A.meets_target_only_at_anchor (.inl i) x hiL
        (hMsubset j hjM)
      have hz := hcentral_anchor j (.inl i) (by rwa [← hiA])
      rcases hz with hz | hz
      · exact hij (Sum.inl.inj hz)
      · exact Sum.inl_ne_inr hz
    · exact (Set.disjoint_left.mp (A.disjoint Sum.inl_ne_inr) hiL hjR).elim
    · have hjA := A.meets_target_only_at_anchor (.inl j) x hjL
        (hMsubset i hiM)
      have hz := hcentral_anchor i (.inl j) (by rwa [← hjA])
      rcases hz with hz | hz
      · exact hij (Sum.inl.inj hz).symm
      · exact Sum.inl_ne_inr hz
    · exact (Set.disjoint_left.mp (M.disjoint hij) hiM hjM).elim
    · have hjA := A.meets_target_only_at_anchor (.inr j) x hjR
        (hMsubset i hiM)
      have hz := hcentral_anchor i (.inr j) (by rwa [← hjA])
      rcases hz with hz | hz
      · exact Sum.inr_ne_inl hz
      · exact hij (Sum.inr.inj hz).symm
    · exact (Set.disjoint_left.mp (A.disjoint Sum.inr_ne_inl) hiR hjL).elim
    · have hiA := A.meets_target_only_at_anchor (.inr i) x hiR
        (hMsubset j hjM)
      have hz := hcentral_anchor j (.inr i) (by rwa [← hiA])
      rcases hz with hz | hz
      · exact Sum.inr_ne_inl hz
      · exact hij (Sum.inr.inj hz)
    · exact (Set.disjoint_left.mp (A.disjoint (fun h =>
        hij (Sum.inr.inj h))) hiR hjR).elim

/-- A linked set in the target region joins any family of terminal arms whose
anchors lie in that linked set. -/
theorem nonempty_pairLinkage_of_isLinkedSet {J : Type} [Fintype J]
    {G : SimpleGraph V} {B : Set V} {terminal : Sum J J ↪ V}
    (A : TerminalArms G B terminal) (S : Set B)
    (hanchor : Set.range (terminalIntoSet B A.anchor A.anchor_mem) ⊆ S)
    (hlinked : Erdos718.IsLinkedSet (G.induce B) S) :
    Nonempty (Erdos718.PairLinkage G (Set.range terminal) terminal) := by
  obtain ⟨L⟩ := hlinked J (terminalIntoSet B A.anchor A.anchor_mem) hanchor
  have hsmall : {x : B | (x : V) ∈ Set.range A.anchor} ⊆ S := by
    rintro x ⟨z, hz⟩
    have hx : x = terminalIntoSet B A.anchor A.anchor_mem z := by
      apply Subtype.ext
      exact hz.symm
    rw [hx]
    exact hanchor ⟨z, rfl⟩
  let L' : Erdos718.PairLinkage (G.induce B)
      {x : B | (x : V) ∈ Set.range A.anchor}
      (terminalIntoSet B A.anchor A.anchor_mem) := {
    path := L.path
    isPath := L.isPath
    avoids := fun i => (L.avoids i).mono_right hsmall
    disjoint := L.disjoint
  }
  exact ⟨A.glue L'⟩

end TerminalArms

/-! ### Crossing a separation into its linked right side -/

/-- When disjoint terminal paths are truncated at their first entry into the
right side of a separation, every resulting anchor lies in the separator. -/
lemma anchor_mem_separator_of_left
    {W : Type} [Fintype W] [DecidableEq W]
    {J : Type} [Fintype J] {G : SimpleGraph W}
    {terminal : Sum J J ↪ W} (s : Erdos718.Separation G)
    (hterminalLeft : Set.range terminal ⊆ (s.left : Set W))
    (A : TerminalArms G (s.right : Set W) terminal) (z : Sum J J) :
    A.anchor z ∈ s.separator := by
  have hright : A.anchor z ∈ s.right := A.anchor_mem ⟨z, rfl⟩
  have hstartLeft : terminal z ∈ s.left := hterminalLeft ⟨z, rfl⟩
  rw [Erdos718.Separation.separator, Finset.mem_inter]
  refine ⟨?_, hright⟩
  by_contra hnotLeft
  by_cases hstartRight : terminal z ∈ s.right
  · have hstartEq : terminal z = A.anchor z :=
      A.meets_target_only_at_anchor z _ (A.path z).start_mem_support hstartRight
    exact hnotLeft (hstartEq ▸ hstartLeft)
  · have hstartStrict : terminal z ∈ s.left \ s.right :=
      Finset.mem_sdiff.mpr ⟨hstartLeft, hstartRight⟩
    have hendStrict : A.anchor z ∈ s.right \ s.left :=
      Finset.mem_sdiff.mpr ⟨hright, hnotLeft⟩
    obtain ⟨x, hxPath, hxSep⟩ :=
      s.walk_meets_separator (A.path z) hstartStrict hendStrict
    have hxRight : x ∈ s.right := (Finset.mem_inter.mp hxSep).2
    have hxEq := A.meets_target_only_at_anchor z x hxPath hxRight
    exact hnotLeft (hxEq ▸ (Finset.mem_inter.mp hxSep).1)

/-- Disjoint paths from all terminals into a separation with linked right
boundary solve the prescribed pairing in the whole graph. -/
theorem nonempty_pairLinkage_of_abLinkage_to_linked_right
    {W : Type} [Fintype W] [DecidableEq W]
    {J : Type} [Fintype J] {G : SimpleGraph W}
    {terminal : Sum J J ↪ W} (s : Erdos718.Separation G)
    (hterminalLeft : Set.range terminal ⊆ (s.left : Set W))
    (P : Erdos718.ABLinkage G (Set.range terminal) (s.right : Set W)
      (Fintype.card (Sum J J)))
    (hlinked : Erdos718.IsLinkedSet (G.induce (s.right : Set W))
      (rightSeparator s : Set (s.right : Set W))) :
    Nonempty (Erdos718.PairLinkage G (Set.range terminal) terminal) := by
  let A := TerminalArms.ofABLinkage P
  apply A.nonempty_pairLinkage_of_isLinkedSet
    (rightSeparator s : Set (s.right : Set W))
  · rintro _ ⟨z, rfl⟩
    change terminalIntoSet (s.right : Set W) A.anchor A.anchor_mem z ∈
      rightSeparator s
    rw [mem_rightSeparator]
    exact anchor_mem_separator_of_left s hterminalLeft A z
  · exact hlinked

end ThomasWollanMassed
end Erdos717
