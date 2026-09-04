/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Selecting prescribed terminal arms from a full set-to-set linkage. -/

import ErdosProblems.Erdos717.GlueLinkage

open Function Set
open SimpleGraph

namespace Erdos717
namespace ThomasWollanMassed

variable {V I : Type}

/-- Terminal arms which, apart from their own source, avoid a larger source
set `X`. -/
structure FullTerminalArms (G : SimpleGraph V) (X B : Set V)
    (terminal : Sum I I ↪ V) extends TerminalArms G B terminal where
  meets_source_only_at_terminal : ∀ z x,
    x ∈ (path z).support → x ∈ X → x = terminal z

/-- Select the arms needed by `terminal` from a maximum-size disjoint
`X`--`B` linkage, and truncate them at their first hit of `B`. -/
noncomputable def FullTerminalArms.ofABLinkage
    [Fintype V] [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} {X B : Set V} (hXfinite : X.Finite)
    {terminal : Sum I I ↪ V} (hterminal : Set.range terminal ⊆ X)
    (P : Erdos718.ABLinkage G X B X.ncard) :
    FullTerminalArms G X B terminal := by
  classical
  letI : Fintype X := hXfinite.fintype
  let leftMap : Fin X.ncard → X := fun i => ⟨P.left i, P.left_mem i⟩
  have hleftInj : Function.Injective leftMap := by
    intro i j hij
    by_contra hne
    have hval : P.left i = P.left j := congrArg Subtype.val hij
    have hjmem : P.left i ∈ (P.path j).support := by
      rw [hval]
      exact (P.path j).start_mem_support
    exact (Set.disjoint_left.mp (P.disjoint hne)
      (P.path i).start_mem_support hjmem).elim
  have hcardX : Fintype.card X = X.ncard := Set.fintypeCard_eq_ncard X
  have hleftBij : Function.Bijective leftMap :=
    (Fintype.bijective_iff_injective_and_card leftMap).mpr
      ⟨hleftInj, by simp [hcardX]⟩
  let leftEquiv : Fin X.ncard ≃ X := Equiv.ofBijective leftMap hleftBij
  let index (z : Sum I I) : Fin X.ncard :=
    leftEquiv.symm ⟨terminal z, hterminal ⟨z, rfl⟩⟩
  have hleft (z : Sum I I) : P.left (index z) = terminal z := by
    have h := leftEquiv.apply_symm_apply
      ⟨terminal z, hterminal ⟨z, rfl⟩⟩
    exact congrArg Subtype.val h
  have hindexInj : Function.Injective index := by
    intro z w hzw
    apply terminal.injective
    rw [← hleft z, ← hleft w, hzw]
  let anchor (z : Sum I I) : V :=
    (P.path (index z)).getVert
      (firstHitIndex (P.path (index z)) B (P.right_mem (index z)))
  have hanchorMem (z : Sum I I) : anchor z ∈ B :=
    (firstHitIndex_spec (P.path (index z)) B
      (P.right_mem (index z))).2
  have hanchorInj : Function.Injective anchor := by
    intro z w hzw
    by_contra hne
    have hidxne : index z ≠ index w := fun h => hne (hindexInj h)
    have hzSupp : anchor z ∈ (P.path (index z)).support :=
      (P.path (index z)).getVert_mem_support _
    have hwSupp : anchor w ∈ (P.path (index w)).support :=
      (P.path (index w)).getVert_mem_support _
    exact (Set.disjoint_left.mp (P.disjoint hidxne) hzSupp
      (by rwa [hzw] at hzSupp ⊢)).elim
  let anchorEmb : Sum I I ↪ V := ⟨anchor, hanchorInj⟩
  let arm (z : Sum I I) :=
    (takeFirstHit (P.path (index z)) B (P.right_mem (index z))).copy
      (hleft z) rfl
  have harmSub (z : Sum I I) {x : V} (hx : x ∈ (arm z).support) :
      x ∈ (P.path (index z)).support := by
    apply support_takeFirstHit_subset (P.path (index z)) B
      (P.right_mem (index z)) x
    simpa only [arm, Walk.support_copy] using hx
  have hsource (z : Sum I I) (x : V) (hx : x ∈ (arm z).support)
      (hxX : x ∈ X) : x = terminal z := by
    let j : Fin X.ncard := leftEquiv.symm ⟨x, hxX⟩
    have hjleft : P.left j = x := by
      exact congrArg Subtype.val (leftEquiv.apply_symm_apply ⟨x, hxX⟩)
    by_cases hj : j = index z
    · calc
        x = P.left j := hjleft.symm
        _ = P.left (index z) := congrArg P.left hj
        _ = terminal z := hleft z
    · have hxj : x ∈ (P.path j).support := by
        rw [← hjleft]
        exact (P.path j).start_mem_support
      exact (Set.disjoint_left.mp (P.disjoint hj) hxj (harmSub z hx)).elim
  refine {
    anchor := anchorEmb
    anchor_mem := fun _ ⟨z, hz⟩ => hz ▸ hanchorMem z
    path := arm
    isPath := fun z => by
      simpa only [arm, Walk.isPath_copy] using isPath_takeFirstHit
        (P.isPath (index z)) B (P.right_mem (index z))
    disjoint := ?_
    meets_target_only_at_anchor := ?_
    meets_source_only_at_terminal := hsource
  }
  · intro z w hzw
    apply Set.disjoint_left.mpr
    intro x hxz hxw
    exact (Set.disjoint_left.mp (P.disjoint (hindexInj.ne hzw))
      (harmSub z hxz) (harmSub w hxw)).elim
  · intro z x hx hxB
    change x = anchor z
    exact takeFirstHit_meets_target_only_at_end (P.path (index z)) B
      (P.right_mem (index z))
      (by simpa only [arm, Walk.support_copy] using hx) hxB

/-- Glue full-source-avoiding arms through a linked target set, retaining
avoidance of the whole source set rather than only the selected terminals. -/
theorem FullTerminalArms.nonempty_pairLinkage_of_isLinkedSet
    [Fintype I] {G : SimpleGraph V} {X B : Set V}
    {terminal : Sum I I ↪ V} (A : FullTerminalArms G X B terminal)
    (S : Set B)
    (hanchor : Set.range (terminalIntoSet B A.anchor A.anchor_mem) ⊆ S)
    (hsourceTarget : ∀ (x : V) (hxB : x ∈ B),
      x ∈ X → (⟨x, hxB⟩ : B) ∈ S)
    (hlinked : Erdos718.IsLinkedSet (G.induce B) S) :
    Nonempty (Erdos718.PairLinkage G X terminal) := by
  classical
  obtain ⟨L⟩ := hlinked I (terminalIntoSet B A.anchor A.anchor_mem) hanchor
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
  let R := A.toTerminalArms.glue L'
  refine ⟨{
    path := R.path
    isPath := R.isPath
    avoids := ?_
    disjoint := R.disjoint
  }⟩
  intro i
  rw [Set.disjoint_left]
  intro x hx hxX
  have hxstart : x ≠ terminal (.inl i) := hx.2.1
  have hxend : x ≠ terminal (.inr i) := hx.2.2
  have hsupport : x ∈
      (((A.path (.inl i)).append
        ((Erdos718.PairLinkage.liftInduce A.anchor_mem L').path i)).append
          (A.path (.inr i)).reverse).support := by
    simpa only [R, TerminalArms.glue] using hx.1
  simp only [Walk.support_append, Walk.support_reverse,
    List.mem_append] at hsupport
  rcases hsupport with (hxLeft | hxMiddle) | hxRight
  · exact hxstart (A.meets_source_only_at_terminal (.inl i) x hxLeft hxX)
  · have hxM : x ∈
        ((Erdos718.PairLinkage.liftInduce A.anchor_mem L').path i).support :=
      List.mem_of_mem_tail hxMiddle
    have hxB : x ∈ B :=
      Erdos718.PairLinkage.support_liftInduce_subset
        A.anchor_mem L' i hxM
    have hxS : (⟨x, hxB⟩ : B) ∈ S := hsourceTarget x hxB hxX
    have hxML : (⟨x, hxB⟩ : B) ∈ (L.path i).support := by
      dsimp only [Erdos718.PairLinkage.liftInduce] at hxM
      rw [Walk.support_copy, Walk.support_map] at hxM
      obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hxM
      have hyEq : y = ⟨x, hxB⟩ := Subtype.ext (by
        change (y : V) = x at hyx
        exact hyx)
      exact hyEq ▸ hy
    by_cases hleft : (⟨x, hxB⟩ : B) =
        terminalIntoSet B A.anchor A.anchor_mem (.inl i)
    · have hxAnchor : x = A.anchor (.inl i) := congrArg Subtype.val hleft
      have hxArm : x ∈ (A.path (.inl i)).support := by
        rw [hxAnchor]
        exact (A.path (.inl i)).end_mem_support
      exact hxstart (A.meets_source_only_at_terminal (.inl i) x hxArm hxX)
    by_cases hright : (⟨x, hxB⟩ : B) =
        terminalIntoSet B A.anchor A.anchor_mem (.inr i)
    · have hxAnchor : x = A.anchor (.inr i) := congrArg Subtype.val hright
      have hxArm : x ∈ (A.path (.inr i)).support := by
        rw [hxAnchor]
        exact (A.path (.inr i)).end_mem_support
      exact hxend (A.meets_source_only_at_terminal (.inr i) x hxArm hxX)
    · have hxInterior : (⟨x, hxB⟩ : B) ∈
          Erdos718.walkInteriorSet (L.path i) :=
        ⟨hxML, hleft, hright⟩
      exact (Set.disjoint_left.mp (L.avoids i) hxInterior hxS).elim
  · have hxRight' : x ∈ (A.path (.inr i)).support := by
      have : x ∈ (A.path (.inr i)).support.reverse :=
        List.mem_of_mem_tail hxRight
      simpa using this
    exact hxend (A.meets_source_only_at_terminal (.inr i) x hxRight' hxX)

/-- A full family of disjoint paths from a finite set `X` into the linked
right side of a separation makes `X` linked in the ambient graph. -/
theorem isLinkedSet_of_full_abLinkage_to_linked_right
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (s : Erdos718.Separation G) (X : Set V)
    (hXfinite : X.Finite) (hXleft : X ⊆ (s.left : Set V))
    (P : Erdos718.ABLinkage G X (s.right : Set V) X.ncard)
    (hright : Erdos718.IsLinkedSet (G.induce (s.right : Set V))
      (rightSeparator s : Set (s.right : Set V))) :
    Erdos718.IsLinkedSet G X := by
  intro I _ terminal hterminal
  let A := FullTerminalArms.ofABLinkage hXfinite hterminal P
  apply A.nonempty_pairLinkage_of_isLinkedSet
    (rightSeparator s : Set (s.right : Set V))
  · rintro _ ⟨z, rfl⟩
    change terminalIntoSet (s.right : Set V) A.anchor A.anchor_mem z ∈
      rightSeparator s
    rw [mem_rightSeparator]
    exact anchor_mem_separator_of_left s (hterminal.trans hXleft)
      A.toTerminalArms z
  · intro x hxR hxX
    change (⟨x, hxR⟩ : (s.right : Set V)) ∈ rightSeparator s
    rw [mem_rightSeparator]
    exact Finset.mem_inter.mpr ⟨hXleft hxX, hxR⟩
  · exact hright

/-- A full disjoint family from a finite source set into a target which is
linked in its induced graph makes the source set linked in the ambient
graph. -/
theorem isLinkedSet_of_full_abLinkage_to_linked_target
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {X B : Set V}
    (hXfinite : X.Finite)
    (P : Erdos718.ABLinkage G X B X.ncard)
    (hlinked : Erdos718.IsLinkedSet (G.induce B) Set.univ) :
    Erdos718.IsLinkedSet G X := by
  intro I _ terminal hterminal
  let A := FullTerminalArms.ofABLinkage hXfinite hterminal P
  apply A.nonempty_pairLinkage_of_isLinkedSet Set.univ
  · exact fun _ _ => Set.mem_univ _
  · exact fun _ _ _ => Set.mem_univ _
  · exact hlinked

/-- If the induced target is `k`-linked and a full linkage attaches every
source vertex to it, then a source of size at most `2k` is linked.  The
central linkage is asked to avoid the first target hit of every one of the
full attachment paths; this set has cardinality at most `|X|` and contains
every source vertex already lying in the target. -/
theorem isLinkedSet_of_full_abLinkage_to_kLinked_target
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {X B : Set V} {k : ℕ}
    (hXfinite : X.Finite) (hXcard : X.ncard ≤ 2 * k)
    (P : Erdos718.ABLinkage G X B X.ncard)
    (hlinked : Erdos718.IsKLinked (G.induce B) k) :
    Erdos718.IsLinkedSet G X := by
  classical
  let : Fintype X := hXfinite.fintype
  let leftMap : Fin X.ncard → X := fun i => ⟨P.left i, P.left_mem i⟩
  have hleftInj : Function.Injective leftMap := by
    intro i j hij
    by_contra hne
    have hval : P.left i = P.left j := congrArg Subtype.val hij
    have hjmem : P.left i ∈ (P.path j).support := by
      rw [hval]
      exact (P.path j).start_mem_support
    exact (Set.disjoint_left.mp (P.disjoint hne)
      (P.path i).start_mem_support hjmem).elim
  have hcardX : Fintype.card X = X.ncard := Set.fintypeCard_eq_ncard X
  have hleftBij : Function.Bijective leftMap :=
    (Fintype.bijective_iff_injective_and_card leftMap).mpr
      ⟨hleftInj, by simp [hcardX]⟩
  let leftEquiv : Fin X.ncard ≃ X := Equiv.ofBijective leftMap hleftBij
  let allTarget (i : Fin X.ncard) : B :=
    ⟨(P.path i).getVert (firstHitIndex (P.path i) B (P.right_mem i)),
      (firstHitIndex_spec (P.path i) B (P.right_mem i)).2⟩
  let S : Set B := Set.range allTarget
  have hSfinite : S.Finite := Set.finite_range allTarget
  have hScard : S.ncard ≤ 2 * k := by
    calc
      S.ncard = (allTarget '' (Set.univ : Set (Fin X.ncard))).ncard := by
        rw [Set.image_univ]
      _ ≤ (Set.univ : Set (Fin X.ncard)).ncard := Set.ncard_image_le
      _ = X.ncard := by simp
      _ ≤ 2 * k := hXcard
  have hSlinked : Erdos718.IsLinkedSet (G.induce B) S :=
    hlinked S hSfinite hScard
  intro I _ terminal hterminal
  let A := FullTerminalArms.ofABLinkage hXfinite hterminal P
  apply A.nonempty_pairLinkage_of_isLinkedSet S
  · rintro _ ⟨z, rfl⟩
    let index : Fin X.ncard :=
      leftEquiv.symm ⟨terminal z, hterminal ⟨z, rfl⟩⟩
    refine ⟨index, ?_⟩
    apply Subtype.ext
    rfl
  · intro x hxB hxX
    let j : Fin X.ncard := leftEquiv.symm ⟨x, hxX⟩
    have hjleft : P.left j = x := by
      exact congrArg Subtype.val
        (leftEquiv.apply_symm_apply ⟨x, hxX⟩)
    have hfirst : firstHitIndex (P.path j) B (P.right_mem j) = 0 := by
      classical
      let witness : ∃ n, n ≤ (P.path j).length ∧
          (P.path j).getVert n ∈ B :=
        ⟨(P.path j).length, le_rfl, by simpa using P.right_mem j⟩
      change Nat.find witness = 0
      rw [Nat.find_eq_zero]
      refine ⟨Nat.zero_le _, ?_⟩
      simpa only [Walk.getVert_zero, hjleft] using hxB
    change (⟨x, hxB⟩ : B) ∈ S
    refine ⟨j, Subtype.ext ?_⟩
    simp only [allTarget, hfirst, Walk.getVert_zero, hjleft]
  · exact hSlinked

/-! ### Moving a disjoint path family onto a crossed separator -/

noncomputable def firstSetHitIndex {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (S : Set V)
    (h : ∃ x ∈ p.support, x ∈ S) : ℕ := by
  classical
  let hw : ∃ n : ℕ, n ≤ p.length ∧ p.getVert n ∈ S := by
    obtain ⟨x, hxp, hxS⟩ := h
    refine ⟨p.support.idxOf x, ?_, ?_⟩
    · have := List.idxOf_lt_length_of_mem hxp
      rw [p.length_support] at this
      omega
    · rwa [p.getVert_support_idxOf hxp]
  exact Nat.find hw

lemma firstSetHitIndex_spec {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (S : Set V)
    (h : ∃ x ∈ p.support, x ∈ S) :
    firstSetHitIndex p S h ≤ p.length ∧
      p.getVert (firstSetHitIndex p S h) ∈ S := by
  classical
  let hw : ∃ n : ℕ, n ≤ p.length ∧ p.getVert n ∈ S := by
    obtain ⟨x, hxp, hxS⟩ := h
    refine ⟨p.support.idxOf x, ?_, ?_⟩
    · have := List.idxOf_lt_length_of_mem hxp
      rw [p.length_support] at this
      omega
    · rwa [p.getVert_support_idxOf hxp]
  exact Nat.find_spec hw

/-- If every path of a disjoint family crosses a separation, discard its
prefix before the first separator hit. -/
noncomputable def Erdos718.ABLinkage.moveLeftToSeparator
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A B : Set V} {m : ℕ}
    (P : Erdos718.ABLinkage G A B m) (s : Erdos718.Separation G)
    (hAleft : A ⊆ (s.left : Set V))
    (hBright : B ⊆ (s.right : Set V)) :
    Erdos718.ABLinkage G (s.separator : Set V) B m := by
  classical
  have hcross (i : Fin m) : ∃ x ∈ (P.path i).support,
      x ∈ (s.separator : Set V) := by
    have haL : P.left i ∈ s.left := hAleft (P.left_mem i)
    have hbR : P.right i ∈ s.right := hBright (P.right_mem i)
    by_cases haR : P.left i ∈ s.right
    · exact ⟨P.left i, (P.path i).start_mem_support,
        Finset.mem_inter.mpr ⟨haL, haR⟩⟩
    by_cases hbL : P.right i ∈ s.left
    · exact ⟨P.right i, (P.path i).end_mem_support,
        Finset.mem_inter.mpr ⟨hbL, hbR⟩⟩
    · exact s.walk_meets_separator (P.path i)
        (Finset.mem_sdiff.mpr ⟨haL, haR⟩)
        (Finset.mem_sdiff.mpr ⟨hbR, hbL⟩)
  let hit (i : Fin m) := firstSetHitIndex (P.path i)
    (s.separator : Set V) (hcross i)
  let q (i : Fin m) := (P.path i).drop (hit i)
  refine {
    left := fun i => (P.path i).getVert (hit i)
    right := P.right
    path := q
    left_mem := fun i => (firstSetHitIndex_spec (P.path i)
      (s.separator : Set V) (hcross i)).2
    right_mem := P.right_mem
    isPath := fun i => (P.isPath i).drop (hit i)
    disjoint := ?_
  }
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  apply Set.disjoint_left.mp (P.disjoint hij)
  · change x ∈ (q i).support at hxi
    dsimp only [q] at hxi
    rw [Walk.drop_support_eq_support_drop_min] at hxi
    exact List.mem_of_mem_drop hxi
  · change x ∈ (q j).support at hxj
    dsimp only [q] at hxj
    rw [Walk.drop_support_eq_support_drop_min] at hxj
    exact List.mem_of_mem_drop hxj

/-- Lift a set-to-set linkage from an induced graph to its host. -/
noncomputable def Erdos718.ABLinkage.liftInduce
    {G : SimpleGraph V} {R A B : Set V} {m : ℕ}
    (P : Erdos718.ABLinkage (G.induce R)
      {x : R | (x : V) ∈ A} {x : R | (x : V) ∈ B} m) :
    Erdos718.ABLinkage G A B m := by
  let inclusion : G.induce R →g G :=
    (SimpleGraph.Embedding.induce R).toHom
  refine {
    left := fun i => (P.left i : V)
    right := fun i => (P.right i : V)
    path := fun i => (P.path i).map inclusion
    left_mem := P.left_mem
    right_mem := P.right_mem
    isPath := fun i => (P.isPath i).map Subtype.val_injective
    disjoint := ?_
  }
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  change x ∈ (Walk.map inclusion (P.path i)).support at hxi
  change x ∈ (Walk.map inclusion (P.path j)).support at hxj
  rw [Walk.support_map] at hxi hxj
  obtain ⟨y, hyi, hyx⟩ := List.mem_map.mp hxi
  obtain ⟨z, hzj, hzx⟩ := List.mem_map.mp hxj
  have hyz : y = z := Subtype.ext (by
    change (y : V) = x at hyx
    change (z : V) = x at hzx
    exact hyx.trans hzx.symm)
  exact (Set.disjoint_left.mp (P.disjoint hij) hyi (hyz ▸ hzj)).elim

end ThomasWollanMassed
end Erdos717
