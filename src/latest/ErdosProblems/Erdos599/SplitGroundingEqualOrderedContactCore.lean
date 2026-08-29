/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingEqualStrictSelection
import ErdosProblems.Erdos599.GroundingFiniteAlternatingRoot

/-!
# Ordered entry contacts without legacy ladder legality

These are the purely alternating, input-generic facts used to stop a route
at its first self-owned backward link.  They are restated here so the split
grounding route does not import the legacy chronology chain.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace Alternating.FiniteTrace

/-- A backward entry is fed either from the whole trace initial or from the
ambient start of a strictly earlier backward link. -/
theorem splitBackwardLink_entry_reached_from_initial_or_priorBackward
    (Q : FiniteTrace Gamma.graph) {Y : Set Gamma.DPath}
    (hback : BackwardLinksOn Y (.finite Q))
    (l : Link Gamma.graph) (hl : l ∈ (AltPath.finite Q).links)
    (hldir : l.direction = .backward) :
    Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          (AltPath.finite Q).directionEdges .forward)
        Q.initial l.entry ∨
      ∃ (b : Link Gamma.graph),
        b ∈ (AltPath.finite Q).links ∧
        b.direction = .backward ∧
        (∃ parent ∈ Y, b.path.IsSubpathOf parent) ∧
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            (AltPath.finite Q).directionEdges .forward)
          b.path.start l.entry ∧
        ∃ (bi li : Fin (Q.lastIndex + 1)),
          Q.link bi = b ∧ Q.link li = l ∧ bi.1 < li.1 := by
  change l ∈ Q.links at hl
  rcases hl with ⟨i, rfl⟩
  cases hi : i.1 with
  | zero =>
      left
      have hizero : i = (0 : Fin (Q.lastIndex + 1)) := by
        apply Fin.ext
        exact hi
      have hinitial : Q.initial = (Q.link i).entry := by
        rw [hizero]
        rfl
      rw [hinitial]
  | succ n =>
      have hn : n < Q.lastIndex := by omega
      let predShort : Fin Q.lastIndex := ⟨n, hn⟩
      let pred : Fin (Q.lastIndex + 1) := Fin.castSucc predShort
      have hipred : i = predShort.succ := by
        apply Fin.ext
        change i.1 = n + 1
        exact hi
      have hpredDir : (Q.link pred).direction = .forward := by
        have halt := Q.alternates predShort
        change (Q.link pred).direction ≠
          (Q.link predShort.succ).direction at halt
        rw [← hipred, hldir] at halt
        cases hp : (Q.link pred).direction with
        | forward => rfl
        | backward => exact False.elim (halt hp)
      have hreach := Q.reflTransGen_entry_exit_of_forward pred hpredDir
        (Set.Subset.rfl)
      have hfinish : (Q.link pred).exit = (Q.link i).entry := by
        rw [hipred]
        exact Q.joins predShort
      cases hnval : n with
      | zero =>
          left
          have hpredZero : pred = (0 : Fin (Q.lastIndex + 1)) := by
            apply Fin.ext
            exact hnval
          have hinitial : Q.initial = (Q.link pred).entry := by
            rw [hpredZero]
            rfl
          rw [← hfinish, hinitial]
          exact hreach
      | succ m =>
          right
          have hm : m < Q.lastIndex := by omega
          let priorShort : Fin Q.lastIndex := ⟨m, hm⟩
          let prior : Fin (Q.lastIndex + 1) := Fin.castSucc priorShort
          have hpredSucc : pred = priorShort.succ := by
            apply Fin.ext
            change n = m + 1
            exact hnval
          have hpriorDir : (Q.link prior).direction = .backward := by
            have halt := Q.alternates priorShort
            change (Q.link prior).direction ≠
              (Q.link priorShort.succ).direction at halt
            rw [← hpredSucc, hpredDir] at halt
            cases hp : (Q.link prior).direction with
            | forward => exact False.elim (halt hp)
            | backward => rfl
          have hpriorMem : Q.link prior ∈
              (AltPath.finite Q).links := ⟨prior, rfl⟩
          obtain ⟨parent, hparent, hsub⟩ :=
            hback (Q.link prior) hpriorMem hpriorDir
          refine ⟨Q.link prior, hpriorMem, hpriorDir,
            ⟨parent, hparent, hsub⟩, ?_, prior, i, rfl, rfl, ?_⟩
          · have hjoin : (Q.link prior).exit =
                (Q.link pred).entry := by
              rw [hpredSucc]
              exact Q.joins priorShort
            have hstart : (Q.link prior).path.start =
                (Q.link prior).exit := by
              simp [Link.exit, hpriorDir]
            rw [hstart, hjoin, ← hfinish]
            exact hreach
          · change m < i.1
            omega

/-- Link positions of a finite alternating trace are injective. -/
theorem splitLink_injective (F : FiniteTrace Gamma.graph) :
    Function.Injective F.link := by
  intro i j hij
  by_contra hne
  have hlt : i < j ∨ j < i := lt_or_gt_of_ne hne
  cases hlt with
  | inl hlt =>
      have hcompat := F.compatible i j hlt
      rw [hij] at hcompat
      cases hd : (F.link j).direction with
      | forward =>
          simp only [CompatibleInOrder, hd] at hcompat
          rcases hcompat (F.link j).entry_mem_support
              (F.link j).entry_mem_support with h | h
          · exact (F.link j).entry_ne_exit h.2
          · exact (F.link j).entry_ne_exit h.1
      | backward =>
          simp only [CompatibleInOrder, hd] at hcompat
          rcases hcompat (F.link j).entry_mem_support
              (F.link j).entry_mem_support with h | h
          · exact (F.link j).entry_ne_exit h.2
          · exact (F.link j).entry_ne_exit h.1
  | inr hlt =>
      have hji : F.link j = F.link i := hij.symm
      have hcompat := F.compatible j i hlt
      rw [hji] at hcompat
      cases hd : (F.link i).direction with
      | forward =>
          simp only [CompatibleInOrder, hd] at hcompat
          rcases hcompat (F.link i).entry_mem_support
              (F.link i).entry_mem_support with h | h
          · exact (F.link i).entry_ne_exit h.2
          · exact (F.link i).entry_ne_exit h.1
      | backward =>
          simp only [CompatibleInOrder, hd] at hcompat
          rcases hcompat (F.link i).entry_mem_support
              (F.link i).entry_mem_support with h | h
          · exact (F.link i).entry_ne_exit h.2
          · exact (F.link i).entry_ne_exit h.1

/-- A nonempty predicate on trace links has a first occurrence. -/
theorem splitExists_first_link
    (F : FiniteTrace Gamma.graph) (P : Link Gamma.graph → Prop)
    (hex : ∃ l ∈ (AltPath.finite F).links, P l) :
    ∃ l ∈ (AltPath.finite F).links, P l ∧
      ∀ (bi li : Fin (F.lastIndex + 1)),
        F.link li = l → bi.1 < li.1 → ¬ P (F.link bi) := by
  classical
  let S : Finset (Fin (F.lastIndex + 1)) :=
    Finset.univ.filter (fun i ↦ P (F.link i))
  have hS : S.Nonempty := by
    obtain ⟨l, hl, hPl⟩ := hex
    change l ∈ F.links at hl
    obtain ⟨i, rfl⟩ := hl
    exact ⟨i, by simp [S, hPl]⟩
  let i : Fin (F.lastIndex + 1) := S.min' hS
  have hiS : i ∈ S := Finset.min'_mem S hS
  have hPi : P (F.link i) := (Finset.mem_filter.1 hiS).2
  refine ⟨F.link i, ⟨i, rfl⟩, hPi, ?_⟩
  intro bi li hli hbil hPbi
  have hlii : li = i := F.splitLink_injective hli
  subst li
  have hbiS : bi ∈ S := by simp [S, hPbi]
  exact (not_lt_of_ge (Finset.min'_le S bi hbiS)) hbil

end Alternating.FiniteTrace

namespace PopularAuxiliary.Input

/-- The full target decoder ends at the old target vertex. -/
theorem splitDecodeFinitePath_terminal_of_finish_old
    {I : Type u} (J : PopularAuxiliary.Input Gamma I)
    (p : FinitePath J.lambda.graph)
    (hsource : p.start ∈ J.lambda.source)
    (htarget : p.finish ∈ J.lambda.target)
    (y : V) (hfinish : p.finish = .old y) :
    (J.decodeFinitePath p hsource htarget).terminal = y := by
  classical
  unfold decodeFinitePath
  split
  · rename_i x hx
    unfold decodeFinitePathFromFinite
    apply PopularAuxiliary.Input.LambdaVertex.old.inj
    exact (J.chooseTargetEndpoint p htarget).2.2.symm.trans hfinish
  · rename_i i hi
    unfold decodeFinitePathFromProxy
    apply PopularAuxiliary.Input.LambdaVertex.old.inj
    exact (J.chooseTargetEndpoint p htarget).2.2.symm.trans hfinish

end PopularAuxiliary.Input

namespace DWeb.KappaLadder

open GroundingEqualActiveSelection

variable {kappa : Cardinal.{u}}

/-- Canonical-route form of the ordered backward-entry reachability lemma. -/
theorem splitCanonicalErasedRoute_backwardLink_entry_reached
    {I : Type u} (J : PopularAuxiliary.Input Gamma I)
    (Q : Popular.XSWarp J.lambda J.lambda.target) (p : WarpPath Q)
    (l : Link Gamma.graph)
    (hl : l ∈ (canonicalErasedRoute J Q p).links)
    (hldir : l.direction = .backward) :
    Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          (canonicalErasedRoute J Q p).directionEdges .forward)
        (canonicalErasedRoute J Q p).initial l.entry ∨
      ∃ (b : Link Gamma.graph),
        b ∈ (canonicalErasedRoute J Q p).links ∧
        b.direction = .backward ∧
        (∃ parent ∈ J.ladder.paths, b.path.IsSubpathOf parent) ∧
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            (canonicalErasedRoute J Q p).directionEdges .forward)
          b.path.start l.entry ∧
        ∃ (F : FiniteTrace Gamma.graph)
            (hroute : canonicalErasedRoute J Q p = .finite F)
            (bi li : Fin (F.lastIndex + 1)),
          F.link bi = b ∧ F.link li = l ∧ bi.1 < li.1 := by
  cases hroute : canonicalErasedRoute J Q p with
  | trivial v => simp [hroute, AltPath.links] at hl
  | finite F =>
      let T := J.decodeFinitePath p.1
        (Q.starts_in_source p.2) (Q.ends_in_target p.2)
      have hback : BackwardLinksOn J.ladder.paths (.finite F) := by
        have hfull : BackwardLinksOn J.ladder.paths
            (canonicalErasedRoute J Q p) := by
          change BackwardLinksOn J.ladder.paths T.erasedCompression.path
          apply T.runs.erasedSignedRoute.compressionOfValid_backwardLinksOn
            (fun {_s} hs ↦ T.valid _
              (T.runs.erasedSignedRoute.steps_sublist.subset hs))
            J.ladder.disjoint
          intro s hs hdir
          simpa [PopularAuxiliary.Input.familyEdges,
            Alternating.familyEdges] using
            T.backward_on_ladder s
              (T.runs.erasedSignedRoute.steps_sublist.subset hs) hdir
        simpa only [hroute] using hfull
      rcases F.splitBackwardLink_entry_reached_from_initial_or_priorBackward
          hback l (by simpa only [hroute] using hl) hldir with
          hroot | ⟨b, hb, hbdir, hbowner, hreach, bi, li,
            hbi, hli, hlt⟩
      · left
        simpa only [hroute, AltPath.initial,
          AltPath.directionEdges] using hroot
      · right
        refine ⟨b, ?_, hbdir, hbowner, ?_, F, rfl, bi, li,
          hbi, hli, hlt⟩
        · simpa only [hroute] using hb
        · simpa only [hroute, AltPath.directionEdges] using hreach
  | infinite R =>
      let T := J.decodeFinitePath p.1
        (Q.starts_in_source p.2) (Q.ends_in_target p.2)
      have hterminal := T.erasedCompression.terminal_eq
      have hpath : T.erasedCompression.path = .infinite R := by
        simpa only [canonicalErasedRoute, T] using hroute
      rw [hpath] at hterminal
      simp at hterminal

/-- Transfer existing roots to the entry of a chosen backward link, using
only roots for strictly earlier backward links. -/
theorem splitCanonicalErasedRoute_backwardLink_entry_rooted
    {I : Type u} (J : PopularAuxiliary.Input Gamma I)
    (Q : Popular.XSWarp J.lambda J.lambda.target) (p : WarpPath Q)
    (l : Link Gamma.graph)
    (hl : l ∈ (canonicalErasedRoute J Q p).links)
    (hldir : l.direction = .backward)
    {A : Set V} {E : Set (V × V)}
    (hinitial : ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a
        (canonicalErasedRoute J Q p).initial)
    (hforward :
      (canonicalErasedRoute J Q p).directionEdges .forward ⊆ E)
    (hprior : ∀ (b : Link Gamma.graph),
      b ∈ (canonicalErasedRoute J Q p).links →
      b.direction = .backward →
      (∃ parent ∈ J.ladder.paths, b.path.IsSubpathOf parent) →
      ∀ (F : FiniteTrace Gamma.graph)
        (hroute : canonicalErasedRoute J Q p = .finite F)
        (bi li : Fin (F.lastIndex + 1)),
        F.link bi = b → F.link li = l → bi.1 < li.1 →
        ∃ a ∈ A,
          Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E)
            a b.path.start) :
    ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a l.entry := by
  rcases splitCanonicalErasedRoute_backwardLink_entry_reached
      J Q p l hl hldir with hfromInitial |
        ⟨b, hb, hbdir, hbowner, hfromPrior,
          F, hroute, bi, li, hbi, hli, hlt⟩
  · obtain ⟨a, haA, haInitial⟩ := hinitial
    refine ⟨a, haA, haInitial.trans ?_⟩
    exact Relation.ReflTransGen.mono
      (fun _ _ h ↦ hforward h) _ _ hfromInitial
  · obtain ⟨a, haA, haPrior⟩ :=
      hprior b hb hbdir hbowner F hroute bi li hbi hli hlt
    refine ⟨a, haA, haPrior.trans ?_⟩
    exact Relation.ReflTransGen.mono
      (fun _ _ h ↦ hforward h) _ _ hfromPrior

/-- A backward-link traversal entry belongs to its reference-warp owner. -/
theorem splitCanonicalErasedRoute_backwardLink_entry_mem_owner
    {I : Type u} (J : PopularAuxiliary.Input Gamma I)
    (Q : Popular.XSWarp J.lambda J.lambda.target) (p : WarpPath Q)
    (l : Link Gamma.graph)
    (_hl : l ∈ (canonicalErasedRoute J Q p).links)
    (_hldir : l.direction = .backward)
    (parent : Gamma.DPath) (_hparent : parent ∈ J.ladder.paths)
    (hsub : l.path.IsSubpathOf parent) :
    l.entry ∈ parent.support :=
  hsub.1 l.entry_mem_support

end DWeb.KappaLadder
end Erdos599
