/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ConcreteWave
import ErdosProblems.Erdos599.IteratedArrow
import ErdosProblems.Erdos599.RelationalRoof
import ErdosProblems.Erdos599.RoofQuotient
import Mathlib.Order.SuccPred.Archimedean
import Mathlib.Order.Zorn

/-!
# Limits and maximal waves for Erdős Problem 599

This file proves the concrete limit and maximality results from
Aharoni--Berger, Lemmas 3.19--3.26.  In particular, the upper-bound theorem
below constructs genuine finite paths or rays at a limit: it does not treat
an arbitrary union of path records as a path.
-/

namespace Erdos599

open Set
open DirectedPath
open WarpLimits

universe u v

namespace DirectedPath

variable {V : Type u} {D : Digraph V}

namespace Walk

/-- Consecutive entries of a walk's ordered support are joined by an arc. -/
theorem adj_getElem_succ {a b : V} (p : Walk D a b) (n : ℕ)
    (hn : n + 1 < p.support.length) :
    D.Adj p.support[n] p.support[n + 1] := by
  induction p generalizing n with
  | nil => simp at hn
  | @cons a c b e p ih =>
      cases n with
      | zero =>
          have hp0 : 0 < p.support.length :=
            List.length_pos_iff.mpr p.support_ne_nil
          have h0 : p.support[0] = c := by
            calc
              p.support[0] = p.support.head p.support_ne_nil := List.getElem_zero hp0
              _ = c := p.head_support
          simpa [h0] using e
      | succ n =>
          have hn' : n + 1 < p.support.length := by simpa using hn
          simpa [Nat.add_assoc] using ih n hn'

end Walk

namespace FinitePath

/-- Comparable finite simple paths with the same final vertex have the same
ordered support: a proper extension would repeat that final vertex. -/
theorem IsPrefixOf.eq_support_of_finish_eq {p q : FinitePath D}
    (hpq : p.IsPrefixOf q) (hfinish : p.finish = q.finish) :
    p.walk.support = q.walk.support := by
  rcases hpq with ⟨t, ht⟩
  by_cases hempty : t = []
  · simpa [hempty] using ht
  · exfalso
    have hnodup : (p.walk.support ++ t).Nodup := by
      rw [ht]
      exact q.isPath
    have hdisjoint := hnodup.disjoint
    have hpfinish : p.finish ∈ p.walk.support := p.walk.end_mem_support
    have happ : p.walk.support ++ t ≠ [] := by
      rw [ht]
      exact q.walk.support_ne_nil
    have htfinish : p.finish ∈ t := by
      have hlast : (p.walk.support ++ t).getLast happ = q.finish := by
        simpa only [← ht] using q.walk.getLast_support
      have hlastt : (p.walk.support ++ t).getLast happ =
          t.getLast hempty := List.getLast_append_of_ne_nil happ hempty
      have : t.getLast hempty = p.finish := by
        rw [← hlastt, hlast, hfinish]
      rw [← this]
      exact List.getLast_mem hempty
    exact List.disjoint_left.1 hdisjoint hpfinish htfinish

end FinitePath

namespace Path

/-- The finite members of a path family have a common length bound. -/
def FiniteLengthsBounded (C : Set (Path D)) : Prop :=
  ∃ N, ∀ p : FinitePath D, (Sum.inl p : Path D) ∈ C →
    p.walk.support.length ≤ N

theorem exists_longFinitePath (C : Set (Path D))
    (h : ¬ FiniteLengthsBounded C) (n : ℕ) :
    ∃ p : FinitePath D, (Sum.inl p : Path D) ∈ C ∧
      n < p.walk.support.length := by
  by_contra hn
  apply h
  refine ⟨n, ?_⟩
  intro p hp
  exact Nat.le_of_not_gt (fun hgt ↦ hn ⟨p, hp, hgt⟩)

/-- Choice of a member witnessing that finite lengths are unbounded. -/
noncomputable def longFinitePath (C : Set (Path D))
    (h : ¬ FiniteLengthsBounded C) (n : ℕ) : FinitePath D :=
  Classical.choose (exists_longFinitePath C h n)

theorem longFinitePath_mem (C : Set (Path D))
    (h : ¬ FiniteLengthsBounded C) (n : ℕ) :
    (Sum.inl (longFinitePath C h n) : Path D) ∈ C :=
  (Classical.choose_spec (exists_longFinitePath C h n)).1

theorem lt_longFinitePath_length (C : Set (Path D))
    (h : ¬ FiniteLengthsBounded C) (n : ℕ) :
    n < (longFinitePath C h n).walk.support.length :=
  (Classical.choose_spec (exists_longFinitePath C h n)).2

/-- The `n`th vertex of any member long enough; chain comparability makes
this independent of the chosen member. -/
noncomputable def chainVertex (C : Set (Path D))
    (h : ¬ FiniteLengthsBounded C) (n : ℕ) : V :=
  (longFinitePath C h n).walk.support[n]'(lt_longFinitePath_length C h n)

/-- Long finite members of a chain agree at every common occupied index. -/
theorem chain_getElem_eq (C : Set (Path D)) (hC : IsChain Extends C)
    {p q : FinitePath D} (hp : (Sum.inl p : Path D) ∈ C)
    (hq : (Sum.inl q : Path D) ∈ C) (n : ℕ)
    (hnp : n < p.walk.support.length) (hnq : n < q.walk.support.length) :
    p.walk.support[n] = q.walk.support[n] := by
  by_cases hpqeq : p = q
  · subst q
    rfl
  · rcases hC hp hq (by simpa using hpqeq) with hpq | hqp
    · exact hpq.getElem hnp
    · exact (hqp.getElem hnq).symm

/-- The ray obtained as the direct limit of an unbounded chain of finite
paths. -/
noncomputable def rayOfUnboundedChain (C : Set (Path D))
    (hC : IsChain Extends C) (h : ¬ FiniteLengthsBounded C) : Ray D where
  toFun := chainVertex C h
  adj_succ n := by
    let q := longFinitePath C h (n + 1)
    have hqC : (Sum.inl q : Path D) ∈ C := longFinitePath_mem C h (n + 1)
    have hnq : n < q.walk.support.length :=
      lt_trans (Nat.lt_succ_self n) (lt_longFinitePath_length C h (n + 1))
    have hsnq : n + 1 < q.walk.support.length :=
      lt_longFinitePath_length C h (n + 1)
    have hvn : chainVertex C h n = q.walk.support[n] := by
      simpa [chainVertex] using
        chain_getElem_eq C hC (longFinitePath_mem C h n) hqC n
          (lt_longFinitePath_length C h n) hnq
    have hvn1 : chainVertex C h (n + 1) = q.walk.support[n + 1] := by
      simpa [chainVertex] using
        chain_getElem_eq C hC (longFinitePath_mem C h (n + 1)) hqC (n + 1)
          (lt_longFinitePath_length C h (n + 1)) hsnq
    rw [hvn, hvn1]
    exact q.walk.adj_getElem_succ n hsnq
  injective := by
    intro m n hmn
    let k := max m n
    let q := longFinitePath C h k
    have hqC : (Sum.inl q : Path D) ∈ C := longFinitePath_mem C h k
    have hmk : m < q.walk.support.length :=
      lt_of_le_of_lt (Nat.le_max_left m n) (lt_longFinitePath_length C h k)
    have hnk : n < q.walk.support.length :=
      lt_of_le_of_lt (Nat.le_max_right m n) (lt_longFinitePath_length C h k)
    have hm : chainVertex C h m = q.walk.support[m] := by
      simpa [chainVertex] using
        chain_getElem_eq C hC (longFinitePath_mem C h m) hqC m
          (lt_longFinitePath_length C h m) hmk
    have hn : chainVertex C h n = q.walk.support[n] := by
      simpa [chainVertex] using
        chain_getElem_eq C hC (longFinitePath_mem C h n) hqC n
          (lt_longFinitePath_length C h n) hnk
    exact q.isPath.getElem_inj_iff.mp (hm ▸ hn ▸ hmn)

/-- A fixed terminal occurs cofinally if above every member of the chain
there is a member terminating there. -/
def TerminalCofinal (C : Set (Path D)) (x : V) : Prop :=
  ∀ p ∈ C, ∃ q ∈ C, Extends p q ∧ q.terminal? = some x

theorem exists_finite_of_terminalCofinal {C : Set (Path D)} {x : V}
    (hCne : C.Nonempty) (hx : TerminalCofinal C x) :
    ∃ q : FinitePath D, (Sum.inl q : Path D) ∈ C ∧ q.finish = x := by
  obtain ⟨p, hp⟩ := hCne
  obtain ⟨q, hq, _, hqt⟩ := hx p hp
  rcases q with q | r
  · exact ⟨q, hq, Option.some.inj hqt⟩
  · simp at hqt

theorem no_ray_of_terminalCofinal {C : Set (Path D)} {x : V}
    (hx : TerminalCofinal C x) :
    ∀ r : Ray D, (Sum.inr r : Path D) ∉ C := by
  intro r hr
  obtain ⟨q, hq, hrq, hqt⟩ := hx (.inr r) hr
  rcases q with q | s
  · exact hrq
  · simp at hqt

/-- In a chain, two finite members with the same terminal have the same
ordered support. -/
theorem finite_support_eq_of_chain_terminal_eq {C : Set (Path D)}
    (hC : IsChain Extends C) {p q : FinitePath D}
    (hp : (Sum.inl p : Path D) ∈ C) (hq : (Sum.inl q : Path D) ∈ C)
    (hfinish : p.finish = q.finish) : p.walk.support = q.walk.support := by
  by_cases hpq : p = q
  · subst q
    rfl
  · rcases hC hp hq (by simpa using hpq) with hpref | qpref
    · exact hpref.eq_support_of_finish_eq hfinish
    · exact (qpref.eq_support_of_finish_eq hfinish.symm).symm

/-- Cofinal occurrence of one terminal forces the finite members' lengths
to be bounded. -/
theorem finiteLengthsBounded_of_terminalCofinal {C : Set (Path D)}
    (hCne : C.Nonempty) (hC : IsChain Extends C) {x : V}
    (hx : TerminalCofinal C x) : FiniteLengthsBounded C := by
  obtain ⟨q, hqC, hqfinish⟩ := exists_finite_of_terminalCofinal hCne hx
  refine ⟨q.walk.support.length, ?_⟩
  intro p hpC
  obtain ⟨t, htC, hpt, htterm⟩ := hx (.inl p) hpC
  rcases t with t | r
  · have htfinish : t.finish = x := Option.some.inj htterm
    have hsupports : t.walk.support = q.walk.support :=
      finite_support_eq_of_chain_terminal_eq hC htC hqC
        (htfinish.trans hqfinish.symm)
    exact hpt.length_le.trans_eq (congrArg List.length hsupports)
  · simp at htterm

/-- A bounded nonempty family of finite chain members contains a longest
one. -/
theorem exists_longestFinitePath {C : Set (Path D)}
    (hCne : C.Nonempty) (hnoRay : ∀ r : Ray D, (Sum.inr r : Path D) ∉ C)
    (hb : FiniteLengthsBounded C) :
    ∃ q : FinitePath D, (Sum.inl q : Path D) ∈ C ∧
      ∀ p : FinitePath D, (Sum.inl p : Path D) ∈ C →
        p.walk.support.length ≤ q.walk.support.length := by
  classical
  obtain ⟨N, hN⟩ := hb
  obtain ⟨z, hzC⟩ := hCne
  obtain ⟨z, hzC⟩ : ∃ z : FinitePath D, (Sum.inl z : Path D) ∈ C := by
    rcases z with z | r
    · exact ⟨z, hzC⟩
    · exact (hnoRay r hzC).elim
  let P : ℕ → Prop := fun n ↦
    ∃ p : FinitePath D, (Sum.inl p : Path D) ∈ C ∧
      p.walk.support.length = n
  let m := Nat.findGreatest P N
  have hzN : z.walk.support.length ≤ N := hN z hzC
  have hzP : P z.walk.support.length := ⟨z, hzC, rfl⟩
  have hmP : P m := Nat.findGreatest_spec hzN hzP
  obtain ⟨q, hqC, hqlen⟩ := hmP
  refine ⟨q, hqC, ?_⟩
  intro p hpC
  rw [hqlen]
  exact Nat.le_findGreatest (hN p hpC) ⟨p, hpC, rfl⟩

/-- A member of maximal finite length is above the entire chain. -/
theorem longestFinitePath_isUpper {C : Set (Path D)}
    (hC : IsChain Extends C) {q : FinitePath D}
    (hqC : (Sum.inl q : Path D) ∈ C)
    (hqmax : ∀ p : FinitePath D, (Sum.inl p : Path D) ∈ C →
      p.walk.support.length ≤ q.walk.support.length)
    (hnoRay : ∀ r : Ray D, (Sum.inr r : Path D) ∉ C) :
    ∀ p ∈ C, Extends p (.inl q) := by
  intro p hpC
  rcases p with p | r
  · by_cases hpq : p = q
    · subst q
      exact extends_refl _
    · rcases hC hpC hqC (by simpa using hpq) with hpref | qpref
      · exact hpref
      · have hs : q.walk.support = p.walk.support :=
          qpref.eq_of_length_le (hqmax p hpC)
        change p.walk.support <+: q.walk.support
        rw [hs]
  · exact (hnoRay r hpC).elim

/-- If an upper bound is itself in the chain, its support is exactly the
union of supports of all chain members. -/
theorem support_eq_iUnion_of_mem_upper {C : Set (Path D)} {q : Path D}
    (hqC : q ∈ C) (hu : ∀ p ∈ C, Extends p q) :
    q.support = ⋃ p ∈ C, p.support := by
  apply Set.Subset.antisymm
  · intro x hx
    exact Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨hqC, hx⟩⟩
  · intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨p, hpC, hxp⟩ := hx
    exact support_mono_of_extends (hu p hpC) hxp

/-- The ray direct limit is above every member of an unbounded all-finite
chain. -/
theorem extends_rayOfUnboundedChain {C : Set (Path D)}
    (hC : IsChain Extends C)
    (hnoRay : ∀ r : Ray D, (Sum.inr r : Path D) ∉ C)
    (hb : ¬ FiniteLengthsBounded C) :
    ∀ p ∈ C, Extends p (.inr (rayOfUnboundedChain C hC hb)) := by
  intro p hpC
  rcases p with p | r
  · intro n hn
    simpa [rayOfUnboundedChain, chainVertex] using
      chain_getElem_eq C hC hpC (longFinitePath_mem C hb n) n hn
        (lt_longFinitePath_length C hb n)
  · exact (hnoRay r hpC).elim

/-- The support of the ray direct limit is the union of the supports in the
unbounded chain. -/
theorem support_rayOfUnboundedChain {C : Set (Path D)}
    (hC : IsChain Extends C)
    (hnoRay : ∀ r : Ray D, (Sum.inr r : Path D) ∉ C)
    (hb : ¬ FiniteLengthsBounded C) :
    Path.support (Sum.inr (rayOfUnboundedChain C hC hb) : Path D) =
      ⋃ p ∈ C, p.support := by
  apply Set.Subset.antisymm
  · rintro x ⟨n, rfl⟩
    refine Set.mem_iUnion.2 ⟨.inl (longFinitePath C hb n),
      Set.mem_iUnion.2 ⟨longFinitePath_mem C hb n, ?_⟩⟩
    change chainVertex C hb n ∈ (longFinitePath C hb n).walk.support
    rw [chainVertex]
    exact List.getElem_mem _
  · intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨p, hpC, hxp⟩ := hx
    exact support_mono_of_extends
      (extends_rayOfUnboundedChain hC hnoRay hb p hpC) hxp

/-- Existence package for the direct limit of a nonempty extension chain. -/
theorem exists_chainLimit (C : Set (Path D)) (hCne : C.Nonempty)
    (hC : IsChain Extends C) :
    ∃ q : Path D,
      (∀ p ∈ C, Extends p q) ∧
      q.support = ⋃ p ∈ C, p.support ∧
      ∀ x, TerminalCofinal C x → q.terminal? = some x := by
  by_cases hray : ∃ r : Ray D, (Sum.inr r : Path D) ∈ C
  · obtain ⟨r, hrC⟩ := hray
    have hu : ∀ p ∈ C, Extends p (.inr r) := by
      intro p hpC
      by_cases hpr : p = .inr r
      · subst p
        exact extends_refl _
      · rcases hC hpC hrC hpr with h | h
        · exact h
        · rcases p with p | s
          · exact h.elim
          · exact h.symm
    refine ⟨.inr r, hu, support_eq_iUnion_of_mem_upper hrC hu, ?_⟩
    intro x hx
    exact (no_ray_of_terminalCofinal hx r hrC).elim
  · have hnoRay : ∀ r : Ray D, (Sum.inr r : Path D) ∉ C := by
      intro r hr
      exact hray ⟨r, hr⟩
    by_cases hb : FiniteLengthsBounded C
    · obtain ⟨q, hqC, hqmax⟩ := exists_longestFinitePath hCne hnoRay hb
      have hu := longestFinitePath_isUpper hC hqC hqmax hnoRay
      refine ⟨.inl q, hu, support_eq_iUnion_of_mem_upper hqC hu, ?_⟩
      intro x hx
      obtain ⟨t, htC, hqt, htterm⟩ := hx (.inl q) hqC
      rcases t with t | r
      · have hs : q.walk.support = t.walk.support :=
          hqt.eq_of_length_le (hqmax t htC)
        have hfinish : q.finish = t.finish := by
          calc
            q.finish = q.walk.support.getLast q.walk.support_ne_nil :=
              q.walk.getLast_support.symm
            _ = t.walk.support.getLast t.walk.support_ne_nil := by
              simpa only [hs]
            _ = t.finish := t.walk.getLast_support
        simpa [hfinish] using htterm
      · simp at htterm
    · refine ⟨.inr (rayOfUnboundedChain C hC hb),
        extends_rayOfUnboundedChain hC hnoRay hb,
        support_rayOfUnboundedChain hC hnoRay hb, ?_⟩
      intro x hx
      exact (hb (finiteLengthsBounded_of_terminalCofinal hCne hC hx)).elim

/-- A chosen concrete direct limit of a nonempty extension chain. -/
noncomputable def chainLimit (C : Set (Path D)) (hCne : C.Nonempty)
    (hC : IsChain Extends C) : Path D :=
  Classical.choose (exists_chainLimit C hCne hC)

theorem extends_chainLimit (C : Set (Path D)) (hCne : C.Nonempty)
    (hC : IsChain Extends C) {p : Path D} (hp : p ∈ C) :
    Extends p (chainLimit C hCne hC) :=
  (Classical.choose_spec (exists_chainLimit C hCne hC)).1 p hp

theorem support_chainLimit (C : Set (Path D)) (hCne : C.Nonempty)
    (hC : IsChain Extends C) :
    (chainLimit C hCne hC).support = ⋃ p ∈ C, p.support :=
  (Classical.choose_spec (exists_chainLimit C hCne hC)).2.1

theorem terminal_chainLimit_of_cofinal (C : Set (Path D))
    (hCne : C.Nonempty) (hC : IsChain Extends C) {x : V}
    (hx : TerminalCofinal C x) :
    (chainLimit C hCne hC).terminal? = some x :=
  (Classical.choose_spec (exists_chainLimit C hCne hC)).2.2 x hx

end Path

end DirectedPath

namespace DWeb

variable {V : Type u} (G : DWeb V)

/-- In one warp, the initial vertex determines the member uniquely. -/
theorem IsWarp.eq_of_initial_eq {W : Set G.DPath} (hW : G.IsWarp W)
    {p q : G.DPath} (hp : p ∈ W) (hq : q ∈ W)
    (hi : p.initial = q.initial) : p = q := by
  by_contra hpq
  have hd := hW hp hq hpq
  exact Set.disjoint_left.1 hd p.initial_mem_support
    (hi ▸ q.initial_mem_support)

/-- Concrete forward extension as a reflexive-transitive system. -/
def waveForwardSystem : WarpLimits.ForwardSystem (Set G.DPath) where
  Extends := G.ForwardExtension
  refl := G.forwardExtension_refl
  trans := G.forwardExtension_trans

@[simp]
theorem waveForwardSystem_extends (U W : Set G.DPath) :
    G.waveForwardSystem.Extends U W ↔ G.ForwardExtension U W :=
  Iff.rfl

/-! ## Direct limits of chains of concrete waves -/

/-- The paths with initial vertex `a` occurring in some member of a wave
chain. -/
def waveThread (c : Set G.Wave) (a : V) : Set G.DPath :=
  {p | ∃ W ∈ c, p ∈ W.1 ∧ p.initial = a}

theorem waveThread_nonempty {c : Set G.Wave} {a : V}
    {W : G.Wave} (hWc : W ∈ c) (ha : a ∈ G.initialSet W.1) :
    (G.waveThread c a).Nonempty := by
  obtain ⟨p, hp, hpa⟩ := ha
  exact ⟨p, W, hWc, hp, hpa⟩

theorem initialSet_eq_of_mem_chain {c : Set G.Wave}
    (hc : IsChain (· ≤ ·) c) {U W : G.Wave} (hUc : U ∈ c) (hWc : W ∈ c) :
    G.initialSet U.1 = G.initialSet W.1 := by
  by_cases hUW : U = W
  · subst W
    rfl
  · rcases hc hUc hWc hUW with h | h
    · exact G.initialSet_eq_of_forwardExtension h
    · exact (G.initialSet_eq_of_forwardExtension h).symm

theorem waveThread_isChain {c : Set G.Wave}
    (hc : IsChain (· ≤ ·) c) (a : V) :
    IsChain DirectedPath.Path.Extends (G.waveThread c a) := by
  rintro p ⟨U, hUc, hpU, hip⟩ q ⟨W, hWc, hqW, hiq⟩ hpq
  by_cases hUW : U = W
  · subst W
    have hpqe : p = q :=
      IsWarp.eq_of_initial_eq G U.property.1 hpU hqW (hip.trans hiq.symm)
    exact (hpq hpqe).elim
  · rcases hc hUc hWc hUW with hUW | hWU
    · obtain ⟨r, hrW, hpr⟩ := hUW.1 p hpU
      have hir : r.initial = a := (G.extends_initial hpr).symm.trans hip
      have hrq : r = q :=
        IsWarp.eq_of_initial_eq G W.property.1 hrW hqW (hir.trans hiq.symm)
      exact Or.inl (hrq ▸ hpr)
    · obtain ⟨r, hrU, hqr⟩ := hWU.1 q hqW
      have hir : r.initial = a := (G.extends_initial hqr).symm.trans hiq
      have hrp : r = p :=
        IsWarp.eq_of_initial_eq G U.property.1 hrU hpU (hir.trans hip.symm)
      exact Or.inr (hrp ▸ hqr)

/-- A fixed member chosen from a nonempty chain. -/
noncomputable def waveChainBase (c : Set G.Wave) (hcne : c.Nonempty) : G.Wave :=
  Classical.choose hcne

theorem waveChainBase_mem (c : Set G.Wave) (hcne : c.Nonempty) :
    G.waveChainBase c hcne ∈ c :=
  Classical.choose_spec hcne

/-- The direct-limit path belonging to one initial thread of a nonempty
wave chain. -/
noncomputable def waveThreadLimit (c : Set G.Wave) (hcne : c.Nonempty)
    (hc : IsChain (· ≤ ·) c)
    (a : G.initialSet (G.waveChainBase c hcne).1) : G.DPath :=
  DirectedPath.Path.chainLimit (G.waveThread c a.1)
    (G.waveThread_nonempty (G.waveChainBase_mem c hcne) a.2)
    (G.waveThread_isChain hc a.1)

theorem waveThreadLimit_initial (c : Set G.Wave) (hcne : c.Nonempty)
    (hc : IsChain (· ≤ ·) c)
    (a : G.initialSet (G.waveChainBase c hcne).1) :
    (G.waveThreadLimit c hcne hc a).initial = a.1 := by
  obtain ⟨p, W, hWc, hpW, hip⟩ := G.waveThread_nonempty
    (G.waveChainBase_mem c hcne) a.2
  exact (G.extends_initial
    (DirectedPath.Path.extends_chainLimit (G.waveThread c a.1)
      (G.waveThread_nonempty (G.waveChainBase_mem c hcne) a.2)
      (G.waveThread_isChain hc a.1) ⟨W, hWc, hpW, hip⟩)).symm.trans hip

/-- The path family obtained by taking the direct limit in every initial
thread. -/
noncomputable def waveChainUpper (c : Set G.Wave) (hcne : c.Nonempty)
    (hc : IsChain (· ≤ ·) c) : Set G.DPath :=
  Set.range (G.waveThreadLimit c hcne hc)

theorem mem_waveChainUpper_iff (c : Set G.Wave) (hcne : c.Nonempty)
    (hc : IsChain (· ≤ ·) c) (p : G.DPath) :
    p ∈ G.waveChainUpper c hcne hc ↔
      ∃ a : G.initialSet (G.waveChainBase c hcne).1,
        G.waveThreadLimit c hcne hc a = p :=
  Iff.rfl

theorem initialSet_waveChainUpper (c : Set G.Wave) (hcne : c.Nonempty)
    (hc : IsChain (· ≤ ·) c) :
    G.initialSet (G.waveChainUpper c hcne hc) =
      G.initialSet (G.waveChainBase c hcne).1 := by
  apply Set.Subset.antisymm
  · rintro x ⟨p, ⟨a, rfl⟩, rfl⟩
    simpa [G.waveThreadLimit_initial c hcne hc a] using a.2
  · intro x hx
    let a : G.initialSet (G.waveChainBase c hcne).1 := ⟨x, hx⟩
    exact ⟨G.waveThreadLimit c hcne hc a, ⟨a, rfl⟩,
      G.waveThreadLimit_initial c hcne hc a⟩

/-- Two members of a chain have a common later member (one of the two). -/
theorem exists_common_later {c : Set G.Wave}
    (hc : IsChain (· ≤ ·) c) {U W : G.Wave} (hUc : U ∈ c) (hWc : W ∈ c) :
    ∃ Z ∈ c, U ≤ Z ∧ W ≤ Z := by
  by_cases hUW : U = W
  · subst W
    exact ⟨U, hUc, le_rfl, le_rfl⟩
  · rcases hc hUc hWc hUW with h | h
    · exact ⟨W, hWc, h, le_rfl⟩
    · exact ⟨U, hUc, le_rfl, h⟩

/-- Paths drawn from two stages of a wave chain have extensions in one
common later stage. -/
theorem exists_common_stage_extensions {c : Set G.Wave}
    (hc : IsChain (· ≤ ·) c) {U W : G.Wave} (hUc : U ∈ c) (hWc : W ∈ c)
    {p q : G.DPath} (hpU : p ∈ U.1) (hqW : q ∈ W.1) :
    ∃ Z ∈ c, ∃ r ∈ Z.1, ∃ s ∈ Z.1,
      G.Extends p r ∧ G.Extends q s := by
  obtain ⟨Z, hZc, hUZ, hWZ⟩ := G.exists_common_later hc hUc hWc
  obtain ⟨r, hrZ, hpr⟩ := hUZ.1 p hpU
  obtain ⟨s, hsZ, hqs⟩ := hWZ.1 q hqW
  exact ⟨Z, hZc, r, hrZ, s, hsZ, hpr, hqs⟩

theorem isWarp_waveChainUpper (c : Set G.Wave) (hcne : c.Nonempty)
    (hc : IsChain (· ≤ ·) c) :
    G.IsWarp (G.waveChainUpper c hcne hc) := by
  rintro qa ⟨a, rfl⟩ qb ⟨b, rfl⟩ hab
  apply Set.disjoint_left.2
  intro x hxa hxb
  have hthreadA := G.waveThread_isChain hc a.1
  have hthreadB := G.waveThread_isChain hc b.1
  have hneA := G.waveThread_nonempty (G.waveChainBase_mem c hcne) a.2
  have hneB := G.waveThread_nonempty (G.waveChainBase_mem c hcne) b.2
  have hxa' : x ∈ ⋃ p ∈ G.waveThread c a.1, p.support := by
    simpa only [waveThreadLimit, DirectedPath.Path.support_chainLimit] using hxa
  have hxb' : x ∈ ⋃ p ∈ G.waveThread c b.1, p.support := by
    simpa only [waveThreadLimit, DirectedPath.Path.support_chainLimit] using hxb
  simp only [Set.mem_iUnion] at hxa' hxb'
  obtain ⟨p, hpThread, hxp⟩ := hxa'
  obtain ⟨q, hqThread, hxq⟩ := hxb'
  obtain ⟨U, hUc, hpU, hip⟩ := hpThread
  obtain ⟨W, hWc, hqW, hiq⟩ := hqThread
  obtain ⟨Z, hZc, r, hrZ, s, hsZ, hpr, hqs⟩ :=
    G.exists_common_stage_extensions hc hUc hWc hpU hqW
  have hxr : x ∈ r.support := G.support_mono_of_extends hpr hxp
  have hxs : x ∈ s.support := G.support_mono_of_extends hqs hxq
  have hrs : r = s := by
    by_contra hrs
    exact Set.disjoint_left.1 (Z.property.1 hrZ hsZ hrs) hxr hxs
  have habv : a.1 = b.1 := by
    calc
      a.1 = p.initial := hip.symm
      _ = r.initial := G.extends_initial hpr
      _ = s.initial := congrArg DirectedPath.Path.initial hrs
      _ = q.initial := (G.extends_initial hqs).symm
      _ = b.1 := hiq
  have hab' : a = b := Subtype.ext habv
  exact hab (congrArg (G.waveThreadLimit c hcne hc) hab')

theorem forwardExtension_waveChainUpper (c : Set G.Wave) (hcne : c.Nonempty)
    (hc : IsChain (· ≤ ·) c) {W : G.Wave} (hWc : W ∈ c) :
    G.ForwardExtension W.1 (G.waveChainUpper c hcne hc) := by
  have hbase := G.waveChainBase_mem c hcne
  have hiEq : G.initialSet W.1 = G.initialSet (G.waveChainBase c hcne).1 :=
    G.initialSet_eq_of_mem_chain hc hWc hbase
  constructor
  · intro p hpW
    have hpInit : p.initial ∈ G.initialSet W.1 := ⟨p, hpW, rfl⟩
    let a : G.initialSet (G.waveChainBase c hcne).1 :=
      ⟨p.initial, hiEq ▸ hpInit⟩
    refine ⟨G.waveThreadLimit c hcne hc a, ⟨a, rfl⟩, ?_⟩
    exact DirectedPath.Path.extends_chainLimit (G.waveThread c a.1)
      (G.waveThread_nonempty hbase a.2) (G.waveThread_isChain hc a.1)
      ⟨W, hWc, hpW, rfl⟩
  · intro q hq
    obtain ⟨a, rfl⟩ := hq
    have haW : a.1 ∈ G.initialSet W.1 := hiEq.symm ▸ a.2
    obtain ⟨p, hpW, hpa⟩ := haW
    refine ⟨p, hpW, ?_⟩
    exact DirectedPath.Path.extends_chainLimit (G.waveThread c a.1)
      (G.waveThread_nonempty hbase a.2) (G.waveThread_isChain hc a.1)
      ⟨W, hWc, hpW, hpa⟩

/-- The terminal frontier of an earlier wave lies under the roof of the
terminal frontier of a forward extension. -/
theorem terminalFrontier_subset_roof_of_forwardExtension
    {U W : Set G.DPath} (hW : G.IsWave W)
    (hUW : G.ForwardExtension U W) :
    G.terminalFrontier U ⊆ G.roof (G.terminalFrontier W) := by
  rintro t ⟨p, hpU, hpt⟩
  obtain ⟨q, hqW, hpq⟩ := hUW.1 p hpU
  apply hW.self_roofing
  apply (G.mem_vertexSet).2
  exact ⟨q, hqW, G.support_mono_of_extends hpq (G.terminal_mem_support hpt)⟩

/-- Forward extension of a wave advances (or preserves) its roof. -/
theorem roofLE_of_forwardExtension {U W : Set G.DPath}
    (hW : G.IsWave W) (hUW : G.ForwardExtension U W) :
    G.RoofLE U W :=
  G.roof_cut (G.terminalFrontier_subset_roof_of_forwardExtension hW hUW)

/-- A last-hit argument: for a directed family whose members progressively
roof one another, the union of their roofs is below the roof of the set
liminf. -/
theorem roof_setLiminf_of_roof_chain
    {I : Type v} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (S : I → Set V)
    (hS : ∀ ⦃i j⦄, i ≤ j → S i ⊆ G.roof (S j)) :
    (⋃ i, G.roof (S i)) ⊆ G.roof (setLiminf S) := by
  classical
  intro x hx p hp
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨y, hyp, hySi⟩ := hxi p hp
  let U : Set V := ⋃ j, S j
  have hpU : p.walk.Meets U :=
    ⟨y, hyp, Set.mem_iUnion_of_mem i hySi⟩
  let q : FinitePath G.graph := p.lastHit U hpU
  have hqStartU : q.start ∈ U := FinitePath.lastHit_start_mem p U hpU
  obtain ⟨j₀, hqStartj₀⟩ := Set.mem_iUnion.mp hqStartU
  have hlate : ∀ j, j₀ ≤ j → q.start ∈ S j := by
    intro j hj
    have hroof : q.start ∈ G.roof (S j) := hS hj hqStartj₀
    have hqTarget : G.IsTargetPathFrom q.start q := ⟨rfl, hp.2⟩
    obtain ⟨z, hzq, hzSj⟩ := hroof q hqTarget
    change z ∈ q.walk.support at hzq
    have hsupport : q.walk.support = q.start :: q.walk.support.tail := by
      have h := (List.cons_head_tail q.walk.support_ne_nil).symm
      simpa only [q.walk.head_support] using h
    rw [hsupport] at hzq
    rcases List.mem_cons.mp hzq with hzs | hzTail
    · exact hzs ▸ hzSj
    · exact False.elim
        (FinitePath.lastHit_no_mem_after p U hpU hzTail
          (Set.mem_iUnion_of_mem j hzSj))
  refine ⟨q.start, ?_, ?_⟩
  · exact FinitePath.lastHit_support_subset p U hpU q.start_mem_support
  · exact (mem_setLiminf S q.start).mpr ⟨j₀, hlate⟩

/-- Directed limits of waves retain the separator property once their
eventual terminal vertices occur as terminals in the limit family. -/
theorem limit_terminalFrontier_separates
    {I : Type v} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (stage : I → Set G.DPath) (L : Set G.DPath)
    (hWave : ∀ i, G.IsWave (stage i))
    (hforward : ∀ ⦃i j⦄, i ≤ j → G.ForwardExtension (stage i) (stage j))
    (hterminal : setLiminf (fun i ↦ G.terminalFrontier (stage i)) ⊆
      G.terminalFrontier L) :
    G.source ⊆ G.roof (G.terminalFrontier L) := by
  intro a ha
  let i₀ := Classical.choice (inferInstance : Nonempty I)
  have haUnion : a ∈ ⋃ i, G.roof (G.terminalFrontier (stage i)) :=
    Set.mem_iUnion_of_mem i₀ ((hWave i₀).2.2 ha)
  have hchain : ∀ ⦃i j⦄, i ≤ j →
      G.terminalFrontier (stage i) ⊆
        G.roof (G.terminalFrontier (stage j)) := by
    intro i j hij
    exact G.terminalFrontier_subset_roof_of_forwardExtension
      (hWave j) (hforward hij)
  exact G.roof_mono hterminal
    (G.roof_setLiminf_of_roof_chain
      (fun i ↦ G.terminalFrontier (stage i)) hchain haUnion)

/-- Every vertex that is eventually terminal along a chain of waves is
terminal on the corresponding direct-limit path. -/
theorem terminalFrontier_waveChainUpper_of_setLiminf
    (c : Set G.Wave) (hcne : c.Nonempty) (hc : IsChain (· ≤ ·) c) :
    setLiminf (fun W : c ↦ G.terminalFrontier W.1) ⊆
      G.terminalFrontier (G.waveChainUpper c hcne hc) := by
  let : Nonempty c := ⟨⟨hcne.choose, hcne.choose_spec⟩⟩
  let : IsDirectedOrder c := hc.directedOn.isDirectedOrder
  intro x hx
  obtain ⟨U₀, hxlate⟩ := (mem_setLiminf _ _).mp hx
  have hxU₀ : x ∈ G.terminalFrontier U₀.1 := hxlate U₀ le_rfl
  obtain ⟨p₀, hp₀U₀, hp₀term⟩ := hxU₀
  have hp₀initU₀ : p₀.initial ∈ G.initialSet U₀.1 := ⟨p₀, hp₀U₀, rfl⟩
  have hinitEq := G.initialSet_eq_of_mem_chain hc U₀.2
    (G.waveChainBase_mem c hcne)
  let a : G.initialSet (G.waveChainBase c hcne).1 :=
    ⟨p₀.initial, hinitEq ▸ hp₀initU₀⟩
  have hcofinal : DirectedPath.Path.TerminalCofinal
      (G.waveThread c a.1) x := by
    intro p hpThread
    obtain ⟨U, hUc, hpU, hpinit⟩ := hpThread
    obtain ⟨Z, hZc, hUZ, hU₀Z⟩ := G.exists_common_later hc hUc U₀.2
    obtain ⟨q, hqZ, hpq⟩ := hUZ.1 p hpU
    obtain ⟨s, hsZ, hp₀s⟩ := hU₀Z.1 p₀ hp₀U₀
    have hxZ : x ∈ G.terminalFrontier Z.1 := hxlate ⟨Z, hZc⟩ hU₀Z
    obtain ⟨r, hrZ, hrterm⟩ := hxZ
    have hxs : x ∈ s.support :=
      G.support_mono_of_extends hp₀s (G.terminal_mem_support hp₀term)
    have hxr : x ∈ r.support := G.terminal_mem_support hrterm
    have hsr : s = r := by
      by_contra hne
      exact Set.disjoint_left.1 (Z.property.1 hsZ hrZ hne) hxs hxr
    have hqinit : q.initial = a.1 :=
      (G.extends_initial hpq).symm.trans hpinit
    have hsinit : s.initial = a.1 :=
      (G.extends_initial hp₀s).symm.trans rfl
    have hqs : q = s :=
      IsWarp.eq_of_initial_eq G Z.property.1 hqZ hsZ
        (hqinit.trans hsinit.symm)
    refine ⟨q, ?_, hpq, ?_⟩
    · exact ⟨Z, hZc, hqZ, hqinit⟩
    · simpa only [hqs, hsr] using hrterm
  let L := G.waveThreadLimit c hcne hc a
  have hLterm : L.terminal? = some x := by
    exact DirectedPath.Path.terminal_chainLimit_of_cofinal
      (G.waveThread c a.1)
      (G.waveThread_nonempty (G.waveChainBase_mem c hcne) a.2)
      (G.waveThread_isChain hc a.1) hcofinal
  exact ⟨L, ⟨a, rfl⟩, hLterm⟩

/-- The direct limit of a nonempty chain of concrete waves is a wave.  This
is the concrete content of Aharoni--Berger, Lemma 3.19. -/
theorem isWave_waveChainUpper (c : Set G.Wave) (hcne : c.Nonempty)
    (hc : IsChain (· ≤ ·) c) :
    G.IsWave (G.waveChainUpper c hcne hc) := by
  refine ⟨G.isWarp_waveChainUpper c hcne hc, ?_, ?_⟩
  · rw [G.initialSet_waveChainUpper c hcne hc]
    exact (G.waveChainBase c hcne).property.2.1
  · let : Nonempty c := ⟨⟨hcne.choose, hcne.choose_spec⟩⟩
    let : IsDirectedOrder c := hc.directedOn.isDirectedOrder
    exact G.limit_terminalFrontier_separates
      (fun W : c ↦ W.1.1) (G.waveChainUpper c hcne hc)
      (fun W ↦ W.1.property) (fun {_ _} hij ↦ hij)
      (G.terminalFrontier_waveChainUpper_of_setLiminf c hcne hc)

/-- The bundled direct-limit wave of a nonempty chain. -/
noncomputable def waveChainUpperWave (c : Set G.Wave) (hcne : c.Nonempty)
    (hc : IsChain (· ≤ ·) c) : G.Wave :=
  ⟨G.waveChainUpper c hcne hc, G.isWave_waveChainUpper c hcne hc⟩

/-- Each stage forward-extends to the bundled direct-limit wave. -/
theorem le_waveChainUpperWave (c : Set G.Wave) (hcne : c.Nonempty)
    (hc : IsChain (· ≤ ·) c) {W : G.Wave} (hWc : W ∈ c) :
    W ≤ G.waveChainUpperWave c hcne hc :=
  G.forwardExtension_waveChainUpper c hcne hc hWc

/-- Every nonempty chain of concrete waves has a forward-extension upper
bound.  Together with `isWave_waveChainUpper`, this is Lemma 3.19 in its
order-theoretic form. -/
theorem waveChain_hasUpperBound (c : Set G.Wave)
    (hc : IsChain (· ≤ ·) c) (hcne : c.Nonempty) :
    ∃ ub : G.Wave, ∀ W ∈ c, W ≤ ub := by
  exact ⟨G.waveChainUpperWave c hcne hc,
    fun _ hWc ↦ G.le_waveChainUpperWave c hcne hc hWc⟩

/-- Aharoni--Berger, Lemma 3.20: every concrete wave has a maximal forward
extension. -/
theorem exists_maximal_wave_extending (W₀ : G.Wave) :
    ∃ M : G.Wave, W₀ ≤ M ∧ IsMax M := by
  exact G.exists_maximal_forward_extension W₀
    (fun c hc hcne ↦ G.waveChain_hasUpperBound c hc hcne)

/-- Every web has a forward-extension-maximal wave. -/
theorem exists_maximal_wave : ∃ M : G.Wave, IsMax M := by
  let W₀ : G.Wave := ⟨G.trivialWave, G.isWave_trivialWave⟩
  obtain ⟨M, -, hM⟩ := G.exists_maximal_wave_extending W₀
  exact ⟨M, hM⟩

/-- Corollary 3.21: a hindrance forward-extends to a maximal hindrance. -/
theorem exists_maximal_hindrance_extending {W₀ : Set G.DPath}
    (hW₀ : G.IsHindrance W₀) :
    ∃ M : G.Wave, G.ForwardExtension W₀ M.1 ∧
      IsMax M ∧ G.IsHindrance M.1 := by
  let U₀ : G.Wave := ⟨W₀, hW₀.1⟩
  obtain ⟨M, hU₀M, hMmax⟩ := G.exists_maximal_wave_extending U₀
  refine ⟨M, hU₀M, hMmax, M.property, ?_⟩
  intro hMsource
  apply hW₀.2
  rw [G.initialSet_eq_of_forwardExtension hU₀M, hMsource]

/-- If the web has any hindrance, it has a maximal one. -/
theorem exists_maximal_hindrance
    (hG : ∃ W : Set G.DPath, G.IsHindrance W) :
    ∃ M : G.Wave, IsMax M ∧ G.IsHindrance M.1 := by
  obtain ⟨W, hW⟩ := hG
  obtain ⟨M, -, hMmax, hMh⟩ := G.exists_maximal_hindrance_extending hW
  exact ⟨M, hMmax, hMh⟩

/-! ## Roof maximality -/

/-- Equality modulo the essential terminal frontier. -/
def RoofEquivalent (U W : Set G.DPath) : Prop :=
  G.essential (G.terminalFrontier U) =
    G.essential (G.terminalFrontier W)

/-- Maximality in the roof preorder, stated without installing a second
global order on the type of waves. -/
def IsRoofMaximal (M : G.Wave) : Prop :=
  ∀ W : G.Wave, G.RoofLE M.1 W.1 → G.RoofLE W.1 M.1

theorem roofLE_of_roofEquivalent {U W : Set G.DPath}
    (h : G.RoofEquivalent U W) : G.RoofLE U W := by
  rw [RoofLE, ← G.roof_essential (G.terminalFrontier U),
    ← G.roof_essential (G.terminalFrontier W), h]

/-- Mutual comparison in roof order is exactly enough to identify the
essential terminal frontiers. -/
theorem roofEquivalent_of_mutual_roofLE {U W : Set G.DPath}
    (hUW : G.RoofLE U W) (hWU : G.RoofLE W U) :
    G.RoofEquivalent U W := by
  let S := G.terminalFrontier U
  let T := G.terminalFrontier W
  have hTS : T ⊆ G.roof S :=
    (G.subset_roof T).trans hWU
  have hST : S ⊆ G.roof T :=
    (G.subset_roof S).trans hUW
  calc
    G.essential S = G.essential (S ∪ T) :=
      (RelationalRoof.essential_union_eq_of_subset_roof
        G.graph.Adj G.target hTS).symm
    _ = G.essential (T ∪ S) := by rw [Set.union_comm]
    _ = G.essential T :=
      RelationalRoof.essential_union_eq_of_subset_roof
        G.graph.Adj G.target hST

/-! ## Quotient source -/

/-- Essentialization is idempotent. -/
theorem essential_idem (S : Set V) :
    G.essential (G.essential S) = G.essential S := by
  exact RelationalRoof.essential_sandwich G.graph.Adj G.target
    (C := G.essential S) (D := S) Set.Subset.rfl (G.essential_subset S)

theorem strictRoof_essential (S : Set V) :
    G.strictRoof (G.essential S) = G.strictRoof S := by
  rw [strictRoof, strictRoof, G.roof_essential, G.essential_idem]

/-- When `S` roofs the source, quotienting by `S` or by its essential part
produces definitionally transportable equal webs.  The graph argument uses
that inessential points of `S` already lie in its strict roof. -/
theorem quotient_essential_eq_of_subset_roof (S : Set V)
    (hsource : G.source ⊆ G.roof S) :
    G.quotient (G.essential S) = G.quotient S := by
  cases G with
  | mk graph source target =>
    simp only [quotient]
    congr 1
    · ext x y
      simp only [quotientGraph]
      rw [strictRoof_essential]
      constructor
      · rintro ⟨hxy, hx, hy, hyEss⟩
        refine ⟨hxy, hx, hy, ?_⟩
        intro hyS
        by_cases hEss : y ∈ (DWeb.mk graph source target).essential S
        · exact hyEss hEss
        · exact hy ⟨(DWeb.mk graph source target).subset_roof S hyS, hEss⟩
      · rintro ⟨hxy, hx, hy, hyS⟩
        exact ⟨hxy, hx, hy, fun hEss ↦ hyS hEss.1⟩
    · rw [Set.union_comm source, Set.union_comm source]
      calc
        (DWeb.mk graph source target).essential
            ((DWeb.mk graph source target).essential S ∪ source) =
            (DWeb.mk graph source target).essential
              ((DWeb.mk graph source target).essential S) :=
          RelationalRoof.essential_union_eq_of_subset_roof
            graph.Adj target (by
              have hs : source ⊆
                  (DWeb.mk graph source target).roof
                    ((DWeb.mk graph source target).essential S) := by
                rw [(DWeb.mk graph source target).roof_essential]
                exact hsource
              exact hs)
        _ = (DWeb.mk graph source target).essential S :=
          (DWeb.mk graph source target).essential_idem S
        _ = (DWeb.mk graph source target).essential (S ∪ source) :=
          (RelationalRoof.essential_union_eq_of_subset_roof
            graph.Adj target hsource).symm

/-- Observation 3.24: quotienting by the terminal frontier of a wave makes
its essential terminal frontier the new source. -/
theorem quotient_source_terminalFrontier_of_isWave
    {W : Set G.DPath} (hW : G.IsWave W) :
    (G.quotient (G.terminalFrontier W)).source =
      G.essential (G.terminalFrontier W) := by
  rw [G.quotient_source, Set.union_comm]
  exact RelationalRoof.essential_union_eq_of_subset_roof
    G.graph.Adj G.target hW.2.2

/-- The normalized version of Observation 3.24, quotienting by the
essential terminal frontier itself. -/
theorem quotient_source_essentialTerminalFrontier_of_isWave
    {W : Set G.DPath} (hW : G.IsWave W) :
    (G.quotient (G.essential (G.terminalFrontier W))).source =
      G.essential (G.terminalFrontier W) := by
  rw [G.quotient_source, Set.union_comm]
  calc
    G.essential
        (G.essential (G.terminalFrontier W) ∪ G.source) =
        G.essential (G.essential (G.terminalFrontier W)) :=
      RelationalRoof.essential_union_eq_of_subset_roof
        G.graph.Adj G.target (by
          have hs : G.source ⊆
              G.roof (G.essential (G.terminalFrontier W)) := by
            rw [G.roof_essential]
            exact hW.2.2
          exact hs)
    _ = G.essential (G.terminalFrontier W) := G.essential_idem _

/-- Lifting a quotient path preserves whether it is finite and its terminal
vertex. -/
@[simp]
theorem terminal?_liftQuotientPath (S : Set V)
    (q : (G.quotient S).DPath) :
    (G.liftQuotientPath S q).terminal? = q.terminal? := by
  rcases q with q | r <;> rfl

/-- Every quotient-path vertex after the initial one avoids both the old
strict roof and the commitment set. -/
theorem quotientPath_avoids_after_initial (S : Set V)
    (q : (G.quotient S).DPath) {x : V} (hx : x ∈ q.support)
    (hne : x ≠ q.initial) :
    x ∉ G.strictRoof S ∧ x ∉ S := by
  rcases q with q | r
  · have hxwalk : x ∈ q.walk.support := hx
    rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
      (G.quotient S).graph.Adj q.walk).1 hxwalk with hstart | htail
    · exact (hne hstart).elim
    · exact G.quotientWalk_tail_avoids q.walk htail
  · obtain ⟨n, hn⟩ := hx
    cases n with
    | zero =>
        exact (hne (by simpa [DirectedPath.Path.initial,
          DirectedPath.Ray.initial] using hn.symm)).elim
    | succ n =>
        have he := r.adj_succ n
        have hxn : x = r (n + 1) := hn.symm
        exact hxn.symm ▸ ⟨he.2.2.1, he.2.2.2⟩

/-- A simple finite path or ray supported only at its initial vertex is the
length-zero path. -/
theorem path_eq_trivial_of_support_subset (H : DWeb V) (q : H.DPath)
    (hsub : q.support ⊆ {q.initial}) :
    q = H.trivialPath q.initial := by
  rcases q with f | r
  · rcases f with ⟨a, b, w, hw⟩
    cases w with
    | nil => rfl
    | @cons a c b e w =>
        exfalso
        have hc : c ∈ ({x | x ∈ a :: w.support} : Set V) := by simp
        have hca : c = a := Set.mem_singleton_iff.mp (hsub hc)
        have hnot : a ∉ w.support := (List.nodup_cons.mp hw).1
        exact hnot (hca.symm ▸ w.start_mem_support)
  · exfalso
    have hr1 : r 1 ∈ r.support := ⟨1, rfl⟩
    have heq : r 1 = r 0 := by
      simpa [DirectedPath.Path.initial, DirectedPath.Ray.initial] using
        Set.mem_singleton_iff.mp (hsub hr1)
    exact Nat.one_ne_zero (r.injective heq)

/-- A nontrivial path has a vertex strictly after its initial vertex. -/
theorem exists_support_ne_initial_of_ne_trivial (H : DWeb V) (q : H.DPath)
    (hne : q ≠ H.trivialPath q.initial) :
    ∃ x ∈ q.support, x ≠ q.initial := by
  by_contra h
  apply hne
  apply H.path_eq_trivial_of_support_subset
  intro x hx
  apply Set.mem_singleton_iff.mpr
  by_contra hxne
  exact h ⟨x, hx, hxne⟩

end DWeb

namespace DirectedPath

variable {V : Type u} {D : Digraph V}

namespace Ray

/-- Add one new vertex and edge in front of a ray. -/
def cons {a : V} (r : Ray D) (h : D.Adj a r.initial) (ha : a ∉ r.support) : Ray D where
  toFun
    | 0 => a
    | n + 1 => r n
  adj_succ
    | 0 => h
    | n + 1 => r.adj_succ n
  injective := by
    intro m n hmn
    cases m with
    | zero =>
      cases n with
      | zero => rfl
      | succ n => exact (ha ⟨n, hmn.symm⟩).elim
    | succ m =>
      cases n with
      | zero => exact (ha ⟨m, hmn⟩).elim
      | succ n => exact congrArg Nat.succ (r.injective hmn)

@[simp] theorem cons_apply_zero {a : V} (r : Ray D) (h : D.Adj a r.initial)
    (ha : a ∉ r.support) : r.cons h ha 0 = a := rfl

@[simp] theorem cons_apply_succ {a : V} (r : Ray D) (h : D.Adj a r.initial)
    (ha : a ∉ r.support) (n : ℕ) : r.cons h ha (n + 1) = r n := rfl

@[simp] theorem initial_cons {a : V} (r : Ray D) (h : D.Adj a r.initial)
    (ha : a ∉ r.support) : (r.cons h ha).initial = a := rfl

theorem support_cons {a : V} (r : Ray D) (h : D.Adj a r.initial)
    (ha : a ∉ r.support) :
    (r.cons h ha).support = {a} ∪ r.support := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    cases n with
    | zero => exact Or.inl rfl
    | succ n => exact Or.inr ⟨n, rfl⟩
  · rintro (rfl | ⟨n, rfl⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨n + 1, rfl⟩

end Ray

namespace Walk

/-- A ray obtained by placing a finite simple walk in front of a ray. -/
structure PrependRayResult {a b : V} (p : Walk D a b) (r : Ray D) where
  ray : Ray D
  initial_eq : ray.initial = a
  support_eq : ray.support = {x | x ∈ p.support} ∪ r.support
  initialSegment : ∀ n (hn : n < p.support.length), p.support[n] = ray n

/-- Prepend a finite simple walk to a ray when their only common vertex is
the joining endpoint. -/
def prependRay : {a b : V} → (p : Walk D a b) → p.IsPath →
    (r : Ray D) → r.initial = b →
    ({x | x ∈ p.support} ∩ r.support ⊆ {b}) → PrependRayResult p r
  | a, _, .nil, _, r, hr, _ =>
      { ray := r
        initial_eq := hr
        support_eq := by
          ext x
          simp only [support_nil, List.mem_singleton, Set.mem_union,
            Set.mem_setOf_eq, Set.mem_singleton_iff]
          constructor
          · exact Or.inr
          · rintro (rfl | hx)
            · simpa [hr] using r.initial_mem_support
            · exact hx
        initialSegment := by
          intro n hn
          have hn0 : n = 0 := by simpa using hn
          subst n
          simpa [Ray.initial] using hr.symm }
  | a, b, .cons e p, hp, r, hr, hinter => by
      have hp' : p.IsPath := by
        simpa [Walk.IsPath] using hp.tail
      have hinter' : {x | x ∈ p.support} ∩ r.support ⊆ {b} := by
        intro x hx
        apply hinter
        refine ⟨?_, hx.2⟩
        change x ∈ (Walk.cons e p).support
        simp only [Walk.support_cons, List.mem_cons]
        exact Or.inr hx.1
      let R := prependRay p hp' r hr hinter'
      have haTail : a ∉ ({x | x ∈ p.support} : Set V) := by
        intro ha
        exact (List.nodup_cons.mp hp).1 ha
      have haRay : a ∉ r.support := by
        intro ha
        have hab : a = b := Set.mem_singleton_iff.mp
          (hinter ⟨by simp, ha⟩)
        exact haTail (hab.symm ▸ p.end_mem_support)
      have haR : a ∉ R.ray.support := by
        rw [R.support_eq]
        exact fun ha => ha.elim haTail haRay
      have e' : D.Adj a R.ray.initial := R.initial_eq.symm ▸ e
      refine
        { ray := R.ray.cons e' haR
          initial_eq := Ray.initial_cons R.ray e' haR
          support_eq := by
            rw [Ray.support_cons, R.support_eq]
            ext x
            simp [or_assoc]
          initialSegment := ?_ }
      intro n hn
      cases n with
      | zero => rfl
      | succ n =>
          simpa only [Walk.support_cons, List.getElem_cons_succ,
            Ray.cons_apply_succ] using R.initialSegment n (by simpa using hn)

end Walk

namespace FinitePath

/-- Append a finite path to another finite path at their sole common endpoint. -/
def appendFiniteAtEndpoint (p q : FinitePath D) (hstart : q.start = p.finish)
    (hdisjoint : p.walk.support.Disjoint q.walk.support.tail) : FinitePath D := by
  rcases q with ⟨qstart, qfinish, qwalk, hq⟩
  dsimp only at hstart
  subst qstart
  exact p.appendWalkOfDisjoint qwalk hq hdisjoint

/-- The sole-intersection form of finite concatenation. -/
def appendFinite (p q : FinitePath D) (hstart : q.start = p.finish)
    (hinter : p.support ∩ q.support ⊆ {p.finish}) : FinitePath D := by
  apply p.appendFiniteAtEndpoint q hstart
  apply List.disjoint_left.2
  intro x hxp hxq
  have hxqSupport : x ∈ q.support := List.mem_of_mem_tail hxq
  have hxeq : x = p.finish := Set.mem_singleton_iff.mp (hinter ⟨hxp, hxqSupport⟩)
  have hhead : q.walk.support.head q.walk.support_ne_nil = q.start :=
    q.walk.head_support
  have hne := q.isPath.rel_head_tail hxq
  apply hne
  rw [hhead, hstart, hxeq]

@[simp] theorem appendFinite_start (p q : FinitePath D)
    (hstart : q.start = p.finish)
    (hinter : p.support ∩ q.support ⊆ {p.finish}) :
    (p.appendFinite q hstart hinter).start = p.start := by
  rcases q with ⟨qstart, qfinish, qwalk, hq⟩
  dsimp only at hstart
  subst qstart
  rfl

@[simp] theorem appendFinite_finish (p q : FinitePath D)
    (hstart : q.start = p.finish)
    (hinter : p.support ∩ q.support ⊆ {p.finish}) :
    (p.appendFinite q hstart hinter).finish = q.finish := by
  rcases q with ⟨qstart, qfinish, qwalk, hq⟩
  dsimp only at hstart
  subst qstart
  rfl

theorem appendFinite_walk_support (p q : FinitePath D)
    (hstart : q.start = p.finish)
    (hinter : p.support ∩ q.support ⊆ {p.finish}) :
    (p.appendFinite q hstart hinter).walk.support =
      p.walk.support ++ q.walk.support.tail := by
  rcases q with ⟨qstart, qfinish, qwalk, hq⟩
  dsimp only at hstart
  subst qstart
  exact Walk.support_append p.walk qwalk

theorem support_appendFinite_eq_union (p q : FinitePath D)
    (hstart : q.start = p.finish)
    (hinter : p.support ∩ q.support ⊆ {p.finish}) :
    (p.appendFinite q hstart hinter).support = p.support ∪ q.support := by
  ext x
  rw [FinitePath.support, p.appendFinite_walk_support q hstart hinter]
  simp only [List.mem_append, Set.mem_union, FinitePath.support]
  constructor
  · rintro (hx | hx)
    · exact Or.inl hx
    · exact Or.inr (List.mem_of_mem_tail hx)
  · rintro (hx | hx)
    · exact Or.inl hx
    · rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
        D.Adj q.walk).1 hx with hxeq | hxtail
      · left
        have : x = p.finish := hxeq.trans hstart
        exact this ▸ p.walk.end_mem_support
      · exact Or.inr hxtail

theorem isPrefixOf_appendFinite (p q : FinitePath D)
    (hstart : q.start = p.finish)
    (hinter : p.support ∩ q.support ⊆ {p.finish}) :
    p.IsPrefixOf (p.appendFinite q hstart hinter) := by
  rw [FinitePath.IsPrefixOf, p.appendFinite_walk_support q hstart hinter]
  exact List.prefix_append _ _

/-- Concatenate a finite path and a ray at their sole common endpoint. -/
def appendRay (p : FinitePath D) (r : Ray D) (hstart : r.initial = p.finish)
    (hinter : p.support ∩ r.support ⊆ {p.finish}) : Ray D :=
  (p.walk.prependRay p.isPath r hstart hinter).ray

@[simp] theorem initial_appendRay (p : FinitePath D) (r : Ray D)
    (hstart : r.initial = p.finish)
    (hinter : p.support ∩ r.support ⊆ {p.finish}) :
    (p.appendRay r hstart hinter).initial = p.start :=
  (p.walk.prependRay p.isPath r hstart hinter).initial_eq

theorem support_appendRay (p : FinitePath D) (r : Ray D)
    (hstart : r.initial = p.finish)
    (hinter : p.support ∩ r.support ⊆ {p.finish}) :
    (p.appendRay r hstart hinter).support = p.support ∪ r.support :=
  (p.walk.prependRay p.isPath r hstart hinter).support_eq

theorem isInitialSegmentOf_appendRay (p : FinitePath D) (r : Ray D)
    (hstart : r.initial = p.finish)
    (hinter : p.support ∩ r.support ⊆ {p.finish}) :
    p.IsInitialSegmentOf (p.appendRay r hstart hinter) :=
  (p.walk.prependRay p.isPath r hstart hinter).initialSegment

end FinitePath

namespace Path

/-- Append a finite path to a finite path or ray. -/
def appendFinite (p : FinitePath D) (q : Path D)
    (hstart : q.initial = p.finish)
    (hinter : p.support ∩ q.support ⊆ {p.finish}) : Path D := by
  rcases q with q | r
  · exact .inl (p.appendFinite q hstart hinter)
  · exact .inr (p.appendRay r hstart hinter)

@[simp] theorem initial_appendFinite (p : FinitePath D) (q : Path D)
    (hstart : q.initial = p.finish)
    (hinter : p.support ∩ q.support ⊆ {p.finish}) :
    (appendFinite p q hstart hinter).initial = p.start := by
  rcases q with q | r
  · exact p.appendFinite_start q hstart hinter
  · exact p.initial_appendRay r hstart hinter

theorem support_appendFinite (p : FinitePath D) (q : Path D)
    (hstart : q.initial = p.finish)
    (hinter : p.support ∩ q.support ⊆ {p.finish}) :
    (appendFinite p q hstart hinter).support = p.support ∪ q.support := by
  rcases q with q | r
  · exact p.support_appendFinite_eq_union q hstart hinter
  · exact p.support_appendRay r hstart hinter

@[simp] theorem terminal?_appendFinite (p : FinitePath D) (q : Path D)
    (hstart : q.initial = p.finish)
    (hinter : p.support ∩ q.support ⊆ {p.finish}) :
    (appendFinite p q hstart hinter).terminal? = q.terminal? := by
  rcases q with q | r
  · change some (p.appendFinite q hstart hinter).finish = some q.finish
    rw [p.appendFinite_finish q hstart hinter]
  · rfl

theorem extends_appendFinite (p : FinitePath D) (q : Path D)
    (hstart : q.initial = p.finish)
    (hinter : p.support ∩ q.support ⊆ {p.finish}) :
    Extends (.inl p) (appendFinite p q hstart hinter) := by
  rcases q with q | r
  · exact p.isPrefixOf_appendFinite q hstart hinter
  · exact p.isInitialSegmentOf_appendRay r hstart hinter

end Path

end DirectedPath

namespace DWeb

variable {V : Type u} (G : DWeb V)

/-- The exact vertex-intersection hypothesis under which source star is
defined: an old and a new path can meet only where the old one terminates
and the new one begins. -/
def StarCompatible (W U : Set G.DPath) : Prop :=
  ∀ p ∈ W, ∀ q ∈ U, ∀ x ∈ p.support, x ∈ q.support →
    G.terminal? p = some x ∧ q.initial = x

/-- Splice one old member to the unique available continuation. -/
noncomputable def starPath {W U : Set G.DPath}
    (hcompat : G.StarCompatible W U) (p : W) : G.DPath := by
  rcases p with ⟨p, hpW⟩
  rcases p with fp | r
  · by_cases h : ∃ q ∈ U, q.initial = fp.finish
    · let q := Classical.choose h
      have hqU := (Classical.choose_spec h).1
      have hqstart := (Classical.choose_spec h).2
      have hinter : fp.support ∩ q.support ⊆ {fp.finish} := by
        intro x hx
        have hx' := hcompat (.inl fp) hpW q hqU x hx.1 hx.2
        exact Set.mem_singleton_iff.2 (Option.some.inj hx'.1).symm
      exact DirectedPath.Path.appendFinite fp q hqstart hinter
    · exact .inl fp
  · exact .inr r

/-- Source-faithful star: one output path for every old path, retaining old
rays and unmatched finite paths. -/
noncomputable def star {W U : Set G.DPath}
    (hcompat : G.StarCompatible W U) : Set G.DPath :=
  Set.range (G.starPath hcompat)

theorem initial_starPath {W U : Set G.DPath}
    (hcompat : G.StarCompatible W U) (p : W) :
    (G.starPath hcompat p).initial = p.1.initial := by
  rcases p with ⟨p, hpW⟩
  rcases p with fp | r
  · simp only [starPath]
    split
    · exact DirectedPath.Path.initial_appendFinite _ _ _ _
    · rfl
  · rfl

theorem extends_starPath {W U : Set G.DPath}
    (hcompat : G.StarCompatible W U) (p : W) :
    G.Extends p.1 (G.starPath hcompat p) := by
  rcases p with ⟨p, hpW⟩
  rcases p with fp | r
  · simp only [starPath]
    split
    · exact DirectedPath.Path.extends_appendFinite _ _ _ _
    · exact G.extends_refl _
  · exact G.extends_refl _

theorem mem_support_starPath_cases {W U : Set G.DPath}
    (hcompat : G.StarCompatible W U) (p : W) {x : V}
    (hx : x ∈ (G.starPath hcompat p).support) :
    x ∈ p.1.support ∨
      ∃ t q, G.terminal? p.1 = some t ∧ q ∈ U ∧
        q.initial = t ∧ x ∈ q.support := by
  rcases p with ⟨p, hpW⟩
  rcases p with fp | r
  · simp only [starPath] at hx
    split at hx
    next h =>
      let q := Classical.choose h
      have hqU := (Classical.choose_spec h).1
      have hqstart := (Classical.choose_spec h).2
      have hinter : fp.support ∩ q.support ⊆ {fp.finish} := by
        intro y hy
        have hy' := hcompat (.inl fp) hpW q hqU y hy.1 hy.2
        exact Set.mem_singleton_iff.2 (Option.some.inj hy'.1).symm
      rw [DirectedPath.Path.support_appendFinite fp q hqstart hinter] at hx
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr ⟨fp.finish, q, rfl, hqU, hqstart, hx⟩
    next h => exact Or.inl hx
  · exact Or.inl hx

theorem isWarp_star {W U : Set G.DPath}
    (hW : G.IsWarp W) (hU : G.IsWarp U)
    (hcompat : G.StarCompatible W U) :
    G.IsWarp (G.star hcompat) := by
  intro r₁ hr₁ r₂ hr₂ hrne
  obtain ⟨p₁, rfl⟩ := hr₁
  obtain ⟨p₂, rfl⟩ := hr₂
  have hpne : p₁.1 ≠ p₂.1 := by
    intro heq
    apply hrne
    exact congrArg (G.starPath hcompat) (Subtype.ext heq)
  apply Set.disjoint_left.2
  intro x hx₁ hx₂
  rcases G.mem_support_starPath_cases hcompat p₁ hx₁ with hx₁old | hx₁new
  · rcases G.mem_support_starPath_cases hcompat p₂ hx₂ with hx₂old | hx₂new
    · exact Set.disjoint_left.1 (hW p₁.2 p₂.2 hpne) hx₁old hx₂old
    · obtain ⟨t₂, q₂, hp₂t, hq₂U, hq₂start, hxq₂⟩ := hx₂new
      have hmeet := hcompat p₁.1 p₁.2 q₂ hq₂U x hx₁old hxq₂
      have hxt₂ : x = t₂ := hmeet.2.symm.trans hq₂start
      exact Set.disjoint_left.1 (hW p₁.2 p₂.2 hpne) hx₁old
        (G.terminal_mem_support (hp₂t.trans (congrArg some hxt₂.symm)))
  · obtain ⟨t₁, q₁, hp₁t, hq₁U, hq₁start, hxq₁⟩ := hx₁new
    rcases G.mem_support_starPath_cases hcompat p₂ hx₂ with hx₂old | hx₂new
    · have hmeet := hcompat p₂.1 p₂.2 q₁ hq₁U x hx₂old hxq₁
      have hxt₁ : x = t₁ := hmeet.2.symm.trans hq₁start
      exact Set.disjoint_left.1 (hW p₁.2 p₂.2 hpne)
        (G.terminal_mem_support (hp₁t.trans (congrArg some hxt₁.symm))) hx₂old
    · obtain ⟨t₂, q₂, hp₂t, hq₂U, hq₂start, hxq₂⟩ := hx₂new
      by_cases hqeq : q₁ = q₂
      · subst q₂
        have ht : t₁ = t₂ := hq₁start.symm.trans hq₂start
        exact Set.disjoint_left.1 (hW p₁.2 p₂.2 hpne)
          (G.terminal_mem_support hp₁t)
          (G.terminal_mem_support (hp₂t.trans (congrArg some ht.symm)))
      · exact Set.disjoint_left.1 (hU hq₁U hq₂U hqeq) hxq₁ hxq₂

theorem initialSet_star_subset {W U : Set G.DPath}
    (hcompat : G.StarCompatible W U) :
    G.initialSet (G.star hcompat) ⊆ G.initialSet W := by
  rintro x ⟨r, ⟨p, rfl⟩, rfl⟩
  exact ⟨p.1, p.2, (G.initial_starPath hcompat p).symm⟩

theorem forwardExtension_star {W U : Set G.DPath}
    (hcompat : G.StarCompatible W U) :
    G.ForwardExtension W (G.star hcompat) := by
  constructor
  · intro p hp
    exact ⟨G.starPath hcompat ⟨p, hp⟩, ⟨⟨p, hp⟩, rfl⟩,
      G.extends_starPath hcompat ⟨p, hp⟩⟩
  · rintro r ⟨p, rfl⟩
    exact ⟨p.1, p.2, G.extends_starPath hcompat p⟩

/-! ### Quotient families and source star specialization -/

/-- Transport a quotient family back to the original graph. -/
def liftQuotientFamily (S : Set V)
    (U : Set (G.quotient S).DPath) : Set G.DPath :=
  G.liftQuotientPath S '' U

theorem IsWarp.liftQuotientFamily {S : Set V}
    {U : Set (G.quotient S).DPath} (hU : (G.quotient S).IsWarp U) :
    G.IsWarp (G.liftQuotientFamily S U) := by
  rintro p ⟨p₀, hp₀, rfl⟩ q ⟨q₀, hq₀, rfl⟩ hpq
  change Disjoint (G.liftQuotientPath S p₀).support
    (G.liftQuotientPath S q₀).support
  rw [G.support_liftQuotientPath, G.support_liftQuotientPath]
  apply hU hp₀ hq₀
  intro hp₀q₀
  subst q₀
  exact hpq rfl

@[simp] theorem initialSet_liftQuotientFamily (S : Set V)
    (U : Set (G.quotient S).DPath) :
    G.initialSet (G.liftQuotientFamily S U) =
      (G.quotient S).initialSet U := by
  ext x
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hpx⟩
    exact ⟨q, hq, by simpa using hpx⟩
  · rintro ⟨q, hq, hqx⟩
    exact ⟨G.liftQuotientPath S q, ⟨q, hq, rfl⟩, by simpa using hqx⟩

@[simp] theorem terminalFrontier_liftQuotientFamily (S : Set V)
    (U : Set (G.quotient S).DPath) :
    G.terminalFrontier (G.liftQuotientFamily S U) =
      (G.quotient S).terminalFrontier U := by
  ext x
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hpx⟩
    exact ⟨q, hq, by simpa using hpx⟩
  · rintro ⟨q, hq, hqx⟩
    exact ⟨G.liftQuotientPath S q, ⟨q, hq, rfl⟩, by simpa using hqx⟩

/-- Every quotient-path vertex is either its initial vertex or is outside
both the deleted strict roof and the commitment set. -/
theorem quotientPath_support_initial_or_avoids (S : Set V)
    (p : (G.quotient S).DPath) {x : V} (hx : x ∈ p.support) :
    x = p.initial ∨ (x ∉ G.strictRoof S ∧ x ∉ S) := by
  by_cases h : x = p.initial
  · exact Or.inl h
  · exact Or.inr (G.quotientPath_avoids_after_initial S p hx h)

/-- In a warp, a member that meets a terminal-frontier point has that
point as its own terminal. -/
theorem IsWarp.terminal_eq_of_mem_support_mem_terminalFrontier
    {W : Set G.DPath} (hW : G.IsWarp W) {p : G.DPath} (hpW : p ∈ W)
    {x : V} (hxp : x ∈ p.support) (hxT : x ∈ G.terminalFrontier W) :
    G.terminal? p = some x := by
  obtain ⟨q, hqW, hqx⟩ := hxT
  by_cases hpq : p = q
  · simpa [hpq] using hqx
  · exact (Set.disjoint_left.1 (hW hpW hqW hpq) hxp
      (G.terminal_mem_support hqx)).elim

/-- A wave is compatible with every lifted quotient wave at its essential
terminal frontier. -/
theorem starCompatible_liftQuotientFamily {W : Set G.DPath}
    (hW : G.IsWave W)
    {U : Set (G.quotient (G.essential (G.terminalFrontier W))).DPath}
    (hU : (G.quotient
      (G.essential (G.terminalFrontier W))).IsWave U) :
    G.StarCompatible W
      (G.liftQuotientFamily (G.essential (G.terminalFrontier W)) U) := by
  let S := G.essential (G.terminalFrontier W)
  have hEssS : G.essential S = S := by
    dsimp only [S]
    exact RelationalRoof.essential_sandwich G.graph.Adj G.target
      (C := G.essential (G.terminalFrontier W))
      (D := G.terminalFrontier W) Set.Subset.rfl (G.essential_subset _)
  intro p hpW q hq x hxp hxq
  obtain ⟨q₀, hq₀U, rfl⟩ := hq
  have hq₀init : q₀.initial ∈ (G.quotient S).source := by
    apply hU.2.1
    exact ⟨q₀, hq₀U, rfl⟩
  have hsource : (G.quotient S).source = S := by
    simpa [S] using G.quotient_source_essentialTerminalFrontier_of_isWave hW
  have hq₀initS : q₀.initial ∈ S := hsource ▸ hq₀init
  have hxRoof : x ∈ G.roof S := by
    rw [G.roof_essential]
    exact DWeb.IsWave.self_roofing G hW ⟨p, hpW, hxp⟩
  have hxclass := G.quotientPath_support_initial_or_avoids S q₀ (by
    simpa using hxq)
  have hxeq : q₀.initial = x := by
    rcases hxclass with h | h
    · exact h.symm
    · exfalso
      have hxEss : x ∈ G.essential S := by
        by_contra hxNotEss
        exact h.1 ⟨hxRoof, hxNotEss⟩
      exact h.2 (hEssS ▸ hxEss)
  have hxT : x ∈ G.terminalFrontier W :=
    G.essential_subset _ (hxeq ▸ hq₀initS)
  exact ⟨DWeb.IsWarp.terminal_eq_of_mem_support_mem_terminalFrontier
      G hW.1 hpW hxp hxT,
    by simpa using hxeq⟩

/-- If every new path begins at an old terminal, every new finite terminal
is the terminal of its starred old path. -/
theorem terminalFrontier_subset_star {W U : Set G.DPath}
    (hU : G.IsWarp U) (hcompat : G.StarCompatible W U)
    (hcover : ∀ q ∈ U, q.initial ∈ G.terminalFrontier W) :
    G.terminalFrontier U ⊆ G.terminalFrontier (G.star hcompat) := by
  rintro x ⟨q, hqU, hqx⟩
  obtain ⟨p, hpW, hpinit⟩ := hcover q hqU
  rcases p with fp | r
  · have hfinish : fp.finish = q.initial := Option.some.inj hpinit
    let old : W := ⟨(.inl fp : G.DPath), hpW⟩
    refine ⟨G.starPath hcompat old, ⟨old, rfl⟩, ?_⟩
    dsimp only [old]
    simp only [starPath]
    split
    next h =>
      let q' := Classical.choose h
      have hq'U : q' ∈ U := (Classical.choose_spec h).1
      have hq'start : q'.initial = fp.finish := (Classical.choose_spec h).2
      have hq'eq : q' = q := by
        by_contra hne
        apply Set.disjoint_left.1 (hU hq'U hqU hne)
          q'.initial_mem_support
        rw [hq'start, hfinish]
        exact q.initial_mem_support
      dsimp only [q'] at hq'eq ⊢
      simpa only [DirectedPath.Path.terminal?_appendFinite, hq'eq] using hqx
    next h =>
      exfalso
      apply h
      exact ⟨q, hqU, hfinish.symm⟩
  · simp at hpinit

/-- Every vertex of a covered new path occurs on the starred old path
whose terminal is its initial vertex. -/
theorem mem_vertexSet_star_of_mem_new {W U : Set G.DPath}
    (hU : G.IsWarp U) (hcompat : G.StarCompatible W U)
    (hcover : ∀ q ∈ U, q.initial ∈ G.terminalFrontier W)
    {q : G.DPath} (hqU : q ∈ U) {x : V} (hxq : x ∈ q.support) :
    x ∈ G.vertexSet (G.star hcompat) := by
  obtain ⟨p, hpW, hpinit⟩ := hcover q hqU
  rcases p with fp | r
  · have hfinish : fp.finish = q.initial := Option.some.inj hpinit
    let old : W := ⟨(.inl fp : G.DPath), hpW⟩
    refine ⟨G.starPath hcompat old, ⟨old, rfl⟩, ?_⟩
    dsimp only [old]
    simp only [starPath]
    split
    next h =>
      let q' := Classical.choose h
      have hq'U : q' ∈ U := (Classical.choose_spec h).1
      have hq'start : q'.initial = fp.finish := (Classical.choose_spec h).2
      have hq'eq : q' = q := by
        by_contra hne
        apply Set.disjoint_left.1 (hU hq'U hqU hne)
          q'.initial_mem_support
        rw [hq'start, hfinish]
        exact q.initial_mem_support
      dsimp only [q'] at hq'eq ⊢
      have hxchoose : x ∈ (Classical.choose h).support := by
        simpa only [hq'eq] using hxq
      have hinter : fp.support ∩ (Classical.choose h).support ⊆
          {fp.finish} := by
        intro y hy
        have hy' := hcompat (.inl fp) hpW (Classical.choose h) hq'U
          y hy.1 hy.2
        exact Set.mem_singleton_iff.2 (Option.some.inj hy'.1).symm
      have hmem : x ∈ (DirectedPath.Path.appendFinite fp
          (Classical.choose h) hq'start hinter).support := by
        rw [DirectedPath.Path.support_appendFinite]
        exact Or.inr hxchoose
      exact hmem
    next h =>
      exfalso
      apply h
      exact ⟨q, hqU, hfinish.symm⟩
  · simp at hpinit

/-- The lifted quotient wave begins at old essential terminals, so its
terminal frontier is inherited by the source star. -/
theorem terminalFrontier_liftQuotientFamily_subset_star
    {W : Set G.DPath} (hW : G.IsWave W)
    {U : Set (G.quotient (G.essential (G.terminalFrontier W))).DPath}
    (hU : (G.quotient
      (G.essential (G.terminalFrontier W))).IsWave U) :
    let S := G.essential (G.terminalFrontier W)
    let L := G.liftQuotientFamily S U
    let hc := G.starCompatible_liftQuotientFamily hW hU
    G.terminalFrontier L ⊆ G.terminalFrontier (G.star hc) := by
  dsimp only
  apply G.terminalFrontier_subset_star
    (DWeb.IsWarp.liftQuotientFamily G hU.1)
  intro q hq
  obtain ⟨q₀, hq₀U, rfl⟩ := hq
  apply G.essential_subset
  have hq₀source := hU.2.1 ⟨q₀, hq₀U, rfl⟩
  rw [G.quotient_source_essentialTerminalFrontier_of_isWave hW] at hq₀source
  simpa using hq₀source

/-- The terminal frontier of any quotient wave still separates the
original source.  The witness is the suffix after the last essential old
terminal on an arbitrary original source--target path. -/
theorem source_subset_roof_quotientWave_terminal
    {W : Set G.DPath} (hW : G.IsWave W)
    {U : Set (G.quotient
      (G.essential (G.terminalFrontier W))).DPath}
    (hU : (G.quotient
      (G.essential (G.terminalFrontier W))).IsWave U) :
    G.source ⊆ G.roof
      ((G.quotient (G.essential (G.terminalFrontier W))).terminalFrontier U) := by
  let S := G.essential (G.terminalFrontier W)
  let Q := G.quotient S
  have hQS : Q.source = S := by
    simpa [S, Q] using G.quotient_source_essentialTerminalFrontier_of_isWave hW
  have hsourceRoofS : G.source ⊆ G.roof S := by
    change G.source ⊆
      G.roof (G.essential (G.terminalFrontier W))
    rw [G.roof_essential]
    exact hW.2.2
  intro a ha p hp
  have hmeetS : G.Meets p S := hsourceRoofS ha p hp
  let hwMeet : p.walk.Meets S :=
    ⟨hmeetS.choose, hmeetS.choose_spec.1, hmeetS.choose_spec.2⟩
  let L := Walk.lastHit p.walk S hwMeet
  obtain ⟨q, hqstart, hqfinish, hqsupport⟩ :=
    G.exists_quotientPath_from_lastHit S p hp hmeetS
  have hLess : L.startpoint ∈ G.essential S :=
    G.lastHit_mem_essential S p hp hmeetS
  have hqsource : q.start ∈ Q.source := by
    rw [hQS, hqstart]
    simpa only [S, G.essential_idem] using hLess
  have hqtarget : Q.IsTargetPathFrom q.start q := by
    refine ⟨rfl, ?_⟩
    change q.finish ∈ G.target
    rw [hqfinish]
    exact hp.2
  obtain ⟨x, hxq, hxT⟩ := hU.2.2 hqsource q hqtarget
  refine ⟨x, ?_, hxT⟩
  apply L.support_subset
  have hxset : x ∈ ({y | y ∈ L.walk.support} : Set V) := by
    rw [← hqsupport]
    exact hxq
  exact hxset

/-- Source Lemma 3.25: a wave starred with a wave in the quotient by its
essential terminal frontier is again a wave. -/
theorem isWave_star_liftQuotientFamily
    {W : Set G.DPath} (hW : G.IsWave W)
    {U : Set (G.quotient
      (G.essential (G.terminalFrontier W))).DPath}
    (hU : (G.quotient
      (G.essential (G.terminalFrontier W))).IsWave U) :
    let S := G.essential (G.terminalFrontier W)
    let L := G.liftQuotientFamily S U
    let hc := G.starCompatible_liftQuotientFamily hW hU
    G.IsWave (G.star hc) := by
  dsimp only
  let S := G.essential (G.terminalFrontier W)
  let L := G.liftQuotientFamily S U
  let hc : G.StarCompatible W L :=
    G.starCompatible_liftQuotientFamily hW hU
  refine ⟨G.isWarp_star hW.1
      (DWeb.IsWarp.liftQuotientFamily G hU.1) hc, ?_, ?_⟩
  · exact (G.initialSet_star_subset hc).trans hW.2.1
  · have hs := G.source_subset_roof_quotientWave_terminal hW hU
    have hfront : G.terminalFrontier L ⊆
        G.terminalFrontier (G.star hc) := by
      exact G.terminalFrontier_liftQuotientFamily_subset_star hW hU
    have hsL : G.source ⊆ G.roof (G.terminalFrontier L) := by
      simpa only [L, S, G.terminalFrontier_liftQuotientFamily] using hs
    exact hsL.trans (G.roof_mono hfront)

/-- Every essential commitment vertex starts an honest finite path in the
quotient to the old target. -/
theorem exists_quotientTargetPath_from_essential (S : Set V) {a : V}
    (ha : a ∈ G.essential S) :
    ∃ q : FinitePath (G.quotient S).graph,
      q.start = a ∧ q.finish ∈ (G.quotient S).target := by
  obtain ⟨p, hp, hav⟩ :=
    (G.not_mem_roof_iff (S \ {a}) a).1 ha.2
  have hmeet : G.Meets p S :=
    ⟨p.start, p.start_mem_support, hp.1 ▸ ha.1⟩
  let hwMeet : p.walk.Meets S :=
    ⟨hmeet.choose, hmeet.choose_spec.1, hmeet.choose_spec.2⟩
  let L := Walk.lastHit p.walk S hwMeet
  obtain ⟨q, hqstart, hqfinish, _hqsupport⟩ :=
    G.exists_quotientPath_from_lastHit S p hp hmeet
  have hLa : L.startpoint = a := by
    by_contra hne
    apply Set.disjoint_left.1 hav
      (L.support_subset L.walk.start_mem_support)
    exact ⟨L.startpoint_mem, by simpa [Set.mem_singleton_iff] using hne⟩
  refine ⟨q, hqstart.trans hLa, ?_⟩
  change q.finish ∈ G.target
  rw [hqfinish]
  exact hp.2

/-- A quotient wave all of whose members are trivial contains exactly the
trivial path at every quotient source. -/
theorem quotientWave_eq_trivialWave_of_all_trivial
    {W : Set G.DPath} (hW : G.IsWave W)
    {U : Set (G.quotient
      (G.essential (G.terminalFrontier W))).DPath}
    (hU : (G.quotient
      (G.essential (G.terminalFrontier W))).IsWave U)
    (hall : ∀ q ∈ U,
      q = (G.quotient
        (G.essential (G.terminalFrontier W))).trivialPath q.initial) :
    U = (G.quotient
      (G.essential (G.terminalFrontier W))).trivialWave := by
  let S := G.essential (G.terminalFrontier W)
  let Q := G.quotient S
  have hQS : Q.source = S := by
    simpa [S, Q] using G.quotient_source_essentialTerminalFrontier_of_isWave hW
  apply Set.Subset.antisymm
  · intro q hqU
    rw [hall q hqU]
    exact ⟨q.initial, hU.2.1 ⟨q, hqU, rfl⟩, rfl⟩
  · rintro _ ⟨a, haQ, rfl⟩
    have haS : a ∈ S := hQS ▸ haQ
    have haEss : a ∈ G.essential S := by
      simpa only [S, G.essential_idem] using haS
    obtain ⟨q, hqstart, hqtarget⟩ :=
      G.exists_quotientTargetPath_from_essential S haEss
    have hqTarget : Q.IsTargetPathFrom a q := ⟨hqstart, hqtarget⟩
    obtain ⟨x, hxq, hxFront⟩ := hU.2.2 haQ q hqTarget
    obtain ⟨r, hrU, hrterm⟩ := hxFront
    have hreq := hall r hrU
    have hrinit : r.initial = x := by
      rw [hreq] at hrterm
      exact Option.some.inj hrterm
    have hxS : x ∈ S := by
      rw [← hQS, ← hrinit]
      exact hU.2.1 ⟨r, hrU, rfl⟩
    have hxa : x = a := by
      by_contra hne
      have hav := G.quotientPath_avoids_after_initial S
        (.inl q) hxq (by
          intro hxi
          apply hne
          exact hxi.trans hqstart)
      exact hav.2 hxS
    have hreqa : r = Q.trivialPath a := by
      simpa [hrinit, hxa] using hreq
    simpa [hreqa] using hrU

/-- Hence a nontrivial quotient wave contains a genuinely nontrivial path. -/
theorem exists_nontrivial_mem_of_quotientWave_ne_trivialWave
    {W : Set G.DPath} (hW : G.IsWave W)
    {U : Set (G.quotient
      (G.essential (G.terminalFrontier W))).DPath}
    (hU : (G.quotient
      (G.essential (G.terminalFrontier W))).IsWave U)
    (hne : U ≠ (G.quotient
      (G.essential (G.terminalFrontier W))).trivialWave) :
    ∃ q ∈ U, q ≠ (G.quotient
      (G.essential (G.terminalFrontier W))).trivialPath q.initial := by
  by_contra h
  apply hne
  apply G.quotientWave_eq_trivialWave_of_all_trivial hW hU
  intro q hqU
  by_contra hq
  exact h ⟨q, hqU, hq⟩

/-- A genuinely nontrivial quotient member makes the star a proper forward
extension: its first later vertex lies outside the old wave's roof. -/
theorem not_forwardExtension_star_liftQuotientFamily_of_nontrivial
    {W : Set G.DPath} (hW : G.IsWave W)
    {U : Set (G.quotient
      (G.essential (G.terminalFrontier W))).DPath}
    (hU : (G.quotient
      (G.essential (G.terminalFrontier W))).IsWave U)
    {q : (G.quotient
      (G.essential (G.terminalFrontier W))).DPath}
    (hqU : q ∈ U)
    (hqne : q ≠ (G.quotient
      (G.essential (G.terminalFrontier W))).trivialPath q.initial) :
    let S := G.essential (G.terminalFrontier W)
    let L := G.liftQuotientFamily S U
    let hc := G.starCompatible_liftQuotientFamily hW hU
    ¬ G.ForwardExtension (G.star hc) W := by
  dsimp only
  let S := G.essential (G.terminalFrontier W)
  let Q := G.quotient S
  let L := G.liftQuotientFamily S U
  let hc : G.StarCompatible W L :=
    G.starCompatible_liftQuotientFamily hW hU
  obtain ⟨x, hxq, hxne⟩ := Q.exists_support_ne_initial_of_ne_trivial q hqne
  have hxavoid : x ∉ G.strictRoof S ∧ x ∉ S :=
    G.quotientPath_avoids_after_initial S q hxq hxne
  have hxNotRoofS : x ∉ G.roof S := by
    intro hxRoof
    have hxEss : x ∈ G.essential S := by
      by_contra hxNotEss
      exact hxavoid.1 ⟨hxRoof, hxNotEss⟩
    have hEssS : G.essential S = S := by
      simpa only [S] using G.essential_idem (G.terminalFrontier W)
    exact hxavoid.2 (hEssS ▸ hxEss)
  have hcover : ∀ r ∈ L, r.initial ∈ G.terminalFrontier W := by
    intro r hr
    obtain ⟨r₀, hr₀U, rfl⟩ := hr
    apply G.essential_subset
    have hr₀source := hU.2.1 ⟨r₀, hr₀U, rfl⟩
    rw [G.quotient_source_essentialTerminalFrontier_of_isWave hW] at hr₀source
    simpa only [S, G.initial_liftQuotientPath] using hr₀source
  have hxstar : x ∈ G.vertexSet (G.star hc) := by
    apply G.mem_vertexSet_star_of_mem_new
      (DWeb.IsWarp.liftQuotientFamily G hU.1) hc hcover
      (q := G.liftQuotientPath S q)
    · exact ⟨q, hqU, rfl⟩
    · simpa using hxq
  intro hback
  obtain ⟨r, hrstar, hxr⟩ := hxstar
  obtain ⟨p, hpW, hrp⟩ := hback.1 r hrstar
  have hxp : x ∈ p.support := G.support_mono_of_extends hrp hxr
  have hxRoofT : x ∈ G.roof (G.terminalFrontier W) :=
    DWeb.IsWave.self_roofing G hW ⟨p, hpW, hxp⟩
  apply hxNotRoofS
  simpa only [S, G.roof_essential] using hxRoofT

/-- Source Lemma 3.26 in normalized form: the quotient by the essential
terminal frontier of a forward-maximal wave is loose. -/
theorem quotient_essentialTerminalFrontier_isLoose_of_isMax
    {W : Set G.DPath} (hW : G.IsWave W)
    (hmax : IsMax (⟨W, hW⟩ : G.Wave)) :
    (G.quotient (G.essential (G.terminalFrontier W))).IsLoose := by
  intro U hU
  by_contra hne
  obtain ⟨q, hqU, hqne⟩ :=
    G.exists_nontrivial_mem_of_quotientWave_ne_trivialWave hW hU hne
  let S := G.essential (G.terminalFrontier W)
  let L := G.liftQuotientFamily S U
  let hc : G.StarCompatible W L :=
    G.starCompatible_liftQuotientFamily hW hU
  have hstarWave : G.IsWave (G.star hc) := by
    exact G.isWave_star_liftQuotientFamily hW hU
  have hforward : G.ForwardExtension W (G.star hc) :=
    G.forwardExtension_star hc
  have hback : G.ForwardExtension (G.star hc) W := by
    exact hmax (b := (⟨G.star hc, hstarWave⟩ : G.Wave)) hforward
  exact (G.not_forwardExtension_star_liftQuotientFamily_of_nontrivial
    hW hU hqU hqne) hback

/-- Source Lemma 3.26 exactly as stated in the paper: the quotient by the
full terminal frontier of a maximal wave is loose.  The normalized and full
quotients coincide because the frontier already roofs the source. -/
theorem quotient_terminalFrontier_isLoose_of_isMax
    {W : Set G.DPath} (hW : G.IsWave W)
    (hmax : IsMax (⟨W, hW⟩ : G.Wave)) :
    (G.quotient (G.terminalFrontier W)).IsLoose := by
  rw [← G.quotient_essential_eq_of_subset_roof
    (G.terminalFrontier W) hW.2.2]
  exact G.quotient_essentialTerminalFrontier_isLoose_of_isMax hW hmax

end DWeb

end Erdos599
namespace Erdos599.DirectedPath

open Function Set
universe u
variable {V : Type u} {D : Digraph V}

namespace Ray

/-- Prepend one fresh vertex and edge to a ray. -/
def prependVertex {u : V} (r : Ray D) (h : D.Adj u r.initial)
    (hu : u ∉ r.support) : Ray D where
  toFun
    | 0 => u
    | n + 1 => r n
  adj_succ n := by
    cases n with
    | zero => exact h
    | succ n => simpa [Nat.add_assoc] using r.adj_succ n
  injective := by
    intro m n hmn
    cases m with
    | zero =>
        cases n with
        | zero => rfl
        | succ n => exact (hu ⟨n, hmn.symm⟩).elim
    | succ m =>
        cases n with
        | zero => exact (hu ⟨m, hmn⟩).elim
        | succ n => exact congrArg Nat.succ (r.injective hmn)

@[simp] theorem prependVertex_apply_zero {u : V} (r : Ray D)
    (h : D.Adj u r.initial) (hu) : r.prependVertex h hu 0 = u := rfl

@[simp] theorem prependVertex_apply_succ {u : V} (r : Ray D)
    (h : D.Adj u r.initial) (hu) (n : ℕ) :
    r.prependVertex h hu (n + 1) = r n := rfl

@[simp] theorem initial_prependVertex {u : V} (r : Ray D)
    (h : D.Adj u r.initial) (hu) : (r.prependVertex h hu).initial = u := rfl

@[simp] theorem support_prependVertex {u : V} (r : Ray D)
    (h : D.Adj u r.initial) (hu) :
    (r.prependVertex h hu).support = insert u r.support := by
  ext x
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => exact Or.inl hn.symm
    | succ n => exact Or.inr ⟨n, hn⟩
  · rintro (rfl | ⟨n, rfl⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨n + 1, rfl⟩

/-- Select the tail of a ray beginning at a specified support vertex. -/
noncomputable def suffixFrom (r : Ray D) (x : V) (hx : x ∈ r.support) : Ray D :=
  r.tail (Classical.choose hx)

@[simp] theorem initial_suffixFrom (r : Ray D) (x : V) (hx : x ∈ r.support) :
    (r.suffixFrom x hx).initial = x := by
  rw [suffixFrom, initial_tail]
  exact Classical.choose_spec hx

theorem support_suffixFrom_subset (r : Ray D) (x : V) (hx : x ∈ r.support) :
    (r.suffixFrom x hx).support ⊆ r.support :=
  r.support_tail_subset _

end Ray

namespace Walk

/-- Vertices of a finite walk before its final vertex. -/
def front {a b : V} (p : Walk D a b) : Set V :=
  {x | x ∈ p.support.dropLast}

@[simp] theorem front_nil (x : V) : front (.nil : Walk D x x) = ∅ := by
  ext y
  simp [front]

@[simp] theorem front_cons {a b c : V} (h : D.Adj a b) (p : Walk D b c) :
    front (.cons h p) = insert a (front p) := by
  ext x
  simp [front, List.dropLast_cons_of_ne_nil p.support_ne_nil]

/-- A ray obtained by prepending all edges of `p`, with its exact initial
vertex and support recorded. -/
structure PrependedRay {a b : V} (p : Walk D a b) (r : Ray D) where
  ray : Ray D
  initial_eq : ray.initial = a
  prefix_eq : ∀ n (hn : n < p.support.length), ray n = p.support[n]
  support_eq : ray.support = {x | x ∈ p.support} ∪ r.support

/-- Prepend a simple finite walk to a ray beginning at the walk's endpoint.
The front of the walk must avoid the ray. -/
noncomputable def prependRayAux : ∀ {a b : V} (p : Walk D a b) (r : Ray D),
    p.IsPath → r.initial = b → Disjoint p.front r.support → PrependedRay p r
  | a, _, .nil, r, _, hinit, _ =>
      { ray := r
        initial_eq := hinit
        prefix_eq := by
          intro n hn
          have hn0 : n = 0 := by simpa using hn
          subst n
          simpa [Ray.initial] using hinit
        support_eq := by
          have ha : a ∈ r.support := hinit ▸ r.initial_mem_support
          ext x
          simp only [support_nil, List.mem_singleton, Set.mem_union, Set.mem_setOf_eq]
          constructor
          · exact fun hx ↦ Or.inr hx
          · rintro (rfl | hx)
            · exact ha
            · exact hx }
  | a, b, .cons h p, r, hpath, hinit, hdis => by
      have hpath' : p.IsPath := by
        exact (List.nodup_cons.mp hpath).2
      have hdis' : Disjoint p.front r.support := by
        exact hdis.mono (by simp) Set.Subset.rfl
      let R := prependRayAux p r hpath' hinit hdis'
      have ha_not_p : a ∉ p.support := (List.nodup_cons.mp hpath).1
      have ha_not_r : a ∉ r.support := by
        intro har
        exact Set.disjoint_left.1 hdis (by simp) har
      have ha_not_R : a ∉ R.ray.support := by
        rw [R.support_eq]
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or]
        exact ⟨ha_not_p, ha_not_r⟩
      have h' : D.Adj a R.ray.initial := by simpa [R.initial_eq] using h
      exact
        { ray := R.ray.prependVertex h' ha_not_R
          initial_eq := by simp
          prefix_eq := by
            intro n hn
            cases n with
            | zero => rfl
            | succ n =>
                have hn' : n < p.support.length := by simpa using hn
                simpa using R.prefix_eq n hn'
          support_eq := by
            rw [Ray.support_prependVertex, R.support_eq]
            ext x
            simp only [Ray.support_prependVertex, Set.mem_insert_iff, Set.mem_union,
              Set.mem_setOf_eq, Walk.support_cons, List.mem_cons]
            constructor
            · rintro (hxa | hxp | hxr)
              · exact Or.inl (Or.inl hxa)
              · exact Or.inl (Or.inr hxp)
              · exact Or.inr hxr
            · rintro ((hxa | hxp) | hxr)
              · exact Or.inl hxa
              · exact Or.inr (Or.inl hxp)
              · exact Or.inr (Or.inr hxr) }

end Walk

namespace FinitePath

/-- A support occurrence determines a suffix walk with the requested
endpoint type. -/
theorem exists_walk_suffix {a b : V} (p : Walk D a b) (x : V)
    (hx : x ∈ p.support) :
    ∃ w : Walk D x b, w.support <:+ p.support := by
  induction p generalizing x with
  | nil =>
      simp only [Walk.support_nil, List.mem_singleton] at hx
      subst x
      exact ⟨.nil, List.suffix_rfl⟩
  | @cons a c b h p ih =>
      simp only [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨.cons h p, List.suffix_rfl⟩
      · obtain ⟨w, hw⟩ := ih x hx
        exact ⟨w, hw.trans (by simpa using List.suffix_cons a p.support)⟩

/-- Exact-endpoint data for the suffix of a finite path beginning at a
specified support vertex. -/
structure SuffixData (q : FinitePath D) (x : V) where
  walk : Walk D x q.finish
  isPath : walk.IsPath
  support_subset : {y | y ∈ walk.support} ⊆ q.support

noncomputable def suffixData (q : FinitePath D) (x : V) (hx : x ∈ q.support) :
    SuffixData q x := by
  change x ∈ q.walk.support at hx
  let w := Classical.choose (exists_walk_suffix q.walk x hx)
  have hw : w.support <:+ q.walk.support :=
    Classical.choose_spec (exists_walk_suffix q.walk x hx)
  exact
    { walk := w
      isPath := hw.nodup q.isPath
      support_subset := hw.subset }

/-- The suffix of a finite path beginning at a specified support vertex. -/
noncomputable def suffixFromAux (q : FinitePath D) (x : V) (hx : x ∈ q.support) :
    FinitePath D where
  start := x
  finish := q.finish
  walk := (q.suffixData x hx).walk
  isPath := (q.suffixData x hx).isPath

@[simp] theorem suffixFromAux_start (q : FinitePath D) (x : V) (hx : x ∈ q.support) :
    (q.suffixFromAux x hx).start = x := rfl

@[simp] theorem suffixFromAux_finish (q : FinitePath D) (x : V) (hx : x ∈ q.support) :
    (q.suffixFromAux x hx).finish = q.finish := rfl

theorem suffixFromAux_support_subset (q : FinitePath D) (x : V) (hx : x ∈ q.support) :
    (q.suffixFromAux x hx).support ⊆ q.support :=
  (q.suffixData x hx).support_subset

/-- Append a finite suffix whose first vertex is `p.finish`. -/
noncomputable def appendSuffix (p q : FinitePath D) (hx : p.finish ∈ q.support)
    (hdis : p.walk.support.Disjoint (q.suffixData p.finish hx).walk.support.tail) :
    FinitePath D :=
  p.appendWalkOfDisjoint (q.suffixData p.finish hx).walk
    (q.suffixData p.finish hx).isPath hdis

@[simp] theorem appendSuffix_start (p q : FinitePath D) (hx : p.finish ∈ q.support)
    (hdis) : (p.appendSuffix q hx hdis).start = p.start := rfl

@[simp] theorem appendSuffix_finish (p q : FinitePath D) (hx : p.finish ∈ q.support)
    (hdis) : (p.appendSuffix q hx hdis).finish = q.finish := rfl

/-- The append has precisely the old support together with the selected suffix. -/
theorem support_appendSuffix (p q : FinitePath D) (hx : p.finish ∈ q.support)
    (hdis) :
    (p.appendSuffix q hx hdis).support =
      p.support ∪ {x | x ∈ (q.suffixData p.finish hx).walk.support} := by
  ext x
  change x ∈ (p.walk.append (q.suffixData p.finish hx).walk).support ↔
    x ∈ p.walk.support ∨ x ∈ (q.suffixData p.finish hx).walk.support
  rw [Walk.support_append]
  constructor
  · intro h
    simp only [List.mem_append] at h
    exact h.elim Or.inl (fun ht ↦ Or.inr (List.mem_of_mem_tail ht))
  · rintro (hp | hs)
    · exact List.mem_append_left _ hp
    · by_cases ht : x ∈ (q.suffixData p.finish hx).walk.support.tail
      · exact List.mem_append_right _ ht
      · have hxstart : x = p.finish := by
          let l := (q.suffixData p.finish hx).walk.support
          have hl : l ≠ [] := (q.suffixData p.finish hx).walk.support_ne_nil
          have hhead : l.head hl = p.finish :=
            (q.suffixData p.finish hx).walk.head_support
          have hxhead : x = l.head hl := by
            obtain ⟨a, t, hlst⟩ := List.exists_cons_of_ne_nil hl
            have hs' : x = a ∨ x ∈ t := by simpa [l, hlst] using hs
            have ht' : x ∉ t := by simpa [l, hlst] using ht
            have hxa : x = a := hs'.resolve_right ht'
            calc
              x = a := hxa
              _ = l.head hl := by simp [hlst]
          exact hxhead.trans hhead
        subst x
        exact List.mem_append_left _ p.walk.end_mem_support

/-- Append a ray suffix beginning at `p.finish`. -/
noncomputable def appendRaySuffix (p : FinitePath D) (r : Ray D)
    (hx : p.finish ∈ r.support)
    (hdis : Disjoint p.walk.front (r.suffixFrom p.finish hx).support) : Ray D :=
  (p.walk.prependRayAux (r.suffixFrom p.finish hx) p.isPath
    (r.initial_suffixFrom p.finish hx) hdis).ray

@[simp] theorem initial_appendRaySuffix (p : FinitePath D) (r : Ray D)
    (hx : p.finish ∈ r.support) (hdis) :
    (p.appendRaySuffix r hx hdis).initial = p.start :=
  (p.walk.prependRayAux (r.suffixFrom p.finish hx) p.isPath
    (r.initial_suffixFrom p.finish hx) hdis).initial_eq

theorem support_appendRaySuffix (p : FinitePath D) (r : Ray D)
    (hx : p.finish ∈ r.support) (hdis) :
    (p.appendRaySuffix r hx hdis).support =
      p.support ∪ (r.suffixFrom p.finish hx).support := by
  exact (p.walk.prependRayAux (r.suffixFrom p.finish hx) p.isPath
    (r.initial_suffixFrom p.finish hx) hdis).support_eq

end FinitePath


namespace Walk

/-- In a simple walk, the initial vertex does not occur in the tail. -/
theorem start_not_mem_tail {a b : V} (p : Walk D a b) (hp : p.IsPath) :
    a ∉ p.support.tail := by
  cases p with
  | nil => simp
  | cons h p =>
      exact (List.nodup_cons.mp hp).1

/-- In a simple walk, the final vertex does not occur before the end. -/
theorem end_not_mem_front {a b : V} (p : Walk D a b) (hp : p.IsPath) :
    b ∉ p.front := by
  intro hb
  have hn : (p.support.dropLast ++ [p.support.getLast p.support_ne_nil]).Nodup := by
    rw [List.dropLast_append_getLast]
    exact hp
  have hd := (List.nodup_append.mp hn).2.2
  have hne : b ≠ p.support.getLast p.support_ne_nil :=
    hd b hb (p.support.getLast p.support_ne_nil) (by simp)
  exact hne p.getLast_support.symm

end Walk

namespace Path

/-- Select the suffix of a finite path or ray beginning at a support vertex. -/
noncomputable def suffixFrom (q : Path D) (x : V) (hx : x ∈ q.support) : Path D :=
  match q with
  | .inl f => .inl (f.suffixFromAux x hx)
  | .inr r => .inr (r.suffixFrom x hx)

@[simp] theorem terminal?_suffixFrom (q : Path D) (x : V) (hx : x ∈ q.support) :
    (q.suffixFrom x hx).terminal? = q.terminal? := by
  rcases q with q | r <;> rfl

/-- The suffix remains inside the original path. -/
theorem support_suffixFrom_subset (q : Path D) (x : V) (hx : x ∈ q.support) :
    (q.suffixFrom x hx).support ⊆ q.support := by
  rcases q with q | r
  · exact q.suffixFromAux_support_subset x hx
  · exact r.support_suffixFrom_subset x hx

/-- The exact disjointness condition for splicing at `p.finish`: all vertices
of the selected suffix after the common splice vertex avoid `p`. -/
def Appendable (p : FinitePath D) (q : Path D) (hx : p.finish ∈ q.support) : Prop :=
  Disjoint p.support ((q.suffixFrom p.finish hx).support \ {p.finish})

end Path

namespace FinitePath

/-- Convert the set-level appendability condition into the list-level
condition used by finite walk concatenation. -/
theorem disjoint_tail_of_appendableFinite (p q : FinitePath D)
    (hx : p.finish ∈ Path.support (.inl q : Path D))
    (h : Path.Appendable p (.inl q) hx) :
    p.walk.support.Disjoint (q.suffixData p.finish hx).walk.support.tail := by
  apply List.disjoint_left.2
  intro x hxp hxs
  have hxne : x ≠ p.finish := by
    intro hxeq
    subst x
    exact (q.suffixData p.finish hx).walk.start_not_mem_tail
      (q.suffixData p.finish hx).isPath hxs
  exact Set.disjoint_left.1 h hxp ⟨List.mem_of_mem_tail hxs, hxne⟩

/-- Convert appendability into the front/ray disjointness condition used by
finite-walk-to-ray concatenation. -/
theorem disjoint_front_of_appendableRay (p : FinitePath D) (r : Ray D)
    (hx : p.finish ∈ Path.support (.inr r : Path D))
    (h : Path.Appendable p (.inr r) hx) :
    Disjoint p.walk.front (r.suffixFrom p.finish hx).support := by
  rw [Set.disjoint_left]
  intro x hxp hxr
  have hxSupport : x ∈ p.support := List.mem_of_mem_dropLast hxp
  have hxne : x ≠ p.finish := by
    intro hxeq
    subst x
    exact p.walk.end_not_mem_front p.isPath hxp
  exact Set.disjoint_left.1 h hxSupport ⟨hxr, hxne⟩

end FinitePath

namespace Path

/-- Splice a finite path onto the suffix of a finite path or ray. -/
noncomputable def appendAt (p : FinitePath D) (q : Path D)
    (hx : p.finish ∈ q.support) (h : Appendable p q hx) : Path D :=
  match q with
  | .inl f =>
      .inl (p.appendSuffix f hx (p.disjoint_tail_of_appendableFinite f hx h))
  | .inr r =>
      .inr (p.appendRaySuffix r hx (p.disjoint_front_of_appendableRay r hx h))

/-- Splicing preserves the original finite path as an initial segment. -/
theorem extends_appendAt (p : FinitePath D) (q : Path D)
    (hx : p.finish ∈ q.support) (h : Appendable p q hx) :
    Extends (.inl p) (appendAt p q hx h) := by
  rcases q with f | r
  · change p.IsPrefixOf
      (p.appendSuffix f hx (p.disjoint_tail_of_appendableFinite f hx h))
    change p.walk.support <+:
      (p.walk.append (f.suffixData p.finish hx).walk).support
    rw [Walk.support_append]
    exact List.prefix_append _ _
  · intro n hn
    exact (p.walk.prependRayAux (r.suffixFrom p.finish hx) p.isPath
      (r.initial_suffixFrom p.finish hx)
      (p.disjoint_front_of_appendableRay r hx h)).prefix_eq n hn |>.symm

/-- The splice support is exactly the old support plus the chosen suffix. -/
theorem support_appendAt (p : FinitePath D) (q : Path D)
    (hx : p.finish ∈ q.support) (h : Appendable p q hx) :
    (appendAt p q hx h).support = p.support ∪ (q.suffixFrom p.finish hx).support := by
  rcases q with f | r
  · exact p.support_appendSuffix f hx _
  · exact p.support_appendRaySuffix r hx _

/-- A splice inherits finiteness and terminal vertex from the second path. -/
@[simp] theorem terminal?_appendAt (p : FinitePath D) (q : Path D)
    (hx : p.finish ∈ q.support) (h : Appendable p q hx) :
    (appendAt p q hx h).terminal? = q.terminal? := by
  rcases q with f | r <;> rfl

end Path

end Erdos599.DirectedPath

namespace Erdos599
open Set DirectedPath
universe u

namespace List

/-- Suffixes of the same list are linearly ordered by the suffix relation. -/
theorem suffix_total {α : Type*} {a b l : List α}
    (ha : a <:+ l) (hb : b <:+ l) : a <:+ b ∨ b <:+ a := by
  wlog hlen : a.length ≤ b.length generalizing a b
  · exact Or.symm (this hb ha (Nat.le_of_not_ge hlen))
  · apply Or.inl
    have har := ha.reverse
    have hbr := hb.reverse
    rw [List.prefix_iff_eq_take] at har hbr
    apply List.reverse_prefix.mp
    rw [List.prefix_iff_eq_take]
    rw [List.length_reverse] at har hbr ⊢
    rw [har, hbr, List.take_take, Nat.min_eq_left hlen]

end List

namespace DirectedPath
variable {V : Type u} {D : Digraph V}

namespace FinitePath

theorem suffixData_support_suffix (q : FinitePath D) (x : V) (hx : x ∈ q.support) :
    (q.suffixData x hx).walk.support <:+ q.walk.support := by
  change (Classical.choose (exists_walk_suffix q.walk x hx)).support <:+ q.walk.support
  exact Classical.choose_spec (exists_walk_suffix q.walk x hx)

end FinitePath

namespace Path

/-- On one simple path, either selected suffix contains the other's start. -/
theorem start_mem_suffixFrom_or_start_mem_suffixFrom (q : Path D)
    {a b : V} (ha : a ∈ q.support) (hb : b ∈ q.support) :
    a ∈ (q.suffixFrom b hb).support ∨ b ∈ (q.suffixFrom a ha).support := by
  rcases q with q | r
  · have hs := List.suffix_total (q.suffixData_support_suffix a ha)
        (q.suffixData_support_suffix b hb)
    rcases hs with hab | hba
    · left
      change a ∈ (q.suffixData b hb).walk.support
      exact hab.subset (q.suffixData a ha).walk.start_mem_support
    · right
      change b ∈ (q.suffixData a ha).walk.support
      exact hba.subset (q.suffixData b hb).walk.start_mem_support
  · let m := Classical.choose ha
    have hm : r m = a := Classical.choose_spec ha
    let n := Classical.choose hb
    have hn : r n = b := Classical.choose_spec hb
    by_cases hmn : m ≤ n
    · right
      refine ⟨n - m, ?_⟩
      simp only [suffixFrom, Ray.suffixFrom, Ray.tail_apply]
      dsimp only [m, n]
      rw [Nat.add_sub_of_le hmn, hn]
    · left
      have hnm : n ≤ m := Nat.le_of_not_ge hmn
      refine ⟨m - n, ?_⟩
      simp only [suffixFrom, Ray.suffixFrom, Ray.tail_apply]
      dsimp only [m, n]
      rw [Nat.add_sub_of_le hnm, hm]

end Path
end DirectedPath

namespace DWeb
variable {V : Type u} (G : DWeb V)

/-- A W-path whose suffix from the terminal of `p` has no further U vertex. -/
structure ArrowCandidate (U W : Set G.DPath) (p : FinitePath G.graph) where
  path : G.DPath
  mem_path : path ∈ W
  finish_mem : p.finish ∈ path.support
  clean : (path.suffixFrom p.finish finish_mem).support ∩ G.vertexSet U = {p.finish}

namespace ArrowCandidate

variable {G} {U W : Set G.DPath} {p : FinitePath G.graph}

theorem appendable (c : G.ArrowCandidate U W p) (hp : (Sum.inl p : G.DPath) ∈ U) :
    DirectedPath.Path.Appendable p c.path c.finish_mem := by
  rw [DirectedPath.Path.Appendable, Set.disjoint_left]
  intro x hxp hxs
  have hxU : x ∈ G.vertexSet U := ⟨.inl p, hp, hxp⟩
  have hxi : x ∈ (c.path.suffixFrom p.finish c.finish_mem).support ∩
      G.vertexSet U := ⟨hxs.1, hxU⟩
  have hxeq : x = p.finish := by
    have : x ∈ ({p.finish} : Set V) := c.clean ▸ hxi
    simpa using this
  exact hxs.2 hxeq

end ArrowCandidate

/-- Chosen source arrow image of one path of `U`. Rays and finite paths
without a clean `W` suffix are unchanged. -/
noncomputable def arrowFinite (U W : Set G.DPath) (f : FinitePath G.graph)
    (hf : (Sum.inl f : G.DPath) ∈ U) : G.DPath := by
  classical
  exact if h : Nonempty (G.ArrowCandidate U W f) then
    let c := Classical.choice h
    DirectedPath.Path.appendAt f c.path c.finish_mem (c.appendable hf)
  else .inl f

noncomputable def arrowPath (U W : Set G.DPath) : U → G.DPath
  | ⟨.inl f, hf⟩ => G.arrowFinite U W f hf
  | ⟨.inr r, _⟩ => .inr r

/-- The source arrow family. -/
noncomputable def arrow (U W : Set G.DPath) : Set G.DPath :=
  Set.range (G.arrowPath U W)


@[simp] theorem arrowPath_ray (U W : Set G.DPath) (r : Ray G.graph)
    (hr : (Sum.inr r : G.DPath) ∈ U) :
    G.arrowPath U W ⟨.inr r, hr⟩ = .inr r := by
  simp [arrowPath]

theorem arrowPath_finite_cases (U W : Set G.DPath) (f : FinitePath G.graph)
    (hf : (Sum.inl f : G.DPath) ∈ U) :
    G.arrowPath U W ⟨.inl f, hf⟩ = .inl f ∨
      ∃ c : G.ArrowCandidate U W f,
        G.arrowPath U W ⟨.inl f, hf⟩ =
          DirectedPath.Path.appendAt f c.path c.finish_mem (c.appendable hf) := by
  classical
  change G.arrowFinite U W f hf = .inl f ∨ _
  rw [arrowFinite]
  split
  next h =>
    refine Or.inr ⟨Classical.choice h, ?_⟩
    simp [arrowPath, arrowFinite, h]
  next h => exact Or.inl rfl

theorem arrowPath_extends (U W : Set G.DPath) (p : U) :
    G.Extends p.1 (G.arrowPath U W p) := by
  rcases hp : p.1 with f | r
  · have hf : (Sum.inl f : G.DPath) ∈ U := by simpa [hp] using p.2
    have peq : p = ⟨.inl f, hf⟩ := Subtype.ext hp
    subst p
    rcases G.arrowPath_finite_cases U W f hf with h | ⟨c, h⟩
    · rw [h]
      exact G.extends_refl _
    · rw [h]
      exact DirectedPath.Path.extends_appendAt f c.path c.finish_mem (c.appendable hf)
  · have hr : (Sum.inr r : G.DPath) ∈ U := by simpa [hp] using p.2
    have peq : p = ⟨.inr r, hr⟩ := Subtype.ext hp
    subst p
    rw [G.arrowPath_ray U W r hr]
    exact G.extends_refl _

@[simp] theorem arrowPath_initial (U W : Set G.DPath) (p : U) :
    (G.arrowPath U W p).initial = p.1.initial :=
  (G.extends_initial (G.arrowPath_extends U W p)).symm

/-- An arrow image meets the old warp exactly in its original path. -/
theorem support_arrowPath_inter_vertexSet (hU : G.IsWarp U)
    (U W : Set G.DPath) (p : U) :
    (G.arrowPath U W p).support ∩ G.vertexSet U = p.1.support := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hp : p.1 with f | r
    · have hf : (Sum.inl f : G.DPath) ∈ U := by simpa [hp] using p.2
      have peq : p = ⟨.inl f, hf⟩ := Subtype.ext hp
      subst p
      rcases G.arrowPath_finite_cases U W f hf with heq | ⟨c, heq⟩
      · rw [heq] at hx
        exact hx.1
      · rw [heq, DirectedPath.Path.support_appendAt] at hx
        rcases hx.1 with hxf | hxs
        · exact hxf
        · have hxi : x ∈ (c.path.suffixFrom f.finish c.finish_mem).support ∩
              G.vertexSet U := ⟨hxs, hx.2⟩
          have hxfinish : x = f.finish := by
            have : x ∈ ({f.finish} : Set V) := c.clean ▸ hxi
            simpa using this
          exact hxfinish ▸ f.finish_mem_support
    · have hr : (Sum.inr r : G.DPath) ∈ U := by simpa [hp] using p.2
      have peq : p = ⟨.inr r, hr⟩ := Subtype.ext hp
      subst p
      simpa [G.arrowPath_ray U W r hr] using hx.1
  · intro x hxp
    exact ⟨G.support_mono_of_extends (G.arrowPath_extends U W p) hxp,
      ⟨p.1, p.2, hxp⟩⟩

/-- Distinct arrow images are disjoint. -/
theorem isWarp_arrow (hU : G.IsWarp U) (hW : G.IsWarp W) :
    G.IsWarp (G.arrow U W) := by
  rintro r₁ ⟨p₁, rfl⟩ r₂ ⟨p₂, rfl⟩ hr
  have hpne : p₁ ≠ p₂ := by
    intro h
    exact hr (congrArg (G.arrowPath U W) h)
  change Disjoint (G.arrowPath U W p₁).support (G.arrowPath U W p₂).support
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  by_cases hxU : x ∈ G.vertexSet U
  · have hxP₁ : x ∈ p₁.1.support := by
      rw [← G.support_arrowPath_inter_vertexSet hU U W p₁]
      exact ⟨hx₁, hxU⟩
    have hxP₂ : x ∈ p₂.1.support := by
      rw [← G.support_arrowPath_inter_vertexSet hU U W p₂]
      exact ⟨hx₂, hxU⟩
    exact Set.disjoint_left.1 (hU p₁.2 p₂.2 (fun h ↦ hpne (Subtype.ext h))) hxP₁ hxP₂
  · rcases hp₁ : p₁.1 with f₁ | ray₁
    · have hf₁ : (Sum.inl f₁ : G.DPath) ∈ U := by simpa [hp₁] using p₁.2
      have peq₁ : p₁ = ⟨.inl f₁, hf₁⟩ := Subtype.ext hp₁
      subst p₁
      rcases G.arrowPath_finite_cases U W f₁ hf₁ with heq₁ | ⟨c₁, heq₁⟩
      · apply hxU
        exact ⟨.inl f₁, hf₁, heq₁ ▸ hx₁⟩
      · have hxs₁ : x ∈ (c₁.path.suffixFrom f₁.finish c₁.finish_mem).support := by
          rw [heq₁, DirectedPath.Path.support_appendAt] at hx₁
          exact hx₁.resolve_left (fun hxf ↦ hxU ⟨.inl f₁, hf₁, hxf⟩)
        rcases hp₂ : p₂.1 with f₂ | ray₂
        · have hf₂ : (Sum.inl f₂ : G.DPath) ∈ U := by simpa [hp₂] using p₂.2
          have peq₂ : p₂ = ⟨.inl f₂, hf₂⟩ := Subtype.ext hp₂
          subst p₂
          rcases G.arrowPath_finite_cases U W f₂ hf₂ with heq₂ | ⟨c₂, heq₂⟩
          · apply hxU
            exact ⟨.inl f₂, hf₂, heq₂ ▸ hx₂⟩
          · have hxs₂ : x ∈ (c₂.path.suffixFrom f₂.finish c₂.finish_mem).support := by
              rw [heq₂, DirectedPath.Path.support_appendAt] at hx₂
              exact hx₂.resolve_left (fun hxf ↦ hxU ⟨.inl f₂, hf₂, hxf⟩)
            by_cases hc : c₁.path = c₂.path
            · have hcomp := DirectedPath.Path.start_mem_suffixFrom_or_start_mem_suffixFrom
                  c₁.path c₁.finish_mem (hc ▸ c₂.finish_mem)
              rcases hcomp with h₁₂ | h₂₁
              · have hi : f₁.finish ∈
                    (c₂.path.suffixFrom f₂.finish c₂.finish_mem).support ∩
                      G.vertexSet U := ⟨by simpa [hc] using h₁₂,
                        ⟨.inl f₁, hf₁, f₁.finish_mem_support⟩⟩
                have he : f₁.finish = f₂.finish := by
                  have : f₁.finish ∈ ({f₂.finish} : Set V) := c₂.clean ▸ hi
                  simpa using this
                exact Set.disjoint_left.1 (hU hf₁ hf₂ (fun h ↦ hpne (Subtype.ext h)))
                  f₁.finish_mem_support (he ▸ f₂.finish_mem_support)
              · have hi : f₂.finish ∈
                    (c₁.path.suffixFrom f₁.finish c₁.finish_mem).support ∩
                      G.vertexSet U := ⟨h₂₁,
                        ⟨.inl f₂, hf₂, f₂.finish_mem_support⟩⟩
                have he : f₂.finish = f₁.finish := by
                  have : f₂.finish ∈ ({f₁.finish} : Set V) := c₁.clean ▸ hi
                  simpa using this
                exact Set.disjoint_left.1 (hU hf₁ hf₂ (fun h ↦ hpne (Subtype.ext h)))
                  (he ▸ f₁.finish_mem_support) f₂.finish_mem_support
            · exact Set.disjoint_left.1 (hW c₁.mem_path c₂.mem_path hc)
                (c₁.path.support_suffixFrom_subset _ _ hxs₁)
                (c₂.path.support_suffixFrom_subset _ _ hxs₂)
        · have hr₂ : (Sum.inr ray₂ : G.DPath) ∈ U := by simpa [hp₂] using p₂.2
          have peq₂ : p₂ = ⟨.inr ray₂, hr₂⟩ := Subtype.ext hp₂
          subst p₂
          apply hxU
          exact ⟨.inr ray₂, hr₂, by simpa [G.arrowPath_ray U W ray₂ hr₂] using hx₂⟩
    · have hr₁ : (Sum.inr ray₁ : G.DPath) ∈ U := by simpa [hp₁] using p₁.2
      have peq₁ : p₁ = ⟨.inr ray₁, hr₁⟩ := Subtype.ext hp₁
      subst p₁
      apply hxU
      exact ⟨.inr ray₁, hr₁, by simpa [G.arrowPath_ray U W ray₁ hr₁] using hx₁⟩

/-- Every original path is extended by its arrow image. -/
theorem forwardExtension_arrow (U W : Set G.DPath) :
    G.ForwardExtension U (G.arrow U W) := by
  constructor
  · intro p hp
    let q : U := ⟨p, hp⟩
    exact ⟨G.arrowPath U W q, ⟨q, rfl⟩, G.arrowPath_extends U W q⟩
  · intro q hq
    obtain ⟨p, rfl⟩ := hq
    exact ⟨p.1, p.2, G.arrowPath_extends U W p⟩


/-- The arrow's terminal frontier is contained in the union of the two old
frontiers. -/
theorem terminalFrontier_arrow_subset_union (U W : Set G.DPath) :
    G.terminalFrontier (G.arrow U W) ⊆
      G.terminalFrontier U ∪ G.terminalFrontier W := by
  rintro z ⟨r, ⟨p, rfl⟩, hrz⟩
  rcases hp : p.1 with f | ray
  · have hf : (Sum.inl f : G.DPath) ∈ U := by simpa [hp] using p.2
    have peq : p = ⟨.inl f, hf⟩ := Subtype.ext hp
    subst p
    rcases G.arrowPath_finite_cases U W f hf with heq | ⟨c, heq⟩
    · exact Or.inl ⟨.inl f, hf, by simpa [heq] using hrz⟩
    · have hcTerm : c.path.terminal? = some z := by
        calc
        c.path.terminal? =
            (DirectedPath.Path.appendAt f c.path c.finish_mem (c.appendable hf)).terminal? :=
          (DirectedPath.Path.terminal?_appendAt f c.path c.finish_mem (c.appendable hf)).symm
        _ = some z := by simpa [heq] using hrz
      exact Or.inr ⟨c.path, c.mem_path, hcTerm⟩
  · have hray : (Sum.inr ray : G.DPath) ∈ U := by simpa [hp] using p.2
    have peq : p = ⟨.inr ray, hray⟩ := Subtype.ext hp
    subst p
    simp [G.arrowPath_ray U W ray hray] at hrz

/-- Two suffix walks of one simple walk which begin at the same vertex have
the same ordered support. -/
theorem suffix_support_eq_of_same_start {a b x : V}
    (q : Walk G.graph a b) (hq : q.IsPath)
    (r s : Walk G.graph x b) (hr : r.support <:+ q.support)
    (hs : s.support <:+ q.support) : r.support = s.support := by
  rcases List.suffix_total hr hs with hrs | hsr
  · exact List.Nodup.eq_of_head_mem_of_suffix (hne := s.support_ne_nil) hrs
      (by simpa using r.start_mem_support) (hs.nodup hq)
  · exact (List.Nodup.eq_of_head_mem_of_suffix (hne := r.support_ne_nil) hsr
      (by simpa using s.start_mem_support) (hr.nodup hq)).symm

/-- If a finite W-path ending at `z` has an A-avoiding continuation to the
target, then its last U-terminal supplies a clean arrow candidate ending at
`z`. -/
theorem exists_arrow_candidate_ending
    {U W : Set G.DPath} (hU : G.IsWave U)
    {q : FinitePath G.graph} (hqW : (Sum.inl q : G.DPath) ∈ W)
    (hqSource : q.start ∈ G.source)
    {r : FinitePath G.graph} (hrStart : r.start = q.finish)
    (hrTarget : r.finish ∈ G.target)
    (hrAvoid : G.Avoids r (G.terminalFrontier U)) :
    ∃ f : FinitePath G.graph, ∃ hfU : (Sum.inl f : G.DPath) ∈ U,
      ∃ c : G.ArrowCandidate U W f,
        c.path = (.inl q : G.DPath) ∧
        (DirectedPath.Path.appendAt f c.path c.finish_mem (c.appendable hfU)).terminal? =
          some q.finish := by
  let rwlk : Walk G.graph q.finish r.finish :=
    RelationalRoof.castStart G.graph.Adj hrStart r.walk
  let whole := q.walk.append rwlk
  have hmeet : whole.Meets (G.terminalFrontier U) :=
    RelationalRoof.roof_meets_walk G.graph.Adj G.target (hU.2.2 hqSource) whole hrTarget
  have hqmeet : q.walk.Meets (G.terminalFrontier U) := by
    obtain ⟨z, hzwhole, hzU⟩ := hmeet
    rw [Walk.support_append] at hzwhole
    rcases List.mem_append.mp hzwhole with hzq | hzr
    · exact ⟨z, hzq, hzU⟩
    · exfalso
      apply Set.disjoint_left.1 hrAvoid
      · change z ∈ r.walk.support
        simpa [rwlk, RelationalRoof.support_castStart] using List.mem_of_mem_tail hzr
      · exact hzU
  let L := q.walk.lastHit (G.terminalFrontier U) hqmeet
  obtain ⟨up, hupU, hupTerm⟩ := L.startpoint_mem
  rcases up with f | ray
  · have hfinish : f.finish = L.startpoint := Option.some.inj hupTerm
    let sf := q.suffixData L.startpoint (L.support_subset L.walk.start_mem_support)
    have hsfL : sf.walk.support = L.walk.support := by
      apply G.suffix_support_eq_of_same_start q.walk q.isPath
      · exact q.suffixData_support_suffix _ _
      · exact L.support_suffix
    have hclean :
        (DirectedPath.Path.suffixFrom (Sum.inl q : DirectedPath.Path G.graph)
          L.startpoint (L.support_subset L.walk.start_mem_support)).support ∩ G.vertexSet U =
          {L.startpoint} := by
      ext x
      constructor
      · rintro ⟨hxs, hxU⟩
        change x ∈ sf.walk.support at hxs
        rw [hsfL] at hxs
        rcases RelationalRoof.mem_support_iff_start_or_mem_tail G.graph.Adj L.walk |>.1 hxs with hxeq | hxtail
        · simpa [hxeq]
        · exfalso
          obtain ⟨v, hvU, hxv⟩ := hxU
          have hxRoof : x ∈ G.roof (G.terminalFrontier U) :=
            (DWeb.IsWave.self_roofing (Γ := G) hU) ⟨v, hvU, hxv⟩
          let X := L.walk.lastHit ({x} : Set V)
            ⟨x, hxs, by simp⟩
          have hXstart : X.startpoint = x := by simpa using X.startpoint_mem
          let xwalk : Walk G.graph x r.finish :=
            (RelationalRoof.castStart G.graph.Adj hXstart X.walk).append rwlk
          have hxwalkAvoid : ∀ {y}, y ∈ xwalk.support →
              y ∉ G.terminalFrontier U := by
            intro y hy hyA
            dsimp only [xwalk] at hy
            rw [Walk.support_append] at hy
            rcases List.mem_append.mp hy with hyX | hyr
            · have hyL : y ∈ L.walk.support := X.support_subset (by
                simpa [RelationalRoof.support_castStart] using hyX)
              rcases RelationalRoof.mem_support_iff_start_or_mem_tail G.graph.Adj L.walk |>.1 hyL with hyeq | hytail
              · have hxEq : x = L.startpoint := by
                  have hLXin : L.startpoint ∈ X.walk.support := by
                    have hyX' : y ∈ X.walk.support := by
                      simpa [RelationalRoof.support_castStart] using hyX
                    simpa [hyeq] using hyX'
                  have heqSupports : X.walk.support = L.walk.support :=
                    List.Nodup.eq_of_head_mem_of_suffix
                      (hne := L.walk.support_ne_nil) X.support_suffix
                      (by simpa using hLXin) (L.isPath q.isPath)
                  have := congrArg (fun l => l[0]?) heqSupports
                  have hheads : X.startpoint = L.startpoint := by
                    rw [RelationalRoof.getElem?_zero_support G.graph.Adj X.walk,
                      RelationalRoof.getElem?_zero_support G.graph.Adj L.walk] at this
                    exact Option.some.inj this
                  exact hXstart.symm.trans hheads
                exact (L.no_mem_after (hxEq ▸ hxtail)) L.startpoint_mem
              · exact L.no_mem_after hytail hyA
            · exact Set.disjoint_left.1 hrAvoid
                (by
                  change y ∈ r.walk.support
                  simpa [rwlk, RelationalRoof.support_castStart] using
                    List.mem_of_mem_tail hyr) hyA
          obtain ⟨y, hy, hyA⟩ :=
            RelationalRoof.roof_meets_walk G.graph.Adj G.target hxRoof xwalk hrTarget
          exact hxwalkAvoid hy hyA
      · intro hx
        have hxeq : x = L.startpoint := by simpa using hx
        subst x
        exact ⟨by
          change L.startpoint ∈ sf.walk.support
          rw [hsfL]
          exact L.walk.start_mem_support,
          ⟨.inl f, hupU, by
            change L.startpoint ∈ f.support
            simpa [hfinish] using f.finish_mem_support⟩⟩
    have hfU : (Sum.inl f : G.DPath) ∈ U := hupU
    have hfinishMem : f.finish ∈ (Path.support (.inl q : G.DPath)) := by
      rw [hfinish]
      exact L.support_subset L.walk.start_mem_support
    let c : G.ArrowCandidate U W f :=
      { path := .inl q
        mem_path := hqW
        finish_mem := hfinishMem
        clean := by simpa [hfinish] using hclean }
    refine ⟨f, hfU, c, rfl, ?_⟩
    rw [DirectedPath.Path.terminal?_appendAt]
    rfl
  · simp at hupTerm

/-- All clean candidates for the same old finite path use the same member of
the second warp. -/
theorem ArrowCandidate.path_eq {U W : Set G.DPath} {f : FinitePath G.graph}
    (hW : G.IsWarp W) (c d : G.ArrowCandidate U W f) : c.path = d.path := by
  by_contra hne
  exact Set.disjoint_left.1 (hW c.mem_path d.mem_path hne)
    c.finish_mem d.finish_mem

/-- A clean candidate with finite terminal `z` forces the chosen arrow image
to have the same terminal. -/
theorem terminal_arrowPath_of_candidate {U W : Set G.DPath}
    (hW : G.IsWarp W) {f : FinitePath G.graph}
    (hf : (Sum.inl f : G.DPath) ∈ U) (c : G.ArrowCandidate U W f)
    {z : V} (hc : c.path.terminal? = some z) :
    (G.arrowPath U W ⟨.inl f, hf⟩).terminal? = some z := by
  classical
  change (G.arrowFinite U W f hf).terminal? = some z
  rw [arrowFinite, dif_pos ⟨c⟩]
  let d := Classical.choice (show Nonempty (G.ArrowCandidate U W f) from ⟨c⟩)
  rw [DirectedPath.Path.terminal?_appendAt]
  rw [ArrowCandidate.path_eq (G := G) hW d c]
  exact hc

/-- Every essential point of the union of the two old terminal frontiers is
a terminal of the concrete arrow.  This is the content of source Lemmas
3.12--3.17 needed for the common-upper construction. -/
theorem essential_union_subset_terminalFrontier_arrow
    {U W : Set G.DPath} (hU : G.IsWave U) (hW : G.IsWave W) :
    G.essential (G.terminalFrontier U ∪ G.terminalFrontier W) ⊆
      G.terminalFrontier (G.arrow U W) := by
  intro z hzEss
  let A := G.terminalFrontier U
  let B := G.terminalFrontier W
  simp only [DWeb.essential] at hzEss
  replace hzEss : z ∈ A ∪ B ∧ z ∉ G.roof ((A ∪ B) \ {z}) := by
    simpa [A, B] using hzEss
  have hzOld : z ∈ A ∪ B := hzEss.1
  have of_mem_A : z ∈ A → z ∈ G.terminalFrontier (G.arrow U W) := by
    intro hzA
    obtain ⟨p, hpU, hpTerm⟩ := hzA
    rcases p with f | ray
    · have hfFinish : f.finish = z := Option.some.inj hpTerm
      rcases G.arrowPath_finite_cases U W f hpU with heq | ⟨c, heq⟩
      · exact ⟨G.arrowPath U W ⟨.inl f, hpU⟩, ⟨⟨.inl f, hpU⟩, rfl⟩,
          by simpa [heq] using hpTerm⟩
      · by_cases hzB : z ∈ B
        · obtain ⟨q, hqW, hqTerm⟩ := hzB
          have hcq : c.path = q := by
            by_contra hne
            exact Set.disjoint_left.1 (hW.1 c.mem_path hqW hne)
              (hfFinish ▸ c.finish_mem) (G.terminal_mem_support hqTerm)
          have hcTerm : c.path.terminal? = some z := hcq ▸ hqTerm
          exact ⟨G.arrowPath U W ⟨.inl f, hpU⟩, ⟨⟨.inl f, hpU⟩, rfl⟩,
            G.terminal_arrowPath_of_candidate hW.1 hpU c hcTerm⟩
        · exfalso
          have hzRoofB : z ∈ G.roof B :=
            (DWeb.IsWave.self_roofing (Γ := G) hW)
              ⟨c.path, c.mem_path, hfFinish ▸ c.finish_mem⟩
          have hsub : B ⊆ (A ∪ B) \ {z} := by
            intro x hxB
            exact ⟨Or.inr hxB, by
              intro hxz
              have : x = z := by simpa using hxz
              exact hzB (this ▸ hxB)⟩
          exact hzEss.2 (G.roof_mono hsub hzRoofB)
    · simp at hpTerm
  rcases hzOld with hzA | hzB
  · exact of_mem_A hzA
  · by_cases hzA : z ∈ A
    · exact of_mem_A hzA
    · obtain ⟨q, hqW, hqTerm⟩ := hzB
      rcases q with q | ray
      · have hqFinish : q.finish = z := Option.some.inj hqTerm
        have hqSource : q.start ∈ G.source := hW.2.1 ⟨.inl q, hqW, rfl⟩
        obtain ⟨r, hrTarget, hrAvoid⟩ :=
          (G.not_mem_roof_iff ((A ∪ B) \ {z}) z).1 hzEss.2
        have hrStart : r.start = q.finish := hrTarget.1.trans hqFinish.symm
        have hrAvoidA : G.Avoids r A := by
          change Disjoint r.support A
          change Disjoint r.support ((A ∪ B) \ {z}) at hrAvoid
          rw [Set.disjoint_left] at hrAvoid ⊢
          intro x hxr hxA
          apply hrAvoid hxr
          exact ⟨Or.inl hxA, by
            intro hxz
            have : x = z := by simpa using hxz
            exact hzA (this ▸ hxA)⟩
        obtain ⟨f, hfU, c, hcPath, _⟩ :=
          G.exists_arrow_candidate_ending hU hqW hqSource hrStart
            hrTarget.2 hrAvoidA
        have hcTerm : c.path.terminal? = some z := by
          rw [hcPath]
          exact hqTerm
        exact ⟨G.arrowPath U W ⟨.inl f, hfU⟩, ⟨⟨.inl f, hfU⟩, rfl⟩,
          G.terminal_arrowPath_of_candidate hW.1 hfU c hcTerm⟩
      · simp at hqTerm

/-- The arrow frontier and the union of the two old frontiers have the same
essential part. -/
theorem essential_terminalFrontier_arrow_eq_union
    {U W : Set G.DPath} (hU : G.IsWave U) (hW : G.IsWave W) :
    G.essential (G.terminalFrontier (G.arrow U W)) =
      G.essential (G.terminalFrontier U ∪ G.terminalFrontier W) := by
  exact RelationalRoof.essential_sandwich G.graph.Adj G.target
    (G.essential_union_subset_terminalFrontier_arrow hU hW)
    (G.terminalFrontier_arrow_subset_union U W)

/-- The arrow frontier roofs exactly the union of the two old frontiers. -/
theorem roof_terminalFrontier_arrow_eq_union
    {U W : Set G.DPath} (hU : G.IsWave U) (hW : G.IsWave W) :
    G.roof (G.terminalFrontier (G.arrow U W)) =
      G.roof (G.terminalFrontier U ∪ G.terminalFrontier W) := by
  calc
    G.roof (G.terminalFrontier (G.arrow U W)) =
        G.roof (G.essential (G.terminalFrontier (G.arrow U W))) :=
      (G.roof_essential _).symm
    _ = G.roof (G.essential
        (G.terminalFrontier U ∪ G.terminalFrontier W)) :=
      congrArg G.roof (G.essential_terminalFrontier_arrow_eq_union hU hW)
    _ = G.roof (G.terminalFrontier U ∪ G.terminalFrontier W) :=
      G.roof_essential _

/-- The concrete source arrow of two waves is itself a wave. -/
theorem isWave_arrow {U W : Set G.DPath}
    (hU : G.IsWave U) (hW : G.IsWave W) : G.IsWave (G.arrow U W) := by
  have hforward := G.forwardExtension_arrow U W
  have hroof := G.roof_terminalFrontier_arrow_eq_union hU hW
  refine ⟨G.isWarp_arrow hU.1 hW.1, ?_, ?_⟩
  · rw [← G.initialSet_eq_of_forwardExtension hforward]
    exact hU.2.1
  · rw [hroof]
    exact hU.2.2.trans (G.roof_mono Set.subset_union_left)

/-- The second wave lies below the arrow in the roof order. -/
theorem roofLE_arrow_right {U W : Set G.DPath}
    (hU : G.IsWave U) (hW : G.IsWave W) : G.RoofLE W (G.arrow U W) := by
  change G.roof (G.terminalFrontier W) ⊆
    G.roof (G.terminalFrontier (G.arrow U W))
  rw [G.roof_terminalFrontier_arrow_eq_union hU hW]
  exact G.roof_mono Set.subset_union_right

/-- The source-arrow common upper bound: it extends the first wave pathwise
and dominates the second wave in the roof order. -/
theorem exists_forwardExtension_roofLE (U W : G.Wave) :
    ∃ R : G.Wave, G.ForwardExtension U R ∧ G.RoofLE W R := by
  let R : G.Wave :=
    ⟨G.arrow U.1 W.1, G.isWave_arrow U.2 W.2⟩
  exact ⟨R, G.forwardExtension_arrow U.1 W.1,
    G.roofLE_arrow_right U.2 W.2⟩

/-! ## Maximal waves and roof equivalence -/

/-- Lemma 3.22, first assertion: a forward-extension-maximal wave roofs
every wave.  The arrow supplies a common upper bound, and maximality folds
that upper bound back into the maximal wave. -/
theorem roofLE_of_isMax {M : G.Wave} (hM : IsMax M) (W : G.Wave) :
    G.RoofLE W M := by
  obtain ⟨R, hMR, hWR⟩ := G.exists_forwardExtension_roofLE M W
  have hRM : G.ForwardExtension R M := hM hMR
  exact hWR.trans (G.roofLE_of_forwardExtension M.property hRM)

/-- A forward-extension-maximal wave is maximal in the roof preorder. -/
theorem isRoofMaximal_of_isMax {M : G.Wave} (hM : IsMax M) :
    G.IsRoofMaximal M := by
  intro W _
  exact G.roofLE_of_isMax hM W

/-- Every web has a roof-maximal wave. -/
theorem exists_roofMaximal_wave : ∃ M : G.Wave, G.IsRoofMaximal M := by
  obtain ⟨M, hM⟩ := G.exists_maximal_wave
  exact ⟨M, G.isRoofMaximal_of_isMax hM⟩

/-- Two roof-maximal waves have the same essential terminal frontier.
This is Corollary 3.23 for the roof order. -/
theorem roofEquivalent_of_isRoofMaximal {U W : G.Wave}
    (hU : G.IsRoofMaximal U) (hW : G.IsRoofMaximal W) :
    G.RoofEquivalent U W := by
  obtain ⟨R, hURforward, hWR⟩ :=
    G.exists_forwardExtension_roofLE U W
  have hUR : G.RoofLE U R :=
    G.roofLE_of_forwardExtension R.property hURforward
  have hRU : G.RoofLE R U := hU R hUR
  have hRW : G.RoofLE R W := hW R hWR
  exact G.roofEquivalent_of_mutual_roofLE
    (hUR.trans hRW) (hWR.trans hRU)

/-- Corollary 3.23 for forward-extension-maximal waves. -/
theorem roofEquivalent_of_isMax {U W : G.Wave}
    (hU : IsMax U) (hW : IsMax W) : G.RoofEquivalent U W :=
  G.roofEquivalent_of_isRoofMaximal
    (G.isRoofMaximal_of_isMax hU) (G.isRoofMaximal_of_isMax hW)

/-- Corollary 3.23 uniformly for either represented maximality notion:
forward-extension maximality or roof maximality. -/
theorem roofEquivalent_of_maximal {U W : G.Wave}
    (hU : IsMax U ∨ G.IsRoofMaximal U)
    (hW : IsMax W ∨ G.IsRoofMaximal W) :
    G.RoofEquivalent U W := by
  apply G.roofEquivalent_of_isRoofMaximal
  · exact hU.elim G.isRoofMaximal_of_isMax id
  · exact hW.elim G.isRoofMaximal_of_isMax id

end DWeb
end Erdos599
