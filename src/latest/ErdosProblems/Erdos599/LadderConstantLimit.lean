/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Ladder

/-!
# Eventually constant limits of growing warps

This file records the stabilization lemma needed at an inactive limit stage
of the ladder recursion.  Since `GrowingWarpChain.limitPaths` is the genuine
threadwise direct limit, the statement is not definitionally true: one must
show that the stabilized stage is an upper bound of every thread and then use
uniqueness of a concrete path with a prescribed support.
-/

namespace Erdos599

open Set DirectedPath

universe u v

namespace DirectedPath.Walk

/-- A private, dependency-light support extensionality helper for this file. -/
private theorem head?_support_constantLimit {V : Type u} {D : Digraph V}
    {a b : V} (p : Walk D a b) : p.support.head? = some a := by
  cases p <;> rfl

private theorem eq_of_support_eq_constantLimit {V : Type u}
    {D : Digraph V} {a b : V} (p q : Walk D a b)
    (h : p.support = q.support) : p = q := by
  induction p with
  | nil =>
      cases q with
      | nil => rfl
      | cons e q => simp at h
  | @cons a x b e p ih =>
      cases q with
      | nil => simp at h
      | @cons _ y _ f q =>
          simp only [support_cons] at h
          have hpqList : p.support = q.support := (List.cons.inj h).2
          have hxy : x = y := by
            have hhead := congrArg List.head? hpqList
            simpa only [head?_support_constantLimit, Option.some.injEq] using hhead
          subst y
          have hpq : p = q := ih q hpqList
          subst q
          rfl

end DirectedPath.Walk

namespace DirectedPath.FinitePath

private theorem eq_of_start_finish_support_eq {V : Type u} {D : Digraph V}
    (p q : FinitePath D) (hstart : p.start = q.start)
    (hfinish : p.finish = q.finish)
    (hsupport : p.walk.support = q.walk.support) : p = q := by
  rcases p with ⟨a, b, p, hp⟩
  rcases q with ⟨c, d, q, hq⟩
  dsimp only at hstart hfinish hsupport
  subst c
  subst d
  have hpq : p = q :=
    DirectedPath.Walk.eq_of_support_eq_constantLimit p q hsupport
  subst q
  rfl

end DirectedPath.FinitePath

namespace DirectedPath.Path

variable {V : Type u} {D : Digraph V}

/-- An extension which adds no vertices is the original concrete path. -/
theorem eq_of_extends_of_support_subset {p q : Path D}
    (hpq : Extends p q) (hqp : q.support ⊆ p.support) : p = q := by
  classical
  rcases p with p | r <;> rcases q with q | s
  · have hlen : q.walk.support.length ≤ p.walk.support.length := by
      rw [← List.toFinset_card_of_nodup q.isPath,
        ← List.toFinset_card_of_nodup p.isPath]
      apply Finset.card_le_card
      intro x hx
      simp only [List.mem_toFinset] at hx ⊢
      change ∀ ⦃x⦄, x ∈ q.walk.support → x ∈ p.walk.support at hqp
      exact hqp hx
    have hsupp : p.walk.support = q.walk.support :=
      hpq.eq_of_length_le hlen
    have hstart : p.start = q.start := hpq.start_eq
    have hfinish : p.finish = q.finish := by
      calc
        p.finish = p.walk.support.getLast p.walk.support_ne_nil :=
          p.walk.getLast_support.symm
        _ = q.walk.support.getLast q.walk.support_ne_nil := by
          simp only [hsupp]
        _ = q.finish := q.walk.getLast_support
    exact congrArg Sum.inl
      (DirectedPath.FinitePath.eq_of_start_finish_support_eq
        p q hstart hfinish hsupp)
  · exfalso
    change s.support ⊆ p.support at hqp
    exact (Set.infinite_range_of_injective s.injective)
      (p.support_finite.subset hqp)
  · exact False.elim hpq
  · exact congrArg Sum.inr hpq

end DirectedPath.Path

namespace DWeb.GrowingWarpChain

variable {V : Type u} (G : DWeb V)
variable {I : Type v} [LinearOrder I]

/-- The genuine threadwise direct limit of a growing warp chain agrees with
an eventually literally constant stage. -/
theorem limitPaths_eq_stage_of_eventually_constant
    (C : G.GrowingWarpChain I) (i₀ : I)
    (hconstant : ∀ j, i₀ ≤ j → C.stage j = C.stage i₀) :
    C.limitPaths G = C.stage i₀ := by
  have hlimitSubset : C.limitPaths G ⊆ C.stage i₀ := by
    rintro q ⟨a, rfl⟩
    obtain ⟨r₀, i, hr₀i, hr₀initial⟩ := C.thread_nonempty G a
    obtain ⟨p, hpi₀, hpinitial⟩ :
        ∃ p ∈ C.stage i₀, p.initial = a.1 := by
      rcases le_total i i₀ with hii₀ | hi₀i
      · obtain ⟨p, hpi₀, hr₀p⟩ := C.grows hii₀ r₀ hr₀i
        exact ⟨p, hpi₀, (G.extends_initial hr₀p).symm.trans hr₀initial⟩
      · exact ⟨r₀, (hconstant i hi₀i).symm ▸ hr₀i, hr₀initial⟩
    have hpUpper : ∀ r ∈ C.thread G a.1, G.Extends r p := by
      rintro r ⟨j, hrj, hrinitial⟩
      rcases le_total j i₀ with hji₀ | hi₀j
      · obtain ⟨s, hsi₀, hrs⟩ := C.grows hji₀ r hrj
        have hsp : s = p :=
          DWeb.IsWarp.eq_of_initial_eq G (C.isWarp i₀) hsi₀ hpi₀
            ((G.extends_initial hrs).symm.trans
              (hrinitial.trans hpinitial.symm))
        exact hsp ▸ hrs
      · have hri₀ : r ∈ C.stage i₀ :=
          (hconstant j hi₀j).symm ▸ hrj
        have hrp : r = p :=
          DWeb.IsWarp.eq_of_initial_eq G (C.isWarp i₀) hri₀ hpi₀
            (hrinitial.trans hpinitial.symm)
        exact hrp ▸ G.extends_refl p
    have hsupport : (C.threadLimit G a).support ⊆ p.support := by
      intro x hx
      obtain ⟨j, r, hrj, hrinitial, hxr⟩ :=
        (C.mem_support_threadLimit_iff G a x).1 hx
      exact G.support_mono_of_extends
        (hpUpper r ⟨j, hrj, hrinitial⟩) hxr
    have hpThread : p ∈ C.thread G a.1 := ⟨i₀, hpi₀, hpinitial⟩
    have hpLimit : G.Extends p (C.threadLimit G a) :=
      DirectedPath.Path.extends_chainLimit (C.thread G a.1)
        (C.thread_nonempty G a) (C.thread_isChain G a.1) hpThread
    have hpEq : p = C.threadLimit G a :=
      DirectedPath.Path.eq_of_extends_of_support_subset hpLimit hsupport
    exact hpEq ▸ hpi₀
  apply Set.Subset.antisymm hlimitSubset
  intro p hpi₀
  obtain ⟨q, hqLimit, hpq⟩ := C.grows_limitPaths G i₀ p hpi₀
  have hqStage : q ∈ C.stage i₀ := hlimitSubset hqLimit
  have hpqEq : p = q :=
    DWeb.IsWarp.eq_of_initial_eq G (C.isWarp i₀) hpi₀ hqStage
      (G.extends_initial hpq)
  exact hpqEq ▸ hqLimit

end DWeb.GrowingWarpChain

end Erdos599
