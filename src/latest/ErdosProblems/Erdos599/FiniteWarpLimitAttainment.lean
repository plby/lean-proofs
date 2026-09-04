/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LadderConstantLimit

/-!
# Finite paths are attained in any growing-warp limit

Only finitely many vertex-birth stages must be bounded for a finite limiting
path. No uncountable cofinality assumption is needed. This is distinct from
the corresponding statement for rays.
-/

noncomputable section

open Set

namespace Erdos599.DWeb.GrowingWarpChain

open DirectedPath

universe u v

variable {V : Type u} {G : DWeb V}
variable {I : Type v} [LinearOrder I]

/-- A finite-support limit path is already a complete component at some
earlier stage. -/
theorem exists_stage_of_mem_limitPaths_of_finite_support
    (C : G.GrowingWarpChain I) {p : G.DPath}
    (hp : p ∈ C.limitPaths G) (hfinite : p.support.Finite) :
    ∃ a : I, p ∈ C.stage a := by
  obtain ⟨root, rfl⟩ := hp
  let p := C.threadLimit G root
  obtain ⟨q0, i0, hq0, hq0root⟩ := C.thread_nonempty G root
  let : Nonempty I := ⟨i0⟩
  let : Finite p.support := hfinite.to_subtype
  have hborn : ∀ x : p.support, ∃ a : I,
      ∃ q ∈ C.stage a, q.initial = root.1 ∧ x.1 ∈ q.support := by
    intro x
    exact (C.mem_support_threadLimit_iff G root x.1).1 x.2
  let birth : p.support → I := fun x ↦ Classical.choose (hborn x)
  have hbirth (x : p.support) :
      ∃ q ∈ C.stage (birth x), q.initial = root.1 ∧ x.1 ∈ q.support :=
    Classical.choose_spec (hborn x)
  have hbounded : BddAbove (Set.range birth) :=
    (Set.finite_range birth).bddAbove
  obtain ⟨upper, hupper⟩ := hbounded
  let a := max i0 upper
  have hi0a : i0 ≤ a := le_max_left _ _
  have hbirthLe (x : p.support) : birth x ≤ a :=
    (hupper ⟨x, rfl⟩).trans (le_max_right _ _)
  obtain ⟨q, hq, hq0q⟩ := C.grows hi0a q0 hq0
  have hqroot : q.initial = root.1 :=
    (G.extends_initial hq0q).symm.trans hq0root
  have hsupport : p.support ⊆ q.support := by
    intro x hx
    let xs : p.support := ⟨x, hx⟩
    obtain ⟨r, hr, hrroot, hxr⟩ := hbirth xs
    obtain ⟨s, hs, hrs⟩ := C.grows (hbirthLe xs) r hr
    have hsroot : s.initial = root.1 :=
      (G.extends_initial hrs).symm.trans hrroot
    have hsq : s = q :=
      DWeb.IsWarp.eq_of_initial_eq G (C.isWarp a) hs hq
        (hsroot.trans hqroot.symm)
    exact hsq ▸ G.support_mono_of_extends hrs hxr
  have hqp : G.Extends q p :=
    Path.extends_chainLimit (C.thread G root.1)
      (C.thread_nonempty G root) (C.thread_isChain G root.1)
      ⟨a, hq, hqroot⟩
  have hqpEq : q = p := Path.eq_of_extends_of_support_subset hqp hsupport
  refine ⟨a, ?_⟩
  change p ∈ C.stage a
  exact hqpEq ▸ hq

/-- Convenient finite-path form, keeping the concrete finite path value. -/
theorem exists_stage_of_finite_mem_limitPaths
    (C : G.GrowingWarpChain I) {p : FinitePath G.graph}
    (hp : (Sum.inl p : G.DPath) ∈ C.limitPaths G) :
    ∃ a : I, (Sum.inl p : G.DPath) ∈ C.stage a :=
  C.exists_stage_of_mem_limitPaths_of_finite_support hp p.support_finite

#print axioms exists_stage_of_mem_limitPaths_of_finite_support
#print axioms exists_stage_of_finite_mem_limitPaths

end Erdos599.DWeb.GrowingWarpChain
