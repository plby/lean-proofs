/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LadderConstantLimit
import ErdosProblems.Erdos599.Stationary

/-!
# Literal attainment of paths at an uncountable regular warp limit

Each limiting path has countable support. Every vertex comes from an earlier
prefix in its thread, so regularity bounds all its birth stages below the
limit ordinal. The unique component at that common stage is the full limit
path. This is a pathwise statement, not stabilization of the whole warp.
-/

noncomputable section

open Set Cardinal Order

namespace Erdos599.DWeb.GrowingWarpChain

open DirectedPath

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

/-- A path already present in a stage and in the limit persists literally
at every later stage: no strict extension can precede that same limit. -/
theorem mem_stage_of_mem_limit_and_mem_earlier
    (C : G.GrowingWarpChain (Stationary.Below kappa))
    {p : G.DPath} (hpLimit : p ∈ C.limitPaths G)
    {a b : Stationary.Below kappa} (hpA : p ∈ C.stage a) (hab : a ≤ b) :
    p ∈ C.stage b := by
  obtain ⟨q, hqB, hpq⟩ := C.grows hab p hpA
  obtain ⟨r, hrLimit, hqr⟩ := C.grows_limitPaths G b q hqB
  have hrp : r = p :=
    DWeb.IsWarp.eq_of_initial_eq G (C.isWarp_limitPaths G) hrLimit hpLimit
      ((G.extends_initial hqr).symm.trans (G.extends_initial hpq).symm)
  have hqp : G.Extends q p := hrp ▸ hqr
  have hpEq : p = q :=
    Path.eq_of_extends_of_support_subset hpq (G.support_mono_of_extends hqp)
  exact hpEq ▸ hqB

/-- Every path of the limiting warp occurs literally at some earlier stage.
The uncountable cofinality is essential for limiting rays. -/
theorem exists_stage_of_mem_limitPaths
    (C : G.GrowingWarpChain (Stationary.Below kappa))
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    {p : G.DPath} (hp : p ∈ C.limitPaths G) :
    ∃ a : Stationary.Below kappa, p ∈ C.stage a := by
  obtain ⟨root, rfl⟩ := hp
  let p := C.threadLimit G root
  have hborn : ∀ x : p.support, ∃ a : Stationary.Below kappa,
      ∃ q ∈ C.stage a, q.initial = root.1 ∧ x.1 ∈ q.support := by
    intro x
    exact (C.mem_support_threadLimit_iff G root x.1).1 x.2
  let birth : p.support → Stationary.Below kappa :=
    fun x ↦ Classical.choose (hborn x)
  have hbirth (x : p.support) :
      ∃ q ∈ C.stage (birth x), q.initial = root.1 ∧ x.1 ∈ q.support :=
    Classical.choose_spec (hborn x)
  let bound : Ordinal.{u} := ⨆ x : p.support, (birth x).1
  have hbound : bound < kappa.ord :=
    Stationary.iSup_lt_ord_of_lt hkappa
      (p.support_countable.le_aleph0.trans_lt huncountable)
      (fun x ↦ (birth x).2)
  let a : Stationary.Below kappa := ⟨bound, hbound⟩
  have hbirthLe (x : p.support) : birth x ≤ a :=
    Ordinal.le_iSup (fun y : p.support ↦ (birth y).1) x
  let x0 : p.support := ⟨p.initial, p.initial_mem_support⟩
  obtain ⟨q0, hq0, hq0root, _hx0⟩ := hbirth x0
  obtain ⟨q, hq, hq0q⟩ := C.grows (hbirthLe x0) q0 hq0
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

/-- A small family of limiting paths is present simultaneously at one stage
and hence at every subsequent stage. -/
theorem exists_stage_subset_of_small_limitFamily
    (C : G.GrowingWarpChain (Stationary.Below kappa))
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    {P : Set G.DPath} (hP : P ⊆ C.limitPaths G) (hsmall : #P < kappa) :
    ∃ a : Stationary.Below kappa, ∀ b, a ≤ b → P ⊆ C.stage b := by
  have hexists (p : P) : ∃ a : Stationary.Below kappa, p.1 ∈ C.stage a :=
    C.exists_stage_of_mem_limitPaths hkappa huncountable (hP p.2)
  let birth : P → Stationary.Below kappa :=
    fun p ↦ Classical.choose (hexists p)
  have hbirth (p : P) : p.1 ∈ C.stage (birth p) :=
    Classical.choose_spec (hexists p)
  let bound : Ordinal.{u} := ⨆ p : P, (birth p).1
  have hbound : bound < kappa.ord :=
    Stationary.iSup_lt_ord_of_lt hkappa hsmall (fun p ↦ (birth p).2)
  let a : Stationary.Below kappa := ⟨bound, hbound⟩
  refine ⟨a, ?_⟩
  intro b hab p hp
  let ps : P := ⟨p, hp⟩
  have hbirthA : birth ps ≤ a :=
    Ordinal.le_iSup (fun q : P ↦ (birth q).1) ps
  exact C.mem_stage_of_mem_limit_and_mem_earlier
    (hP hp) (hbirth ps) (hbirthA.trans hab)

#print axioms exists_stage_of_mem_limitPaths
#print axioms exists_stage_subset_of_small_limitFamily

end Erdos599.DWeb.GrowingWarpChain
