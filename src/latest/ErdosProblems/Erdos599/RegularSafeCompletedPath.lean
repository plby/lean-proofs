/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularCompletedPendingSplice
import ErdosProblems.Erdos599.SafeLinkPropositionComplete

/-!
# Future-safe completed paths for the regular splice

The completed/pending recursion freezes target paths.  Such a path must be
chosen in the web obtained by deleting the already frozen carrier; Theorem
6.1 then guarantees that deleting the new path as well preserves
unhinderedness.  This file packages that one-step transport in the ambient
web.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace RegularCompletedPendingSplice

universe u

variable {V : Type u}

/-- Choose a target path which avoids an already protected carrier and whose
addition to that carrier is still a safe deletion. -/
theorem exists_safeCompletedPath
    (G : DWeb V) (Q : Set V)
    (hresidual : (G.delete Q).IsUnhindered)
    {a : V} (ha : a ∈ (G.delete Q).source) :
    ∃ p : DirectedPath.FinitePath G.graph,
      p.start = a ∧ p.finish ∈ G.target ∧
        Disjoint p.support Q ∧
        (G.delete (Q ∪ p.support)).IsUnhindered := by
  obtain ⟨p, hpstart, hptarget, hpsafe⟩ :=
    SafeLink.exists_safeTargetPath (G.delete Q) hresidual ha
  let q : DirectedPath.FinitePath G.graph :=
    p.lift (fun {_ _} e ↦ G.delete_adj_imp e)
  have hqSupport : q.support = p.support :=
    DirectedPath.FinitePath.support_lift _ p
  have hqAvoid : Disjoint q.support Q := by
    rw [hqSupport]
    have hinitial : DirectedPath.Path.initial
        (Sum.inl p : (G.delete Q).DPath) ∉ Q := by
      change p.start ∉ Q
      simpa only [hpstart] using ha.2
    have hav := G.liftDeletePath_avoids Q (Sum.inl p) hinitial
    rw [G.support_liftDeletePath] at hav
    change Disjoint p.support Q at hav
    exact hav
  have hqSafe : (G.delete (Q ∪ q.support)).IsUnhindered := by
    rw [hqSupport]
    simpa only [G.delete_delete] using hpsafe
  exact ⟨q, hpstart, hptarget.1, hqAvoid, hqSafe⟩

end RegularCompletedPendingSplice
end CardinalInduction
end Erdos599
