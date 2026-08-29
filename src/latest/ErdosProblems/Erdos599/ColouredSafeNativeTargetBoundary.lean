/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeNativeNoStrongReal
import ErdosProblems.Erdos599.Normalization

/-!
# Original target vertices do not lie on native augmented rays

A distinct-endpoint imaginary edge requires a literal real forward edge
at its source. Normalization therefore forbids it from leaving the target.
No assertion about degenerate self-connections is needed for rays.
-/

namespace Erdos599.Blueprint.ColouredSafeShortcutGraph

open Set Cardinal DirectedPath Alternating ColouredSafeHammock

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

theorem not_nativeAdj_of_target_of_ne
    (hGamma : Gamma.IsNormalized) (hY : Gamma.IsWarp Y)
    {s t : V} (hs : s ∈ Gamma.target) (hne : s ≠ t) :
    ¬(imaginaryWeb Y kappa).graph.Adj s t := by
  rintro (hreal | ⟨H, hH, hcard⟩)
  · exact (hGamma hreal).2 hs
  · obtain ⟨A, _hAH, hgood, _hdisjoint⟩ :=
      exists_mem_avoiding (X := (∅ : Set V)) hH hcard (by simp)
    obtain ⟨z, hsz⟩ := (hgood.1.forward_endpoint_incidence hY
      hgood.2.1 hne hgood.2.2.1 (hgood.2.2.2.1 t rfl)).1
    obtain ⟨W, _hW, _hWfin, hforward⟩ := hgood.1
    exact (hGamma (familyEdges_subset_adj W (hforward hsz))).2 hs

theorem nativeRay_not_mem_target
    (hGamma : Gamma.IsNormalized) (hY : Gamma.IsWarp Y)
    (r : Ray (imaginaryWeb Y kappa).graph) (n : ℕ) : r n ∉ Gamma.target := by
  intro hn
  apply not_nativeAdj_of_target_of_ne hGamma hY hn _ (r.adj_succ n)
  intro heq
  have := r.injective heq
  omega

#print axioms not_nativeAdj_of_target_of_ne
#print axioms nativeRay_not_mem_target

end Erdos599.Blueprint.ColouredSafeShortcutGraph
