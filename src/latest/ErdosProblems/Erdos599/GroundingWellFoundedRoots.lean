/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingRootedReachabilityWarp

/-!
# Roots of well-founded directed relations

The corrected simultaneous switch excludes reverse-directed rays.  Together
with acyclicity this makes its predecessor relation well founded.  The lemmas
below expose the exact finite reachability consequence needed by the final
grounding geometry, without first decomposing the relation into a warp.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingWellFoundedRoots

open Alternating

universe u

variable {V : Type u}

/-- Every vertex of a well-founded predecessor relation is reachable from a
vertex with no incoming relation edge. -/
theorem exists_noIncoming_root
    (E : Set (V × V))
    (hwf : WellFounded (fun x y : V ↦ (x, y) ∈ E)) (b : V) :
    ∃ a : V,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b ∧
        ¬ HasIncoming E a := by
  induction b using hwf.induction with
  | h b ih =>
      by_cases hb : HasIncoming E b
      · obtain ⟨x, hxb⟩ := hb
        obtain ⟨a, hax, ha⟩ := ih x hxb
        exact ⟨a, hax.tail hxb, ha⟩
      · exact ⟨b, Relation.ReflTransGen.refl, hb⟩

/-- Specialized packaging: if every no-incoming root which can reach `B`
belongs to `A`, then every point of `B` has the rooted reachability witness
consumed by `GroundingRootedReachabilityWarp`. -/
theorem rooted_reachability_of_noIncoming_classification
    (E : Set (V × V))
    (hwf : WellFounded (fun x y : V ↦ (x, y) ∈ E))
    (A B : Set V)
    (hclassify : ∀ a b,
      ¬ HasIncoming E a → b ∈ B →
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b → a ∈ A) :
    ∀ b ∈ B, ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b ∧
        ¬ HasIncoming E a := by
  intro b hb
  obtain ⟨a, hab, haNo⟩ := exists_noIncoming_root E hwf b
  exact ⟨a, hclassify a b haNo hb hab, hab, haNo⟩

end GroundingWellFoundedRoots
end Erdos599
