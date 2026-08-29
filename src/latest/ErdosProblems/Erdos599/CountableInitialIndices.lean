/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.PopularAuxiliary

/-!
# Countable initial-index fibers of a joined family

The countable-collision lemma in `PopularAuxiliary` is usually consumed only
through nonstationarity.  Assertion 8.20 needs its sharper intermediate
conclusion: paths assigned to one fixed fragment have a countable set of
initial indices, so a stationary family can be thinned to one path per
fragment.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace PopularAuxiliary.Input

open DirectedPath Stationary

universe u

/-- The initial indices of a joined family meeting a fixed countable set away
from its join set form a countable set. -/
theorem joinedFamily_initialIndices_countable_of_meets_countable
    {W : Type u} {web : DWeb W} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed web kappa) {S R : Set W}
    (F : Popular.JoinedFamily web S) (hR : R.Countable)
    (hRS : Disjoint R S)
    (hmeet : ∀ p ∈ F.paths, ∃ x ∈ R, x ∈ p.support) :
    (Popular.initialIndicesOf U F.paths F.starts_in_source).Countable := by
  have hpaths : F.paths.Countable :=
    joinedFamily_paths_countable_of_meets_countable F hR hRS hmeet
  let indexOf : F.paths → Below kappa := fun p ↦
    U.f ⟨p.1.start, F.starts_in_source p.2⟩
  let _ : Countable F.paths := hpaths.to_subtype
  refine (Set.countable_range indexOf).mono ?_
  rintro a ⟨p, hp, hpa⟩
  exact ⟨⟨p, hp⟩, hpa⟩

end PopularAuxiliary.Input
end Erdos599
