/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayGroupedContactTransaction
import ErdosProblems.Erdos599.FracturedInfiniteTraversalBlocks

/-!
# The recombined owner of a fractured path

The paths of a `FracturedWarp` may share a displayed terminal/initial
vertex, so their literal source indices are not suitable global owner tags.
Every nontrivial member does, however, have a unique owner in the honest
recombined `edgeWarp`.  This file constructs that owner and proves that a
common vertex identifies it.  These are the ownership facts required when
contact chains are projected from the occurrence-split web.
-/

noncomputable section

open Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint
namespace FracturedAssignmentPeel

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- A nontrivial finite member is supported by every recombined path which
contains all of its edges. -/
theorem activePath_support_subset_of_edges_subset
    (Z : FracturedWarp Gamma)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    {p q : Gamma.DPath} (hp : p ∈ activePaths Z)
    (hedges : p.edgeSet ⊆ q.edgeSet) : p.support ⊆ q.support := by
  obtain ⟨pf, rfl⟩ := hZfinite hp.1
  have hne : pf.start ≠ pf.finish :=
    Alternating.FracturedDuplication.finite_start_ne_finish_of_nontrivial
      pf hp.2
  intro x hx
  rcases finitePath_mem_support_incident_of_nontrivial pf hne hx with
      ⟨y, hxy⟩ | ⟨y, hyx⟩
  · exact (q.edgeSet_subset_support_prod (hedges hxy)).1
  · exact (q.edgeSet_subset_support_prod (hedges hyx)).2

/-- The honest recombination has exactly one member which contains the
edges of a fixed active fractured path. -/
theorem existsUnique_edgeWarp_carrier_of_activePath
    (Z : FracturedWarp Gamma)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    {p : Gamma.DPath} (hp : p ∈ activePaths Z) :
    ∃! q : Gamma.DPath, q ∈ Z.edgeWarp ∧ p.edgeSet ⊆ q.edgeSet := by
  obtain ⟨q, hq, hpq⟩ :=
    InfiniteTraversalFrontend.exists_edgeWarp_carrier_of_activePath
      Z hZfinite hp
  refine ⟨q, ⟨hq, hpq⟩, ?_⟩
  intro r hr
  have hpSupportQ : p.support ⊆ q.support :=
    activePath_support_subset_of_edges_subset Z hZfinite hp hpq
  have hpSupportR : p.support ⊆ r.support :=
    activePath_support_subset_of_edges_subset Z hZfinite hp hr.2
  rcases hp.2 with ⟨x, hx, _y, _hy, _hxy⟩
  exact DWeb.IsWarp.eq_of_mem_support Z.edgeWarp_isWarp
    hr.1 hq (hpSupportR hx) (hpSupportQ hx)

/-- The canonical recombined owner of an active fractured member. -/
noncomputable def recombinedOwner
    (Z : FracturedWarp Gamma)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (p : activePaths Z) : Z.edgeWarp :=
  ⟨Classical.choose
      (existsUnique_edgeWarp_carrier_of_activePath Z hZfinite p.property),
    (Classical.choose_spec
      (existsUnique_edgeWarp_carrier_of_activePath Z hZfinite p.property)).1.1⟩

theorem activePath_edges_subset_recombinedOwner
    (Z : FracturedWarp Gamma)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (p : activePaths Z) :
    p.1.edgeSet ⊆ (recombinedOwner Z hZfinite p).1.edgeSet :=
  (Classical.choose_spec
    (existsUnique_edgeWarp_carrier_of_activePath Z hZfinite p.property)).1.2

theorem activePath_support_subset_recombinedOwner
    (Z : FracturedWarp Gamma)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (p : activePaths Z) :
    p.1.support ⊆ (recombinedOwner Z hZfinite p).1.support :=
  activePath_support_subset_of_edges_subset Z hZfinite p.property
    (activePath_edges_subset_recombinedOwner Z hZfinite p)

/-- Any recombined carrier of the active member is its canonical owner. -/
theorem recombinedOwner_eq_of_activePath_edges_subset
    (Z : FracturedWarp Gamma)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (p : activePaths Z) (q : Z.edgeWarp)
    (hedges : p.1.edgeSet ⊆ q.1.edgeSet) :
    recombinedOwner Z hZfinite p = q := by
  apply Subtype.ext
  exact ((Classical.choose_spec
    (existsUnique_edgeWarp_carrier_of_activePath Z hZfinite p.property)).2
      q.1 ⟨q.2, hedges⟩).symm

/-- A common projected vertex of two active fragments identifies their
recombined owner, even when the two literal fragments are distinct. -/
theorem recombinedOwner_eq_of_common_vertex
    (Z : FracturedWarp Gamma)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (p q : activePaths Z) {x : V}
    (hxp : x ∈ p.1.support) (hxq : x ∈ q.1.support) :
    recombinedOwner Z hZfinite p = recombinedOwner Z hZfinite q := by
  apply Subtype.ext
  exact DWeb.IsWarp.eq_of_mem_support Z.edgeWarp_isWarp
    (recombinedOwner Z hZfinite p).property
    (recombinedOwner Z hZfinite q).property
    (activePath_support_subset_recombinedOwner Z hZfinite p hxp)
    (activePath_support_subset_recombinedOwner Z hZfinite q hxq)

/-- Recombined owner attached directly to an active downstairs assignment
source. -/
noncomputable def recombinedSourceOwner
    (Z : FracturedWarp Gamma)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (z : {x // x ∈ Gamma.initialSet (activePaths Z) \
      Gamma.initialSet Y}) : Z.edgeWarp :=
  recombinedOwner Z hZfinite
    (initialPath (activePaths Z) ⟨z.1, z.property.1⟩)

/-- The literal active source is a vertex of its honest recombined owner. -/
theorem source_mem_recombinedSourceOwner
    (Z : FracturedWarp Gamma)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (z : {x // x ∈ Gamma.initialSet (activePaths Z) \
      Gamma.initialSet Y}) :
    z.1 ∈ (recombinedSourceOwner Z hZfinite z).1.support := by
  let za : {x // x ∈ Gamma.initialSet (activePaths Z)} :=
    ⟨z.1, z.property.1⟩
  have hmem : (initialPath (activePaths Z) za).1.initial ∈
      (initialPath (activePaths Z) za).1.support :=
    (initialPath (activePaths Z) za).1.initial_mem_support
  apply activePath_support_subset_recombinedOwner Z hZfinite
    (initialPath (activePaths Z) za)
  simpa only [initialPath_initial] using hmem

end FracturedAssignmentPeel
end LinkageBlueprint
end Blueprint
end Erdos599
