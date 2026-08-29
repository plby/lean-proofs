/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GlobalAdvance931
import ErdosProblems.Erdos599.HalfwaySourceWarpDiamond

/-!
# Source and predecessor inheritance through the 9.31 warp diamond

The actual source diamond keeps the whole starred old family, so it keeps
every old root.  Its later-row part introduces no edge into the old carrier.
Consequently a predecessor-preserving 9.30 joint remains fully predecessor
preserving after the 9.31 diamond.  These are the two inheritance facts used
when the compressed outside assignment is added.
-/

noncomputable section

open Cardinal Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- Every old initial remains an initial of the source warp diamond. -/
theorem initialSet_subset_sourceWarpDiamond
    (old later : LinkageBlueprint Gamma Y kappa)
    (hcompat : (imaginaryWeb Gamma Y kappa).StarCompatible
      old.paths later.paths) :
    old.initialSet ⊆
      (sourceWarpDiamond old later hcompat).initialSet := by
  intro x hx
  obtain ⟨p, hp, hpinitial⟩ := hx
  let oldPath : old.paths := ⟨p, hp⟩
  exact ⟨(imaginaryWeb Gamma Y kappa).starPath hcompat oldPath,
    Or.inl ⟨oldPath, rfl⟩,
    ((imaginaryWeb Gamma Y kappa).initial_starPath
      hcompat oldPath).trans hpinitial⟩

/-- Source coverage is inherited from the old family. -/
theorem sourceWarpDiamond_covers_source
    (old later : LinkageBlueprint Gamma Y kappa)
    (hcompat : (imaginaryWeb Gamma Y kappa).StarCompatible
      old.paths later.paths)
    (hsource : Gamma.source ⊆ old.initialSet) :
    Gamma.source ⊆
      (sourceWarpDiamond old later hcompat).initialSet :=
  hsource.trans (initialSet_subset_sourceWarpDiamond old later hcompat)

/-- Compose the full predecessor preservation of the preceding joint with
the exact no-new-incoming fact of the source diamond. -/
theorem noNewPredecessorsTo_sourceWarpDiamond
    (current old later : LinkageBlueprint Gamma Y kappa)
    (hlaterFinite : (imaginaryWeb Gamma Y kappa).HasFiniteCharacter
      later.paths)
    (hcompat : (imaginaryWeb Gamma Y kappa).StarCompatible
      old.paths later.paths)
    (hcurrentVertices : current.vertexSet ⊆ old.vertexSet)
    (hcurrentOld : current.NoNewPredecessorsTo old) :
    current.NoNewPredecessorsTo
      (sourceWarpDiamond old later hcompat) := by
  intro x y hxCurrent hyx
  apply hcurrentOld hxCurrent
  exact sourceWarpDiamond_noNewIncomingOld old later hlaterFinite hcompat
    (hcurrentVertices hxCurrent) hyx

/-- Set-difference form consumed by the fresh occurrence compiler. -/
theorem sourceWarpDiamond_fresh_noIncomingCurrent
    (current old later : LinkageBlueprint Gamma Y kappa)
    (hlaterFinite : (imaginaryWeb Gamma Y kappa).HasFiniteCharacter
      later.paths)
    (hcompat : (imaginaryWeb Gamma Y kappa).StarCompatible
      old.paths later.paths)
    (hcurrentVertices : current.vertexSet ⊆ old.vertexSet)
    (hcurrentOld : current.NoNewPredecessorsTo old) :
    ∀ {x y : V}, x ∈ current.vertexSet →
      (y, x) ∈
        (sourceWarpDiamond old later hcompat).edgeSet \ current.edgeSet →
      False := by
  intro x y hxCurrent hyx
  exact hyx.2
    (noNewPredecessorsTo_sourceWarpDiamond current old later
      hlaterFinite hcompat hcurrentVertices hcurrentOld hxCurrent hyx.1)

#print axioms initialSet_subset_sourceWarpDiamond
#print axioms sourceWarpDiamond_covers_source
#print axioms noNewPredecessorsTo_sourceWarpDiamond
#print axioms sourceWarpDiamond_fresh_noIncomingCurrent

end Erdos599.Blueprint.LinkageBlueprint
