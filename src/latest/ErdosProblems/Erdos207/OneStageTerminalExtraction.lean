/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialRootTypicality
import ErdosProblems.Erdos207.MasterLawCompression

/-!
# Terminal extraction for the one-stage vortex

The long initial sparsification and its single root-covering transition
already produce a compressed law at level one.  This file records that no
finite induction is needed after that point: level one is definitionally the
flexible absorber set.
-/

namespace Erdos207

open scoped NNReal

noncomputable section

/-- A compressed master law at the inner level of `oneStageVortex X`
contains the outside packing needed by the absorber reduction. -/
theorem IsCompressedMasterLaw.exists_ksssOutsidePacking_oneStage
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V} {law : FiniteLaw (MasterStateOn V)}
    {p eta xi C b : ℝ≥0} {h : ℕ}
    (hlaw : IsCompressedMasterLaw law (oneStageVortex X) (1 : Fin 2)
      (absorberErdosForbiddenConfigurationsOn q B)
      (graphDifference (SimpleGraph.completeGraph V) H)
      (outsideAvailableTriangles H B) p eta xi C b h)
    (hxi : xi < 1) :
    ∃ P : TripleSystemOn V, HasKSSSOutsidePacking q H X B P := by
  exact hlaw.exists_ksssOutsidePacking (oneStageVortex_U_one X) hxi

end

end Erdos207
