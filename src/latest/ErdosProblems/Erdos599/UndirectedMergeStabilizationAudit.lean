/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UndirectedSingularMerge

/-!
# Audit of the proposed small-disturbance stabilization step

`UndirectedSingularMerge.mk_nestedComponentMerge_diff_lt` bounds the number
of genuinely new paths at each individual stage.  Club stabilization needs
the transposed estimate: for each fixed old path (or vertex), the set of
stages which disturb it must be small.  The two estimates are not equivalent,
even at a regular uncountable cardinal.

The elementary construction below records the precise obstruction.  Every
stage may have a singleton exceptional set while one fixed object belongs to
the exceptional set at every stage.  Thus no argument using only the
per-stage cardinal bound can produce the required eventual stabilization.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace UndirectedMergeStabilizationAudit

universe u

variable {I X : Type u}

/-- The stages at which a fixed object lies in the exceptional set. -/
def disturbanceStages (E : I → Set X) (x : X) : Set I :=
  {i | x ∈ E i}

/-- The constant singleton exceptional family. -/
def constantSingletonDisturbance (x : X) : I → Set X :=
  fun _ ↦ {x}

@[simp]
theorem constantSingletonDisturbance_apply (x : X) (i : I) :
    constantSingletonDisturbance x i = {x} :=
  rfl

/-- Every individual stage of the counterexample is smaller than `kappa`. -/
theorem mk_constantSingletonDisturbance_lt
    {kappa : Cardinal.{u}} (hkappa : 1 < kappa) (x : X) (i : I) :
    #(constantSingletonDisturbance x i) < kappa := by
  rw [constantSingletonDisturbance, Cardinal.mk_singleton]
  exact hkappa

/-- Nevertheless the distinguished object is disturbed at every stage. -/
@[simp]
theorem disturbanceStages_constantSingletonDisturbance (x : X) :
    disturbanceStages (constantSingletonDisturbance (I := I) x) x = Set.univ := by
  ext i
  simp [disturbanceStages, constantSingletonDisturbance]

/-- If the stage type has cardinality `kappa`, the set of disturbance stages
of the distinguished object is not smaller than `kappa`. -/
theorem not_mk_disturbanceStages_constantSingleton_lt
    {kappa : Cardinal.{u}} (hI : #I = kappa) (x : X) :
    ¬ #(disturbanceStages
      (constantSingletonDisturbance (I := I) x) x) < kappa := by
  rw [disturbanceStages_constantSingletonDisturbance,
    Cardinal.mk_univ, hI]
  exact lt_irrefl kappa

/-- Bundled failure of the small-row-to-small-column inference.  This is the
exact inference which would be needed to deduce pathwise eventual stability
from `mk_nestedComponentMerge_diff_lt`. -/
theorem exists_stagewise_small_with_full_disturbanceFiber
    {kappa : Cardinal.{u}} (hkappa : 1 < kappa)
    (hI : #I = kappa) (x : X) :
    ∃ E : I → Set X,
      (∀ i, #(E i) < kappa) ∧ #(disturbanceStages E x) = kappa := by
  refine ⟨constantSingletonDisturbance x,
    mk_constantSingletonDisturbance_lt hkappa x, ?_⟩
  rw [disturbanceStages_constantSingletonDisturbance,
    Cardinal.mk_univ, hI]

#print axioms mk_constantSingletonDisturbance_lt
#print axioms not_mk_disturbanceStages_constantSingleton_lt
#print axioms exists_stagewise_small_with_full_disturbanceFiber

end UndirectedMergeStabilizationAudit
end Erdos599

