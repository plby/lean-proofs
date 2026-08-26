import ErdosProblems.Erdos593.TripleSystem.CardinalPairPartition
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Continuum

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Erdos--Rado carrier interface

This module fixes the base-universe carrier of cardinality the successor of
the continuum and records the exact infinite homogeneous-set premise needed
by the countably-coloured Erdos--Rado special case.  It intentionally does
not assert or prove that premise.
-/

namespace Erdos593
namespace TripleSystem
namespace TriangleHost

/-- The base-universe carrier of cardinality `(2^aleph0)^+`. -/
noncomputable abbrev ErdosRadoCarrier : Type :=
  (Order.succ (Cardinal.continuum : Cardinal)).out

/-- The chosen cardinal carrier has decidable equality, noncomputably. -/
noncomputable instance erdosRadoCarrierDecidableEq : DecidableEq ErdosRadoCarrier :=
  Classical.decEq _

/-- The carrier has exactly the desired successor-of-continuum cardinality. -/
theorem mk_erdosRadoCarrier :
    Cardinal.mk ErdosRadoCarrier = Order.succ (Cardinal.continuum : Cardinal) :=
  Cardinal.mk_out _

/-- The precise countably-coloured infinite homogeneous-set consequence that
a future Erdos--Rado formalization must establish. -/
def ErdosRadoHomogeneousPairSet : Prop :=
  ∀ c : Pair ErdosRadoCarrier → ℕ, ∃ H : Set ErdosRadoCarrier,
    H.Infinite ∧ PairHomogeneous c H


/-- A stronger, cardinal-form target for the countably-coloured
Erdős--Rado special case.  This is an interface only: no partition
calculus theorem is asserted here. -/
def ErdosRadoUncountableHomogeneousPairSet : Prop :=
  ∀ c : Pair ErdosRadoCarrier → ℕ, ∃ H : Set ErdosRadoCarrier,
    Cardinal.aleph0 < Cardinal.mk H ∧ PairHomogeneous c H

/-- An uncountable homogeneous set supplies the infinite homogeneous set
required by the finite Ramsey extraction bridge. -/
theorem erdosRadoHomogeneousPairSet_of_uncountable
    (h : ErdosRadoUncountableHomogeneousPairSet) :
    ErdosRadoHomogeneousPairSet := by
  intro c
  obtain ⟨H, hH, hhomogeneous⟩ := h c
  refine ⟨H, ?_, hhomogeneous⟩
  exact Set.infinite_coe_iff.mp (Cardinal.aleph0_le_mk_iff.mp hH.le)

/-- The external homogeneous-set theorem implies the local Ramsey interface.
This is only a conditional composition of the checked finite bridge. -/
theorem pairRamseyTriangle_erdosRadoCarrier_of
    (h : ErdosRadoHomogeneousPairSet) :
    PairRamseyTriangle ErdosRadoCarrier :=
  pairRamseyTriangle_of_infinite_pair_homogeneous h

/-- The stronger cardinal-form target implies the local Ramsey interface. -/
theorem pairRamseyTriangle_erdosRadoCarrier_of_uncountable
    (h : ErdosRadoUncountableHomogeneousPairSet) :
    PairRamseyTriangle ErdosRadoCarrier :=
  pairRamseyTriangle_erdosRadoCarrier_of
    (erdosRadoHomogeneousPairSet_of_uncountable h)

end TriangleHost
end TripleSystem
end Erdos593
