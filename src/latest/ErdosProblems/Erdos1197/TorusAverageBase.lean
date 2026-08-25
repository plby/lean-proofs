import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Topology.Algebra.Group.ClosedSubgroup

namespace Erdos1197

open scoped BigOperators

noncomputable section

/-! ## Torus Separation Infrastructure -/

open MeasureTheory
open UnitAddTorus
open MeasureTheory.Measure

variable {d : Type*} [Fintype d]

abbrev T := UnitAddTorus d

/-- A convenient normalized Haar measure on a compact additive group. -/
noncomputable def subgroupUnivPositiveCompact {α : Type*} [AddGroup α] [TopologicalSpace α]
    [ContinuousAdd α] [ContinuousNeg α] [CompactSpace α] [Nonempty α] :
    TopologicalSpace.PositiveCompacts α :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

def torusTranslate (a : UnitAddTorus d) : C(UnitAddTorus d, UnitAddTorus d) :=
  ContinuousMap.id _ + ContinuousMap.const _ a

def avgOverSubgroup (H : ClosedAddSubgroup (UnitAddTorus d))
    (f : C(UnitAddTorus d, ℂ)) : C(UnitAddTorus d, ℂ) :=
  let μH : Measure H := addHaarMeasure (subgroupUnivPositiveCompact (α := H))
  ∫ h : H, f.comp (torusTranslate (d := d) (h : UnitAddTorus d)) ∂μH


end

end Erdos1197
