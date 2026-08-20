import ErdosProblems.Erdos957.CyclicWindow
import ErdosProblems.Erdos957.CaseClassification

/-!
# The genuine cyclic-window datum supplies the local hull window used by row realization

This small adapter contains no charging or collision assumption.  It only
combines the checked distance-two coordinate estimate with the checked
diameter-chord locality theorem.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace Erdos957RealizationWindow

open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957CollisionInstantiation
open Erdos957GeometryLocalityBridge
open Erdos957CaseClassification

abbrev Point := Erdos957GeometryCore.Point

variable {A : Finset Point} {P : CyclicHullData A}
variable {W : DiameterWitnessData P} {F : P.FlatAlignedFrameData}

/-- Every hull vertex joined to an emitting source by at most two unit edges
lies in the source's genuine seven-vertex cyclic window. -/
theorem localHullWindowHypothesis
    (L : CyclicWindowGeometry W F) (s : Source P W) :
    LocalHullWindowHypothesis P (sourceIndex P W s.1 s.property) := by
  intro v hvH hpath
  let i := sourceIndex P W s.1 s.property
  have hd : dist (i.1 : Point) (v : Point) ≤ 2 :=
    Erdos957GeometryLocalityBridge.dist_le_two_of_withinTwoUnitEdges hpath
  obtain ⟨hx, hy⟩ := abs_chartCoord_sub_le_two F.chart i hd
  have hsource := F.chart.coord_source i
  rw [hsource] at hx hy
  simp only [Prod.fst_zero, Prod.snd_zero, sub_zero] at hx hy
  have hrect : Erdos957Locality.InCompetingSourceRectangle
      (F.chart.coord i v) := by
    rw [abs_le] at hx hy
    exact ⟨by linarith, by linarith, by linarith,
      F.chart.coord_snd_nonpos i v⟩
  exact mem_sevenHullWindow_of_mem_competingRectangle W F L s v hvH hrect

end Erdos957RealizationWindow
