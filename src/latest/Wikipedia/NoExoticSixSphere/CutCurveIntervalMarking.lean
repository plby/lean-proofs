import Wikipedia.NoExoticSixSphere.CutCurveIntervalClosures

/-!
# Actual coordinate markings of component closures

The marking retains the original chart, the proof that the entire closure
lies in its source, and exact equality of the interval homeomorphism with
the actual real-valued coordinate. Such markings are constructed for the
cut components; their endpoints are actual points of the original closure.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.CurveDecomposition

open InvolutionQuotient

variable {X : Type*} [TopologicalSpace X]

structure IntervalMarking (C : Set X) where
  left : ℝ
  right : ℝ
  lt : left < right
  chart : OpenPartialHomeomorph X HalfLine
  source : closure C ⊆ chart.source
  homeo : closure C ≃ₜ Icc left right
  coordinate : ∀ y, (homeo y).val = CurveChart.realCoordinate chart y.val

def IntervalMarking.leftPoint {C : Set X} (m : IntervalMarking C) : closure C :=
  m.homeo.symm ⟨m.left, le_rfl, m.lt.le⟩

def IntervalMarking.rightPoint {C : Set X} (m : IntervalMarking C) : closure C :=
  m.homeo.symm ⟨m.right, m.lt.le, le_rfl⟩

theorem IntervalMarking.left_coordinate {C : Set X} (m : IntervalMarking C) :
    CurveChart.realCoordinate m.chart m.leftPoint.val = m.left := by
  rw [← m.coordinate]
  exact congrArg Subtype.val (m.homeo.apply_symm_apply _)

theorem IntervalMarking.right_coordinate {C : Set X} (m : IntervalMarking C) :
    CurveChart.realCoordinate m.chart m.rightPoint.val = m.right := by
  rw [← m.coordinate]
  exact congrArg Subtype.val (m.homeo.apply_symm_apply _)

theorem IntervalMarking.point_bounds {C : Set X} (m : IntervalMarking C)
    {y : X} (hy : y ∈ closure C) :
    m.left ≤ CurveChart.realCoordinate m.chart y ∧
      CurveChart.realCoordinate m.chart y ≤ m.right := by
  rw [← m.coordinate ⟨y, hy⟩]
  exact (m.homeo ⟨y, hy⟩).property

theorem IntervalMarking.endpoints_distinct {C : Set X} (m : IntervalMarking C) :
    m.leftPoint.val ≠ m.rightPoint.val := by
  intro he
  have h := congrArg (CurveChart.realCoordinate m.chart) he
  rw [m.left_coordinate, m.right_coordinate] at h
  exact m.lt.ne h

theorem IntervalMarking.eq_leftPoint_of_coordinate {C : Set X} (m : IntervalMarking C)
    {y : X} (hy : y ∈ closure C) (he : CurveChart.realCoordinate m.chart y = m.left) :
    y = m.leftPoint.val :=
  CurveChart.injOn_realCoordinate m.chart (m.source hy) (m.source m.leftPoint.property)
    (he.trans m.left_coordinate.symm)

theorem IntervalMarking.eq_rightPoint_of_coordinate {C : Set X} (m : IntervalMarking C)
    {y : X} (hy : y ∈ closure C) (he : CurveChart.realCoordinate m.chart y = m.right) :
    y = m.rightPoint.val :=
  CurveChart.injOn_realCoordinate m.chart (m.source hy) (m.source m.rightPoint.property)
    (he.trans m.right_coordinate.symm)

theorem exists_cutComponent_marking [T2Space X] [LocallyConnectedSpace X]
    {ι : Type*} (t : Finset ι) (N : ι → IntervalNeighborhood X)
    (hcov : univ ⊆ ⋃ i ∈ t, (N i).openSet) (x : {x : X // x ∉ cutSet t N}) :
    ∃ i ∈ t, ∃ m : IntervalMarking (cutComponent (cutSet t N) x), m.chart = (N i).chart := by
  obtain ⟨i, hi, hs, a, b, hab, h, hh⟩ := exists_cutComponent_interval_in_chart t N hcov x
  exact ⟨i, hi, ⟨a, b, hab, (N i).chart, hs, h, hh⟩, rfl⟩

end NoExoticSixSphere.CurveDecomposition
