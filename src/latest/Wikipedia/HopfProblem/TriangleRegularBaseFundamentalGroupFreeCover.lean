import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupCover
import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupCoveringCore
import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupMeridians
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Algebra.Group.Equiv.Opposite

/-!
# The free-group transition covering of the twice-punctured plane

Give the free group on the two marked meridians the discrete topology.
On the three components of the actual slit-cover overlap the transition
is, respectively, the inverse first generator, the identity, and the
second generator.  This locally constant transition constructs an actual
covering space through the proved two-open bundle construction.
-/

noncomputable section

open Set
open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- The discrete topology used on the two-generator free deck group. -/
@[instance_reducible] def discreteFreeGroup : TopologicalSpace (FreeGroup Bool) := ⊥

attribute [local instance] discreteFreeGroup

instance discreteFreeGroup_discrete : DiscreteTopology (FreeGroup Bool) := ⟨rfl⟩

/-- The transition values on the left, middle, and right overlap strips. -/
def freeGroupTransitionValue : Fin 3 → FreeGroup Bool
  | 0 => (FreeGroup.of false)⁻¹
  | 1 => 1
  | 2 => FreeGroup.of true

/-- The explicit transition. Its values outside the overlap play no role
in the topology of the covering. -/
def freeGroupTransition (z : TwicePuncturedPlane) : FreeGroup Bool :=
  if (z : ℂ).re < 0 then (FreeGroup.of false)⁻¹
  else if (z : ℂ).re < 1 then 1 else FreeGroup.of true

/-- The transition is constant on each of the three actual overlap strips. -/
theorem freeGroupTransition_eqOn_strip (i : Fin 3) :
    EqOn freeGroupTransition (fun _ => freeGroupTransitionValue i)
      (slitOverlapStrip i : Set TwicePuncturedPlane) := by
  intro z hz
  fin_cases i
  · have hneg : (z : ℂ).re < 0 := hz
    simp only [freeGroupTransition, if_pos hneg, freeGroupTransitionValue]
  · have hmid : 0 < (z : ℂ).re ∧ (z : ℂ).re < 1 := hz
    simp only [freeGroupTransition, if_neg (not_lt.mpr hmid.1.le), if_pos hmid.2,
      freeGroupTransitionValue]
  · have hpos : 1 < (z : ℂ).re := hz
    have hnonneg : ¬(z : ℂ).re < 0 := by linarith
    simp only [freeGroupTransition, if_neg hnonneg, if_neg (not_lt.mpr hpos.le),
      freeGroupTransitionValue]

/-- Local constancy on the open strips proves continuity on the entire
overlap, including arbitrary heights in each component. -/
theorem freeGroupTransition_continuousOn :
    ContinuousOn freeGroupTransition
      ((upperSlit : Set TwicePuncturedPlane) ∩ lowerSlit) := by
  apply continuousOn_of_locally_continuousOn
  intro z hz
  have hz' : z ∈ ⋃ i : Fin 3, (slitOverlapStrip i : Set TwicePuncturedPlane) := by
    rw [slitOverlapStrip_iUnion]
    exact hz
  obtain ⟨i, hi⟩ := mem_iUnion.mp hz'
  refine ⟨slitOverlapStrip i, (slitOverlapStrip i).isOpen, hi, ?_⟩
  apply (continuousOn_const (c := freeGroupTransitionValue i)).congr
  intro w hw
  exact freeGroupTransition_eqOn_strip i hw.2

/-- The actual two-chart transition datum defining the free-group covering. -/
def freeGroupCover : TwoOpenTransition TwicePuncturedPlane (FreeGroup Bool) where
  U := upperSlit
  V := lowerSlit
  cover := upperSlit_union_lowerSlit
  transition := freeGroupTransition
  continuousOn_transition := freeGroupTransition_continuousOn

@[simp] theorem freeGroupCover_U : freeGroupCover.U = upperSlit := rfl

@[simp] theorem freeGroupCover_V : freeGroupCover.V = lowerSlit := rfl

@[simp] theorem freeGroupCover_transition : freeGroupCover.transition = freeGroupTransition := rfl

/-- The transition construction supplies a genuine covering projection. -/
theorem freeGroupCover_isCoveringMap : IsCoveringMap freeGroupCover.proj :=
  freeGroupCover.isCoveringMap

@[simp] theorem freeGroupTransition_basepoint :
    freeGroupTransition meridianBasepoint = 1 := by
  norm_num [freeGroupTransition, meridianBasepoint]

@[simp] theorem freeGroupTransition_leftPoint :
    freeGroupTransition meridianLeftPoint = (FreeGroup.of false)⁻¹ := by
  norm_num [freeGroupTransition, meridianLeftPoint]

@[simp] theorem freeGroupTransition_rightPoint :
    freeGroupTransition meridianRightPoint = FreeGroup.of true := by
  norm_num [freeGroupTransition, meridianRightPoint]

theorem freeGroupCover_basepoint_mem :
    meridianBasepoint ∈ (freeGroupCover.U : Set TwicePuncturedPlane) ∩ freeGroupCover.V := by
  change (meridianBasepoint : ℂ) ∈ upperSlitPlane ∩ lowerSlitPlane
  rw [slitPlanes_inter]
  norm_num [meridianBasepoint]

theorem freeGroupCover_leftPoint_mem :
    meridianLeftPoint ∈ (freeGroupCover.U : Set TwicePuncturedPlane) ∩ freeGroupCover.V := by
  change (meridianLeftPoint : ℂ) ∈ upperSlitPlane ∩ lowerSlitPlane
  rw [slitPlanes_inter]
  norm_num [meridianLeftPoint]

theorem freeGroupCover_rightPoint_mem :
    meridianRightPoint ∈ (freeGroupCover.U : Set TwicePuncturedPlane) ∩ freeGroupCover.V := by
  change (meridianRightPoint : ℂ) ∈ upperSlitPlane ∩ lowerSlitPlane
  rw [slitPlanes_inter]
  norm_num [meridianRightPoint]

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
