import Wikipedia.HopfProblem.PeriodTorusAppellHumbertCoreCharts
import Wikipedia.HopfProblem.HolomorphicCharacterBundleCore

/-!
# The holomorphic bundle core of a factor of automorphy

The local lifts are charts in the existing period-torus atlas. Evaluating
the factor on their deck difference gives the scalar transition from the
first fibre coordinate to the second. The actual cocycle law gives a
vector bundle, and local constancy of the deck difference proves that its
transition functions are holomorphic. No triviality or coboundary is assumed.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusAppellHumbert.Core

open HolomorphicCharacterBundle

variable {p : PeriodDomain} (F : FactorOfAutomorphy p)

/-- On an overlap, the analytic transition is locally evaluation at one
fixed lattice element; the base point in the factor still varies. -/
theorem transition_locally_eq (i j : p.Torus) {x : p.Torus}
    (hx : x ∈ baseSet p i ∩ baseSet p j) :
    (fun y => (F.factor (deck p i j y) (lift p i y) : ℂ)) =ᶠ[𝓝 x]
      (fun y => (F.factor (deck p i j x) (lift p i y) : ℂ)) := by
  filter_upwards [deck_locally_constant p i j hx] with y hy
  rw [hy]

theorem transition_holomorphic (i j : p.Torus) :
    ContMDiffOn (modelWithCornersSelf ℂ ComplexPlane₂) (modelWithCornersSelf ℂ ℂ) ω
      (fun x => (F.factor (deck p i j x) (lift p i x) : ℂ))
      (baseSet p i ∩ baseSet p j) := by
  intro x hx
  have hi := (lift_holomorphic p i).contMDiffAt ((isOpen_baseSet p i).mem_nhds hx.1)
  have hF := (F.holomorphic_factor (deck p i j x)).contMDiff.contMDiffAt
    (x := lift p i x)
  exact ((hF.comp x hi).congr_of_eventuallyEq
    (transition_locally_eq F i j hx)).contMDiffWithinAt

/-- The genuine factor cocycle on the existing torus cover. -/
def data : TransitionData p.Torus p.Torus where
  baseSet := baseSet p
  isOpen_baseSet := isOpen_baseSet p
  indexAt := id
  mem_baseSet_at := mem_baseSet p
  transition i j x := F.factor (deck p i j x) (lift p i x)
  transition_self i x hx := by rw [deck_self p i hx, F.factor_zero]
  transition_comp i j k x hx := by
    rw [← deck_spec p i j hx.1, ← F.factor_add, deck_comp p i j k hx]
  continuousOn_transition i j := (transition_holomorphic F i j).continuousOn

@[simp] theorem data_baseSet (i : p.Torus) : (data F).baseSet i = baseSet p i := rfl

@[simp] theorem data_indexAt (x : p.Torus) : (data F).indexAt x = x := rfl

@[simp] theorem data_transition (i j x : p.Torus) :
    (data F).transition i j x = F.factor (deck p i j x) (lift p i x) := rfl

instance data_isHolomorphic :
    (data F).IsHolomorphic (modelWithCornersSelf ℂ ComplexPlane₂) where
  contMDiffOn_transition := transition_holomorphic F

/-- The bundle topology and the analytic vector-bundle structure come
from the proved transition data. -/
theorem core_contMDiffVectorBundle :
    ContMDiffVectorBundle ω ℂ (data F).core.Fiber
      (modelWithCornersSelf ℂ ComplexPlane₂) :=
  inferInstance

/-- Its genuine bundle total space is a complex threefold. -/
theorem core_totalSpace_isManifold :
    IsManifold ((modelWithCornersSelf ℂ ComplexPlane₂).prod (modelWithCornersSelf ℂ ℂ))
      ω (data F).core.TotalSpace :=
  inferInstance

end Wikipedia.HopfProblem.PeriodTorusAppellHumbert.Core
