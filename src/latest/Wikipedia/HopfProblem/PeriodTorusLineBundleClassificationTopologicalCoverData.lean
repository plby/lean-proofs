import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNativeData
import Wikipedia.HopfProblem.PeriodTori
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.Contractible

/-!
# A convex trivializing cover of a native line bundle on `ℂ²`

Each point receives a positive-radius ball contained in its original native
trivializing set. The scalar transitions are the original native coordinate
changes, restricted to this ball cover. All finite intersections are open and
convex. No logarithmic cocycle or global frame is assumed.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTopological

open HolomorphicCharacterBundle
open PeriodTorusLineBundleClassificationNative

variable (V : ComplexPlane₂ → Type*)
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V]

theorem exists_ball_in_nativeTriv (x : ComplexPlane₂) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ (nativeTriv V x).baseSet :=
  Metric.mem_nhds_iff.mp ((nativeTriv V x).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt ℂ V x))

/-- A positive radius chosen inside the existing native trivializing set. -/
def coverRadius (x : ComplexPlane₂) : ℝ := (exists_ball_in_nativeTriv V x).choose

theorem coverRadius_pos (x : ComplexPlane₂) : 0 < coverRadius V x :=
  (exists_ball_in_nativeTriv V x).choose_spec.1

theorem ball_subset_nativeTriv (x : ComplexPlane₂) :
    Metric.ball x (coverRadius V x) ⊆ (nativeTriv V x).baseSet :=
  (exists_ball_in_nativeTriv V x).choose_spec.2

variable [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)] [VectorBundle ℂ ℂ V]

/-- The genuine scalar cocycle on a refinement by open convex balls. -/
def ballData : TransitionData ComplexPlane₂ ComplexPlane₂ where
  baseSet x := Metric.ball x (coverRadius V x)
  isOpen_baseSet _ := Metric.isOpen_ball
  indexAt := id
  mem_baseSet_at x := Metric.mem_ball_self (coverRadius_pos V x)
  transition := scalarTransition V
  transition_self i x hx := scalarTransition_self V i x (ball_subset_nativeTriv V i hx)
  transition_comp i j k x hx := scalarTransition_comp V i j k x
    ⟨⟨ball_subset_nativeTriv V i hx.1.1, ball_subset_nativeTriv V j hx.1.2⟩,
      ball_subset_nativeTriv V k hx.2⟩
  continuousOn_transition i j := (scalarTransition_continuousOn V i j).mono
    (fun _ hx => ⟨ball_subset_nativeTriv V i hx.1, ball_subset_nativeTriv V j hx.2⟩)

@[simp] theorem ballData_baseSet (x : ComplexPlane₂) :
    (ballData V).baseSet x = Metric.ball x (coverRadius V x) := rfl

@[simp] theorem ballData_indexAt (x : ComplexPlane₂) : (ballData V).indexAt x = x := rfl

@[simp] theorem ballData_transition (i j x : ComplexPlane₂) :
    (ballData V).transition i j x = scalarTransition V i j x := rfl

theorem ballData_baseSet_convex (x : ComplexPlane₂) :
    Convex ℝ ((ballData V).baseSet x) := convex_ball x (coverRadius V x)

theorem ballData_overlap_convex (i j : ComplexPlane₂) :
    Convex ℝ ((ballData V).baseSet i ∩ (ballData V).baseSet j) :=
  (ballData_baseSet_convex V i).inter (ballData_baseSet_convex V j)

theorem ballData_finite_intersection_convex (s : Finset ComplexPlane₂) :
    Convex ℝ (⋂ i ∈ s, (ballData V).baseSet i) :=
  convex_iInter fun i => convex_iInter fun _ => ballData_baseSet_convex V i

theorem ballData_finite_intersection_isOpen (s : Finset ComplexPlane₂) :
    IsOpen (⋂ i ∈ s, (ballData V).baseSet i) :=
  s.finite_toSet.isOpen_biInter fun i _ => (ballData V).isOpen_baseSet i

/-- Every nonempty finite overlap is genuinely contractible in its subtype
topology, as required for local logarithmic transition lifts. -/
theorem ballData_finite_intersection_contractible (s : Finset ComplexPlane₂)
    (hne : (⋂ i ∈ s, (ballData V).baseSet i).Nonempty) :
    ContractibleSpace (⋂ i ∈ s, (ballData V).baseSet i : Set ComplexPlane₂) :=
  (ballData_finite_intersection_convex V s).contractibleSpace hne

local notation "I₀" => modelWithCornersSelf ℂ ComplexPlane₂

variable [ContMDiffVectorBundle ω ℂ V I₀]

instance ballData_isHolomorphic : (ballData V).IsHolomorphic I₀ where
  contMDiffOn_transition i j := (scalarTransition_holomorphic V I₀ i j).mono
    (fun _ hx => ⟨ball_subset_nativeTriv V i hx.1, ball_subset_nativeTriv V j hx.2⟩)

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTopological
