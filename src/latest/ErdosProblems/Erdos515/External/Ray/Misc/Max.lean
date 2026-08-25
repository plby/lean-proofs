module
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Order.PartialSups
import Mathlib.Tactic.Cases

/-!
## Lemmas about `max` and `partialSups`
-/

open Set (univ)
noncomputable section

/-- `max` is continuous, `ContinuousOn` comp version -/
public theorem ContinuousOn.max {A : Type} [TopologicalSpace A] {f g : A → ℝ} {s : Set A}
    (fc : ContinuousOn f s) (gc : ContinuousOn g s) : ContinuousOn (fun x ↦ max (f x) (g x)) s :=
  continuous_max.comp_continuousOn (fc.prodMk gc)

/-- `max` is convex -/
public theorem convexOn_max : ConvexOn ℝ univ (fun p : ℝ × ℝ ↦ max p.1 p.2) := by
  apply ConvexOn.sup; · use convex_univ; intros; simp
  · use convex_univ; intros; simp
