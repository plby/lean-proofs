module
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Order.PartialSups
public import Mathlib.Topology.MetricSpace.Basic
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

/-- `partialSups` is continuous -/
public theorem ContinuousOn.partialSups {A : Type} [TopologicalSpace A] {f : ℕ → A → ℝ} {s : Set A}
    (fc : ∀ n, ContinuousOn (f n) s) (n : ℕ) :
    ContinuousOn (fun x ↦ partialSups (fun k ↦ f k x) n) s := by
  induction' n with n h
  · simp only [partialSups_zero, fc 0]
  · simp only [← Order.succ_eq_add_one, partialSups_succ]
    exact ContinuousOn.max h (fc _)
