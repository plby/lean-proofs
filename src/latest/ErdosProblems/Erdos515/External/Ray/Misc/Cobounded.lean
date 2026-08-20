module
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Bornology.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Order.Directed
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.MetricSpace.Basic
import ErdosProblems.Erdos515.External.Ray.Misc.Bound
import ErdosProblems.Erdos515.External.Ray.Misc.Topology

/-!
## Facts about `Bornology.cobounded`
-/

open Bornology (cobounded)
open Filter (Tendsto atTop)
open Metric (ball closedBall)
open Set
open scoped Topology

variable {α : Type}
variable {X : Type} [NormedAddCommGroup X]
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

/-- `Filter.hasBasis_cobounded_norm` but with `r < ‖x‖` instead of `r ≤ ‖x‖` -/
public lemma hasBasis_cobounded_norm_lt :
    (cobounded X).HasBasis (fun _ ↦ True) (fun r ↦ {x | r < ‖x‖}) := by
  have b := Filter.hasBasis_cobounded_norm (E := X)
  simp only [Filter.hasBasis_iff, ofPred_subset, true_and] at b ⊢
  intro s
  rw [b s]
  constructor
  all_goals exact fun ⟨r, h⟩ ↦ ⟨r + 1, fun x lt ↦ h x (by linarith)⟩

/-- Characterization of `→ cobounded` convergence -/
public theorem tendsto_cobounded {f : α → X} {l : Filter α} :
    Tendsto f l (cobounded X) ↔ ∀ r, ∀ᶠ x in l, r < ‖f x‖ := by
  rw [hasBasis_cobounded_norm_lt.tendsto_right_iff]
  simp only [true_imp_iff, mem_ofPred]

/-- Characterization of `atTop → cobounded` convergence -/
theorem tendsto_atTop_cobounded {f : ℕ → X} :
    Tendsto f atTop (cobounded X) ↔ ∀ r, ∃ N, ∀ n, N ≤ n → r < ‖f n‖ := by
  simpa only [mem_Ici, mem_ofPred_eq, exists_true_left, forall_true_left, true_and] using
    Filter.HasBasis.tendsto_iff (f := f) Filter.atTop_basis hasBasis_cobounded_norm_lt

/-- `cobounded` convergence in terms of norm convergence -/
public theorem tendsto_cobounded_iff_norm_tendsto_atTop {f : Filter α} {g : α → X} :
    Tendsto (fun x ↦ g x) f (cobounded X) ↔ Tendsto (fun x ↦ ‖g x‖) f atTop := by
  rw [Filter.atTop_basis_Ioi.tendsto_right_iff]
  simp only [hasBasis_cobounded_norm_lt.tendsto_right_iff, true_imp_iff, mem_ofPred, mem_Ioi]

/-- Characterization of `s ∈ cobounded` -/
theorem mem_cobounded_iff {s : Set X} : s ∈ cobounded X ↔ ∃ r, {x | r < ‖x‖} ⊆ s := by
  simp only [Filter.hasBasis_iff.mp hasBasis_cobounded_norm_lt s, true_and]

/-- Eventually `cobounded` the norm is as large as desired -/
public theorem eventually_cobounded (r : ℝ) : ∀ᶠ x : X in cobounded X, r < ‖x‖ := by
  rw [Filter.eventually_iff, mem_cobounded_iff]; use r

/-- Eventually `cobounded` is the same as eventually `𝓝[≠] 0` for `x⁻¹` -/
public theorem eventually_cobounded_iff_nhds_zero {p : 𝕜 → Prop} :
    (∀ᶠ x in cobounded 𝕜, p x) ↔ ∀ᶠ x in 𝓝[≠] 0, p x⁻¹ := by
  rw [hasBasis_cobounded_norm_lt.eventually_iff, Metric.nhdsWithin_basis_ball.eventually_iff]
  constructor
  · intro ⟨r,_,h⟩
    refine ⟨(max r 1)⁻¹, by bound, fun x ⟨m,x0⟩ ↦ ?_⟩
    refine @h x⁻¹ ?_
    simp only [Metric.mem_ball, dist_zero_right, mem_compl_iff, mem_singleton_iff, mem_ofPred_eq,
      norm_inv] at m x0 ⊢
    rw [← lt_inv_comm₀ (by bound) (by simpa)] at m
    exact lt_of_le_of_lt (le_max_left _ _) m
  · intro ⟨i,i0,h⟩
    refine ⟨i⁻¹, trivial, fun x m ↦ ?_⟩
    refine inv_inv x ▸ @h x⁻¹ ?_
    simp only [mem_ofPred_eq, mem_inter_iff, Metric.mem_ball, dist_zero_right, norm_inv,
      mem_compl_iff, mem_singleton_iff, inv_eq_zero] at m ⊢
    have x0 : x ≠ 0 := by have : 0 < ‖x‖ := lt_trans (by bound) m; simpa
    rw [← inv_lt_comm₀ i0 (by simpa)]
    exact ⟨m, x0⟩

/-- Convergence `cobounded` is the same as convergence at `0` for the reciprocal function -/
public theorem tendsto_cobounded_iff_tendsto_nhds_zero {l : Filter α}
    {f : 𝕜 → α} : Tendsto f (cobounded 𝕜) l ↔ Tendsto (fun x ↦ f x⁻¹) (𝓝[{0}ᶜ] 0) l := by
  rw [Filter.HasBasis.tendsto_left_iff hasBasis_cobounded_norm_lt,
    Metric.nhdsWithin_basis_ball.tendsto_left_iff]
  constructor
  · intro h t tl; rcases h t tl with ⟨r, _, m⟩
    by_cases rp : 0 < r
    · use r⁻¹; simp only [rp, inv_pos, true_and]; intro x xs; refine m ?_
      simp only [mem_inter_iff, mem_ball_zero_iff, mem_compl_iff, mem_singleton_iff] at xs
      simp only [← lt_inv_comm₀ (norm_pos_iff.mpr xs.2) rp, xs.1, mem_ofPred_eq, norm_inv]
    · use 1; simp only [zero_lt_one, true_and]; intro x xs; refine m ?_
      simp only [mem_inter_iff, mem_ball_zero_iff, mem_compl_iff, mem_singleton_iff] at xs
      simp only [mem_ofPred_eq, norm_inv]; simp only [not_lt] at rp
      exact lt_of_le_of_lt rp (inv_pos.mpr (norm_pos_iff.mpr xs.2))
  · intro h t tl; rcases h t tl with ⟨r, rp, m⟩; use r⁻¹; simp only [true_and]
    intro x xs; simp only [mem_ofPred_eq] at xs
    have m := @m x⁻¹ ?_; · simp only [inv_inv] at m; exact m
    simp only [mem_inter_iff, mem_ball_zero_iff, norm_inv, mem_compl_iff, mem_singleton_iff,
      inv_eq_zero]
    have np : 0 < ‖x‖ := _root_.trans (inv_pos.mpr rp) xs
    simp [inv_lt_comm₀ np rp, xs, norm_pos_iff.mp np]

/-- `⁻¹` tendsto `cobounded` near `0` -/
public theorem inv_tendsto_cobounded :
    Tendsto (fun x : 𝕜 ↦ x⁻¹) (𝓝[{(0 : 𝕜)}ᶜ] 0) (cobounded 𝕜) := by
  rw [← tendsto_cobounded_iff_tendsto_nhds_zero (f := fun x : 𝕜 ↦ x)]
  exact Filter.tendsto_id

/-- `⁻¹` tendsto `0` near `cobounded` -/
public theorem inv_tendsto_cobounded' :
    Tendsto (fun x : 𝕜 ↦ x⁻¹) (cobounded 𝕜) (𝓝 0) := by
  simp only [tendsto_cobounded_iff_tendsto_nhds_zero, inv_inv]
  exact Filter.tendsto_id.mono_left nhdsWithin_le_nhds

/-- We either tend to infinity or have a cluster point -/
public lemma tendsto_cobounded_or_mapClusterPt [ProperSpace X] (f : α → X) (l : Filter α) :
    Tendsto f l (cobounded X) ∨ ∃ z, MapClusterPt z l f := by
  by_cases t : Tendsto f l (cobounded X)
  · exact .inl t
  · simp only [t, false_or]
    simp only [tendsto_cobounded, not_forall, Filter.not_eventually, not_lt,
      ← add_mem_closedBall_iff_norm (a := (0 : X)), zero_add] at t
    obtain ⟨r,t⟩ := t
    have t := IsCompact.exists_mapClusterPt_of_frequently (isCompact_closedBall _ _) t
    obtain ⟨z,m,c⟩ := t
    exact ⟨z,c⟩

public lemma eventually_cobounded_lt_norm (r : ℝ) : ∀ᶠ x in cobounded X, r < ‖x‖ := by
  filter_upwards [eventually_cobounded_le_norm (r + 1)]
  intro x le
  linarith
