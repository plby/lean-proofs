import ErdosProblems.Erdos556.CubeEquality
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas

/-! Approximate profile constraints and their exact limits. -/

namespace Erdos556

open Finset Filter
open scoped Topology

structure ApproxCubeWeight (w : CubeProfile → ℝ) (δ : ℝ) : Prop where
  nonneg : ∀ p, 0 ≤ w p
  sum_close : |∑ p, w p - 4| ≤ δ
  vertex_small : ∀ p, profileDimension p = 0 → w p ≤ δ
  edge_bound : ∀ p, profileDimension p = 1 → w p ≤ 1 + δ
  incompatible_small : ∀ p q, (profileVertices p ∩ profileVertices q).card = 1 → w p * w q ≤ δ
  energy_small : cubeEnergy w ≤ δ

theorem ApproxCubeWeight.mono {w : CubeProfile → ℝ} {δ ε : ℝ}
    (h : ApproxCubeWeight w δ) (hδε : δ ≤ ε) : ApproxCubeWeight w ε := by
  refine ⟨h.nonneg, h.sum_close.trans hδε, ?_, ?_, ?_, h.energy_small.trans hδε⟩
  · intro p hp
    exact (h.vertex_small p hp).trans hδε
  · intro p hp
    exact (h.edge_bound p hp).trans (add_le_add le_rfl hδε)
  · intro p q hpq
    exact (h.incompatible_small p q hpq).trans hδε

theorem ApproxCubeWeight.le_five {w : CubeProfile → ℝ} {δ : ℝ}
    (h : ApproxCubeWeight w δ) (hδ : δ ≤ 1) (p : CubeProfile) : w p ≤ 5 := by
  have hsum := (abs_le.mp h.sum_close).2
  have hp : w p ≤ ∑ q, w q := single_le_sum (fun q _ => h.nonneg q) (mem_univ p)
  linarith

theorem ApproxCubeWeight.exact_of_zero {w : CubeProfile → ℝ} (h : ApproxCubeWeight w 0) :
    IsCubeWeight w ∧ IsCubeTiling w := by
  have hw : IsCubeWeight w := by
    refine ⟨h.nonneg, ?_, ?_, ?_, ?_⟩
    · have hs := abs_le.mp h.sum_close
      linarith
    · intro p hp
      exact le_antisymm (h.vertex_small p hp) (h.nonneg p)
    · intro p hp
      simpa only [add_zero] using h.edge_bound p hp
    · intro p q hp hq heq
      have hmul := h.incompatible_small p q heq
      exact (not_lt_of_ge hmul) (mul_pos hp hq)
  exact ⟨hw, cube_tiling_of_zero_energy w hw (le_antisymm h.energy_small (cube_energy_nonneg w hw))⟩

theorem continuous_cubeEnergy : Continuous cubeEnergy := by
  unfold cubeEnergy
  fun_prop

theorem approximate_cube_limit {w : ℕ → CubeProfile → ℝ} {δ : ℕ → ℝ} {v : CubeProfile → ℝ}
    (hw : ∀ n, ApproxCubeWeight (w n) (δ n))
    (hδ : Tendsto δ atTop (𝓝 0)) (hv : Tendsto w atTop (𝓝 v)) :
    IsCubeWeight v ∧ IsCubeTiling v := by
  have hp (p : CubeProfile) : Tendsto (fun n => w n p) atTop (𝓝 (v p)) :=
    (tendsto_pi_nhds.mp hv) p
  have hs : Tendsto (fun n => ∑ p, w n p) atTop (𝓝 (∑ p, v p)) :=
    tendsto_finsetSum univ (fun p _ => hp p)
  have he : Tendsto (fun n => cubeEnergy (w n)) atTop (𝓝 (cubeEnergy v)) :=
    (continuous_cubeEnergy.tendsto v).comp hv
  apply ApproxCubeWeight.exact_of_zero
  constructor
  · intro p
    exact ge_of_tendsto' (hp p) (fun n => (hw n).nonneg p)
  · exact le_of_tendsto_of_tendsto' ((hs.sub_const 4).abs) hδ (fun n => (hw n).sum_close)
  · intro p hd
    exact le_of_tendsto_of_tendsto' (hp p) hδ (fun n => (hw n).vertex_small p hd)
  · intro p hd
    have h := le_of_tendsto_of_tendsto' (hp p) (tendsto_const_nhds.add hδ)
      (fun n => (hw n).edge_bound p hd)
    simpa only [add_zero] using h
  · intro p q hbad
    exact le_of_tendsto_of_tendsto' ((hp p).mul (hp q)) hδ
      (fun n => (hw n).incompatible_small p q hbad)
  · exact le_of_tendsto_of_tendsto' he hδ (fun n => (hw n).energy_small)

#print axioms approximate_cube_limit

end Erdos556
