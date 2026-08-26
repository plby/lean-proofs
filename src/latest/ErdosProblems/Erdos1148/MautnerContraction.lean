import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.Algebra.MulAction

/-! # A contraction form of the Mautner argument -/

namespace Erdos1148.DukeArithmetic

open Filter
open scoped Topology

theorem fixed_of_conjugates_tendsto_one {G X ι : Type*} [Group G] [TopologicalSpace G]
    [MetricSpace X] [MulAction G X] [ContinuousSMul G X] [IsIsometricSMul G X]
    {l : Filter ι} [l.NeBot] {g : ι → G} {u : G} {x : X}
    (hfixed : ∀ i, g i • x = x)
    (hconj : Tendsto (fun i => (g i)⁻¹ * u * g i) l (𝓝 1)) : u • x = x := by
  have hinv (i : ι) : (g i)⁻¹ • x = x := by
    calc
      (g i)⁻¹ • x = (g i)⁻¹ • (g i • x) := by rw [hfixed]
      _ = x := inv_smul_smul _ _
  have hdist (i : ι) : dist (((g i)⁻¹ * u * g i) • x) x = dist (u • x) x := by
    calc
      _ = dist ((g i)⁻¹ • (u • x)) ((g i)⁻¹ • x) := by
        simp only [mul_smul, hfixed, hinv]
      _ = _ := dist_smul _ _ _
  have haction : Tendsto (fun i => ((g i)⁻¹ * u * g i) • x) l (𝓝 x) := by
    simpa only [one_smul] using hconj.smul (tendsto_const_nhds (x := x))
  have hzero : Tendsto (fun _ : ι => dist (u • x) x) l (𝓝 0) := by
    simpa only [hdist, dist_self] using haction.dist (tendsto_const_nhds (x := x))
  exact dist_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hzero)

end Erdos1148.DukeArithmetic
