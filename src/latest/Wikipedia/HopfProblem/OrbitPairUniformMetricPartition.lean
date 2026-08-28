import Wikipedia.NoExoticSixSphere.CompactParameter
import Wikipedia.NoExoticSixSphere.UniformUnitIntervalPartition
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Uniform metric control for compact continuous path families

A finite uniform subdivision makes every prefix in each cell uniformly close
to the left endpoint, simultaneously for a compact parameter space. The target
can be any pseudometric space. No differentiability or energy bound is used.
-/

open Set unitInterval

namespace Wikipedia.HopfProblem.OrbitPair.UniformMetricPartition

open NoExoticSixSphere UniformTimePartition

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [PseudoMetricSpace Y]

theorem exists_uniform_partition (H : C(I × X, Y)) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ ∀ i : Fin (m + 1),
      ∀ u ∈ Icc (unitTime m i.castSucc) (unitTime m i.succ), ∀ x,
        dist (H (u, x)) (H (unitTime m i.castSucc, x)) < ε := by
  let V (s : I) : Set I := {t | ∀ x, dist (H (t, x)) (H (s, x)) < ε / 2}
  have hV : ∀ s, IsOpen (V s) := by
    intro s
    have hs : Continuous (fun p : I × X => H (s, p.2)) :=
      H.continuous.comp (continuous_const.prodMk continuous_snd)
    exact isOpen_forall_compact (isOpen_lt (H.continuous.dist hs) continuous_const)
  have hcover : univ ⊆ ⋃ s, V s := by
    intro s _
    refine mem_iUnion.mpr ⟨s, ?_⟩
    intro x
    simpa only [dist_self] using half_pos hε
  obtain ⟨δ, hδ, hcoverBall⟩ := lebesgue_number_lemma_of_metric isCompact_univ hV hcover
  obtain ⟨m, hNm, hmesh⟩ := exists_mesh_lt_above δ hδ N
  refine ⟨m, hNm, ?_⟩
  intro i u hu x
  obtain ⟨s, hs⟩ := hcoverBall (unitTime m i.castSucc) (mem_univ _)
  have hux := hs ((dist_left_le_step m i hu).trans_lt hmesh) x
  have hlx := hs (Metric.mem_ball_self hδ) x
  have htri := dist_triangle (H (u, x)) (H (s, x)) (H (unitTime m i.castSucc, x))
  rw [dist_comm (H (s, x)) (H (unitTime m i.castSucc, x))] at htri
  linarith

end Wikipedia.HopfProblem.OrbitPair.UniformMetricPartition
