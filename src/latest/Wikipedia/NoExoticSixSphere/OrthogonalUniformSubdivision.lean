import Wikipedia.NoExoticSixSphere.OrthogonalSmallLogarithm
import Wikipedia.NoExoticSixSphere.UniformUnitIntervalPartition

/-!
# Uniform finite subdivisions of compact orthogonal path families

Every prefix increment in every cell of a sufficiently fine uniform partition
lies in the prescribed identity neighborhood, simultaneously for the entire
compact family. The partition has distinct vertices and no repeated tail.
-/

open Set unitInterval

namespace NoExoticSixSphere.OrthogonalExponential

open GLOrthonormalization OrthogonalMetric UniformTimePartition

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X]

theorem exists_uniform_increment_partition (H : C(I × X, OrthogonalOperators n))
    (U : Set (OrthogonalOperators n)) (hU : U ∈ nhds (1 : OrthogonalOperators n)) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ ∀ i : Fin (m + 1),
      ∀ u ∈ Icc (unitTime m i.castSucc) (unitTime m i.succ), ∀ x,
        (H (unitTime m i.castSucc, x))⁻¹ * H (u, x) ∈ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  let V (s : I) : Set I := {t | ∀ x, dist (H (t, x)) (H (s, x)) < ε / 2}
  have hV : ∀ s, IsOpen (V s) := by
    intro s
    have hs : Continuous (fun p : I × X ↦ H (s, p.2)) :=
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
  apply hball
  rw [Metric.mem_ball, dist_left_increment]
  have htri := dist_triangle (H (u, x)) (H (s, x)) (H (unitTime m i.castSucc, x))
  rw [dist_comm (H (s, x)) (H (unitTime m i.castSucc, x))] at htri
  linarith

theorem exists_uniform_smallLogarithm_partition (H : C(I × X, OrthogonalOperators n))
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ ∀ i : Fin (m + 1),
      ∀ u ∈ Icc (unitTime m i.castSucc) (unitTime m i.succ), ∀ x,
        (H (unitTime m i.castSucc, x))⁻¹ * H (u, x) ∈ (logarithmChart n).source ∧
          ‖logarithmChart n ((H (unitTime m i.castSucc, x))⁻¹ * H (u, x))‖ < ε :=
  exists_uniform_increment_partition H _ (smallLogarithm_mem_nhds hε) N

end NoExoticSixSphere.OrthogonalExponential
