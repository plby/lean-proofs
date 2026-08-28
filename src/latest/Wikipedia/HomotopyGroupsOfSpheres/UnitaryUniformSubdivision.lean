import Wikipedia.HomotopyGroupsOfSpheres.UnitaryCompatibleLogarithm
import Wikipedia.NoExoticSixSphere.OrthogonalUniformSubdivision

/-! # Uniform subdivisions of compact complex unitary path families -/

noncomputable section

open scoped Matrix.Norms.Frobenius Topology unitInterval
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexSkewMatrices.CompatibleLog

open NoExoticSixSphere.UniformTimePartition

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem dist_left_increment (U V : unitary (Matrix N N ℂ)) :
    dist (U⁻¹ * V) 1 = dist V U := by
  change dist ((U⁻¹).val * V.val) (1 : Matrix N N ℂ) = dist V.val U.val
  rw [dist_eq_norm, dist_eq_norm]
  have hm : (U⁻¹).val * (V.val - U.val) = (U⁻¹).val * V.val - 1 := by
    rw [mul_sub]
    have h : (U⁻¹).val * U.val = 1 := congrArg Subtype.val (inv_mul_cancel U)
    rw [h]
  rw [← hm, ComplexMatrixRealRepresentation.frobenius_norm_unitary_left]

theorem exists_uniform_increment_partition {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (H : C(I × X, unitary (Matrix N N ℂ))) (U : Set (unitary (Matrix N N ℂ)))
    (hU : U ∈ nhds (1 : unitary (Matrix N N ℂ))) (lower : ℕ) :
    ∃ m : ℕ, lower ≤ m ∧ ∀ i : Fin (m + 1),
      ∀ u ∈ Icc (unitTime m i.castSucc) (unitTime m i.succ), ∀ x,
        (H (unitTime m i.castSucc, x))⁻¹ * H (u, x) ∈ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  let V (s : I) : Set I := {t | ∀ x, dist (H (t, x)) (H (s, x)) < ε / 2}
  have hV : ∀ s, IsOpen (V s) := by
    intro s
    have hs : Continuous (fun p : I × X ↦ H (s, p.2)) :=
      H.continuous.comp (continuous_const.prodMk continuous_snd)
    exact NoExoticSixSphere.isOpen_forall_compact
      (isOpen_lt (H.continuous.dist hs) continuous_const)
  have hcover : univ ⊆ ⋃ s, V s := by
    intro s _
    refine mem_iUnion.mpr ⟨s, ?_⟩
    intro x
    simpa only [dist_self] using half_pos hε
  obtain ⟨δ, hδ, hcoverBall⟩ := lebesgue_number_lemma_of_metric isCompact_univ hV hcover
  obtain ⟨m, hNm, hmesh⟩ := exists_mesh_lt_above δ hδ lower
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

end Wikipedia.HomotopyGroupsOfSpheres.ComplexSkewMatrices.CompatibleLog
