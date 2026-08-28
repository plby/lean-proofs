import Wikipedia.HomotopyGroupsOfSpheres.ComplexSkewMatrices
import Wikipedia.NoExoticSixSphere.OrthogonalCompactLogarithm

/-! # A uniform neighborhood where complex and real orthogonal logarithms agree -/

noncomputable section

open scoped Matrix.Norms.Frobenius Topology
open Set Metric Filter

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexSkewMatrices.CompatibleLog

variable {N : Type*} [Fintype N] [DecidableEq N]

def target (N : Type*) [Fintype N] [DecidableEq N] : Set (Space N) :=
  {K | K.val ∈ (ComplexMatrixLocalLogarithm.exponentialChart N).source ∧
    toOrthogonalSkew K ∈
      (NoExoticSixSphere.OrthogonalExponential.logarithmChart (2 * Fintype.card N)).target ∧
    ‖toOrthogonalSkew K‖ < Real.pi}

theorem isOpen_target : IsOpen (target N) :=
  ((ComplexMatrixLocalLogarithm.exponentialChart N).open_source.preimage
    continuous_subtype_val).inter
    (((NoExoticSixSphere.OrthogonalExponential.logarithmChart
      (2 * Fintype.card N)).open_target.preimage continuous_toOrthogonalSkew).inter
      (isOpen_lt continuous_toOrthogonalSkew.norm continuous_const))

theorem zero_mem_target : (0 : Space N) ∈ target N := by
  refine ⟨ComplexMatrixLocalLogarithm.zero_mem_source, ?_, ?_⟩
  · rw [map_zero]
    exact NoExoticSixSphere.OrthogonalExponential.zero_mem_logarithmChart_target _
  · rw [map_zero, norm_zero]
    exact Real.pi_pos

theorem exists_radius : ∃ r : ℝ, 0 < r ∧ r < ComplexMatrixLocalLogarithm.radius N ∧
    closedBall (0 : Space N) r ⊆ target N := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (isOpen_target.mem_nhds (zero_mem_target (N := N)))
  let r := min (ε / 2) (ComplexMatrixLocalLogarithm.radius N / 2)
  have hr : 0 < r := lt_min (by linarith)
    (half_pos (ComplexMatrixLocalLogarithm.radius_pos (N := N)))
  have hrε : r < ε := (min_le_left _ _).trans_lt (by linarith)
  have hrr : r < ComplexMatrixLocalLogarithm.radius N :=
    (min_le_right _ _).trans_lt (half_lt_self (ComplexMatrixLocalLogarithm.radius_pos (N := N)))
  refine ⟨r, hr, hrr, ?_⟩
  intro K hK
  exact hball (lt_of_le_of_lt hK hrε)

def radius (N : Type*) [Fintype N] [DecidableEq N] : ℝ :=
  Classical.choose (exists_radius (N := N))

theorem radius_pos : 0 < radius N := (Classical.choose_spec (exists_radius (N := N))).1

theorem radius_lt : radius N < ComplexMatrixLocalLogarithm.radius N :=
  (Classical.choose_spec (exists_radius (N := N))).2.1

theorem radius_closedBall : closedBall (0 : Space N) (radius N) ⊆ target N :=
  (Classical.choose_spec (exists_radius (N := N))).2.2

def domain (N : Type*) [Fintype N] [DecidableEq N] : Set (unitary (Matrix N N ℂ)) :=
  {U | U.val ∈ ComplexMatrixLocalLogarithm.domain N ∧ ‖logarithm U‖ < radius N}

theorem isOpen_domain : IsOpen (domain N) := by
  apply isOpen_iff_mem_nhds.mpr
  intro U hU
  have hs : {V : unitary (Matrix N N ℂ) | V.val ∈ ComplexMatrixLocalLogarithm.domain N} ∈
      𝓝 U := (ComplexMatrixLocalLogarithm.isOpen_domain.preimage
        continuous_subtype_val).mem_nhds hU.1
  have hc : ContinuousAt (logarithm (N := N)) U := continuousOn_logarithm.continuousAt hs
  have hn := hc.norm (Iio_mem_nhds hU.2)
  filter_upwards [hs, hn] with V hV hv
  exact ⟨hV, hv⟩

theorem one_mem_domain : (1 : unitary (Matrix N N ℂ)) ∈ domain N := by
  refine ⟨ComplexMatrixLocalLogarithm.one_mem_domain, ?_⟩
  rw [logarithm_one, norm_zero]
  exact radius_pos

theorem logarithm_mem_target (U : unitary (Matrix N N ℂ)) (hU : U ∈ domain N) :
    logarithm U ∈ target N := by
  apply radius_closedBall (N := N)
  simpa only [mem_closedBall, dist_zero_right] using hU.2.le

theorem orthogonal_exp_logarithm (U : unitary (Matrix N N ℂ)) (hU : U ∈ domain N) :
    NoExoticSixSphere.OrthogonalExponential.exp (toOrthogonalSkew (logarithm U)) =
      ComplexMatrixRealRepresentation.orthogonal U := by
  rw [← orthogonal_exponential, exponential_logarithm U hU.1]

theorem orthogonal_mem_source (U : unitary (Matrix N N ℂ)) (hU : U ∈ domain N) :
    ComplexMatrixRealRepresentation.orthogonal U ∈
      (NoExoticSixSphere.OrthogonalExponential.logarithmChart (2 * Fintype.card N)).source := by
  rw [← orthogonal_exp_logarithm U hU]
  exact NoExoticSixSphere.OrthogonalExponential.exp_mem_logarithmChart_source _
    (logarithm_mem_target U hU).2.1

theorem orthogonal_logarithm_eq (U : unitary (Matrix N N ℂ)) (hU : U ∈ domain N) :
    NoExoticSixSphere.OrthogonalExponential.logarithmChart (2 * Fintype.card N)
      (ComplexMatrixRealRepresentation.orthogonal U) = toOrthogonalSkew (logarithm U) := by
  rw [← orthogonal_exp_logarithm U hU]
  exact NoExoticSixSphere.OrthogonalExponential.logarithmChart_exp _
    (logarithm_mem_target U hU).2.1

theorem inverse_mem_domain (U : unitary (Matrix N N ℂ)) (hU : U ∈ domain N) :
    U⁻¹ ∈ domain N := by
  refine ⟨(ComplexMatrixLocalLogarithm.logarithm_inverse U hU.1).1, ?_⟩
  rw [logarithm_inverse U hU.1, norm_neg]
  exact hU.2

theorem continuous_logarithm : Continuous (fun U : domain N ↦ logarithm U.val) :=
  continuousOn_logarithm.comp_continuous continuous_subtype_val (fun U ↦ U.property.1)

end Wikipedia.HomotopyGroupsOfSpheres.ComplexSkewMatrices.CompatibleLog
