/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos254.SpectralMeasure

namespace Erdos254

open Filter MeasureTheory Set
open scoped BigOperators Topology

/-- Normalized geometric sums on the unit circle. The positive length avoids a
separate empty-average case. -/
noncomputable def circleAverage (N : ℕ) : C(Circle, ℂ) :=
  ((N + 1 : ℂ)⁻¹) • ∑ k ∈ Finset.range (N + 1), circleCoordinate ^ k

lemma circleAverage_apply (N : ℕ) (z : Circle) :
    circleAverage N z = (N + 1 : ℂ)⁻¹ * ∑ k ∈ Finset.range (N + 1), (z : ℂ) ^ k := by
  simp [circleAverage]

@[simp] lemma circleAverage_one (N : ℕ) : circleAverage N 1 = 1 := by
  rw [circleAverage_apply]
  simp only [Circle.coe_one, one_pow, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
  exact inv_mul_cancel₀ (by exact_mod_cast (Nat.succ_ne_zero N))

lemma norm_circleAverage_le_one (N : ℕ) (z : Circle) : ‖circleAverage N z‖ ≤ 1 := by
  rw [circleAverage_apply, norm_mul, norm_inv]
  have hsum : ‖∑ k ∈ Finset.range (N + 1), (z : ℂ) ^ k‖ ≤ (N + 1 : ℝ) := by
    calc
      _ ≤ ∑ k ∈ Finset.range (N + 1), ‖(z : ℂ) ^ k‖ := norm_sum_le _ _
      _ = N + 1 := by simp [norm_pow, Circle.norm_coe]
  have hnorm : ‖(N + 1 : ℂ)‖ = (N + 1 : ℝ) := by
    norm_cast
  rw [hnorm]
  calc
    _ ≤ (N + 1 : ℝ)⁻¹ * (N + 1) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 := inv_mul_cancel₀ (by positivity)

lemma tendsto_circleAverage_of_ne_one {z : Circle} (hz : z ≠ 1) :
    Tendsto (fun N ↦ circleAverage N z) atTop (𝓝 0) := by
  have hz' : (z : ℂ) ≠ 1 := fun h ↦ hz (Subtype.ext h)
  have hd : 0 < ‖(z : ℂ) - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz')
  have hbound (N : ℕ) :
      ‖circleAverage N z‖ ≤ (2 / ‖(z : ℂ) - 1‖) / (N + 1 : ℝ) := by
    rw [circleAverage_apply, geom_sum_eq hz', norm_mul, norm_inv, norm_div]
    have hnum : ‖(z : ℂ) ^ (N + 1) - 1‖ ≤ 2 := by
      calc
        _ ≤ ‖(z : ℂ) ^ (N + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by norm_num [norm_pow, Circle.norm_coe]
    have hnorm : ‖(N + 1 : ℂ)‖ = (N + 1 : ℝ) := by norm_cast
    rw [hnorm]
    calc
      _ ≤ (N + 1 : ℝ)⁻¹ * (2 / ‖(z : ℂ) - 1‖) := by gcongr
      _ = _ := by ring
  apply squeeze_zero_norm hbound
  exact tendsto_const_nhds.div_atTop
    (by simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))

lemma tendsto_integral_circleAverage_sq (μ : Measure Circle) [IsFiniteMeasure μ] :
    Tendsto (fun N ↦ ∫ z, ‖circleAverage N z‖ ^ 2 ∂μ) atTop (𝓝 (μ.real {1})) := by
  classical
  have hlim (z : Circle) : Tendsto (fun N ↦ ‖circleAverage N z‖ ^ 2) atTop
      (𝓝 (({1} : Set Circle).indicator (fun _ ↦ (1 : ℝ)) z)) := by
    by_cases hz : z = 1
    · subst z
      simp
    · simpa [hz] using (tendsto_circleAverage_of_ne_one hz).norm.pow 2
  have h := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ : Circle ↦ (1 : ℝ))
    (fun N ↦ ((circleAverage N).continuous.norm.pow 2).aestronglyMeasurable)
    (integrable_const 1) (fun N ↦ Filter.Eventually.of_forall (fun z ↦ ?_))
    (Filter.Eventually.of_forall hlim)
  · have hval : (∫ z, ({1} : Set Circle).indicator (fun _ ↦ (1 : ℝ)) z ∂μ) =
        μ.real {1} := by
      rw [integral_indicator (measurableSet_singleton 1)]
      simp [Measure.real]
    simpa only [hval, Pi.pow_apply] using h
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change ‖circleAverage N z‖ ^ 2 ≤ 1
    nlinarith [norm_circleAverage_le_one N z, norm_nonneg (circleAverage N z)]

section Unitary

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma inner_circleAverage_fixed (U : unitary (H →L[ℂ] H)) (v w : H)
    (hw : (U : H →L[ℂ] H) w = w) (N : ℕ) :
    inner ℂ w (circleRepresentation U (circleAverage N) v) = inner ℂ w v := by
  have hp (k : ℕ) : inner ℂ w (((U : H →L[ℂ] H) ^ k) v) = inner ℂ w v := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', mul_apply_eq_comp]
      nth_rw 1 [← hw]
      rw [Unitary.inner_map_map]
      exact ih
  have hN : (N + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
  calc
    _ = (N + 1 : ℂ)⁻¹ * ∑ k ∈ Finset.range (N + 1),
        inner ℂ w (((U : H →L[ℂ] H) ^ k) v) := by
      simp [circleAverage]
    _ = inner ℂ w v := by
      simp_rw [hp]
      simp [hN]

/-- A fixed unit vector forces a positive atom at `1` in the scalar spectral
measure. No spectral projection theorem is needed: normalized powers and
dominated convergence suffice. -/
theorem exists_unitary_spectral_measure_with_atom (U : unitary (H →L[ℂ] H)) (v w : H)
    (hw : (U : H →L[ℂ] H) w = w) (hwn : ‖w‖ = 1) :
    ∃ μ : Measure Circle, IsFiniteMeasure μ ∧
      (∀ n : ℕ, ∫ z, (z : ℂ) ^ n ∂μ = inner ℂ v (((U : H →L[ℂ] H) ^ n) v)) ∧
      ‖inner ℂ w v‖ ^ 2 ≤ μ.real {1} := by
  obtain ⟨μ, hfin, hmom, hsq⟩ := exists_unitary_spectral_measure U v
  have : IsFiniteMeasure μ := hfin
  refine ⟨μ, hfin, hmom, ge_of_tendsto (tendsto_integral_circleAverage_sq μ) ?_⟩
  apply Filter.Eventually.of_forall
  intro N
  rw [hsq]
  have hb := norm_inner_le_norm (𝕜 := ℂ) w (circleRepresentation U (circleAverage N) v)
  rw [inner_circleAverage_fixed U v w hw N, hwn, one_mul] at hb
  nlinarith [norm_nonneg (inner ℂ w v),
    norm_nonneg (circleRepresentation U (circleAverage N) v)]

end Unitary

end Erdos254
