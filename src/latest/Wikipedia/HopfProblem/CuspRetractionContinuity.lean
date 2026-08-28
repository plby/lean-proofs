import Wikipedia.HopfProblem.CuspRetractionBasic
import Wikipedia.HopfProblem.CuspRetractionPosition

/-!
# Continuity of cusp straightening at the central fibre

The rescaled logarithmic position is locally bounded in the actual toric
charts.  Consequently a correction whose matrix tends to zero has norm
tending to zero, despite the individual logarithmic coordinates being
undefined as continuous functions on the boundary.  This proves the
boundary-continuity step of Lemma 7.5 without a growth assumption or an
assumed extension theorem.
-/

noncomputable section

open Set Topology Filter
open scoped Matrix

namespace Wikipedia.HopfProblem.CuspRetraction

open ToricCharts ToricFan ToricSpace

def complexEntryNorm (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  ‖fun i : Fin 2 => fun j : Fin 2 => A i j‖

theorem complexEntryNorm_nonneg (A : Matrix (Fin 2) (Fin 2) ℂ) :
    0 ≤ complexEntryNorm A := norm_nonneg _

theorem norm_complex_mulVec_le (A : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    ‖A *ᵥ v‖ ≤ 2 * complexEntryNorm A * ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (by
    have := complexEntryNorm_nonneg A
    positivity)).mpr
  intro i
  calc
    ‖(A *ᵥ v) i‖ ≤ ∑ j, ‖A i j * v j‖ := by
      change ‖∑ j, A i j * v j‖ ≤ _
      exact norm_sum_le _ _
    _ ≤ ∑ _j : Fin 2, complexEntryNorm A * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul
        ((norm_le_pi_norm (A i) j).trans
          (norm_le_pi_norm (fun k : Fin 2 => fun l : Fin 2 => A k l) i))
        (norm_le_pi_norm v j) (norm_nonneg _) (norm_nonneg _)
    _ = 2 * complexEntryNorm A * ‖v‖ := by simp; ring

variable (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)

theorem correction_norm_le {x : Space} (ht : Real.log ‖time x‖ < 0)
    (hR : entryNorm (driftMatrix C (time x)) ≤ -Real.log ‖time x‖ / 4) :
    ‖correction C D x‖ ≤
      4 * complexEntryNorm (D (time x) - C (time x)) * ‖position x‖ := by
  have hA := complexEntryNorm_nonneg (D (time x) - C (time x))
  calc
    ‖correction C D x‖ ≤
        2 * complexEntryNorm (D (time x) - C (time x)) *
          ‖inverseDisplacement C (time x) (position x)‖ := by
      simpa only [correction, norm_realToComplex] using
        norm_complex_mulVec_le (D (time x) - C (time x))
          (realToComplex (inverseDisplacement C (time x) (position x)))
    _ ≤ 2 * complexEntryNorm (D (time x) - C (time x)) * (2 * ‖position x‖) := by
      exact mul_le_mul_of_nonneg_left (inverseDisplacement_norm_le C ht hR _) (by positivity)
    _ = 4 * complexEntryNorm (D (time x) - C (time x)) * ‖position x‖ := by ring

/-- The correction extends continuously by zero at every actual point
of the central fibre, because both twists have the same central value. -/
theorem correction_continuousAt_central {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousAt (fun t => C t i j) 0)
    (hD : ∀ i j, ContinuousAt (fun t => D t i j) 0)
    (hzero : C 0 = D 0) (hR : SmallDrift C ε)
    {x : Space} (hx : time x = 0) : ContinuousAt (correction C D) x := by
  obtain ⟨B, hB, hbound⟩ := position_locally_bounded hε hε1
    (x := x) (by simpa only [hx, norm_zero] using hε)
  have htime : Tendsto time (𝓝 x) (𝓝 0) := by
    simpa only [hx] using (time_holomorphic.continuous.continuousAt (x := x)).tendsto
  have hdelta : ContinuousAt
      (fun t : ℂ => fun i : Fin 2 => fun j : Fin 2 => D t i j - C t i j) 0 := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    exact (hD i j).sub (hC i j)
  have hnorm : Tendsto (fun y : Space => complexEntryNorm (D (time y) - C (time y)))
      (𝓝 x) (𝓝 0) := by
    have hz : (fun i : Fin 2 => fun j : Fin 2 => D 0 i j - C 0 i j) = 0 := by
      ext i j
      simp only [hzero, sub_self, Pi.zero_apply]
    have h := hdelta.norm.tendsto.comp htime
    rw [hz, norm_zero] at h
    exact h
  have hlim : Tendsto
      (fun y : Space => 4 * complexEntryNorm (D (time y) - C (time y)) * B)
      (𝓝 x) (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      (tendsto_const_nhds.mul hnorm).mul (tendsto_const_nhds (x := B))
  have hb : ∀ᶠ y in 𝓝 x, ‖correction C D y‖ ≤
      4 * complexEntryNorm (D (time y) - C (time y)) * B := by
    filter_upwards [hbound] with y hy
    by_cases hy0 : time y = 0
    · rw [correction_of_time_zero C D hy0, norm_zero]
      have := complexEntryNorm_nonneg (D (time y) - C (time y))
      positivity
    · have hn : 0 < ‖time y‖ := norm_pos_iff.mpr hy0
      exact (correction_norm_le C D (Real.log_neg hn (hy.1.trans hε1))
        (hR _ hn hy.1)).trans
          (mul_le_mul_of_nonneg_left hy.2 (by
            have := complexEntryNorm_nonneg (D (time y) - C (time y))
            positivity))
  change Tendsto (correction C D) (𝓝 x) (𝓝 (correction C D x))
  rw [correction_of_time_zero C D hx]
  exact squeeze_zero_norm' hb hlim

theorem correction_continuousAt_of_time_ne_zero {ε : ℝ} (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) {x : Space} (hx0 : time x ≠ 0) (hxε : ‖time x‖ < ε) :
    ContinuousAt (correction C D) x := by
  have hmem : time x ∈ Metric.ball (0 : ℂ) ε := by
    simpa only [Metric.mem_ball, dist_zero_right] using hxε
  have hC' (i j) : ContinuousAt (fun t => C t i j) (time x) :=
    (hC i j).continuousAt (Metric.isOpen_ball.mem_nhds hmem)
  have hD' (i j) : ContinuousAt (fun t => D t i j) (time x) :=
    (hD i j).continuousAt (Metric.isOpen_ball.mem_nhds hmem)
  have hn : 0 < ‖time x‖ := norm_pos_iff.mpr hx0
  have ht : Real.log ‖time x‖ < 0 := Real.log_neg hn (hxε.trans hε1)
  have htime : ContinuousAt time x := time_holomorphic.continuous.continuousAt
  have hi : ContinuousAt
      (fun y : Space => inverseDisplacement C (time y) (position y)) x := by
    exact ContinuousAt.comp
      (f := fun y : Space => (time y, position y))
      (g := fun p : ℂ × (Fin 2 → ℝ) => inverseDisplacement C p.1 p.2)
      (inverseDisplacement_continuousAt C hC' ht (hR _ hn hxε) (position x))
      (htime.prodMk (position_continuousAt hx0 ht.ne))
  have hv : ContinuousAt (fun y : Space =>
      realToComplex (inverseDisplacement C (time y) (position y))) x := by
    exact ContinuousAt.comp
      (f := fun y : Space => inverseDisplacement C (time y) (position y))
      (g := fun u : Fin 2 → ℝ => realToComplex u)
      realToComplex_continuous.continuousAt hi
  have hm : ContinuousAt (fun y : Space => D (time y) - C (time y)) x := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    exact ((hD' i j).comp htime).sub ((hC' i j).comp htime)
  have hmul : Continuous
      (fun p : Matrix (Fin 2) (Fin 2) ℂ × (Fin 2 → ℂ) => p.1 *ᵥ p.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  change ContinuousAt ((fun p : Matrix (Fin 2) (Fin 2) ℂ × (Fin 2 → ℂ) => p.1 *ᵥ p.2) ∘
    (fun y : Space => (D (time y) - C (time y),
      realToComplex (inverseDisplacement C (time y) (position y))))) x
  exact ContinuousAt.comp hmul.continuousAt (hm.prodMk hv)

theorem correction_continuousAt {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε))
    (hzero : C 0 = D 0) (hR : SmallDrift C ε)
    {x : Space} (hxε : ‖time x‖ < ε) : ContinuousAt (correction C D) x := by
  by_cases hx0 : time x = 0
  · have hmem : (0 : ℂ) ∈ Metric.ball 0 ε := by simpa using hε
    exact correction_continuousAt_central C D hε hε1
      (fun i j => (hC i j).continuousAt (Metric.isOpen_ball.mem_nhds hmem))
      (fun i j => (hD i j).continuousAt (Metric.isOpen_ball.mem_nhds hmem)) hzero hR hx0
  · exact correction_continuousAt_of_time_ne_zero C D hε1 hC hD hR hx0 hxε

theorem changeTwist_continuousAt {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε))
    (hzero : C 0 = D 0) (hR : SmallDrift C ε)
    {x : Space} (hxε : ‖time x‖ < ε) : ContinuousAt (changeTwist C D) x := by
  change ContinuousAt ((fun p : (Fin 2 → ℂ) × Space => expFibreAction p.1 p.2) ∘
    (fun y : Space => (correction C D y, y))) x
  exact ContinuousAt.comp expFibreAction_continuous.continuousAt
    ((correction_continuousAt C D hε hε1 hC hD hzero hR hxε).prodMk continuousAt_id)

theorem changeTwist_continuousOn {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε))
    (hzero : C 0 = D 0) (hR : SmallDrift C ε) :
    ContinuousOn (changeTwist C D) (time ⁻¹' Metric.ball 0 ε) := by
  intro x hx
  have hxε : ‖time x‖ < ε := by
    simpa only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] using hx
  exact (changeTwist_continuousAt C D hε hε1 hC hD hzero hR hxε).continuousWithinAt

theorem tubeChangeTwist_continuous {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε))
    (hzero : C 0 = D 0) (hR : SmallDrift C ε) :
    Continuous (tubeChangeTwist C D ε) :=
  (changeTwist_continuousOn C D hε hε1 hC hD hzero hR).domRestrict.subtype_mk _

end Wikipedia.HopfProblem.CuspRetraction
