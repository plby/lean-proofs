/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166PotentialKernelAnalytic
import ErdosProblems.Erdos1166.Erdos1166HLOZLemma410PotentialRace

namespace Erdos1166.PotentialConvergence

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

open HeatKernel KilledGreen
open HLOZLemma410PotentialRace
open HLOZLemma410Race

/-- The finite-domain potential comparison with an additive quasi-triangle
defect. Subtracting the defect from the harmonic comparison function makes
the boundary values nonpositive without changing harmonicity. -/
theorem puncturedGreen_toReal_le_two_mul_potential_add
    {a : Site → ℝ} {C : ℝ} (ha : KilledGreen.IsPlanarPotentialKernel a)
    (ha0 : a 0 = 0) (heven : ∀ z, a (-z) = a z)
    (htriangle : ∀ w z, a w ≤ a (w - z) + a z + C)
    (N : ℕ) {z : Site} (hz : z ≠ 0) :
    (killedGreen (puncturedDisk N z) 0 0).toReal ≤ 2 * a z + C := by
  let A : Finset Site := (squareDisk N).filter fun w ↦ w ≠ z
  have hAeq : (A : Set Site) = puncturedDisk N z := by
    ext w
    simp [A, puncturedDisk]
  have hAsub : (A : Set Site) ⊆ (squareDisk N : Set Site) := by
    intro w hw
    exact (Finset.mem_filter.mp hw).1
  let g : Site → ℝ := fun w ↦ a (w - z) - a w + a z
  let u : Site → ℝ := fun w ↦
    (killedGreen (puncturedDisk N z) w 0).toReal - g w
  let v : Site → ℝ := fun w ↦ u w - C
  have hfinite : ∀ w, killedGreen (puncturedDisk N z) w 0 ≠ ∞ := by
    intro w
    exact ne_of_lt ((killedGreen_mono (puncturedDisk_subset_squareDisk N z)
      w 0).trans_lt (diskGreen_lt_top N w 0))
  have hgstep : ∀ w, w ∈ A →
      KilledGreen.stepAverage g w =
        g w - (if w = 0 then 1 else 0) := by
    intro w hw
    have hwz : w ≠ z := (Finset.mem_filter.mp hw).2
    have hwsub : w - z ≠ 0 := sub_ne_zero.mpr hwz
    have hshift : KilledGreen.stepAverage (fun q ↦ a (q - z)) w =
        KilledGreen.stepAverage a (w - z) := by
      unfold KilledGreen.stepAverage
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      exact congrArg a (by abel)
    change KilledGreen.stepAverage
        (fun q ↦ (a (q - z) - a q) + a z) w = _
    rw [KilledGreen.stepAverage_add, KilledGreen.stepAverage_sub,
      KilledGreen.stepAverage_const, hshift, ha (w - z), ha w]
    simp only [if_neg hwsub, add_zero]
    dsimp only [g]
    ring
  have huharm : ∀ w ∈ A, u w = KilledGreen.stepAverage u w := by
    intro w hw
    have hwD : w ∈ puncturedDisk N z := by simpa [← hAeq] using hw
    have hG := killedGreen_toReal_eq_indicator_add_stepAverage hwD hfinite
    have hg := hgstep w hw
    change (killedGreen (puncturedDisk N z) w 0).toReal - g w = _
    rw [KilledGreen.stepAverage_sub]
    linarith
  have hvharm : ∀ w ∈ A, v w = KilledGreen.stepAverage v w := by
    intro w hw
    change u w - C = KilledGreen.stepAverage (fun q ↦ u q - C) w
    rw [KilledGreen.stepAverage_sub, KilledGreen.stepAverage_const,
      ← huharm w hw]
  have hvout : ∀ w, w ∉ A → v w ≤ 0 := by
    intro w hw
    have hwD : w ∉ puncturedDisk N z := by
      intro hwD
      apply hw
      simpa [← hAeq] using hwD
    have hGzero : killedGreen (puncturedDisk N z) w 0 = 0 :=
      killedGreen_eq_zero_of_start_not_mem hwD
    change (killedGreen (puncturedDisk N z) w 0).toReal - g w - C ≤ 0
    rw [hGzero]
    change 0 - (a (w - z) - a w + a z) - C ≤ 0
    linarith [htriangle w z]
  have hzeroA : (0 : Site) ∈ A := by
    apply Finset.mem_filter.mpr
    exact ⟨by
      apply Finset.mem_product.mpr
      constructor <;> simp, hz.symm⟩
  have hv0 := finite_subset_square_maximum_principle
    hAsub hvharm hvout 0 hzeroA
  change (killedGreen (puncturedDisk N z) 0 0).toReal -
      (a (0 - z) - a 0 + a z) - C ≤ 0 at hv0
  rw [zero_sub, ha0, heven] at hv0
  linarith

theorem planarPotentialKernel_puncturedGreen_le (N : ℕ) {z : Site}
    (hz : z ≠ 0) :
    (killedGreen (puncturedDisk N z) 0 0).toReal ≤
      2 * planarPotentialKernel z + 2500 :=
  puncturedGreen_toReal_le_two_mul_potential_add
    planarPotentialKernel_isPlanar planarPotentialKernel_zero
    planarPotentialKernel_neg planarPotentialKernel_quasiTriangle N hz

theorem siteNormInf_le_radius_of_squaredDistance_zero_le
    {R : ℕ} {z : Site} (hdist : siteSquaredDistance 0 z ≤ R ^ 2) :
    siteNormInf z ≤ R := by
  have h₁sq : z.1.natAbs ^ 2 ≤ R ^ 2 := by
    unfold siteSquaredDistance at hdist
    simp only [Prod.fst_zero, Prod.snd_zero, zero_sub, Int.natAbs_neg] at hdist
    omega
  have h₂sq : z.2.natAbs ^ 2 ≤ R ^ 2 := by
    unfold siteSquaredDistance at hdist
    simp only [Prod.fst_zero, Prod.snd_zero, zero_sub, Int.natAbs_neg] at hdist
    omega
  have h₁ : z.1.natAbs ≤ R :=
    (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).mp h₁sq
  have h₂ : z.2.natAbs ≤ R :=
    (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).mp h₂sq
  exact max_le h₁ h₂

/-- A deliberately coarse logarithmic punctured-Green bound. Its constant
is harmless in the HLOZ race: the much larger outer square absorbs it in the
exit-before-return error. -/
theorem planarPotentialKernel_puncturedGreen_le_log
    {R : ℕ} (hR : 2 ≤ R) {z : Site} (hz : z ≠ 0)
    (hdist : siteSquaredDistance 0 z ≤ R ^ 2) (N : ℕ) :
    (killedGreen (puncturedDisk N z) 0 0).toReal ≤
      21000 * Real.log R := by
  have hzNorm : 0 < siteNormInf z := siteNormInf_pos_of_ne_zero hz
  have hnorm : siteNormInf z ≤ R :=
    siteNormInf_le_radius_of_squaredDistance_zero_le hdist
  have hlogR : 0 < Real.log (R : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  have hlogMono : Real.log (siteNormInf z : ℝ) ≤ Real.log (R : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast hzNorm
    · exact_mod_cast hnorm
  have hc0 : 0 ≤ 2 / Real.pi := by positivity
  have hc1 : 2 / Real.pi ≤ 1 := by
    apply (div_le_one Real.pi_pos).2
    linarith [Real.pi_gt_three]
  have hpot := planarPotentialKernel_log_upper z hzNorm
  have hscaled := mul_le_mul_of_nonneg_left hlogMono hc0
  have hcoef : (2 / Real.pi) * Real.log (R : ℝ) ≤ Real.log R := by
    simpa using mul_le_mul_of_nonneg_right hc1 hlogR.le
  have hG := planarPotentialKernel_puncturedGreen_le N hz
  have hlogMonoTwo : Real.log 2 ≤ Real.log (R : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hR
  have hden : (1 : ℝ) ≤ 8 * Real.log R := by
    nlinarith [Real.log_two_gt_d9]
  nlinarith

/-- A source-sufficient off-origin hitting estimate. The exponent `400000`
is only the finite outer cutoff; the resulting probability bound depends on
the target radius as `1 / log R`, as required by the HLOZ race argument. -/
theorem planar_hitBeforePositiveReturn_zero_real_lower
    {R : ℕ} (hR : 2 ≤ R) {z : Site} (hz : z ≠ 0)
    (hdist : siteSquaredDistance 0 z ≤ R ^ 2) :
    1 / (50000 * Real.log R) ≤
      incrementLaw.real (hitBeforePositiveReturnEvent 0 z) := by
  have hlog : 0 < Real.log (R : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  have hRpow : 2 ≤ R ^ 400000 := by
    calc
      2 ≤ R := hR
      _ ≤ R ^ 400000 := Nat.le_pow (a := R) (b := 400000) (by norm_num)
  have hexit := exitBeforeReturn_zero_real_le_eight_div_log hRpow
  have hlogPow : Real.log (((R ^ 400000 : ℕ) : ℝ)) =
      400000 * Real.log (R : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have hexit' : incrementLaw.real
      (exitBeforeReturnEvent (squareDisk (R ^ 400000) : Set Site) 0) ≤
        1 / (50000 * Real.log R) := by
    calc
      incrementLaw.real
          (exitBeforeReturnEvent (squareDisk (R ^ 400000) : Set Site) 0) ≤
          8 / Real.log (((R ^ 400000 : ℕ) : ℝ)) := hexit
      _ = 1 / (50000 * Real.log R) := by
        rw [hlogPow]
        field_simp
        ring
  have hlower :=
    hitBeforePositiveReturn_zero_real_lower_of_puncturedGreen_le
      (N := R ^ 400000) hz
        (planarPotentialKernel_puncturedGreen_le_log hR hz hdist _)
  have halg : 1 / (50000 * Real.log R) ≤
      1 / (21000 * Real.log R) - 1 / (50000 * Real.log R) := by
    field_simp [ne_of_gt hlog]
    norm_num
  calc
    1 / (50000 * Real.log R) ≤
        1 / (21000 * Real.log R) - 1 / (50000 * Real.log R) := halg
    _ ≤ 1 / (21000 * Real.log R) -
        incrementLaw.real
          (exitBeforeReturnEvent (squareDisk (R ^ 400000) : Set Site) 0) :=
      sub_le_sub_left hexit' _
    _ ≤ incrementLaw.real (hitBeforePositiveReturnEvent 0 z) := hlower

theorem hasOffOriginHitBeforeReturnLowerBound_planar
    {R : ℕ} (hR : 2 ≤ R) :
    HasOffOriginHitBeforeReturnLowerBound R
      (ENNReal.ofReal (1 / (50000 * Real.log R))) := by
  intro x y hxy hdist
  let z : Site := y - x
  have hz : z ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hdistz : siteSquaredDistance 0 z ≤ R ^ 2 := by
    simpa [z, siteSquaredDistance_zero_sub] using hdist
  rw [hitBeforePositiveReturnEvent_translate_to_zero x y]
  apply (ENNReal.ofReal_le_iff_le_toReal
    (measure_ne_top incrementLaw _)).mpr
  exact planar_hitBeforePositiveReturn_zero_real_lower hR hz hdistz

theorem hasHLOZLemma410PostHitRaceEstimate_exp_planar
    (window : Site → Finset Site) (m k qCandidate qRace R : ℕ)
    (hR : 2 ≤ R)
    (hwindow : ∀ c x, x ∈ window c → siteSquaredDistance x c ≤ R ^ 2) :
    HasHLOZLemma410PostHitRaceEstimate simpleRandomWalkLaw window
      m k qCandidate qRace
      (fun _ ↦ ENNReal.ofReal
        (Real.exp (-((qRace : ℝ) * (1 / (50000 * Real.log R)))))) := by
  have hlog : 0 < Real.log (R : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  have hlogMono : Real.log 2 ≤ Real.log (R : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hR
  have hden : (1 : ℝ) ≤ 50000 * Real.log R := by
    nlinarith [Real.log_two_gt_d9]
  have hε0 : 0 ≤ (1 : ℝ) / (50000 * Real.log R) := by positivity
  have hε1 : (1 : ℝ) / (50000 * Real.log R) ≤ 1 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hlog)).mpr
    simpa using hden
  exact hasHLOZLemma410PostHitRaceEstimate_exp_of_offOriginHitBeforeReturn
    window m k qCandidate qRace R (1 / (50000 * Real.log R)) hε0 hε1
      hwindow (hasOffOriginHitBeforeReturnLowerBound_planar hR)

end Erdos1166.PotentialConvergence
