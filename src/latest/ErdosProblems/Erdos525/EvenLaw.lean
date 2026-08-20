import ErdosProblems.Erdos525.BadMinimum

open scoped BigOperators Topology ComplexConjugate RealInnerProductSpace

namespace Erdos525

open Classical Filter Finset Set MeasureTheory

noncomputable def lowVelocityDiagonalError (u : ℝ) (k : ℕ) : ℝ :=
  256 * Real.pi ^ 2 *
      (u + 1 + 2 * Real.pi * (1 / (k + 1 : ℝ))) ^ 2 *
    (2 * (1 / (k + 1 : ℝ))) ^ 2

lemma lowVelocityDiagonalError_tendsto_zero (u : ℝ) :
    Tendsto (lowVelocityDiagonalError u) atTop (𝓝 0) := by
  change Tendsto (fun k : ℕ ↦
    256 * Real.pi ^ 2 *
        (u + 1 + 2 * Real.pi * (1 / (k + 1 : ℝ))) ^ 2 *
      (2 * (1 / (k + 1 : ℝ))) ^ 2) atTop (𝓝 0)
  have hinv : Tendsto (fun k : ℕ ↦ (1 : ℝ) / (k + 1 : ℝ))
      atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hA : Tendsto (fun k : ℕ ↦
      u + 1 + 2 * Real.pi * (1 / (k + 1 : ℝ))) atTop (𝓝 (u + 1)) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv))
  have hB : Tendsto (fun k : ℕ ↦ 2 * (1 / (k + 1 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hinv.const_mul 2
  have h := ((hA.pow 2).const_mul (256 * Real.pi ^ 2)).mul (hB.pow 2)
  have hzero : 256 * Real.pi ^ 2 * (u + 1) ^ 2 * (0 : ℝ) ^ 2 = 0 := by ring
  rw [hzero] at h
  simpa only [one_div] using h

noncomputable def highVelocityDiagonalError (u : ℝ) (k : ℕ) : ℝ :=
  (72 / Real.pi) * (u + 2) *
    blockVelocityTailMass ((k + 1 : ℝ) / 4)

lemma highVelocityDiagonalError_tendsto_zero (u : ℝ) :
    Tendsto (highVelocityDiagonalError u) atTop (𝓝 0) := by
  change Tendsto (fun k : ℕ ↦
    (72 / Real.pi) * (u + 2) *
      blockVelocityTailMass ((k + 1 : ℝ) / 4)) atTop (𝓝 0)
  have hplus : Tendsto (fun k : ℕ ↦ (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hseq : Tendsto (fun k : ℕ ↦ ((k : ℝ) + 1) / 4) atTop atTop :=
    hplus.atTop_div_const (by norm_num)
  have htail := blockVelocityTailMass_tendsto_zero.comp hseq
  have h := htail.const_mul ((72 / Real.pi) * (u + 2))
  convert h using 1 <;> simp only [Function.comp_apply, mul_zero]

lemma diagonalHalfVoidLimit (v : ℝ) :
    Tendsto (fun k : ℕ ↦
      Real.exp (-((6 * v / Real.pi) *
        blockVelocityMass (1 / (k + 1 : ℝ)) (k + 1 : ℝ))))
      atTop (𝓝 (Real.exp (-2 * rate * v))) := by
  have hmass := halfScaledExhaustedBlockMass_tendsto v
  exact Real.continuous_exp.continuousAt.tendsto.comp (by
    convert hmass.neg using 1 <;> ring)

theorem centeredTail_liminf_ge
    (u : ℝ) (hu : 0 < u) {a : ℝ}
    (ha : a < Real.exp (-2 * rate * u)) :
    ∀ᶠ n : ℕ in atTop, a < centeredTail n u := by
  let vSeq : ℕ → ℝ := fun j ↦ u + 1 / (j + 1 : ℝ)
  have hinv : Tendsto (fun j : ℕ ↦ (1 : ℝ) / (j + 1 : ℝ))
      atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hvSeq : Tendsto vSeq atTop (𝓝 u) := by
    simpa [vSeq] using tendsto_const_nhds.add hinv
  have hexpV : Tendsto (fun j : ℕ ↦ Real.exp (-2 * rate * vSeq j))
      atTop (𝓝 (Real.exp (-2 * rate * u))) := by
    have hlin : Tendsto (fun j : ℕ ↦ -2 * rate * vSeq j)
        atTop (𝓝 (-2 * rate * u)) := by
      simpa only [mul_assoc] using hvSeq.const_mul (-2 * rate)
    exact Real.continuous_exp.continuousAt.tendsto.comp hlin
  have hvAbove : ∀ᶠ j : ℕ in atTop,
      a < Real.exp (-2 * rate * vSeq j) :=
    hexpV.eventually (Ioi_mem_nhds ha)
  rcases hvAbove.exists with ⟨j, hj⟩
  let v : ℝ := vSeq j
  have huv : u < v := by
    dsimp [v, vSeq]
    have : (0 : ℝ) < 1 / (j + 1 : ℝ) := by positivity
    linarith
  have hv : 0 < v := hu.trans huv
  let E : ℝ := Real.exp (-2 * rate * v)
  have haE : a < E := by simpa [E, v] using hj
  let δ : ℝ := (E - a) / 10
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hvoidK : ∀ᶠ k : ℕ in atTop,
      E - δ < Real.exp (-((6 * v / Real.pi) *
        blockVelocityMass (1 / (k + 1 : ℝ)) (k + 1 : ℝ))) :=
    (diagonalHalfVoidLimit v).eventually
      (Ioi_mem_nhds (by dsimp [E, δ]; linarith))
  have hlowK : ∀ᶠ k : ℕ in atTop,
      lowVelocityDiagonalError u k < δ :=
    (lowVelocityDiagonalError_tendsto_zero u).eventually (Iio_mem_nhds hδ)
  have hhighK : ∀ᶠ k : ℕ in atTop,
      highVelocityDiagonalError u k < δ :=
    (highVelocityDiagonalError_tendsto_zero u).eventually (Iio_mem_nhds hδ)
  rcases (hvoidK.and (hlowK.and hhighK)).exists with
    ⟨k, hvoidK, hlowK, hhighK⟩
  let L : ℝ := 1 / (k + 1 : ℝ)
  let V : ℝ := k + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  let I : ℝ := (6 * v / Real.pi) * blockVelocityMass L V
  have hI0 : 0 ≤ I := by
    dsimp [I]
    exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hv.le) Real.pi_pos.le)
      (blockVelocityMass_nonneg L V)
  let widthFactor : ℝ := 1 + δ / (I + 1)
  have hdenom : 0 < I + 1 := by linarith
  have hwidth : 1 < widthFactor := by
    dsimp [widthFactor]
    exact lt_add_of_pos_right 1 (div_pos hδ hdenom)
  have houterMain : (widthFactor - 1) * I < δ := by
    have hfrac : I / (I + 1) < 1 := (div_lt_one hdenom).2 (by linarith)
    dsimp [widthFactor]
    calc
      (1 + δ / (I + 1) - 1) * I = δ * (I / (I + 1)) := by ring
      _ < δ * 1 := mul_lt_mul_of_pos_left hfrac hδ
      _ = δ := mul_one δ
  have hvoidLimit :=
    uniformProbability_halfTruncatedLocalMinimumCount_eq_zero_tendsto
      v L V hv hL hV
  have hvoidEvent : ∀ᶠ n : ℕ in atTop,
      Real.exp (-I) - δ <
        uniformProbability (fun e : SignVector (2 * n) ↦
          halfTruncatedLocalMinimumCount n v L V e = 0) :=
    hvoidLimit.eventually (Ioi_mem_nhds (by dsimp [I]; linarith))
  have hbadEvent : ∀ᶠ n : ℕ in atTop,
      uniformProbability (HasBadArcSmallMinimum n u) < δ :=
    (uniformProbability_badArcSmallMinimum_tendsto_zero u hu).eventually
      (Iio_mem_nhds hδ)
  have haccEvent : ∀ᶠ n : ℕ in atTop,
      uniformProbability (HasHighMeshAcceleration n) < δ :=
    uniformProbability_highMeshAcceleration_tendsto_zero.eventually
      (Iio_mem_nhds hδ)
  have hlowBound := eventually_lowVelocitySmallMinimum_probability_le u L hu.le hL
  have hhighBound := highVelocitySmallMinimum_eventually_lt u V δ hu.le hV (by
    simpa [highVelocityDiagonalError, V] using hhighK)
  have hirregularBound :=
    eventually_irregularSmallMinimum_probability_le_elementaryExceptions u L V
  have houterBound :=
    eventually_uniformProbability_halfHasFactored_and_not_truncated_lt
      widthFactor v L V hwidth.le hv hL hV hδ
  have hcomparison :=
    eventually_halfTruncatedVoidProbability_le_tail_add_exceptions
      u v widthFactor L V huv hwidth hL
  filter_upwards [hvoidEvent, hbadEvent, haccEvent, hlowBound, hhighBound,
      hirregularBound, houterBound, hcomparison] with
      n hvoidN hbadN haccN hlowN hhighN hirregularN houterN hcomparisonN
  have hlowN' : uniformProbability (HasLowVelocitySmallMinimum n u L) <
      2 * δ := by
    have hlowK' :
        256 * Real.pi ^ 2 * (u + 1 + 2 * Real.pi * L) ^ 2 *
            (2 * L) ^ 2 < δ := by
      simpa [lowVelocityDiagonalError, L] using hlowK
    linarith
  have hirregularN' :
      uniformProbability (HasIrregularSmallMinimum n u L V) < 5 * δ := by
    linarith
  have houterN' : uniformProbability (fun e : SignVector (2 * n) ↦
      HalfHasFactoredRepresentative n widthFactor v L V e ∧
        ¬HalfHasTruncatedRepresentative n v L V e) < 2 * δ := by
    linarith
  have hvoidLower : E - 2 * δ <
      uniformProbability (fun e : SignVector (2 * n) ↦
        halfTruncatedLocalMinimumCount n v L V e = 0) := by
    have hdiag : E - δ < Real.exp (-I) := by
      simpa [I, L, V] using hvoidK
    linarith
  have htailLower : E - 9 * δ < centeredTail n u := by
    linarith
  have hEa : a < E - 9 * δ := by
    dsimp [δ]
    linarith
  exact hEa.trans htailLower

theorem centeredTail_tendsto (u : ℝ) (hu : 0 < u) :
    Tendsto (fun n : ℕ ↦ centeredTail n u) atTop
      (𝓝 (Real.exp (-2 * rate * u))) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    exact centeredTail_liminf_ge u hu ha
  · intro b hb
    exact centeredTail_limsup_le u hu hb

end Erdos525
