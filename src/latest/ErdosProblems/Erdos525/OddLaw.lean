import ErdosProblems.Erdos525.OddGlobalTransfer

open scoped BigOperators Topology ComplexConjugate RealInnerProductSpace

namespace Erdos525

open Classical Filter Finset Set MeasureTheory

namespace Odd

noncomputable def lowVelocityDiagonalError (u : ℝ) (k : ℕ) : ℝ :=
  256 * Real.pi ^ 2 *
      (u + 1 + 2 * Real.pi * (2 * (1 / (k + 1 : ℝ)))) ^ 2 *
    (2 * (2 * (1 / (k + 1 : ℝ)))) ^ 2

lemma lowVelocityDiagonalError_tendsto_zero (u : ℝ) :
    Tendsto (lowVelocityDiagonalError u) atTop (𝓝 0) := by
  change Tendsto (fun k : ℕ ↦
    256 * Real.pi ^ 2 *
        (u + 1 + 2 * Real.pi * (2 * (1 / (k + 1 : ℝ)))) ^ 2 *
      (2 * (2 * (1 / (k + 1 : ℝ)))) ^ 2) atTop (𝓝 0)
  have hinv : Tendsto (fun k : ℕ ↦ (1 : ℝ) / (k + 1 : ℝ))
      atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hA : Tendsto (fun k : ℕ ↦
      u + 1 + 2 * Real.pi * (2 * (1 / (k + 1 : ℝ))))
      atTop (𝓝 (u + 1)) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds.add
        (tendsto_const_nhds.mul (hinv.const_mul 2)))
  have hB : Tendsto (fun k : ℕ ↦ 2 * (2 * (1 / (k + 1 : ℝ))))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (hinv.const_mul 2).const_mul 2
  have h := ((hA.pow 2).const_mul (256 * Real.pi ^ 2)).mul (hB.pow 2)
  have hzero : 256 * Real.pi ^ 2 * (u + 1) ^ 2 * (0 : ℝ) ^ 2 = 0 := by ring
  rw [hzero] at h
  simpa only [one_div] using h

noncomputable def highVelocityDiagonalError (u : ℝ) (k : ℕ) : ℝ :=
  (72 / Real.pi) * (u + 2) *
    blockVelocityTailMass ((k + 1 : ℝ) / 8)

lemma highVelocityDiagonalError_tendsto_zero (u : ℝ) :
    Tendsto (highVelocityDiagonalError u) atTop (𝓝 0) := by
  change Tendsto (fun k : ℕ ↦
    (72 / Real.pi) * (u + 2) * blockVelocityTailMass ((k + 1 : ℝ) / 8))
      atTop (𝓝 0)
  have hplus : Tendsto (fun k : ℕ ↦ (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hseq : Tendsto (fun k : ℕ ↦ ((k : ℝ) + 1) / 8) atTop atTop :=
    hplus.atTop_div_const (by norm_num)
  have htail := blockVelocityTailMass_tendsto_zero.comp hseq
  have h := htail.const_mul ((72 / Real.pi) * (u + 2))
  convert h using 1 <;> simp only [Function.comp_apply, mul_zero]

lemma diagonalFactor_tendsto_one :
    Tendsto (fun k : ℕ ↦ (k + 1 : ℝ) / (k + 2 : ℝ)) atTop (𝓝 1) := by
  have hinv : Tendsto (fun k : ℕ ↦ (1 : ℝ) / (k + 2 : ℝ))
      atTop (𝓝 0) := by
    have hden : Tendsto (fun k : ℕ ↦ (k + 2 : ℝ)) atTop atTop := by
      simpa only [Nat.cast_add, Nat.cast_ofNat] using
        tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
    have hraw : Tendsto (fun k : ℕ ↦ ((k + 2 : ℝ))⁻¹)
        atTop (𝓝 0) :=
      (tendsto_inv_atTop_zero.comp hden).congr'
        (Eventually.of_forall fun _ ↦ rfl)
    simpa only [div_eq_mul_inv, one_mul] using hraw
  have h : Tendsto (fun k : ℕ ↦ 1 - 1 / (k + 2 : ℝ))
      atTop (𝓝 1) := by simpa using tendsto_const_nhds.sub hinv
  apply h.congr'
  exact Eventually.of_forall fun k ↦ by
    field_simp
    ring

lemma diagonalHalfVoidLimit (v : ℝ) :
    Tendsto (fun k : ℕ ↦
      Real.exp (-(((k + 1 : ℝ) / (k + 2 : ℝ)) *
        ((6 * v / Real.pi) *
          blockVelocityMass (1 / (k + 1 : ℝ)) (k + 1 : ℝ)))))
      atTop (𝓝 (Real.exp (-2 * rate * v))) := by
  have hmass := Erdos525.halfScaledExhaustedBlockMass_tendsto v
  have hprod := diagonalFactor_tendsto_one.mul hmass
  have hneg : Tendsto (fun k : ℕ ↦
      -(((k + 1 : ℝ) / (k + 2 : ℝ)) *
        ((6 * v / Real.pi) *
          blockVelocityMass (1 / (k + 1 : ℝ)) (k + 1 : ℝ))))
      atTop (𝓝 (-2 * rate * v)) := by
    convert hprod.neg using 1 <;> ring_nf
  exact Real.continuous_exp.continuousAt.tendsto.comp hneg

theorem tail_limsup_le
    (u : ℝ) (hu : 0 < u) {b : ℝ}
    (hb : Real.exp (-2 * rate * u) < b) :
    ∀ᶠ n : ℕ in atTop, tail n u < b := by
  have hlt := (diagonalHalfVoidLimit u).eventually (Iio_mem_nhds hb)
  rcases hlt.exists with ⟨k, hk⟩
  exact tail_limsup_le_cutoffIntensity u
    ((k + 1 : ℝ) / (k + 2 : ℝ))
    (1 / (k + 1 : ℝ)) (k + 1 : ℝ) hu
    (by positivity) ((div_lt_one (by positivity : (0 : ℝ) < k + 2)).2 (by norm_num))
    (by positivity) (by positivity) hk

theorem tail_liminf_ge
    (u : ℝ) (hu : 0 < u) {a : ℝ}
    (ha : a < Real.exp (-2 * rate * u)) :
    ∀ᶠ n : ℕ in atTop, a < tail n u := by
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
      E - δ < Real.exp (-(((k + 1 : ℝ) / (k + 2 : ℝ)) *
        ((6 * v / Real.pi) *
          blockVelocityMass (1 / (k + 1 : ℝ)) (k + 1 : ℝ)))) :=
    (diagonalHalfVoidLimit v).eventually
      (Ioi_mem_nhds (by dsimp [E, δ]; linarith))
  have hlowK : ∀ᶠ k : ℕ in atTop,
      lowVelocityDiagonalError u k < δ :=
    (lowVelocityDiagonalError_tendsto_zero u).eventually (Iio_mem_nhds hδ)
  have hhighK : ∀ᶠ k : ℕ in atTop,
      highVelocityDiagonalError u k < δ :=
    (highVelocityDiagonalError_tendsto_zero u).eventually (Iio_mem_nhds hδ)
  have hfactorK : ∀ᶠ k : ℕ in atTop,
      (1 - (k + 1 : ℝ) / (k + 2 : ℝ)) *
        ((6 * v / Real.pi) *
          blockVelocityMass (1 / (k + 1 : ℝ)) (k + 1 : ℝ)) < δ := by
    have hgap : Tendsto (fun k : ℕ ↦
        1 - (k + 1 : ℝ) / (k + 2 : ℝ)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
        diagonalFactor_tendsto_one
    have hmass := Erdos525.halfScaledExhaustedBlockMass_tendsto v
    have hprod := hgap.mul hmass
    have hzero : (0 : ℝ) * (2 * rate * v) = 0 := by ring
    rw [hzero] at hprod
    exact hprod.eventually (Iio_mem_nhds hδ)
  rcases (hvoidK.and (hlowK.and (hhighK.and hfactorK))).exists with
    ⟨k, hvoidK, hlowK, hhighK, hfactorK⟩
  let L : ℝ := 1 / (k + 1 : ℝ)
  let V : ℝ := k + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  let I : ℝ := (6 * v / Real.pi) * blockVelocityMass L V
  have hI0 : 0 ≤ I := by
    dsimp [I]
    exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hv.le) Real.pi_pos.le)
      (blockVelocityMass_nonneg L V)
  let narrowFactor : ℝ := (k + 1 : ℝ) / (k + 2 : ℝ)
  have hnarrow0 : 0 < narrowFactor := by dsimp [narrowFactor]; positivity
  have hnarrow1 : narrowFactor < 1 := by
    dsimp [narrowFactor]
    exact (div_lt_one (by positivity : (0 : ℝ) < k + 2)).2 (by norm_num)
  let α : ℝ := δ / (4 * (δ + I + 1))
  have hdenom : 0 < 4 * (δ + I + 1) := by positivity
  have hα : 0 < α := div_pos hδ hdenom
  have hαQuarter : α < 1 / 4 := by
    dsimp [α]
    rw [div_lt_iff₀ hdenom]
    nlinarith
  let wideFactor : ℝ := 1 + α
  have hwide : 1 < wideFactor := by dsimp [wideFactor]; linarith
  have hnarrowWide : narrowFactor ≤ wideFactor :=
    hnarrow1.le.trans (by linarith : (1 : ℝ) ≤ wideFactor)
  have houterMain : (wideFactor - narrowFactor) * I < 2 * δ := by
    have hαI : α * I < δ / 4 := by
      have hratio : I / (δ + I + 1) < 1 :=
        (div_lt_one (by positivity)).2 (by linarith)
      dsimp [α]
      calc
        δ / (4 * (δ + I + 1)) * I = δ / 4 * (I / (δ + I + 1)) := by
          field_simp [show δ + I + 1 ≠ 0 by positivity]
        _ < δ / 4 * 1 := mul_lt_mul_of_pos_left hratio (by positivity)
        _ = δ / 4 := by ring
    have hgapI : (1 - narrowFactor) * I < δ := by
      simpa [I, L, V, narrowFactor] using hfactorK
    have hsplit : (wideFactor - narrowFactor) * I =
        (1 - narrowFactor) * I + α * I := by
      dsimp [wideFactor]
      ring
    rw [hsplit]
    linarith
  have hvoidLimit :=
    uniformProbability_halfFactoredTruncatedLocalMinimumCount_eq_zero_tendsto
      narrowFactor v L V hnarrow0 hnarrow1 hv hL hV
  have hvoidEvent : ∀ᶠ n : ℕ in atTop,
      Real.exp (-(narrowFactor * I)) - δ <
        uniformProbability (fun e : SignVector (2 * n + 1) ↦
          halfFactoredTruncatedLocalMinimumCount n narrowFactor v L V e = 0) :=
    hvoidLimit.eventually (Ioi_mem_nhds (by dsimp [I]; linarith))
  have hbadEvent : ∀ᶠ n : ℕ in atTop,
      uniformProbability (HasBadArcSmallMinimum n u) < δ :=
    (uniformProbability_badArcSmallMinimum_tendsto_zero u hu).eventually
      (Iio_mem_nhds hδ)
  have hlowBound := eventually_lowVelocitySmallMinimum_probability_le
    u (2 * L) hu.le (by positivity)
  have hhighTail : (72 / Real.pi) * (u + 2) *
      blockVelocityTailMass ((V / 2) / 4) < δ := by
    rw [show V / 2 / 4 = (k + 1 : ℝ) / 8 by dsimp [V]; ring]
    simpa [highVelocityDiagonalError] using hhighK
  have hhighBound := highVelocitySmallMinimum_eventually_lt
    u (V / 2) δ hu.le (by positivity) hhighTail
  have hirregularBound :=
    eventually_irregularSmallMinimum_probability_le_elementaryExceptions u L V
  have houterBound :=
    eventually_uniformProbability_halfHasWide_and_not_narrow_lt
      wideFactor narrowFactor v L V (lt_trans (by norm_num) hwide) hnarrow0
        hnarrowWide hv hL hV hδ
  have hcomparison :=
    eventually_halfFactoredVoidProbability_le_tail_add_exceptions
      u v wideFactor narrowFactor L V huv hwide hL hV
  filter_upwards [hvoidEvent, hbadEvent, hlowBound, hhighBound,
      hirregularBound, houterBound, hcomparison] with
      n hvoidN hbadN hlowN hhighN hirregularN houterN hcomparisonN
  have hlowN' : uniformProbability (HasLowVelocitySmallMinimum n u (2 * L)) < δ := by
    have hlowK' :
        256 * Real.pi ^ 2 * (u + 1 + 2 * Real.pi * (2 * L)) ^ 2 *
            (2 * (2 * L)) ^ 2 < δ := by
      simpa [lowVelocityDiagonalError, L] using hlowK
    exact hlowN.trans_lt hlowK'
  have hirregularN' :
      uniformProbability (HasIrregularSmallMinimum n u L V) < 3 * δ := by
    linarith
  have houterN' : uniformProbability (fun e : SignVector (2 * n + 1) ↦
      HalfHasFactoredRepresentative n wideFactor v L V e ∧
        ¬HalfHasFactoredRepresentative n narrowFactor v L V e) < 3 * δ := by
    linarith
  have hdiag : E - δ < Real.exp (-(narrowFactor * I)) := by
    simpa [I, L, V, narrowFactor] using hvoidK
  have hvoidLower : E - 2 * δ <
      uniformProbability (fun e : SignVector (2 * n + 1) ↦
        halfFactoredTruncatedLocalMinimumCount n narrowFactor v L V e = 0) := by
    linarith
  have htailLower : E - 8 * δ < tail n u := by
    linarith
  have hEa : a < E - 8 * δ := by
    dsimp [δ]
    linarith
  exact hEa.trans htailLower

theorem tail_tendsto (u : ℝ) (hu : 0 < u) :
    Tendsto (fun n : ℕ ↦ tail n u) atTop
      (𝓝 (Real.exp (-2 * rate * u))) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    exact tail_liminf_ge u hu ha
  · intro b hb
    exact tail_limsup_le u hu hb

end Odd

end Erdos525
