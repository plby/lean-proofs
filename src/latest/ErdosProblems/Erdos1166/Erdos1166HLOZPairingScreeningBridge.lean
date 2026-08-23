import ErdosProblems.Erdos1166.Erdos1166HLOZPairing
import ErdosProblems.Erdos1166.Erdos1166HLOZScreeningAssembly

namespace Erdos1166.HLOZPairing

open MeasureTheory Set
open scoped ENNReal

namespace ScreeningBridge

open HLOZScreeningAssembly

variable {ι : Type*}

/-- The one-stage inverse-level cost. -/
noncomputable def stageRate (m : ℕ) : ℝ≥0∞ := ((m : ℝ≥0∞) + 1)⁻¹

theorem stageRate_le_one (m : ℕ) : stageRate m ≤ 1 := by
  simp [stageRate]

/-- The exceptional-error scale, chosen at the desired final cubic rate. -/
noncomputable def exceptionalRate (m : ℕ) : ℝ≥0∞ := stageRate m ^ 3

theorem explicit_cubic_rate (m K : ℕ) :
    ((1 + 4 * K : ℕ) : ℝ≥0∞) * exceptionalRate m =
      ENNReal.ofReal (((1 + 4 * K : ℕ) : ℝ) / ((m : ℝ) + 1) ^ (3 : ℝ)) := by
  rw [Real.rpow_ofNat]
  rw [ENNReal.ofReal_div_of_pos (by positivity)]
  have hnum : ENNReal.ofReal (((1 + 4 * K : ℕ) : ℝ)) =
      ((1 + 4 * K : ℕ) : ℝ≥0∞) :=
    ENNReal.ofReal_natCast (1 + 4 * K)
  have hbase : ENNReal.ofReal ((m : ℝ) + 1) = (m : ℝ≥0∞) + 1 := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    simp
  have hden : ENNReal.ofReal (((m : ℝ) + 1) ^ (3 : ℕ)) =
      ((m : ℝ≥0∞) + 1) ^ (3 : ℕ) := by
    rw [ENNReal.ofReal_pow (by positivity), hbase]
  rw [hnum, hden]
  simp only [exceptionalRate, stageRate, div_eq_mul_inv]
  rw [← ENNReal.inv_pow]

/-- A finite grid of three screenings for one exact first-four pairing event gives
the explicit `O((m+1)⁻³)` estimate.  Each stage costs at most `(m+1)⁻¹`,
and both the global bad event and each stage error are charged at the already
cubic scale. -/
theorem pairingEvent_measure_le_of_three_screenings
    (m : ℕ) (i : Fin 6) (K : ℕ)
    (grid : Finset ι) (bad : Set (ℕ → Site))
    (E₀ E₁ E₂ E₃ : ι → Set (ℕ → Site))
    (hcard : grid.card ≤ K)
    (hcover : firstFourPairingEvent m i ⊆ bad ∪ ⋃ a ∈ grid, E₃ a)
    (hbad : simpleRandomWalkLaw bad ≤ exceptionalRate m)
    (h₁ : ∀ a ∈ grid,
      StageBound simpleRandomWalkLaw (stageRate m) (exceptionalRate m) (E₀ a) (E₁ a))
    (h₂ : ∀ a ∈ grid,
      StageBound simpleRandomWalkLaw (stageRate m) (exceptionalRate m) (E₁ a) (E₂ a))
    (h₃ : ∀ a ∈ grid,
      StageBound simpleRandomWalkLaw (stageRate m) (exceptionalRate m) (E₂ a) (E₃ a)) :
    simpleRandomWalkLaw (firstFourPairingEvent m i) ≤
      ENNReal.ofReal (((1 + 4 * K : ℕ) : ℝ) / ((m : ℝ) + 1) ^ (3 : ℝ)) := by
  have hassembly := finite_grid_three_stage simpleRandomWalkLaw grid bad
    (firstFourPairingEvent m i) E₀ E₁ E₂ E₃ hcover hbad h₁ h₂ h₃
  have hr : stageRate m ≤ 1 := stageRate_le_one m
  have hgeom : stageRate m ^ 2 + stageRate m + 1 ≤ 3 := by
    calc
      stageRate m ^ 2 + stageRate m + 1 ≤ 1 ^ 2 + 1 + 1 := by gcongr
      _ = 3 := by norm_num
  calc
    simpleRandomWalkLaw (firstFourPairingEvent m i) ≤
        exceptionalRate m + grid.card *
          (stageRate m ^ 3 +
            (stageRate m ^ 2 + stageRate m + 1) * exceptionalRate m) := hassembly
    _ ≤ exceptionalRate m + grid.card *
          (exceptionalRate m + 3 * exceptionalRate m) := by
      gcongr
      simpa [exceptionalRate]
    _ = ((1 + 4 * grid.card : ℕ) : ℝ≥0∞) * exceptionalRate m := by
      simp only [exceptionalRate]
      push_cast
      ring
    _ ≤ ((1 + 4 * K : ℕ) : ℝ≥0∞) * exceptionalRate m := by
      gcongr
    _ = ENNReal.ofReal (((1 + 4 * K : ℕ) : ℝ) /
        ((m : ℝ) + 1) ^ (3 : ℝ)) := explicit_cubic_rate m K

/-- Source-facing global form: uniform screening data for all six pairings
and all levels proves the HLOZ planar conclusion. -/
theorem hlozPlanarConclusion_of_uniform_three_screenings
    (K : ℕ)
    (grid : ℕ → Fin 6 → Finset ι)
    (bad : ℕ → Fin 6 → Set (ℕ → Site))
    (E₀ E₁ E₂ E₃ : ℕ → Fin 6 → ι → Set (ℕ → Site))
    (hcard : ∀ m i, (grid m i).card ≤ K)
    (hcover : ∀ m i,
      firstFourPairingEvent m i ⊆ bad m i ∪ ⋃ a ∈ grid m i, E₃ m i a)
    (hbad : ∀ m i,
      simpleRandomWalkLaw (bad m i) ≤ exceptionalRate m)
    (h₁ : ∀ m i a, a ∈ grid m i →
      StageBound simpleRandomWalkLaw (stageRate m) (exceptionalRate m)
        (E₀ m i a) (E₁ m i a))
    (h₂ : ∀ m i a, a ∈ grid m i →
      StageBound simpleRandomWalkLaw (stageRate m) (exceptionalRate m)
        (E₁ m i a) (E₂ m i a))
    (h₃ : ∀ m i a, a ∈ grid m i →
      StageBound simpleRandomWalkLaw (stageRate m) (exceptionalRate m)
        (E₂ m i a) (E₃ m i a)) :
    HLOZPlanarConclusion := by
  apply hlozPlanarConclusion_of_concrete_pairing_polynomial_bounds
      (C := ((1 + 4 * K : ℕ) : ℝ)) (p := 3) (by positivity) (by norm_num)
  intro m i
  exact pairingEvent_measure_le_of_three_screenings m i K (grid m i) (bad m i)
    (E₀ m i) (E₁ m i) (E₂ m i) (E₃ m i)
    (hcard m i) (hcover m i) (hbad m i)
    (h₁ m i) (h₂ m i) (h₃ m i)

/-! The same bridge in the source's `m^{-κ}` notation. -/

/-- One HLOZ screening cost, including an explicit natural prefactor. -/
noncomputable def sourceStageRate (m A : ℕ) (κ : ℝ) : ℝ≥0∞ :=
  (A : ℝ≥0∞) * ((m : ℝ≥0∞) + 1) ^ (-κ)

/-- The common target scale after three screenings. -/
noncomputable def sourceExceptionalRate (m : ℕ) (κ : ℝ) : ℝ≥0∞ :=
  ((m : ℝ≥0∞) + 1) ^ (-(3 * κ))

/-- Explicit constant resulting from one bad-event charge, a grid of size
`K`, a stage prefactor `A`, and one cubic-scale error at each stage. -/
def sourceScreeningConstant (A K : ℕ) : ℕ :=
  1 + K * (A ^ 3 + A ^ 2 + A + 1)

theorem source_inverse_rate_le_one (m : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ((m : ℝ≥0∞) + 1) ^ (-κ) ≤ 1 := by
  apply ENNReal.rpow_le_one_of_one_le_of_neg
  · simp
  · linarith

theorem sourceStageRate_le_prefactor (m A : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    sourceStageRate m A κ ≤ (A : ℝ≥0∞) := by
  calc
    sourceStageRate m A κ ≤ (A : ℝ≥0∞) * 1 := by
      rw [sourceStageRate]
      gcongr
      exact source_inverse_rate_le_one m hκ
    _ = (A : ℝ≥0∞) := by simp

theorem sourceStageRate_cube (m A : ℕ) (κ : ℝ) :
    sourceStageRate m A κ ^ 3 =
      (A : ℝ≥0∞) ^ 3 * sourceExceptionalRate m κ := by
  rw [sourceStageRate, mul_pow,
    HLOZScreeningAssembly.ennreal_inverse_rpow_cube]
  rfl

theorem source_explicit_rate (m A K : ℕ) (κ : ℝ) :
    (sourceScreeningConstant A K : ℝ≥0∞) * sourceExceptionalRate m κ =
      ENNReal.ofReal (((sourceScreeningConstant A K : ℕ) : ℝ) /
        ((m : ℝ) + 1) ^ (3 * κ)) := by
  rw [ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos (by positivity) _)]
  have hnum : ENNReal.ofReal (((sourceScreeningConstant A K : ℕ) : ℝ)) =
      (sourceScreeningConstant A K : ℝ≥0∞) :=
    ENNReal.ofReal_natCast (sourceScreeningConstant A K)
  have hbase : ENNReal.ofReal ((m : ℝ) + 1) = (m : ℝ≥0∞) + 1 := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    simp
  rw [hnum, ← ENNReal.ofReal_rpow_of_pos (by positivity), hbase]
  simp only [sourceExceptionalRate, div_eq_mul_inv]
  rw [ENNReal.rpow_neg]

/-- Proposition-4.7-shaped local bridge.  Three bounds of order
`A (m+1)^{-κ}`, together with bad and stage errors already controlled at
order `(m+1)^{-3κ}`, give an explicit bound for the exact first-four pairing
event. -/
theorem pairingEvent_measure_le_of_source_screenings
    (m : ℕ) (i : Fin 6) (A K : ℕ) {κ : ℝ} (hκ : 0 < κ)
    (grid : Finset ι) (bad : Set (ℕ → Site))
    (E₀ E₁ E₂ E₃ : ι → Set (ℕ → Site))
    (hcard : grid.card ≤ K)
    (hcover : firstFourPairingEvent m i ⊆ bad ∪ ⋃ a ∈ grid, E₃ a)
    (hbad : simpleRandomWalkLaw bad ≤ sourceExceptionalRate m κ)
    (h₁ : ∀ a ∈ grid,
      StageBound simpleRandomWalkLaw (sourceStageRate m A κ)
        (sourceExceptionalRate m κ) (E₀ a) (E₁ a))
    (h₂ : ∀ a ∈ grid,
      StageBound simpleRandomWalkLaw (sourceStageRate m A κ)
        (sourceExceptionalRate m κ) (E₁ a) (E₂ a))
    (h₃ : ∀ a ∈ grid,
      StageBound simpleRandomWalkLaw (sourceStageRate m A κ)
        (sourceExceptionalRate m κ) (E₂ a) (E₃ a)) :
    simpleRandomWalkLaw (firstFourPairingEvent m i) ≤
      ENNReal.ofReal (((sourceScreeningConstant A K : ℕ) : ℝ) /
        ((m : ℝ) + 1) ^ (3 * κ)) := by
  have hassembly := finite_grid_three_stage simpleRandomWalkLaw grid bad
    (firstFourPairingEvent m i) E₀ E₁ E₂ E₃ hcover hbad h₁ h₂ h₃
  have hq : sourceStageRate m A κ ≤ (A : ℝ≥0∞) :=
    sourceStageRate_le_prefactor m A hκ
  have hgeom : sourceStageRate m A κ ^ 2 + sourceStageRate m A κ + 1 ≤
      (A : ℝ≥0∞) ^ 2 + A + 1 := by gcongr
  calc
    simpleRandomWalkLaw (firstFourPairingEvent m i) ≤
        sourceExceptionalRate m κ + grid.card *
          (sourceStageRate m A κ ^ 3 +
            (sourceStageRate m A κ ^ 2 + sourceStageRate m A κ + 1) *
              sourceExceptionalRate m κ) := hassembly
    _ ≤ sourceExceptionalRate m κ + grid.card *
          ((A : ℝ≥0∞) ^ 3 * sourceExceptionalRate m κ +
            ((A : ℝ≥0∞) ^ 2 + A + 1) * sourceExceptionalRate m κ) := by
      gcongr
      simpa [sourceStageRate_cube]
    _ = (sourceScreeningConstant A grid.card : ℝ≥0∞) *
          sourceExceptionalRate m κ := by
      simp only [sourceScreeningConstant]
      push_cast
      ring
    _ ≤ (sourceScreeningConstant A K : ℝ≥0∞) *
          sourceExceptionalRate m κ := by
      gcongr
      have hconstant : sourceScreeningConstant A grid.card ≤
          sourceScreeningConstant A K := by
        simp only [sourceScreeningConstant]
        gcongr
      exact_mod_cast hconstant
    _ = ENNReal.ofReal (((sourceScreeningConstant A K : ℕ) : ℝ) /
        ((m : ℝ) + 1) ^ (3 * κ)) := source_explicit_rate m A K κ

/-- Uniform source estimates for the six pairings imply the planar HLOZ
conclusion as soon as the published exponent satisfies `3κ > 1`. -/
theorem hlozPlanarConclusion_of_source_screenings
    (A K : ℕ) (κ : ℝ) (hκ : 1 < 3 * κ)
    (grid : ℕ → Fin 6 → Finset ι)
    (bad : ℕ → Fin 6 → Set (ℕ → Site))
    (E₀ E₁ E₂ E₃ : ℕ → Fin 6 → ι → Set (ℕ → Site))
    (hcard : ∀ m i, (grid m i).card ≤ K)
    (hcover : ∀ m i,
      firstFourPairingEvent m i ⊆ bad m i ∪ ⋃ a ∈ grid m i, E₃ m i a)
    (hbad : ∀ m i,
      simpleRandomWalkLaw (bad m i) ≤ sourceExceptionalRate m κ)
    (h₁ : ∀ m i a, a ∈ grid m i →
      StageBound simpleRandomWalkLaw (sourceStageRate m A κ)
        (sourceExceptionalRate m κ) (E₀ m i a) (E₁ m i a))
    (h₂ : ∀ m i a, a ∈ grid m i →
      StageBound simpleRandomWalkLaw (sourceStageRate m A κ)
        (sourceExceptionalRate m κ) (E₁ m i a) (E₂ m i a))
    (h₃ : ∀ m i a, a ∈ grid m i →
      StageBound simpleRandomWalkLaw (sourceStageRate m A κ)
        (sourceExceptionalRate m κ) (E₂ m i a) (E₃ m i a)) :
    HLOZPlanarConclusion := by
  apply hlozPlanarConclusion_of_concrete_pairing_polynomial_bounds
      (C := (sourceScreeningConstant A K : ℝ)) (p := 3 * κ)
      (by positivity) hκ
  intro m i
  exact pairingEvent_measure_le_of_source_screenings m i A K (by linarith)
    (grid m i) (bad m i) (E₀ m i) (E₁ m i) (E₂ m i) (E₃ m i)
    (hcard m i) (hcover m i) (hbad m i)
    (h₁ m i) (h₂ m i) (h₃ m i)

/-! Source estimates carry unspecified finite constants.  The following
variant records that prefactor rather than requiring coefficient one. -/

/-- Cubic exceptional scale with an explicit source prefactor. -/
noncomputable def sourceExceptionalRateWithPrefactor
    (m B : ℕ) (kappa : ℝ) : ℝ≥0∞ :=
  (B : ℝ≥0∞) * sourceExceptionalRate m kappa

/-- Constant produced by the three-stage assembly when every exceptional
charge has prefactor `B`. -/
def sourcePrefactoredScreeningConstant (A B K : ℕ) : ℕ :=
  B + K * (A ^ 3 + (A ^ 2 + A + 1) * B)

theorem source_prefactored_explicit_rate (m A B K : ℕ) (kappa : ℝ) :
    (sourcePrefactoredScreeningConstant A B K : ℝ≥0∞) *
        sourceExceptionalRate m kappa =
      ENNReal.ofReal (((sourcePrefactoredScreeningConstant A B K : ℕ) : ℝ) /
        ((m : ℝ) + 1) ^ (3 * kappa)) := by
  rw [ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos (by positivity) _)]
  have hnum : ENNReal.ofReal
      (((sourcePrefactoredScreeningConstant A B K : ℕ) : ℝ)) =
      (sourcePrefactoredScreeningConstant A B K : ℝ≥0∞) :=
    ENNReal.ofReal_natCast (sourcePrefactoredScreeningConstant A B K)
  have hbase : ENNReal.ofReal ((m : ℝ) + 1) = (m : ℝ≥0∞) + 1 := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    simp
  rw [hnum, ← ENNReal.ofReal_rpow_of_pos (by positivity), hbase]
  simp only [sourceExceptionalRate, div_eq_mul_inv]
  rw [ENNReal.rpow_neg]

theorem pairingEvent_measure_le_of_prefactored_source_screenings
    (m : ℕ) (i : Fin 6) (A B K : ℕ) {kappa : ℝ} (hkappa : 0 < kappa)
    (grid : Finset ι) (bad : Set (ℕ → Site))
    (E₀ E₁ E₂ E₃ : ι → Set (ℕ → Site))
    (hcard : grid.card ≤ K)
    (hcover : firstFourPairingEvent m i ⊆ bad ∪ ⋃ a ∈ grid, E₃ a)
    (hbad : simpleRandomWalkLaw bad ≤
      sourceExceptionalRateWithPrefactor m B kappa)
    (h₁ : ∀ a ∈ grid,
      StageBound simpleRandomWalkLaw (sourceStageRate m A kappa)
        (sourceExceptionalRateWithPrefactor m B kappa) (E₀ a) (E₁ a))
    (h₂ : ∀ a ∈ grid,
      StageBound simpleRandomWalkLaw (sourceStageRate m A kappa)
        (sourceExceptionalRateWithPrefactor m B kappa) (E₁ a) (E₂ a))
    (h₃ : ∀ a ∈ grid,
      StageBound simpleRandomWalkLaw (sourceStageRate m A kappa)
        (sourceExceptionalRateWithPrefactor m B kappa) (E₂ a) (E₃ a)) :
    simpleRandomWalkLaw (firstFourPairingEvent m i) ≤
      ENNReal.ofReal (((sourcePrefactoredScreeningConstant A B K : ℕ) : ℝ) /
        ((m : ℝ) + 1) ^ (3 * kappa)) := by
  have hassembly := finite_grid_three_stage simpleRandomWalkLaw grid bad
    (firstFourPairingEvent m i) E₀ E₁ E₂ E₃ hcover hbad h₁ h₂ h₃
  have hq : sourceStageRate m A kappa ≤ (A : ℝ≥0∞) :=
    sourceStageRate_le_prefactor m A hkappa
  have hgeom : sourceStageRate m A kappa ^ 2 + sourceStageRate m A kappa + 1 ≤
      (A : ℝ≥0∞) ^ 2 + A + 1 := by gcongr
  calc
    simpleRandomWalkLaw (firstFourPairingEvent m i) ≤
        sourceExceptionalRateWithPrefactor m B kappa + grid.card *
          (sourceStageRate m A kappa ^ 3 +
            (sourceStageRate m A kappa ^ 2 + sourceStageRate m A kappa + 1) *
              sourceExceptionalRateWithPrefactor m B kappa) := hassembly
    _ ≤ (B : ℝ≥0∞) * sourceExceptionalRate m kappa + grid.card *
          ((A : ℝ≥0∞) ^ 3 * sourceExceptionalRate m kappa +
            ((A : ℝ≥0∞) ^ 2 + A + 1) *
              ((B : ℝ≥0∞) * sourceExceptionalRate m kappa)) := by
      simp only [sourceExceptionalRateWithPrefactor]
      gcongr
      simpa [sourceStageRate_cube]
    _ = (sourcePrefactoredScreeningConstant A B grid.card : ℝ≥0∞) *
          sourceExceptionalRate m kappa := by
      simp only [sourcePrefactoredScreeningConstant]
      push_cast
      ring
    _ ≤ (sourcePrefactoredScreeningConstant A B K : ℝ≥0∞) *
          sourceExceptionalRate m kappa := by
      gcongr
      have hconstant : sourcePrefactoredScreeningConstant A B grid.card ≤
          sourcePrefactoredScreeningConstant A B K := by
        simp only [sourcePrefactoredScreeningConstant]
        gcongr
      exact_mod_cast hconstant
    _ = ENNReal.ofReal
        (((sourcePrefactoredScreeningConstant A B K : ℕ) : ℝ) /
          ((m : ℝ) + 1) ^ (3 * kappa)) :=
      source_prefactored_explicit_rate m A B K kappa

/-- Uniform source estimates with arbitrary finite exceptional prefactor
still imply the planar conclusion. -/
theorem hlozPlanarConclusion_of_prefactored_source_screenings
    (A B K : ℕ) (kappa : ℝ) (hkappa : 1 < 3 * kappa)
    (grid : ℕ → Fin 6 → Finset ι)
    (bad : ℕ → Fin 6 → Set (ℕ → Site))
    (E₀ E₁ E₂ E₃ : ℕ → Fin 6 → ι → Set (ℕ → Site))
    (hcard : ∀ m i, (grid m i).card ≤ K)
    (hcover : ∀ m i,
      firstFourPairingEvent m i ⊆ bad m i ∪ ⋃ a ∈ grid m i, E₃ m i a)
    (hbad : ∀ m i, simpleRandomWalkLaw (bad m i) ≤
      sourceExceptionalRateWithPrefactor m B kappa)
    (h₁ : ∀ m i a, a ∈ grid m i →
      StageBound simpleRandomWalkLaw (sourceStageRate m A kappa)
        (sourceExceptionalRateWithPrefactor m B kappa) (E₀ m i a) (E₁ m i a))
    (h₂ : ∀ m i a, a ∈ grid m i →
      StageBound simpleRandomWalkLaw (sourceStageRate m A kappa)
        (sourceExceptionalRateWithPrefactor m B kappa) (E₁ m i a) (E₂ m i a))
    (h₃ : ∀ m i a, a ∈ grid m i →
      StageBound simpleRandomWalkLaw (sourceStageRate m A kappa)
        (sourceExceptionalRateWithPrefactor m B kappa) (E₂ m i a) (E₃ m i a)) :
    HLOZPlanarConclusion := by
  apply hlozPlanarConclusion_of_concrete_pairing_polynomial_bounds
      (C := (sourcePrefactoredScreeningConstant A B K : ℝ)) (p := 3 * kappa)
      (by positivity) hkappa
  intro m i
  exact pairingEvent_measure_le_of_prefactored_source_screenings
    m i A B K (by linarith) (grid m i) (bad m i)
    (E₀ m i) (E₁ m i) (E₂ m i) (E₃ m i)
    (hcard m i) (hcover m i) (hbad m i)
    (h₁ m i) (h₂ m i) (h₃ m i)

private theorem ennreal_tsum_ne_top_of_eventually_le
    (f g : ℕ → ℝ≥0∞) (hf : ∀ m, f m ≠ ∞)
    (hfg : ∀ᶠ m : ℕ in Filter.atTop, f m ≤ g m)
    (hg : (∑' m : ℕ, g m) ≠ ∞) :
    (∑' m : ℕ, f m) ≠ ∞ := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hfg
  have htail : (∑' i : {i : ℕ // i ∉ Finset.range N}, f i) ≤
      ∑' m : ℕ, g m := by
    calc
      (∑' i : {i : ℕ // i ∉ Finset.range N}, f i) ≤
          ∑' i : {i : ℕ // i ∉ Finset.range N}, g i := by
        apply ENNReal.tsum_le_tsum
        intro i
        apply hN i
        simpa only [Finset.mem_range, not_lt] using i.property
      _ ≤ ∑' m : ℕ, g m :=
        ENNReal.tsum_comp_le_tsum_of_injective Subtype.coe_injective g
  have htailFinite :
      (∑' i : {i : ℕ // i ∉ Finset.range N}, f i) ≠ ∞ :=
    ne_top_of_le_ne_top hg htail
  rw [← ENNReal.sum_add_tsum_compl (Finset.range N) f]
  exact ENNReal.add_ne_top.mpr
    ⟨ENNReal.sum_ne_top.mpr (fun i _hi ↦ hf i), htailFinite⟩

/-- Polynomial pairing estimates are needed only eventually; their finite
initial segment contributes a finite amount to the Borel--Cantelli sum. -/
theorem hlozPlanarConclusion_of_eventually_concrete_pairing_polynomial_bounds
    {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hpair : ∀ᶠ m : ℕ in Filter.atTop, ∀ i : Fin 6,
      simpleRandomWalkLaw (firstFourPairingEvent m i) ≤
        ENNReal.ofReal (C / ((m : ℝ) + 1) ^ p)) :
    HLOZPlanarConclusion := by
  have hlevel : ∀ᶠ m : ℕ in Filter.atTop,
      simpleRandomWalkLaw (hlozFourSitesReachLevelFirst m) ≤
        ENNReal.ofReal ((6 * C) / ((m : ℝ) + 1) ^ p) := by
    filter_upwards [hpair] with m hm
    calc
      simpleRandomWalkLaw (hlozFourSitesReachLevelFirst m) ≤
          simpleRandomWalkLaw (⋃ i : Fin 6, firstFourPairingEvent m i) :=
        measure_mono (hlozFourSitesReachLevelFirst_subset_iUnion_firstFourPairingEvent m)
      _ ≤ ∑ i : Fin 6, simpleRandomWalkLaw (firstFourPairingEvent m i) :=
        measure_iUnion_fintype_le simpleRandomWalkLaw (firstFourPairingEvent m)
      _ ≤ ∑ _i : Fin 6,
          ENNReal.ofReal (C / ((m : ℝ) + 1) ^ p) := by
        exact Finset.sum_le_sum fun i _ ↦ hm i
      _ = 6 * ENNReal.ofReal (C / ((m : ℝ) + 1) ^ p) := by simp
      _ = ENNReal.ofReal ((6 * C) / ((m : ℝ) + 1) ^ p) := by
        rw [← ENNReal.ofReal_ofNat 6,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6)]
        congr 1
        ring
  have hsummable : Summable (fun m : ℕ ↦
      (6 * C) / ((m : ℝ) + 1) ^ p) := by
    have hbase := (Real.summable_one_div_nat_add_rpow 1 p).2 hp
    have hmul := hbase.mul_left (6 * C)
    exact hmul.congr (fun m ↦ by
      rw [abs_of_nonneg (by positivity : 0 ≤ (m : ℝ) + 1)]
      ring)
  have hnonneg : ∀ m : ℕ, 0 ≤ (6 * C) / ((m : ℝ) + 1) ^ p := by
    intro m
    positivity
  have hmajorant :
      (∑' m : ℕ, ENNReal.ofReal ((6 * C) / ((m : ℝ) + 1) ^ p)) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hsummable]
    exact ENNReal.ofReal_ne_top
  have hsum := ennreal_tsum_ne_top_of_eventually_le
    (fun m ↦ simpleRandomWalkLaw (hlozFourSitesReachLevelFirst m))
    (fun m ↦ ENNReal.ofReal ((6 * C) / ((m : ℝ) + 1) ^ p))
    (fun m ↦ measure_ne_top _ _) hlevel hmajorant
  exact hlozPlanarConclusion_of_level_tsum
    simpleRandomWalkLaw_maxLocalTime_tendsto (by
      simpa only [hlozFourSitesReachLevelFirst_eq_fourFavoritesAtLevel] using hsum)

/-- Eventual source screenings, with a finite exceptional prefactor, are the
direct interface needed by Proposition 4.7. -/
theorem hlozPlanarConclusion_of_eventually_prefactored_source_screenings
    (A B K : ℕ) (kappa : ℝ) (hkappa : 1 < 3 * kappa)
    (grid : ℕ → Fin 6 → Finset ι)
    (bad : ℕ → Fin 6 → Set (ℕ → Site))
    (E₀ E₁ E₂ E₃ : ℕ → Fin 6 → ι → Set (ℕ → Site))
    (hcard : ∀ m i, (grid m i).card ≤ K)
    (hcover : ∀ m i,
      firstFourPairingEvent m i ⊆ bad m i ∪ ⋃ a ∈ grid m i, E₃ m i a)
    (hsource : ∀ᶠ m : ℕ in Filter.atTop, ∀ i : Fin 6,
      simpleRandomWalkLaw (bad m i) ≤
          sourceExceptionalRateWithPrefactor m B kappa ∧
      (∀ a ∈ grid m i,
        StageBound simpleRandomWalkLaw (sourceStageRate m A kappa)
          (sourceExceptionalRateWithPrefactor m B kappa) (E₀ m i a) (E₁ m i a)) ∧
      (∀ a ∈ grid m i,
        StageBound simpleRandomWalkLaw (sourceStageRate m A kappa)
          (sourceExceptionalRateWithPrefactor m B kappa) (E₁ m i a) (E₂ m i a)) ∧
      (∀ a ∈ grid m i,
        StageBound simpleRandomWalkLaw (sourceStageRate m A kappa)
          (sourceExceptionalRateWithPrefactor m B kappa) (E₂ m i a) (E₃ m i a))) :
    HLOZPlanarConclusion := by
  apply hlozPlanarConclusion_of_eventually_concrete_pairing_polynomial_bounds
      (C := (sourcePrefactoredScreeningConstant A B K : ℝ))
      (p := 3 * kappa) (by positivity) hkappa
  filter_upwards [hsource] with m hm
  intro i
  exact pairingEvent_measure_le_of_prefactored_source_screenings
    m i A B K (by linarith) (grid m i) (bad m i)
    (E₀ m i) (E₁ m i) (E₂ m i) (E₃ m i)
    (hcard m i) (hcover m i) (hm i).1
    (hm i).2.1 (hm i).2.2.1 (hm i).2.2.2

end ScreeningBridge
end Erdos1166.HLOZPairing
