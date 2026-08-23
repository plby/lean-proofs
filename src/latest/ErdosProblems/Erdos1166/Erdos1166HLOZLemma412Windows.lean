import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Parameters
import ErdosProblems.Erdos1166.Erdos1166HLOZNegBinCompare

namespace Erdos1166.HLOZLemma412Windows

open Filter

open HLOZProp47Parameters
open HLOZUrn

/-- The integer width `ceil (m ^ κ₁)` of one source interval `I_ℓ`. -/
noncomputable def sourceCellWidth (m : ℕ) : ℕ :=
  Nat.ceil ((m : ℝ) ^ kappaOne)

/-- An integer envelope for the source deviation `c m ^ (1 - κ₁)`. -/
noncomputable def sourceDeviationWidth (c m : ℕ) : ℕ :=
  c * Nat.ceil ((m : ℝ) ^ (1 - kappaOne))

/-- The mean-band radius needed after converting total local time to lazy local time. -/
noncomputable def sourceMeanBandRadius (c m : ℕ) : ℕ :=
  2 * (sourceCellWidth m + sourceDeviationWidth c m)

/-- A safe fixed exponent in the mass-comparison constant. -/
def sourceComparisonExponent (c : ℕ) : ℕ := 1280 * (c + 1)

/-- Lower endpoint `a_ℓ = m - ℓ ceil(m^κ₁)`. -/
noncomputable def sourceIntervalLower (m ℓ : ℕ) : ℕ :=
  m - ℓ * sourceCellWidth m

/-- Upper endpoint `b_ℓ = m - (ℓ-1) ceil(m^κ₁)`. -/
noncomputable def sourceIntervalUpper (m ℓ : ℕ) : ℕ :=
  m - (ℓ - 1) * sourceCellWidth m

/-- The source endpoint `b_{ℓ-1}`, with the defining formula extended to `ℓ = 1`. -/
noncomputable def sourcePreviousUpper (m ℓ : ℕ) : ℕ :=
  m + sourceCellWidth m - (ℓ - 1) * sourceCellWidth m

/-- Upper endpoint used by the path-space Proposition-4.5 estimate for the
profile exception at level `ℓ`.  At the first level the formal adjacent band
extends above `m`, but it is empty on the below-`m` event, so the genuine
source interval stops at `m`.  From level two onward the relevant union is
the current band together with its preceding neighbor. -/
noncomputable def sourceThetaIntervalUpper (m ℓ : ℕ) : ℕ :=
  if ℓ = 1 then m else sourcePreviousUpper m ℓ

def InSourceInterval (m ℓ j : ℕ) : Prop :=
  sourceIntervalLower m ℓ ≤ j ∧ j < sourceIntervalUpper m ℓ

/-- Integer form of the external-local-time window in HLOZ Lemma 4.12. -/
def InSourceExternalWindow (c m ℓ i : ℕ) : Prop :=
  15 * sourceIntervalLower m ℓ ≤ 16 * i + 16 * sourceDeviationWidth c m ∧
    16 * i ≤ 15 * sourcePreviousUpper m ℓ + 16 * sourceDeviationWidth c m

/-- The paper's `bar p(i,j) = p(i,j-i)`. -/
noncomputable def barNegBinMass (i j : ℕ) : ℝ :=
  negBinMass i (j - i)

/-- Exact natural-number growth conditions used by the source-window specialization. -/
def SourceWindowGrowth (c m : ℕ) : Prop :=
  1 ≤ m ∧
    32 * sourceDeviationWidth c m ≤ m ∧
    60 * sourceCellWidth m + 32 * sourceDeviationWidth c m ≤ m ∧
    240 * (sourceCellWidth m + sourceDeviationWidth c m + 1) ≤ m ∧
    32 * sourceCellWidth m * (sourceMeanBandRadius c m + 1) ≤
      320 * (c + 1) * m

/-- A source interval whose lower endpoint is still at least `m / 2`. -/
def SourceIntervalIndex (m ℓ : ℕ) : Prop :=
  1 ≤ ℓ ∧ 2 * ℓ * sourceCellWidth m ≤ m

/-- A uniform cutoff covering the source range `ℓ ≤ m^(α-κ₁)+1` for `α < 4/5`. -/
noncomputable def sourceIntervalCutoff (m : ℕ) : ℕ :=
  Nat.ceil ((m : ℝ) ^ ((4 : ℝ) / 5 - kappaOne)) + 1

/-- The exact source interval count `floor (m^(α-κ₁)) + 1` from (4.43). -/
noncomputable def sourceAlphaIntervalCount (m : ℕ) (α : ℝ) : ℕ :=
  Nat.floor ((m : ℝ) ^ (α - kappaOne)) + 1

lemma kappaOne_pos : 0 < kappaOne := by
  norm_num [kappaOne]

lemma one_sub_kappaOne_pos : 0 < 1 - kappaOne := by
  norm_num [kappaOne]

lemma sourceCellWidth_cast_le (m : ℕ) (hm : 1 ≤ m) :
    (sourceCellWidth m : ℝ) ≤ 2 * (m : ℝ) ^ kappaOne := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpow : (1 : ℝ) ≤ (m : ℝ) ^ kappaOne :=
    Real.one_le_rpow hmR kappaOne_pos.le
  have hceil := Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity) kappaOne)
  dsimp [sourceCellWidth]
  linarith

lemma sourceDeviationWidth_cast_le (c m : ℕ) (hm : 1 ≤ m) :
    (sourceDeviationWidth c m : ℝ) ≤
      2 * c * (m : ℝ) ^ (1 - kappaOne) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpow : (1 : ℝ) ≤ (m : ℝ) ^ (1 - kappaOne) :=
    Real.one_le_rpow hmR one_sub_kappaOne_pos.le
  have hceil := Nat.ceil_lt_add_one
    (Real.rpow_nonneg (by positivity) (1 - kappaOne))
  dsimp [sourceDeviationWidth]
  push_cast
  nlinarith

lemma source_rpow_mul (m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) ^ kappaOne * (m : ℝ) ^ (1 - kappaOne) = m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  rw [← Real.rpow_add hmR]
  norm_num [Real.rpow_one]

lemma sourceCellWidth_rpow_mono (m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) ^ kappaOne ≤ (m : ℝ) ^ (1 - kappaOne) := by
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast hm
  norm_num [kappaOne]

lemma source_scale_bound (c m : ℕ) (hm : 1 ≤ m) :
    32 * sourceCellWidth m * (sourceMeanBandRadius c m + 1) ≤
      320 * (c + 1) * m := by
  have hs := sourceCellWidth_cast_le m hm
  have hd := sourceDeviationWidth_cast_le c m hm
  have hxy := sourceCellWidth_rpow_mono m hm
  have hy1 : (1 : ℝ) ≤ (m : ℝ) ^ (1 - kappaOne) := by
    apply Real.one_le_rpow
    · exact_mod_cast hm
    · exact one_sub_kappaOne_pos.le
  have hradiusR : (sourceMeanBandRadius c m + 1 : ℝ) ≤
      5 * (c + 1) * (m : ℝ) ^ (1 - kappaOne) := by
    dsimp [sourceMeanBandRadius]
    push_cast
    nlinarith
  have hprodR : (32 : ℝ) * sourceCellWidth m *
      (sourceMeanBandRadius c m + 1) ≤ 320 * (c + 1) * m := by
    calc
      (32 : ℝ) * sourceCellWidth m * (sourceMeanBandRadius c m + 1) ≤
          32 * (2 * (m : ℝ) ^ kappaOne) *
            (5 * (c + 1) * (m : ℝ) ^ (1 - kappaOne)) := by
              gcongr <;> positivity
      _ = 320 * (c + 1) *
          ((m : ℝ) ^ kappaOne * (m : ℝ) ^ (1 - kappaOne)) := by ring
      _ = 320 * (c + 1) * m := by rw [source_rpow_mul m hm]
  exact_mod_cast hprodR

/-- The source growth conditions hold for every sufficiently large local-time level. -/
theorem eventually_sourceWindowGrowth (c : ℕ) :
    ∀ᶠ m : ℕ in atTop, SourceWindowGrowth c m := by
  have hx : ∀ᶠ m : ℕ in atTop,
      (1440 * c : ℝ) ≤ (m : ℝ) ^ kappaOne :=
    ((tendsto_rpow_atTop kappaOne_pos).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1440 * c : ℝ))
  have hy : ∀ᶠ m : ℕ in atTop,
      (1440 : ℝ) ≤ (m : ℝ) ^ (1 - kappaOne) :=
    ((tendsto_rpow_atTop one_sub_kappaOne_pos).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1440 : ℝ))
  filter_upwards [hx, hy, eventually_ge_atTop 720] with m hxm hym hm720
  have hm : 1 ≤ m := by omega
  have hs := sourceCellWidth_cast_le m hm
  have hd := sourceDeviationWidth_cast_le c m hm
  have hmul := source_rpow_mul m hm
  have hx64 : (64 : ℝ) * c ≤ (m : ℝ) ^ kappaOne := by nlinarith
  have hx128 : (128 : ℝ) * c ≤ (m : ℝ) ^ kappaOne := by nlinarith
  have hy240 : (240 : ℝ) ≤ (m : ℝ) ^ (1 - kappaOne) := by nlinarith
  have hdev32R : (32 : ℝ) * sourceDeviationWidth c m ≤ m := by
    calc
      (32 : ℝ) * sourceDeviationWidth c m ≤
          64 * c * (m : ℝ) ^ (1 - kappaOne) := by nlinarith
      _ ≤ (m : ℝ) ^ kappaOne * (m : ℝ) ^ (1 - kappaOne) := by gcongr
      _ = m := hmul
  have hsumR : (60 : ℝ) * sourceCellWidth m +
      32 * sourceDeviationWidth c m ≤ m := by
    have hS : (120 : ℝ) * sourceCellWidth m ≤ m := by
      calc
        (120 : ℝ) * sourceCellWidth m ≤ 240 * (m : ℝ) ^ kappaOne := by nlinarith
        _ ≤ (m : ℝ) ^ kappaOne * (m : ℝ) ^ (1 - kappaOne) := by
          simpa only [mul_comm] using
            (mul_le_mul_of_nonneg_left hy240
              (Real.rpow_nonneg (show (0 : ℝ) ≤ m by positivity) kappaOne))
        _ = m := hmul
    have hD : (64 : ℝ) * sourceDeviationWidth c m ≤ m := by
      calc
        (64 : ℝ) * sourceDeviationWidth c m ≤
            128 * c * (m : ℝ) ^ (1 - kappaOne) := by nlinarith
        _ ≤ (m : ℝ) ^ kappaOne * (m : ℝ) ^ (1 - kappaOne) := by
          exact mul_le_mul_of_nonneg_right hx128 (Real.rpow_nonneg (by positivity) _)
        _ = m := hmul
    nlinarith
  have hlargeR : (240 : ℝ) *
      (sourceCellWidth m + sourceDeviationWidth c m + 1) ≤ m := by
    have hS : (720 : ℝ) * sourceCellWidth m ≤ m := by
      calc
        (720 : ℝ) * sourceCellWidth m ≤ 1440 * (m : ℝ) ^ kappaOne := by nlinarith
        _ ≤ (m : ℝ) ^ kappaOne * (m : ℝ) ^ (1 - kappaOne) := by
          simpa only [mul_comm] using
            (mul_le_mul_of_nonneg_left hym
              (Real.rpow_nonneg (show (0 : ℝ) ≤ m by positivity) kappaOne))
        _ = m := hmul
    have hD : (720 : ℝ) * sourceDeviationWidth c m ≤ m := by
      calc
        (720 : ℝ) * sourceDeviationWidth c m ≤
            1440 * c * (m : ℝ) ^ (1 - kappaOne) := by nlinarith
        _ ≤ (m : ℝ) ^ kappaOne * (m : ℝ) ^ (1 - kappaOne) := by
          exact mul_le_mul_of_nonneg_right hxm (Real.rpow_nonneg (by positivity) _)
        _ = m := hmul
    have hmR : (720 : ℝ) ≤ m := by exact_mod_cast hm720
    push_cast
    nlinarith
  exact ⟨hm, by exact_mod_cast hdev32R, by exact_mod_cast hsumR,
    by exact_mod_cast hlargeR, source_scale_bound c m hm⟩

lemma sourceIntervalCutoff_cast_le (m : ℕ) (hm : 1 ≤ m) :
    (sourceIntervalCutoff m : ℝ) ≤
      3 * (m : ℝ) ^ ((4 : ℝ) / 5 - kappaOne) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hexp : 0 ≤ (4 : ℝ) / 5 - kappaOne := by norm_num [kappaOne]
  have hpow : (1 : ℝ) ≤ (m : ℝ) ^ ((4 : ℝ) / 5 - kappaOne) :=
    Real.one_le_rpow hmR hexp
  have hceil := Nat.ceil_lt_add_one
    (Real.rpow_nonneg (show (0 : ℝ) ≤ m by positivity) ((4 : ℝ) / 5 - kappaOne))
  dsimp [sourceIntervalCutoff]
  push_cast
  linarith

lemma source_cutoff_rpow_mul (m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) ^ ((4 : ℝ) / 5 - kappaOne) * (m : ℝ) ^ kappaOne =
      (m : ℝ) ^ ((4 : ℝ) / 5) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  rw [← Real.rpow_add hmR]
  congr 1
  ring

lemma sourceAlphaIntervalCount_le_cutoff (m : ℕ) (hm : 1 ≤ m) {α : ℝ}
    (hα : α ≤ (4 : ℝ) / 5) :
    sourceAlphaIntervalCount m α ≤ sourceIntervalCutoff m := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hrpow : (m : ℝ) ^ (α - kappaOne) ≤
      (m : ℝ) ^ ((4 : ℝ) / 5 - kappaOne) := by
    apply Real.rpow_le_rpow_of_exponent_le hmR
    linarith
  have hfloor : (Nat.floor ((m : ℝ) ^ (α - kappaOne)) : ℝ) ≤
      Nat.ceil ((m : ℝ) ^ ((4 : ℝ) / 5 - kappaOne)) := by
    exact (Nat.floor_le (Real.rpow_nonneg (by positivity) _)).trans
      (hrpow.trans (Nat.le_ceil _))
  unfold sourceAlphaIntervalCount sourceIntervalCutoff
  exact Nat.add_le_add_right (by exact_mod_cast hfloor) 1

/-- In the range used by Proposition 4.8, all interval levels together move
the local-time endpoint by at most `4 m^(7/10)`.  This is sharper than the
generic `m/2` cutoff: it is the estimate which keeps the arbitrary
Proposition-4.5 endpoints above the fixed Proposition-4.4 threshold. -/
lemma sourceAlphaIntervalCount_mul_sourceCellWidth_cast_le
    (m : ℕ) (hm : 1 ≤ m) {α : ℝ}
    (hα0 : kappaOne ≤ α) (hα1 : α ≤ (7 : ℝ) / 10) :
    ((sourceAlphaIntervalCount m α * sourceCellWidth m : ℕ) : ℝ) ≤
      4 * (m : ℝ) ^ ((7 : ℝ) / 10) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmPos : (0 : ℝ) < m := lt_of_lt_of_le (by norm_num) hmR
  have hexp0 : 0 ≤ α - kappaOne := sub_nonneg.mpr hα0
  have hp1 : (1 : ℝ) ≤ (m : ℝ) ^ (α - kappaOne) :=
    Real.one_le_rpow hmR hexp0
  have hfloor :
      (Nat.floor ((m : ℝ) ^ (α - kappaOne)) : ℝ) ≤
        (m : ℝ) ^ (α - kappaOne) :=
    Nat.floor_le (Real.rpow_nonneg (by positivity) _)
  have hcount : (sourceAlphaIntervalCount m α : ℝ) ≤
      2 * (m : ℝ) ^ (α - kappaOne) := by
    unfold sourceAlphaIntervalCount
    push_cast
    linarith
  have hwidth := sourceCellWidth_cast_le m hm
  calc
    ((sourceAlphaIntervalCount m α * sourceCellWidth m : ℕ) : ℝ) =
        (sourceAlphaIntervalCount m α : ℝ) * sourceCellWidth m := by
          push_cast
          rfl
    _ ≤ (2 * (m : ℝ) ^ (α - kappaOne)) *
        (2 * (m : ℝ) ^ kappaOne) := by gcongr <;> positivity
    _ = 4 * ((m : ℝ) ^ (α - kappaOne) *
        (m : ℝ) ^ kappaOne) := by ring
    _ = 4 * (m : ℝ) ^ α := by
      rw [← Real.rpow_add hmPos]
      congr 2
      ring
    _ ≤ 4 * (m : ℝ) ^ ((7 : ℝ) / 10) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hmR hα1) (by norm_num)

/-- Every individual interval endpoint in the Proposition-4.8 range is at
least `m - 4 m^(7/10)`. -/
lemma sourceIntervalLower_cast_ge_of_le_alphaCount
    (m ℓ : ℕ) {α : ℝ} (hm : 1 ≤ m)
    (hα0 : kappaOne ≤ α) (hα1 : α ≤ (7 : ℝ) / 10)
    (hℓ : ℓ ≤ sourceAlphaIntervalCount m α)
    (hindex : SourceIntervalIndex m ℓ) :
    (m : ℝ) - 4 * (m : ℝ) ^ ((7 : ℝ) / 10) ≤
      sourceIntervalLower m ℓ := by
  have hfit : ℓ * sourceCellWidth m ≤ m := by
    calc
      ℓ * sourceCellWidth m ≤ 2 * (ℓ * sourceCellWidth m) := by omega
      _ = 2 * ℓ * sourceCellWidth m := by ring
      _ ≤ m := hindex.2
  have hprodNat : ℓ * sourceCellWidth m ≤
      sourceAlphaIntervalCount m α * sourceCellWidth m :=
    Nat.mul_le_mul_right (sourceCellWidth m) hℓ
  have hprod : ((ℓ * sourceCellWidth m : ℕ) : ℝ) ≤
      4 * (m : ℝ) ^ ((7 : ℝ) / 10) := by
    have hprodNatR : ((ℓ * sourceCellWidth m : ℕ) : ℝ) ≤
        ((sourceAlphaIntervalCount m α * sourceCellWidth m : ℕ) : ℝ) := by
      exact_mod_cast hprodNat
    exact hprodNatR.trans
      (sourceAlphaIntervalCount_mul_sourceCellWidth_cast_le
        m hm hα0 hα1)
  rw [sourceIntervalLower, Nat.cast_sub hfit]
  push_cast at hprod ⊢
  linarith

/-- Every interval up to the source's `m^(4/5-κ₁)` cutoff has lower endpoint at least `m/2`,
eventually and uniformly in the interval index. -/
theorem eventually_sourceIntervalIndex :
    ∀ᶠ m : ℕ in atTop, ∀ ℓ, 1 ≤ ℓ → ℓ ≤ sourceIntervalCutoff m →
      SourceIntervalIndex m ℓ := by
  have hp : ∀ᶠ m : ℕ in atTop,
      (12 : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 5) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (12 : ℝ))
  filter_upwards [hp, eventually_ge_atTop 1] with m hp hm ℓ hℓ hℓcut
  have hcut := sourceIntervalCutoff_cast_le m hm
  have hs := sourceCellWidth_cast_le m hm
  have hprod := source_cutoff_rpow_mul m hm
  have hpowOne : (m : ℝ) ^ ((4 : ℝ) / 5) * (m : ℝ) ^ ((1 : ℝ) / 5) = m := by
    have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    rw [← Real.rpow_add hmR]
    norm_num [Real.rpow_one]
  have hℓcutR : (ℓ : ℝ) ≤ sourceIntervalCutoff m := by exact_mod_cast hℓcut
  have hℓR : (ℓ : ℝ) ≤ 3 * (m : ℝ) ^ ((4 : ℝ) / 5 - kappaOne) :=
    hℓcutR.trans hcut
  have hmainR : (2 : ℝ) * ℓ * sourceCellWidth m ≤ m := by
    calc
      (2 : ℝ) * ℓ * sourceCellWidth m ≤
          2 * (3 * (m : ℝ) ^ ((4 : ℝ) / 5 - kappaOne)) *
            (2 * (m : ℝ) ^ kappaOne) := by gcongr <;> positivity
      _ = 12 *
          ((m : ℝ) ^ ((4 : ℝ) / 5 - kappaOne) * (m : ℝ) ^ kappaOne) := by ring
      _ = 12 * (m : ℝ) ^ ((4 : ℝ) / 5) := by rw [hprod]
      _ ≤ (m : ℝ) ^ ((4 : ℝ) / 5) * (m : ℝ) ^ ((1 : ℝ) / 5) := by
        simpa only [mul_comm] using
          (mul_le_mul_of_nonneg_left hp
            (Real.rpow_nonneg (show (0 : ℝ) ≤ m by positivity) ((4 : ℝ) / 5)))
      _ = m := hpowOne
  exact ⟨hℓ, by exact_mod_cast hmainR⟩

/-- A product form of the exponential comparison, separating band radius from interval width. -/
lemma negBinBandFactor_pow_le_exp_nat (i w d K : ℕ) (hi : 1 ≤ i)
    (hscale : 32 * d * (w + 1) ≤ K * i) :
    negBinBandFactor i w ^ d ≤ Real.exp K := by
  let x : ℝ := 32 * ((w : ℝ) + 1) / (i : ℝ)
  have hiR : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  have hfactor : negBinBandFactor i w ≤ Real.exp x := by
    dsimp [negBinBandFactor, x]
    simpa only [add_comm] using Real.add_one_le_exp (32 * ((w : ℝ) + 1) / (i : ℝ))
  have hdx : (d : ℝ) * x ≤ K := by
    dsimp [x]
    have hscaleR : (32 : ℝ) * d * (w + 1) ≤ K * i := by exact_mod_cast hscale
    rw [show (d : ℝ) * (32 * ((w : ℝ) + 1) / (i : ℝ)) =
        ((d : ℝ) * 32 * ((w : ℝ) + 1)) / (i : ℝ) by ring]
    apply (div_le_iff₀ hiR).2
    nlinarith
  calc
    negBinBandFactor i w ^ d ≤ (Real.exp x) ^ d :=
      pow_le_pow_left₀ (negBinBandFactor_nonneg i w) hfactor d
    _ = Real.exp ((d : ℝ) * x) := by rw [Real.exp_nat_mul]
    _ ≤ Real.exp K := Real.exp_le_exp.mpr hdx

lemma sourceInterval_endpoint_relations (m ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (hfit : ℓ * sourceCellWidth m ≤ m) :
    sourceIntervalUpper m ℓ = sourceIntervalLower m ℓ + sourceCellWidth m ∧
      sourcePreviousUpper m ℓ = sourceIntervalLower m ℓ + 2 * sourceCellWidth m := by
  have hℓeq : ℓ = (ℓ - 1) + 1 := by omega
  have hmul : ℓ * sourceCellWidth m =
      (ℓ - 1) * sourceCellWidth m + sourceCellWidth m := by
    conv_lhs => rw [hℓeq]
    rw [Nat.add_mul]
    simp only [one_mul]
  unfold sourceIntervalUpper sourceIntervalLower sourcePreviousUpper
  constructor <;> omega

lemma source_interval_arithmetic (c m ℓ i j : ℕ)
    (hℓ : 1 ≤ ℓ) (hhalf : m ≤ 2 * sourceIntervalLower m ℓ)
    (hgrowth : SourceWindowGrowth c m)
    (hiwin : InSourceExternalWindow c m ℓ i)
    (hj : InSourceInterval m ℓ j) :
    i ≤ j ∧ InNegBinMeanBand i (sourceMeanBandRadius c m) (j - i) := by
  rcases hgrowth with ⟨hm, hdev, hgap, hlarge, hscale⟩
  have hfit : ℓ * sourceCellWidth m ≤ m := by
    by_contra h
    have hzero : sourceIntervalLower m ℓ = 0 := by
      unfold sourceIntervalLower
      exact Nat.sub_eq_zero_of_le (by omega)
    omega
  obtain ⟨hupper, hprev⟩ := sourceInterval_endpoint_relations m ℓ hℓ hfit
  have hclose : 30 * sourceCellWidth m + 16 * sourceDeviationWidth c m ≤
      sourceIntervalLower m ℓ := by omega
  have hiLower : i ≤ sourceIntervalLower m ℓ := by
    unfold InSourceExternalWindow at hiwin
    omega
  have hij : i ≤ j := hiLower.trans hj.1
  refine ⟨hij, ?_⟩
  unfold InNegBinMeanBand
  unfold InSourceExternalWindow at hiwin
  unfold InSourceInterval at hj
  unfold sourceMeanBandRadius
  omega

/-- Source-facing form of HLOZ Lemma 4.12: masses in one `I_ℓ` are comparable. -/
theorem barNegBinMass_compare_sourceInterval (c m ℓ i j₁ j₂ : ℕ)
    (hindex : SourceIntervalIndex m ℓ) (hgrowth : SourceWindowGrowth c m)
    (hiwin : InSourceExternalWindow c m ℓ i)
    (h₁₂ : j₁ ≤ j₂) (hj₁ : InSourceInterval m ℓ j₁)
    (hj₂ : InSourceInterval m ℓ j₂) :
    barNegBinMass i j₂ ≤ Real.exp (sourceComparisonExponent c) * barNegBinMass i j₁ ∧
      barNegBinMass i j₁ ≤ Real.exp (sourceComparisonExponent c) * barNegBinMass i j₂ := by
  rcases hindex with ⟨hℓ, hindex⟩
  have hell_double : ℓ ≤ 2 * ℓ := by omega
  have hfit : ℓ * sourceCellWidth m ≤ m :=
    (Nat.mul_le_mul_right (sourceCellWidth m) hell_double).trans hindex
  have hindex' : 2 * (ℓ * sourceCellWidth m) ≤ m := by
    calc
      2 * (ℓ * sourceCellWidth m) = 2 * ℓ * sourceCellWidth m := by ring
      _ ≤ m := hindex
  have hhalf : m ≤ 2 * sourceIntervalLower m ℓ := by
    unfold sourceIntervalLower
    omega
  obtain ⟨hi₁, hband₁⟩ :=
    source_interval_arithmetic c m ℓ i j₁ hℓ hhalf hgrowth hiwin hj₁
  obtain ⟨hi₂, hband₂⟩ :=
    source_interval_arithmetic c m ℓ i j₂ hℓ hhalf hgrowth hiwin hj₂
  rcases hgrowth with ⟨hm, hdev, hgap, hlarge, hsourceScale⟩
  have hmi : m ≤ 4 * i := by
    unfold InSourceExternalWindow at hiwin
    omega
  have hi : 1 ≤ i := by omega
  have hsize : 30 * (sourceMeanBandRadius c m + 1) ≤ i := by
    unfold sourceMeanBandRadius
    omega
  have hdistTotal : j₂ - j₁ ≤ sourceCellWidth m := by
    obtain ⟨hupper, hprev⟩ := sourceInterval_endpoint_relations m ℓ hℓ hfit
    unfold InSourceInterval at hj₁ hj₂
    omega
  have hdiff : (j₂ - i) - (j₁ - i) = j₂ - j₁ := by omega
  have hdist : (j₂ - i) - (j₁ - i) ≤ sourceCellWidth m := by
    rw [hdiff]
    exact hdistTotal
  have hscaleM : 320 * (c + 1) * m ≤ sourceComparisonExponent c * i := by
    have hmul := Nat.mul_le_mul_left (320 * (c + 1)) hmi
    convert hmul using 1 <;> simp [sourceComparisonExponent] <;> ring
  have hscale :
      32 * ((j₂ - i) - (j₁ - i)) * (sourceMeanBandRadius c m + 1) ≤
        sourceComparisonExponent c * i := by
    apply le_trans _ hscaleM
    apply le_trans _ hsourceScale
    exact Nat.mul_le_mul_right (sourceMeanBandRadius c m + 1)
      (Nat.mul_le_mul_left 32 hdist)
  have hpow := negBinBandFactor_pow_le_exp_nat i (sourceMeanBandRadius c m)
    ((j₂ - i) - (j₁ - i)) (sourceComparisonExponent c) hi hscale
  have hlazy : j₁ - i ≤ j₂ - i := Nat.sub_le_sub_right h₁₂ i
  constructor
  · unfold barNegBinMass
    exact (negBinMass_forward_pow i (sourceMeanBandRadius c m) (j₁ - i) (j₂ - i)
      hi hsize hlazy hband₁ hband₂).trans
        (mul_le_mul_of_nonneg_right hpow (negBinMass_nonneg i (j₁ - i)))
  · unfold barNegBinMass
    exact (negBinMass_reverse_pow i (sourceMeanBandRadius c m) (j₁ - i) (j₂ - i)
      hi hlazy hband₁ hband₂).trans
        (mul_le_mul_of_nonneg_right hpow (negBinMass_nonneg i (j₂ - i)))

/-- The exact external-count window in equation (4.58). -/
def InEquation458ExternalWindow (c m i : ℕ) : Prop :=
  15 * (m - sourceCellWidth m) ≤ 16 * i + 16 * sourceDeviationWidth c m ∧
    16 * i ≤ 15 * m + 16 * sourceDeviationWidth c m

/-- Equation (4.58), with the source window `(m-m^κ₁,m)` rounded by
`sourceCellWidth`, and with the explicit fixed comparison constant
`exp (1280(c+1))`. -/
theorem barNegBinMass_compare_equation458 (c m i j₁ j₂ : ℕ)
    (hgrowth : SourceWindowGrowth c m) (hiwin : InEquation458ExternalWindow c m i)
    (h₁₂ : j₁ ≤ j₂) (hj₁ : m - sourceCellWidth m ≤ j₁ ∧ j₁ < m)
    (hj₂ : m - sourceCellWidth m ≤ j₂ ∧ j₂ < m) :
    barNegBinMass i j₂ ≤ Real.exp (sourceComparisonExponent c) * barNegBinMass i j₁ ∧
      barNegBinMass i j₁ ≤ Real.exp (sourceComparisonExponent c) * barNegBinMass i j₂ := by
  have hindex : SourceIntervalIndex m 1 := by
    refine ⟨by omega, ?_⟩
    rcases hgrowth with ⟨hm, hdev, hgap, hlarge, hscale⟩
    omega
  have hiwin' : InSourceExternalWindow c m 1 i := by
    unfold InEquation458ExternalWindow at hiwin
    unfold InSourceExternalWindow sourceIntervalLower sourcePreviousUpper
    simp only [one_mul, Nat.sub_self, zero_mul, Nat.sub_zero]
    omega
  have hj₁' : InSourceInterval m 1 j₁ := by
    unfold InSourceInterval sourceIntervalLower sourceIntervalUpper
    simpa using hj₁
  have hj₂' : InSourceInterval m 1 j₂ := by
    unfold InSourceInterval sourceIntervalLower sourceIntervalUpper
    simpa using hj₂
  exact barNegBinMass_compare_sourceInterval c m 1 i j₁ j₂
    hindex hgrowth hiwin' h₁₂ hj₁' hj₂'

/-- Uniform source form: for all sufficiently large `m`, every interval `I_ℓ`
in the full HLOZ range `ℓ ≤ floor(m^(α-κ₁))+1`, uniformly for
`κ₁ ≤ α ≤ 4/5`, satisfies the fixed mass-comparison estimate. -/
theorem eventually_barNegBinMass_compare_all_sourceIntervals (c : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (α : ℝ) (ℓ i j₁ j₂ : ℕ),
      kappaOne ≤ α → α ≤ (4 : ℝ) / 5 → 1 ≤ ℓ →
      ℓ ≤ sourceAlphaIntervalCount m α →
      InSourceExternalWindow c m ℓ i → j₁ ≤ j₂ →
      InSourceInterval m ℓ j₁ → InSourceInterval m ℓ j₂ →
      barNegBinMass i j₂ ≤ Real.exp (sourceComparisonExponent c) * barNegBinMass i j₁ ∧
        barNegBinMass i j₁ ≤ Real.exp (sourceComparisonExponent c) * barNegBinMass i j₂ := by
  filter_upwards [eventually_sourceWindowGrowth c, eventually_sourceIntervalIndex]
    with m hgrowth hindices α ℓ i j₁ j₂ hκα hα hℓ hℓcount hiwin h₁₂ hj₁ hj₂
  have hm : 1 ≤ m := hgrowth.1
  have hcut : ℓ ≤ sourceIntervalCutoff m :=
    hℓcount.trans (sourceAlphaIntervalCount_le_cutoff m hm hα)
  exact barNegBinMass_compare_sourceInterval c m ℓ i j₁ j₂
    (hindices ℓ hℓ hcut) hgrowth hiwin h₁₂ hj₁ hj₂

end Erdos1166.HLOZLemma412Windows
