import ErdosProblems.Erdos1166.Erdos1166HLOZLemma412Windows
import ErdosProblems.Erdos1166.Erdos1166HLOZFiniteUnion
import ErdosProblems.Erdos1166.Erdos1166HLOZLemma411

namespace Erdos1166.HLOZBandRatios

open Filter
open scoped BigOperators ENNReal

open HLOZProp47Parameters
open HLOZUrn
open HLOZLemma412Windows

/-- Total mass of a finite integer band. -/
noncomputable def bandMass (p : ℕ → ℝ) (A : Finset ℕ) : ℝ :=
  ∑ j ∈ A, p j

lemma bandMass_nonneg {p : ℕ → ℝ} (hp : ∀ j, 0 ≤ p j) (A : Finset ℕ) :
    0 ≤ bandMass p A := by
  unfold bandMass
  exact Finset.sum_nonneg fun j _hj ↦ hp j

/-- Summing a pointwise comparison over two finite bands, retaining both cardinalities. -/
lemma card_mul_bandMass_le_of_pointwise
    {p : ℕ → ℝ} {A B : Finset ℕ} {C : ℝ}
    (hcomp : ∀ a ∈ A, ∀ b ∈ B, p a ≤ C * p b) :
    (B.card : ℝ) * bandMass p A ≤ C * A.card * bandMass p B := by
  calc
    (B.card : ℝ) * bandMass p A =
        ∑ a ∈ A, ∑ _b ∈ B, p a := by
      simp [bandMass, Finset.mul_sum]
    _ ≤ ∑ a ∈ A, ∑ b ∈ B, C * p b := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact hcomp a ha b hb
    _ = C * A.card * bandMass p B := by
      simp [bandMass, Finset.mul_sum]
      ring

/-- Equal-cardinality bands inherit the pointwise multiplicative comparison. -/
lemma bandMass_le_of_pointwise_of_card_eq
    {p : ℕ → ℝ} {A B : Finset ℕ} {C : ℝ}
    (hcard : A.card = B.card) (hpos : 0 < A.card)
    (hcomp : ∀ a ∈ A, ∀ b ∈ B, p a ≤ C * p b) :
    bandMass p A ≤ C * bandMass p B := by
  have h := card_mul_bandMass_le_of_pointwise hcomp
  rw [← hcard] at h
  apply le_of_mul_le_mul_left (a := (A.card : ℝ)) _ (by positivity)
  calc
    (A.card : ℝ) * bandMass p A ≤ C * A.card * bandMass p B := h
    _ = (A.card : ℝ) * (C * bandMass p B) := by ring

/-- If the target band has at least as many points as the source band, the
same pointwise multiplicative comparison still controls their total masses.
Only the source band needs to be nonempty. -/
lemma bandMass_le_of_pointwise_of_card_le
    {p : ℕ → ℝ} {A B : Finset ℕ} {C : ℝ}
    (hp : ∀ j, 0 ≤ p j)
    (hcard : A.card ≤ B.card) (hpos : 0 < A.card)
    (hcomp : ∀ a ∈ A, ∀ b ∈ B, p a ≤ C * p b) :
    bandMass p A ≤ C * bandMass p B := by
  have h := card_mul_bandMass_le_of_pointwise hcomp
  have hA : 0 ≤ bandMass p A := bandMass_nonneg hp A
  have hcard' : (A.card : ℝ) ≤ B.card := by exact_mod_cast hcard
  apply le_of_mul_le_mul_left (a := (A.card : ℝ)) _ (by positivity)
  calc
    (A.card : ℝ) * bandMass p A ≤
        (B.card : ℝ) * bandMass p A :=
      mul_le_mul_of_nonneg_right hcard' hA
    _ ≤ C * A.card * bandMass p B := h
    _ = (A.card : ℝ) * (C * bandMass p B) := by ring

/-- The conditional Bernoulli parameter of the first of two finite bands. -/
noncomputable def twoBandParameter (p : ℕ → ℝ) (A B : Finset ℕ) : ℝ :=
  bandMass p A / (bandMass p A + bandMass p B)

/-- If the first band has at most `C` times the mass of the second, its
conditional Bernoulli parameter is at most `C/(1+C)`. -/
lemma twoBandParameter_le {p : ℕ → ℝ} (hp : ∀ j, 0 ≤ p j)
    (A B : Finset ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hcomp : bandMass p A ≤ C * bandMass p B) :
    twoBandParameter p A B ≤ C / (1 + C) := by
  have hA := bandMass_nonneg hp A
  have hB := bandMass_nonneg hp B
  by_cases hB0 : bandMass p B = 0
  · have hA0 : bandMass p A = 0 := by nlinarith
    rw [twoBandParameter, hA0, hB0]
    simp only [zero_add, zero_div]
    exact div_nonneg hC (by linarith)
  · have hBpos : 0 < bandMass p B := lt_of_le_of_ne hB (Ne.symm hB0)
    unfold twoBandParameter
    rw [div_le_div_iff₀ (by positivity : 0 < bandMass p A + bandMass p B)
      (by linarith : 0 < 1 + C)]
    nlinarith

/-- Ratio of the mass in a narrow band to the mass in a broad band. -/
noncomputable def bandRatio (p : ℕ → ℝ) (narrow broad : Finset ℕ) : ℝ :=
  bandMass p narrow / bandMass p broad

/-- Cardinality-aware comparison of a narrow-band ratio. -/
lemma bandRatio_le_card_ratio_of_pointwise
    {p : ℕ → ℝ} (hp : ∀ j, 0 ≤ p j)
    (narrow broad : Finset ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hbroad : 0 < broad.card)
    (hcomp : ∀ a ∈ narrow, ∀ b ∈ broad, p a ≤ C * p b) :
    bandRatio p narrow broad ≤ C * narrow.card / broad.card := by
  have hdouble := card_mul_bandMass_le_of_pointwise hcomp
  have hn := bandMass_nonneg hp narrow
  have hb := bandMass_nonneg hp broad
  by_cases hb0 : bandMass p broad = 0
  · have hn0 : bandMass p narrow = 0 := by
      have hcardR : (0 : ℝ) < broad.card := by exact_mod_cast hbroad
      have hdouble' : (broad.card : ℝ) * bandMass p narrow ≤ 0 := by
        simpa [hb0] using hdouble
      by_contra hn0
      have hnpos : 0 < bandMass p narrow := lt_of_le_of_ne hn (Ne.symm hn0)
      nlinarith [mul_pos hcardR hnpos]
    rw [bandRatio, hn0, hb0]
    simp only [zero_div]
    exact div_nonneg (mul_nonneg hC (by positivity)) (by positivity)
  · have hbpos : 0 < bandMass p broad := lt_of_le_of_ne hb (Ne.symm hb0)
    unfold bandRatio
    rw [div_le_div_iff₀ hbpos (by exact_mod_cast hbroad)]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hdouble

/-- The lower cell `I_ℓ`. -/
noncomputable def sourceLowerBand (m ℓ : ℕ) : Finset ℕ :=
  Finset.Ico (sourceIntervalLower m ℓ) (sourceIntervalUpper m ℓ)

/-- Its adjacent upper cell `I_{ℓ-1}`, expressed using the shared endpoint. -/
noncomputable def sourceUpperAdjacentBand (m ℓ : ℕ) : Finset ℕ :=
  Finset.Ico (sourceIntervalUpper m ℓ) (sourcePreviousUpper m ℓ)

def sourceAdjacentComparisonExponent (c : ℕ) : ℕ :=
  2 * sourceComparisonExponent c

/-- The geometric recursion factor supplied to the Lemma 4.11 assembly. -/
noncomputable def sourceLemma411GrowthFactor (c : ℕ) : ℝ :=
  2 * Real.exp (sourceAdjacentComparisonExponent c)

lemma sourceLemma411GrowthFactor_one_le (c : ℕ) :
    1 ≤ sourceLemma411GrowthFactor c := by
  unfold sourceLemma411GrowthFactor
  have := Real.one_le_exp (show (0 : ℝ) ≤ sourceAdjacentComparisonExponent c by positivity)
  nlinarith

lemma source_union_interval_arithmetic (c m ℓ i j : ℕ)
    (hindex : SourceIntervalIndex m ℓ) (hgrowth : SourceWindowGrowth c m)
    (hiwin : InSourceExternalWindow c m ℓ i)
    (hj : sourceIntervalLower m ℓ ≤ j ∧ j < sourcePreviousUpper m ℓ) :
    i ≤ j ∧ InNegBinMeanBand i (sourceMeanBandRadius c m) (j - i) := by
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
  obtain ⟨hupper, hprev⟩ := sourceInterval_endpoint_relations m ℓ hℓ hfit
  rcases hgrowth with ⟨hm, hdev, hgap, hlarge, hscale⟩
  have hclose : 30 * sourceCellWidth m + 16 * sourceDeviationWidth c m ≤
      sourceIntervalLower m ℓ := by omega
  have hiLower : i ≤ sourceIntervalLower m ℓ := by
    unfold InSourceExternalWindow at hiwin
    omega
  have hij : i ≤ j := hiLower.trans hj.1
  refine ⟨hij, ?_⟩
  unfold InNegBinMeanBand sourceMeanBandRadius
  unfold InSourceExternalWindow at hiwin
  omega

theorem barNegBinMass_compare_adjacentUnion (c m ℓ i j₁ j₂ : ℕ)
    (hindex : SourceIntervalIndex m ℓ) (hgrowth : SourceWindowGrowth c m)
    (hiwin : InSourceExternalWindow c m ℓ i)
    (hj₁ : sourceIntervalLower m ℓ ≤ j₁ ∧ j₁ < sourcePreviousUpper m ℓ)
    (hj₂ : sourceIntervalLower m ℓ ≤ j₂ ∧ j₂ < sourcePreviousUpper m ℓ) :
    barNegBinMass i j₁ ≤ Real.exp (sourceAdjacentComparisonExponent c) * barNegBinMass i j₂ := by
  obtain ⟨hi₁, hband₁⟩ := source_union_interval_arithmetic c m ℓ i j₁
    hindex hgrowth hiwin hj₁
  obtain ⟨hi₂, hband₂⟩ := source_union_interval_arithmetic c m ℓ i j₂
    hindex hgrowth hiwin hj₂
  rcases hindex with ⟨hℓ, hindex⟩
  have hell_double : ℓ ≤ 2 * ℓ := by omega
  have hfit : ℓ * sourceCellWidth m ≤ m :=
    (Nat.mul_le_mul_right (sourceCellWidth m) hell_double).trans hindex
  obtain ⟨hupper, hprev⟩ := sourceInterval_endpoint_relations m ℓ hℓ hfit
  rcases hgrowth with ⟨hm, hdev, hgap, hlarge, hsourceScale⟩
  have hmi : m ≤ 4 * i := by
    unfold InSourceExternalWindow at hiwin
    have hindex' : 2 * (ℓ * sourceCellWidth m) ≤ m := by
      calc
        2 * (ℓ * sourceCellWidth m) = 2 * ℓ * sourceCellWidth m := by ring
        _ ≤ m := hindex
    have hhalf : m ≤ 2 * sourceIntervalLower m ℓ := by
      unfold sourceIntervalLower
      omega
    omega
  have hi : 1 ≤ i := by omega
  have hsize : 30 * (sourceMeanBandRadius c m + 1) ≤ i := by
    unfold sourceMeanBandRadius
    omega
  have hscaleM : 640 * (c + 1) * m ≤ sourceAdjacentComparisonExponent c * i := by
    have hmul := Nat.mul_le_mul_left (640 * (c + 1)) hmi
    convert hmul using 1 <;> simp [sourceAdjacentComparisonExponent,
      sourceComparisonExponent] <;> ring
  have sourceScaleTwo :
      32 * (2 * sourceCellWidth m) * (sourceMeanBandRadius c m + 1) ≤
        640 * (c + 1) * m := by
    have htwice := Nat.mul_le_mul_left 2 hsourceScale
    convert htwice using 1 <;> ring
  have compare_ordered (x y : ℕ)
      (hx : sourceIntervalLower m ℓ ≤ x ∧ x < sourcePreviousUpper m ℓ)
      (hy : sourceIntervalLower m ℓ ≤ y ∧ y < sourcePreviousUpper m ℓ)
      (hix : i ≤ x) (hiy : i ≤ y) (hxy : x ≤ y)
      (hbandx : InNegBinMeanBand i (sourceMeanBandRadius c m) (x - i))
      (hbandy : InNegBinMeanBand i (sourceMeanBandRadius c m) (y - i)) :
      barNegBinMass i x ≤
          Real.exp (sourceAdjacentComparisonExponent c) * barNegBinMass i y ∧
        barNegBinMass i y ≤
          Real.exp (sourceAdjacentComparisonExponent c) * barNegBinMass i x := by
    have hdistTotal : y - x ≤ 2 * sourceCellWidth m := by omega
    have hdiff : (y - i) - (x - i) = y - x := by omega
    have hdist : (y - i) - (x - i) ≤ 2 * sourceCellWidth m := by
      rw [hdiff]
      exact hdistTotal
    have hscale :
        32 * ((y - i) - (x - i)) * (sourceMeanBandRadius c m + 1) ≤
          sourceAdjacentComparisonExponent c * i := by
      apply le_trans _ hscaleM
      apply le_trans _ sourceScaleTwo
      exact Nat.mul_le_mul_right (sourceMeanBandRadius c m + 1)
        (Nat.mul_le_mul_left 32 hdist)
    have hpow := negBinBandFactor_pow_le_exp_nat i (sourceMeanBandRadius c m)
      ((y - i) - (x - i)) (sourceAdjacentComparisonExponent c) hi hscale
    have hlazy : x - i ≤ y - i := Nat.sub_le_sub_right hxy i
    constructor
    · unfold barNegBinMass
      exact (negBinMass_reverse_pow i (sourceMeanBandRadius c m) (x - i) (y - i)
        hi hlazy hbandx hbandy).trans
          (mul_le_mul_of_nonneg_right hpow (negBinMass_nonneg i (y - i)))
    · unfold barNegBinMass
      exact (negBinMass_forward_pow i (sourceMeanBandRadius c m) (x - i) (y - i)
        hi hsize hlazy hbandx hbandy).trans
          (mul_le_mul_of_nonneg_right hpow (negBinMass_nonneg i (x - i)))
  rcases le_total j₁ j₂ with h₁₂ | h₂₁
  · exact (compare_ordered j₁ j₂ hj₁ hj₂ hi₁ hi₂ h₁₂ hband₁ hband₂).1
  · exact (compare_ordered j₂ j₁ hj₂ hj₁ hi₂ hi₁ h₂₁ hband₂ hband₁).2

/-- Exact conditional ratio used in (4.48), for the two adjacent equal-width bands. -/
theorem adjacentBandParameter_le (c m ℓ i : ℕ)
    (hindex : SourceIntervalIndex m ℓ) (hgrowth : SourceWindowGrowth c m)
    (hiwin : InSourceExternalWindow c m ℓ i) :
    twoBandParameter (barNegBinMass i) (sourceLowerBand m ℓ)
        (sourceUpperAdjacentBand m ℓ) ≤
      Real.exp (sourceAdjacentComparisonExponent c) /
        (1 + Real.exp (sourceAdjacentComparisonExponent c)) := by
  rcases hindex with ⟨hℓ, hindex⟩
  have hell_double : ℓ ≤ 2 * ℓ := by omega
  have hfit : ℓ * sourceCellWidth m ≤ m :=
    (Nat.mul_le_mul_right (sourceCellWidth m) hell_double).trans hindex
  obtain ⟨hupper, hprev⟩ := sourceInterval_endpoint_relations m ℓ hℓ hfit
  have hspos : 0 < sourceCellWidth m := by
    unfold sourceCellWidth
    apply Nat.ceil_pos.mpr
    have hm : 1 ≤ m := hgrowth.1
    exact Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < m by omega)) _
  have hcardLower : (sourceLowerBand m ℓ).card = sourceCellWidth m := by
    simp [sourceLowerBand, hupper]
  have hcardUpper : (sourceUpperAdjacentBand m ℓ).card = sourceCellWidth m := by
    simp [sourceUpperAdjacentBand, hupper, hprev]
    omega
  have hlowerupper : sourceIntervalLower m ℓ ≤ sourceIntervalUpper m ℓ := by omega
  have huprev : sourceIntervalUpper m ℓ ≤ sourcePreviousUpper m ℓ := by omega
  apply twoBandParameter_le (fun j ↦ negBinMass_nonneg i (j - i))
    _ _ (Real.exp_nonneg _)
  apply bandMass_le_of_pointwise_of_card_eq
      (hcardLower.trans hcardUpper.symm) (by simpa [hcardLower] using hspos)
  intro a ha b hb
  have ha' : sourceIntervalLower m ℓ ≤ a ∧ a < sourcePreviousUpper m ℓ := by
    simp only [sourceLowerBand, Finset.mem_Ico] at ha
    exact ⟨ha.1, ha.2.trans_le huprev⟩
  have hb' : sourceIntervalLower m ℓ ≤ b ∧ b < sourcePreviousUpper m ℓ := by
    simp only [sourceUpperAdjacentBand, Finset.mem_Ico] at hb
    exact ⟨hlowerupper.trans hb.1, hb.2⟩
  exact barNegBinMass_compare_adjacentUnion c m ℓ i a b
    ⟨hℓ, hindex⟩ hgrowth hiwin ha' hb'

/-- Open top band `(m-w,m)` used in (4.58). -/
def openTopBand (m w : ℕ) : Finset ℕ :=
  Finset.Ico (m - w + 1) m

/-- Rounded source narrow width `ceil(m^α)`. -/
noncomputable def sourceNarrowWidth (m : ℕ) (α : ℝ) : ℕ :=
  Nat.ceil ((m : ℝ) ^ α)

lemma sourceNarrowWidth_le_cell (m : ℕ) (hm : 1 ≤ m) {α : ℝ}
    (hα : α ≤ kappaOne) : sourceNarrowWidth m α ≤ sourceCellWidth m := by
  unfold sourceNarrowWidth sourceCellWidth
  apply Nat.ceil_mono
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm) hα

lemma openTopBand_card (m w : ℕ) (hwpos : 1 ≤ w) (hwm : w ≤ m) :
    (openTopBand m w).card = w - 1 := by
  simp [openTopBand]
  omega

/-- The exact finite-sum narrow/broad ratio behind equation (4.58). -/
theorem equation458_bandRatio_le_cardRatio (c m i : ℕ) (α : ℝ)
    (hgrowth : SourceWindowGrowth c m) (hiwin : InEquation458ExternalWindow c m i)
    (hα0 : 0 ≤ α) (hα : α ≤ kappaOne) :
    bandRatio (barNegBinMass i) (openTopBand m (sourceNarrowWidth m α))
        (openTopBand m (sourceCellWidth m)) ≤
      Real.exp (sourceComparisonExponent c) *
        (openTopBand m (sourceNarrowWidth m α)).card /
        (openTopBand m (sourceCellWidth m)).card := by
  have hm : 1 ≤ m := hgrowth.1
  have hnle : sourceNarrowWidth m α ≤ sourceCellWidth m :=
    sourceNarrowWidth_le_cell m hm hα
  have hspos : 0 < sourceCellWidth m := by
    unfold sourceCellWidth
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < m by omega)) _)
  have hmLarge : 2 ≤ m := by
    rcases hgrowth with ⟨hm, hdev, hgap, hlarge, hscale⟩
    omega
  have hsTwo : 2 ≤ sourceCellWidth m := by
    unfold sourceCellWidth
    rw [← Nat.lt_iff_add_one_le, Nat.lt_ceil]
    norm_num only [Nat.cast_one]
    exact Real.one_lt_rpow
      (show (1 : ℝ) < (m : ℝ) by exact_mod_cast (show 1 < m by omega)) kappaOne_pos
  have hsm : sourceCellWidth m ≤ m := by
    rcases hgrowth with ⟨hm, hdev, hgap, hlarge, hscale⟩
    omega
  have hbcard : 0 < (openTopBand m (sourceCellWidth m)).card := by
    rw [openTopBand_card m (sourceCellWidth m) (by omega) hsm]
    omega
  apply bandRatio_le_card_ratio_of_pointwise
    (fun j ↦ negBinMass_nonneg i (j - i)) _ _ (Real.exp_nonneg _) hbcard
  intro a ha b hb
  have haMem : m - sourceCellWidth m ≤ a ∧ a < m := by
    have ha' := (Finset.mem_Ico.mp ha)
    exact ⟨(Nat.sub_le_sub_left hnle m).trans (by omega), ha'.2⟩
  have hbMem : m - sourceCellWidth m ≤ b ∧ b < m := by
    have hb' := (Finset.mem_Ico.mp hb)
    exact ⟨by omega, hb'.2⟩
  rcases le_total a b with hab | hba
  · exact (barNegBinMass_compare_equation458 c m i a b hgrowth hiwin hab haMem hbMem).2
  · exact (barNegBinMass_compare_equation458 c m i b a hgrowth hiwin hba hbMem haMem).1

/-- Polynomial form of the one-coordinate narrow/broad estimate used by
`HLOZFiniteUnion.polynomialBandRatio`. -/
theorem equation458_bandRatio_le_rpow (c m i : ℕ) (α : ℝ)
    (hgrowth : SourceWindowGrowth c m) (hiwin : InEquation458ExternalWindow c m i)
    (hα0 : 0 ≤ α) (hα : α < kappaOne) :
    bandRatio (barNegBinMass i) (openTopBand m (sourceNarrowWidth m α))
        (openTopBand m (sourceCellWidth m)) ≤
      4 * Real.exp (sourceComparisonExponent c) * (m : ℝ) ^ (α - kappaOne) := by
  have hm : 1 ≤ m := hgrowth.1
  have hnle : sourceNarrowWidth m α ≤ sourceCellWidth m :=
    sourceNarrowWidth_le_cell m hm hα.le
  have hnpos : 1 ≤ sourceNarrowWidth m α := by
    unfold sourceNarrowWidth
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < m by omega)) _)
  have hspos : 0 < sourceCellWidth m := by
    unfold sourceCellWidth
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < m by omega)) _)
  have hmLarge : 2 ≤ m := by
    rcases hgrowth with ⟨hm, hdev, hgap, hlarge, hscale⟩
    omega
  have hsTwo : 2 ≤ sourceCellWidth m := by
    unfold sourceCellWidth
    rw [← Nat.lt_iff_add_one_le, Nat.lt_ceil]
    norm_num only [Nat.cast_one]
    exact Real.one_lt_rpow
      (show (1 : ℝ) < (m : ℝ) by exact_mod_cast (show 1 < m by omega)) kappaOne_pos
  have hsm : sourceCellWidth m ≤ m := by
    rcases hgrowth with ⟨hm, hdev, hgap, hlarge, hscale⟩
    omega
  have hnm : sourceNarrowWidth m α ≤ m := hnle.trans hsm
  have hNcard : (openTopBand m (sourceNarrowWidth m α)).card =
      sourceNarrowWidth m α - 1 := openTopBand_card _ _ hnpos hnm
  have hBcard : (openTopBand m (sourceCellWidth m)).card =
      sourceCellWidth m - 1 := openTopBand_card _ _ (by omega) hsm
  have hBpos : 0 < (openTopBand m (sourceCellWidth m)).card := by
    rw [hBcard]
    omega
  have hnCast : (sourceNarrowWidth m α : ℝ) ≤ 2 * (m : ℝ) ^ α := by
    have hpowOne : (1 : ℝ) ≤ (m : ℝ) ^ α :=
      Real.one_le_rpow (by exact_mod_cast hm) hα0
    have hceil := Nat.ceil_lt_add_one
      (Real.rpow_nonneg (show (0 : ℝ) ≤ m by positivity) α)
    dsimp [sourceNarrowWidth]
    linarith
  have hNcardCast : ((openTopBand m (sourceNarrowWidth m α)).card : ℝ) ≤
      2 * (m : ℝ) ^ α := by
    have hNcardNat : (openTopBand m (sourceNarrowWidth m α)).card ≤
        sourceNarrowWidth m α := by rw [hNcard]; omega
    have hNcardReal : ((openTopBand m (sourceNarrowWidth m α)).card : ℝ) ≤
        sourceNarrowWidth m α := by exact_mod_cast hNcardNat
    exact hNcardReal.trans hnCast
  have hxB : (m : ℝ) ^ kappaOne ≤
      2 * ((openTopBand m (sourceCellWidth m)).card : ℝ) := by
    have hxS : (m : ℝ) ^ kappaOne ≤ sourceCellWidth m := by
      unfold sourceCellWidth
      exact Nat.le_ceil _
    have hSB : (sourceCellWidth m : ℝ) ≤
        2 * ((openTopBand m (sourceCellWidth m)).card : ℝ) := by
      rw [hBcard]
      rw [Nat.cast_sub (by omega : 1 ≤ sourceCellWidth m)]
      push_cast
      have hsTwoR : (2 : ℝ) ≤ sourceCellWidth m := by exact_mod_cast hsTwo
      nlinarith
    exact hxS.trans hSB
  have hrpowMul : (m : ℝ) ^ (α - kappaOne) * (m : ℝ) ^ kappaOne =
      (m : ℝ) ^ α := by
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    rw [← Real.rpow_add hmpos]
    congr 1
    ring
  have hyBound : (m : ℝ) ^ α ≤
      2 * (m : ℝ) ^ (α - kappaOne) *
        ((openTopBand m (sourceCellWidth m)).card : ℝ) := by
    calc
      (m : ℝ) ^ α = (m : ℝ) ^ (α - kappaOne) * (m : ℝ) ^ kappaOne :=
        hrpowMul.symm
      _ ≤ (m : ℝ) ^ (α - kappaOne) *
          (2 * ((openTopBand m (sourceCellWidth m)).card : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hxB (Real.rpow_nonneg (by positivity) _)
      _ = 2 * (m : ℝ) ^ (α - kappaOne) *
          ((openTopBand m (sourceCellWidth m)).card : ℝ) := by ring
  have hbase := equation458_bandRatio_le_cardRatio c m i α hgrowth hiwin hα0 hα.le
  calc
    bandRatio (barNegBinMass i) (openTopBand m (sourceNarrowWidth m α))
        (openTopBand m (sourceCellWidth m)) ≤
      Real.exp (sourceComparisonExponent c) *
        (openTopBand m (sourceNarrowWidth m α)).card /
          (openTopBand m (sourceCellWidth m)).card := hbase
    _ ≤ 4 * Real.exp (sourceComparisonExponent c) * (m : ℝ) ^ (α - kappaOne) := by
      rw [div_le_iff₀ (by exact_mod_cast hBpos)]
      have hE : 0 ≤ Real.exp (sourceComparisonExponent c) := Real.exp_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left hNcardCast hE,
        mul_le_mul_of_nonneg_left hyBound (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hE)]

/-- Direct compatibility with the one-coordinate input expected by
`HLOZFiniteUnion.polynomialBandRatio`. -/
theorem equation458_bandRatio_le_polynomialBandRatio (c m i : ℕ) (α : ℝ)
    (hgrowth : SourceWindowGrowth c m) (hiwin : InEquation458ExternalWindow c m i)
    (hα0 : 0 ≤ α) (hα : α < kappaOne) :
    ENNReal.ofReal
        (bandRatio (barNegBinMass i) (openTopBand m (sourceNarrowWidth m α))
          (openTopBand m (sourceCellWidth m))) ≤
      HLOZFiniteUnion.polynomialBandRatio
        (4 * Real.exp (sourceComparisonExponent c)) kappaOne α m := by
  unfold HLOZFiniteUnion.polynomialBandRatio
  exact ENNReal.ofReal_le_ofReal
    (equation458_bandRatio_le_rpow c m i α hgrowth hiwin hα0 hα)

end Erdos1166.HLOZBandRatios
