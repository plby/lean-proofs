import ErdosProblems.Erdos67b.MRScheduledTailDensity
import ErdosProblems.Erdos67b.MRTypicalTailEnergy
import ErdosProblems.Erdos67b.MRRelativeEnergyBudget
import ErdosProblems.Erdos67b.MRFixedPowerTypicalEnergy

/-!
# Quantitative typical energy for one fixed finite family

The family is fixed before every later ambient scale, coefficient, and
frequency cutoff. All comparisons use the actual typical coefficient.
-/

open Filter MeasureTheory
open scoped Interval

namespace Erdos67b

noncomputable section

theorem mrExists_fixed_typical_energy_le_relativeBudget
    {eta p q c epsilon : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p) (hq : 1 ≤ q) (hpq : 2 * p ≤ q)
    (hlogq : 1 ≤ Real.log q) (hbudget : 4096 * Real.log q ≤ eta * p)
    (hmertens : Real.log 2 + 2 * PrimeEstimates.mertensBound ≤ Real.log q - Real.log p)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / 2) (hepsilon : 0 < epsilon) :
    ∃ K M₀ X₀ : ℕ, 0 < K ∧ 0 < M₀ ∧ 2 ≤ X₀ ∧
      ∀ {M X : ℕ}, M₀ ≤ M → X₀ ≤ X →
      ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRArchimedeanNonpretentious f M X →
      ∀ {T : ℝ}, 0 ≤ T → T ≤ c * X →
        (∫ t in -T..T, ‖mrTypicalDyadicPolynomial (mrScheduledBlocks p q K) f X t‖ ^ 2) ≤
          2 * mrFirstSmallRelativeBudget eta p q c + epsilon := by
  let delta : ℝ := epsilon / (4 * (1 + 4 * Real.pi))
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  obtain ⟨K, X₁, hK, _, hdensity⟩ :=
    mrExists_scheduled_tail_density_small heta1 hp hq hpq hlogq hbudget hdelta
  obtain ⟨M₀, X₂, hM₀, hX₂, henergy⟩ := mrExists_typical_energy_le_firstSmall_add_small
    heta0 heta1 hp hq hpq hlogq hbudget hmertens (by positivity : 0 < epsilon / 8)
  obtain ⟨X₃, hindex⟩ := eventually_atTop.1 (mrEventually_lastBlock_index_error
    (by positivity : 0 < epsilon / (1536 * (1 + Real.pi))))
  obtain ⟨X₄, hprefix⟩ := eventually_atTop.1
    (mrEventually_maximal_index_ge heta1 hp hq (by linarith) hlogq hbudget K)
  let X₀ := max X₂ (max X₁ (max X₃ X₄))
  refine ⟨K, M₀, X₀, hK, hM₀, hX₂.trans (le_max_left _ _), ?_⟩
  intro M X hM hX f hmul hbound hnonpret T hT hTX
  have hX₁ : X₁ ≤ X := by dsimp only [X₀] at hX; omega
  have hX₂' : X₂ ≤ X := by dsimp only [X₀] at hX; omega
  have hX₃ : X₃ ≤ X := by dsimp only [X₀] at hX; omega
  have hX₄ : X₄ ≤ X := by dsimp only [X₀] at hX; omega
  have hXpos : 0 < X := by omega
  have hXR : (0 : ℝ) < X := by exact_mod_cast hXpos
  have hTMain : T ≤ (X : ℝ) / 2 := by
    have hh := mul_le_mul_of_nonneg_right hc1 hXR.le
    linarith
  obtain ⟨J, hJ, hupper, hnext, hfull⟩ := henergy hM hX₂'
  have hKJ : K ≤ J := hprefix X hX₄ J hnext
  have hbad := hdensity (K := K) le_rfl hX₁ hJ hupper (2 * X) (by omega)
  have htailBase := intervalIntegral_mrTypicalTailPolynomial_le
    (mrScheduledBlocks p q K) (mrScheduledTailBlocks p q K J) hXpos hbound hT
  have htail : (∫ t in -T..T,
      ‖mrTypicalTailPolynomial (mrScheduledBlocks p q K)
        (mrScheduledTailBlocks p q K J) f X t‖ ^ 2) ≤ epsilon / 4 := by
    calc
      _ ≤ (2 * T + 4 * Real.pi * X) *
          (atypicalFactorizationSet (mrScheduledTailBlocks p q K J) (2 * X)).card /
            (X : ℝ) ^ 2 := htailBase
      _ ≤ ((1 + 4 * Real.pi) * X) * (delta * X) / (X : ℝ) ^ 2 := by
        gcongr
        linarith
      _ = (1 + 4 * Real.pi) * delta := by field_simp
      _ = epsilon / 4 := by dsimp only [delta]; field_simp
  have hindex' := (hindex X hX₃).2.2 hq hJ hupper
  have hindexCost : 192 * (1 + Real.pi) * (J : ℝ) / X ≤ epsilon / 8 := by
    have hh := mul_le_mul_of_nonneg_left hindex' (by positivity : 0 ≤ 192 * (1 + Real.pi))
    have heq : 192 * (1 + Real.pi) * (epsilon / (1536 * (1 + Real.pi))) = epsilon / 8 := by
      field_simp
      ring
    rw [heq] at hh
    simpa only [mul_div_assoc] using hh
  have hfirst := mrFirstSmallEnergyBudget_le_relativeBudget (eta := eta) (p := p) (q := q)
    hXpos J hc0 hc1 hT hTX
  have hfullEnergy := hfull hmul hbound hnonpret hT hTMain
  have hcompare := intervalIntegral_mrTypicalDyadicPolynomial_le_union_add_tail
    (mrScheduledBlocks p q K) (mrScheduledTailBlocks p q K J) f X hT
  rw [← mrScheduledBlocks_eq_union_tail p q hKJ] at hcompare
  linarith

end

end Erdos67b
