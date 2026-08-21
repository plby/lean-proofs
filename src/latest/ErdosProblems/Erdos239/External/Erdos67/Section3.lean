import ErdosProblems.Erdos239.External.Erdos67.Stochastic
import ErdosProblems.Erdos239.External.Erdos67.LogElliott
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Tao's Section 3: the elementary van der Corput layer

This file formalizes the elementary part of Section 3 of Tao's proof of the
Erdős discrepancy theorem.  It deliberately does not postulate the deep
logarithmically averaged Elliott theorem.  The final extraction theorem below
takes whatever pointwise correlation upper bound a future Elliott module
provides as an explicit hypothesis.
-/

open scoped BigOperators ENNReal NNReal BoundedContinuousFunction
open MeasureTheory Finset

namespace Erdos67

/-- Evaluation of a compact circle character on a natural number, with the
harmless value `0` at the unused input `0`. -/
noncomputable def compactCharacterNatValue
    (g : CompactCircleCharacter) (n : ℕ) : ℂ :=
  if hn : 0 < n then (g.1 (⟨n, hn⟩ : ℕ+) : ℂ) else 0

theorem compactCharacterNatValue_of_pos
    (g : CompactCircleCharacter) {n : ℕ} (hn : 0 < n) :
    compactCharacterNatValue g n = (g.1 (⟨n, hn⟩ : ℕ+) : ℂ) := by
  simp [compactCharacterNatValue, hn]

theorem continuous_compactCharacterNatValue (n : ℕ) :
    Continuous fun g : CompactCircleCharacter ↦ compactCharacterNatValue g n := by
  by_cases hn : 0 < n
  · simpa [compactCharacterNatValue, hn] using
      continuous_compactCircleCharacter_eval_complex (⟨n, hn⟩ : ℕ+)
  · simpa [compactCharacterNatValue, hn] using
      (continuous_const : Continuous fun _ : CompactCircleCharacter ↦ (0 : ℂ))

/-- The sum on the translated interval `n+1, ..., n+H`. -/
noncomputable def compactCharacterIntervalSum
    (n H : ℕ) (g : CompactCircleCharacter) : ℂ :=
  ∑ h ∈ range H, compactCharacterNatValue g (n + h + 1)

theorem continuous_compactCharacterIntervalSum (n H : ℕ) :
    Continuous fun g : CompactCircleCharacter ↦ compactCharacterIntervalSum n H g := by
  unfold compactCharacterIntervalSum
  exact continuous_finsetSum (range H) fun h _ ↦
    continuous_compactCharacterNatValue (n + h + 1)

/-- A translated interval sum is the difference of two initial partial sums. -/
theorem compactCharacterIntervalSum_eq_sub (n H : ℕ) (g : CompactCircleCharacter) :
    compactCharacterIntervalSum n H g =
      compactCharacterPartialSum 1 (n + H) g - compactCharacterPartialSum 1 n g := by
  unfold compactCharacterIntervalSum compactCharacterPartialSum
  rw [Finset.sum_range_add]
  simp only [add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro h hh
  rw [compactCharacterNatValue_of_pos g (by omega)]
  exact congrArg (fun x : ℕ+ ↦ (g.1 x : ℂ)) (mul_one _).symm

/-- Squared norm of a translated interval sum. -/
noncomputable def compactCharacterIntervalEnergy
    (n H : ℕ) (g : CompactCircleCharacter) : ℝ :=
  ‖compactCharacterIntervalSum n H g‖ ^ 2

theorem continuous_compactCharacterIntervalEnergy (n H : ℕ) :
    Continuous (compactCharacterIntervalEnergy n H) := by
  exact (continuous_compactCharacterIntervalSum n H).norm.pow 2

theorem compactCharacterIntervalEnergy_nonneg (n H : ℕ) (g : CompactCircleCharacter) :
    0 ≤ compactCharacterIntervalEnergy n H g := sq_nonneg _

theorem integrable_compactCharacterIntervalEnergy
    (μ : ProbabilityMeasure CompactCircleCharacter) (n H : ℕ) :
    Integrable (compactCharacterIntervalEnergy n H)
      (μ : Measure CompactCircleCharacter) := by
  let F : C(CompactCircleCharacter, ℝ) :=
    ⟨compactCharacterIntervalEnergy n H,
      continuous_compactCharacterIntervalEnergy n H⟩
  let F' : CompactCircleCharacter →ᵇ ℝ :=
    ContinuousMap.equivBoundedOfCompact CompactCircleCharacter ℝ F
  have hF : (F' : CompactCircleCharacter → ℝ) =
      compactCharacterIntervalEnergy n H := by
    funext g
    rfl
  rw [← hF]
  exact F'.integrable (μ : Measure CompactCircleCharacter)

theorem integrable_compactCharacterPartialSumSq
    (μ : ProbabilityMeasure CompactCircleCharacter) (d : ℕ+) (m : ℕ) :
    Integrable (compactCharacterPartialSumSq d m)
      (μ : Measure CompactCircleCharacter) := by
  let F : C(CompactCircleCharacter, ℝ) :=
    ⟨compactCharacterPartialSumSq d m,
      continuous_compactCharacterPartialSumSq d m⟩
  let F' : CompactCircleCharacter →ᵇ ℝ :=
    ContinuousMap.equivBoundedOfCompact CompactCircleCharacter ℝ F
  have hF : (F' : CompactCircleCharacter → ℝ) =
      compactCharacterPartialSumSq d m := by
    funext g
    rfl
  rw [← hF]
  exact F'.integrable (μ : Measure CompactCircleCharacter)

/-- The elementary pointwise quadratic triangle inequality used on partial
sums before integration. -/
theorem norm_sub_sq_le_two {E : Type*} [SeminormedAddCommGroup E] (x y : E) :
    ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  calc
    ‖x - y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := by
      gcongr
      exact norm_sub_le x y
    _ ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
      nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

theorem compactCharacterIntervalEnergy_le (n H : ℕ) (g : CompactCircleCharacter) :
    compactCharacterIntervalEnergy n H g ≤
      2 * compactCharacterPartialSumSq 1 (n + H) g +
        2 * compactCharacterPartialSumSq 1 n g := by
  rw [compactCharacterIntervalEnergy, compactCharacterIntervalSum_eq_sub,
    compactCharacterPartialSumSq]
  exact norm_sub_sq_le_two _ _

/-- Uniformly bounded expected initial partial sums give the `4 C²` bound
for every translated interval. -/
theorem meanSquareIntervalSum_le_four
    (μ : ProbabilityMeasure CompactCircleCharacter) (C : ℝ)
    (hbound : ∀ m : ℕ, compactMeanSquarePartialSum μ m ≤ C ^ 2)
    (n H : ℕ) :
    ∫ g, compactCharacterIntervalEnergy n H g
      ∂(μ : Measure CompactCircleCharacter) ≤ 4 * C ^ 2 := by
  have hInt := integrable_compactCharacterIntervalEnergy μ n H
  have hIntAdd : Integrable
      (fun g : CompactCircleCharacter ↦
        2 * compactCharacterPartialSumSq 1 (n + H) g +
          2 * compactCharacterPartialSumSq 1 n g)
      (μ : Measure CompactCircleCharacter) :=
    ((integrable_compactCharacterPartialSumSq μ 1 (n + H)).const_mul 2).add
      ((integrable_compactCharacterPartialSumSq μ 1 n).const_mul 2)
  calc
    (∫ g, compactCharacterIntervalEnergy n H g
        ∂(μ : Measure CompactCircleCharacter)) ≤
        ∫ g, (2 * compactCharacterPartialSumSq 1 (n + H) g +
          2 * compactCharacterPartialSumSq 1 n g)
          ∂(μ : Measure CompactCircleCharacter) :=
      integral_mono hInt hIntAdd (fun g ↦
        compactCharacterIntervalEnergy_le n H g)
    _ = 2 * compactMeanSquarePartialSum μ (n + H) +
          2 * compactMeanSquarePartialSum μ n := by
      rw [integral_add
        ((integrable_compactCharacterPartialSumSq μ 1 (n + H)).const_mul 2)
        ((integrable_compactCharacterPartialSumSq μ 1 n).const_mul 2),
        integral_const_mul, integral_const_mul]
      rfl
    _ ≤ 4 * C ^ 2 := by
      linarith [hbound (n + H), hbound n]

/-- Pointwise square expansion for one translated interval. -/
theorem compactCharacterIntervalEnergy_coe_eq_double_sum
    (n H : ℕ) (g : CompactCircleCharacter) :
    (compactCharacterIntervalEnergy n H g : ℂ) =
      ∑ a ∈ range H, ∑ b ∈ range H,
        compactCharacterNatValue g (n + a + 1) *
          (starRingEnd ℂ) (compactCharacterNatValue g (n + b + 1)) := by
  unfold compactCharacterIntervalEnergy compactCharacterIntervalSum
  calc
    ((‖∑ h ∈ range H, compactCharacterNatValue g (n + h + 1)‖ ^ 2 : ℝ) : ℂ) =
        (∑ h ∈ range H, compactCharacterNatValue g (n + h + 1)) *
          (starRingEnd ℂ) (∑ h ∈ range H,
            compactCharacterNatValue g (n + h + 1)) :=
      by simpa only [Complex.ofReal_pow] using (Complex.mul_conj' _).symm
    _ = _ := by
      simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]

/-- The complex correlation of shifts `a` and `b` over a finite set, with
arbitrary real weights. -/
noncomputable def compactCharacterCorrelation
    (s : Finset ℕ) (weight : ℕ → ℝ) (a b : ℕ)
    (g : CompactCircleCharacter) : ℂ :=
  ∑ n ∈ s, (weight n : ℂ) *
    compactCharacterNatValue g (n + a + 1) *
      (starRingEnd ℂ) (compactCharacterNatValue g (n + b + 1))

/-- Weighted energy of all length-`H` translated sums. -/
noncomputable def compactCharacterWeightedEnergy
    (s : Finset ℕ) (weight : ℕ → ℝ) (H : ℕ)
    (g : CompactCircleCharacter) : ℝ :=
  ∑ n ∈ s, weight n * compactCharacterIntervalEnergy n H g

theorem integrable_compactCharacterWeightedEnergy
    (μ : ProbabilityMeasure CompactCircleCharacter)
    (s : Finset ℕ) (weight : ℕ → ℝ) (H : ℕ) :
    Integrable (compactCharacterWeightedEnergy s weight H)
      (μ : Measure CompactCircleCharacter) := by
  unfold compactCharacterWeightedEnergy
  exact integrable_finsetSum s fun n _ ↦
    (integrable_compactCharacterIntervalEnergy μ n H).const_mul (weight n)

theorem continuous_compactCharacterWeightedEnergy
    (s : Finset ℕ) (weight : ℕ → ℝ) (H : ℕ) :
    Continuous (compactCharacterWeightedEnergy s weight H) := by
  unfold compactCharacterWeightedEnergy
  exact continuous_finsetSum s fun n _ ↦
    continuous_const.mul (continuous_compactCharacterIntervalEnergy n H)

/-- Finite weighted Fubini: the expected translated energy is at most
`4 C²` times the total nonnegative weight. -/
theorem integral_compactCharacterWeightedEnergy_le
    (μ : ProbabilityMeasure CompactCircleCharacter) (C : ℝ)
    (hbound : ∀ m : ℕ, compactMeanSquarePartialSum μ m ≤ C ^ 2)
    (s : Finset ℕ) (weight : ℕ → ℝ) (H : ℕ)
    (hweight : ∀ n ∈ s, 0 ≤ weight n) :
    ∫ g, compactCharacterWeightedEnergy s weight H g
      ∂(μ : Measure CompactCircleCharacter) ≤
        4 * C ^ 2 * ∑ n ∈ s, weight n := by
  unfold compactCharacterWeightedEnergy
  rw [integral_finsetSum s fun n _ ↦
    (integrable_compactCharacterIntervalEnergy μ n H).const_mul (weight n)]
  simp only [integral_const_mul]
  calc
    (∑ n ∈ s, weight n *
        ∫ g, compactCharacterIntervalEnergy n H g
          ∂(μ : Measure CompactCircleCharacter)) ≤
        ∑ n ∈ s, weight n * (4 * C ^ 2) := by
      exact Finset.sum_le_sum fun n hn ↦
        mul_le_mul_of_nonneg_left
          (meanSquareIntervalSum_le_four μ C hbound n H) (hweight n hn)
    _ = 4 * C ^ 2 * ∑ n ∈ s, weight n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring

/-- Markov's inequality for the weighted interval energy. -/
theorem measure_compactCharacterWeightedEnergy_ge_le
    (μ : ProbabilityMeasure CompactCircleCharacter) (C B W : ℝ)
    (hB : 0 < B) (hW : 0 < W)
    (hbound : ∀ m : ℕ, compactMeanSquarePartialSum μ m ≤ C ^ 2)
    (s : Finset ℕ) (weight : ℕ → ℝ) (H : ℕ)
    (hweight : ∀ n ∈ s, 0 ≤ weight n)
    (hweightSum : ∑ n ∈ s, weight n = W) :
    (μ : Measure CompactCircleCharacter)
        {g | B * W ≤ compactCharacterWeightedEnergy s weight H g} ≤
      ENNReal.ofReal (4 * C ^ 2 / B) := by
  have hBW : 0 < B * W := mul_pos hB hW
  have hInt := integrable_compactCharacterWeightedEnergy μ s weight H
  have hScaled := (hInt.div_const (B * W)).measure_le_integral
    (f_nonneg := ae_of_all _ fun g ↦ div_nonneg
      (Finset.sum_nonneg fun n hn ↦ mul_nonneg (hweight n hn)
        (compactCharacterIntervalEnergy_nonneg n H g)) hBW.le)
    (s := {g | B * W ≤ compactCharacterWeightedEnergy s weight H g})
    (hs := fun g hg ↦ by
      rw [le_div_iff₀ hBW, one_mul]
      exact hg)
  refine hScaled.trans ?_
  apply ENNReal.ofReal_le_ofReal
  rw [integral_div]
  have hMean := integral_compactCharacterWeightedEnergy_le
    μ C hbound s weight H hweight
  rw [hweightSum] at hMean
  have hBWnonneg : 0 ≤ B * W := hBW.le
  calc
    (∫ g, compactCharacterWeightedEnergy s weight H g
        ∂(μ : Measure CompactCircleCharacter)) / (B * W) ≤
        (4 * C ^ 2 * W) / (B * W) :=
      div_le_div_of_nonneg_right hMean hBWnonneg
    _ = 4 * C ^ 2 / B := by field_simp

/-- Expansion of a complex square into its shift correlations. -/
theorem compactCharacterWeightedEnergy_eq_correlation_sum
    (s : Finset ℕ) (weight : ℕ → ℝ) (H : ℕ)
    (g : CompactCircleCharacter) :
    (compactCharacterWeightedEnergy s weight H g : ℂ) =
      ∑ a ∈ range H, ∑ b ∈ range H,
        compactCharacterCorrelation s weight a b g := by
  unfold compactCharacterWeightedEnergy compactCharacterCorrelation
  rw [Complex.ofReal_sum]
  simp only [Complex.ofReal_mul]
  calc
    (∑ n ∈ s, (weight n : ℂ) *
        (compactCharacterIntervalEnergy n H g : ℂ)) =
        ∑ n ∈ s, ∑ a ∈ range H, ∑ b ∈ range H,
          (weight n : ℂ) *
            (compactCharacterNatValue g (n + a + 1) *
              (starRingEnd ℂ) (compactCharacterNatValue g (n + b + 1))) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [compactCharacterIntervalEnergy_coe_eq_double_sum]
      simp only [Finset.mul_sum]
    _ = ∑ a ∈ range H, ∑ b ∈ range H, ∑ n ∈ s,
        (weight n : ℂ) * compactCharacterNatValue g (n + a + 1) *
          (starRingEnd ℂ) (compactCharacterNatValue g (n + b + 1)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = _ := rfl

/-- Every diagonal correlation is exactly the total weight, since the
character values lie on the unit circle. -/
theorem compactCharacterCorrelation_self
    (s : Finset ℕ) (weight : ℕ → ℝ) (a : ℕ)
    (g : CompactCircleCharacter) :
    compactCharacterCorrelation s weight a a g =
      (∑ n ∈ s, weight n : ℝ) := by
  unfold compactCharacterCorrelation
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [compactCharacterNatValue_of_pos g (by omega)]
  rw [mul_assoc, Complex.mul_conj]
  simp

/-- Replace the diagonal of a square matrix by zero. -/
def eraseDiagonal {ι : Type*} [DecidableEq ι]
    (A : ι → ι → ℂ) (p : ι × ι) : ℂ :=
  if p.1 = p.2 then 0 else A p.1 p.2

/-- Summing a matrix with its diagonal erased subtracts exactly the diagonal
sum from the full double sum. -/
theorem sum_eraseDiagonal_eq
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (A : ι → ι → ℂ) (w : ℂ)
    (hdiag : ∀ i ∈ s, A i i = w) :
    ∑ p ∈ s ×ˢ s, eraseDiagonal A p =
      (∑ i ∈ s, ∑ j ∈ s, A i j) - (s.card : ℂ) * w := by
  rw [Finset.sum_product]
  have hsplit : ∀ i ∈ s,
      (∑ j ∈ s, A i j) = w + ∑ j ∈ s, eraseDiagonal A (i, j) := by
    intro i hi
    rw [← hdiag i hi]
    nth_rewrite 1 [← Finset.add_sum_erase s (fun j ↦ A i j) hi]
    congr 1
    calc
      (∑ j ∈ s.erase i, A i j) =
          ∑ j ∈ s.erase i, eraseDiagonal A (i, j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hji : j ≠ i := by
          exact (Finset.mem_erase.mp hj).1
        simp [eraseDiagonal, hji.symm]
      _ = ∑ j ∈ s, eraseDiagonal A (i, j) := by
        exact Finset.sum_erase s (by simp [eraseDiagonal])
  have h := Finset.sum_congr rfl hsplit
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h
  rw [h]
  ring

/-- If the norm of a finite sum is at least `D`, one summand has norm at
least `δ` whenever `card * δ ≤ D`. -/
theorem exists_norm_ge_of_norm_sum_ge
    {ι : Type*} (s : Finset ι) (f : ι → ℂ) (D δ : ℝ)
    (hs : s.Nonempty)
    (hcard : (s.card : ℝ) * δ ≤ D)
    (hsum : D ≤ ‖∑ i ∈ s, f i‖) :
    ∃ i ∈ s, δ ≤ ‖f i‖ := by
  by_contra h
  push Not at h
  have hlt : ∑ i ∈ s, ‖f i‖ < ∑ _i ∈ s, δ :=
    Finset.sum_lt_sum_of_nonempty hs h
  have htri : ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le _ _
  have hconst : ∑ _i ∈ s, δ = (s.card : ℝ) * δ := by simp
  linarith

/-- Deterministic van der Corput extraction.  A small total energy compared
with the diagonal forces one large off-diagonal correlation. -/
theorem exists_large_offDiagonal
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ι → ℂ) (energy B W δ : ℝ)
    (hs : s.Nonempty) (hW : 0 < W)
    (hdiag : ∀ i ∈ s, A i i = (W : ℂ))
    (hexpand : (energy : ℂ) = ∑ i ∈ s, ∑ j ∈ s, A i j)
    (henergy : energy ≤ B * W)
    (hB : B < s.card)
    (hδ : (s.card : ℝ) ^ 2 * δ ≤ ((s.card : ℝ) - B) * W)
    (hδpos : 0 < δ) :
    ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ δ ≤ ‖A i j‖ := by
  let off : ι × ι → ℂ := eraseDiagonal A
  have hoff : ∑ p ∈ s ×ˢ s, off p =
      (energy : ℂ) - ((s.card : ℝ) * W : ℝ) := by
    rw [sum_eraseDiagonal_eq s A (W : ℂ) hdiag, ← hexpand]
    norm_cast
  have hgap : ((s.card : ℝ) - B) * W ≤
      ‖∑ p ∈ s ×ˢ s, off p‖ := by
    rw [hoff, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos]
    · linarith
    · have hBcast : B ≤ (s.card : ℝ) := by exact_mod_cast hB.le
      exact sub_nonpos.mpr
        (henergy.trans (mul_le_mul_of_nonneg_right hBcast hW.le))
  have hprod : (s ×ˢ s).Nonempty := hs.product hs
  have hcardProd : (((s ×ˢ s).card : ℕ) : ℝ) * δ ≤
      ((s.card : ℝ) - B) * W := by
    rw [Finset.card_product, Nat.cast_mul]
    simpa [pow_two] using hδ
  obtain ⟨p, hp, hpδ⟩ := exists_norm_ge_of_norm_sum_ge
    (s ×ˢ s) off (((s.card : ℝ) - B) * W) δ
    hprod hcardProd hgap
  have hpne : p.1 ≠ p.2 := by
    intro heq
    have : off p = 0 := by simp [off, eraseDiagonal, heq]
    rw [this, norm_zero] at hpδ
    linarith
  refine ⟨p.1, (Finset.mem_product.mp hp).1, p.2,
    (Finset.mem_product.mp hp).2, hpne, ?_⟩
  simpa [off, eraseDiagonal, hpne] using hpδ

/-- Specialization of `exists_large_offDiagonal` to the finite correlations
arising from a compact circle character. -/
theorem exists_large_compactCharacterCorrelation
    (s : Finset ℕ) (weight : ℕ → ℝ) (H : ℕ)
    (g : CompactCircleCharacter) (energy B W : ℝ)
    (hH : 0 < H) (hW : 0 < W)
    (hweightSum : ∑ n ∈ s, weight n = W)
    (henergyEq : compactCharacterWeightedEnergy s weight H g = energy)
    (henergy : energy ≤ B * W) (hB : B < H) :
    ∃ a < H, ∃ b < H, a ≠ b ∧
      ((H : ℝ) - B) * W / (H : ℝ) ^ 2 ≤
        ‖compactCharacterCorrelation s weight a b g‖ := by
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  let δ : ℝ := ((H : ℝ) - B) * W / (H : ℝ) ^ 2
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ : ((range H).card : ℝ) ^ 2 * δ ≤
      (((range H).card : ℝ) - B) * W := by
    simp only [Finset.card_range, δ]
    field_simp
    rfl
  have hexpand : (energy : ℂ) =
      ∑ a ∈ range H, ∑ b ∈ range H,
        compactCharacterCorrelation s weight a b g := by
    rw [← compactCharacterWeightedEnergy_eq_correlation_sum s weight H g,
      henergyEq]
  obtain ⟨a, ha, b, hb, hab, hcorr⟩ := exists_large_offDiagonal
    (range H) (fun a b ↦ compactCharacterCorrelation s weight a b g)
    energy B W δ ⟨0, Finset.mem_range.mpr hH⟩ hW
    (fun a ha ↦ by
      rw [compactCharacterCorrelation_self, hweightSum])
    hexpand henergy (by simpa using hB) hδ hδpos
  exact ⟨a, Finset.mem_range.mp ha, b, Finset.mem_range.mp hb, hab, hcorr⟩

/-- The geometric window `2^K < n ≤ 4^K` used to avoid square-root
rounding in the logarithmic Elliott input. -/
def dyadicCorrelationWindow (K : ℕ) : Finset ℕ :=
  Finset.Ioc (2 ^ K) (4 ^ K)

/-- Reciprocal weight on the geometric window. -/
noncomputable def dyadicCorrelationWeight (K : ℕ) : ℝ :=
  ∑ n ∈ dyadicCorrelationWindow K, (n : ℝ)⁻¹

theorem dyadicCorrelationWindow_weight_nonneg (K : ℕ) {n : ℕ}
    (_hn : n ∈ dyadicCorrelationWindow K) :
    0 ≤ (n : ℝ)⁻¹ := by positivity

/-- Every dyadic block `(a,2a]` has reciprocal mass at least `1/2`. -/
theorem half_le_sum_Ioc_inv_double (a : ℕ) (ha : 0 < a) :
    (1 / 2 : ℝ) ≤ ∑ n ∈ Finset.Ioc a (2 * a), (n : ℝ)⁻¹ := by
  have hcard : (Finset.Ioc a (2 * a)).card = a := by
    simp
    omega
  calc
    (1 / 2 : ℝ) = ∑ _n ∈ Finset.Ioc a (2 * a), ((2 * a : ℕ) : ℝ)⁻¹ := by
      rw [Finset.sum_const, hcard, nsmul_eq_mul]
      push_cast
      field_simp
    _ ≤ ∑ n ∈ Finset.Ioc a (2 * a), (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      apply inv_anti₀ (by
        exact_mod_cast ha.trans (Finset.mem_Ioc.mp hn).1)
      exact_mod_cast (Finset.mem_Ioc.mp hn).2

/-- `K` consecutive dyadic blocks have reciprocal mass at least `K/2`. -/
theorem half_mul_le_sum_Ioc_inv_pow_two (a K : ℕ) (ha : 0 < a) :
    (K : ℝ) / 2 ≤
      ∑ n ∈ Finset.Ioc a (a * 2 ^ K), (n : ℝ)⁻¹ := by
  induction K with
  | zero => simp
  | succ K ih =>
      let m := a * 2 ^ K
      have hm : 0 < m := mul_pos ha (pow_pos (by omega) _)
      have ham : a ≤ m := by
        dsimp [m]
        exact Nat.le_mul_of_pos_right a (pow_pos (by omega) _)
      have hmend : m ≤ a * 2 ^ (K + 1) := by
        dsimp [m]
        exact Nat.mul_le_mul_left a
          (Nat.pow_le_pow_right (by omega) (Nat.le_succ K))
      have hend : 2 * m = a * 2 ^ (K + 1) := by
        dsimp [m]
        rw [pow_succ]
        ring
      calc
        ((K + 1 : ℕ) : ℝ) / 2 = (K : ℝ) / 2 + 1 / 2 := by
          push_cast
          ring
        _ ≤ (∑ n ∈ Finset.Ioc a m, (n : ℝ)⁻¹) +
              ∑ n ∈ Finset.Ioc m (2 * m), (n : ℝ)⁻¹ :=
          add_le_add ih (half_le_sum_Ioc_inv_double m hm)
        _ = ∑ n ∈ Finset.Ioc a (a * 2 ^ (K + 1)), (n : ℝ)⁻¹ := by
          rw [hend]
          exact Finset.sum_Ioc_consecutive (fun n : ℕ ↦ (n : ℝ)⁻¹) ham hmend

/-- The reciprocal mass of `2^K < n ≤ 4^K` is at least `K/2`. -/
theorem half_mul_le_dyadicCorrelationWeight (K : ℕ) :
    (K : ℝ) / 2 ≤ dyadicCorrelationWeight K := by
  have h := half_mul_le_sum_Ioc_inv_pow_two (2 ^ K) K (pow_pos (by omega) _)
  have hpows : 2 ^ K * 2 ^ K = 4 ^ K := by
    rw [← mul_pow]
    norm_num
  simpa only [dyadicCorrelationWeight, dyadicCorrelationWindow, hpows] using h

theorem dyadicCorrelationWeight_pos {K : ℕ} (hK : 0 < K) :
    0 < dyadicCorrelationWeight K := by
  have hmem : 2 ^ K + 1 ∈ dyadicCorrelationWindow K := by
    simp only [dyadicCorrelationWindow, Finset.mem_Ioc]
    constructor
    · omega
    · have hpow : 2 ^ K < 4 ^ K :=
        Nat.pow_lt_pow_left (by omega) hK.ne'
      omega
  have hterm : 0 < (((2 ^ K + 1 : ℕ) : ℝ)⁻¹) := by positivity
  exact hterm.trans_le (Finset.single_le_sum
    (fun n hn ↦ dyadicCorrelationWindow_weight_nonneg K hn) hmem)

/-! ## The logarithmic Elliott interface -/

/-- The natural-valued realization of a compact circle character is completely
multiplicative on positive inputs. -/
theorem compactCharacterNatValue_isCompletelyMultiplicative
    (g : CompactCircleCharacter) :
    IsCompletelyMultiplicativeOnPositive (compactCharacterNatValue g) := by
  constructor
  · rw [compactCharacterNatValue_of_pos g (by omega)]
    change ((g.1 1 : Circle) : ℂ) = 1
    rw [g.2.1]
    rfl
  · intro m n hm hn
    rw [compactCharacterNatValue_of_pos g (Nat.mul_pos hm hn),
      compactCharacterNatValue_of_pos g hm,
      compactCharacterNatValue_of_pos g hn]
    let mp : ℕ+ := ⟨m, hm⟩
    let np : ℕ+ := ⟨n, hn⟩
    have hprod : (⟨m * n, Nat.mul_pos hm hn⟩ : ℕ+) = mp * np := by
      apply Subtype.ext
      rfl
    have hcircle :
        g.1 (⟨m * n, Nat.mul_pos hm hn⟩ : ℕ+) = g.1 mp * g.1 np := by
      rw [hprod, g.2.2]
    exact congrArg (fun z : Circle ↦ (z : ℂ)) hcircle

theorem norm_compactCharacterNatValue (g : CompactCircleCharacter)
    {n : ℕ} (hn : 0 < n) :
    ‖compactCharacterNatValue g n‖ = 1 := by
  rw [compactCharacterNatValue_of_pos g hn]
  exact Circle.norm_coe _

/-- The geometric window used above is exactly an Elliott logarithmic window
with `X = 4^K` and `W = 2^K`. -/
theorem elliottLogWindow_four_two (K : ℕ) :
    elliottLogWindow (4 ^ K) (2 ^ K) = dyadicCorrelationWindow K := by
  rw [elliottLogWindow_eq_Ioc (pow_pos (by omega) K)]
  unfold dyadicCorrelationWindow
  have hp : 4 ^ K = 2 ^ K * 2 ^ K := by
    rw [← mul_pow]
    norm_num
  rw [hp]
  simp

/-- The correlations extracted from the energy expansion are literally the
affine two-point correlations appearing in the general logarithmic Elliott
theorem. -/
theorem compactCharacterCorrelation_eq_elliottLogCorrelation
    (K a b : ℕ) (g : CompactCircleCharacter) :
    compactCharacterCorrelation (dyadicCorrelationWindow K)
        (fun n ↦ (n : ℝ)⁻¹) a b g =
      elliottLogCorrelation
        (positiveIntExtension (compactCharacterNatValue g))
        (positiveIntExtension
          (fun n ↦ (starRingEnd ℂ) (compactCharacterNatValue g n)))
        1 1 ((a : ℤ) + 1) ((b : ℤ) + 1) (4 ^ K) (2 ^ K) := by
  unfold compactCharacterCorrelation elliottLogCorrelation harmonicWeight
  rw [elliottLogWindow_four_two]
  apply Finset.sum_congr rfl
  intro n hn
  have hna : 0 < n + (a + 1) := by omega
  have hnb : 0 < n + (b + 1) := by omega
  have haff : integerAffine 1 ((a : ℤ) + 1) n =
      ((n + (a + 1) : ℕ) : ℤ) := by
    unfold integerAffine
    push_cast
    ring
  have hbff : integerAffine 1 ((b : ℤ) + 1) n =
      ((n + (b + 1) : ℕ) : ℤ) := by
    unfold integerAffine
    push_cast
    ring
  rw [haff, hbff, positiveIntExtension_natCast hna,
    positiveIntExtension_natCast hnb]
  simp only [Nat.add_assoc]

/-- A bounded-period, bounded-frequency pretentious approximation at the
finite scale `X`.  This is kept as a plain existential proposition: no
measurable selection of `q`, `χ`, or `t` is needed. -/
def HasBoundedPretentiousApproximation
    (A X : ℕ) (g : CompactCircleCharacter) : Prop :=
  ∃ q : ℕ, 0 < q ∧ q ≤ A ∧
    ∃ χ : DirichletCharacter ℂ q, ∃ t : ℝ,
      |t| ≤ (A : ℝ) * X ∧
        pretentiousDistSqToTwist (compactCharacterNatValue g) χ t X < A

/-- The general affine logarithmic Elliott theorem bounds exactly one of the
off-diagonal correlations from the energy expansion, provided no bounded
pretentious approximation exists. -/
theorem NonasymptoticLogElliott.compactCharacterCorrelation
    (helliott : NonasymptoticLogElliott)
    (a b : ℕ) (hab : a ≠ b) (η : ℝ) (hη : 0 < η) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧
      ∀ A K : ℕ, A₀ ≤ A → A ≤ 2 ^ K →
        ∀ g : CompactCircleCharacter,
          ¬ HasBoundedPretentiousApproximation A (4 ^ K) g →
          ‖compactCharacterCorrelation (dyadicCorrelationWindow K)
              (fun n ↦ (n : ℝ)⁻¹) a b g‖ ≤
            η * Real.log ((2 ^ K : ℕ) : ℝ) := by
  have hdet :
      ((1 : ℕ) : ℤ) * ((b : ℤ) + 1) -
          ((1 : ℕ) : ℤ) * ((a : ℤ) + 1) ≠ 0 := by
    intro hzero
    apply hab
    omega
  obtain ⟨A₀, hA₀, hmain⟩ :=
    helliott 1 1 ((a : ℤ) + 1) ((b : ℤ) + 1)
      (by omega) (by omega) hdet η hη
  refine ⟨A₀, hA₀, ?_⟩
  intro A K hA hAK g hno
  let f : ℕ → ℂ := compactCharacterNatValue g
  have hfMult : IsCompletelyMultiplicativeOnPositive f :=
    compactCharacterNatValue_isCompletelyMultiplicative g
  have hfUnit : ∀ n : ℕ, 0 < n → ‖f n‖ = 1 :=
    fun n hn ↦ norm_compactCharacterNatValue g hn
  have hconjMult :
      IsCompletelyMultiplicativeOnPositive (fun n ↦ (starRingEnd ℂ) (f n)) :=
    conj_isCompletelyMultiplicativeOnPositive hfMult
  have hpret :
      ∀ q : ℕ, 0 < q → q ≤ A →
        ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
          |t| ≤ (A : ℝ) * ((4 ^ K : ℕ) : ℝ) →
            (A : ℝ) ≤
              pretentiousDistSqToTwist
                (restrictToNat (positiveIntExtension f)) χ t (4 ^ K) := by
    intro q hq hqA χ t ht
    rw [pretentiousDistSqToTwist_positiveIntExtension]
    by_contra hdist
    apply hno
    exact ⟨q, hq, hqA, χ, t, ht, lt_of_not_ge hdist⟩
  have hWX : 2 ^ K ≤ 4 ^ K := by
    exact Nat.pow_le_pow_left (by omega) K
  have hresult := hmain A (4 ^ K) (2 ^ K) hA hAK hWX
    (positiveIntExtension f)
    (positiveIntExtension fun n ↦ (starRingEnd ℂ) (f n))
    (positiveIntExtension_isMultiplicative hfMult)
    (positiveIntExtension_isMultiplicative hconjMult)
    (norm_positiveIntExtension_le_one fun n hn ↦ (hfUnit n hn).le)
    (norm_positiveIntExtension_le_one fun n hn ↦ by
      rw [Complex.norm_conj, hfUnit n hn])
    hpret
  dsimp [f] at hresult
  rw [← compactCharacterCorrelation_eq_elliottLogCorrelation] at hresult
  exact hresult

/-- A finite family of eventual natural-number bounds has one common bound. -/
theorem exists_uniform_nat_bound
    {ι : Type*} [Fintype ι] (P : ι → ℕ → Prop)
    (hP : ∀ i, ∃ N : ℕ, 2 ≤ N ∧ ∀ A : ℕ, N ≤ A → P i A) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ A : ℕ, N ≤ A → ∀ i, P i A := by
  classical
  choose N hN hmain using hP
  let N₀ := max 2 (∑ i, N i)
  refine ⟨N₀, le_max_left _ _, ?_⟩
  intro A hA i
  apply hmain i A
  have hi : N i ≤ ∑ j, N j := by
    exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  exact hi.trans ((le_max_right 2 _).trans hA)

/-- For finitely many shifts, the Elliott threshold can be chosen uniformly.
This is the precise finite-uniformity step hidden by the phrase "choose `A`
large enough for every pair of shifts". -/
theorem NonasymptoticLogElliott.uniform_compactCharacterCorrelation
    (helliott : NonasymptoticLogElliott)
    (H : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧
      ∀ A K : ℕ, A₀ ≤ A → A ≤ 2 ^ K →
        ∀ a < H, ∀ b < H, a ≠ b →
          ∀ g : CompactCircleCharacter,
            ¬ HasBoundedPretentiousApproximation A (4 ^ K) g →
            ‖Erdos67.compactCharacterCorrelation (dyadicCorrelationWindow K)
                (fun n ↦ (n : ℝ)⁻¹) a b g‖ ≤
              η * Real.log ((2 ^ K : ℕ) : ℝ) := by
  classical
  let P : Fin H × Fin H → ℕ → Prop := fun p A ↦
    p.1.val ≠ p.2.val →
      ∀ K : ℕ, A ≤ 2 ^ K →
        ∀ g : CompactCircleCharacter,
          ¬ HasBoundedPretentiousApproximation A (4 ^ K) g →
          ‖Erdos67.compactCharacterCorrelation (dyadicCorrelationWindow K)
              (fun n ↦ (n : ℝ)⁻¹) p.1.val p.2.val g‖ ≤
            η * Real.log ((2 ^ K : ℕ) : ℝ)
  have hP : ∀ p : Fin H × Fin H,
      ∃ N : ℕ, 2 ≤ N ∧ ∀ A : ℕ, N ≤ A → P p A := by
    intro p
    by_cases hp : p.1.val = p.2.val
    · refine ⟨2, le_rfl, ?_⟩
      intro _A _hA hne
      exact (hne hp).elim
    · obtain ⟨N, hN, hmain⟩ :=
        helliott.compactCharacterCorrelation p.1.val p.2.val hp η hη
      refine ⟨N, hN, ?_⟩
      intro A hA hne K hAK g hno
      exact hmain A K hA hAK g hno
  obtain ⟨A₀, hA₀, huniform⟩ :=
    exists_uniform_nat_bound P hP
  refine ⟨A₀, hA₀, ?_⟩
  intro A K hA hAK a ha b hb hab g hno
  let ai : Fin H := ⟨a, ha⟩
  let bi : Fin H := ⟨b, hb⟩
  exact huniform A hA (ai, bi) hab K hAK g hno

/-- The deterministic off-diagonal extraction on Tao's geometric window. -/
theorem exists_large_dyadicCorrelation
    (K H : ℕ) (g : CompactCircleCharacter) (B : ℝ)
    (hK : 0 < K) (hH : 0 < H) (hB : B < H)
    (henergy : compactCharacterWeightedEnergy
      (dyadicCorrelationWindow K) (fun n ↦ (n : ℝ)⁻¹) H g ≤
        B * dyadicCorrelationWeight K) :
    ∃ a < H, ∃ b < H, a ≠ b ∧
      ((H : ℝ) - B) * dyadicCorrelationWeight K / (H : ℝ) ^ 2 ≤
        ‖compactCharacterCorrelation (dyadicCorrelationWindow K)
          (fun n ↦ (n : ℝ)⁻¹) a b g‖ := by
  exact exists_large_compactCharacterCorrelation
    (dyadicCorrelationWindow K) (fun n ↦ (n : ℝ)⁻¹) H g
    (compactCharacterWeightedEnergy
      (dyadicCorrelationWindow K) (fun n ↦ (n : ℝ)⁻¹) H g)
    B (dyadicCorrelationWeight K) hH (dyadicCorrelationWeight_pos hK)
    rfl rfl henergy hB

/-- Markov's inequality specialized to the geometric window. -/
theorem measure_dyadicWeightedEnergy_ge_le
    (μ : ProbabilityMeasure CompactCircleCharacter) (C B : ℝ)
    (K H : ℕ) (hK : 0 < K) (hB : 0 < B)
    (hbound : ∀ m : ℕ, compactMeanSquarePartialSum μ m ≤ C ^ 2) :
    (μ : Measure CompactCircleCharacter)
        {g | B * dyadicCorrelationWeight K ≤
          compactCharacterWeightedEnergy (dyadicCorrelationWindow K)
            (fun n ↦ (n : ℝ)⁻¹) H g} ≤
      ENNReal.ofReal (4 * C ^ 2 / B) := by
  exact measure_compactCharacterWeightedEnergy_ge_le
    μ C B (dyadicCorrelationWeight K) hB (dyadicCorrelationWeight_pos hK)
    hbound (dyadicCorrelationWindow K) (fun n ↦ (n : ℝ)⁻¹) H
    (fun n hn ↦ dyadicCorrelationWindow_weight_nonneg K hn) rfl

/-- Tao's Proposition 1.11 at the finite geometric scales used in this file.

The good event is the explicitly measurable small-energy event.  On it,
off-diagonal extraction and the contrapositive of logarithmic Elliott give a
character of period at most `A`, a frequency of size at most `A * 4^K`, and
pretentious distance less than `A`.  The witnesses remain existential, so no
measurable choice theorem is required. -/
theorem NonasymptoticLogElliott.exists_highProbability_pretentiousSet
    (helliott : NonasymptoticLogElliott)
    (μ : ProbabilityMeasure CompactCircleCharacter) (C B η : ℝ) (H : ℕ)
    (hBpos : 0 < B) (hH : 0 < H) (hBH : B < H) (hη : 0 < η)
    (hbound : ∀ m : ℕ, compactMeanSquarePartialSum μ m ≤ C ^ 2) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧
      ∀ A K : ℕ, A₀ ≤ A → A ≤ 2 ^ K → 0 < K →
        η * Real.log ((2 ^ K : ℕ) : ℝ) <
          ((H : ℝ) - B) * dyadicCorrelationWeight K / (H : ℝ) ^ 2 →
        ∃ G : Set CompactCircleCharacter,
          MeasurableSet G ∧
          (μ : Measure CompactCircleCharacter) Gᶜ ≤
            ENNReal.ofReal (4 * C ^ 2 / B) ∧
          ∀ g ∈ G, HasBoundedPretentiousApproximation A (4 ^ K) g := by
  obtain ⟨A₀, hA₀, hcorr⟩ :=
    helliott.uniform_compactCharacterCorrelation H η hη
  refine ⟨A₀, hA₀, ?_⟩
  intro A K hA hAK hK hthreshold
  let G : Set CompactCircleCharacter :=
    {g | compactCharacterWeightedEnergy (dyadicCorrelationWindow K)
        (fun n ↦ (n : ℝ)⁻¹) H g <
      B * dyadicCorrelationWeight K}
  refine ⟨G, ?_, ?_, ?_⟩
  · exact isOpen_lt
      (continuous_compactCharacterWeightedEnergy
        (dyadicCorrelationWindow K) (fun n ↦ (n : ℝ)⁻¹) H)
      continuous_const |>.measurableSet
  · have hmarkov := measure_dyadicWeightedEnergy_ge_le
      μ C B K H hK hBpos hbound
    simpa only [G, Set.compl_ofPred, not_lt] using hmarkov
  · intro g hg
    have henergy :
        compactCharacterWeightedEnergy (dyadicCorrelationWindow K)
            (fun n ↦ (n : ℝ)⁻¹) H g ≤
          B * dyadicCorrelationWeight K := hg.le
    obtain ⟨a, ha, b, hb, hab, hlarge⟩ :=
      exists_large_dyadicCorrelation K H g B hK hH hBH henergy
    by_contra hno
    have hsmall := hcorr A K hA hAK a ha b hb hab g hno
    linarith

/-- Consumer interface for a future logarithmic Elliott theorem.  Any theorem
which makes every off-diagonal correlation strictly smaller than the displayed
threshold contradicts the small-energy event.  The correlation bound is an
explicit hypothesis; no Elliott result is assumed in this file. -/
theorem not_dyadicWeightedEnergy_le_of_all_correlations_lt
    (K H : ℕ) (g : CompactCircleCharacter) (B : ℝ)
    (hK : 0 < K) (hH : 0 < H) (hB : B < H)
    (hCorrelationUpper :
      ∀ a < H, ∀ b < H, a ≠ b →
        ‖compactCharacterCorrelation (dyadicCorrelationWindow K)
          (fun n ↦ (n : ℝ)⁻¹) a b g‖ <
            ((H : ℝ) - B) * dyadicCorrelationWeight K / (H : ℝ) ^ 2) :
    ¬ compactCharacterWeightedEnergy (dyadicCorrelationWindow K)
        (fun n ↦ (n : ℝ)⁻¹) H g ≤ B * dyadicCorrelationWeight K := by
  intro henergy
  obtain ⟨a, ha, b, hb, hab, hlarge⟩ :=
    exists_large_dyadicCorrelation K H g B hK hH hB henergy
  exact (not_lt_of_ge hlarge) (hCorrelationUpper a ha b hb hab)

end Erdos67
