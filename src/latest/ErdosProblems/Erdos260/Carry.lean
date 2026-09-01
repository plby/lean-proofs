import ErdosProblems.Erdos260.Elementary

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Integral carries, gap control, and weighted mass

This module corresponds to Section 3 of the manuscript.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos260

/-- Finite-sum integer carry associated with a rational support expansion. -/
def carryInt (R : RationalSupport) (N : ℕ) : ℤ :=
  R.eta.num * (2 : ℤ) ^ N -
    (R.eta.den : ℤ) *
      ∑ n ∈ Finset.Icc 1 N,
        (n : ℤ) * (digit R.S n : ℤ) * (2 : ℤ) ^ (N - n)

/-- A genuine support gap: both endpoints are in the support and the open
integer interval between them is empty. -/
def IsSupportGap (S : Set ℕ) (x g : ℕ) : Prop :=
  0 < g ∧ x ∈ S ∧ x + g ∈ S ∧
    ∀ n, x < n → n < x + g → n ∉ S

/-- Counting measure in the anchor coordinate and Lebesgue measure in the
threshold coordinate. -/
def windowThresholdMeasure : Measure WindowThreshold :=
  Measure.count.prod volume

/-- Paper label: `def:mass` (Section 3).  Nonnegative mass is defined by a
lintegral so that non-integrability cannot silently turn it into zero. -/
def mass (E : Set WindowThreshold) (weight : WindowThreshold → ℝ) : ℝ≥0∞ :=
  ∫⁻ e in E, ENNReal.ofReal (weight e) ∂windowThresholdMeasure

/-- A proof-carrying witness that a mass is finite.  Unlike an unguarded
`ENNReal.toReal`, an
instance of this structure cannot be constructed when the underlying
`ℝ≥0∞`-valued mass is infinite. -/
structure FiniteMass (E : Set WindowThreshold)
    (weight : WindowThreshold → ℝ) : Prop where
  ne_top : mass E weight ≠ ⊤

namespace FiniteMass

/-- Safely convert a finite mass to a real number. -/
def toReal {E : Set WindowThreshold} {weight : WindowThreshold → ℝ}
    (_h : FiniteMass E weight) : ℝ :=
  (mass E weight).toReal

/-- The safe real conversion is nonnegative. -/
theorem toReal_nonneg {E : Set WindowThreshold} {weight : WindowThreshold → ℝ}
    (h : FiniteMass E weight) : 0 ≤ h.toReal := by
  exact ENNReal.toReal_nonneg

/-- Re-embedding the safe real conversion recovers the original mass. -/
@[simp] theorem ofReal_toReal {E : Set WindowThreshold}
    {weight : WindowThreshold → ℝ} (h : FiniteMass E weight) :
    ENNReal.ofReal h.toReal = mass E weight := by
  exact ENNReal.ofReal_toReal h.ne_top

end FiniteMass

namespace WindowSystem

theorem pairSet_eq_prod (W : WindowSystem) :
    W.pairSet = Set.prod (W.anchors : Set ℕ) W.thresholds := by
  ext e
  rfl

theorem measurableSet_pairSet (W : WindowSystem) :
    MeasurableSet W.pairSet := by
  rw [pairSet_eq_prod]
  exact MeasurableSet.prod W.anchors.measurableSet
    (by simp [WindowSystem.thresholds, thresholdInterval])

theorem measurable_excess (W : WindowSystem) :
    Measurable W.excess := by
  unfold WindowSystem.excess
  fun_prop

theorem excess_le_rawWindowSpan (W : WindowSystem) (e : WindowThreshold)
    (he : e ∈ W.pairSet) :
    W.excess e ≤ (W.rawWindowSpan e.1 : ℝ) := by
  have he' : e.1 ∈ W.anchors ∧ e.2 ∈ W.thresholds := he
  have hTlower :
      2 * (W.L : ℝ) + W.structural.C0 ≤ e.2 := he'.2.1
  have hbase :
      0 ≤ 2 * (W.L : ℝ) + W.structural.C0 := by positivity
  have hTnonneg : 0 ≤ e.2 := hbase.trans hTlower
  have heps : 0 ≤ W.epsilon * W.L :=
    mul_nonneg W.epsilon_nonneg (Nat.cast_nonneg _)
  unfold WindowSystem.excess
  apply max_le
  case h₁ => linarith
  case h₂ => positivity

end WindowSystem

theorem mass_mono_set {E F : Set WindowThreshold}
    {weight : WindowThreshold → ℝ} (hEF : E ⊆ F) :
    mass E weight ≤ mass F weight := by
  unfold mass
  exact lintegral_mono_set hEF

theorem windowThresholdMeasure_pairSet_ne_top (W : WindowSystem) :
    windowThresholdMeasure W.pairSet ≠ ⊤ := by
  rw [WindowSystem.pairSet_eq_prod, windowThresholdMeasure]
  have hprod :
      (Measure.count.prod volume)
          (Set.prod (W.anchors : Set ℕ) W.thresholds) =
        Measure.count (W.anchors : Set ℕ) * volume W.thresholds :=
    MeasureTheory.Measure.prod_prod _ _
  rw [hprod]
  simp only [Measure.count_apply_finset, WindowSystem.thresholds,
    thresholdInterval, Real.volume_Icc]
  let v : ℝ :=
    2 * (W.L : ℝ) + W.structural.C0 +
      W.structural.cI * W.L -
        (2 * (W.L : ℝ) + W.structural.C0)
  have hcard : (W.anchors.card : ℝ≥0∞) < ⊤ :=
    ENNReal.natCast_lt_top W.anchors.card
  have hvol : ENNReal.ofReal v < ⊤ := ENNReal.ofReal_lt_top
  change (W.anchors.card : ℝ≥0∞) * ENNReal.ofReal v ≠ ⊤
  exact (ENNReal.mul_lt_top hcard hvol).ne

theorem totalMass_finite (W : WindowSystem) :
    mass W.pairSet W.excess ≠ ⊤ := by
  unfold mass
  apply
    (setLIntegral_lt_top_of_le_nnreal
      (windowThresholdMeasure_pairSet_ne_top W) ?_).ne
  let bound : NNReal :=
    ⟨((W.anchors.sum W.rawWindowSpan : ℕ) : ℝ), by positivity⟩
  refine ⟨bound, ?_⟩
  intro e he
  rw [ENNReal.ofReal_le_coe]
  change
    W.excess e ≤
      ((W.anchors.sum W.rawWindowSpan : ℕ) : ℝ)
  calc
    W.excess e ≤ (W.rawWindowSpan e.1 : ℝ) :=
      W.excess_le_rawWindowSpan e he
    _ ≤ ((W.anchors.sum W.rawWindowSpan : ℕ) : ℝ) := by
      exact_mod_cast
        Finset.single_le_sum
          (fun i hi => Nat.zero_le _) he.1

theorem totalFiniteMass (W : WindowSystem) :
    FiniteMass W.pairSet W.excess :=
  ⟨totalMass_finite W⟩

/-- Every genuine subfamily of the window-pair set inherits a finite mass. -/
theorem finiteMassOfSubset (W : WindowSystem) (E : Set WindowThreshold)
    (hE : E ⊆ W.pairSet) : FiniteMass E W.excess :=
  ⟨ne_top_of_le_ne_top (totalMass_finite W) (mass_mono_set hE)⟩

/-- Safe real value of a finite window-pair subfamily.  The subset proof is
part of the interface, so infinite mass can never be silently mapped to zero. -/
def finiteWindowMass (W : WindowSystem) (E : Set WindowThreshold)
    (hE : E ⊆ W.pairSet) : ℝ :=
  (finiteMassOfSubset W E hE).toReal

def totalMassReal (W : WindowSystem) : ℝ :=
  (totalFiniteMass W).toReal

@[simp] theorem ofReal_totalMassReal (W : WindowSystem) :
    ENNReal.ofReal (totalMassReal W) =
      mass W.pairSet W.excess := by
  exact FiniteMass.ofReal_toReal (totalFiniteMass W)

@[simp] theorem weightedSupportTerm_eq_digit (S : Set ℕ) (n : ℕ) :
    weightedSupportTerm S n =
      (n : ℝ) * (digit S n : ℝ) / (2 : ℝ) ^ n := by
  by_cases hn : n ∈ S <;>
    simp [weightedSupportTerm, digit, hn]

theorem sum_range_weightedSupportTerm (S : Set ℕ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), weightedSupportTerm S n =
      ∑ n ∈ Finset.Icc 1 N, weightedSupportTerm S n := by
  rw [Finset.range_eq_Ico]
  have hinterval : Finset.Ico 0 (N + 1) = Finset.Icc 0 N := by
    ext n
    simp
  rw [hinterval, ← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le N),
    Finset.sum_insert (by simp)]
  simp [weightedSupportTerm]

theorem carryFiniteSum_cast (R : RationalSupport) (N : ℕ) :
    ((∑ n ∈ Finset.Icc 1 N,
        (n : ℤ) * (digit R.S n : ℤ) * (2 : ℤ) ^ (N - n) : ℤ) : ℝ) =
      (2 : ℝ) ^ N *
        ∑ n ∈ Finset.Icc 1 N, weightedSupportTerm R.S n := by
  rw [Int.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
  push_cast
  rw [weightedSupportTerm_eq_digit]
  have hpow : (2 : ℝ) ^ (N - n) * (2 : ℝ) ^ n = (2 : ℝ) ^ N := by
    rw [← pow_add]
    congr 1
    omega
  field_simp
  rw [← hpow]
  ring

theorem carryInt_cast_eq_partial (R : RationalSupport) (N : ℕ) :
    (carryInt R N : ℝ) =
      (R.eta.den : ℝ) * (2 : ℝ) ^ N *
        ((R.eta : ℝ) -
          ∑ n ∈ Finset.Icc 1 N, weightedSupportTerm R.S n) := by
  unfold carryInt
  push_cast
  have hfinite := carryFiniteSum_cast R N
  push_cast at hfinite
  rw [hfinite]
  have hden : (R.eta.den : ℝ) ≠ 0 := by positivity
  rw [Rat.cast_def]
  field_simp

/-- Scaled tail summand whose sum is the integer carry. -/
def carryTailTerm (R : RationalSupport) (N j : ℕ) : ℝ :=
  (R.eta.den : ℝ) * (2 : ℝ) ^ N *
    weightedSupportTerm R.S (j + (N + 1))

theorem weightedSupportTerm_nonneg (S : Set ℕ) (n : ℕ) :
    0 ≤ weightedSupportTerm S n := by
  rw [weightedSupportTerm_eq_digit]
  positivity

theorem carryTailTerm_nonneg (R : RationalSupport) (N j : ℕ) :
    0 ≤ carryTailTerm R N j := by
  have hterm :
    0 ≤ weightedSupportTerm R.S (j + (N + 1)) := by
    by_cases hmem : j + (N + 1) ∈ R.S
    · simp only [weightedSupportTerm_eq_digit, Nat.cast_add, Nat.cast_one]
      positivity
    · simp [weightedSupportTerm, hmem]
  unfold carryTailTerm
  exact mul_nonneg (by positivity) hterm

def carryMajorant (R : RationalSupport) (N j : ℕ) : ℝ :=
  (R.eta.den : ℝ) *
    (((N + 1 : ℝ) / 2) * ((1 : ℝ) / 2) ^ j +
      ((1 : ℝ) / 2) * (j : ℝ) * ((1 : ℝ) / 2) ^ j)

theorem carryTailTerm_le_majorant (R : RationalSupport) (N j : ℕ) :
    carryTailTerm R N j ≤ carryMajorant R N j := by
  let n := j + (N + 1)
  have hdigit : (digit R.S n : ℝ) ≤ 1 := by
    by_cases hn : n ∈ R.S <;> simp [digit, hn]
  have hpow : (2 : ℝ) ^ n =
      (2 : ℝ) ^ N * (2 : ℝ) ^ (j + 1) := by
    dsimp [n]
    rw [← pow_add]
    congr 1
    omega
  rw [carryTailTerm, carryMajorant, weightedSupportTerm_eq_digit]
  change
    (R.eta.den : ℝ) * 2 ^ N * ((n : ℝ) * (digit R.S n : ℝ) / 2 ^ n) ≤ _
  calc
    (R.eta.den : ℝ) * 2 ^ N *
          ((n : ℝ) * (digit R.S n : ℝ) / 2 ^ n) ≤
        (R.eta.den : ℝ) * 2 ^ N * ((n : ℝ) * 1 / 2 ^ n) := by
      gcongr
    _ = (R.eta.den : ℝ) *
        (((N + 1 : ℝ) / 2) * ((1 : ℝ) / 2) ^ j +
          ((1 : ℝ) / 2) * (j : ℝ) * ((1 : ℝ) / 2) ^ j) := by
      rw [hpow]
      simp only [div_pow, one_pow]
      field_simp
      dsimp [n]
      push_cast
      ring

theorem exists_support_gt (R : RationalSupport) (N : ℕ) :
    ∃ n ∈ R.S, N < n := by
  by_contra h
  push Not at h
  have hsubset : R.S ⊆ (Finset.range (N + 1) : Set ℕ) := by
    intro n hn
    simp only [Finset.coe_range, Set.mem_Iio]
    have hnle := h n hn
    omega
  exact R.infinite ((Finset.range (N + 1)).finite_toSet.subset hsubset)

theorem carryInt_succ (R : RationalSupport) (N : ℕ) :
    carryInt R (N + 1) =
      2 * carryInt R N -
        (R.eta.den : ℤ) * (N + 1) * (digit R.S (N + 1) : ℤ) := by
  have hsum :
      (∑ n ∈ Finset.Icc 1 (N + 1),
          (n : ℤ) * (digit R.S n : ℤ) * (2 : ℤ) ^ (N + 1 - n)) =
        2 * ∑ n ∈ Finset.Icc 1 N,
          (n : ℤ) * (digit R.S n : ℤ) * (2 : ℤ) ^ (N - n) +
          (N + 1 : ℤ) * (digit R.S (N + 1) : ℤ) := by
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hold :
        (∑ n ∈ Finset.Icc 1 N,
            (n : ℤ) * (digit R.S n : ℤ) * (2 : ℤ) ^ (N + 1 - n)) =
          2 * ∑ n ∈ Finset.Icc 1 N,
            (n : ℤ) * (digit R.S n : ℤ) * (2 : ℤ) ^ (N - n) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
      have hexponent : N + 1 - n = (N - n) + 1 := by omega
      rw [hexponent, pow_succ]
      ring
    rw [hold]
    norm_num
  unfold carryInt
  rw [hsum, pow_succ]
  ring

theorem carryInt_inside_gap (R : RationalSupport) (x g : ℕ)
    (hgap : IsSupportGap R.S x g) :
    ∀ r < g, carryInt R (x + r) = (2 : ℤ) ^ r * carryInt R x := by
  intro r hr
  induction r with
  | zero => simp
  | succ r ih =>
      have hrg : r < g := r.lt_succ_self.trans hr
      have hnotmem : x + (r + 1) ∉ R.S := by
        apply hgap.2.2.2 (x + (r + 1))
        · omega
        · omega
      have hnotmem' : x + r + 1 ∉ R.S := by
        simpa [Nat.add_assoc] using hnotmem
      rw [show x + (r + 1) = (x + r) + 1 by omega,
        carryInt_succ, ih hrg]
      simp [digit, hnotmem', pow_succ]
      ring

/-- Exact carry update from one support point to the next support point. -/
theorem carryInt_across_supportGap (R : RationalSupport) (x g : ℕ)
    (hgap : IsSupportGap R.S x g) :
    carryInt R (x + g) =
      (2 : ℤ) ^ g * carryInt R x -
        (R.eta.den : ℤ) * (x + g) := by
  have hg : 0 < g := hgap.1
  have hinside := carryInt_inside_gap R x g hgap (g - 1) (by omega)
  rw [show x + g = (x + (g - 1)) + 1 by omega, carryInt_succ,
    hinside]
  have hend : x + g ∈ R.S := hgap.2.2.1
  have hdigit : digit R.S (x + g) = 1 := by
    simp [digit, hend]
  rw [show x + (g - 1) + 1 = x + g by omega, hdigit]
  have hpow : (2 : ℤ) ^ g = 2 * (2 : ℤ) ^ (g - 1) := by
    conv_lhs => rw [show g = (g - 1) + 1 by omega, pow_succ]
    ring
  rw [hpow]
  have hcast : ((x + (g - 1) : ℕ) : ℤ) + 1 = (x : ℤ) + g := by
    exact_mod_cast (show (x + (g - 1)) + 1 = x + g by omega)
  linear_combination -(R.eta.den : ℤ) * hcast

/-- Paper label: `prop:carry` (Section 3). -/
theorem prop_carry (R : RationalSupport) :
    (∀ N : ℕ,
      carryInt R (N + 1) =
        2 * carryInt R N -
          (R.eta.den : ℤ) * (N + 1) * (digit R.S (N + 1) : ℤ)) ∧
    (∀ N : ℕ, 0 ≤ carryInt R N) ∧
    (∀ N : ℕ, carryInt R N ≤ (R.eta.den : ℤ) * (N + 2)) ∧
    (∀ N : ℕ, 1 ≤ carryInt R N) := by
  refine ⟨carryInt_succ R, ?_, ?_, ?_⟩
  · intro N
    have htail := (hasSum_nat_add_iff' (f := weightedSupportTerm R.S)
      (N + 1)).mpr R.hasSum
    rw [sum_range_weightedSupportTerm] at htail
    have htail_nonneg :
        0 ≤ (R.eta : ℝ) -
          ∑ n ∈ Finset.Icc 1 N, weightedSupportTerm R.S n := by
      rw [← htail.tsum_eq]
      simpa using htail.summable.sum_le_tsum ∅
        (fun j _ => weightedSupportTerm_nonneg R.S (j + (N + 1)))
    have hcarry : 0 ≤ (carryInt R N : ℝ) := by
      rw [carryInt_cast_eq_partial]
      exact mul_nonneg (by positivity) htail_nonneg
    exact_mod_cast hcarry
  · intro N
    have htail := (hasSum_nat_add_iff' (f := weightedSupportTerm R.S)
      (N + 1)).mpr R.hasSum
    rw [sum_range_weightedSupportTerm] at htail
    have hscaled := htail.mul_left
      ((R.eta.den : ℝ) * (2 : ℝ) ^ N)
    have hgeom := hasSum_geometric_of_norm_lt_one
      (ξ := ((1 : ℝ) / 2)) (by norm_num)
    have hlinear := hasSum_coe_mul_geometric_of_norm_lt_one
      (r := ((1 : ℝ) / 2)) (by norm_num)
    have hmajorBase :=
      (hgeom.mul_left ((N + 1 : ℝ) / 2)).add
        (hlinear.mul_left ((1 : ℝ) / 2))
    have hmajor := hmajorBase.mul_left (R.eta.den : ℝ)
    have hle := hscaled.summable.tsum_le_tsum
      (fun j => by
        simpa only [carryTailTerm, carryMajorant, mul_assoc] using
          carryTailTerm_le_majorant R N j)
      hmajor.summable
    rw [hscaled.tsum_eq, hmajor.tsum_eq] at hle
    rw [← carryInt_cast_eq_partial] at hle
    norm_num at hle
    exact_mod_cast hle
  · intro N
    have htail := (hasSum_nat_add_iff' (f := weightedSupportTerm R.S)
      (N + 1)).mpr R.hasSum
    rw [sum_range_weightedSupportTerm] at htail
    obtain ⟨n, hnS, hnN⟩ := exists_support_gt R N
    let j := n - (N + 1)
    have hindex : j + (N + 1) = n := by
      dsimp [j]
      omega
    have htermpos :
        0 < weightedSupportTerm R.S (j + (N + 1)) := by
      have hnpos : (0 : ℝ) < n := by
        exact_mod_cast R.positive n hnS
      rw [hindex]
      simp only [weightedSupportTerm, hnS, if_pos]
      positivity
    have hterm_le :
        weightedSupportTerm R.S (j + (N + 1)) ≤
          (R.eta : ℝ) -
            ∑ n ∈ Finset.Icc 1 N, weightedSupportTerm R.S n := by
      rw [← htail.tsum_eq]
      simpa using htail.summable.sum_le_tsum {j}
        (fun i _ => weightedSupportTerm_nonneg R.S (i + (N + 1)))
    have htailpos :
        0 < (R.eta : ℝ) -
          ∑ n ∈ Finset.Icc 1 N, weightedSupportTerm R.S n :=
      htermpos.trans_le hterm_le
    have hcarry : 0 < (carryInt R N : ℝ) := by
      rw [carryInt_cast_eq_partial]
      exact mul_pos (by positivity) htailpos
    have hcarryInt : 0 < carryInt R N := by exact_mod_cast hcarry
    omega

theorem gap_power_bound (R : RationalSupport) (x g : ℕ)
    (hgap : IsSupportGap R.S x g) :
    2 ^ (g - 1) ≤ R.eta.den * (x + g + 1) := by
  have hg : 0 < g := hgap.1
  have hiterate := carryInt_inside_gap R x g hgap (g - 1) (by omega)
  have hpositive : 1 ≤ carryInt R x := (prop_carry R).2.2.2 x
  have hupper := (prop_carry R).2.2.1 (x + (g - 1))
  have hpow_nonneg : (0 : ℤ) ≤ (2 : ℤ) ^ (g - 1) := by positivity
  have hint :
      (2 : ℤ) ^ (g - 1) ≤
        (R.eta.den : ℤ) * (x + g + 1) := by
    calc
      (2 : ℤ) ^ (g - 1) ≤
          (2 : ℤ) ^ (g - 1) * carryInt R x := by
        nlinarith
      _ = carryInt R (x + (g - 1)) := hiterate.symm
      _ ≤ (R.eta.den : ℤ) * ((x + (g - 1) : ℕ) + 2) := hupper
      _ = (R.eta.den : ℤ) * (x + g + 1) := by
        congr 1
        omega
  exact_mod_cast hint

theorem eventually_linear_lt_two_pow_pred (Q : ℕ) :
    ∃ x0 : ℕ, ∀ n : ℕ, x0 ≤ n → 3 * Q * n < 2 ^ (n - 1) := by
  have ht :=
    (tendsto_self_mul_const_pow_of_lt_one
      (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).const_mul
      (6 * (Q : ℝ))
  have hevent : ∀ᶠ n : ℕ in atTop,
      (6 * (Q : ℝ)) * ((n : ℝ) * (1 / 2 : ℝ) ^ n) < 1 :=
    (tendsto_order.1 ht).2 1 (by norm_num)
  obtain ⟨x0, hx0⟩ := (eventually_atTop.1 hevent)
  refine ⟨max x0 1, ?_⟩
  intro n hn
  have hnx0 : x0 ≤ n := (le_max_left x0 1).trans hn
  have hn1 : 1 ≤ n := (le_max_right x0 1).trans hn
  have h := hx0 n hnx0
  have hquot :
      (6 * (Q : ℝ) * (n : ℝ)) / (2 : ℝ) ^ n < 1 := by
    simpa only [one_div, one_mul, inv_pow, div_eq_mul_inv, mul_assoc] using h
  have hden : 0 < (2 : ℝ) ^ n := by positivity
  have h6 :
      6 * (Q : ℝ) * (n : ℝ) < (2 : ℝ) ^ n :=
    (div_lt_one hden).mp hquot
  have hpow :
      (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    calc
      (2 : ℝ) ^ n = (2 : ℝ) ^ ((n - 1) + 1) := by
        congr 1
        omega
      _ = (2 : ℝ) ^ (n - 1) * 2 := by rw [pow_succ]
      _ = 2 * (2 : ℝ) ^ (n - 1) := by ring
  rw [hpow] at h6
  have h3 :
      3 * (Q : ℝ) * (n : ℝ) < (2 : ℝ) ^ (n - 1) := by
    nlinarith
  exact_mod_cast h3

/-- Paper label: `lem:gap` (Section 3).  Both the gap constant and the
starting point are uniform over every rational support with denominator `Q`. -/
theorem lem_gap :
    ∀ Q : ℕ, 0 < Q → ∃ Cgap x0 : ℕ,
      ∀ R : RationalSupport, R.eta.den = Q → ∀ x : ℕ, x0 ≤ x →
        ∀ g : ℕ, IsSupportGap R.S x g →
          g ≤ Nat.log 2 x + Cgap := by
  intro Q hQ
  obtain ⟨xexp, hexp⟩ := eventually_linear_lt_two_pow_pred Q
  refine ⟨Nat.clog 2 (3 * Q) + 1, max xexp 1, ?_⟩
  intro R hden x hx g hgap
  have hxxexp : xexp ≤ x := (le_max_left xexp 1).trans hx
  have hx1 : 1 ≤ x := (le_max_right xexp 1).trans hx
  have hpower := gap_power_bound R x g hgap
  rw [hden] at hpower
  have hgapltx : g < x := by
    by_contra hnot
    have hxg : x ≤ g := Nat.le_of_not_gt hnot
    have hgexp : xexp ≤ g := hxxexp.trans hxg
    have hstrict := hexp g hgexp
    have hsum : x + g + 1 ≤ 3 * g := by omega
    have hlinear : Q * (x + g + 1) ≤ 3 * Q * g := by
      have := Nat.mul_le_mul_left Q hsum
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    exact (Nat.not_lt_of_ge (hpower.trans hlinear)) hstrict
  have hsum : x + g + 1 ≤ 3 * x := by omega
  have hlinear : Q * (x + g + 1) ≤ 3 * Q * x := by
    have := Nat.mul_le_mul_left Q hsum
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hpower' : 2 ^ (g - 1) ≤ 3 * Q * x := hpower.trans hlinear
  have hQpow : 3 * Q ≤ 2 ^ Nat.clog 2 (3 * Q) :=
    Nat.le_pow_clog Nat.one_lt_two (3 * Q)
  have hxpow : x < 2 ^ (Nat.log 2 x + 1) := by
    simpa [Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self Nat.one_lt_two x
  have hthreeQ : 0 < 3 * Q := Nat.mul_pos (by omega) hQ
  have hproduct :
      3 * Q * x <
        2 ^ Nat.clog 2 (3 * Q) * 2 ^ (Nat.log 2 x + 1) := by
    calc
      3 * Q * x < 3 * Q * 2 ^ (Nat.log 2 x + 1) :=
        Nat.mul_lt_mul_of_pos_left hxpow hthreeQ
      _ ≤ 2 ^ Nat.clog 2 (3 * Q) * 2 ^ (Nat.log 2 x + 1) :=
        Nat.mul_le_mul_right _ hQpow
  have hpowers :
      2 ^ (g - 1) <
        2 ^ (Nat.clog 2 (3 * Q) + (Nat.log 2 x + 1)) := by
    calc
      2 ^ (g - 1) ≤ 3 * Q * x := hpower'
      _ < 2 ^ Nat.clog 2 (3 * Q) * 2 ^ (Nat.log 2 x + 1) := hproduct
      _ = 2 ^ (Nat.clog 2 (3 * Q) + (Nat.log 2 x + 1)) := by
        exact (pow_add (2 : ℕ) _ _).symm
  have hexponents :
      g - 1 < Nat.clog 2 (3 * Q) + (Nat.log 2 x + 1) :=
    (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp hpowers
  omega

/-- Denominator-level gap data selected by `lem_gap`.  Keeping the proof in
the structure prevents later affine arguments from accepting an arbitrary
number as though it were a valid uniform gap constant. -/
structure GapParams (Q : ℕ) where
  Cgap : ℕ
  x0 : ℕ
  bound : ∀ R : RationalSupport, R.eta.den = Q → ∀ x : ℕ, x0 ≤ x →
    ∀ g : ℕ, IsSupportGap R.S x g → g ≤ Nat.log 2 x + Cgap

theorem gapParams_exists (Q : ℕ) (hQ : 0 < Q) : Nonempty (GapParams Q) := by
  obtain ⟨Cgap, x0, hbound⟩ := lem_gap Q hQ
  exact ⟨⟨Cgap, x0, hbound⟩⟩

/-- Paper label: `lem:refinement-principle` (Section 3).  Every pair may use
its own finite label set; the weights on that set form a nonnegative partition
of unity. -/
theorem lem_refinement_principle {ι : Type*}
    (E : Set WindowThreshold) (hE : MeasurableSet E)
    (weight : WindowThreshold → ℝ)
    (labels : WindowThreshold → Finset ι)
    (α : WindowThreshold → ι → ℝ)
    (hweight : ∀ e, e ∈ E → 0 ≤ weight e)
    (hα : ∀ e, e ∈ E →
      (∀ i ∈ labels e, 0 ≤ α e i) ∧ ∑ i ∈ labels e, α e i = 1) :
    (∫⁻ e in E,
        ENNReal.ofReal (∑ i ∈ labels e, weight e * α e i)
        ∂windowThresholdMeasure) = mass E weight := by
  classical
  unfold mass
  apply setLIntegral_congr_fun hE
  intro e he
  change ENNReal.ofReal (∑ i ∈ labels e, weight e * α e i) =
    ENNReal.ofReal (weight e)
  have hsum : 0 ≤ ∑ i ∈ labels e, weight e * α e i :=
    Finset.sum_nonneg fun i hi =>
      mul_nonneg (hweight e he) ((hα e he).1 i hi)
  apply (ENNReal.ofReal_eq_ofReal_iff hsum (hweight e he)).2
  rw [← Finset.mul_sum, (hα e he).2, mul_one]

end Erdos260
