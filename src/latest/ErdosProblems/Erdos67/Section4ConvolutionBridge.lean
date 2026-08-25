import ErdosProblems.Erdos67.ArchimedeanPrimeExtension
import ErdosProblems.Erdos67.ModifiedAssignmentPeriodicity
import ErdosProblems.Erdos67.Section4EulerBCC
import ErdosProblems.Erdos67.Section4WeightedSample
import ErdosProblems.Erdos67.ShiftedResidueSeries
import ErdosProblems.Erdos67.WeightedCauchyGrouping

/-!
# From a selected weighted sample to Tao's shifted convolution

This module contains the deterministic bridge from the finite weighted local
energy selected by Markov's inequality to the aggregate shifted-convolution
hypothesis used by the Euler/BCC transfer.  The genuinely scale-dependent
inputs are explicit: a uniform residue-fibre mass bound and a uniform tail
bound comparing the chosen finite Dirichlet sum with its infinite shifted
series.
-/

open scoped BigOperators ENNReal
open MeasureTheory

namespace Erdos67

noncomputable section

open ShiftedResidueSeries

/-- The selected centers lying in one `ZMod r` class. -/
def zmodResidueFiber {r : ℕ} (centers : Finset ℕ) (a : ZMod r) : Finset ℕ :=
  centers.filter fun n ↦ (n : ZMod r) = a

@[simp] theorem mem_zmodResidueFiber {r : ℕ} {centers : Finset ℕ}
    {a : ZMod r} {n : ℕ} :
    n ∈ zmodResidueFiber centers a ↔ n ∈ centers ∧ (n : ZMod r) = a := by
  simp [zmodResidueFiber]

/-- Finite shifted residue sum attached to the center set and weight. -/
def finiteShiftedResidueSeries {r : ℕ}
    (centers : Finset ℕ) (weight : ℕ → ℝ) (h : ℕ → ℂ)
    (a : ZMod r) (m : ℕ) : ℂ :=
  ∑ n ∈ zmodResidueFiber centers a, (weight n : ℂ) * h (n + m)

/-- The finite approximation to Tao's shifted residue convolution. -/
def finiteShiftedResidueConvolution {r : ℕ}
    (centers : Finset ℕ) (weight : ℕ → ℝ) (h : ℕ → ℂ)
    (u : ZMod r → ℂ) (L : ℕ) (a : ZMod r) : ℂ :=
  ∑ m ∈ Finset.Icc 1 L,
    u (a + (m : ZMod r)) * finiteShiftedResidueSeries centers weight h a m

/-- Grouping a weighted local sum by one residue class gives the finite
shifted convolution exactly.  Periodicity is required only on the displayed
fibre and shifts. -/
theorem finiteShiftedResidueConvolution_eq_groupedLocalSum
    {r : ℕ} (centers : Finset ℕ) (weight : ℕ → ℝ)
    (uNat h : ℕ → ℂ) (u : ZMod r → ℂ) (L : ℕ) (a : ZMod r)
    (hperiodic : ∀ n ∈ zmodResidueFiber centers a,
      ∀ m ∈ Finset.Icc 1 L, uNat (n + m) = u (a + (m : ZMod r))) :
    finiteShiftedResidueConvolution centers weight h u L a =
      ∑ n ∈ zmodResidueFiber centers a,
        (weight n : ℂ) * shiftedFiniteSum (fun j ↦ uNat j * h j) n L := by
  unfold finiteShiftedResidueConvolution finiteShiftedResidueSeries shiftedFiniteSum
  calc
    (∑ m ∈ Finset.Icc 1 L,
        u (a + (m : ZMod r)) *
          ∑ n ∈ zmodResidueFiber centers a, (weight n : ℂ) * h (n + m)) =
        ∑ m ∈ Finset.Icc 1 L, ∑ n ∈ zmodResidueFiber centers a,
          u (a + (m : ZMod r)) * ((weight n : ℂ) * h (n + m)) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
    _ = ∑ n ∈ zmodResidueFiber centers a, ∑ m ∈ Finset.Icc 1 L,
          u (a + (m : ZMod r)) * ((weight n : ℂ) * h (n + m)) := by
      rw [Finset.sum_comm]
    _ = ∑ n ∈ zmodResidueFiber centers a,
          (weight n : ℂ) * ∑ m ∈ Finset.Icc 1 L,
            uNat (n + m) * h (n + m) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [hperiodic n hn m hm]
      ring

/-- The residue fibres partition the selected centers. -/
theorem sum_zmodResidueFiber_eq {r : ℕ} [NeZero r]
    (centers : Finset ℕ) (F : ℕ → ℝ) :
    ∑ a : ZMod r, ∑ n ∈ zmodResidueFiber centers a, F n =
      ∑ n ∈ centers, F n := by
  simp only [zmodResidueFiber, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_eq_single (n : ZMod r)]
  · simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb)]
  · simp

/-- Aggregate weighted Cauchy--Schwarz after residue grouping. -/
theorem finiteShiftedResidueConvolutionEnergy_le
    {r : ℕ} [NeZero r]
    (centers : Finset ℕ) (weight : ℕ → ℝ)
    (uNat h : ℕ → ℂ) (u : ZMod r → ℂ)
    (good : Finset (ZMod r)) (L : ℕ) (M : ℝ)
    (hweight : ∀ n ∈ centers, 0 ≤ weight n) (hM : 0 ≤ M)
    (hperiodic : ∀ a ∈ good, ∀ n ∈ zmodResidueFiber centers a,
      ∀ m ∈ Finset.Icc 1 L, uNat (n + m) = u (a + (m : ZMod r)))
    (hfiber : ∀ a ∈ good,
      ∑ n ∈ zmodResidueFiber centers a, weight n ≤ M) :
    ∑ a ∈ good,
        Complex.normSq
          (finiteShiftedResidueConvolution centers weight h u L a) ≤
      M * weightedShiftedEnergy (fun j ↦ uNat j * h j) centers weight L := by
  have hone (a : ZMod r) (ha : a ∈ good) :
      Complex.normSq
          (finiteShiftedResidueConvolution centers weight h u L a) ≤
        M * ∑ n ∈ zmodResidueFiber centers a,
          weight n * Complex.normSq
            (shiftedFiniteSum (fun j ↦ uNat j * h j) n L) := by
    rw [finiteShiftedResidueConvolution_eq_groupedLocalSum
      centers weight uNat h u L a (hperiodic a ha)]
    refine (normSq_weighted_sum_le_mul_weighted_normSq
      (zmodResidueFiber centers a) weight
      (fun n ↦ shiftedFiniteSum (fun j ↦ uNat j * h j) n L)
      (fun n hn ↦ hweight n (mem_zmodResidueFiber.mp hn).1)).trans ?_
    exact mul_le_mul_of_nonneg_right (hfiber a ha)
      (Finset.sum_nonneg fun n hn ↦ mul_nonneg
        (hweight n (mem_zmodResidueFiber.mp hn).1)
        (Complex.normSq_nonneg _))
  calc
    (∑ a ∈ good,
        Complex.normSq
          (finiteShiftedResidueConvolution centers weight h u L a)) ≤
        ∑ a ∈ good, M * ∑ n ∈ zmodResidueFiber centers a,
          weight n * Complex.normSq
            (shiftedFiniteSum (fun j ↦ uNat j * h j) n L) :=
      Finset.sum_le_sum fun a ha ↦ hone a ha
    _ = M * ∑ a ∈ good, ∑ n ∈ zmodResidueFiber centers a,
          weight n * Complex.normSq
            (shiftedFiniteSum (fun j ↦ uNat j * h j) n L) := by
      rw [Finset.mul_sum]
    _ ≤ M * ∑ a : ZMod r, ∑ n ∈ zmodResidueFiber centers a,
          weight n * Complex.normSq
            (shiftedFiniteSum (fun j ↦ uNat j * h j) n L) := by
      apply mul_le_mul_of_nonneg_left _ hM
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ good)
      intro a _ha _hnot
      exact Finset.sum_nonneg fun n hn ↦ mul_nonneg
        (hweight n (mem_zmodResidueFiber.mp hn).1)
        (Complex.normSq_nonneg _)
    _ = M * weightedShiftedEnergy (fun j ↦ uNat j * h j)
          centers weight L := by
      rw [sum_zmodResidueFiber_eq]
      rfl

/-- A uniform finite-tail estimate and the real-exponent shift lemma compare
the finite convolution to the ordinary residue-series convolution. -/
theorem norm_finiteShiftedResidueConvolution_sub_le
    {r : ℕ} [NeZero r] {h : ℕ →*₀ ℂ}
    (hh : EulerResidue.HasUnitNorm h)
    (centers : Finset ℕ) (weight : ℕ → ℝ)
    (uResidue : ZMod r → ℂ) (hu : ∀ b, ‖uResidue b‖ ≤ 1)
    {H L : ℕ} (hL : L ≤ 2 * H) (a : ZMod r)
    {sigma : ℝ} (hsigma : 1 < sigma) (Tail : ℝ) (hTail : 0 ≤ Tail)
    (htail : ∀ m ∈ Finset.Icc 1 L,
      ‖finiteShiftedResidueSeries centers weight h a m -
          shiftedResidueSeries h a m (sigma : ℂ)‖ ≤ Tail) :
    ‖finiteShiftedResidueConvolution centers weight h uResidue L a -
        shiftedResidueConvolution h (sigma : ℂ) uResidue L a‖ ≤
      (L : ℝ) * (Tail + 4 * H) := by
  unfold finiteShiftedResidueConvolution shiftedResidueConvolution
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ m ∈ Finset.Icc 1 L,
        (uResidue (a + (m : ZMod r)) *
            finiteShiftedResidueSeries centers weight h a m -
          uResidue (a + (m : ZMod r)) *
            EulerResidue.residueLSeries h (a + (m : ZMod r)) (sigma : ℂ))‖ ≤
        ∑ _m ∈ Finset.Icc 1 L, (Tail + 4 * H) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm ↦ ?_)
      rw [← mul_sub, norm_mul]
      calc
        ‖uResidue (a + (m : ZMod r))‖ *
            ‖finiteShiftedResidueSeries centers weight h a m -
              EulerResidue.residueLSeries h (a + (m : ZMod r)) (sigma : ℂ)‖ ≤
            1 * (Tail + 2 * (m : ℝ)) := by
          apply mul_le_mul (hu _) _ (norm_nonneg _) (by positivity)
          have hshift :=
            norm_shiftedResidueSeries_sub_residueLSeries_le_two_mul
              hh a m hsigma
          rw [show finiteShiftedResidueSeries centers weight h a m -
              EulerResidue.residueLSeries h (a + (m : ZMod r)) (sigma : ℂ) =
                (finiteShiftedResidueSeries centers weight h a m -
                  shiftedResidueSeries h a m (sigma : ℂ)) +
                (shiftedResidueSeries h a m (sigma : ℂ) -
                  EulerResidue.residueLSeries h (a + (m : ZMod r)) (sigma : ℂ)) by ring]
          exact (norm_add_le _ _).trans (add_le_add (htail m hm) hshift)
        _ ≤ Tail + 4 * H := by
          have hmH : (m : ℝ) ≤ 2 * H := by
            exact_mod_cast (Finset.mem_Icc.mp hm).2.trans hL
          norm_num
          linarith
    _ = (L : ℝ) * (Tail + 4 * H) := by
      simp [nsmul_eq_mul]
      ring

/-- Squared-norm form of the finite-to-infinite convolution comparison. -/
theorem normSq_shiftedResidueConvolution_le_finite
    {r : ℕ} [NeZero r] {h : ℕ →*₀ ℂ}
    (hh : EulerResidue.HasUnitNorm h)
    (centers : Finset ℕ) (weight : ℕ → ℝ)
    (uResidue : ZMod r → ℂ) (hu : ∀ b, ‖uResidue b‖ ≤ 1)
    {H L : ℕ} (hL : L ≤ 2 * H) (a : ZMod r)
    {sigma : ℝ} (hsigma : 1 < sigma) (Tail : ℝ) (hTail : 0 ≤ Tail)
    (htail : ∀ m ∈ Finset.Icc 1 L,
      ‖finiteShiftedResidueSeries centers weight h a m -
          shiftedResidueSeries h a m (sigma : ℂ)‖ ≤ Tail) :
    Complex.normSq (shiftedResidueConvolution h (sigma : ℂ) uResidue L a) ≤
      2 * Complex.normSq
        (finiteShiftedResidueConvolution centers weight h uResidue L a) +
      2 * ((L : ℝ) * (Tail + 4 * H)) ^ 2 := by
  let Fin : ℂ := finiteShiftedResidueConvolution centers weight h uResidue L a
  let Inf : ℂ := shiftedResidueConvolution h (sigma : ℂ) uResidue L a
  have herr : ‖Fin - Inf‖ ≤ (L : ℝ) * (Tail + 4 * H) :=
    norm_finiteShiftedResidueConvolution_sub_le hh centers weight uResidue hu
      hL a hsigma Tail hTail htail
  have hsq := normSq_sub_le_two_mul_add Fin (Fin - Inf)
  rw [show Fin - (Fin - Inf) = Inf by ring] at hsq
  refine hsq.trans ?_
  have hnonneg : 0 ≤ (L : ℝ) * (Tail + 4 * H) :=
    mul_nonneg (Nat.cast_nonneg L) (add_nonneg hTail (by positivity))
  have herrsq : Complex.normSq (Fin - Inf) ≤
      ((L : ℝ) * (Tail + 4 * H)) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) herr 2
  dsimp only [Fin, Inf] at hsq ⊢
  nlinarith

/-- Aggregate finite-to-infinite bridge.  Its right side keeps the three
sources of loss separate: selected local energy, Archimedean phase removal,
and finite-tail/shift error. -/
theorem shiftedResidueConvolutionEnergy_sum_le_of_selectedEnergy
    {r : ℕ} [NeZero r] {h : ℕ →*₀ ℂ}
    (hh : EulerResidue.HasUnitNorm h)
    (centers : Finset ℕ) (weight : ℕ → ℝ)
    (uNat : ℕ → ℂ) (uResidue : ZMod r → ℂ)
    (hu : ∀ b, ‖uResidue b‖ ≤ 1)
    (good : Finset (ZMod r)) {H : ℕ} (hH : 0 < H)
    {sigma : ℝ} (hsigma : 1 < sigma)
    (M Tail E : ℝ) (hM : 0 ≤ M) (hTail : 0 ≤ Tail)
    (hweight : ∀ n ∈ centers, 0 ≤ weight n)
    (hperiodic : ∀ a ∈ good, ∀ n ∈ zmodResidueFiber centers a,
      ∀ m ∈ Finset.Icc 1 (2 * H),
        uNat (n + m) = uResidue (a + (m : ZMod r)))
    (hfiber : ∀ a ∈ good,
      ∑ n ∈ zmodResidueFiber centers a, weight n ≤ M)
    (htail : ∀ a ∈ good, ∀ m ∈ Finset.Icc 1 (2 * H),
      ‖finiteShiftedResidueSeries centers weight h a m -
          shiftedResidueSeries h a m (sigma : ℂ)‖ ≤ Tail)
    (henergy :
      ∑ L ∈ Finset.Ioc H (2 * H),
          weightedShiftedEnergy (fun j ↦ uNat j * h j) centers weight L ≤ E) :
    ∑ L ∈ Finset.Ioc H (2 * H),
        shiftedResidueConvolutionEnergy h (sigma : ℂ) uResidue good L ≤
      2 * M * E + 8 * (r : ℝ) * (H : ℝ) ^ 3 * (Tail + 4 * H) ^ 2 := by
  have hcardGood : (good.card : ℝ) ≤ r := by
    have hc : good.card ≤ r := by
      simpa only [Finset.card_univ, ZMod.card] using
        Finset.card_le_card (Finset.subset_univ good)
    exact_mod_cast hc
  have hLbound (L : ℕ) (hLIoc : L ∈ Finset.Ioc H (2 * H)) :
      shiftedResidueConvolutionEnergy h (sigma : ℂ) uResidue good L ≤
        2 * M * weightedShiftedEnergy (fun j ↦ uNat j * h j)
            centers weight L +
          8 * (r : ℝ) * (H : ℝ) ^ 2 * (Tail + 4 * H) ^ 2 := by
    have hLle : L ≤ 2 * H := (Finset.mem_Ioc.mp hLIoc).2
    unfold shiftedResidueConvolutionEnergy
    calc
      (∑ a ∈ good,
          Complex.normSq (shiftedResidueConvolution h (sigma : ℂ)
            uResidue L a)) ≤
          ∑ a ∈ good,
            (2 * Complex.normSq
                (finiteShiftedResidueConvolution centers weight h uResidue L a) +
              2 * ((L : ℝ) * (Tail + 4 * H)) ^ 2) := by
        apply Finset.sum_le_sum
        intro a ha
        exact normSq_shiftedResidueConvolution_le_finite hh centers weight
          uResidue hu hLle a hsigma Tail hTail
            (fun m hm ↦ htail a ha m
              (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hm).1,
                (Finset.mem_Icc.mp hm).2.trans hLle⟩))
      _ = 2 * (∑ a ∈ good,
            Complex.normSq
              (finiteShiftedResidueConvolution centers weight h uResidue L a)) +
          2 * good.card * ((L : ℝ) * (Tail + 4 * H)) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ 2 * (M * weightedShiftedEnergy (fun j ↦ uNat j * h j)
              centers weight L) +
          2 * (r : ℝ) * (((2 * H : ℕ) : ℝ) * (Tail + 4 * H)) ^ 2 := by
        gcongr
        · exact finiteShiftedResidueConvolutionEnergy_le centers weight
            uNat h uResidue good L M hweight hM
            (fun a ha n hn m hm ↦ hperiodic a ha n hn m
              (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hm).1,
                (Finset.mem_Icc.mp hm).2.trans hLle⟩)) hfiber
      _ = 2 * M * weightedShiftedEnergy (fun j ↦ uNat j * h j)
              centers weight L +
          8 * (r : ℝ) * (H : ℝ) ^ 2 * (Tail + 4 * H) ^ 2 := by
        push_cast
        ring
  have hsum := Finset.sum_le_sum fun L hLIoc ↦ hLbound L hLIoc
  calc
    (∑ L ∈ Finset.Ioc H (2 * H),
        shiftedResidueConvolutionEnergy h (sigma : ℂ) uResidue good L) ≤
        ∑ L ∈ Finset.Ioc H (2 * H),
          (2 * M * weightedShiftedEnergy (fun j ↦ uNat j * h j)
              centers weight L +
            8 * (r : ℝ) * (H : ℝ) ^ 2 * (Tail + 4 * H) ^ 2) := hsum
    _ = 2 * M * (∑ L ∈ Finset.Ioc H (2 * H),
          weightedShiftedEnergy (fun j ↦ uNat j * h j) centers weight L) +
        8 * (r : ℝ) * (H : ℝ) ^ 3 * (Tail + 4 * H) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      have hcard : (Finset.Ioc H (2 * H)).card = H := by
        rw [Nat.card_Ioc]
        omega
      simp only [Finset.sum_const, hcard, nsmul_eq_mul]
      ring
    _ ≤ 2 * M * E +
        8 * (r : ℝ) * (H : ℝ) ^ 3 * (Tail + 4 * H) ^ 2 := by
      gcongr

/-- Aggregate bridge with a class-dependent low-cutoff error and a uniform
high-tail error.  Keeping the square-sum of the low errors is essential:
replacing them by a global supremum would introduce a spurious conductor
factor in the final Section 4 budget. -/
theorem shiftedResidueConvolutionEnergy_sum_le_of_classTail
    {r : ℕ} [NeZero r] {h : ℕ →*₀ ℂ}
    (hh : EulerResidue.HasUnitNorm h)
    (centers : Finset ℕ) (weight : ℕ → ℝ)
    (uNat : ℕ → ℂ) (uResidue : ZMod r → ℂ)
    (hu : ∀ b, ‖uResidue b‖ ≤ 1)
    (good : Finset (ZMod r)) {H : ℕ} (hH : 0 < H)
    {sigma : ℝ} (hsigma : 1 < sigma)
    (M TailHigh LowSq E : ℝ) (hM : 0 ≤ M) (hTailHigh : 0 ≤ TailHigh)
    (low : ZMod r → ℝ) (hlow : ∀ a ∈ good, 0 ≤ low a)
    (hweight : ∀ n ∈ centers, 0 ≤ weight n)
    (hperiodic : ∀ a ∈ good, ∀ n ∈ zmodResidueFiber centers a,
      ∀ m ∈ Finset.Icc 1 (2 * H),
        uNat (n + m) = uResidue (a + (m : ZMod r)))
    (hfiber : ∀ a ∈ good,
      ∑ n ∈ zmodResidueFiber centers a, weight n ≤ M)
    (hlowSq : ∑ a ∈ good, (low a) ^ 2 ≤ LowSq)
    (htail : ∀ a ∈ good, ∀ m ∈ Finset.Icc 1 (2 * H),
      ‖finiteShiftedResidueSeries centers weight h a m -
          shiftedResidueSeries h a m (sigma : ℂ)‖ ≤ low a + TailHigh)
    (henergy :
      ∑ L ∈ Finset.Ioc H (2 * H),
          weightedShiftedEnergy (fun j ↦ uNat j * h j) centers weight L ≤ E) :
    ∑ L ∈ Finset.Ioc H (2 * H),
        shiftedResidueConvolutionEnergy h (sigma : ℂ) uResidue good L ≤
      2 * M * E + 16 * (H : ℝ) ^ 3 * LowSq +
        16 * (r : ℝ) * (H : ℝ) ^ 3 * (TailHigh + 4 * H) ^ 2 := by
  have hcardGood : (good.card : ℝ) ≤ r := by
    have hc : good.card ≤ r := by
      simpa only [Finset.card_univ, ZMod.card] using
        Finset.card_le_card (Finset.subset_univ good)
    exact_mod_cast hc
  have hLbound (L : ℕ) (hLIoc : L ∈ Finset.Ioc H (2 * H)) :
      shiftedResidueConvolutionEnergy h (sigma : ℂ) uResidue good L ≤
        2 * M * weightedShiftedEnergy (fun j ↦ uNat j * h j)
            centers weight L +
          16 * (H : ℝ) ^ 2 * LowSq +
          16 * (r : ℝ) * (H : ℝ) ^ 2 * (TailHigh + 4 * H) ^ 2 := by
    have hLle : L ≤ 2 * H := (Finset.mem_Ioc.mp hLIoc).2
    have hLR : (L : ℝ) ≤ 2 * H := by exact_mod_cast hLle
    unfold shiftedResidueConvolutionEnergy
    calc
      (∑ a ∈ good,
          Complex.normSq (shiftedResidueConvolution h (sigma : ℂ)
            uResidue L a)) ≤
          ∑ a ∈ good,
            (2 * Complex.normSq
                (finiteShiftedResidueConvolution centers weight h uResidue L a) +
              2 * ((L : ℝ) * (low a + TailHigh + 4 * H)) ^ 2) := by
        apply Finset.sum_le_sum
        intro a ha
        simpa only [add_assoc] using
          normSq_shiftedResidueConvolution_le_finite hh centers weight
            uResidue hu hLle a hsigma (low a + TailHigh)
              (add_nonneg (hlow a ha) hTailHigh)
              (fun m hm ↦ htail a ha m
                (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hm).1,
                  (Finset.mem_Icc.mp hm).2.trans hLle⟩))
      _ ≤ ∑ a ∈ good,
            (2 * Complex.normSq
                (finiteShiftedResidueConvolution centers weight h uResidue L a) +
              4 * (L : ℝ) ^ 2 * (low a) ^ 2 +
              4 * (L : ℝ) ^ 2 * (TailHigh + 4 * H) ^ 2) := by
        apply Finset.sum_le_sum
        intro a ha
        have hl0 := hlow a ha
        have hh0 : 0 ≤ TailHigh + 4 * H := add_nonneg hTailHigh (by positivity)
        nlinarith [sq_nonneg (low a - (TailHigh + 4 * H))]
      _ = 2 * (∑ a ∈ good,
            Complex.normSq
              (finiteShiftedResidueConvolution centers weight h uResidue L a)) +
          4 * (L : ℝ) ^ 2 * (∑ a ∈ good, (low a) ^ 2) +
          4 * (L : ℝ) ^ 2 * good.card * (TailHigh + 4 * H) ^ 2 := by
        simp_rw [Finset.sum_add_distrib, Finset.mul_sum]
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ 2 * (M * weightedShiftedEnergy (fun j ↦ uNat j * h j)
              centers weight L) +
          4 * (2 * H : ℝ) ^ 2 * LowSq +
          4 * (2 * H : ℝ) ^ 2 * (r : ℝ) * (TailHigh + 4 * H) ^ 2 := by
        have hfinite := finiteShiftedResidueConvolutionEnergy_le centers weight
          uNat h uResidue good L M hweight hM
          (fun a ha n hn m hm ↦ hperiodic a ha n hn m
            (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hm).1,
              (Finset.mem_Icc.mp hm).2.trans hLle⟩)) hfiber
        have hLsq : (L : ℝ) ^ 2 ≤ (2 * H : ℝ) ^ 2 := by nlinarith
        have hlowSq0 : 0 ≤ ∑ a ∈ good, (low a) ^ 2 :=
          Finset.sum_nonneg fun a ha ↦ sq_nonneg _
        gcongr
      _ = 2 * M * weightedShiftedEnergy (fun j ↦ uNat j * h j)
              centers weight L +
          16 * (H : ℝ) ^ 2 * LowSq +
          16 * (r : ℝ) * (H : ℝ) ^ 2 * (TailHigh + 4 * H) ^ 2 := by ring
  have hsum := Finset.sum_le_sum fun L hLIoc ↦ hLbound L hLIoc
  calc
    (∑ L ∈ Finset.Ioc H (2 * H),
        shiftedResidueConvolutionEnergy h (sigma : ℂ) uResidue good L) ≤
        ∑ L ∈ Finset.Ioc H (2 * H),
          (2 * M * weightedShiftedEnergy (fun j ↦ uNat j * h j)
              centers weight L + 16 * (H : ℝ) ^ 2 * LowSq +
            16 * (r : ℝ) * (H : ℝ) ^ 2 *
              (TailHigh + 4 * H) ^ 2) := hsum
    _ = 2 * M * (∑ L ∈ Finset.Ioc H (2 * H),
          weightedShiftedEnergy (fun j ↦ uNat j * h j) centers weight L) +
        16 * (H : ℝ) ^ 3 * LowSq +
        16 * (r : ℝ) * (H : ℝ) ^ 3 * (TailHigh + 4 * H) ^ 2 := by
      simp_rw [Finset.sum_add_distrib, Finset.mul_sum]
      have hcard : (Finset.Ioc H (2 * H)).card = H := by
        rw [Nat.card_Ioc]
        omega
      simp only [Finset.sum_const, hcard, nsmul_eq_mul]
      ring
    _ ≤ 2 * M * E + 16 * (H : ℝ) ^ 3 * LowSq +
        16 * (r : ℝ) * (H : ℝ) ^ 3 * (TailHigh + 4 * H) ^ 2 := by
      gcongr

/-- One-call generic composition with Archimedean phase removal. -/
theorem shiftedResidueConvolutionEnergy_sum_le_of_phaseRemoval
    {r : ℕ} [NeZero r] {h : ℕ →*₀ ℂ}
    (hh : EulerResidue.HasUnitNorm h)
    (centers : Finset ℕ) (weight : ℕ → ℝ)
    (base uNat phase : ℕ → ℂ) (uResidue : ZMod r → ℂ)
    (hu : ∀ b, ‖uResidue b‖ ≤ 1)
    (good : Finset (ZMod r)) {H : ℕ} (hH : 0 < H)
    {sigma : ℝ} (hsigma : 1 < sigma)
    (B W M Tail eps : ℝ) (hM : 0 ≤ M) (hTail : 0 ≤ Tail)
    (heps : 0 ≤ eps)
    (hweight : ∀ n ∈ centers, 0 ≤ weight n)
    (hweightSum : ∑ n ∈ centers, weight n = W)
    (hbaseEnergy : mediumWeightedShiftedEnergy base centers weight H ≤ B * W)
    (hfactor : ∀ n ∈ centers, ∀ L ∈ Finset.Ioc H (2 * H),
      ∀ j ∈ Finset.Icc 1 L,
        base (n + j) = uNat (n + j) * phase (n + j) * h (n + j))
    (hphase : ∀ n ∈ centers, ‖phase n‖ = 1)
    (huNat : ∀ n ∈ centers, ∀ L ∈ Finset.Ioc H (2 * H),
      ∀ j ∈ Finset.Icc 1 L, ‖uNat (n + j)‖ ≤ 1)
    (hcorr : ∀ n ∈ centers, ∀ L ∈ Finset.Ioc H (2 * H),
      ∀ j ∈ Finset.Icc 1 L, ‖h (n + j)‖ ≤ 1)
    (hslow : ∀ n ∈ centers, ∀ L ∈ Finset.Ioc H (2 * H),
      ∀ j ∈ Finset.Icc 1 L, ‖phase (n + j) - phase n‖ ≤ eps)
    (hperiodic : ∀ a ∈ good, ∀ n ∈ zmodResidueFiber centers a,
      ∀ m ∈ Finset.Icc 1 (2 * H),
        uNat (n + m) = uResidue (a + (m : ZMod r)))
    (hfiber : ∀ a ∈ good,
      ∑ n ∈ zmodResidueFiber centers a, weight n ≤ M)
    (htail : ∀ a ∈ good, ∀ m ∈ Finset.Icc 1 (2 * H),
      ‖finiteShiftedResidueSeries centers weight h a m -
          shiftedResidueSeries h a m (sigma : ℂ)‖ ≤ Tail) :
    ∑ L ∈ Finset.Ioc H (2 * H),
        shiftedResidueConvolutionEnergy h (sigma : ℂ) uResidue good L ≤
      4 * M * B * W * H + 16 * M * (H : ℝ) ^ 3 * eps ^ 2 * W +
        8 * (r : ℝ) * (H : ℝ) ^ 3 * (Tail + 4 * H) ^ 2 := by
  have hremove := mediumWeightedShiftedEnergy_remove_phase_le
    base uNat phase h centers weight hH eps heps hweight hfactor hphase
      huNat hcorr hslow
  rw [hweightSum] at hremove
  have hmedium :
      mediumWeightedShiftedEnergy (fun j ↦ uNat j * h j)
          centers weight H ≤
        2 * B * W + 8 * (H : ℝ) ^ 2 * eps ^ 2 * W := by
    calc
      mediumWeightedShiftedEnergy (fun j ↦ uNat j * h j)
          centers weight H ≤
          2 * mediumWeightedShiftedEnergy base centers weight H +
            8 * (H : ℝ) ^ 2 * eps ^ 2 * W := hremove
      _ ≤ 2 * (B * W) + 8 * (H : ℝ) ^ 2 * eps ^ 2 * W := by
        simpa only [add_comm] using add_le_add_right
          (mul_le_mul_of_nonneg_left hbaseEnergy
            (show (0 : ℝ) ≤ 2 by norm_num))
          (8 * (H : ℝ) ^ 2 * eps ^ 2 * W)
      _ = 2 * B * W + 8 * (H : ℝ) ^ 2 * eps ^ 2 * W := by ring
  have hsum_eq :
      ∑ L ∈ Finset.Ioc H (2 * H),
          weightedShiftedEnergy (fun j ↦ uNat j * h j) centers weight L =
        (H : ℝ) * mediumWeightedShiftedEnergy
          (fun j ↦ uNat j * h j) centers weight H := by
    unfold mediumWeightedShiftedEnergy
    field_simp
  have henergy :
      ∑ L ∈ Finset.Ioc H (2 * H),
          weightedShiftedEnergy (fun j ↦ uNat j * h j) centers weight L ≤
        (H : ℝ) *
          (2 * B * W + 8 * (H : ℝ) ^ 2 * eps ^ 2 * W) := by
    rw [hsum_eq]
    exact mul_le_mul_of_nonneg_left hmedium (Nat.cast_nonneg H)
  have haggregate := shiftedResidueConvolutionEnergy_sum_le_of_selectedEnergy
    hh centers weight uNat uResidue hu good hH hsigma M Tail
      ((H : ℝ) * (2 * B * W + 8 * (H : ℝ) ^ 2 * eps ^ 2 * W))
      hM hTail hweight hperiodic hfiber htail henergy
  refine haggregate.trans_eq ?_
  ring

/-- Phase-removal composition for the conductor-uniform classwise low-tail
bridge. -/
theorem shiftedResidueConvolutionEnergy_sum_le_of_phaseRemoval_classTail
    {r : ℕ} [NeZero r] {h : ℕ →*₀ ℂ}
    (hh : EulerResidue.HasUnitNorm h)
    (centers : Finset ℕ) (weight : ℕ → ℝ)
    (base uNat phase : ℕ → ℂ) (uResidue : ZMod r → ℂ)
    (hu : ∀ b, ‖uResidue b‖ ≤ 1)
    (good : Finset (ZMod r)) {H : ℕ} (hH : 0 < H)
    {sigma : ℝ} (hsigma : 1 < sigma)
    (B W M TailHigh LowSq eps : ℝ) (hM : 0 ≤ M)
    (hTailHigh : 0 ≤ TailHigh) (heps : 0 ≤ eps)
    (low : ZMod r → ℝ) (hlow : ∀ a ∈ good, 0 ≤ low a)
    (hweight : ∀ n ∈ centers, 0 ≤ weight n)
    (hweightSum : ∑ n ∈ centers, weight n = W)
    (hbaseEnergy : mediumWeightedShiftedEnergy base centers weight H ≤ B * W)
    (hfactor : ∀ n ∈ centers, ∀ L ∈ Finset.Ioc H (2 * H),
      ∀ j ∈ Finset.Icc 1 L,
        base (n + j) = uNat (n + j) * phase (n + j) * h (n + j))
    (hphase : ∀ n ∈ centers, ‖phase n‖ = 1)
    (huNat : ∀ n ∈ centers, ∀ L ∈ Finset.Ioc H (2 * H),
      ∀ j ∈ Finset.Icc 1 L, ‖uNat (n + j)‖ ≤ 1)
    (hcorr : ∀ n ∈ centers, ∀ L ∈ Finset.Ioc H (2 * H),
      ∀ j ∈ Finset.Icc 1 L, ‖h (n + j)‖ ≤ 1)
    (hslow : ∀ n ∈ centers, ∀ L ∈ Finset.Ioc H (2 * H),
      ∀ j ∈ Finset.Icc 1 L, ‖phase (n + j) - phase n‖ ≤ eps)
    (hperiodic : ∀ a ∈ good, ∀ n ∈ zmodResidueFiber centers a,
      ∀ m ∈ Finset.Icc 1 (2 * H),
        uNat (n + m) = uResidue (a + (m : ZMod r)))
    (hfiber : ∀ a ∈ good,
      ∑ n ∈ zmodResidueFiber centers a, weight n ≤ M)
    (hlowSq : ∑ a ∈ good, (low a) ^ 2 ≤ LowSq)
    (htail : ∀ a ∈ good, ∀ m ∈ Finset.Icc 1 (2 * H),
      ‖finiteShiftedResidueSeries centers weight h a m -
          shiftedResidueSeries h a m (sigma : ℂ)‖ ≤ low a + TailHigh) :
    ∑ L ∈ Finset.Ioc H (2 * H),
        shiftedResidueConvolutionEnergy h (sigma : ℂ) uResidue good L ≤
      4 * M * B * W * H + 16 * M * (H : ℝ) ^ 3 * eps ^ 2 * W +
        16 * (H : ℝ) ^ 3 * LowSq +
        16 * (r : ℝ) * (H : ℝ) ^ 3 * (TailHigh + 4 * H) ^ 2 := by
  have hremove := mediumWeightedShiftedEnergy_remove_phase_le
    base uNat phase h centers weight hH eps heps hweight hfactor hphase
      huNat hcorr hslow
  rw [hweightSum] at hremove
  have hmedium :
      mediumWeightedShiftedEnergy (fun j ↦ uNat j * h j)
          centers weight H ≤
        2 * B * W + 8 * (H : ℝ) ^ 2 * eps ^ 2 * W := by
    calc
      mediumWeightedShiftedEnergy (fun j ↦ uNat j * h j) centers weight H ≤
          2 * mediumWeightedShiftedEnergy base centers weight H +
            8 * (H : ℝ) ^ 2 * eps ^ 2 * W := hremove
      _ ≤ 2 * (B * W) + 8 * (H : ℝ) ^ 2 * eps ^ 2 * W := by
        simpa only [add_comm] using add_le_add_right
          (mul_le_mul_of_nonneg_left hbaseEnergy
            (show (0 : ℝ) ≤ 2 by norm_num))
          (8 * (H : ℝ) ^ 2 * eps ^ 2 * W)
      _ = _ := by ring
  have hsum_eq :
      ∑ L ∈ Finset.Ioc H (2 * H),
          weightedShiftedEnergy (fun j ↦ uNat j * h j) centers weight L =
        (H : ℝ) * mediumWeightedShiftedEnergy
          (fun j ↦ uNat j * h j) centers weight H := by
    unfold mediumWeightedShiftedEnergy
    field_simp
  have henergy :
      ∑ L ∈ Finset.Ioc H (2 * H),
          weightedShiftedEnergy (fun j ↦ uNat j * h j) centers weight L ≤
        (H : ℝ) *
          (2 * B * W + 8 * (H : ℝ) ^ 2 * eps ^ 2 * W) := by
    rw [hsum_eq]
    exact mul_le_mul_of_nonneg_left hmedium (Nat.cast_nonneg H)
  have haggregate := shiftedResidueConvolutionEnergy_sum_le_of_classTail
    hh centers weight uNat uResidue hu good hH hsigma M TailHigh LowSq
      ((H : ℝ) * (2 * B * W + 8 * (H : ℝ) ^ 2 * eps ^ 2 * W))
      hM hTailHigh low hlow hweight hperiodic hfiber hlowSq htail henergy
  refine haggregate.trans_eq ?_
  ring

/-! ## Specialization to the selected primitive-character data -/

/-- Nearby two-scale frequencies improve the large-scale frequency bound
from `A * Y^D` to `(A+1)Y`. -/
theorem Section4CharacterData.abs_t_le_nearbyScale
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S) :
    |W.t| ≤ (S.A + 1 : ℝ) * (4 ^ S.K : ℕ) := by
  have htri : |W.t| ≤ |W.tSmall| + |W.tSmall - W.t| := by
    calc
      |W.t| = |W.tSmall + (W.t - W.tSmall)| := by ring_nf
      _ ≤ |W.tSmall| + |W.t - W.tSmall| := abs_add_le _ _
      _ = |W.tSmall| + |W.tSmall - W.t| := by rw [abs_sub_comm]
  calc
    |W.t| ≤ |W.tSmall| + |W.tSmall - W.t| := htri
    _ ≤ (S.A : ℝ) * (4 ^ S.K : ℕ) + (4 ^ S.K : ℕ) :=
      add_le_add W.tSmall_bound W.frequencies_near.le
    _ = (S.A + 1 : ℝ) * (4 ^ S.K : ℕ) := by push_cast; ring

/-- Uniform Archimedean error on centers at least `Y²`, where `Y=4^K`.
This is Tao's `O(H/Y)` error after the nearby-frequency step. -/
def Section4Selection.phaseError {C : ℝ} (S : Section4Selection C) : ℝ :=
  ((S.A + 1 : ℝ) * (4 ^ S.K : ℕ) * (2 * S.H : ℕ)) /
    ((4 ^ S.K : ℕ) : ℝ) ^ 2

theorem Section4Selection.phaseError_nonneg
    {C : ℝ} (S : Section4Selection C) : 0 ≤ S.phaseError := by
  unfold Section4Selection.phaseError
  positivity

/-- A scale-transparent version of the Archimedean error: once `A ≤ 2^K`,
the nearby-frequency loss is at most `4H / 2^K`.  Thus this part of the
convolution budget can be made small by the final choice of `K`, after all
conductor and BCC parameters have already been fixed. -/
theorem Section4Selection.phaseError_le_four_mul_div_two_pow
    {C : ℝ} (S : Section4Selection C) :
    S.phaseError ≤ 4 * (S.H : ℝ) / ((2 ^ S.K : ℕ) : ℝ) := by
  have hpowNat : 4 ^ S.K = (2 ^ S.K) ^ 2 := by
    calc
      4 ^ S.K = (2 ^ 2) ^ S.K := by norm_num
      _ = 2 ^ (2 * S.K) := by rw [pow_mul]
      _ = 2 ^ (S.K * 2) := by rw [Nat.mul_comm]
      _ = (2 ^ S.K) ^ 2 := by rw [pow_mul]
  have hzNat : 0 < 2 ^ S.K := pow_pos (by omega) _
  have hz : (0 : ℝ) < (2 ^ S.K : ℕ) := by exact_mod_cast hzNat
  have hA1Nat : S.A + 1 ≤ 2 * (2 ^ S.K) := by
    have hA := S.A_le_two_pow_K
    have hone : 1 ≤ 2 ^ S.K := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
    omega
  have hA1 : (S.A + 1 : ℝ) ≤ 2 * ((2 ^ S.K : ℕ) : ℝ) := by
    exact_mod_cast hA1Nat
  unfold Section4Selection.phaseError
  rw [hpowNat]
  push_cast
  field_simp
  have hmul := mul_le_mul_of_nonneg_right hA1
    (show (0 : ℝ) ≤ 2 * S.H by positivity)
  calc
    ((S.A : ℝ) + 1) * 2 * (S.H : ℝ) =
        ((S.A : ℝ) + 1) * (2 * (S.H : ℝ)) := by ring
    _ ≤ 2 * ((2 ^ S.K : ℕ) : ℝ) * (2 * (S.H : ℝ)) := hmul
    _ = (2 : ℝ) ^ S.K * (S.H : ℝ) * 4 := by
      norm_num
      ring

theorem Section4CharacterData.norm_arch_phase_sub_le_phaseError
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    {n j : ℕ} (hn : (4 ^ S.K) ^ 2 ≤ n) (hj : j ≤ 2 * S.H) :
    ‖(primeExtension (archimedeanPrimeAssignment W.t) (n + j) : ℂ) -
        (primeExtension (archimedeanPrimeAssignment W.t) n : ℂ)‖ ≤
      S.phaseError := by
  have hY : 0 < 4 ^ S.K := pow_pos (by omega) _
  have hnpos : 0 < n := (pow_pos hY 2).trans_le hn
  have hbase := norm_primeExtension_archimedean_sub_le W.t hnpos (h := j)
  have ht := W.abs_t_le_nearbyScale
  have hjR : (j : ℝ) ≤ ((2 * S.H : ℕ) : ℝ) := by exact_mod_cast hj
  have hnR : (((4 ^ S.K) ^ 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
  have hden : (0 : ℝ) < n := by exact_mod_cast hnpos
  calc
    ‖(primeExtension (archimedeanPrimeAssignment W.t) (n + j) : ℂ) -
        (primeExtension (archimedeanPrimeAssignment W.t) n : ℂ)‖ ≤
        |W.t| * (j : ℝ) / n := hbase
    _ ≤ ((S.A + 1 : ℝ) * (4 ^ S.K : ℕ)) * (2 * S.H : ℕ) /
          (((4 ^ S.K) ^ 2 : ℕ) : ℝ) := by
      exact div_le_div₀ (by positivity)
        (mul_le_mul ht hjR (Nat.cast_nonneg _) (by positivity))
        (by exact_mod_cast (pow_pos hY 2)) hnR
    _ = S.phaseError := by
      unfold Section4Selection.phaseError
      push_cast
      ring

theorem Section4CharacterData.primitiveCorrectionHom_apply_pos
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    {n : ℕ} (hn : n ≠ 0) :
    W.primitiveCorrectionHom n =
      (primeExtension W.primitiveAssignmentData.correction n : ℂ) := by
  unfold Section4CharacterData.primitiveCorrectionHom
    WitnessAssignmentData.correctionHom
  rw [zeroPreservingPrimeExtension_apply_of_ne_zero _ hn]

/-- The modified primitive assignment is periodic on every shifted cyclic
good class, including the conductor-one branch. -/
theorem Section4CharacterData.primitiveModified_periodic_on_cyclicGood
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    {a : ZMod (W.primitiveQ ^ S.k)}
    (ha : a ∈ cyclicGoodResidues W.primitiveQ S.k S.H)
    {n m : ℕ} (hn : (n : ZMod (W.primitiveQ ^ S.k)) = a)
    (hm : m ∈ Finset.Icc 1 (2 * S.H)) :
    (primeExtension W.primitiveModifiedAssignment (n + m) : ℂ) =
      W.primitiveModifiedResidueValue (a + (m : ZMod (W.primitiveQ ^ S.k))) := by
  by_cases hQ : W.primitiveQ = 1
  · simp only [Section4CharacterData.primitiveModifiedResidueValue,
      W.primeExtension_primitiveModified_eq_one hQ]
  · unfold Section4CharacterData.primitiveModifiedResidueValue
    apply primeExtension_eq_shiftVal_of_mem_cyclicGoodResidues
      W.primitiveModifiedAssignment W.primitiveChi
      W.primitiveModifiedAssignment_agrees
    · exact lt_of_le_of_ne
        (Nat.one_le_iff_ne_zero.mpr (NeZero.ne W.primitiveQ)) (Ne.symm hQ)
    · exact S.k_pos
    · exact ha
    · exact hm
    · have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
      omega
    · simpa only [Nat.cast_add, hn]

/-- Primitive/cyclic-good specialization of the complete finite-to-infinite
bridge.  Factorization, unit norms, good-class periodicity, nearby-frequency
control, and Archimedean phase removal are all discharged here.  The two
remaining scale facts are stated honestly: a residue-fibre mass bound,
classwise low-cutoff masses, and a uniform high-tail approximation. -/
theorem Section4CharacterData.primitive_shiftedResidueConvolutionEnergy_le_of_selectedEnergy
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    (centers : Finset ℕ) (weight : ℕ → ℝ)
    (Bsel Wmass M TailHigh LowSq : ℝ) {sigma : ℝ} (hsigma : 1 < sigma)
    (hM : 0 ≤ M) (hTailHigh : 0 ≤ TailHigh)
    (low : ZMod (W.primitiveQ ^ S.k) → ℝ)
    (hlow : ∀ a ∈ cyclicGoodResidues W.primitiveQ S.k S.H, 0 ≤ low a)
    (hweight : ∀ n ∈ centers, 0 ≤ weight n)
    (hweightSum : ∑ n ∈ centers, weight n = Wmass)
    (hcenters : ∀ n ∈ centers, (4 ^ S.K) ^ 2 ≤ n)
    (hselected :
      compactMediumWeightedLocalEnergy centers weight S.H S.sample ≤
        Bsel * Wmass)
    (hfiber : ∀ a ∈ cyclicGoodResidues W.primitiveQ S.k S.H,
      ∑ n ∈ zmodResidueFiber centers a, weight n ≤ M)
    (hlowSq : ∑ a ∈ cyclicGoodResidues W.primitiveQ S.k S.H,
      (low a) ^ 2 ≤ LowSq)
    (htail : ∀ a ∈ cyclicGoodResidues W.primitiveQ S.k S.H,
      ∀ m ∈ Finset.Icc 1 (2 * S.H),
        ‖finiteShiftedResidueSeries centers weight W.primitiveCorrectionHom a m -
            shiftedResidueSeries W.primitiveCorrectionHom a m (sigma : ℂ)‖ ≤
          low a + TailHigh) :
    ∑ L ∈ Finset.Ioc S.H (2 * S.H),
        shiftedResidueConvolutionEnergy W.primitiveCorrectionHom (sigma : ℂ)
          W.primitiveModifiedResidueValue
          (cyclicGoodResidues W.primitiveQ S.k S.H) L ≤
      4 * M * Bsel * Wmass * S.H +
        16 * M * (S.H : ℝ) ^ 3 * S.phaseError ^ 2 * Wmass +
        16 * (S.H : ℝ) ^ 3 * LowSq +
        16 * ((W.primitiveQ ^ S.k : ℕ) : ℝ) * (S.H : ℝ) ^ 3 *
          (TailHigh + 4 * S.H) ^ 2 := by
  let base : ℕ → ℂ := fun n ↦
    (primeExtension (compactCharacterPrimeAssignment S.sample) n : ℂ)
  let uNat : ℕ → ℂ := fun n ↦
    (primeExtension W.primitiveModifiedAssignment n : ℂ)
  let phase : ℕ → ℂ := fun n ↦
    (primeExtension (archimedeanPrimeAssignment W.t) n : ℂ)
  have hbaseEnergy : mediumWeightedShiftedEnergy base centers weight S.H ≤
      Bsel * Wmass := by
    rw [← mediumWeightedLocalEnergy_eq_mediumWeightedShiftedEnergy]
    simpa only [base, compactMediumWeightedLocalEnergy,
      compactCharacterPrimeAssignment] using hselected
  apply shiftedResidueConvolutionEnergy_sum_le_of_phaseRemoval_classTail
    W.primitiveCorrectionHom_hasUnitNorm centers weight base uNat phase
      W.primitiveModifiedResidueValue
      W.norm_primitiveModifiedResidueValue_le_one
      (cyclicGoodResidues W.primitiveQ S.k S.H) S.H_pos hsigma
      Bsel Wmass M TailHigh LowSq S.phaseError hM hTailHigh
      S.phaseError_nonneg low hlow hweight hweightSum hbaseEnergy
  · intro n hn L hL j hj
    have hnpos : 0 < n :=
      (pow_pos (pow_pos (by omega : 0 < 4) S.K) 2).trans_le (hcenters n hn)
    have hnj0 : n + j ≠ 0 := by omega
    rw [W.primitiveCorrectionHom_apply_pos hnj0]
    have hf := congrArg (fun z : Circle ↦ (z : ℂ))
      (W.primitive_primeExtension_factorization (n + j))
    simpa only [base, uNat, phase, Circle.coe_mul,
      Section4CharacterData.primitiveAssignmentData,
      witnessAssignmentData, WitnessAssignmentData.correction] using hf
  · intro n hn
    exact norm_primeExtension_archimedeanPrimeAssignment W.t <|
      (pow_pos (pow_pos (by omega : 0 < 4) S.K) 2).trans_le (hcenters n hn)
  · intro n hn L hL j hj
    exact (norm_primeExtension_coe W.primitiveModifiedAssignment (n + j)).le
  · intro n hn L hL j hj
    have hnj0 : n + j ≠ 0 := by
      have hnpos : 0 < n :=
        (pow_pos (pow_pos (by omega : 0 < 4) S.K) 2).trans_le (hcenters n hn)
      omega
    exact (W.primitiveCorrectionHom_hasUnitNorm hnj0).le
  · intro n hn L hL j hj
    apply W.norm_arch_phase_sub_le_phaseError (hcenters n hn)
    exact (Finset.mem_Icc.mp hj).2.trans (Finset.mem_Ioc.mp hL).2
  · intro a ha n hn m hm
    apply W.primitiveModified_periodic_on_cyclicGood ha
    · exact (mem_zmodResidueFiber.mp hn).2
    · exact hm
  · exact hfiber
  · exact hlowSq
  · exact htail

/-- Exact `hconvolution` endpoint consumed by
`primitive_contradiction_of_shiftedConvolution_all`. -/
theorem Section4CharacterData.primitive_hconvolution_of_selectedEnergy
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    (centers : Finset ℕ) (weight : ℕ → ℝ)
    (Bsel Wmass M TailHigh LowSq Kbound : ℝ) (Main : ℂ)
    {sigma : ℝ} (hsigma : 1 < sigma)
    (hM : 0 ≤ M) (hTailHigh : 0 ≤ TailHigh)
    (low : ZMod (W.primitiveQ ^ S.k) → ℝ)
    (hlow : ∀ a ∈ cyclicGoodResidues W.primitiveQ S.k S.H, 0 ≤ low a)
    (hweight : ∀ n ∈ centers, 0 ≤ weight n)
    (hweightSum : ∑ n ∈ centers, weight n = Wmass)
    (hcenters : ∀ n ∈ centers, (4 ^ S.K) ^ 2 ≤ n)
    (hselected : compactMediumWeightedLocalEnergy centers weight S.H S.sample ≤
      Bsel * Wmass)
    (hfiber : ∀ a ∈ cyclicGoodResidues W.primitiveQ S.k S.H,
      ∑ n ∈ zmodResidueFiber centers a, weight n ≤ M)
    (hlowSq : ∑ a ∈ cyclicGoodResidues W.primitiveQ S.k S.H,
      (low a) ^ 2 ≤ LowSq)
    (htail : ∀ a ∈ cyclicGoodResidues W.primitiveQ S.k S.H,
      ∀ m ∈ Finset.Icc 1 (2 * S.H),
        ‖finiteShiftedResidueSeries centers weight W.primitiveCorrectionHom a m -
            shiftedResidueSeries W.primitiveCorrectionHom a m (sigma : ℂ)‖ ≤
          low a + TailHigh)
    (hbudget :
      4 * M * Bsel * Wmass * S.H +
          16 * M * (S.H : ℝ) ^ 3 * S.phaseError ^ 2 * Wmass +
          16 * (S.H : ℝ) ^ 3 * LowSq +
          16 * ((W.primitiveQ ^ S.k : ℕ) : ℝ) * (S.H : ℝ) ^ 3 *
            (TailHigh + 4 * S.H) ^ 2 ≤
        Kbound * ‖Main‖ ^ 2 * ((W.primitiveQ ^ S.k : ℕ) : ℝ) * S.H) :
    ∑ L ∈ Finset.Ioc S.H (2 * S.H),
        shiftedResidueConvolutionEnergy W.primitiveCorrectionHom (sigma : ℂ)
          W.primitiveModifiedResidueValue
          (cyclicGoodResidues W.primitiveQ S.k S.H) L ≤
      Kbound * ‖(Main : ℂ)‖ ^ 2 *
        ((W.primitiveQ ^ S.k : ℕ) : ℝ) * S.H := by
  refine (W.primitive_shiftedResidueConvolutionEnergy_le_of_selectedEnergy
    centers weight Bsel Wmass M TailHigh LowSq hsigma hM hTailHigh low hlow
      hweight hweightSum hcenters hselected hfiber hlowSq htail).trans ?_
  exact hbudget

/-- One-call endpoint from the selected weighted local energy to the final
same-scale Euler/BCC contradiction.  In particular, the correction factor,
the Euler main term, and all residue-series estimates come from the same
`TaoTransferReady` certificate at `X`; no asymptotic estimate is silently
changed to a different scale. -/
theorem Section4CharacterData.primitive_contradiction_of_taoTransferReady_of_selectedEnergy
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    {X : ℕ} {D eta : ℝ}
    (P : EulerResidueBounds.TaoTransferReady W.primitiveCorrectionHom
      W.primitiveQ S.k X D eta)
    (centers : Finset ℕ) (weight : ℕ → ℝ)
    (Bsel Wmass M TailHigh LowSq Kbound J : ℝ)
    (hM : 0 ≤ M) (hTailHigh : 0 ≤ TailHigh)
    (low : ZMod (W.primitiveQ ^ S.k) → ℝ)
    (hlow : ∀ a ∈ cyclicGoodResidues W.primitiveQ S.k S.H, 0 ≤ low a)
    (hweight : ∀ n ∈ centers, 0 ≤ weight n)
    (hweightSum : ∑ n ∈ centers, weight n = Wmass)
    (hcenters : ∀ n ∈ centers, (4 ^ S.K) ^ 2 ≤ n)
    (hselected : compactMediumWeightedLocalEnergy centers weight S.H S.sample ≤
      Bsel * Wmass)
    (hfiber : ∀ a ∈ cyclicGoodResidues W.primitiveQ S.k S.H,
      ∑ n ∈ zmodResidueFiber centers a, weight n ≤ M)
    (hlowSq : ∑ a ∈ cyclicGoodResidues W.primitiveQ S.k S.H,
      (low a) ^ 2 ≤ LowSq)
    (htail : ∀ a ∈ cyclicGoodResidues W.primitiveQ S.k S.H,
      ∀ m ∈ Finset.Icc 1 (2 * S.H),
        ‖finiteShiftedResidueSeries centers weight W.primitiveCorrectionHom a m -
            shiftedResidueSeries W.primitiveCorrectionHom a m
              (EulerResidue.taoExponent X : ℂ)‖ ≤ low a + TailHigh)
    (hconvolutionBudget :
      4 * M * Bsel * Wmass * S.H +
          16 * M * (S.H : ℝ) ^ 3 * S.phaseError ^ 2 * Wmass +
          16 * (S.H : ℝ) ^ 3 * LowSq +
          16 * ((W.primitiveQ ^ S.k : ℕ) : ℝ) * (S.H : ℝ) ^ 3 *
            (TailHigh + 4 * S.H) ^ 2 ≤
        Kbound *
          ‖EulerResidue.singularSeries W.primitiveCorrectionHom X /
            ((W.primitiveQ ^ S.k : ℕ) : ℂ)‖ ^ 2 *
          ((W.primitiveQ ^ S.k : ℕ) : ℝ) * S.H)
    (hsmall : 4 * (S.H : ℝ) ^ 2 * eta ^ 2 ≤ J)
    (hbudget : 2 * Kbound + 2 * J ≤ S.B) : False := by
  have hX : 1 < X := lt_of_lt_of_le one_lt_two P.two_le
  have hconvolution := W.primitive_hconvolution_of_selectedEnergy
    centers weight Bsel Wmass M TailHigh LowSq Kbound
      (EulerResidue.singularSeries W.primitiveCorrectionHom X /
        ((W.primitiveQ ^ S.k : ℕ) : ℂ))
      (EulerResidue.one_lt_taoExponent hX) hM hTailHigh low hlow hweight
      hweightSum hcenters hselected hfiber hlowSq htail hconvolutionBudget
  exact W.primitive_contradiction_of_taoTransferReady
    P hconvolution hsmall hbudget

/-! ## Bundling the Markov certificate with the two-scale sample -/

/-- A finite weighted window selected only after the prefix length and the
last dyadic scale are known. -/
structure Section4WeightWindow (H Y : ℕ) where
  centers : Finset ℕ
  weight : ℕ → ℝ
  mass : ℝ
  mass_pos : 0 < mass
  weight_nonneg : ∀ n ∈ centers, 0 ≤ weight n
  weight_sum : ∑ n ∈ centers, weight n = mass
  center_lower : ∀ n ∈ centers, Y ^ 2 ≤ n

/-- Intersect a *specified two-scale nearby event* with the weighted Markov
event and store both certificates on the resulting `Section4Selection`.
The complement budget visibly has three contributions in the intended use:
two pretentious events inside `delta`, and this theorem's final Markov term.
-/
theorem exists_weightedSection4Selection_of_nearbySet
    (mu : ProbabilityMeasure CompactCircleCharacter) (C : ℝ)
    (hbound : ∀ m : ℕ, compactMeanSquarePartialSum mu m ≤ C ^ 2)
    {A K : ℕ} {Bccb : ℝ} (P : Section4BCCParameters A Bccb)
    (hA : 2 ≤ A) (hK : 0 < K) (hAK : A ≤ 2 ^ K)
    (G : Set CompactCircleCharacter) (delta : ℝ≥0∞)
    (hG : (mu : Measure CompactCircleCharacter) Gᶜ ≤ delta)
    (hnear : ∀ g ∈ G, HasNearbyTwoScalePretentiousPair A (4 ^ K) P.D g)
    (V : Section4WeightWindow P.H (4 ^ K))
    (Bmarkov : ℝ) (hBmarkov : 0 < Bmarkov)
    (hthree : delta + ENNReal.ofReal (4 * C ^ 2 / Bmarkov) < 1) :
    ∃ S : Section4Selection C,
      S.A = A ∧ S.K = K ∧ S.B = Bccb ∧ HEq S.params P ∧
      S.sample ∈ G ∧
      compactMediumWeightedLocalEnergy V.centers V.weight S.H S.sample <
        Bmarkov * V.mass := by
  obtain ⟨g, hgG, hgEnergy⟩ :=
    exists_mem_and_compactMediumWeightedLocalEnergy_lt
      mu C Bmarkov V.mass hBmarkov V.mass_pos hbound
      V.centers V.weight P.H_pos V.weight_nonneg V.weight_sum
      G delta hG hthree
  let S : Section4Selection C := {
    A := A
    K := K
    B := Bccb
    params := P
    sample := g
    two_le_A := hA
    K_pos := hK
    A_le_two_pow_K := hAK
    nearby := hnear g hgG
  }
  refine ⟨S, rfl, rfl, rfl, HEq.rfl, hgG, ?_⟩
  exact hgEnergy

end

end Erdos67
