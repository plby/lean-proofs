/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RationalStepanovExtensionSum
import Mathlib.Algebra.Star.BigOperators

/-!
# Cyclic differencing after Fourier completion

A linear Fourier twist disappears after one cyclic difference.  This file
records the exact finite-group identity and combines it with the
unconditional two-pole rational Weil estimate.  The result is a
three-quarter-power type bound for a complete linearly twisted reciprocal
sum; no pointwise Kloosterman estimate is assumed.
-/

namespace Erdos387

open scoped BigOperators ComplexConjugate

namespace CyclicWeyl

/-- Reparameterize an ordered pair `(u,v)` by its difference and second
coordinate. -/
def differencePairEquiv (A : Type*) [AddGroup A] :
    (A × A) ≃ (A × A) where
  toFun q := (q.1 - q.2, q.2)
  invFun q := (q.1 + q.2, q.2)
  left_inv q := by ext <;> simp
  right_inv q := by ext <;> simp

/-- Exact cyclic autocorrelation expansion on a finite additive group. -/
theorem sum_mul_conj_sum_eq_cyclicCorrelation
    {A : Type*} [AddCommGroup A] [Fintype A]
    (z : A → ℂ) :
    (∑ x : A, z x) * conj (∑ x : A, z x) =
      ∑ h : A, ∑ x : A, z (h + x) * conj (z x) := by
  rw [map_sum, Finset.sum_mul_sum]
  calc
    (∑ i : A, ∑ j : A, z i * conj (z j)) =
        ∑ j : A, ∑ i : A, z i * conj (z j) := Finset.sum_comm
    _ = ∑ x : A, ∑ h : A, z (h + x) * conj (z x) := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact (Fintype.sum_equiv (Equiv.addRight x)
        (fun h : A => z (h + x) * conj (z x))
        (fun i : A => z i * conj (z x)) (fun _h => rfl)).symm
    _ = ∑ h : A, ∑ x : A, z (h + x) * conj (z x) := Finset.sum_comm

/-- Triangle inequality after the exact cyclic autocorrelation expansion. -/
theorem norm_sum_sq_le_sum_norm_cyclicCorrelation
    {A : Type*} [AddCommGroup A] [Fintype A]
    (z : A → ℂ) :
    ‖∑ x : A, z x‖ ^ 2 ≤
      ∑ h : A, ‖∑ x : A, z (h + x) * conj (z x)‖ := by
  have hid := sum_mul_conj_sum_eq_cyclicCorrelation z
  calc
    ‖∑ x : A, z x‖ ^ 2 =
        ‖(∑ x : A, z x) * conj (∑ x : A, z x)‖ := by
      rw [norm_mul, Complex.norm_conj, pow_two]
    _ = ‖∑ h : A, ∑ x : A, z (h + x) * conj (z x)‖ :=
      congrArg norm hid
    _ ≤ ∑ h : A, ‖∑ x : A, z (h + x) * conj (z x)‖ :=
      norm_sum_le _ _

/-- A complete reciprocal phase with an arbitrary linear Fourier twist. -/
noncomputable def twistedInversePhase
    (p : ℕ) [NeZero p] (c a b x : ZMod p) : ℂ :=
  ZMod.stdAddChar (b * x + c * (a + x)⁻¹)

theorem norm_twistedInversePhase (p : ℕ) [NeZero p]
    (c a b x : ZMod p) :
    ‖twistedInversePhase p c a b x‖ = 1 := by
  exact AddChar.norm_apply _ _

/-- A cyclic correlation is a constant linear character times the
two-translate rational phase. -/
theorem twistedInversePhase_correlation
    {p : ℕ} [NeZero p] (c a b h x : ZMod p) :
    twistedInversePhase p c a b (h + x) *
        conj (twistedInversePhase p c a b x) =
      ZMod.stdAddChar (b * h) *
        ZMod.stdAddChar
          (InverseRational.simplePolePhase
            (InverseRational.iteratedDifferenceCoefficient
              (InverseRational.singlePoleCoefficient c (-a)) [(h, 0)]) x) := by
  unfold twistedInversePhase
  rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul,
    ← AddChar.map_add_eq_mul]
  congr 1
  rw [InverseRational.simplePolePhase_iteratedDifferenceCoefficient]
  simp only [InverseRational.iteratedTranslateDifference, sub_eq_add_neg]
  rw [InverseRational.simplePolePhase_singlePoleCoefficient_neg,
    InverseRational.simplePolePhase_singlePoleCoefficient_neg]
  rw [show a + (h + x) = a + (x + h) by ring]
  simp only [add_zero]
  ring

/-- Every nonzero cyclic shift has a two-pole square-root correlation
bound. -/
theorem norm_correlation_le
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (hp : 2 < p) {c : ZMod p} (hc : c ≠ 0) (a b : ZMod p)
    {h : ZMod p} (hh : h ≠ 0) :
    ‖∑ x : ZMod p,
        twistedInversePhase p c a b (h + x) *
          conj (twistedInversePhase p c a b x)‖ ≤
      (3 : ℝ) * Real.sqrt (p : ℝ) + 2 := by
  let coeff := InverseRational.iteratedDifferenceCoefficient
    (InverseRational.singlePoleCoefficient c (-a)) [(h, 0)]
  have hne : (InverseRational.poleSupport coeff).Nonempty := by
    apply InverseRational.singlePole_iteratedDifference_nonempty hc
    · intro t ht
      simp only [List.mem_singleton] at ht
      subst t
      simpa using hh
    · simpa using hp
  have hcard : (InverseRational.poleSupport coeff).card ≤ 2 := by
    calc
      (InverseRational.poleSupport coeff).card ≤
          2 ^ ([(h, 0)] : List (ZMod p × ZMod p)).length *
            (InverseRational.poleSupport
              (InverseRational.singlePoleCoefficient c (-a))).card :=
        InverseRational.card_poleSupport_iteratedDifferenceCoefficient_le
          _ _
      _ = 2 := by
        rw [InverseRational.poleSupport_singlePoleCoefficient
          (pole := -a) hc]
        simp
  have hcardp : (InverseRational.poleSupport coeff).card < p :=
    hcard.trans_lt hp
  have hweil := RationalStepanov.norm_simplePolePhase_sum_le
    (by omega : 1 < p) coeff hne hcardp
  rw [show (∑ x : ZMod p,
      twistedInversePhase p c a b (h + x) *
        conj (twistedInversePhase p c a b x)) =
      ZMod.stdAddChar (b * h) *
        ∑ x : ZMod p,
          ZMod.stdAddChar (InverseRational.simplePolePhase coeff x) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    exact twistedInversePhase_correlation c a b h x,
    norm_mul, AddChar.norm_apply, one_mul]
  calc
    ‖∑ x : ZMod p,
        ZMod.stdAddChar (InverseRational.simplePolePhase coeff x)‖ ≤
        ((2 * (InverseRational.poleSupport coeff).card - 1 : ℕ) : ℝ) *
          Real.sqrt (p : ℝ) +
        (InverseRational.poleSupport coeff).card := hweil
    _ ≤ (3 : ℝ) * Real.sqrt (p : ℝ) + 2 := by
      have hcond : 2 * (InverseRational.poleSupport coeff).card - 1 ≤ 3 :=
        by omega
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcond)
          (Real.sqrt_nonneg _)
      · exact_mod_cast hcard

/-- One cyclic differencing step bounds every complete linearly twisted
reciprocal sum. -/
theorem norm_sum_twistedInversePhase_sq_le
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (hp : 2 < p) {c : ZMod p} (hc : c ≠ 0) (a b : ZMod p) :
    ‖∑ x : ZMod p, twistedInversePhase p c a b x‖ ^ 2 ≤
      (p : ℝ) + (p - 1 : ℕ) *
        ((3 : ℝ) * Real.sqrt (p : ℝ) + 2) := by
  let z : ZMod p → ℂ := twistedInversePhase p c a b
  have hcyclic := norm_sum_sq_le_sum_norm_cyclicCorrelation z
  calc
    ‖∑ x : ZMod p, twistedInversePhase p c a b x‖ ^ 2 ≤
        ∑ h : ZMod p,
          ‖∑ x : ZMod p, z (h + x) * conj (z x)‖ := hcyclic
    _ = ‖∑ x : ZMod p, z (0 + x) * conj (z x)‖ +
        ∑ h ∈ (Finset.univ : Finset (ZMod p)).erase 0,
          ‖∑ x : ZMod p, z (h + x) * conj (z x)‖ := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p))]
    _ ≤ (p : ℝ) +
        ∑ _h ∈ (Finset.univ : Finset (ZMod p)).erase 0,
          ((3 : ℝ) * Real.sqrt (p : ℝ) + 2) := by
      apply add_le_add
      · have hzero :
            (∑ x : ZMod p, z (0 + x) * conj (z x)) = (p : ℂ) := by
          calc
            (∑ x : ZMod p, z (0 + x) * conj (z x)) =
                ∑ _x : ZMod p, (1 : ℂ) := by
              apply Finset.sum_congr rfl
              intro x _hx
              simp only [zero_add]
              rw [Complex.mul_conj', norm_twistedInversePhase]
              norm_num
            _ = (p : ℂ) := by simp
        rw [hzero, Complex.norm_natCast]
      · apply Finset.sum_le_sum
        intro h hh
        exact norm_correlation_le hp hc a b
          (Finset.ne_of_mem_erase hh)
    _ = (p : ℝ) + (p - 1 : ℕ) *
        ((3 : ℝ) * Real.sqrt (p : ℝ) + 2) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 2
      rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p)),
        Finset.card_univ, ZMod.card]

end CyclicWeyl

end Erdos387
