/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedSourcePrimeCount

/-!
# Exact expansion of the pinned source weight over auxiliary primes

The squared divisor sum is expanded before prime counting. Every raw
quadruple and every profile cross term remains in this finite identity.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def PinnedIntegerSingleCondition {K : ℕ} (h : Fin K) (w m p₀ q : ℕ)
    (d e : PinnedShiftIndex h → ℕ) : Prop :=
  ∀ i, (d i : ℤ) ∣ pinnedFirstIntegerForm h w p₀ q i ∧
    (e i : ℤ) ∣ (m : ℤ) * pinnedFirstIntegerForm h w p₀ q i - 1

theorem natCast_lcm_dvd_int_iff (a b : ℕ) (n : ℤ) :
    ((Nat.lcm a b : ℕ) : ℤ) ∣ n ↔ (a : ℤ) ∣ n ∧ (b : ℤ) ∣ n := by
  simp only [Int.natCast_dvd]
  exact ⟨fun h ↦ ⟨(Nat.dvd_lcm_left _ _).trans h, (Nat.dvd_lcm_right _ _).trans h⟩,
    fun h ↦ Nat.lcm_dvd h.1 h.2⟩

theorem pinnedIntegerDivisorCondition_pack_iff
    {K : ℕ} (h : Fin K) (w m p₀ q : ℕ)
    (d e d' e' : PinnedShiftIndex h → ℕ) :
    PinnedIntegerDivisorCondition h w m p₀ q
        (fourDivisorPackEquiv (PinnedShiftIndex h) (d, e, d', e')) ↔
      PinnedIntegerSingleCondition h w m p₀ q d e ∧
        PinnedIntegerSingleCondition h w m p₀ q d' e' := by
  simp only [PinnedIntegerDivisorCondition, PinnedIntegerSingleCondition,
    fourDivisorPackEquiv, Equiv.coe_fn_mk, natCast_lcm_dvd_int_iff]
  constructor
  · intro hs
    exact ⟨fun i ↦ ⟨(hs i).1.1, (hs i).2.1⟩, fun i ↦ ⟨(hs i).1.2, (hs i).2.2⟩⟩
  · rintro ⟨ha, hb⟩ i
    exact ⟨⟨(ha i).1, (hb i).1⟩, ⟨(ha i).2, (hb i).2⟩⟩

open Classical in
def pinnedSourceIntegerWeight {K : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K)
    (P : Finset ℕ) (w m p₀ q : ℕ) (LD LE : ℝ) : ℂ :=
  (∑ d ∈ cutoffDivisorTupleSupport (PinnedShiftIndex h) P,
    ∑ e ∈ cutoffDivisorTupleSupport (PinnedShiftIndex h) P,
      if PinnedIntegerSingleCondition h w m p₀ q d e then
        pinnedSourceSelbergCoefficient S F G h LD LE d e else 0) ^ 2

open Classical in
theorem pinnedSourceIntegerWeight_eq_raw_sum
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (w m p₀ q : ℕ) (LD LE : ℝ) :
    pinnedSourceIntegerWeight S F G h P w m p₀ q LD LE =
      ∑ d ∈ rawDoubledCutoffDivisorTuples (PinnedShiftIndex h) P,
        if PinnedIntegerDivisorCondition h w m p₀ q d then
          pinnedSourceFlatCoefficient S F G h LD LE (fun i ↦ d i false) *
            pinnedSourceFlatCoefficient S F G h LD LE (fun i ↦ d i true) else 0 := by
  rw [sum_rawDoubledCutoffDivisorTuples P hP]
  unfold pinnedSourceIntegerWeight
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d' hd'
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e' he'
  rw [pinnedIntegerDivisorCondition_pack_iff]
  simp only [pinnedSourceFlatCoefficient, fourDivisorPackEquiv, Equiv.coe_fn_mk]
  split_ifs <;> simp_all

theorem sum_pinnedSourceIntegerWeight_eq_primeDivisorSum
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (w m p₀ A B : ℕ) (LD LE : ℝ) :
    (∑ q ∈ auxiliaryPrimeInterval A B, pinnedSourceIntegerWeight S F G h P w m p₀ q LD LE) =
      pinnedSourcePrimeDivisorSum S F G h P w m p₀ A B LD LE := by
  classical
  simp_rw [pinnedSourceIntegerWeight_eq_raw_sum S F G h P hP]
  rw [Finset.sum_comm]
  unfold pinnedSourcePrimeDivisorSum
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, pinnedIntegerDivisorPrimeCount]
  ring

end

end Erdos4b
