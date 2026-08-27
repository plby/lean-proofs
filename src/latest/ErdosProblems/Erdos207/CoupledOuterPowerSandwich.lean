/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CoupledOuterScaleCrossmul

/-!
# Power-window sandwiches for the coupled outer corridor

The normalized inverse-power window starts at the fine offset.  If the
initial and current eligible-pair clocks differ by at most a factor `c`, its
growth is at most `c^k`.  Comparable elementary bounds trap the quadratic
centre between `N/(4c²)` and `4N`.
-/

namespace Erdos207

noncomputable section

/-- The four analytic sandwiches used by the final scale certificate. -/
theorem coupledOuter_power_sandwich
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (outside t k i : ℕ) (c : ℝ)
    (houtside : 0 < outside)
    (hc : 0 ≤ c)
    (hE : 0 < outerSharpEligiblePairs H X i)
    (hE_le : outerSharpEligiblePairs H X i ≤
      outerSharpEligiblePairs H X 0)
    (hcompare : (outerSharpEligiblePairs H X 0 : ℝ) ≤
      c * outerSharpEligiblePairs H X i)
    (hlowerClock : (outside : ℝ) ^ 2 ≤
      4 * c * outerSharpEligiblePairs H X i)
    (hupperClock : (outerSharpEligiblePairs H X i : ℝ) ≤
      (outside : ℝ) ^ 2) :
    let A := fineOuterInitialOffset outside t *
      (outerSharpEligiblePairs H X 0 : ℝ) ^ k
    fineOuterInitialOffset outside t ≤
        outerCoupledWindow H X A k i ∧
      outerCoupledWindow H X A k i ≤
        fineOuterInitialOffset outside t * c ^ k ∧
      (outside : ℝ) / (4 * c ^ 2) ≤
        outerCoupledCenter H X outside i ∧
      outerCoupledCenter H X outside i ≤ 4 * outside := by
  dsimp only
  let E0 : ℝ := outerSharpEligiblePairs H X 0
  let E : ℝ := outerSharpEligiblePairs H X i
  let N : ℝ := outside
  let offset : ℝ := fineOuterInitialOffset outside t
  have hEpos : 0 < E := by
    dsimp only [E]
    exact_mod_cast hE
  have hE0pos : 0 < E0 := by
    apply hEpos.trans_le
    dsimp only [E, E0]
    exact_mod_cast hE_le
  have hNpos : 0 < N := by
    dsimp only [N]
    exact_mod_cast houtside
  have hoffset : 0 ≤ offset := by
    dsimp only [offset, fineOuterInitialOffset]
    positivity
  have hEreal : E ≤ E0 := by
    dsimp only [E, E0]
    exact_mod_cast hE_le
  have hpowLower : E ^ k ≤ E0 ^ k :=
    pow_le_pow_left₀ hEpos.le hEreal k
  have hpowUpper : E0 ^ k ≤ c ^ k * E ^ k := by
    calc
      E0 ^ k ≤ (c * E) ^ k := pow_le_pow_left₀ hE0pos.le (by
        simpa only [E0, E] using hcompare) k
      _ = c ^ k * E ^ k := mul_pow c E k
  have hwindowLower : offset ≤
      coupledOuterWindow (offset * E0 ^ k) k E := by
    unfold coupledOuterWindow
    apply (le_div_iff₀ (pow_pos hEpos k)).2
    exact mul_le_mul_of_nonneg_left hpowLower hoffset
  have hwindowUpper : coupledOuterWindow (offset * E0 ^ k) k E ≤
      offset * c ^ k := by
    unfold coupledOuterWindow
    apply (div_le_iff₀ (pow_pos hEpos k)).2
    calc
      offset * E0 ^ k ≤ offset * (c ^ k * E ^ k) := by gcongr
      _ = offset * c ^ k * E ^ k := by ring
  have hNsq : N ^ 4 ≤ 16 * c ^ 2 * E ^ 2 := by
    have hsquare := mul_self_le_mul_self (sq_nonneg N)
      (by simpa only [N, E] using hlowerClock)
    nlinarith
  have hcenterLower : N / (4 * c ^ 2) ≤ coupledOuterCenter N E := by
    unfold coupledOuterCenter
    by_cases hc0 : c = 0
    · subst c
      norm_num at hlowerClock
      nlinarith
    · field_simp
      nlinarith
  have hEsq : E ^ 2 ≤ N ^ 4 := by
    have hsquare := mul_self_le_mul_self hEpos.le
      (by simpa only [E, N] using hupperClock)
    nlinarith
  have hcenterUpper : coupledOuterCenter N E ≤ 4 * N := by
    unfold coupledOuterCenter
    field_simp
    nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [outerCoupledWindow, E0, E, offset] using hwindowLower
  · simpa only [outerCoupledWindow, E0, E, offset] using hwindowUpper
  · simpa only [outerCoupledCenter, E, N] using hcenterLower
  · simpa only [outerCoupledCenter, E, N] using hcenterUpper

/-- Complete scale facts from clock comparability and six explicit scalar
inequalities.  These inequalities involve only the initial offset, the
outside order, the comparison factor, and the aggregate cutoff. -/
theorem coupledOuterScaleFacts_of_power
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (outside t K k i : ℕ)
    (buffer c : ℝ)
    (houtside : 0 < outside)
    (hc : 0 < c)
    (hE : 0 < outerSharpEligiblePairs H X i)
    (hE_le : outerSharpEligiblePairs H X i ≤
      outerSharpEligiblePairs H X 0)
    (hcompare : (outerSharpEligiblePairs H X 0 : ℝ) ≤
      c * outerSharpEligiblePairs H X i)
    (hlowerClock : (outside : ℝ) ^ 2 ≤
      4 * c * outerSharpEligiblePairs H X i)
    (hupperClock : (outerSharpEligiblePairs H X i : ℝ) ≤
      (outside : ℝ) ^ 2)
    (hsmall : 100 * (fineOuterInitialOffset outside t * c ^ k) ≤
      (outside : ℝ) / (4 * c ^ 2))
    (hroundBuffer : buffer + 1 ≤ fineOuterInitialOffset outside t)
    (hroundTwo : 2 ≤ fineOuterInitialOffset outside t)
    (hlowerOne : 1 + buffer +
        fineOuterInitialOffset outside t * c ^ k ≤
      (outside : ℝ) / (4 * c ^ 2))
    (hclock : 100 * (4 * outside : ℝ) ≤
      fineOuterInitialOffset outside t * outerSharpEligiblePairs H X i)
    (haggregate : (K : ℝ) ≤ fineOuterInitialOffset outside t *
      ((outside : ℝ) / (4 * c ^ 2))) :
    let A := fineOuterInitialOffset outside t *
      (outerSharpEligiblePairs H X 0 : ℝ) ^ k
    CoupledOuterScaleFacts H X outside K A k i buffer
      (outerCoupledWindow H X A k i /
        outerCoupledCenter H X outside i) := by
  dsimp only
  let A := fineOuterInitialOffset outside t *
    (outerSharpEligiblePairs H X 0 : ℝ) ^ k
  have hs := coupledOuter_power_sandwich H X outside t k i c
    houtside hc.le hE hE_le hcompare hlowerClock hupperClock
  have hA : 0 ≤ A := by
    dsimp only [A, fineOuterInitialOffset]
    positivity
  apply coupledOuterScaleFacts_of_sandwich H X outside K A k i buffer
    (fineOuterInitialOffset outside t)
    (fineOuterInitialOffset outside t * c ^ k)
    ((outside : ℝ) / (4 * c ^ 2)) (4 * outside : ℝ)
    hA (by positivity)
  · simpa only [A] using hs.1
  · simpa only [A] using hs.2.1
  · simpa only [A] using hs.2.2.1
  · simpa only [A] using hs.2.2.2
  · exact hsmall
  · exact hroundBuffer
  · exact hroundTwo
  · exact hlowerOne
  · exact hclock
  · exact haggregate

end

end Erdos207
