/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.KloostermanOrthogonality

/-!
# Weyl differencing for reciprocal additive phases

This file records the exact phase after any finite list of positive-shift
correlations.  It is independent of the later analytic estimate for the
resulting rational-function character sum.
-/

namespace Erdos387

open scoped BigOperators ComplexConjugate

namespace InverseWeyl

/-- A reciprocal additive-character sequence sampled on a natural interval. -/
noncomputable def inversePhaseSequence
    (q : ℕ) [NeZero q] (c a : ZMod q) (x : ℕ) : ℂ :=
  ZMod.stdAddChar (c * (a + (x : ZMod q))⁻¹)

theorem norm_inversePhaseSequence
    (q : ℕ) [NeZero q] (c a : ZMod q) (x : ℕ) :
    ‖inversePhaseSequence q c a x‖ = 1 := by
  unfold inversePhaseSequence
  exact AddChar.norm_apply _ _

/-- Correlation with the translate by the positive shift `h+1`. -/
def positiveShiftCorrelation
    (z : ℕ → ℂ) (h x : ℕ) : ℂ :=
  z (x + h + 1) * conj (z x)

/-- Iterate positive-shift correlation through a list of zero-based shifts. -/
def iteratedPositiveShiftCorrelation
    (z : ℕ → ℂ) : List ℕ → ℕ → ℂ
  | [], x => z x
  | h :: hs, x =>
      positiveShiftCorrelation
        (iteratedPositiveShiftCorrelation z hs) h x

/-- The corresponding recursively differenced reciprocal phase. -/
noncomputable def iteratedInversePhase
    (q : ℕ) [NeZero q] (c a : ZMod q) : List ℕ → ℕ → ZMod q
  | [], x => c * (a + (x : ZMod q))⁻¹
  | h :: hs, x =>
      iteratedInversePhase q c a hs (x + h + 1) -
        iteratedInversePhase q c a hs x

/-- Every iterated correlation is exactly the standard additive character
of the recursively differenced rational phase. -/
theorem iteratedPositiveShiftCorrelation_inversePhaseSequence
    (q : ℕ) [NeZero q] (c a : ZMod q) (hs : List ℕ) (x : ℕ) :
    iteratedPositiveShiftCorrelation (inversePhaseSequence q c a) hs x =
      ZMod.stdAddChar (iteratedInversePhase q c a hs x) := by
  induction hs generalizing x with
  | nil => rfl
  | cons h hs ih =>
      unfold iteratedPositiveShiftCorrelation positiveShiftCorrelation
      rw [ih, ih, ← AddChar.map_neg_eq_conj,
        ← AddChar.map_add_eq_mul]
      simp only [iteratedInversePhase, sub_eq_add_neg]

/-- One reciprocal differencing step, in explicit form. -/
theorem iteratedInversePhase_singleton
    (q : ℕ) [NeZero q] (c a : ZMod q) (h x : ℕ) :
    iteratedInversePhase q c a [h] x =
      c * (a + ((x + h + 1 : ℕ) : ZMod q))⁻¹ -
        c * (a + (x : ZMod q))⁻¹ := rfl

/-- Two reciprocal differencing steps, retaining all four vertices of the
shift parallelogram. -/
theorem iteratedInversePhase_pair
    (q : ℕ) [NeZero q] (c a : ZMod q) (h₁ h₂ x : ℕ) :
    iteratedInversePhase q c a [h₁, h₂] x =
      (c * (a + ((x + h₁ + 1 + h₂ + 1 : ℕ) : ZMod q))⁻¹ -
        c * (a + ((x + h₁ + 1 : ℕ) : ZMod q))⁻¹) -
      (c * (a + ((x + h₂ + 1 : ℕ) : ZMod q))⁻¹ -
        c * (a + (x : ZMod q))⁻¹) := by
  rfl

/-- The iterated phase depends only on the base point modulo `q`. -/
theorem iteratedInversePhase_eq_of_modEq
    (q : ℕ) [NeZero q] (c a : ZMod q) (hs : List ℕ)
    {x y : ℕ} (hxy : Nat.ModEq q x y) :
    iteratedInversePhase q c a hs x =
      iteratedInversePhase q c a hs y := by
  induction hs generalizing x y with
  | nil =>
      simp only [iteratedInversePhase]
      have hcast : (x : ZMod q) = (y : ZMod q) := by
        rw [ZMod.natCast_eq_natCast_iff]
        exact hxy
      rw [hcast]
  | cons h hs ih =>
      simp only [iteratedInversePhase]
      have hshift : Nat.ModEq q (x + h + 1) (y + h + 1) := by
        exact hxy.add_right (h + 1)
      rw [ih hshift, ih hxy]

/-- A shift which vanishes modulo `q` produces an identically zero next
difference. -/
theorem iteratedInversePhase_cons_eq_zero_of_dvd_shift
    (q : ℕ) [NeZero q] (c a : ZMod q) (h : ℕ)
    (hs : List ℕ) (hh : q ∣ h + 1) (x : ℕ) :
    iteratedInversePhase q c a (h :: hs) x = 0 := by
  unfold iteratedInversePhase
  have hcast : ((h + 1 : ℕ) : ZMod q) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact hh
  have hx : ((x + h + 1 : ℕ) : ZMod q) = (x : ZMod q) := by
    push_cast
    calc
      (x : ZMod q) + (h : ZMod q) + 1 =
          (x : ZMod q) + ((h + 1 : ℕ) : ZMod q) := by
        push_cast
        ring
      _ = (x : ZMod q) := by rw [hcast, add_zero]
  have harg : x + h + 1 ≡ x [MOD q] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    exact hx
  rw [iteratedInversePhase_eq_of_modEq q c a hs harg, sub_self]

/-- If any stored positive shift is zero modulo `q`, the full iterated phase
is identically zero. -/
theorem iteratedInversePhase_eq_zero_of_exists_dvd_shift
    (q : ℕ) [NeZero q] (c a : ZMod q) (hs : List ℕ)
    (hex : ∃ h ∈ hs, q ∣ h + 1) (x : ℕ) :
    iteratedInversePhase q c a hs x = 0 := by
  induction hs generalizing x with
  | nil => simp at hex
  | cons h hs ih =>
      rcases hex with ⟨j, hj, hjdvd⟩
      simp only [List.mem_cons] at hj
      rcases hj with rfl | hj
      · exact iteratedInversePhase_cons_eq_zero_of_dvd_shift
          q c a j hs hjdvd x
      · simp only [iteratedInversePhase,
          ih ⟨j, hj, hjdvd⟩ (x := x + h + 1),
          ih ⟨j, hj, hjdvd⟩ (x := x), sub_self]

/-- Iterated correlation preserves unit norm. -/
theorem norm_iteratedPositiveShiftCorrelation_eq_one
    (z : ℕ → ℂ) (hz : ∀ x, ‖z x‖ = 1)
    (hs : List ℕ) (x : ℕ) :
    ‖iteratedPositiveShiftCorrelation z hs x‖ = 1 := by
  induction hs generalizing x with
  | nil => exact hz x
  | cons h hs ih =>
      unfold iteratedPositiveShiftCorrelation positiveShiftCorrelation
      rw [norm_mul, Complex.norm_conj, ih, ih, one_mul]

end InverseWeyl

end Erdos387
