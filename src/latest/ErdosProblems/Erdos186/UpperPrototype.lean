import ErdosProblems.Erdos186.Foundations

/-!
# Erdős Problem 186: upper-bound prototype

This file isolates the exact finite statement needed from the
Pham--Zakharov theorem and proves that it is equivalent to the desired
asymptotic upper bound for the extremal function `F`.

No part of the deep additive-combinatorial estimate is assumed as a global
declaration: it occurs only as an explicit hypothesis of the transfer theorems.
The final section proves the elementary exponent-one bound, recording the
point beyond which genuinely new mathematics is needed.
-/

namespace Erdos186

open Filter Finset
open scoped Topology

noncomputable section

/-- The real-valued extremal function. -/
def growth (N : ℕ) : ℝ := F N

/-- The comparison function `N ^ (1/4 + ε)`. -/
def upperScale (ε : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ ((1 / 4 : ℝ) + ε)

/-- The uniform finite form of the one-dimensional Pham--Zakharov theorem.

This formulation is deliberately over *every* admissible finite set, rather
than just the extremal function.  It is the direct specialization of the box
theorem to the integer interval `[1,N]`.
-/
def UniformFiniteUpperBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Finset ℕ,
      Admissible N A → (A.card : ℝ) ≤ C * upperScale ε N

/-- The eventual pointwise form of the upper estimate for `F`. -/
def EventualExtremalUpperBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N in atTop,
      growth N ≤ C * upperScale ε N

/-- The conventional `N^(1/4+o(1))` upper statement, written as one
big-`O` estimate for every positive exponent loss. -/
def AsymptoticUpperBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    growth =O[atTop] upperScale ε

/-- The coefficient-one finite form which is the literal one-dimensional
specialization of the Pham--Zakharov box theorem. -/
def CoefficientOneFiniteUpperBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Finset ℕ,
      Admissible N A → (A.card : ℝ) ≤ upperScale ε N

/-- The coefficient-one eventual form for the extremal function. -/
def CoefficientOneExtremalUpperBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in atTop, growth N ≤ upperScale ε N

/-- A uniform estimate for all admissible sets applies to a maximizer. -/
theorem eventualExtremalUpperBound_of_uniformFiniteUpperBound
    (h : UniformFiniteUpperBound) : EventualExtremalUpperBound := by
  intro ε hε
  obtain ⟨C, hC, N₀, hbound⟩ := h ε hε
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop N₀] with N hN
  obtain ⟨A, hA, hcard⟩ := exists_extremizer N
  simpa [growth, hcard] using hbound N hN A hA

/-- An eventual estimate for the maximum bounds every admissible set. -/
theorem uniformFiniteUpperBound_of_eventualExtremalUpperBound
    (h : EventualExtremalUpperBound) : UniformFiniteUpperBound := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := h ε hε
  rw [eventually_atTop] at hbound
  obtain ⟨N₀, hN₀⟩ := hbound
  refine ⟨C, hC, N₀, ?_⟩
  intro N hN A hA
  calc
    (A.card : ℝ) ≤ growth N := by
      change (A.card : ℝ) ≤ (F N : ℝ)
      exact_mod_cast card_le_F hA
    _ ≤ C * upperScale ε N := hN₀ N hN

theorem uniformFiniteUpperBound_iff_eventualExtremalUpperBound :
    UniformFiniteUpperBound ↔ EventualExtremalUpperBound :=
  ⟨eventualExtremalUpperBound_of_uniformFiniteUpperBound,
    uniformFiniteUpperBound_of_eventualExtremalUpperBound⟩

/-- The eventual pointwise form implies the standard big-`O` form. -/
theorem asymptoticUpperBound_of_eventualExtremalUpperBound
    (h : EventualExtremalUpperBound) : AsymptoticUpperBound := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := h ε hε
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [hbound] with N hN
  simpa only [growth, upperScale, Real.norm_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ (F N : ℝ) by positivity),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)] using hN

/-- The big-`O` form yields an eventual pointwise estimate with a positive
constant.  Nonnegativity removes the norms in the definition of big-`O`.
-/
theorem eventualExtremalUpperBound_of_asymptoticUpperBound
    (h : AsymptoticUpperBound) : EventualExtremalUpperBound := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := (h ε hε).exists_pos
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound.bound] with N hN
  simpa only [growth, upperScale, Real.norm_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ (F N : ℝ) by positivity),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)] using hN

theorem eventualExtremalUpperBound_iff_asymptoticUpperBound :
    EventualExtremalUpperBound ↔ AsymptoticUpperBound :=
  ⟨asymptoticUpperBound_of_eventualExtremalUpperBound,
    eventualExtremalUpperBound_of_asymptoticUpperBound⟩

/-- Exact transfer statement: proving the one-dimensional
Pham--Zakharov finite theorem is equivalent to proving the requested
asymptotic upper bound for the literal extremal function `F`.
-/
theorem uniformFiniteUpperBound_iff_asymptoticUpperBound :
    UniformFiniteUpperBound ↔ AsymptoticUpperBound := by
  rw [uniformFiniteUpperBound_iff_eventualExtremalUpperBound,
    eventualExtremalUpperBound_iff_asymptoticUpperBound]

/-- A coefficient-one finite estimate applies to an extremizer. -/
theorem coefficientOneExtremalUpperBound_of_coefficientOneFiniteUpperBound
    (h : CoefficientOneFiniteUpperBound) :
    CoefficientOneExtremalUpperBound := by
  intro ε hε
  obtain ⟨N₀, hbound⟩ := h ε hε
  filter_upwards [eventually_ge_atTop N₀] with N hN
  obtain ⟨A, hA, hcard⟩ := exists_extremizer N
  simpa [growth, hcard] using hbound N hN A hA

/-- An eventual coefficient-one estimate for the maximum bounds every
admissible set. -/
theorem coefficientOneFiniteUpperBound_of_coefficientOneExtremalUpperBound
    (h : CoefficientOneExtremalUpperBound) :
    CoefficientOneFiniteUpperBound := by
  intro ε hε
  have heventual := h ε hε
  rw [eventually_atTop] at heventual
  obtain ⟨N₀, hbound⟩ := heventual
  refine ⟨N₀, ?_⟩
  intro N hN A hA
  calc
    (A.card : ℝ) ≤ growth N := by
      change (A.card : ℝ) ≤ (F N : ℝ)
      exact_mod_cast card_le_F hA
    _ ≤ upperScale ε N := hbound N hN

theorem coefficientOneFiniteUpperBound_iff_coefficientOneExtremalUpperBound :
    CoefficientOneFiniteUpperBound ↔ CoefficientOneExtremalUpperBound :=
  ⟨coefficientOneExtremalUpperBound_of_coefficientOneFiniteUpperBound,
    coefficientOneFiniteUpperBound_of_coefficientOneExtremalUpperBound⟩

/-- The coefficient-one eventual statement immediately gives big-`O` with
constant one. -/
theorem asymptoticUpperBound_of_coefficientOneExtremalUpperBound
    (h : CoefficientOneExtremalUpperBound) : AsymptoticUpperBound := by
  intro ε hε
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [h ε hε] with N hN
  simpa only [growth, upperScale, one_mul, Real.norm_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ (F N : ℝ) by positivity),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)] using hN

/-- Conversely, a big-`O` constant can be absorbed into half of the positive
exponent loss.  Thus using coefficient one does not strengthen the final
`N^(1/4+o(1))` statement. -/
theorem coefficientOneExtremalUpperBound_of_asymptoticUpperBound
    (h : AsymptoticUpperBound) : CoefficientOneExtremalUpperBound := by
  intro ε hε
  obtain ⟨C, hC, hwith⟩ := (h (ε / 2) (half_pos hε)).exists_pos
  have htendsto : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (ε / 2)) atTop atTop :=
    (tendsto_rpow_atTop (half_pos hε)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hwith.bound,
    htendsto.eventually (eventually_ge_atTop C), eventually_ge_atTop 1]
      with N hN hCpow hN_one
  have hbound : growth N ≤ C * upperScale (ε / 2) N := by
    simpa only [growth, upperScale, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ (F N : ℝ) by positivity),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)] using hN
  have hbase_nonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hbase_pos : (0 : ℝ) < N := by exact_mod_cast hN_one
  calc
    growth N ≤ C * upperScale (ε / 2) N := hbound
    _ ≤ (N : ℝ) ^ (ε / 2) * upperScale (ε / 2) N :=
      mul_le_mul_of_nonneg_right hCpow
        (Real.rpow_nonneg hbase_nonneg _)
    _ = upperScale ε N := by
      rw [upperScale, upperScale, ← Real.rpow_add hbase_pos]
      congr 1
      ring

theorem coefficientOneExtremalUpperBound_iff_asymptoticUpperBound :
    CoefficientOneExtremalUpperBound ↔ AsymptoticUpperBound :=
  ⟨asymptoticUpperBound_of_coefficientOneExtremalUpperBound,
    coefficientOneExtremalUpperBound_of_asymptoticUpperBound⟩

/-- The exact coefficient-one finite Pham--Zakharov specialization is
equivalent to the requested asymptotic upper bound. -/
theorem coefficientOneFiniteUpperBound_iff_asymptoticUpperBound :
    CoefficientOneFiniteUpperBound ↔ AsymptoticUpperBound := by
  rw [coefficientOneFiniteUpperBound_iff_coefficientOneExtremalUpperBound,
    coefficientOneExtremalUpperBound_iff_asymptoticUpperBound]

/-- The elementary bound `F(N) ≤ N` gives every exponent at least one.
This is useful as a checked baseline, but it does not approach the sharp
quarter-power result.
-/
theorem eventual_upperScale_of_one_le_exponent (ε : ℝ)
    (hExponent : 1 ≤ (1 / 4 : ℝ) + ε) :
    ∀ᶠ N : ℕ in atTop, growth N ≤ upperScale ε N := by
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc
    growth N = (F N : ℝ) := rfl
    _ ≤ N := by exact_mod_cast F_le N
    _ = (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ ≤ (N : ℝ) ^ ((1 / 4 : ℝ) + ε) :=
      Real.rpow_le_rpow_of_exponent_le hbase hExponent
    _ = upperScale ε N := rfl

/-- In particular, the desired shape is elementary when `ε ≥ 3/4`,
i.e. when the total exponent is at least one. -/
theorem trivial_asymptotic_upper (ε : ℝ) (hε : (3 / 4 : ℝ) ≤ ε) :
    growth =O[atTop] upperScale ε := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventual_upperScale_of_one_le_exponent ε (by linarith)] with N hN
  simpa only [growth, upperScale, one_mul, Real.norm_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ (F N : ℝ) by positivity),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)] using hN

end

end Erdos186
