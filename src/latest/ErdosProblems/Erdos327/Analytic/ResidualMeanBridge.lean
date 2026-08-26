import ErdosProblems.Erdos327.Analytic.ResidualMean
import ErdosProblems.Erdos327.Analytic.RoughCount

/-!
# Rough-interval bridge for residual moments

`ResidualMean` is stated for the slightly larger `OddRough` support,
which is convenient after extracting a possible factor of two.  The
mixed estimate uses fully `L`-rough integers on a subinterval.  This
file records the direct domination needed to apply the residual theorem
there.
-/

namespace Erdos327.Analytic

open Finset

/-- Full `L`-roughness implies odd-prime `L`-roughness. -/
theorem Rough.oddRough {L n : ℕ} (h : Rough L n) :
    OddRough L n := by
  intro p hp hp2 hpL
  exact h p hp hpL

/-- A fully rough residual moment on a subinterval is bounded by the
`OddRough` residual moment on `[1,Y]`. -/
theorem sum_roughResidual_subinterval_le
    {L X a Y : ℕ} {q : ℝ} (ha : 1 ≤ a) (hq : 0 ≤ q) :
    (∑ n ∈ Icc a Y,
        if Rough L n then
          q ^ primeFactorCountBetween L X n else 0) ≤
      ∑ n ∈ Icc 1 Y,
        if OddRough L n then
          q ^ primeFactorCountBetween L X n else 0 := by
  let f : ℕ → ℝ := fun n ↦
    if Rough L n then q ^ primeFactorCountBetween L X n else 0
  let g : ℕ → ℝ := fun n ↦
    if OddRough L n then q ^ primeFactorCountBetween L X n else 0
  have hpoint (n : ℕ) : f n ≤ g n := by
    dsimp [f, g]
    by_cases hr : Rough L n
    · rw [if_pos hr, if_pos hr.oddRough]
    · rw [if_neg hr]
      positivity
  have hsubset : Icc a Y ⊆ Icc 1 Y := by
    intro n hn
    rw [mem_Icc] at hn ⊢
    exact ⟨ha.trans hn.1, hn.2⟩
  calc
    (∑ n ∈ Icc a Y,
        if Rough L n then
          q ^ primeFactorCountBetween L X n else 0) =
        ∑ n ∈ Icc a Y, f n := rfl
    _ ≤ ∑ n ∈ Icc a Y, g n :=
      sum_le_sum fun n _ ↦ hpoint n
    _ ≤ ∑ n ∈ Icc 1 Y, g n := by
      apply sum_le_sum_of_subset_of_nonneg hsubset
      intro n _ _
      dsimp [g]
      split_ifs <;> positivity
    _ = _ := rfl

/-- Explicit Mertens bound for a fully rough residual moment on an
arbitrary positive subinterval. -/
theorem roughResidualSubinterval_le_mertens
    {L X a Y : ℕ} {q : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hLY : L ≤ Y)
    (hY : 2 ≤ Y) (ha : 1 ≤ a)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∑ n ∈ Icc a Y,
        if Rough L n then
          q ^ primeFactorCountBetween L X n else 0) ≤
      2 * ((Real.log 4 + 5) * Y / Real.log Y) *
        Real.exp
          (q * primeInvTailUpper (L - 1) (min X Y) +
            primeInvTailUpper (min X Y) Y + 38) := by
  exact (sum_roughResidual_subinterval_le ha hq0).trans
    (residualMoment_le_mertens
      hL hLX hLY hY hq0 hq1)

end Erdos327.Analytic
