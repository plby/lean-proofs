/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos920.Bridge
import ErdosProblems.Erdos920.Construction
import ErdosProblems.Erdos920.Inversion
import ErdosProblems.Erdos920.RamseyPackaging

/-!
# Erdős Problem 920

The graph-theoretic Ramsey bridge is in `Bridge`, the finite-geometric Ramsey
construction is packaged in `RamseyPackaging`, and the asymptotic inversion is
in `Inversion`.
-/

open Real Filter

/-- `g ≫ h` means that `h` is big-O of `g` at infinity. -/
notation:50 g " ≫ " h => Asymptotics.IsBigO Filter.atTop h g

namespace Erdos920

/--
The final implication, isolated from the construction of Bradač's Ramsey
lower bound.  This is the narrow assembly interface used by the main theorem.
-/
theorem erdos_920_of_eventual_bradac_ramsey_lower_bound
    (hbradac : ∀ s : ℕ, 3 ≤ s → ∃ A : ℝ, 0 < A ∧
      ∀ᶠ m : ℕ in atTop,
        A * (m : ℝ) ^ (s - 1) / Real.log (m : ℝ) ^ (2 * s - 4) ≤
          (Ramsey.ramseyNumber s m : ℝ)) :
    ∀ k : ℕ, k ≥ 4 → ∃ c > 0,
      (fun n : ℕ ↦ (f k n : ℝ)) ≫
        (fun n : ℕ ↦ (n : ℝ) ^ (1 - 1 / ((k : ℝ) - 1)) / (log n) ^ c) := by
  intro k hk
  obtain ⟨A, hA, hRamsey⟩ := hbradac k (by omega)
  refine ⟨2, by norm_num, ?_⟩
  exact Inversion.isBigO_problem920_of_eventual_ramsey_lower_bound
    k (by omega) (Ramsey.ramseyNumber k) (fun n ↦ (f k n : ℝ)) A hA hRamsey
    (by
      intro n m hm hlt
      exact real_div_le_f_of_lt_ramseyNumber hm hlt)

/-- A family of proved `D⋆` constructions for all positive parameters is
enough to settle Problem 920. -/
theorem erdos_920_of_dStarFamilies
    (families : ∀ u : ℕ, 1 ≤ u → RamseyPackaging.DStarFamily u) :
    ∀ k : ℕ, k ≥ 4 → ∃ c > 0,
      (fun n : ℕ ↦ (f k n : ℝ)) ≫
        (fun n : ℕ ↦ (n : ℝ) ^ (1 - 1 / ((k : ℝ) - 1)) / (log n) ^ c) := by
  apply erdos_920_of_eventual_bradac_ramsey_lower_bound
  intro s hs
  exact RamseyPackaging.bradac_ramsey_lower_bound_eventually_of_package
    s hs (families (s - 2) (by omega))

/-- Erdős Problem 920 has a positive answer. -/
theorem erdos_920 :
    ∀ k : ℕ, k ≥ 4 → ∃ c > 0,
      (fun n : ℕ ↦ (f k n : ℝ)) ≫
        (fun n : ℕ ↦ (n : ℝ) ^ (1 - 1 / ((k : ℝ) - 1)) / (log n) ^ c) := by
  exact erdos_920_of_dStarFamilies Construction.dStarFamily

end Erdos920

#print axioms Erdos920.erdos_920_of_dStarFamilies
#print axioms Erdos920.erdos_920
