/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.ScreeningInstantiation
import ErdosProblems.Erdos1165.Upper
import ErdosProblems.Erdos1165.UpperAssembly

/-!
# Canonical assembly of the HLOZ upper bound

This module joins three independently checked pieces of the upper bound for
Erdős Problem 1165:

* the concrete exponent `ScreeningInstantiation.kappa`, whose triple is
  larger than one;
* the three-transition finite-mesh estimate in `UpperAssembly`;
* the six concrete lattice domino tilings and recurrence-backed
  Borel--Cantelli endgame in `Upper`.

The resulting theorem does not assert a missing random-walk estimate.  Its
premises display the remaining path-level screening decomposition, the three
successive one-transition probability estimates, and summability of the
exceptional family.  The power-envelope calculation, six-tiling cover,
recurrence, and Borel--Cantelli argument are discharged here.
-/

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace Erdos1165
namespace UpperCanonical

open ScreeningInstantiation UpperAssembly

/-! ## The checked cubic power envelope -/

/-- Cubing the shifted `p`-series weight triples its exponent. -/
lemma pSeriesWeight_cube (p : ℝ) (m : ℕ) :
    pSeriesWeight p m ^ 3 = pSeriesWeight (3 * p) m := by
  unfold pSeriesWeight
  rw [← ENNReal.ofReal_pow (by positivity : 0 ≤
    1 / |(m : ℝ) + 1| ^ p)]
  congr 1
  rw [div_pow]
  simp only [one_pow]
  congr 1
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (abs_nonneg ((m : ℝ) + 1))]
  ring_nf

/-- The canonical one-transition envelope at level `m`.  The constant is
uniform in the tiling and the three bins. -/
noncomputable def hlozTransitionCost (K : ℝ≥0) (m : ℕ) : ℝ≥0∞ :=
  (K : ℝ≥0∞) * pSeriesWeight kappa m

/-- The cube of the canonical transition envelope is exactly a constant
multiple of a `p`-series with the summable exponent `3 * kappa`. -/
lemma hlozTransitionCost_cube (K : ℝ≥0) (m : ℕ) :
    hlozTransitionCost K m ^ 3 =
      ((K ^ 3 : ℝ≥0) : ℝ≥0∞) * pSeriesWeight (3 * kappa) m := by
  rw [hlozTransitionCost, mul_pow, pSeriesWeight_cube, ENNReal.coe_pow]

/-! ## Six concrete tilings and the canonical walk -/

/-- The checked HLOZ transition exponent makes every concrete separated
four-favorite level family summable.  The event decomposition and the three
successive measure inequalities are exactly the path-level estimates still
required from the planar walk argument. -/
theorem separated_level_series_ne_top_of_hloz_transition_estimates
    {Scale : Type*} (mesh : Finset Scale)
    (exceptional : DominoTiling → ℕ → Set WalkPath)
    (firstStage secondStage thirdStage :
      DominoTiling → ℕ → ((Scale × Scale) × Scale) → Set WalkPath)
    (K : ℝ≥0)
    (hmesh : ∀ t m, separatedFourFavoriteLevelEvent t m ⊆
      exceptional t m ∪ meshBranchUnion mesh (thirdStage t m))
    (hfirst : ∀ t m a, a ∈ meshTriples mesh →
      simpleRandomWalk (firstStage t m a) ≤ hlozTransitionCost K m)
    (hsecond : ∀ t m a, a ∈ meshTriples mesh →
      simpleRandomWalk (secondStage t m a) ≤
        hlozTransitionCost K m * simpleRandomWalk (firstStage t m a))
    (hthird : ∀ t m a, a ∈ meshTriples mesh →
      simpleRandomWalk (thirdStage t m a) ≤
        hlozTransitionCost K m * simpleRandomWalk (secondStage t m a))
    (hexception : ∀ t, ∑' m, simpleRandomWalk (exceptional t m) ≠ ∞) :
    ∀ t, ∑' m, simpleRandomWalk (separatedFourFavoriteLevelEvent t m) ≠ ∞ := by
  intro t
  apply screenedLevel_series_ne_top simpleRandomWalk mesh
    (separatedFourFavoriteLevelEvent t) (exceptional t)
    (firstStage t) (secondStage t) (thirdStage t)
    (hlozTransitionCost K) (K ^ 3) (3 * kappa)
  · exact hloz_parameter_inequalities.2.2.2.2.2.2.2.1
  · exact hmesh t
  · exact hfirst t
  · exact hsecond t
  · exact hthird t
  · exact hexception t
  · intro m
    exact (hlozTransitionCost_cube K m).le

/-- Canonical upper-bound endgame.  The six separated tilings are the actual
lattice tilings from `Tilings`, and recurrence of `simpleRandomWalk` is used
internally.  Thus no abstract six-cover or maximal-local-time divergence
hypothesis remains. -/
theorem simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_hloz_transition_estimates
    {Scale : Type*} (mesh : Finset Scale)
    (exceptional : DominoTiling → ℕ → Set WalkPath)
    (firstStage secondStage thirdStage :
      DominoTiling → ℕ → ((Scale × Scale) × Scale) → Set WalkPath)
    (K : ℝ≥0)
    (hmesh : ∀ t m, separatedFourFavoriteLevelEvent t m ⊆
      exceptional t m ∪ meshBranchUnion mesh (thirdStage t m))
    (hfirst : ∀ t m a, a ∈ meshTriples mesh →
      simpleRandomWalk (firstStage t m a) ≤ hlozTransitionCost K m)
    (hsecond : ∀ t m a, a ∈ meshTriples mesh →
      simpleRandomWalk (secondStage t m a) ≤
        hlozTransitionCost K m * simpleRandomWalk (firstStage t m a))
    (hthird : ∀ t m a, a ∈ meshTriples mesh →
      simpleRandomWalk (thirdStage t m a) ≤
        hlozTransitionCost K m * simpleRandomWalk (secondStage t m a))
    (hexception : ∀ t, ∑' m, simpleRandomWalk (exceptional t m) ≠ ∞) :
    ∀ᵐ s ∂simpleRandomWalk,
      ∀ᶠ n in atTop, favoriteCount s n ≤ 3 := by
  apply simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_separated_level_summable
  exact separated_level_series_ne_top_of_hloz_transition_estimates mesh exceptional
    firstStage secondStage thirdStage K hmesh hfirst hsecond hthird hexception

end UpperCanonical
end Erdos1165
