/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1215.
https://www.erdosproblems.com/forum/thread/1215

Informal authors:
- Gerald R. Mac Lane

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1215.md
-/
import ErdosProblems.Erdos1215.Barrier
import ErdosProblems.Erdos1215.Geometry
import ErdosProblems.Erdos1215.Reciprocal
import ErdosProblems.Erdos1215.Separator
import ErdosProblems.Erdos1215.Topology

/-!
# Erdős Problem 1215

Mac Lane's negative answer to the question whether paths in the strict
sublevel set of a polynomial whose roots lie on the unit circle have a
universal length bound.

The strict inequality is imposed away from the initial parameter: the
historical statement explicitly excludes the origin, where the normalization
`P(0) = 1` makes strict sublevel membership impossible.

The detailed mathematical proof and Leanization map are in `tex/1215.tex`.
-/

open Set Metric
open scoped ENNReal Topology BigOperators

noncomputable section

namespace Erdos1215

/-- A normalized, nonconstant polynomial all of whose roots lie on the complex
unit circle. -/
def IsAdmissible (P : Polynomial ℂ) : Prop :=
  P.eval 0 = 1 ∧
    0 < P.natDegree ∧
      ∀ z : ℂ, P.IsRoot z → ‖z‖ = 1

/-- An endpoint-correct escape path.  The value at `t = 0` is excluded from
the strict sublevel condition, exactly as in the original formulation. -/
def IsEscapePath (P : Polynomial ℂ) (γ : ℝ → ℂ) : Prop :=
  ContinuousOn γ (Icc 0 1) ∧
    γ 0 = 0 ∧
      ‖γ 1‖ = 1 ∧
        ∀ t ∈ Icc (0 : ℝ) 1, t ≠ 0 → ‖P.eval (γ t)‖ < 1

/-- Extended total variation on the parameter interval.  Nonrectifiable paths
have infinite extended length. -/
def PathELength (γ : ℝ → ℂ) : ℝ≥0∞ :=
  eVariationOn γ (Icc 0 1)

/-- The positive assertion asked in Problem 1215. -/
def HasUniformEscapeBound : Prop :=
  ∃ C : ℝ, ∀ P : Polynomial ℂ, IsAdmissible P →
    ∃ γ : ℝ → ℂ, IsEscapePath P γ ∧ PathELength γ ≤ ENNReal.ofReal C

/-- The stronger form of Mac Lane's counterexample statement. -/
def HasArbitrarilyLongCounterexamples : Prop :=
  ∀ L : ℝ, 0 ≤ L →
    ∃ P : Polynomial ℂ, IsAdmissible P ∧
      ∀ γ : ℝ → ℂ, IsEscapePath P γ → ENNReal.ofReal L < PathELength γ

theorem not_hasUniformEscapeBound_of_arbitrarilyLong
    (h : HasArbitrarilyLongCounterexamples) :
    ¬ HasUniformEscapeBound := by
  rintro ⟨C, hC⟩
  obtain ⟨P, hP, hlong⟩ := h (max C 0) (le_max_right C 0)
  obtain ⟨γ, hγ, hγle⟩ := hC P hP
  have hCmax : ENNReal.ofReal C ≤ ENNReal.ofReal (max C 0) :=
    ENNReal.ofReal_le_ofReal (le_max_left C 0)
  exact (not_lt_of_ge (hγle.trans hCmax)) (hlong γ hγ)

/-- Mac Lane's strong counterexample statement: for every proposed finite
length, one normalized positive-degree polynomial forces every escape path
to have strictly larger extended variation. -/
theorem hasArbitrarilyLongCounterexamples :
    HasArbitrarilyLongCounterexamples := by
  intro L hL
  let m : ℕ := wallCount L
  let K : Set ℂ := alternatingWalls (standardWallRadius m) m
  have hKcompact : IsCompact K := by
    simpa [K] using standardAlternatingWalls_isCompact m
  have hKlower : ∀ z ∈ K, (1 : ℝ) / 2 ≤ ‖z‖ := by
    intro z hz
    rcases mem_iUnion₂.1 hz with ⟨j, hj, hjwall⟩
    rw [hjwall.1]
    exact (half_lt_standardWallRadius m j).le
  have hKopenDisk : ∀ z ∈ K, ‖z‖ < 1 := by
    intro z hz
    rcases mem_iUnion₂.1 hz with ⟨j, hj, hjwall⟩
    rw [hjwall.1]
    exact (standardWallRadius_lt_three_quarters hj).trans (by norm_num)
  have hKclosedDisk : ∀ z ∈ K, ‖z‖ ≤ 1 :=
    fun z hz ↦ (hKopenDisk z hz).le
  have hKcompl : IsPreconnected (insert (0 : ℂ) K)ᶜ := by
    simpa [K] using standardAlternatingWalls_compl_isPreconnected m
  obtain ⟨h, hh0, hhK⟩ :=
    exists_polynomial_separator K hKcompact hKlower hKcompl
  obtain ⟨p, hp0, hpzero, hplarge⟩ :=
    exists_zeroFree_polynomial_large_on_set K h 1 hh0 (by norm_num) hhK hKclosedDisk
  obtain ⟨N, hN⟩ :=
    exists_macLanePolynomial_for_all_large_degrees
      p K hp0 hpzero hKcompact hKopenDisk hplarge
  let n : ℕ := max N 1
  obtain ⟨P, hPdegree, hPzero, hProots, hPlarge⟩ :=
    hN n (le_max_left N 1)
  refine ⟨P, ⟨hPzero, ?_, hProots⟩, ?_⟩
  · rw [hPdegree]
    exact lt_of_lt_of_le Nat.zero_lt_one (le_max_right N 1)
  · intro γ hγ
    apply explicit_labyrinth_forces_long_path hL
    · exact ⟨hγ.1, hγ.2.1, hγ.2.2.1⟩
    · intro t ht htwall
      have hsublevel := hγ.2.2.2 t ⟨ht.1.le, ht.2⟩ (ne_of_gt ht.1)
      have hbarrier : 2 < ‖P.eval (γ t)‖ := hPlarge (γ t) htwall
      linarith

/-- The negative resolution of Erdős Problem 1215, stated without an
abbreviation: no real constant bounds an escape path for every normalized
positive-degree polynomial whose roots lie on the unit circle. -/
theorem erdos_1215 :
    ¬ ∃ C : ℝ, ∀ P : Polynomial ℂ,
      (P.eval 0 = 1 ∧ 0 < P.natDegree ∧
        ∀ z : ℂ, P.IsRoot z → ‖z‖ = 1) →
      ∃ γ : ℝ → ℂ,
        (ContinuousOn γ (Icc 0 1) ∧ γ 0 = 0 ∧ ‖γ 1‖ = 1 ∧
          ∀ t ∈ Icc (0 : ℝ) 1, t ≠ 0 → ‖P.eval (γ t)‖ < 1) ∧
        eVariationOn γ (Icc 0 1) ≤ ENNReal.ofReal C := by
  change ¬ HasUniformEscapeBound
  exact not_hasUniformEscapeBound_of_arbitrarilyLong hasArbitrarilyLongCounterexamples

end Erdos1215

#print axioms Erdos1215.erdos_1215
