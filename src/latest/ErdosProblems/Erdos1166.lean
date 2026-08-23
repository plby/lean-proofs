/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166Core
import ErdosProblems.Erdos1165

/-!
The integration module for Erdős Problem 1166.

The exact planar walk model, deterministic plateau argument, recurrence, and
the unconditional Erdős--Taylor maximal-local-time estimate are developed in
`Erdos1166Core`.  The unconditional Hao--Li--Okada--Zheng eventual-three-site
theorem is imported from the complete formalization of Erdős Problem 1165.

The two files use extensionally identical presentations of the canonical
walk.  The lemmas below make that identification explicit before transferring
the almost-sure theorem.
-/

open Filter MeasureTheory ProbabilityTheory

namespace Erdos1166

/-- The direction encodings used by Problems 1165 and 1166 agree. -/
theorem directionStep_eq_erdos1165_directionVector (d : Direction) :
    directionStep d = Erdos1165.directionVector d := by
  fin_cases d <;> rfl

/-- The two uniform one-step laws are the same measure. -/
theorem directionLaw_eq_erdos1165_fairStep :
    directionLaw = Erdos1165.fairStep := by
  apply Measure.ext_of_singleton
  intro d
  rw [Erdos1165.fairStep_singleton]
  simp [directionLaw]

/-- Consequently, the two iid increment laws agree. -/
theorem incrementLaw_eq_erdos1165_fairSteps :
    incrementLaw = Erdos1165.fairSteps := by
  unfold incrementLaw Erdos1165.fairSteps
  congr 1
  funext n
  exact directionLaw_eq_erdos1165_fairStep

/-- Partial summation gives the same path in both formalizations. -/
theorem simpleRandomWalk_eq_erdos1165_trajectory (ω : ℕ → Direction) :
    simpleRandomWalk ω = Erdos1165.trajectory ω := by
  funext n
  simp only [simpleRandomWalk, Erdos1165.trajectory]
  apply Finset.sum_congr rfl
  intro d hd
  exact directionStep_eq_erdos1165_directionVector (ω d)

/-- The canonical path laws in Problems 1165 and 1166 are equal. -/
theorem simpleRandomWalkLaw_eq_erdos1165_simpleRandomWalk :
    simpleRandomWalkLaw = Erdos1165.simpleRandomWalk := by
  rw [simpleRandomWalkLaw, Erdos1165.simpleRandomWalk,
    incrementLaw_eq_erdos1165_fairSteps]
  congr 1
  funext ω n
  exact congr_fun (simpleRandomWalk_eq_erdos1165_trajectory ω) n

/-- The finite-prefix and range-filter definitions count the same visits. -/
theorem localTime_eq_erdos1165_localTime
    (s : ℕ → Site) (n : ℕ) (x : Site) :
    localTime s n x = Erdos1165.localTime s n x := by
  simp only [localTime, Erdos1165.localTime, Erdos1165.localTimePrefix,
    Erdos1165.pathPrefix]
  apply Finset.card_bij'
      (fun j hj ↦ ⟨j, Finset.mem_range.mp (Finset.mem_filter.mp hj).1⟩)
      (fun j _hj ↦ j.val)
  · intro j hj
    rfl
  · intro j hj
    apply Fin.ext
    rfl
  · intro j hj
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
  · intro j hj
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr j.isLt, (Finset.mem_filter.mp hj).2⟩

/-- Hence the favorite-site finsets in the two developments coincide. -/
theorem favoriteSites_eq_erdos1165_favoriteSites
    (s : ℕ → Site) (n : ℕ) :
    favoriteSites s n = Erdos1165.favoriteSites s n := by
  ext x
  rw [mem_favoriteSites_iff_globalMax,
    Erdos1165.mem_favoriteSites_iff_forall]
  simp only [localTime_eq_erdos1165_localTime]

/-- The completed Problem 1165 source construction gives the upper half of
the planar HLOZ theorem without any additional hypothesis. -/
theorem erdos1165_ae_eventually_favoriteCount_le_three :
    ∀ᵐ s ∂Erdos1165.simpleRandomWalk,
      ∀ᶠ n : ℕ in atTop, Erdos1165.favoriteCount s n ≤ 3 := by
  apply
    Erdos1165.HLOZStructuralPastAdditiveRecurrence.simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_lowerDeviation
  apply
    Erdos1165.HLOZDirectSourceFinalAssembly.hasPlanarMaximumLowerDeviation_of_asymmetricPairSource
  intro delta _hdelta
  exact
    Erdos1165.AsymmetricCoarseRadialCompletionFamily.eventually_nonempty_asymmetricPairSourceData
      delta

/-- Unconditional eventual-three-favorite-sites conclusion in the Problem
1166 model. -/
theorem hlozPlanar : HLOZPlanarConclusion := by
  unfold HLOZPlanarConclusion
  rw [simpleRandomWalkLaw_eq_erdos1165_simpleRandomWalk]
  filter_upwards [erdos1165_ae_eventually_favoriteCount_le_three] with s hs
  simpa only [EventuallyAtMostThree,
    favoriteSites_eq_erdos1165_favoriteSites,
    Erdos1165.favoriteCount] using hs

/-- Erdős Problem 1166 for the canonical planar simple symmetric random-walk
law.  Almost surely, the cumulative favorite set is `O((log n)^2)`. -/
theorem erdos_1166 :
    ∀ᵐ s ∂simpleRandomWalkLaw, HasCumulativeFavoriteLogSqBound s :=
  erdos_1166_of_hloz hlozPlanar

end Erdos1166
