import Wikipedia.HopfProblem.FourthHurewiczFourSimplexQuotientBasic
import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexCubeFacets
import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexQuotientFacesMinimum

/-!
# Extended prefix minima on genuine cube facets

Insertion of one repeats one successive minimum. Appending zero leaves
the whole extended sequence unchanged, including its zero tail.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry

open CubicalBoundary

theorem extendedMinimum_cubeFacet_one_le {n : ℕ} (i : Fin (n + 1))
    (u : Fin n → I) (k : ℕ) (hk : k ≤ i.val) :
    extendedMinimum (cubeFacet n i 1 u) k = extendedMinimum u k := by
  have hkn : k ≤ n := hk.trans (Nat.le_of_lt_succ i.isLt)
  rw [extendedMinimum_of_le _ k (hkn.trans (Nat.le_succ n)),
    extendedMinimum_of_le u k hkn]
  exact prefixMinimum_insertNth_one_le i u k hk

theorem extendedMinimum_cubeFacet_one_succ {n : ℕ} (i : Fin (n + 1))
    (u : Fin n → I) (k : ℕ) (hk : i.val ≤ k) :
    extendedMinimum (cubeFacet n i 1 u) (k + 1) = extendedMinimum u k := by
  by_cases hkn : k ≤ n
  · rw [extendedMinimum_of_le _ (k + 1) (Nat.succ_le_succ hkn),
      extendedMinimum_of_le u k hkn]
    exact prefixMinimum_insertNth_one_succ i u k hk
  · simp only [extendedMinimum, if_neg hkn,
      if_neg (show ¬k + 1 ≤ n + 1 from fun h => hkn (Nat.succ_le_succ_iff.mp h))]

theorem extendedMinimum_cubeFacet_last_zero {n : ℕ} (u : Fin n → I) (k : ℕ) :
    extendedMinimum (cubeFacet n (Fin.last n) 0 u) k = extendedMinimum u k := by
  by_cases hkn : k ≤ n
  · rw [extendedMinimum_of_le _ k (hkn.trans (Nat.le_succ n)),
      extendedMinimum_of_le u k hkn]
    exact prefixMinimum_insertNth_last_le u 0 k hkn
  · by_cases hks : k ≤ n + 1
    · have hk : k = n + 1 := by omega
      subst k
      rw [extendedMinimum_of_le _ (n + 1) le_rfl, extendedMinimum_last_succ]
      change prefixMinimum (Fin.insertNth (Fin.last n) 0 u) (n + 1) = 0
      rw [prefixMinimum_insertNth_succ (Fin.last n) 0 u n le_rfl]
      exact min_eq_left (show (0 : I) ≤ prefixMinimum u n from bot_le)
    · simp only [extendedMinimum, if_neg hkn, if_neg hks]

end Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry
