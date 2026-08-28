import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexWhiskerGeometry
import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexCubicalBasic

/-!
# Codimension-two basedness of the actual whiskering map

Two endpoint coordinates in the parameter cube remain two endpoint
coordinates along the whisker. If the last coordinate is involved, the
three-edge rectangle track supplies the required second endpoint.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}

/-- The two endpoints of each whisker lie on the actual codimension-two boundary. -/
theorem whiskerCorner_based (F : BasedCubicalCell (n + 2) x)
    (ε : I) (hε : ε = 0 ∨ ε = 1) (v : Fin n → I) :
    F.val (Fin.cons ε (Fin.snoc v 0)) = x := by
  apply F.property _ 0 (Fin.last n).succ (by simp)
  · simpa only [Fin.cons_zero] using hε
  · exact Or.inl (by simp)

/-- Two endpoint coordinates among the unchanged coordinates stay based. -/
theorem whiskerMap_based_of_two_prefix (F : BasedCubicalCell (n + 2) x)
    (u : Fin (n + 1) → I) (s : I) (i j : Fin n) (hij : i ≠ j)
    (hi : u i.castSucc = 0 ∨ u i.castSucc = 1)
    (hj : u j.castSucc = 0 ∨ u j.castSucc = 1) :
    F.val (whiskerMap n (u, s)) = x := by
  apply F.property _ i.castSucc.succ j.castSucc.succ (by simpa using hij)
  · simpa only [whiskerMap_middle] using hi
  · simpa only [whiskerMap_middle] using hj

/-- One unchanged endpoint coordinate and an endpoint of the radial coordinate
keep every point of the three-piece whisker on the based boundary. -/
theorem whiskerMap_based_of_prefix_last (F : BasedCubicalCell (n + 2) x)
    (u : Fin (n + 1) → I) (s : I) (i : Fin n)
    (hi : u i.castSucc = 0 ∨ u i.castSucc = 1)
    (hz : u (Fin.last n) = 0 ∨ u (Fin.last n) = 1) :
    F.val (whiskerMap n (u, s)) = x := by
  rcases hz with hz | hz
  · apply F.property _ i.castSucc.succ (Fin.last n).succ (by simp)
    · simpa only [whiskerMap_middle] using hi
    · exact Or.inl (whiskerMap_last_zero n u s hz)
  · rcases whiskerTrack_boundary s with ht | hr
    · apply F.property _ 0 i.castSucc.succ (Fin.succ_ne_zero i.castSucc).symm
      · simpa only [whiskerMap_first] using ht
      · simpa only [whiskerMap_middle] using hi
    · apply F.property _ i.castSucc.succ (Fin.last n).succ (by simp)
      · simpa only [whiskerMap_middle] using hi
      · exact Or.inr (by simp [hr, hz])

/-- The complete, generic codimension-two boundary condition for whiskering. -/
theorem whiskerMap_codimTwo_based (F : BasedCubicalCell (n + 2) x)
    (u : Fin (n + 1) → I) (s : I) (i j : Fin (n + 1)) (hij : i ≠ j)
    (hi : u i = 0 ∨ u i = 1) (hj : u j = 0 ∨ u j = 1) :
    F.val (whiskerMap n (u, s)) = x := by
  cases i using Fin.lastCases with
  | last =>
    cases j using Fin.lastCases with
    | last => exact (hij rfl).elim
    | cast j => exact whiskerMap_based_of_prefix_last F u s j hj hi
  | cast i =>
    cases j using Fin.lastCases with
    | last => exact whiskerMap_based_of_prefix_last F u s i hi hj
    | cast j =>
      exact whiskerMap_based_of_two_prefix F u s i j (by simpa using hij) hi hj

end Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary
