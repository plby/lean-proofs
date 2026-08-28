import Wikipedia.HopfProblem.FourthHurewiczFourSimplexQuotientBasic
import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexCubeFacets

/-!
# Two missing barycentric coordinates on the cubical two-boundary

The statements concern the original native cube and simplex. Two endpoint
coordinates force two distinct zero barycentric coordinates. A bottom
facet other than the last one already has this property everywhere.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry

open FirstHurewicz CubicalBoundary SecondHurewicz.SimplyConnected

/-- The union of the actual codimension-two simplex faces. -/
def simplexTwoBoundary (n : ℕ) : Set (Simplex n) :=
  {s | ∃ i j : Fin (n + 1), i ≠ j ∧ s i = 0 ∧ s j = 0}

theorem simplexTwoBoundary_subset (n : ℕ) : simplexTwoBoundary n ⊆ simplexBoundary n := by
  rintro s ⟨i, j, _, hi, _⟩
  exact ⟨i, hi⟩

theorem simplexFace_simplexBoundary (n : ℕ) (i : Fin (n + 2)) (s : Simplex n)
    (hs : s ∈ simplexBoundary n) : simplexFace n i s ∈ simplexTwoBoundary (n + 1) := by
  obtain ⟨j, hj⟩ := hs
  exact ⟨i, i.succAbove j, (Fin.succAbove_ne i j).symm,
    simplexFace_apply_self n i s, (simplexFace_apply_succAbove n i s j).trans hj⟩

theorem prefixMinimum_eq_zero_of_coordinate {n : ℕ} (u : Fin n → I)
    (i : Fin n) (hi : u i = 0) (k : ℕ) (hik : i.val < k) :
    prefixMinimum u k = 0 :=
  le_antisymm (hi ▸ prefixMinimum_le_coordinate u k i hik) bot_le

theorem simplexQuotient_last_eq_zero_of_zero {n : ℕ} (u : Fin n → I)
    (i : Fin n) (hi : u i = 0) : simplexQuotient n u (Fin.last n) = 0 := by
  rw [simplexQuotient_last, prefixMinimum_eq_zero_of_coordinate u i hi n i.isLt]
  rfl

theorem simplexQuotient_castSucc_eq_zero_of_one {n : ℕ} (u : Fin n → I)
    (i : Fin n) (hi : u i = 1) : simplexQuotient n u i.castSucc = 0 := by
  rw [simplexQuotient_castSucc, prefixMinimum_succ u i.val i.isLt]
  change (prefixMinimum u i.val : ℝ) - (min (prefixMinimum u i.val) (u i) : I) = 0
  rw [hi, min_eq_left (show prefixMinimum u i.val ≤ 1 from
    (prefixMinimum u i.val).property.2)]
  exact sub_self _

theorem simplexQuotient_castSucc_eq_zero_of_earlier_zero {n : ℕ}
    (u : Fin n → I) (i j : Fin n) (hij : i < j) (hi : u i = 0) :
    simplexQuotient n u j.castSucc = 0 := by
  rw [simplexQuotient_castSucc,
    prefixMinimum_eq_zero_of_coordinate u i hi j.val hij,
    prefixMinimum_eq_zero_of_coordinate u i hi (j.val + 1)
      ((show i.val < j.val from hij).trans_le (Nat.le_succ j.val))]
  exact sub_self _

/-- No lower bound on the dimension is needed: the two distinct endpoint
coordinates themselves supply the necessary dimension information. -/
theorem simplexQuotient_codimTwo {n : ℕ} (u : Fin n → I)
    (hu : ∃ i j : Fin n, i ≠ j ∧ (u i = 0 ∨ u i = 1) ∧ (u j = 0 ∨ u j = 1)) :
    simplexQuotient n u ∈ simplexTwoBoundary n := by
  obtain ⟨i, j, hij, hi | hi, hj | hj⟩ := hu
  · rcases lt_or_gt_of_ne hij with hij' | hji'
    · exact ⟨j.castSucc, Fin.last n, Fin.castSucc_ne_last j,
        simplexQuotient_castSucc_eq_zero_of_earlier_zero u i j hij' hi,
        simplexQuotient_last_eq_zero_of_zero u i hi⟩
    · exact ⟨i.castSucc, Fin.last n, Fin.castSucc_ne_last i,
        simplexQuotient_castSucc_eq_zero_of_earlier_zero u j i hji' hj,
        simplexQuotient_last_eq_zero_of_zero u j hj⟩
  · exact ⟨j.castSucc, Fin.last n, Fin.castSucc_ne_last j,
      simplexQuotient_castSucc_eq_zero_of_one u j hj,
      simplexQuotient_last_eq_zero_of_zero u i hi⟩
  · exact ⟨i.castSucc, Fin.last n, Fin.castSucc_ne_last i,
      simplexQuotient_castSucc_eq_zero_of_one u i hi,
      simplexQuotient_last_eq_zero_of_zero u j hj⟩
  · exact ⟨i.castSucc, j.castSucc, fun h => hij (Fin.castSucc_injective n h),
      simplexQuotient_castSucc_eq_zero_of_one u i hi,
      simplexQuotient_castSucc_eq_zero_of_one u j hj⟩

theorem simplexQuotient_bottom_not_last_twoBoundary (n : ℕ) (i : Fin (n + 1))
    (hi : i ≠ Fin.last n) (u : Fin n → I) :
    simplexQuotient (n + 1) (cubeFacet n i 0 u) ∈ simplexTwoBoundary (n + 1) := by
  have hil : i < Fin.last n := lt_of_le_of_ne (Fin.le_last i) hi
  exact ⟨(Fin.last n).castSucc, Fin.last (n + 1), Fin.castSucc_ne_last _,
    simplexQuotient_castSucc_eq_zero_of_earlier_zero (cubeFacet n i 0 u) i
      (Fin.last n) hil (cubeFacet_apply_self n i 0 u),
    simplexQuotient_last_eq_zero_of_zero (cubeFacet n i 0 u) i
      (cubeFacet_apply_self n i 0 u)⟩

theorem simplexQuotient_cubeFacet_boundary_twoBoundary (n : ℕ)
    (i : Fin (n + 1)) (ε : I) (hε : ε = 0 ∨ ε = 1) (u : Fin n → I)
    (hu : u ∈ Cube.boundary (Fin n)) :
    simplexQuotient (n + 1) (cubeFacet n i ε u) ∈ simplexTwoBoundary (n + 1) :=
  simplexQuotient_codimTwo _ (cubeFacet_codimTwo n i ε hε u hu)

end Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry
