import Wikipedia.HopfProblem.FourthHurewiczFourSimplexQuotientMinimum
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedExtensionBasic

/-!
# The simplex quotient in arbitrary dimension

The successive differences of extended prefix minima are nonnegative and
sum to one.  They define an actual continuous map from the native cube to
the standard simplex, taking the whole cube boundary into the simplex
boundary.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry

open FirstHurewicz

/-- The nested-minimum quotient from a native cube to the actual simplex. -/
def simplexQuotient (n : ℕ) : C(Fin n → I, Simplex n) where
  toFun u := ⟨fun i => (extendedMinimum u i.val : ℝ) -
    (extendedMinimum u (i.val + 1) : ℝ), by
      constructor
      · intro i
        exact sub_nonneg.mpr (extendedMinimum_antitone u (Nat.le_succ i.val))
      · calc
          (∑ i : Fin (n + 1), ((extendedMinimum u i.val : ℝ) -
              (extendedMinimum u (i.val + 1) : ℝ))) =
              ∑ i ∈ Finset.range (n + 1), ((extendedMinimum u i : ℝ) -
                (extendedMinimum u (i + 1) : ℝ)) :=
            Fin.sum_univ_eq_sum_range (fun k : ℕ => (extendedMinimum u k : ℝ) -
              (extendedMinimum u (k + 1) : ℝ)) (n + 1)
          _ = (extendedMinimum u 0 : ℝ) - (extendedMinimum u (n + 1) : ℝ) :=
            Finset.sum_range_sub' _ _
          _ = 1 := by simp⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (continuous_subtype_val.comp (continuous_extendedMinimum n i.val)).sub
      (continuous_subtype_val.comp (continuous_extendedMinimum n (i.val + 1)))

theorem simplexQuotient_apply {n : ℕ} (u : Fin n → I) (i : Fin (n + 1)) :
    simplexQuotient n u i = (extendedMinimum u i.val : ℝ) -
      (extendedMinimum u (i.val + 1) : ℝ) := rfl

theorem simplexQuotient_castSucc {n : ℕ} (u : Fin n → I) (i : Fin n) :
    simplexQuotient n u i.castSucc = (prefixMinimum u i.val : ℝ) -
      (prefixMinimum u (i.val + 1) : ℝ) := by
  rw [simplexQuotient_apply]
  exact congrArg₂ (fun a b : I => (a : ℝ) - (b : ℝ))
    (extendedMinimum_of_le u i.val i.isLt.le)
    (extendedMinimum_of_le u (i.val + 1) i.isLt)

@[simp] theorem simplexQuotient_last {n : ℕ} (u : Fin n → I) :
    simplexQuotient n u (Fin.last n) = (prefixMinimum u n : ℝ) := by
  rw [simplexQuotient_apply]
  simp only [Fin.val_last, extendedMinimum_last_succ,
    extendedMinimum_of_le u n le_rfl]
  exact sub_zero _

theorem simplexQuotient_boundary_of_zero {n : ℕ} (u : Fin n → I)
    (i : Fin n) (hi : u i = 0) :
    simplexQuotient n u ∈ SecondHurewicz.SimplyConnected.simplexBoundary n := by
  have hp : prefixMinimum u n = 0 := le_antisymm
    (hi ▸ prefixMinimum_le_coordinate u n i i.isLt) bot_le
  exact ⟨Fin.last n, by rw [simplexQuotient_last, hp]; rfl⟩

theorem simplexQuotient_boundary_of_one {n : ℕ} (u : Fin n → I)
    (i : Fin n) (hi : u i = 1) :
    simplexQuotient n u ∈ SecondHurewicz.SimplyConnected.simplexBoundary n := by
  refine ⟨i.castSucc, ?_⟩
  rw [simplexQuotient_castSucc, prefixMinimum_succ u i.val i.isLt]
  change (prefixMinimum u i.val : ℝ) - (min (prefixMinimum u i.val) (u i) : I) = 0
  rw [hi, min_eq_left (show prefixMinimum u i.val ≤ 1 from
    (prefixMinimum u i.val).property.2)]
  exact sub_self _

/-- Every boundary point of the original native cube maps to an actual simplex face. -/
theorem simplexQuotient_boundary {n : ℕ} (u : Fin n → I)
    (hu : u ∈ Cube.boundary (Fin n)) :
    simplexQuotient n u ∈ SecondHurewicz.SimplyConnected.simplexBoundary n := by
  obtain ⟨i, hi | hi⟩ := hu
  · exact simplexQuotient_boundary_of_zero u i hi
  · exact simplexQuotient_boundary_of_one u i hi

end Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry
