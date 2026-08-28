import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleBasic

/-!
# A boundary-preserving return map from the triangle to the native square

The two coordinates are explicit continuous piecewise-affine functions of
the original barycentric coordinates. No disk homeomorphism is an input.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

theorem triangleReturn_first_mem (s : Simplex 2) :
    s 1 + max (s 2 - s 0) 0 ∈ unitInterval := by
  constructor
  · exact add_nonneg (stdSimplex.zero_le s 1) (le_max_right _ _)
  · have hm : max (s 2 - s 0) 0 ≤ s 2 :=
      max_le (sub_le_self _ (stdSimplex.zero_le s 0)) (stdSimplex.zero_le s 2)
    have h0 := stdSimplex.zero_le s 0
    have hs := stdSimplex.sum_eq_one s
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
    change s 0 + (s 1 + s 2) = 1 at hs
    linarith

theorem triangleReturn_second_mem (s : Simplex 2) :
    s 2 + min (s 0) (s 2) ∈ unitInterval := by
  constructor
  · exact add_nonneg (stdSimplex.zero_le s 2)
      (le_min (stdSimplex.zero_le s 0) (stdSimplex.zero_le s 2))
  · have hm : min (s 0) (s 2) ≤ s 0 := min_le_left _ _
    have h1 := stdSimplex.zero_le s 1
    have hs := stdSimplex.sum_eq_one s
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
    change s 0 + (s 1 + s 2) = 1 at hs
    linarith

/-- The explicit return map to Mathlib's actual two-dimensional cube. -/
def triangleCubicalReturn : C(Simplex 2, Fin 2 → I) where
  toFun s := ![⟨s 1 + max (s 2 - s 0) 0, triangleReturn_first_mem s⟩,
    ⟨s 2 + min (s 0) (s 2), triangleReturn_second_mem s⟩]
  continuous_toFun := by
    have hc (j : Fin 3) : Continuous (fun s : Simplex 2 => s j) :=
      (continuous_apply j).comp continuous_subtype_val
    apply continuous_pi
    intro i
    fin_cases i <;> apply Continuous.subtype_mk
    · change Continuous fun s : Simplex 2 => s 1 + max (s 2 - s 0) 0
      exact (hc 1).add (((hc 2).sub (hc 0)).max continuous_const)
    · change Continuous fun s : Simplex 2 => s 2 + min (s 0) (s 2)
      exact (hc 2).add ((hc 0).min (hc 2))

@[simp] theorem triangleCubicalReturn_zero (s : Simplex 2) :
    (triangleCubicalReturn s 0 : ℝ) = s 1 + max (s 2 - s 0) 0 := rfl

@[simp] theorem triangleCubicalReturn_one (s : Simplex 2) :
    (triangleCubicalReturn s 1 : ℝ) = s 2 + min (s 0) (s 2) := rfl

end Wikipedia.HopfProblem.ThirdHurewicz
