import Wikipedia.HopfProblem.Lattice

/-! # The invariant alternating form of `tex/s6.tex`, Lemma 2.8 -/

namespace Wikipedia.HopfProblem

/-- An alternating form in the six independent coordinates
`(γu, γw, γδ, uw, uδ, wδ)`. -/
def alternatingMatrix (a b c d e f : ℤ) : LatticeMatrix :=
  !![0, a, b, c; -a, 0, d, e; -b, -d, 0, f; -c, -e, -f, 0]

/-- The primitive invariant form in Lemma 2.8. -/
def Q₀ : LatticeMatrix := alternatingMatrix 0 0 1 6 0 0

theorem T₁_preserves_Q₀ : T₁.transpose * Q₀ * T₁ = Q₀ := by decide
theorem T₂_preserves_Q₀ : T₂.transpose * Q₀ * T₂ = Q₀ := by decide

/-- The equations for a form invariant under both generators have exactly one
free integral parameter, its `γδ`-coefficient. -/
theorem invariant_alternating_iff (a b c d e f : ℤ) :
    (T₁.transpose * alternatingMatrix a b c d e f * T₁ =
        alternatingMatrix a b c d e f ∧
      T₂.transpose * alternatingMatrix a b c d e f * T₂ =
        alternatingMatrix a b c d e f) ↔
      a = 0 ∧ b = 0 ∧ e = 0 ∧ f = 0 ∧ d = 6 * c := by
  constructor
  · rintro ⟨h₁, h₂⟩
    have h₁₀₁ := congrFun (congrFun h₁ 0) 1
    have h₁₀₂ := congrFun (congrFun h₁ 0) 2
    have h₁₁₃ := congrFun (congrFun h₁ 1) 3
    have h₁₂₃ := congrFun (congrFun h₁ 2) 3
    have h₂₂₃ := congrFun (congrFun h₂ 2) 3
    simp [T₁, T₂, alternatingMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
      at h₁₀₁ h₁₀₂ h₁₁₃ h₁₂₃ h₂₂₃
    omega
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [T₁, T₂, alternatingMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem invariant_alternating_eq_multiple (a b c d e f : ℤ)
    (h₁ : T₁.transpose * alternatingMatrix a b c d e f * T₁ =
      alternatingMatrix a b c d e f)
    (h₂ : T₂.transpose * alternatingMatrix a b c d e f * T₂ =
      alternatingMatrix a b c d e f) :
    alternatingMatrix a b c d e f = c • Q₀ := by
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ :=
    (invariant_alternating_iff a b c d e f).mp ⟨h₁, h₂⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [alternatingMatrix, Q₀] <;> ring

/-- The form `b(x,y) = Q₀(x, Ny)` is symmetric. -/
theorem Q₀_mul_N_symmetric : (Q₀ * N).transpose = Q₀ * N := by decide

/-- On the quotient by `ker N`, the Gram matrix is `diag(6, -1)`. -/
theorem Q₀_mul_N_eq :
    Q₀ * N = !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 6, 0; 0, 0, 0, -1] := by
  decide

theorem quotient_form_discriminant : (Matrix.det !![(6 : ℤ), 0; 0, -1]) = -6 := by
  decide

end Wikipedia.HopfProblem
