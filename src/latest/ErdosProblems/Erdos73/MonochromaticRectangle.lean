import ErdosProblems.Erdos73.OrderedFiniteSelection

/-! A Boolean rectangular array has a large monochromatic subrectangle. -/

namespace Erdos73
noncomputable section
open scoped Classical

open Finset

theorem exists_monochromatic_rectangle {I J : Type*} [Fintype I] [Fintype J]
    (color : I → J → Bool) (m n : ℕ)
    (hcolumns : 2 * n ≤ Fintype.card J)
    (hrows : 2 ^ Fintype.card J * m ≤ Fintype.card I) :
    ∃ A : Finset I, ∃ B : Finset J, ∃ b : Bool,
      m ≤ A.card ∧ n ≤ B.card ∧ ∀ i ∈ A, ∀ j ∈ B, color i j = b := by
  obtain ⟨pattern, A, _, hA, hpattern⟩ := exists_large_finite_fiber univ color m
    (by simpa only [card_univ, Fintype.card_fun, Fintype.card_bool] using hrows)
  obtain ⟨b, B, _, hB, hcolor⟩ := exists_large_finite_fiber univ pattern n
    (by simpa only [card_univ, Fintype.card_bool] using hcolumns)
  refine ⟨A, B, b, hA, hB, ?_⟩
  intro i hi j hj
  exact (congrFun (hpattern i hi) j).trans (hcolor j hj)

end
end Erdos73
