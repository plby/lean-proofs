import ErdosProblems.Erdos121.Weighted

/-!
# The complete graph on five vertices

The ten coordinates below enumerate the edges
`01, 02, 03, 04, 12, 13, 14, 23, 24, 34`.  Writing the five incident-edge
products explicitly keeps the later analytic construction independent of a
large graph library while retaining the exact `K₅` identity used by Tao.
-/

open scoped BigOperators

namespace Erdos121

set_option autoImplicit false

/-- The five products of the edge labels incident to each vertex of `K₅`. -/
def k5Tuple (f : Fin 10 → ℕ) : Fin 5 → ℕ :=
  ![f 0 * f 1 * f 2 * f 3,
    f 0 * f 4 * f 5 * f 6,
    f 1 * f 4 * f 7 * f 8,
    f 2 * f 5 * f 7 * f 9,
    f 3 * f 6 * f 8 * f 9]

/-- Every edge label occurs at its two endpoints, so the product of the five
vertex labels is the square of the product of all ten edge labels. -/
theorem prod_k5Tuple (f : Fin 10 → ℕ) :
    (∏ i, k5Tuple f i) = (∏ e, f e) ^ 2 := by
  simp [k5Tuple, Fin.prod_univ_succ]
  ring

theorem isSquare_prod_k5Tuple (f : Fin 10 → ℕ) :
    IsSquare (∏ i, k5Tuple f i) := by
  rw [prod_k5Tuple]
  exact IsSquare.sq _

end Erdos121
