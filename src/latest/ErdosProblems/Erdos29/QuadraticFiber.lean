import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.LinearCombination

/-!
# Quadratic fiber bounds

This file packages the elementary root-counting fact used in the modular
construction for Erdős Problem 29.  Its statements are deliberately phrased
using `Finset.univ.filter`, so that they can be applied directly to finite-field
representation counts.
-/

namespace Erdos29.QuadraticFiber

open Polynomial

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The finite set of roots of the displayed quadratic expression. -/
def quadraticRoots (a b c : K) : Finset K :=
  Finset.univ.filter fun x ↦ a * x ^ 2 + b * x + c = 0

/-- A genuinely quadratic polynomial over a finite field has at most two
distinct roots. -/
theorem quadraticRoots_card_le_two (a b c : K) (ha : a ≠ 0) :
    (quadraticRoots a b c).card ≤ 2 := by
  classical
  let P : K[X] := C a * X ^ 2 + C b * X + C c
  have hP : P ≠ 0 := by
    intro h
    have hcoeff := congrArg (fun Q : K[X] ↦ Q.coeff 2) h
    simp [P, ha] at hcoeff
  have hsubset : (quadraticRoots a b c).val ⊆ P.roots := by
    intro x hx
    rw [Polynomial.mem_roots hP]
    have hx' : a * x ^ 2 + b * x + c = 0 :=
      (Finset.mem_filter.mp hx).2
    simpa [P] using hx'
  calc
    (quadraticRoots a b c).card ≤ P.natDegree :=
      Polynomial.card_le_degree_of_subset_roots hsubset
    _ = 2 := Polynomial.natDegree_quadratic ha

/-- The same quadratic root bound without the helper-definition wrapper. -/
theorem univ_filter_quadratic_card_le_two (a b c : K) (ha : a ≠ 0) :
    (Finset.univ.filter fun x : K ↦ a * x ^ 2 + b * x + c = 0).card ≤ 2 := by
  simpa only [quadraticRoots] using quadraticRoots_card_le_two a b c ha

/-- The subtype of solutions of a nondegenerate quadratic equation has at
most two elements. -/
theorem fintypeCard_quadratic_solution_le_two (a b c : K) (ha : a ≠ 0) :
    Fintype.card {x : K // a * x ^ 2 + b * x + c = 0} ≤ 2 := by
  classical
  rw [Fintype.card_subtype]
  exact univ_filter_quadratic_card_le_two a b c ha

/-- Ordered pairs lying simultaneously on a line `x + y = u` and on the
diagonal quadratic curve `c*x² + d*y² = v`. -/
def lineQuadraticFiber (c d u v : K) : Finset (K × K) :=
  Finset.univ.filter fun xy ↦
    xy.1 + xy.2 = u ∧ c * xy.1 ^ 2 + d * xy.2 ^ 2 = v

/-- If `c + d` is nonzero, a line meets the diagonal quadratic curve in at
most two ordered pairs. -/
theorem lineQuadraticFiber_card_le_two (c d u v : K) (hcd : c + d ≠ 0) :
    (lineQuadraticFiber c d u v).card ≤ 2 := by
  classical
  let T : Finset K := quadraticRoots (c + d) (-2 * d * u) (d * u ^ 2 - v)
  have hmaps : Set.MapsTo Prod.fst (lineQuadraticFiber c d u v : Set (K × K))
      (T : Set K) := by
    intro xy hxy
    have hxy' := (Finset.mem_filter.mp hxy).2
    have hsum : xy.1 + xy.2 = u := hxy'.1
    have hcurve : c * xy.1 ^ 2 + d * xy.2 ^ 2 = v := hxy'.2
    have hy : xy.2 = u - xy.1 := eq_sub_of_add_eq' hsum
    simp only [T, quadraticRoots, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [hy] at hcurve
    linear_combination hcurve
  have hinj : Set.InjOn Prod.fst (lineQuadraticFiber c d u v : Set (K × K)) := by
    intro xy hxy zw hzw hfst
    have hsumxy : xy.1 + xy.2 = u := ((Finset.mem_filter.mp hxy).2).1
    have hsumzw : zw.1 + zw.2 = u := ((Finset.mem_filter.mp hzw).2).1
    apply Prod.ext hfst
    rw [eq_sub_of_add_eq' hsumxy, eq_sub_of_add_eq' hsumzw, hfst]
  calc
    (lineQuadraticFiber c d u v).card ≤ T.card :=
      Finset.card_le_card_of_injOn Prod.fst hmaps hinj
    _ ≤ 2 := by
      simpa only [T] using
        quadraticRoots_card_le_two (c + d) (-2 * d * u) (d * u ^ 2 - v) hcd

/-- The pair-fiber estimate stated directly for an unwrapped filter. -/
theorem univ_filter_line_quadratic_card_le_two (c d u v : K) (hcd : c + d ≠ 0) :
    (Finset.univ.filter fun xy : K × K ↦
      xy.1 + xy.2 = u ∧ c * xy.1 ^ 2 + d * xy.2 ^ 2 = v).card ≤ 2 := by
  simpa only [lineQuadraticFiber] using lineQuadraticFiber_card_le_two c d u v hcd

/-- The subtype form of the line--quadratic fiber estimate. -/
theorem fintypeCard_line_quadratic_solution_le_two (c d u v : K) (hcd : c + d ≠ 0) :
    Fintype.card {xy : K × K //
      xy.1 + xy.2 = u ∧ c * xy.1 ^ 2 + d * xy.2 ^ 2 = v} ≤ 2 := by
  classical
  rw [Fintype.card_subtype]
  exact univ_filter_line_quadratic_card_le_two c d u v hcd

end Erdos29.QuadraticFiber
