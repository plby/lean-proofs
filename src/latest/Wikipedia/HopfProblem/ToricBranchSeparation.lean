import Wikipedia.HopfProblem.ToricDivisors

/-!
# Separation within a fixed central branch stratum

A nonempty finite set of lattice vertices cannot be invariant under a
nonzero translation. Consequently a twisted lattice translate between
central points with identical branch vertices must use the zero lattice
element. This rules out extra quotient identifications along an affine
axis once its zero pattern is fixed.
-/

noncomputable section

open Set
open scoped BigOperators

namespace Wikipedia.HopfProblem.ToricSpace

theorem finite_image_add_eq_self {S : Set (Fin 2 → ℤ)} (hS : S.Finite) (hne : S.Nonempty)
    (v : Fin 2 → ℤ) (h : (fun w => w + v) '' S = S) : v = 0 := by
  classical
  let A := hS.toFinset
  have hA : A.image (fun w => w + v) = A := by
    apply Finset.coe_injective
    simpa [A] using h
  have hsum := congrArg (fun B : Finset (Fin 2 → ℤ) => ∑ w ∈ B, w) hA
  rw [Finset.sum_image (fun _ _ _ _ he => add_right_cancel he),
    Finset.sum_add_distrib, Finset.sum_const] at hsum
  have hv : A.card • v = 0 := by simpa using hsum
  have hc : (A.card : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Finset.card_ne_zero.mpr (by simpa [A] using hne))
  ext i
  have hi : (A.card : ℤ) * v i = 0 := by
    simpa only [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply] using congrFun hv i
  exact (mul_eq_zero.mp hi).resolve_left hc

theorem twistedTranslate_eq_of_branchVertices_eq
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) (x y : Space)
    (hx : time x = 0) (hbranches : branchVertices x = branchVertices y)
    (he : twistedTranslate C v x = y) : v = 0 := by
  have h := congrArg branchVertices he
  rw [branchVertices_twistedTranslate, ← hbranches] at h
  have hv := finite_image_add_eq_self (branchVertices_finite x)
    ((branchVertices_nonempty x).mpr hx) (cuspVector v) h
  ext i
  fin_cases i
  · simpa [cuspVector] using congrFun hv 1
  · simpa [cuspVector] using congrFun hv 0

end Wikipedia.HopfProblem.ToricSpace

namespace Wikipedia.HopfProblem.ToricFan.Triangle

open ToricCharts

theorem chartBranches_eq_of_zero_iff (s : Triangle) (z w : CoordinateSpace 3)
    (h : ∀ j, z j = 0 ↔ w j = 0) : chartBranches s z = chartBranches s w := by
  unfold chartBranches
  congr 1
  exact Set.ext h

end Wikipedia.HopfProblem.ToricFan.Triangle
