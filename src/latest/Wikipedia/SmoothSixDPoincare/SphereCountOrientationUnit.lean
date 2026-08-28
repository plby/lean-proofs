import Wikipedia.SmoothSixDPoincare.SphereCountMarking

/-!
# The signed-count source marking sends the primitive top class to a unit

Both markings are actual integral homology equivalences. Their comparison
on the constructed sphere generator is therefore a unit of the integers;
no agreement of orientation conventions is assumed.
-/

noncomputable section

namespace Wikipedia.SmoothSixDPoincare

namespace HomologyTransport

theorem integerEquiv_one_natAbs (e : ℤ ≃ₗ[ℤ] ℤ) : (e 1).natAbs = 1 := by
  have h : e.symm 1 * e 1 = 1 := by
    calc
      e.symm 1 * e 1 = e (e.symm 1 • (1 : ℤ)) := by
        rw [map_zsmul, zsmul_eq_mul]
        simp
      _ = 1 := by simp
  exact Int.isUnit_iff_natAbs_eq.mp (IsUnit.of_mul_eq_one_right _ h)

end HomologyTransport

namespace SpherePoint

open Wikipedia.HopfProblem.SphereHomology

variable (n : ℕ) {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [FiniteDimensional ℝ N]
  (j : (ℝ × N) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
  (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] N)

omit [FiniteDimensional ℝ N] in
theorem sourceCountMark_topClass_natAbs :
    (sourceCountMark n j B (unitSphereTopClass (n + 1))).natAbs = 1 :=
  HomologyTransport.integerEquiv_one_natAbs
    ((unitSphereHomologyTopEquiv (n + 1)).symm.trans (sourceCountMark n j B))

end SpherePoint

end Wikipedia.SmoothSixDPoincare
