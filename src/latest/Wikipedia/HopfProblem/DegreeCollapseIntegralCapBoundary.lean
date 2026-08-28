import Wikipedia.HopfProblem.DegreeCollapseIntegralCapChains

/-!
# The signed integral cap boundary identity

Evaluate against arbitrary original cochains and use the checked integral
cup Leibniz identity. The original simplex basis separates chains, so the
result is an equality of actual integral chains, with its sign retained.
The two consequences below provide cycle and boundary witnesses needed
for the relative cap map.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCap

open FirstHurewicz SingularCohomologyCup

variable {X : Type} [TopologicalSpace X]

theorem cap_boundary (p q : ℕ) (α : Cochain X p) (c : Chains X (p + q + 1)) :
    capInDegree rfl α (((singularComplex X).d (p + q + 1) (p + q)).hom c) =
      capInDegree (p := p + 1) (q := q) (by omega) (coboundary α) c +
        (-1 : ℤ) ^ p • ((singularComplex X).d (q + 1) q).hom
          (capInDegree (p := p) (q := q + 1) (by omega) α c) := by
  apply chain_eq_of_evaluation q
  intro β
  calc
    _ = coboundary (cup α β) c := by rw [evaluate_cap]; rfl
    _ = cupInDegree (by omega) (coboundary α) β c +
        (-1 : ℤ) ^ p * cup α (coboundary β) c := by
      have he := LinearMap.congr_fun (coboundary_cup α β) c
      simpa only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] using he
    _ = β (capInDegree (p := p + 1) (q := q) (by omega) (coboundary α) c) +
        (-1 : ℤ) ^ p * coboundary β
          (capInDegree (p := p) (q := q + 1) (by omega) α c) := by
      rw [evaluate_cap, evaluate_cap]
      rfl
    _ = _ := by
      rw [map_add, map_zsmul]
      rfl

theorem sign_mul_self (p : ℕ) : (-1 : ℤ) ^ p * (-1 : ℤ) ^ p = 1 := by
  rw [← mul_pow]
  simp

theorem boundary_cap_closed (p q : ℕ) (α : Cochain X p) (hα : coboundary α = 0)
    (c : Chains X (p + q + 1)) :
    ((singularComplex X).d (q + 1) q).hom
      (capInDegree (p := p) (q := q + 1) (by omega) α c) =
        (-1 : ℤ) ^ p • capInDegree rfl α
          (((singularComplex X).d (p + q + 1) (p + q)).hom c) := by
  have he := cap_boundary p q α c
  rw [hα, capInDegree_zero, LinearMap.zero_apply, zero_add] at he
  have hs := congrArg (fun z : Chains X q ↦ (-1 : ℤ) ^ p • z) he
  rw [← mul_zsmul, sign_mul_self, one_zsmul] at hs
  exact hs.symm

theorem cap_is_cycle_of_boundary_killed (p q : ℕ) (α : Cochain X p)
    (hα : coboundary α = 0) (c : Chains X (p + q + 1))
    (hc : capInDegree rfl α (((singularComplex X).d (p + q + 1) (p + q)).hom c) = 0) :
    ((singularComplex X).d (q + 1) q).hom
      (capInDegree (p := p) (q := q + 1) (by omega) α c) = 0 := by
  rw [boundary_cap_closed p q α hα c, hc, zsmul_zero]

/-- A relative coboundary caps to this explicit absolute boundary whenever
the lower relative cochain kills the ambient boundary chain. -/
theorem cap_coboundary_boundary (p q : ℕ) (α : Cochain X p) (c : Chains X (p + q + 1))
    (hc : capInDegree rfl α (((singularComplex X).d (p + q + 1) (p + q)).hom c) = 0) :
    capInDegree (p := p + 1) (q := q) (by omega) (coboundary α) c =
      ((singularComplex X).d (q + 1) q).hom
        (-((-1 : ℤ) ^ p) • capInDegree (p := p) (q := q + 1) (by omega) α c) := by
  have he := cap_boundary p q α c
  rw [hc] at he
  rw [map_zsmul, neg_zsmul]
  exact eq_neg_of_add_eq_zero_left he.symm

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCap
