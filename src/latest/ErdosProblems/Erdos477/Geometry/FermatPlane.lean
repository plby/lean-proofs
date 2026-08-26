/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The irreducible plane curves arising in nonzero vertical sextic fibers.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.SurfaceIrreducible
import ErdosProblems.Erdos477.Counting.PlaneCurveBound

namespace Erdos477.Geometry

variable {K : Type*} [Field K]

noncomputable def sixthSumCurve (c : K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.X 0 ^ 6 + MvPolynomial.X 1 ^ 6 - MvPolynomial.C c

lemma finSuccEquiv_sixthSumCurve (c : K) :
    MvPolynomial.finSuccEquiv K 1 (sixthSumCurve c) =
      Polynomial.X ^ 6 - Polynomial.C
        (MvPolynomial.C c - MvPolynomial.X (0 : Fin 1) ^ 6) := by
  simp only [sixthSumCurve, MvPolynomial.finSuccEquiv_apply,
    MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, Fin.cases_zero, MvPolynomial.eval₂_C,
    RingHom.coe_comp, Function.comp_apply, map_add, map_sub, map_pow]
  change Polynomial.X ^ 6 + Polynomial.C (MvPolynomial.X (0 : Fin 1)) ^ 6 -
    Polynomial.C (MvPolynomial.C c) = _
  ring

theorem irreducible_sixthSumCurve [CharZero K] [IsAlgClosed K] (c : K) (hc : c ≠ 0) :
    Irreducible (sixthSumCurve c) := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq c (by decide : 0 < 6)
  have ha0 : a ≠ 0 := by intro h; rw [h, zero_pow (by decide)] at ha; exact hc ha.symm
  let g : MvPolynomial (Fin 1) K := MvPolynomial.C c - MvPolynomial.X 0 ^ 6
  have hg : MvPolynomial.eval (fun _ => a) g = 0 := by simp [g, ha]
  have hderiv : MvPolynomial.eval (fun _ => a) (MvPolynomial.pderiv 0 g) ≠ 0 := by
    have h6 : (6 : K) ≠ 0 := by norm_num
    simpa [g, MvPolynomial.pderiv_pow] using neg_ne_zero.mpr (mul_ne_zero h6 (pow_ne_zero 5 ha0))
  have h := irreducible_X_pow_sub_of_simple_zero g (fun _ => a) hg 0 hderiv 6 (by decide)
  rw [← finSuccEquiv_sixthSumCurve c] at h
  exact (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv K 1)).mp h

lemma degreeOf_sixthSumCurve_zero (c : K) : (sixthSumCurve c).degreeOf 0 = 6 := by
  rw [← MvPolynomial.natDegree_finSuccEquiv, finSuccEquiv_sixthSumCurve]
  exact Polynomial.natDegree_X_pow_sub_C

lemma totalDegree_sixthSumCurve (c : K) : (sixthSumCurve c).totalDegree = 6 := by
  apply le_antisymm
  · apply (MvPolynomial.totalDegree_sub_C_le _ c).trans
    exact (MvPolynomial.totalDegree_add _ _).trans (by simp)
  · rw [← degreeOf_sixthSumCurve_zero c]
    exact MvPolynomial.degreeOf_le_totalDegree _ _

theorem exists_sixth_sum_point_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℤ, k ≠ 0 → ∀ B : ℝ, 1 ≤ B →
      ∀ S : Finset (Fin 2 → ℤ), (∀ z ∈ S, z 0 ^ 6 + z 1 ^ 6 = k) →
      (∀ z ∈ S, ∀ i, |(z i : ℝ)| ≤ B) →
      (S.card : ℝ) ≤ C * B ^ ((1 : ℝ) / 6 + ε) := by
  obtain ⟨C, hC, hbound⟩ := Counting.exists_plane_curve_bound (K := ℂ) 6 (by decide) ε hε
  refine ⟨C, hC, ?_⟩
  intro k hk B hB S hS hheight
  apply hbound B hB (sixthSumCurve (k : ℂ))
    (irreducible_sixthSumCurve _ (by exact_mod_cast hk)) (totalDegree_sixthSumCurve _) S _ hheight
  intro z hz
  have h : (z 0 : ℂ) ^ 6 + (z 1 : ℂ) ^ 6 = k := by exact_mod_cast hS z hz
  simpa [sixthSumCurve] using sub_eq_zero.mpr h

#print axioms exists_sixth_sum_point_bound
-- 'Erdos477.Geometry.exists_sixth_sum_point_bound' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
