/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Eliminating one coordinate from the sextic surface and an auxiliary equation.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.SurfaceIrreducible
import ErdosProblems.Erdos477.Geometry.ResultantNonzero
import ErdosProblems.Erdos477.Geometry.MultivariateResultant

namespace Erdos477.Geometry

open scoped Polynomial

variable {K : Type*} [Field K]

lemma eval_finSuccEquiv_three (P : MvPolynomial (Fin 3) K) (z : Fin 3 → K) :
    Polynomial.eval₂ (MvPolynomial.eval ![z 1, z 2]) (z 0)
      (MvPolynomial.finSuccEquiv K 2 P) = MvPolynomial.eval z P := by
  have h := MvPolynomial.eval_eq_eval_mv_eval' ![z 1, z 2] (z 0) P
  rw [Polynomial.eval_map] at h
  have hvec : Fin.cons (z 0) ![z 1, z 2] = z := by
    ext i
    fin_cases i <;> rfl
  rw [hvec] at h
  exact h.symm

/-- Projection of the intersection lies on a nonzero plane polynomial of
degree at most six times the auxiliary degree. No intersection theorem is
used to obtain this eliminant. -/
theorem exists_sextic_plane_eliminant [CharZero K] [IsAlgClosed K]
    (c : K) (hc : c ≠ 0) (P : MvPolynomial (Fin 3) K)
    (hP : ¬ sexticSurface c ∣ P) :
    ∃ Q : MvPolynomial (Fin 2) K, Q ≠ 0 ∧ Q.totalDegree ≤ 6 * P.totalDegree ∧
      ∀ z : Fin 3 → K, MvPolynomial.eval z (sexticSurface c) = 0 →
        MvPolynomial.eval z P = 0 → MvPolynomial.eval ![z 1, z 2] Q = 0 := by
  let e := MvPolynomial.finSuccEquiv K 2
  let f := e (sexticSurface c)
  let g := e P
  have hf : Irreducible f := (MulEquiv.irreducible_iff e).mpr (irreducible_sexticSurface c hc)
  have hfg : ¬ f ∣ g := by
    intro h
    apply hP
    simpa only [f, g, AlgEquiv.symm_apply_apply] using map_dvd e.symm h
  have hfdeg : f.natDegree = 6 := by
    change (MvPolynomial.finSuccEquiv K 2 (sexticSurface c)).natDegree = 6
    rw [finSuccEquiv_sexticSurface, Polynomial.natDegree_X_pow_sub_C]
  have hgdeg : g.natDegree ≤ P.totalDegree := by
    rw [MvPolynomial.natDegree_finSuccEquiv]
    exact MvPolynomial.degreeOf_le_totalDegree P 0
  have hfweight (j) (hj : f.coeff j ≠ 0) : (f.coeff j).totalDegree + j ≤ 6 :=
    (MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le (sexticSurface c) j hj).trans
      (totalDegree_sexticSurface_le c)
  have hgweight (j) (hj : g.coeff j ≠ 0) :
      (g.coeff j).totalDegree + j ≤ P.totalDegree :=
    MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le P j hj
  refine ⟨f.resultant g, resultant_ne_zero_of_irreducible_not_dvd f g hf hfg,
    totalDegree_resultant_le f g f.natDegree g.natDegree 6 P.totalDegree
      hfdeg.le hgdeg hfweight hgweight, ?_⟩
  intro z hz hPz
  obtain ⟨A, B, _, _, hAB⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant f g le_rfl le_rfl
    (Or.inl (by rw [hfdeg]; decide))
  let φ := Polynomial.eval₂RingHom (MvPolynomial.eval ![z 1, z 2]) (z 0)
  have hfz : φ f = 0 := (eval_finSuccEquiv_three (sexticSurface c) z).trans hz
  have hgz : φ g = 0 := (eval_finSuccEquiv_three P z).trans hPz
  have h := congrArg φ hAB
  simp only [map_add, map_mul, hfz, hgz, zero_mul, add_zero] at h
  simpa only [φ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C] using h.symm

#print axioms exists_sextic_plane_eliminant
-- 'Erdos477.Geometry.exists_sextic_plane_eliminant' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
