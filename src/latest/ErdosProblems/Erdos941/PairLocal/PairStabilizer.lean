/- Adapted from the checked repository proof in Erdos1148/PairStabilizer.lean. -/
import ErdosProblems.Erdos941.PairLocal.FrameCongruence

/-!
# Trivial stabilizers of nondegenerate pairs

The local-to-global counting reduction uses the fact that a determinant-one
isometry fixing both columns of a nondegenerate embedding is the identity.
For the discriminant form, this follows from the explicit normal vector.
-/

namespace Erdos941.PairLocal

def matrixOfCoeffMap {R : Type*} [CommRing R] (f : (R × R × R) →ₗ[R] (R × R × R)) :
    Matrix (Fin 3) (Fin 3) R :=
  LinearMap.toMatrix' ((coeffVecEquiv R).toLinearMap.comp
    (f.comp (coeffVecEquiv R).symm.toLinearMap))

lemma coeffMatrixMap_matrixOfCoeffMap {R : Type*} [CommRing R]
    (f : (R × R × R) →ₗ[R] (R × R × R)) : coeffMatrixMap (matrixOfCoeffMap f) = f := by
  apply LinearMap.ext
  intro t
  simp [matrixOfCoeffMap, coeffMatrixMap]

lemma det_matrixOfCoeffMap {R : Type*} [CommRing R]
    (f : (R × R × R) →ₗ[R] (R × R × R)) : (matrixOfCoeffMap f).det = LinearMap.det f := by
  rw [← det_coeffMatrixMap, coeffMatrixMap_matrixOfCoeffMap]

def tripleFrame {R : Type*} [CommRing R] (t u v : R × R × R) : Matrix (Fin 3) (Fin 3) R :=
  !![t.1, u.1, v.1; t.2.1, u.2.1, v.2.1; t.2.2, u.2.2, v.2.2]

lemma tripleFrame_coeffMatrixMap {R : Type*} [CommRing R]
    (M : Matrix (Fin 3) (Fin 3) R) (t u v : R × R × R) :
    tripleFrame (coeffMatrixMap M t) (coeffMatrixMap M u) (coeffMatrixMap M v) =
      M * tripleFrame t u v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tripleFrame, coeffMatrixMap, coeffVecEquiv_apply, coeffVecEquiv_symm_apply,
      Matrix.toLin'_apply, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.mulVec, dotProduct]

lemma det_tripleFrame_map {R : Type*} [CommRing R]
    (f : (R × R × R) →ₗ[R] (R × R × R)) (t u v : R × R × R) :
    (tripleFrame (f t) (f u) (f v)).det = LinearMap.det f * (tripleFrame t u v).det := by
  have h (w : R × R × R) : coeffMatrixMap (matrixOfCoeffMap f) w = f w :=
    congrArg (fun F : (R × R × R) →ₗ[R] (R × R × R) => F w) (coeffMatrixMap_matrixOfCoeffMap f)
  rw [← h t, ← h u, ← h v, tripleFrame_coeffMatrixMap, Matrix.det_mul, det_matrixOfCoeffMap]

lemma pairing_normal_tripleFrame {R : Type*} [CommRing R] (t u v : R × R × R) :
    pairing (pairNormal t u) v = -4 * (tripleFrame t u v).det := by
  simp [tripleFrame, Matrix.det_fin_three, pairNormal, pairing]
  ring

lemma eq_of_pairing_eq {R : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R]
    {t u : R × R × R} (h : ∀ v, pairing t v = pairing u v) : t = u := by
  have ha : (-4 : R) * t.1 = (-4 : R) * u.1 := by
    have hv := h (0, 0, 1)
    dsimp [pairing] at hv
    linear_combination hv
  have hb : (2 : R) * t.2.1 = (2 : R) * u.2.1 := by
    have hv := h (0, 1, 0)
    dsimp [pairing] at hv
    linear_combination hv
  have hc : (-4 : R) * t.2.2 = (-4 : R) * u.2.2 := by
    have hv := h (1, 0, 0)
    dsimp [pairing] at hv
    linear_combination hv
  exact Prod.ext (mul_left_cancel₀ (by norm_num : (-4 : R) ≠ 0) ha)
    (Prod.ext (mul_left_cancel₀ (by norm_num : (2 : R) ≠ 0) hb)
      (mul_left_cancel₀ (by norm_num : (-4 : R) ≠ 0) hc))

lemma pairNormal_specialDiscrGroup {R : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R]
    (g : specialDiscrGroup R) (t u : R × R × R) :
    g.1 (pairNormal t u) = pairNormal (g.1 t) (g.1 u) := by
  apply eq_of_pairing_eq
  intro w
  obtain ⟨v, rfl⟩ := g.1.surjective w
  rw [pairing_linearEquiv g.1 g.2.1, pairing_normal_tripleFrame, pairing_normal_tripleFrame]
  have hdet := det_tripleFrame_map g.1.toLinearMap t u v
  change (tripleFrame (g.1 t) (g.1 u) (g.1 v)).det =
    LinearMap.det g.1.toLinearMap * (tripleFrame t u v).det at hdet
  rw [g.2.2, one_mul] at hdet
  rw [hdet]

theorem specialDiscrGroup_eq_one_of_fix_pair {R : Type*} [CommRing R]
    [NoZeroDivisors R] [CharZero R] {d ℓ : R} (p : FormPair R d ℓ)
    (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) (g : specialDiscrGroup R)
    (ht : g.1 p.1.1 = p.1.1) (hu : g.1 p.1.2 = p.1.2) : g = 1 := by
  have hnormal : g.1 (pairNormal p.1.1 p.1.2) = pairNormal p.1.1 p.1.2 := by
    rw [pairNormal_specialDiscrGroup, ht, hu]
  let P := pairFrame p.1.1 p.1.2
  have hframe (v : R × R × R) : g.1 (coeffMatrixMap P v) = coeffMatrixMap P v := by
    rw [coeffMatrixMap_pairFrame, map_add, map_add, map_smul, map_smul, map_smul, ht, hu, hnormal]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro t
  have hscale : coeffMatrixMap P (coeffMatrixMap P.adjugate t) = P.det • t := by
    rw [← LinearMap.comp_apply, ← coeffMatrixMap_mul, Matrix.mul_adjugate,
      coeffMatrixMap_smul_one]
  have hfix := hframe (coeffMatrixMap P.adjugate t)
  rw [hscale, map_smul] at hfix
  have hP : P.det ≠ 0 := det_pairFrame_ne_zero p hnd
  exact Prod.ext (mul_left_cancel₀ hP (congrArg Prod.fst hfix))
    (Prod.ext (mul_left_cancel₀ hP (congrArg (fun v => v.2.1) hfix))
      (mul_left_cancel₀ hP (congrArg (fun v => v.2.2) hfix)))

theorem specialPairAction_free {R : Type*} [CommRing R]
    [NoZeroDivisors R] [CharZero R] {d ℓ : R} (p : FormPair R d ℓ)
    (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) (g : specialDiscrGroup R) (hg : g • p = p) : g = 1 :=
  specialDiscrGroup_eq_one_of_fix_pair p hnd g
    (congrArg (fun q : FormPair R d ℓ => q.1.1) hg)
    (congrArg (fun q : FormPair R d ℓ => q.1.2) hg)

lemma specialPairAction_left_injective {R : Type*} [CommRing R]
    [NoZeroDivisors R] [CharZero R] {d ℓ : R} (p : FormPair R d ℓ)
    (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) : Function.Injective (fun g : specialDiscrGroup R => g • p) := by
  intro g h hgh
  dsimp only at hgh
  have hfix : (h⁻¹ * g) • p = p := by rw [mul_smul, hgh, inv_smul_smul]
  have heq := specialPairAction_free p hnd (h⁻¹ * g) hfix
  exact (inv_mul_eq_one.mp heq).symm

lemma specialDiscrGroup_ext_of_pair {R : Type*} [CommRing R]
    [NoZeroDivisors R] [CharZero R] {d ℓ : R} (p : FormPair R d ℓ)
    (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) (g h : specialDiscrGroup R)
    (ht : g.1 p.1.1 = h.1 p.1.1) (hu : g.1 p.1.2 = h.1 p.1.2) : g = h := by
  apply specialPairAction_left_injective p hnd
  apply Subtype.ext
  exact Prod.ext ht hu

end Erdos941.PairLocal
