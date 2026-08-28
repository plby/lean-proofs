import Wikipedia.NoExoticSixSphere.SkewPlaneMixing
import Wikipedia.NoExoticSixSphere.SkewComplementRotationData
import Wikipedia.NoExoticSixSphere.HilbertSchmidtOrthogonalFamily

/-!
# A codimension-two family of mixing operators

Mixing a fixed rotation plane with an orthonormal spectral basis of its
complement gives a linearly independent family of actual skew operators.
Both this family and its commutator companions have squared Hilbert--Schmidt
norm four. The formulas below apply to every linear combination.
-/

namespace NoExoticSixSphere.SkewPlaneMixing

open GLOrthonormalization CayleyTransform HilbertSchmidt OrthogonalCommutator
  SkewRotationComplement

variable {n : ℕ} (K : SkewOperators n) {α : ℝ} {x y : Vector n}
  (hx : (K : Vector n →L[ℝ] Vector n) x = α • y)
  (hy : (K : Vector n →L[ℝ] Vector n) y = (-α) • x)
  (D : RotationData K hx hy)

noncomputable def mixingFamily (i : Fin (Module.finrank ℝ (complement x y))) :
    SkewOperators n := mixing x y (basis K hx hy i) (D.partner i)

noncomputable def companionFamily (i : Fin (Module.finrank ℝ (complement x y))) :
    SkewOperators n := companion x y (basis K hx hy i) (D.partner i)

theorem pairing_mixingFamily (hnx : ‖x‖ = 1) (hny : ‖y‖ = 1)
    (hxy : inner ℝ x y = 0) (i j : Fin (Module.finrank ℝ (complement x y))) :
    innerForm (mixingFamily K hx hy D i : Vector n →L[ℝ] Vector n)
      (mixingFamily K hx hy D j : Vector n →L[ℝ] Vector n) =
        if i = j then 4 else 0 := by
  rw [mixingFamily, mixingFamily, innerForm_mixing hnx hny hxy]
  change 2 * (inner ℝ (basis K hx hy i) (basis K hx hy j) +
    inner ℝ (D.partner i) (D.partner j)) = _
  by_cases hij : i = j
  · subst j
    norm_num [(basis K hx hy).orthonormal.norm_eq_one,
      D.orthonormal_partner.norm_eq_one]
  · rw [(basis K hx hy).orthonormal.inner_eq_zero hij,
      D.orthonormal_partner.inner_eq_zero hij, if_neg hij]
    norm_num

theorem pairing_companionFamily (hnx : ‖x‖ = 1) (hny : ‖y‖ = 1)
    (hxy : inner ℝ x y = 0) (i j : Fin (Module.finrank ℝ (complement x y))) :
    innerForm (companionFamily K hx hy D i : Vector n →L[ℝ] Vector n)
      (companionFamily K hx hy D j : Vector n →L[ℝ] Vector n) =
        if i = j then 4 else 0 := by
  rw [companionFamily, companionFamily, innerForm_companion hnx hny hxy]
  change 2 * (inner ℝ (basis K hx hy i) (basis K hx hy j) +
    inner ℝ (D.partner i) (D.partner j)) = _
  by_cases hij : i = j
  · subst j
    norm_num [(basis K hx hy).orthonormal.norm_eq_one,
      D.orthonormal_partner.norm_eq_one]
  · rw [(basis K hx hy).orthonormal.inner_eq_zero hij,
      D.orthonormal_partner.inner_eq_zero hij, if_neg hij]
    norm_num

theorem commutator_mixingFamily (i : Fin (Module.finrank ℝ (complement x y))) :
    commutator (K : Vector n →L[ℝ] Vector n)
      (mixingFamily K hx hy D i : Vector n →L[ℝ] Vector n) =
        (α + D.speed i) • (companionFamily K hx hy D i : Vector n →L[ℝ] Vector n) :=
  commutator_mixing K hx hy (D.map_basis i) (D.map_partner i)

noncomputable def mixingMap :
    (Fin (Module.finrank ℝ (complement x y)) → ℝ) →ₗ[ℝ] SkewOperators n where
  toFun c := ∑ i, c i • mixingFamily K hx hy D i
  map_add' c d := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

theorem mixingMap_coe (c : Fin (Module.finrank ℝ (complement x y)) → ℝ) :
    (mixingMap K hx hy D c : Vector n →L[ℝ] Vector n) =
      ∑ i, c i • (mixingFamily K hx hy D i : Vector n →L[ℝ] Vector n) := by
  exact map_sum (skewAdjoint.submodule ℝ (Vector n →L[ℝ] Vector n)).subtype _ _

theorem squareNorm_mixingMap (hnx : ‖x‖ = 1) (hny : ‖y‖ = 1)
    (hxy : inner ℝ x y = 0) (c : Fin (Module.finrank ℝ (complement x y)) → ℝ) :
    squareNorm (mixingMap K hx hy D c : Vector n →L[ℝ] Vector n) =
      4 * ∑ i, c i ^ 2 := by
  rw [mixingMap_coe]
  exact squareNorm_sum_orthogonal _ 4 (pairing_mixingFamily K hx hy D hnx hny hxy) c

theorem mixingMap_injective (hnx : ‖x‖ = 1) (hny : ‖y‖ = 1)
    (hxy : inner ℝ x y = 0) : Function.Injective (mixingMap K hx hy D) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro c hc
  apply (sum_orthogonal_eq_zero_iff _ (by norm_num : (0 : ℝ) < 4)
    (pairing_mixingFamily K hx hy D hnx hny hxy) c).mp
  rw [← mixingMap_coe, hc]
  rfl

theorem squareNorm_commutator_mixingMap (hnx : ‖x‖ = 1) (hny : ‖y‖ = 1)
    (hxy : inner ℝ x y = 0) (c : Fin (Module.finrank ℝ (complement x y)) → ℝ) :
    squareNorm (commutator (K : Vector n →L[ℝ] Vector n)
      (mixingMap K hx hy D c : Vector n →L[ℝ] Vector n)) =
        4 * ∑ i, (c i * (α + D.speed i)) ^ 2 := by
  rw [mixingMap_coe, commutator_sum_right]
  simp_rw [commutator_smul_right, commutator_mixingFamily, smul_smul]
  exact squareNorm_sum_orthogonal _ 4
    (pairing_companionFamily K hx hy D hnx hny hxy) _

end NoExoticSixSphere.SkewPlaneMixing
