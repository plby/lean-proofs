import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSpectralTheorem

/-!
# Odd quaternionic spectral speeds at the antipodal endpoint

An actual symplectic logarithm of the antipode has a unitary diagonalization
whose entries are positive odd multiples of `π i`. Outside the minimum locus,
the first diagonal speed can be chosen at least `3π`. These statements concern
the original matrix coefficients and their genuine real exponential.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.SkewSpectralPlane
open NoExoticSixSphere.SkewRotationExponential

local notation "ℍ" => Quaternion ℝ

variable {n : ℕ}

theorem antipodal_i_eigenvalue_odd (K : SkewSpace n)
    (hexp : (Exponential.exp K).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    {α : ℝ} {v : Vector (4 * n + 4)} (hα : 0 ≤ α) (hv : ‖v‖ = 1)
    (he : K.val v = α • rightAction n QuaternionicScalars.i v) :
    ∃ m : ℕ, α = (2 * (m : ℝ) + 1) * Real.pi := by
  have hv0 : v ≠ 0 := by
    intro h
    exact zero_ne_one (by simpa only [h, norm_zero] using hv)
  have ha0 : α ≠ 0 := by
    intro ha
    have hKv : K.val v = 0 := by simpa only [ha, zero_smul] using he
    exact hv0 (NoExoticSixSphere.SkewAntipodalSpectrum.ker_eq_zero
      (toOrthogonalSkew n K) hexp hKv)
  have hpos : 0 < α := lt_of_le_of_ne hα (Ne.symm ha0)
  have hcomm : K.val (rightAction n QuaternionicScalars.i v) =
      rightAction n QuaternionicScalars.i (K.val v) :=
    DFunLike.congr_fun ((mem_commutant_iff n K.val).mp K.property.2 QuaternionicScalars.i) v
  have hsquare : rightAction n QuaternionicScalars.i (rightAction n QuaternionicScalars.i v) =
      -v := DFunLike.congr_fun (rightAction_i_square n) v
  have hKy : K.val (rightAction n QuaternionicScalars.i v) = (-α) • v := by
    rw [hcomm, he, map_smul, hsquare, smul_neg, neg_smul]
  have hxy : inner ℝ v (rightAction n QuaternionicScalars.i v) = 0 := by
    have hz := NoExoticSixSphere.CayleyTransform.inner_skew_self (toOrthogonalSkew n K) v
    change inner ℝ v (K.val v) = 0 at hz
    rw [he, inner_smul_right] at hz
    exact (mul_eq_zero.mp hz).resolve_left ha0
  exact speed_eq_odd_pi hpos
    (cos_speed_eq_neg_one (toOrthogonalSkew n K) he hKy hv hxy hexp)

theorem diagonalization_eigenColumn {N : Type*} [Fintype N] [DecidableEq N]
    (U : SpGroup N) (A : Matrix N N ℍ) (d : N → ℍ)
    (hd : conjugateMatrix U A = Matrix.diagonal d) (a : N) :
    A *ᵥ (column a U).val = fun b => (column a U).val b * d a := by
  have hm : A * U.val = U.val * Matrix.diagonal d := by
    calc
      A * U.val = U.val * conjugateMatrix U A := by
        rw [conjugateMatrix, ← mul_assoc, ← mul_assoc,
          Unitary.mul_star_self_of_mem U.property, one_mul]
      _ = _ := congrArg (fun M : Matrix N N ℍ => U.val * M) hd
  funext b
  have hb := congrArg (fun M : Matrix N N ℍ => M b a) hm
  exact hb.trans (Matrix.mul_diagonal d U.val b a)

theorem real_i_eigenvector_of_unit_column
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) (u : UnitColumn (Fin (n + 1))) (α : ℝ)
    (he : A *ᵥ u.val = fun a => u.val a * (α • QuaternionicScalars.i)) :
    realAction n A (quaternionCoordinates n (WithLp.toLp 2 u.val)) =
      α • rightAction n QuaternionicScalars.i (quaternionCoordinates n (WithLp.toLp 2 u.val)) := by
  rw [realAction_apply, rightAction_apply, (quaternionCoordinates n).symm_apply_apply,
    WithLp.ofLp_toLp, he, ← map_smul]
  apply congrArg (quaternionCoordinates n)
  apply (WithLp.equiv 2 (Fin (n + 1) → ℍ)).injective
  funext a
  change u.val a * (α • QuaternionicScalars.i) = α • (u.val a * QuaternionicScalars.i)
  exact mul_smul_comm _ _ _

theorem nonnegative_diagonalization_odd (K : SkewSpace n)
    (hexp : (Exponential.exp K).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (U : SpGroup (Fin (n + 1))) (α : Fin (n + 1) → ℝ) (hα : ∀ a, 0 ≤ α a)
    (hd : conjugateMatrix U (coefficients n K.val) =
      Matrix.diagonal (fun a => α a • QuaternionicScalars.i)) :
    ∀ a, ∃ m : ℕ, α a = (2 * (m : ℝ) + 1) * Real.pi := by
  intro a
  let u := column a U
  let v := quaternionCoordinates n (WithLp.toLp 2 u.val)
  have hv : ‖v‖ = 1 := by
    rw [(quaternionCoordinates n).norm_map]
    exact (pairing_self_eq_one_iff_norm u.val).mp u.property
  have he : K.val v = α a • rightAction n QuaternionicScalars.i v := by
    rw [← realAction_coefficients n K.val K.property.2]
    exact real_i_eigenvector_of_unit_column _ u (α a)
      (diagonalization_eigenColumn U _ _ hd a)
  exact antipodal_i_eigenvalue_odd K hexp (hα a) hv he

/-- Every antipodal symplectic generator has positive odd quaternionic spectral speeds. -/
theorem exists_antipodal_diagonalization (K : SkewSpace n)
    (hexp : (Exponential.exp K).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))) :
    ∃ (U : SpGroup (Fin (n + 1))) (m : Fin (n + 1) → ℕ),
      conjugateMatrix U (coefficients n K.val) =
        Matrix.diagonal (fun a => (((2 * (m a : ℝ) + 1) * Real.pi) • QuaternionicScalars.i)) := by
  obtain ⟨U, α, hα, hd⟩ := exists_unitary_diagonalization (n + 1)
    (coefficients n K.val) (coefficients_skew K)
  choose m hm using nonnegative_diagonalization_odd K hexp U α hα hd
  refine ⟨U, m, ?_⟩
  simpa only [hm] using hd

/-- Outside the minimum locus, a fast odd spectral speed may occupy the first coordinate. -/
theorem exists_fast_antipodal_diagonalization (K : SkewSpace n)
    (hexp : (Exponential.exp K).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (hnot : gram (toOrthogonalSkew n K) ≠
      Real.pi ^ 2 • (1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))) :
    ∃ (U : SpGroup (Fin (n + 1))) (m : Fin (n + 1) → ℕ), 1 ≤ m 0 ∧
      conjugateMatrix U (coefficients n K.val) =
        Matrix.diagonal (fun a => (((2 * (m a : ℝ) + 1) * Real.pi) • QuaternionicScalars.i)) := by
  obtain ⟨α, U, hα, h00, hc⟩ := exists_fast_eigenframe K hexp hnot
  let B := lowerBlock (conjugateMatrix U (coefficients n K.val))
  have hB : star B = -B := lowerBlock_skew _ (conjugateMatrix_skew U _ (coefficients_skew K))
  have hs : conjugateMatrix U (coefficients n K.val) = splitMatrix (α • QuaternionicScalars.i) B :=
    splitMatrix_eq_of_entries _ _ h00 hc
  obtain ⟨V, β, hβ, hdβ⟩ := exists_unitary_diagonalization n B hB
  let W := U * stabilization n V
  let γ : Fin (n + 1) → ℝ := Fin.cons α β
  have hγ : ∀ a, 0 ≤ γ a := by
    intro a
    cases a using Fin.cases
    · exact le_trans (by positivity : (0 : ℝ) ≤ 3 * Real.pi) hα
    · exact hβ _
  have hdγ : conjugateMatrix W (coefficients n K.val) =
      Matrix.diagonal (fun a => γ a • QuaternionicScalars.i) := by
    rw [conjugateMatrix_mul, hs, conjugateMatrix_stabilization, hdβ, splitMatrix_diagonal]
    congr 1
    funext a
    cases a using Fin.cases <;> rfl
  choose m hm using nonnegative_diagonalization_odd K hexp W γ hγ hdγ
  refine ⟨W, m, ?_, by simpa only [hm] using hdγ⟩
  by_contra h
  have hm0 : m 0 = 0 := by omega
  have he := hm 0
  change α = (2 * (m 0 : ℝ) + 1) * Real.pi at he
  rw [hm0] at he
  norm_num at he
  linarith [Real.pi_pos]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
