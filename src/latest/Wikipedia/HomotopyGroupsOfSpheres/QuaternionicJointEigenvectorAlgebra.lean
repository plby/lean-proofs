import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicRotationEigenvector

/-!
# A common quaternionic eigenline from an anticommuting complex structure

An involution on an imaginary eigenspace has a nonzero fixed vector: either
the fixed projection is nonzero, or right multiplication by `i` turns an
anti-fixed vector into a fixed one. Applied to `-J R_j`, this gives a common
eigenvector for `T` and `J`, with right eigenvalues `α i` and `j` respectively.
-/

namespace Wikipedia.HomotopyGroupsOfSpheres

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_fixed_eigenvector_of_involution (T R Q : E →ₗ[ℝ] E)
    (hR : ∀ v, R (R v) = -v) (hQ : ∀ v, Q (Q v) = v)
    (hQR : ∀ v, Q (R v) = -(R (Q v)))
    (hTR : ∀ v, T (R v) = R (T v)) (hTQ : ∀ v, T (Q v) = -(Q (T v)))
    {α : ℝ} {v : E} (hv : v ≠ 0) (he : T v = α • R v) :
    ∃ w : E, w ≠ 0 ∧ T w = α • R w ∧ Q w = w := by
  have heQ : T (Q v) = α • R (Q v) := by
    rw [hTQ, he, map_smul, hQR, smul_neg, neg_neg]
  by_cases hz : v + Q v = 0
  · have hQv : Q v = -v := eq_neg_of_add_eq_zero_right hz
    refine ⟨R v, ?_, ?_, ?_⟩
    · intro hzero
      have h := hR v
      rw [hzero, map_zero] at h
      exact hv (neg_eq_zero.mp h.symm)
    · rw [hTR, he, map_smul]
    · rw [hQR, hQv, map_neg, neg_neg]
  · refine ⟨v + Q v, hz, ?_, ?_⟩
    · rw [map_add, he, heQ, map_add, smul_add]
    · rw [map_add, hQ, add_comm]

theorem exists_joint_quaternionic_eigenvector (T R S J : E →ₗ[ℝ] E)
    (hR : ∀ v, R (R v) = -v) (hS : ∀ v, S (S v) = -v) (hJ : ∀ v, J (J v) = -v)
    (hRS : ∀ v, R (S v) = -(S (R v)))
    (hJR : ∀ v, J (R v) = R (J v)) (hJS : ∀ v, J (S v) = S (J v))
    (hTR : ∀ v, T (R v) = R (T v)) (hTS : ∀ v, T (S v) = S (T v))
    (hTJ : ∀ v, T (J v) = -(J (T v)))
    {α : ℝ} {v : E} (hv : v ≠ 0) (he : T v = α • R v) :
    ∃ w : E, w ≠ 0 ∧ T w = α • R w ∧ J w = S w := by
  let Q : E →ₗ[ℝ] E := -(S.comp J)
  have hQ (x : E) : Q (Q x) = x := by
    change -S (J (-S (J x))) = x
    simp only [map_neg, hJS, hJ, hS, neg_neg]
  have hQR (x : E) : Q (R x) = -(R (Q x)) := by
    change -S (J (R x)) = -R (-S (J x))
    rw [hJR, map_neg, neg_neg, hRS]
  have hTQ (x : E) : T (Q x) = -(Q (T x)) := by
    change T (-S (J x)) = -(-S (J (T x)))
    simp only [map_neg, hTS, hTJ, neg_neg]
  obtain ⟨w, hw, hTw, hQw⟩ := exists_fixed_eigenvector_of_involution T R Q
    hR hQ hQR hTR hTQ hv he
  refine ⟨w, hw, hTw, ?_⟩
  have h := congrArg S hQw
  change S (-S (J w)) = S w at h
  rwa [map_neg, hS, neg_neg] at h

theorem exists_unit_joint_quaternionic_eigenvector (T R S J : E →ₗ[ℝ] E)
    (hR : ∀ v, R (R v) = -v) (hS : ∀ v, S (S v) = -v) (hJ : ∀ v, J (J v) = -v)
    (hRS : ∀ v, R (S v) = -(S (R v)))
    (hJR : ∀ v, J (R v) = R (J v)) (hJS : ∀ v, J (S v) = S (J v))
    (hTR : ∀ v, T (R v) = R (T v)) (hTS : ∀ v, T (S v) = S (T v))
    (hTJ : ∀ v, T (J v) = -(J (T v)))
    {α : ℝ} {v : E} (hv : v ≠ 0) (he : T v = α • R v) :
    ∃ w : E, ‖w‖ = 1 ∧ T w = α • R w ∧ J w = S w := by
  obtain ⟨w, hw, hTw, hJw⟩ := exists_joint_quaternionic_eigenvector T R S J
    hR hS hJ hRS hJR hJS hTR hTS hTJ hv he
  refine ⟨‖w‖⁻¹ • w, norm_smul_inv_norm hw, ?_, ?_⟩
  · rw [map_smul, hTw, map_smul, smul_comm]
  · rw [map_smul, hJw, map_smul]

end Wikipedia.HomotopyGroupsOfSpheres
