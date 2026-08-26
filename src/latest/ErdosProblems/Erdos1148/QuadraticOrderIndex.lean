import ErdosProblems.Erdos1148.QuadraticOrderDiscriminant

/-! # The square of the order index relates order and field discriminants -/

namespace Erdos1148.DukeArithmetic

open NumberField

noncomputable def quadraticIntegersBasis (d : ℤ) [Fact (¬IsSquare d)] :
    Module.Basis (Fin 2) ℤ (𝓞 (QuadraticDiscrAlgebra d)) :=
  (Module.finBasis ℤ (𝓞 (QuadraticDiscrAlgebra d))).reindex
    (finCongr ((RingOfIntegers.rank (QuadraticDiscrAlgebra d)).trans
      (quadraticDiscrAlgebra_finrank d)))

noncomputable def quadraticOrderAddSubgroup {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) : AddSubgroup (𝓞 (QuadraticDiscrAlgebra d)) :=
  (quadraticOrderToIntegers ht).toAddMonoidHom.range

noncomputable def quadraticOrderIndex {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) : ℕ := (quadraticOrderAddSubgroup ht).index

theorem quadraticOrderIndex_eq_natAbs_det {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    quadraticOrderIndex ht = ((quadraticIntegersBasis d).det
      (fun i => quadraticOrderToIntegers ht (quadraticOrderBasis ht i))).natAbs := by
  let e : quadraticOrder d ≃+ quadraticOrderAddSubgroup ht :=
    AddMonoidHom.ofInjective (quadraticOrderToIntegers_injective ht)
  let b := (quadraticOrderBasis ht).map e.toIntLinearEquiv
  exact AddSubgroup.index_eq_natAbs_det (quadraticIntegersBasis d)
    (quadraticOrderAddSubgroup ht) b

theorem quadraticOrderIndex_sq_mul_field_discr {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    (quadraticOrderIndex ht : ℤ) ^ 2 * NumberField.discr (QuadraticDiscrAlgebra d) = d := by
  let b := quadraticIntegersBasis d
  let v : Fin 2 → 𝓞 (QuadraticDiscrAlgebra d) :=
    fun i => quadraticOrderToIntegers ht (quadraticOrderBasis ht i)
  have hdisc : Algebra.discr ℤ v = (b.det v) ^ 2 * Algebra.discr ℤ b := by
    have h := Algebra.discr_of_matrix_vecMul (A := ℤ) b (b.toMatrix v)
    rw [b.toMatrix_map_vecMul v] at h
    exact h
  rw [NumberField.discr_eq_discr] at hdisc
  rw [show Algebra.discr ℤ v = d from quadraticOrderBasis_integer_discr ht] at hdisc
  rw [quadraticOrderIndex_eq_natAbs_det]
  change ((b.det v).natAbs : ℤ) ^ 2 * NumberField.discr (QuadraticDiscrAlgebra d) = d
  simpa only [Int.natCast_natAbs, sq_abs] using hdisc.symm

theorem quadraticOrderIndex_ne_zero {d : ℤ} [hns : Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) : quadraticOrderIndex ht ≠ 0 := by
  intro hz
  have h := quadraticOrderIndex_sq_mul_field_discr ht
  rw [hz, Nat.cast_zero, zero_pow (by decide), zero_mul] at h
  apply hns.out
  rw [← h]
  exact ⟨0, by ring⟩

theorem quadraticDiscrAlgebra_field_discr_pos {d : ℤ} [Fact (¬IsSquare d)]
    (hd : 0 < d) {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    0 < NumberField.discr (QuadraticDiscrAlgebra d) := by
  have h : 0 < (quadraticOrderIndex ht : ℤ) ^ 2 *
      NumberField.discr (QuadraticDiscrAlgebra d) := by
    rw [quadraticOrderIndex_sq_mul_field_discr ht]
    exact hd
  exact pos_of_mul_pos_right h (sq_nonneg _)

end Erdos1148.DukeArithmetic
