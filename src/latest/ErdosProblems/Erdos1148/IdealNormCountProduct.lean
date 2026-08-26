import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.Data.Nat.Factorization.Induction

/-! # Multiplying ideal counts at coprime norms -/

namespace Erdos1148.DukeArithmetic

open NumberField Ideal

variable {K : Type*} [Field K] [NumberField K]

lemma ideals_isCoprime_of_absNorm {I J : Ideal (𝓞 K)}
    (h : (absNorm I).Coprime (absNorm J)) : IsCoprime I J := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply Ideal.absNorm_eq_one_iff.mp
  apply Nat.eq_one_of_dvd_coprimes h
  · exact Ideal.absNorm_dvd_absNorm_of_le le_sup_left
  · exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right

theorem ideal_mul_injective_of_coprime_norms {m n : ℕ} (hmn : m.Coprime n) :
    Function.Injective (fun IJ : {I : Ideal (𝓞 K) // absNorm I = m} ×
      {J : Ideal (𝓞 K) // absNorm J = n} => IJ.1.val * IJ.2.val) := by
  intro ⟨I, J⟩ ⟨I', J'⟩ h
  change I.val * J.val = I'.val * J'.val at h
  have hIJ' : IsCoprime I.val J'.val := ideals_isCoprime_of_absNorm (by rwa [I.prop, J'.prop])
  have hI'J : IsCoprime I'.val J.val := ideals_isCoprime_of_absNorm (by rwa [I'.prop, J.prop])
  have hI : I.val = I'.val := by
    apply le_antisymm
    · apply Ideal.dvd_iff_le.mp
      apply hI'J.dvd_of_dvd_mul_right
      rw [h]
      exact dvd_mul_right _ _
    · apply Ideal.dvd_iff_le.mp
      apply hIJ'.dvd_of_dvd_mul_right
      rw [← h]
      exact dvd_mul_right _ _
  have hJ : J.val = J'.val := by
    apply le_antisymm
    · apply Ideal.dvd_iff_le.mp
      apply hIJ'.symm.dvd_of_dvd_mul_left
      rw [h]
      exact dvd_mul_left _ _
    · apply Ideal.dvd_iff_le.mp
      apply hI'J.symm.dvd_of_dvd_mul_left
      rw [← h]
      exact dvd_mul_left _ _
  exact Prod.ext (Subtype.ext hI) (Subtype.ext hJ)

theorem ideal_norm_count_mul_le {m n : ℕ} (hmn : m.Coprime n) :
    Nat.card {I : Ideal (𝓞 K) // absNorm I = m} *
      Nat.card {J : Ideal (𝓞 K) // absNorm J = n} ≤
        Nat.card {L : Ideal (𝓞 K) // absNorm L = m * n} := by
  let f : {I : Ideal (𝓞 K) // absNorm I = m} × {J : Ideal (𝓞 K) // absNorm J = n} →
      {L : Ideal (𝓞 K) // absNorm L = m * n} :=
    fun IJ => ⟨IJ.1.val * IJ.2.val, by rw [map_mul, IJ.1.prop, IJ.2.prop]⟩
  have hf : Function.Injective f := fun x y h =>
    ideal_mul_injective_of_coprime_norms hmn (congrArg Subtype.val h)
  have : Finite {L : Ideal (𝓞 K) // absNorm L = m * n} :=
    finite_setOfPred_absNorm_eq (m * n)
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hf

end Erdos1148.DukeArithmetic
