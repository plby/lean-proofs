import ErdosProblems.Erdos1148.IntegralIdealClass
import Mathlib.RingTheory.DedekindDomain.Factorization

/-! # Ideal-class representatives prime to a prescribed nonzero ideal -/

namespace Erdos1148.DukeArithmetic

open scoped nonZeroDivisors

theorem exists_coprime_principal_partner {R : Type*} [CommRing R] [IsDedekindDomain R]
    (J C : Ideal R) (hJ : J ≠ ⊥) (hC : C ≠ ⊥) :
    ∃ (L : Ideal R) (a : R), L ≠ ⊥ ∧ a ≠ 0 ∧ J * L = Ideal.span {a} ∧ L ⊔ C = ⊤ := by
  have hex : ∃ a : R, a ≠ 0 ∧ J * C ⊔ Ideal.span {a} = J := by
    by_cases hCtop : C = ⊤
    · obtain ⟨a, ha, ha₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
      refine ⟨a, ha₀, ?_⟩
      rw [hCtop, Ideal.mul_top]
      exact sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem J).mpr ha)
    · obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq
        (Ideal.mul_le_left : J * C ≤ J) (mul_ne_zero hJ hC)
      refine ⟨a, ?_, ha⟩
      intro ha₀
      have hmul : J * C = J * 1 := by simpa [ha₀] using ha
      apply hCtop
      simpa only [Ideal.one_eq_top] using mul_left_cancel₀ hJ hmul
  obtain ⟨a, ha₀, ha⟩ := hex
  have haJ : Ideal.span {a} ≤ J := by rw [← ha]; exact le_sup_right
  obtain ⟨L, hL⟩ := Ideal.dvd_iff_le.mpr haJ
  have hL₀ : L ≠ ⊥ := by
    intro hz
    have hz' : Ideal.span {a} = ⊥ := by simpa [hz] using hL
    exact ha₀ (Ideal.span_singleton_eq_bot.mp hz')
  refine ⟨L, a, hL₀, ha₀, hL.symm, ?_⟩
  have hmul : J * (C ⊔ L) = J * 1 := by
    rw [Ideal.mul_sup, ← hL, ha, mul_one]
  simpa only [sup_comm, Ideal.one_eq_top] using mul_left_cancel₀ hJ hmul

theorem classGroup_exists_coprime_representative {R K : Type*}
    [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (C : Ideal R) (hC : C ≠ ⊥) (c : ClassGroup R) :
    ∃ (I : Ideal R) (_ : I ≠ ⊥) (u : (FractionalIdeal R⁰ K)ˣ),
      (u : FractionalIdeal R⁰ K) = I ∧ ClassGroup.mk K u = c ∧ I ⊔ C = ⊤ := by
  obtain ⟨J, hJ, v, hv, hvc⟩ := classGroup_exists_integral_representative (K := K) c⁻¹
  obtain ⟨I, a, hI, ha, hprod, hIC⟩ := exists_coprime_principal_partner J C hJ hC
  let I₀ : (Ideal R)⁰ := ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
  let u : (FractionalIdeal R⁰ K)ˣ := FractionalIdeal.mk0 K I₀
  have hu : (u : FractionalIdeal R⁰ K) = I := FractionalIdeal.coe_mk0 K I₀
  have haK : algebraMap R K a ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne ha
  let a₀ : Kˣ := Units.mk0 (algebraMap R K a) haK
  have hp : v * u = toPrincipalIdeal R K a₀ := by
    apply Units.ext
    simp only [Units.val_mul, hv, hu, ← FractionalIdeal.coeIdeal_mul, hprod,
      FractionalIdeal.coeIdeal_span_singleton, coe_toPrincipalIdeal]
    rfl
  have hc : c⁻¹ * ClassGroup.mk K u = 1 := by
    rw [← hvc, ← map_mul, hp, classGroup_mk_principal]
  exact ⟨I, hI, u, hu, (inv_mul_eq_one.mp hc).symm, hIC⟩

end Erdos1148.DukeArithmetic
