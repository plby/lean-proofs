import ErdosProblems.Erdos1148.PrimitiveFormClass

/-! # Integral representatives of invertible ideal classes -/

namespace Erdos1148.DukeArithmetic

open scoped nonZeroDivisors

theorem classGroup_exists_integral_representative {R K : Type*} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] (c : ClassGroup R) :
    ∃ (I : Ideal R) (_ : I ≠ ⊥) (u : (FractionalIdeal R⁰ K)ˣ),
      (u : FractionalIdeal R⁰ K) = I ∧ ClassGroup.mk K u = c := by
  refine ClassGroup.induction K (fun J => ?_) c
  let F : FractionalIdeal R⁰ K := J
  have hden : algebraMap R K F.den ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors F.den.prop
  let v : Kˣ := Units.mk0 (algebraMap R K F.den) hden
  let u := toPrincipalIdeal R K v * J
  have hu : (u : FractionalIdeal R⁰ K) = F.num := by
    change (toPrincipalIdeal R K v : FractionalIdeal R⁰ K) * F = _
    rw [coe_toPrincipalIdeal]
    exact FractionalIdeal.den_mul_self_eq_num' R⁰ K F
  have hI : F.num ≠ ⊥ := by
    intro h
    apply J.ne_zero
    exact FractionalIdeal.num_eq_zero_iff.mp h
  refine ⟨F.num, hI, u, hu, ?_⟩
  change ClassGroup.mk K (toPrincipalIdeal R K v * J) = _
  rw [map_mul, classGroup_mk_principal, one_mul]

end Erdos1148.DukeArithmetic
