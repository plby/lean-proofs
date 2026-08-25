import Util.Bernays.FormIdealNorm
import Util.Bernays.InvertibleIdeal

/-!
# Represented values as norms in a specified ideal class
-/

open scoped nonZeroDivisors

namespace Bernays

def quadraticConjugation (d b : ℤ) : QuadraticAlgebra ℤ d b ≃+* QuadraticAlgebra ℤ d b where
  toFun := star
  invFun := star
  left_inv := star_star
  right_inv := star_star
  map_add' := star_add
  map_mul' x y := by rw [star_mul, mul_comm]

theorem cardQuot_map_equiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) :
    (I.map e.toRingHom).cardQuot = I.cardQuot := by
  exact Nat.card_congr (Ideal.quotientEquiv I (I.map e.toRingHom) e rfl).symm.toEquiv

end Bernays

namespace BinQuadForm

theorem conjugateFormIdeal_eq_map (f : BinQuadForm) :
    f.conjugateFormIdeal = f.formIdeal.map
      (Bernays.quadraticConjugation (-f.a * f.c) f.b).toRingHom := by
  ext z
  rw [Ideal.mem_map_iff_of_surjective
    (Bernays.quadraticConjugation (-f.a * f.c) f.b).toRingHom
    (Bernays.quadraticConjugation _ _).surjective]
  constructor
  · intro hz
    refine ⟨star z, ?_, star_star z⟩
    exact hz
  · rintro ⟨x, hx, rfl⟩
    change f.a ∣ (star x).re + f.b * (star x).im
    simpa using hx

theorem conjugateFormIdeal_cardQuot {f : BinQuadForm} (hf : f.PosDef) :
    f.conjugateFormIdeal.cardQuot = f.a.natAbs := by
  rw [conjugateFormIdeal_eq_map, Bernays.cardQuot_map_equiv, formIdeal_cardQuot hf]

theorem formIdeal_product_principal_norm {f : BinQuadForm}
    (hf : f.PosDef) (hp : f.Primitive) (J : Ideal f.Order) (hJ : J ≠ ⊥)
    {z : f.Order} (hz : z ≠ 0)
    (heq : f.formIdeal * J = Ideal.span ({z} : Set f.Order)) :
    z.norm = f.a * (J.cardQuot : ℤ) := by
  letI := hf.orderIsDomain
  have ha : (f.a : f.Order) ≠ 0 := by
    intro h
    have hr := congrArg QuadraticAlgebra.re h
    have : f.a = 0 := by simpa using hr
    exact hf.1.ne' this
  have hconj : f.conjugateFormIdeal ≠ ⊥ := by
    intro hzero
    have hm : (f.a : f.Order) ∈ f.conjugateFormIdeal := by simp
    rw [hzero] at hm
    exact ha hm
  have hprod : Ideal.span ({(f.a : f.Order)} : Set f.Order) * J =
      Ideal.span ({z} : Set f.Order) * f.conjugateFormIdeal := by
    rw [← formIdeal_mul_conjugate hp, ← heq]
    ac_rfl
  have hnorm := Erdos1081.cardQuot_ratio_of_principal_mul_eq
    (QuadraticAlgebra.basis (-f.a * f.c) f.b) hJ hconj ha hz hprod
  rw [Bernays.algebraNorm_quadraticOrder, Bernays.algebraNorm_quadraticOrder,
    QuadraticAlgebra.norm_intCast, Int.cast_id, Int.natAbs_pow,
    conjugateFormIdeal_cardQuot hf] at hnorm
  have hnat : f.a.natAbs * J.cardQuot = z.norm.natAbs := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < f.a.natAbs from Int.natAbs_pos.mpr hf.1.ne')
    nlinarith [hnorm]
  have hnonneg := Bernays.quadraticNorm_nonneg (f.order_discr.trans_lt hf.2) z
  have hcast := congrArg (fun n : ℕ => (n : ℤ)) hnat
  simpa only [Nat.cast_mul, Int.natCast_natAbs, abs_of_pos hf.1, abs_of_nonneg hnonneg] using hcast.symm

theorem represented_pos_iff_idealClass_norm {f : BinQuadForm} (hf : f.PosDef)
    (hp : f.Primitive) {n : ℕ} (hn : 0 < n) :
    letI := hf.orderIsDomain
    (∃ u v : ℤ, f.eval u v = (n : ℤ)) ↔
      ∃ J : Bernays.InvertibleIdeal f.Order,
        J.idealClass * f.formIdealClass hf hp = 1 ∧ (J : Ideal f.Order).cardQuot = n := by
  letI := hf.orderIsDomain
  let I : Bernays.InvertibleIdeal f.Order := ⟨f.formIdeal, formIdeal_isUnit hf hp⟩
  have hIclass : I.idealClass = f.formIdealClass hf hp := rfl
  rw [represented_iff_formIdeal_norm hf.1.ne']
  constructor
  · rintro ⟨z, hzI, hz⟩
    have hz₀ : z ≠ 0 := by
      intro hzero
      have hnp : (0 : ℤ) < n := by exact_mod_cast hn
      simp only [hzero, QuadraticAlgebra.norm_zero] at hz
      have := mul_pos hf.1 hnp
      linarith
    obtain ⟨J, hJ⟩ := Bernays.InvertibleIdeal.exists_mul_eq_of_le I
      (Bernays.InvertibleIdeal.principal z hz₀) ((Ideal.span_singleton_le_iff_mem _).mpr hzI)
    refine ⟨J, ?_, ?_⟩
    · have hc := congrArg Bernays.InvertibleIdeal.idealClass hJ
      simpa only [Bernays.InvertibleIdeal.idealClass_mul,
        Bernays.InvertibleIdeal.idealClass_principal, hIclass, mul_comm] using hc
    · have heq : f.formIdeal * (J : Ideal f.Order) = Ideal.span {z} :=
        congrArg (fun K : Bernays.InvertibleIdeal f.Order => (K : Ideal f.Order)) hJ
      have hnorm := formIdeal_product_principal_norm hf hp _ J.ne_bot hz₀ heq
      have heq' : ((J : Ideal f.Order).cardQuot : ℤ) = n :=
        mul_left_cancel₀ hf.1.ne' (hnorm.symm.trans hz)
      exact_mod_cast heq'
  · rintro ⟨J, hc, hnJ⟩
    have hclass : (I * J).idealClass = 1 := by
      rw [Bernays.InvertibleIdeal.idealClass_mul, hIclass]
      exact (mul_comm _ _).trans hc
    obtain ⟨z, hz₀, hz⟩ := (Bernays.InvertibleIdeal.idealClass_eq_one_iff (I * J)).mp hclass
    have heq : f.formIdeal * (J : Ideal f.Order) = Ideal.span {z} :=
      congrArg (fun K : Bernays.InvertibleIdeal f.Order => (K : Ideal f.Order)) hz
    refine ⟨z, ?_, ?_⟩
    · apply Ideal.mul_le_left (I := f.formIdeal) (J := (J : Ideal f.Order))
      rw [heq]
      exact Ideal.mem_span_singleton_self z
    · rw [formIdeal_product_principal_norm hf hp _ J.ne_bot hz₀ heq, hnJ]

end BinQuadForm
