import Util.Bernays.IdealGenerators

/-!
# Unit residue classes in an ideal coprime to the modulus
-/

namespace Bernays

theorem isCoprime_principal_iff_isUnit_quotient {R : Type*} [CommRing R]
    (F : Ideal R) (x : R) :
    IsCoprime (Ideal.span {x}) F ↔ IsUnit (Ideal.Quotient.mk F x) := by
  constructor
  · intro h
    have htop := Ideal.isCoprime_iff_sup_eq.mp h
    have hone : (1 : R) ∈ Ideal.span {x} + F := by
      change 1 ∈ Ideal.span {x} ⊔ F
      rw [htop]
      exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hone
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp ha
    apply isUnit_iff_exists_inv.mpr
    refine ⟨Ideal.Quotient.mk F r, ?_⟩
    have hq := congrArg (Ideal.Quotient.mk F) hab
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hb, add_zero, map_one, hr, map_mul] at hq
    exact hq
  · intro h
    obtain ⟨u, hu⟩ := h
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (↑(u⁻¹) : R ⧸ F)
    have hmul : Ideal.Quotient.mk F (x * r) = 1 := by rw [map_mul, ← hu, hr, Units.mul_inv]
    have hmem : x * r - 1 ∈ F := Ideal.Quotient.eq.mp (by simpa only [map_one] using hmul)
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply (Ideal.eq_top_iff_one _).mpr
    change (1 : R) ∈ Ideal.span {x} + F
    have hx : x * r ∈ Ideal.span {x} := (Ideal.span {x}).mul_mem_right r (Ideal.mem_span_singleton_self x)
    have hsub := (Ideal.span {x} + F).sub_mem
      ((show Ideal.span {x} ≤ Ideal.span {x} + F from le_sup_left) hx)
      ((show F ≤ Ideal.span {x} + F from le_sup_right) hmem)
    simpa only [sub_sub_cancel] using hsub

theorem quotient_surjective_on_coprime_ideal {R : Type*} [CommRing R]
    (I F : Ideal R) (hIF : IsCoprime I F) :
    Function.Surjective (fun x : I => Ideal.Quotient.mk F (x : R)) := by
  have hone : (1 : R) ∈ I + F := by
    change 1 ∈ I ⊔ F
    rw [Ideal.isCoprime_iff_sup_eq.mp hIF]
    exact Submodule.mem_top
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp hone
  have hqi : Ideal.Quotient.mk F i = 1 := by
    have h := congrArg (Ideal.Quotient.mk F) hij
    simpa only [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hj, add_zero, map_one] using h
  intro a
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨⟨i * r, I.mul_mem_right r hi⟩, ?_⟩
  change Ideal.Quotient.mk F (i * r) = a
  rw [map_mul, hqi, one_mul, hr]

theorem quotient_eq_iff_sub_mem_product {R : Type*} [CommRing R]
    (I F : Ideal R) (hIF : IsCoprime I F) (x y : I) :
    Ideal.Quotient.mk F (x : R) = Ideal.Quotient.mk F (y : R) ↔
      (x : R) - (y : R) ∈ F * I := by
  rw [Ideal.Quotient.eq, Ideal.mul_eq_inf_of_isCoprime hIF.symm]
  exact (and_iff_left (I.sub_mem x.2 y.2)).symm

end Bernays
