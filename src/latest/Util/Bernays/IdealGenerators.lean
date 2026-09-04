import Util.Bernays.IdealNormMultiplicative

/-!
# Generators modulo a finite modulus and coprime class representatives
-/

open scoped nonZeroDivisors

namespace Bernays.InvertibleIdeal

variable {R : Type*} [CommRing R] [IsDomain R] [Ring.HasFiniteQuotients R]

theorem mul_left_cancel_ideal (I : InvertibleIdeal R) {J K : Ideal R}
    (h : (I : Ideal R) * J = (I : Ideal R) * K) : J = K := by
  apply FractionalIdeal.coeIdeal_injective (K := FractionRing R)
  apply I.2.mul_left_cancel
  simpa only [FractionalIdeal.coeIdeal_mul] using
    congrArg (fun A : Ideal R => (A : FractionalIdeal R⁰ (FractionRing R))) h

theorem exists_generator_mod_mul (I : InvertibleIdeal R) (F : Ideal R) (hF : F ≠ ⊥) :
    ∃ x : (I : Ideal R), (x : R) ≠ 0 ∧
      (I : Ideal R) = Ideal.span ({(x : R)} : Set R) + F * (I : Ideal R) := by
  classical
  by_cases htop : F = ⊤
  · obtain ⟨x, hx, hx₀⟩ := (I : Ideal R).ne_bot_iff.mp I.ne_bot
    refine ⟨⟨x, hx⟩, hx₀, ?_⟩
    rw [htop, Ideal.top_mul]
    exact (sup_eq_right.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hx)).symm
  let A := R ⧸ F
  let M := (I : Ideal R)
  let T := TensorProduct R A M
  let : Nontrivial A := (Ideal.Quotient.nontrivial_iff (R := R) (I := F)).mpr htop
  let : Finite A := Ring.HasFiniteQuotients.finiteQuotient hF
  let : IsArtinianRing A := isArtinian_of_finite
  let : Module.Invertible R M := Erdos1081.moduleInvertibleIdealOfIsUnit (I : Ideal R) I.2
  let : Module.Invertible A T := inferInstance
  let : Module.Free A T := inferInstance
  let e : T ≃ₗ[A] A := (Module.Invertible.free_iff_linearEquiv.mp
    (inferInstance : Module.Free A T)).some
  obtain ⟨x, hx⟩ := TensorProduct.mk_surjective R M A Ideal.Quotient.mk_surjective (e.symm 1)
  have hx₀ : (x : R) ≠ 0 := by
    intro hzero
    have hz : x = 0 := Subtype.ext hzero
    have he : e.symm 1 = 0 := by simpa [hz] using hx.symm
    have hone : (1 : A) = 0 := by rw [← e.apply_symm_apply 1, he, map_zero]
    exact one_ne_zero hone
  refine ⟨x, hx₀, le_antisymm ?_ ?_⟩
  · intro y hy
    let ys : M := ⟨y, hy⟩
    let a : A := e (TensorProduct.mk R A M 1 ys)
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective a
    let v : M := ys - r • x
    have hvzero : TensorProduct.mk R A M 1 v = 0 := by
      dsimp only [v]
      rw [map_sub, map_smul, hx]
      apply e.injective
      rw [map_sub, map_zero]
      change a - e (r • e.symm 1) = 0
      rw [← IsScalarTower.algebraMap_smul A r (e.symm 1), map_smul, e.apply_symm_apply,
        smul_eq_mul, mul_one]
      change a - algebraMap R A r = 0
      rw [← hr]
      simp [A, Ideal.Quotient.algebraMap_eq]
    have hvker : v ∈ LinearMap.ker (TensorProduct.mk R A M 1) := LinearMap.mem_ker.mpr hvzero
    rw [LinearMap.ker_tensorProductMk] at hvker
    have hvprod : (v : R) ∈ F * (I : Ideal R) := by
      rw [← Ideal.smul_eq_mul]
      exact Submodule.smul_induction_on hvker
        (fun r hrF w _ => by
          change r * (w : R) ∈ F • (I : Ideal R)
          rw [Ideal.smul_eq_mul]
          exact Ideal.mul_mem_mul hrF w.2)
        (fun _ _ ha hb => add_mem ha hb)
    have hspan : r * (x : R) ∈ Ideal.span ({(x : R)} : Set R) :=
      (Ideal.span ({(x : R)} : Set R)).mul_mem_left r (Ideal.mem_span_singleton_self _)
    have hadd := (Ideal.span ({(x : R)} : Set R) + F * (I : Ideal R)).add_mem
      ((show Ideal.span ({(x : R)} : Set R) ≤
        Ideal.span ({(x : R)} : Set R) + F * (I : Ideal R) from le_sup_left) hspan)
      ((show F * (I : Ideal R) ≤
        Ideal.span ({(x : R)} : Set R) + F * (I : Ideal R) from le_sup_right) hvprod)
    have hvval : (v : R) = y - r * (x : R) := rfl
    simpa [hvval, add_comm] using hadd
  · exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr x.2) Ideal.mul_le_right

theorem exists_coprime_inverse (I : InvertibleIdeal R) (F : Ideal R) (hF : F ≠ ⊥) :
    ∃ J : InvertibleIdeal R, J.idealClass = I.idealClass⁻¹ ∧ IsCoprime (J : Ideal R) F := by
  obtain ⟨x, hx₀, hgen⟩ := exists_generator_mod_mul I F hF
  obtain ⟨J, hIJ⟩ := exists_mul_eq_of_le I (principal (x : R) hx₀)
    ((Ideal.span_singleton_le_iff_mem _).mpr x.2)
  have hc : I.idealClass * J.idealClass = 1 := by
    have h := congrArg idealClass hIJ
    simpa only [idealClass_mul, idealClass_principal] using h
  refine ⟨J, ?_, ?_⟩
  · calc
      J.idealClass = I.idealClass⁻¹ * (I.idealClass * J.idealClass) := by simp
      _ = I.idealClass⁻¹ := by rw [hc, mul_one]
  · have hspan : (I : Ideal R) * (J : Ideal R) = Ideal.span {(x : R)} :=
      congrArg (fun K : InvertibleIdeal R => (K : Ideal R)) hIJ
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply mul_left_cancel_ideal I
    change (I : Ideal R) * ((J : Ideal R) + F) = (I : Ideal R) * ⊤
    rw [mul_add, hspan, mul_comm (I : Ideal R) F, ← hgen, Ideal.mul_top]

theorem exists_coprime_representative (C : ClassGroup R) (F : Ideal R) (hF : F ≠ ⊥) :
    ∃ I : InvertibleIdeal R, I.idealClass = C ∧ IsCoprime (I : Ideal R) F := by
  obtain ⟨J, hJ⟩ := idealClass_surjective C⁻¹
  obtain ⟨I, hI, hc⟩ := exists_coprime_inverse J F hF
  exact ⟨I, by simpa only [hJ, inv_inv] using hI, hc⟩

theorem generator_mod_of_sub_mem (I : InvertibleIdeal R) (F : Ideal R) (c : (I : Ideal R))
    (hc : (I : Ideal R) = Ideal.span ({(c : R)} : Set R) + F * (I : Ideal R))
    {x : R} (hx : x - (c : R) ∈ F * (I : Ideal R)) :
    (I : Ideal R) = Ideal.span ({x} : Set R) + F * (I : Ideal R) := by
  have hxI : x ∈ (I : Ideal R) := by
    have h := (I : Ideal R).add_mem (Ideal.mul_le_right hx) c.2
    simpa only [sub_add_cancel] using h
  apply le_antisymm
  · calc
      (I : Ideal R) = Ideal.span ({(c : R)} : Set R) + F * (I : Ideal R) := hc
      _ ≤ Ideal.span ({x} : Set R) + F * (I : Ideal R) := by
        apply sup_le ?_ le_sup_right
        apply (Ideal.span_singleton_le_iff_mem _).mpr
        change (c : R) ∈ Ideal.span ({x} : Set R) + F * (I : Ideal R)
        have h₁ : x ∈ Ideal.span ({x} : Set R) + F * (I : Ideal R) :=
          (show Ideal.span ({x} : Set R) ≤ Ideal.span ({x} : Set R) + F * (I : Ideal R)
            from le_sup_left) (Ideal.mem_span_singleton_self x)
        have h₂ : x - (c : R) ∈ Ideal.span ({x} : Set R) + F * (I : Ideal R) :=
          (show F * (I : Ideal R) ≤ Ideal.span ({x} : Set R) + F * (I : Ideal R)
            from le_sup_right) hx
        simpa only [sub_sub_cancel] using (Ideal.span ({x} : Set R) + F * (I : Ideal R)).sub_mem h₁ h₂
  · exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hxI) Ideal.mul_le_right

theorem factor_coprime_of_generator_mod (I J : InvertibleIdeal R) (F : Ideal R)
    {x : R} (hx : x ≠ 0) (hIJ : I * J = principal x hx)
    (hgen : (I : Ideal R) = Ideal.span ({x} : Set R) + F * (I : Ideal R)) :
    IsCoprime (J : Ideal R) F := by
  have hspan : (I : Ideal R) * (J : Ideal R) = Ideal.span {x} :=
    congrArg (fun K : InvertibleIdeal R => (K : Ideal R)) hIJ
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply mul_left_cancel_ideal I
  change (I : Ideal R) * ((J : Ideal R) + F) = (I : Ideal R) * ⊤
  rw [mul_add, hspan, mul_comm (I : Ideal R) F, ← hgen, Ideal.mul_top]

end Bernays.InvertibleIdeal
