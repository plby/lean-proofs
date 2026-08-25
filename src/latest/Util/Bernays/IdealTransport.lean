import Util.Bernays.InvertibleIdeal

/-!
# Transport of integral invertible ideals under ring isomorphisms
-/

open scoped nonZeroDivisors

namespace Bernays.InvertibleIdeal

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]

theorem exists_mul_principal (I : InvertibleIdeal R) :
    ∃ J : InvertibleIdeal R, ∃ a : R, ∃ ha : a ≠ 0, I * J = principal a ha := by
  obtain ⟨J, hJ⟩ := idealClass_surjective I.idealClass⁻¹
  have h : (I * J).idealClass = 1 := by rw [idealClass_mul, hJ, mul_inv_cancel]
  obtain ⟨a, ha, heq⟩ := (idealClass_eq_one_iff (I * J)).mp h
  exact ⟨J, a, ha, heq⟩

theorem map_isUnit (e : R ≃+* S) (I : InvertibleIdeal R) :
    IsUnit (((I : Ideal R).map e.toRingHom) : FractionalIdeal S⁰ (FractionRing S)) := by
  obtain ⟨J, a, ha, hIJ⟩ := exists_mul_principal I
  have heq : (I : Ideal R) * J = Ideal.span {a} := congrArg (fun K : InvertibleIdeal R =>
    (K : Ideal R)) hIJ
  have hmap := congrArg (Ideal.map e.toRingHom) heq
  rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton] at hmap
  change (I : Ideal R).map e.toRingHom * (J : Ideal R).map e.toRingHom = Ideal.span {e a} at hmap
  have he : e a ≠ 0 := by exact fun hz => ha (e.injective (hz.trans (map_zero e).symm))
  have hu : IsUnit (((Ideal.span {e a} : Ideal S) : FractionalIdeal S⁰ (FractionRing S))) :=
    (principal (e a) he).2
  rw [← hmap, FractionalIdeal.coeIdeal_mul] at hu
  exact isUnit_of_mul_isUnit_left hu

noncomputable def map (e : R ≃+* S) (I : InvertibleIdeal R) : InvertibleIdeal S :=
  ⟨(I : Ideal R).map e.toRingHom, map_isUnit e I⟩

@[simp] theorem coe_map (e : R ≃+* S) (I : InvertibleIdeal R) :
    (map e I : Ideal S) = (I : Ideal R).map e.toRingHom := rfl

@[simp] theorem map_one (e : R ≃+* S) : map e (1 : InvertibleIdeal R) = 1 := by
  apply ext
  exact Ideal.map_top _

@[simp] theorem map_mul (e : R ≃+* S) (I J : InvertibleIdeal R) :
    map e (I * J) = map e I * map e J := by
  apply ext
  simp only [coe_map, coe_mul, Ideal.map_mul]

@[simp] theorem map_symm_map (e : R ≃+* S) (I : InvertibleIdeal R) :
    map e.symm (map e I) = I := by
  apply ext
  simp only [coe_map, Ideal.map_map]
  have hcomp : e.symm.toRingHom.comp e.toRingHom = RingHom.id R := by
    ext x
    exact e.symm_apply_apply x
  rw [hcomp, Ideal.map_id]

@[simp] theorem map_map_symm (e : R ≃+* S) (I : InvertibleIdeal S) :
    map e (map e.symm I) = I := map_symm_map e.symm I

@[simp] theorem map_principal (e : R ≃+* S) (a : R) (ha : a ≠ 0) :
    map e (principal a ha) = principal (e a) (by simpa using ha) := by
  apply ext
  simp only [coe_map, coe_principal, Ideal.map_span, Set.image_singleton]
  rfl

theorem map_idealClass_eq_one_iff (e : R ≃+* S) (I : InvertibleIdeal R) :
    (map e I).idealClass = 1 ↔ I.idealClass = 1 := by
  constructor
  · intro h
    obtain ⟨a, ha, heq⟩ := (idealClass_eq_one_iff (map e I)).mp h
    have heq' := congrArg (map e.symm) heq
    rw [map_symm_map, map_principal] at heq'
    rw [heq', idealClass_principal]
  · intro h
    obtain ⟨a, ha, rfl⟩ := (idealClass_eq_one_iff I).mp h
    rw [map_principal, idealClass_principal]

theorem map_idealClass_mul_eq_one_iff (e : R ≃+* S) (I J : InvertibleIdeal R) :
    (map e I).idealClass * (map e J).idealClass = 1 ↔ I.idealClass * J.idealClass = 1 := by
  rw [← idealClass_mul, ← map_mul, map_idealClass_eq_one_iff, idealClass_mul]

theorem cardQuot_map (e : R ≃+* S) (I : InvertibleIdeal R) :
    (map e I : Ideal S).cardQuot = (I : Ideal R).cardQuot :=
  Nat.card_congr (Ideal.quotientEquiv _ _ e rfl).symm.toEquiv

end Bernays.InvertibleIdeal
