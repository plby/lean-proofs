import ErdosProblems.Erdos1081.Erdos1081Order

/-!
# Integral invertible ideals of a finite order

This packages the general ideal operations used in the ring-class argument,
without restricting the order to `ℤ[√(-p³)]`.
-/

open scoped nonZeroDivisors

namespace Bernays

def InvertibleIdeal (S : Type*) [CommRing S] [IsDomain S] :=
  {I : Ideal S // IsUnit (I : FractionalIdeal S⁰ (FractionRing S))}

namespace InvertibleIdeal

variable {S : Type*} [CommRing S] [IsDomain S]

instance : Coe (InvertibleIdeal S) (Ideal S) := ⟨Subtype.val⟩

@[ext] theorem ext {I J : InvertibleIdeal S} (h : (I : Ideal S) = J) : I = J := Subtype.ext h

instance : One (InvertibleIdeal S) := ⟨⟨⊤, by simpa using
  (isUnit_one : IsUnit (1 : FractionalIdeal S⁰ (FractionRing S)))⟩⟩

instance : Mul (InvertibleIdeal S) := ⟨fun I J => ⟨(I : Ideal S) * J, by
  rw [FractionalIdeal.coeIdeal_mul]
  exact I.2.mul J.2⟩⟩

instance : CommMonoid (InvertibleIdeal S) where
  mul_assoc _ _ _ := Subtype.ext (mul_assoc _ _ _)
  one_mul _ := Subtype.ext (Ideal.top_mul _)
  mul_one _ := Subtype.ext (Ideal.mul_top _)
  mul_comm _ _ := Subtype.ext (mul_comm _ _)

@[simp] theorem coe_one : ((1 : InvertibleIdeal S) : Ideal S) = ⊤ := rfl
@[simp] theorem coe_mul (I J : InvertibleIdeal S) : ((I * J : InvertibleIdeal S) : Ideal S) =
    (I : Ideal S) * J := rfl

noncomputable def unit (I : InvertibleIdeal S) : (FractionalIdeal S⁰ (FractionRing S))ˣ := I.2.unit

@[simp] theorem unit_coe (I : InvertibleIdeal S) :
    (I.unit : FractionalIdeal S⁰ (FractionRing S)) = (I : Ideal S) := I.2.unit_spec

theorem unit_injective : Function.Injective (unit : InvertibleIdeal S → _) := by
  intro I J h
  apply ext
  apply FractionalIdeal.coeIdeal_injective (K := FractionRing S)
  simpa only [unit_coe] using congrArg Units.val h

@[simp] theorem unit_one : (1 : InvertibleIdeal S).unit = 1 := by
  apply Units.ext
  simp

@[simp] theorem unit_mul (I J : InvertibleIdeal S) : (I * J).unit = I.unit * J.unit := by
  apply Units.ext
  simp [FractionalIdeal.coeIdeal_mul]

noncomputable def idealClass (I : InvertibleIdeal S) : ClassGroup S :=
  ClassGroup.mk (FractionRing S) I.unit

@[simp] theorem idealClass_one : idealClass (1 : InvertibleIdeal S) = 1 := by
  simp [idealClass]

@[simp] theorem idealClass_mul (I J : InvertibleIdeal S) :
    idealClass (I * J) = idealClass I * idealClass J := by simp [idealClass]

theorem idealClass_surjective : Function.Surjective (idealClass : InvertibleIdeal S → ClassGroup S) := by
  intro C
  refine ClassGroup.induction (FractionRing S) ?_ C
  intro U
  obtain ⟨V, hV, hc⟩ := Erdos1081.exists_integralUnitRep U
  let I : InvertibleIdeal S := ⟨U.1.num, ⟨V, hV⟩⟩
  refine ⟨I, ?_⟩
  have hunit : I.unit = V := Units.ext (I.2.unit_spec.trans hV.symm)
  simpa only [idealClass, hunit] using hc

theorem ne_bot (I : InvertibleIdeal S) : (I : Ideal S) ≠ ⊥ := by
  intro h
  have hz : (I.unit : FractionalIdeal S⁰ (FractionRing S)) = 0 := by simp [h]
  exact I.unit.ne_zero hz

noncomputable def principal (a : S) (ha : a ≠ 0) : InvertibleIdeal S :=
  ⟨Ideal.span {a}, IsUnit.of_mul_eq_one _
    (FractionalIdeal.coe_ideal_span_singleton_mul_inv (FractionRing S) ha)⟩

@[simp] theorem coe_principal (a : S) (ha : a ≠ 0) :
    (principal a ha : Ideal S) = Ideal.span {a} := rfl

@[simp] theorem idealClass_principal (a : S) (ha : a ≠ 0) :
    (principal a ha).idealClass = 1 := by
  exact (ClassGroup.mk_eq_one_of_coe_ideal (unit_coe _)).mpr ⟨a, ha, rfl⟩

theorem idealClass_eq_one_iff (I : InvertibleIdeal S) :
    I.idealClass = 1 ↔ ∃ a : S, ∃ ha : a ≠ 0, I = principal a ha := by
  rw [idealClass, ClassGroup.mk_eq_one_of_coe_ideal (unit_coe I)]
  constructor
  · rintro ⟨a, ha, h⟩
    exact ⟨a, ha, ext h⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

theorem exists_mul_eq_of_le (P I : InvertibleIdeal S) (hPI : (I : Ideal S) ≤ P) :
    ∃ J : InvertibleIdeal S, P * J = I := by
  let PF : FractionalIdeal S⁰ (FractionRing S) := (P : Ideal S)
  let IF : FractionalIdeal S⁰ (FractionRing S) := (I : Ideal S)
  have hPF : PF * PF⁻¹ = 1 :=
    (FractionalIdeal.mul_inv_cancel_iff_isUnit (K := FractionRing S)).mpr P.2
  have hu : IsUnit (PF⁻¹ * IF) :=
    (IsUnit.of_mul_eq_one PF (by rw [mul_comm, hPF])).mul I.2
  have hle : PF⁻¹ * IF ≤ 1 := by
    calc
      PF⁻¹ * IF ≤ PF⁻¹ * PF := by
        gcongr
        exact (FractionalIdeal.coeIdeal_le_coeIdeal (FractionRing S)).mpr hPI
      _ = 1 := by rw [mul_comm, hPF]
  obtain ⟨J, hJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  refine ⟨⟨J, ⟨hu.unit, hu.unit_spec.trans hJ.symm⟩⟩, ?_⟩
  apply ext
  change (P : Ideal S) * J = (I : Ideal S)
  apply FractionalIdeal.coeIdeal_injective (K := FractionRing S)
  change (((P : Ideal S) * J : Ideal S) : FractionalIdeal S⁰ (FractionRing S)) =
    ((I : Ideal S) : FractionalIdeal S⁰ (FractionRing S))
  rw [FractionalIdeal.coeIdeal_mul]
  change PF * (J : FractionalIdeal S⁰ (FractionRing S)) = IF
  rw [hJ, ← mul_assoc, hPF, one_mul]

theorem mul_right_cancel (I J K : InvertibleIdeal S) (h : I * K = J * K) : I = J := by
  apply unit_injective
  have hu := congrArg unit h
  simpa only [unit_mul, mul_left_inj] using hu

theorem cardQuot_pos [Ring.HasFiniteQuotients S] (I : InvertibleIdeal S) :
    0 < (I : Ideal S).cardQuot := Ring.HasFiniteQuotients.cardQuot_pos _ I.ne_bot

theorem cardQuot_mul_of_isMaximal (I J : InvertibleIdeal S) (hI : (I : Ideal S).IsMaximal) :
    ((I * J : InvertibleIdeal S) : Ideal S).cardQuot =
      (I : Ideal S).cardQuot * (J : Ideal S).cardQuot :=
  Erdos1081.cardQuot_mul_of_isUnit_right _ _ hI J.2

end InvertibleIdeal

end Bernays
