import ErdosProblems.Erdos1081.Erdos1081Core

namespace Erdos1081

open scoped nonZeroDivisors

noncomputable section

theorem exists_natPrime_under_specialMaximal
    {p : ℕ} [Fact p.Prime]
    (P : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) (hP : P.IsMaximal) :
    ∃ q : ℕ, q.Prime ∧
      P.under ℤ = Ideal.span ({(q : ℤ)} : Set ℤ) := by
  let : Module.Free ℤ (Zsqrtd (-(p : ℤ) ^ 3)) :=
    Module.Free.of_basis (zsqrtdBasis (-(p : ℤ) ^ 3))
  let : Module.Finite ℤ (Zsqrtd (-(p : ℤ) ^ 3)) :=
    Module.Finite.of_basis (zsqrtdBasis (-(p : ℤ) ^ 3))
  let : Ring.HasFiniteQuotients (Zsqrtd (-(p : ℤ) ^ 3)) := inferInstance
  let : P.IsMaximal := hP
  obtain ⟨a, ha⟩ := IsPrincipalIdealRing.principal (P.under ℤ)
  have ha0 : a ≠ 0 := by
    intro haz
    have hPne : P ≠ ⊥ := by
      intro hzero
      have htwoTop : Ideal.span ({(2 : Zsqrtd (-(p : ℤ) ^ 3))} :
          Set (Zsqrtd (-(p : ℤ) ^ 3))) ≠ ⊤ := by
        intro htop
        have hone : (1 : Zsqrtd (-(p : ℤ) ^ 3)) ∈ Ideal.span
            ({(2 : Zsqrtd (-(p : ℤ) ^ 3))} :
              Set (Zsqrtd (-(p : ℤ) ^ 3))) := by
          rw [htop]
          exact Submodule.mem_top
        rw [Ideal.mem_span_singleton] at hone
        obtain ⟨c, hc⟩ := hone
        have hre := congrArg Zsqrtd.re hc
        norm_num at hre
        omega
      have heq := hP.eq_of_le htwoTop (show P ≤ Ideal.span
        ({(2 : Zsqrtd (-(p : ℤ) ^ 3))} : Set (Zsqrtd (-(p : ℤ) ^ 3))) by
          rw [hzero]
          exact bot_le)
      rw [hzero] at heq
      have hmem : (2 : Zsqrtd (-(p : ℤ) ^ 3)) ∈ (⊥ :
          Ideal (Zsqrtd (-(p : ℤ) ^ 3))) := by
        rw [heq]
        exact Ideal.mem_span_singleton_self 2
      norm_num at hmem
    have hcard : 0 < P.cardQuot :=
      Ring.HasFiniteQuotients.cardQuot_pos P hPne
    have hmem : ((P.cardQuot : ℕ) : Zsqrtd (-(p : ℤ) ^ 3)) ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact Ideal.Quotient.index_eq_zero P
    have hundermem : (P.cardQuot : ℤ) ∈ P.under ℤ := hmem
    rw [ha, haz] at hundermem
    have hcardZ : (P.cardQuot : ℤ) = 0 := by simpa using hundermem
    have hcard0 : P.cardQuot = 0 := by exact_mod_cast hcardZ
    omega
  have haprime := (Ideal.span_singleton_prime ha0).mp
  simp only [← Ideal.submodule_span_eq, ← ha] at haprime
  let q := a.natAbs
  have hq : q.Prime := Int.prime_iff_natAbs_prime.mp
    (haprime ((Ideal.IsMaximal.isPrime hP).under ℤ))
  refine ⟨q, hq, ?_⟩
  rw [ha]
  rcases abs_choice a with ha' | ha' <;>
    simp [q, ha', Ideal.span_singleton_neg]

/-- Every maximal ideal of the special quadratic order away from the
conductor primes is either principal or one of the two explicit split
ideals. -/
theorem specialMaximal_isPrincipal_or_eq_orientedSplit
    {p : ℕ} [Fact p.Prime]
    (P : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) (hP : P.IsMaximal)
    (hconductor : Zsqrtd.ofInt ((2 * p : ℕ) : ℤ) ∉ P) :
    P.IsPrincipal ∨
      ∃ q : ℕ, ∃ hq : q.Prime, ∃ hq2 : q ≠ 2, ∃ hqp : q ≠ p,
        ∃ h : ¬ IsQuadraticObstruction (p ^ 3) q, ∃ b : Bool,
          P = specialOrientedSplitIdeal p q h b := by
  let : Module.Free ℤ (Zsqrtd (-(p : ℤ) ^ 3)) :=
    Module.Free.of_basis (zsqrtdBasis (-(p : ℤ) ^ 3))
  let : Module.Finite ℤ (Zsqrtd (-(p : ℤ) ^ 3)) :=
    Module.Finite.of_basis (zsqrtdBasis (-(p : ℤ) ^ 3))
  obtain ⟨q, hq, hunder⟩ := exists_natPrime_under_specialMaximal P hP
  let : Fact q.Prime := ⟨hq⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  have hqP : Zsqrtd.ofInt (q : ℤ) ∈ P := by
    change (q : ℤ) ∈ P.under ℤ
    rw [hunder]
    exact Ideal.mem_span_singleton_self (q : ℤ)
  have hq2 : q ≠ 2 := by
    intro heq
    apply hconductor
    rw [show Zsqrtd.ofInt ((2 * p : ℕ) : ℤ) =
        Zsqrtd.ofInt (p : ℤ) * Zsqrtd.ofInt (q : ℤ) by
      subst q
      ext <;> simp [mul_comm]]
    exact P.mul_mem_left _ hqP
  have hqp : q ≠ p := by
    intro heq
    apply hconductor
    rw [show Zsqrtd.ofInt ((2 * p : ℕ) : ℤ) =
        Zsqrtd.ofInt (2 : ℤ) * Zsqrtd.ofInt (q : ℤ) by
      subst q
      ext <;> simp]
    exact P.mul_mem_left _ hqP
  by_cases hsplit : ¬ IsQuadraticObstruction (p ^ 3) q
  · right
    let r : ZMod q := specialSplitRoot p q hsplit
    have hr : r * r = ((-(p : ℤ) ^ 3 : ℤ) : ZMod q) :=
      specialSplitRoot_sq p q hsplit
    have hcop : Nat.Coprime q (2 * r.val) :=
      specialSplitRoot_coprime_two_val Fact.out hq hq2 hqp hsplit
    let A : Ideal (Zsqrtd (-(p : ℤ) ^ 3)) :=
      splitPrimeIdeal (-(p : ℤ) ^ 3) q r
    let B : Ideal (Zsqrtd (-(p : ℤ) ^ 3)) :=
      splitConjugateIdeal (-(p : ℤ) ^ 3) q r
    have hprod : A * B = Ideal.span
        ({Zsqrtd.ofInt (q : ℤ)} : Set (Zsqrtd (-(p : ℤ) ^ 3))) :=
      splitPrimeIdeal_mul_conjugate (-(p : ℤ) ^ 3) q r hr hcop
    have hprodle : A * B ≤ P := by
      rw [hprod, Ideal.span_singleton_le_iff_mem]
      exact hqP
    have hprimeP : P.IsPrime := hP.isPrime
    rcases hprimeP.mul_le.mp hprodle with hAP | hBP
    · have hAmax : A.IsMaximal := by
        dsimp [A]
        rw [splitPrimeIdeal_eq_ker (-(p : ℤ) ^ 3) q r hr]
        exact RingHom.ker_isMaximal_of_surjective _
          (splitEval_surjective (-(p : ℤ) ^ 3) q r hr)
      refine ⟨q, hq, hq2, hqp, hsplit, false, ?_⟩
      have heq : A = P := hAmax.eq_of_le hP.ne_top hAP
      simpa [specialOrientedSplitIdeal, orientedSplitIdeal, A, r] using heq.symm
    · have hBmax : B.IsMaximal := by
        dsimp [B]
        rw [splitConjugateIdeal_eq_ker (-(p : ℤ) ^ 3) q r hr]
        exact RingHom.ker_isMaximal_of_surjective _
          (splitEval_surjective (-(p : ℤ) ^ 3) q (-r) (by simpa using hr))
      refine ⟨q, hq, hq2, hqp, hsplit, true, ?_⟩
      have heq : B = P := hBmax.eq_of_le hP.ne_top hBP
      simpa [specialOrientedSplitIdeal, orientedSplitIdeal, B, r] using heq.symm
  · left
    have hnonsquare : ¬ IsSquare
        (((-(p : ℤ) ^ 3 : ℤ) : ZMod q)) := by
      simpa [IsQuadraticObstruction] using hsplit
    have hspanle : Ideal.span
        ({Zsqrtd.ofInt (q : ℤ)} : Set (Zsqrtd (-(p : ℤ) ^ 3))) ≤ P :=
      (Ideal.span_singleton_le_iff_mem P).mpr hqP
    have hPle : P ≤ Ideal.span
        ({Zsqrtd.ofInt (q : ℤ)} : Set (Zsqrtd (-(p : ℤ) ^ 3))) := by
      intro z hz
      have hnormP : Zsqrtd.ofInt z.norm ∈ P := by
        rw [Zsqrtd.ofInt_eq_intCast, Zsqrtd.norm_eq_mul_conj]
        exact P.mul_mem_right _ hz
      have hnormUnder : z.norm ∈ P.under ℤ := by
        simpa using hnormP
      have hqnorm : (q : ℤ) ∣ z.norm := by
        rw [hunder, Ideal.mem_span_singleton] at hnormUnder
        exact hnormUnder
      have hnormMod : ((z.norm : ℤ) : ZMod q) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd z.norm q).mpr hqnorm
      have hformula : (z.re : ZMod q) * (z.re : ZMod q) -
          ((-(p : ℤ) ^ 3 : ℤ) : ZMod q) *
            (z.im : ZMod q) * (z.im : ZMod q) = 0 := by
        simpa only [Zsqrtd.norm_def, Int.cast_sub, Int.cast_mul] using hnormMod
      have him0 : (z.im : ZMod q) = 0 := by
        by_contra him
        apply hnonsquare
        refine ⟨(z.re : ZMod q) / (z.im : ZMod q), ?_⟩
        have heq : (z.re : ZMod q) * (z.re : ZMod q) =
            ((-(p : ℤ) ^ 3 : ℤ) : ZMod q) *
              (z.im : ZMod q) * (z.im : ZMod q) :=
          sub_eq_zero.mp hformula
        field_simp [him]
        simpa [pow_two, mul_assoc] using heq.symm
      have hre0 : (z.re : ZMod q) = 0 := by
        rw [him0] at hformula
        have hreSq : (z.re : ZMod q) * (z.re : ZMod q) = 0 := by
          simpa using hformula
        exact eq_zero_of_mul_self_eq_zero hreSq
      have hqre : (q : ℤ) ∣ z.re :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd z.re q).mp hre0
      have hqim : (q : ℤ) ∣ z.im :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd z.im q).mp him0
      rw [Ideal.mem_span_singleton]
      exact (Zsqrtd.intCast_dvd (q : ℤ) z).mpr ⟨hqre, hqim⟩
    have heq : P = Ideal.span
        ({Zsqrtd.ofInt (q : ℤ)} : Set (Zsqrtd (-(p : ℤ) ^ 3))) :=
      le_antisymm hPle hspanle
    rw [heq]
    exact inferInstance

/-! ## The monoid of integral invertible ideals -/

def IntegralUnitIdeal (S : Type*) [CommRing S] [IsDomain S] :=
  {I : Ideal S // IsUnit
    ((I : Ideal S) : FractionalIdeal S⁰ (FractionRing S))}

namespace IntegralUnitIdeal

variable {S : Type*} [CommRing S] [IsDomain S]

instance : Coe (IntegralUnitIdeal S) (Ideal S) := ⟨Subtype.val⟩

@[ext] theorem ext {I J : IntegralUnitIdeal S}
    (h : (I : Ideal S) = (J : Ideal S)) : I = J := Subtype.ext h

instance : One (IntegralUnitIdeal S) :=
  ⟨⟨⊤, by simpa using
    (isUnit_one : IsUnit (1 : FractionalIdeal S⁰ (FractionRing S)))⟩⟩

instance : Mul (IntegralUnitIdeal S) :=
  ⟨fun I J ↦ ⟨(I : Ideal S) * (J : Ideal S), by
    rw [FractionalIdeal.coeIdeal_mul]
    exact I.2.mul J.2⟩⟩

instance : CommMonoid (IntegralUnitIdeal S) where
  mul_assoc I J K := by
    apply Subtype.ext
    exact mul_assoc (I : Ideal S) (J : Ideal S) (K : Ideal S)
  one_mul I := by
    apply Subtype.ext
    exact Ideal.top_mul (I : Ideal S)
  mul_one I := by
    apply Subtype.ext
    exact Ideal.mul_top (I : Ideal S)
  mul_comm I J := by
    apply Subtype.ext
    exact mul_comm (I : Ideal S) (J : Ideal S)

@[simp] theorem coe_one : ((1 : IntegralUnitIdeal S) : Ideal S) = ⊤ := rfl

@[simp] theorem coe_mul (I J : IntegralUnitIdeal S) :
    ((I * J : IntegralUnitIdeal S) : Ideal S) =
      (I : Ideal S) * (J : Ideal S) := rfl

noncomputable def unit (I : IntegralUnitIdeal S) :
    (FractionalIdeal S⁰ (FractionRing S))ˣ := I.2.unit

theorem unit_coe (I : IntegralUnitIdeal S) :
    ((I.unit : (FractionalIdeal S⁰ (FractionRing S))ˣ) :
      FractionalIdeal S⁰ (FractionRing S)) = (I : Ideal S) :=
  I.2.unit_spec

noncomputable def idealClass (I : IntegralUnitIdeal S) : ClassGroup S :=
  ClassGroup.mk (FractionRing S) I.unit

@[simp] theorem idealClass_one : idealClass (1 : IntegralUnitIdeal S) = 1 := by
  unfold idealClass
  rw [← map_one (ClassGroup.mk (R := S) (K := FractionRing S))]
  congr 1
  apply Units.ext
  simpa using (unit_coe (1 : IntegralUnitIdeal S))

theorem idealClass_mul (I J : IntegralUnitIdeal S) :
    idealClass (I * J) = idealClass I * idealClass J := by
  unfold idealClass
  rw [← map_mul]
  congr 1
  apply Units.ext
  change (((I * J).2.unit :
      (FractionalIdeal S⁰ (FractionRing S))ˣ) :
        FractionalIdeal S⁰ (FractionRing S)) =
    (((I.2.unit : (FractionalIdeal S⁰ (FractionRing S))ˣ) *
      J.2.unit : (FractionalIdeal S⁰ (FractionRing S))ˣ) :
        FractionalIdeal S⁰ (FractionRing S))
  rw [(I * J).2.unit_spec, Units.val_mul, I.2.unit_spec, J.2.unit_spec]
  exact FractionalIdeal.coeIdeal_mul (P := FractionRing S)
    (I : Ideal S) (J : Ideal S)

/-- Every class has an integral invertible representative. -/
theorem idealClass_surjective : Function.Surjective
    (idealClass : IntegralUnitIdeal S → ClassGroup S) := by
  intro C
  refine ClassGroup.induction (FractionRing S) ?_ C
  intro U
  obtain ⟨V, hV, hclass⟩ := exists_integralUnitRep U
  let I : IntegralUnitIdeal S := ⟨U.1.num, ⟨V, hV⟩⟩
  refine ⟨I, ?_⟩
  calc
    idealClass I = ClassGroup.mk (FractionRing S) V := by
      unfold idealClass
      congr 1
      apply Units.ext
      exact I.2.unit_spec.trans hV.symm
    _ = ClassGroup.mk (FractionRing S) U := hclass

/-- Divide an integral invertible ideal by an invertible maximal ideal that
contains it.  The quotient stays integral and invertible. -/
theorem exists_mul_eq_of_le
    (P I : IntegralUnitIdeal S) (hPI : (I : Ideal S) ≤ (P : Ideal S)) :
    ∃ J : IntegralUnitIdeal S, P * J = I := by
  let PF : FractionalIdeal S⁰ (FractionRing S) := (P : Ideal S)
  let IF : FractionalIdeal S⁰ (FractionRing S) := (I : Ideal S)
  let JF : FractionalIdeal S⁰ (FractionRing S) := PF⁻¹ * IF
  have hPFunit : IsUnit PF := P.2
  have hIFunit : IsUnit IF := I.2
  have hPFmul : PF * PF⁻¹ = 1 :=
    (FractionalIdeal.mul_inv_cancel_iff_isUnit (K := FractionRing S)).mpr hPFunit
  have hPFinvunit : IsUnit PF⁻¹ := by
    refine IsUnit.of_mul_eq_one PF ?_
    rw [mul_comm, hPFmul]
  have hJFunit : IsUnit JF := hPFinvunit.mul hIFunit
  have hJFle : JF ≤ 1 := by
    dsimp only [JF]
    calc
      PF⁻¹ * IF ≤ PF⁻¹ * PF := by
        gcongr
        simpa only [PF, IF, FractionalIdeal.coeIdeal_le_coeIdeal] using hPI
      _ = 1 := by rw [mul_comm, hPFmul]
  obtain ⟨J, hJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hJFle
  let JU : IntegralUnitIdeal S := ⟨J, ⟨hJFunit.unit,
    hJFunit.unit_spec.trans hJ.symm⟩⟩
  refine ⟨JU, ?_⟩
  apply Subtype.ext
  have hfrac : (((P : Ideal S) * (J : Ideal S) : Ideal S) :
      FractionalIdeal S⁰ (FractionRing S)) =
      ((I : Ideal S) : FractionalIdeal S⁰ (FractionRing S)) := by
    rw [FractionalIdeal.coeIdeal_mul]
    change PF * (J : FractionalIdeal S⁰ (FractionRing S)) = IF
    rw [hJ]
    dsimp only [JF]
    calc
      PF * (PF⁻¹ * IF) = (PF * PF⁻¹) * IF := by ac_rfl
      _ = IF := by rw [hPFmul, one_mul]
  exact FractionalIdeal.coeIdeal_injective (R := S)
    (K := FractionRing S) hfrac

theorem mul_right_cancel (I J K : IntegralUnitIdeal S) (h : I * K = J * K) :
    I = J := by
  have hfrac :
      ((I.unit : (FractionalIdeal S⁰ (FractionRing S))ˣ) :
          FractionalIdeal S⁰ (FractionRing S)) *
        ((K.unit : (FractionalIdeal S⁰ (FractionRing S))ˣ) :
          FractionalIdeal S⁰ (FractionRing S)) =
      ((J.unit : (FractionalIdeal S⁰ (FractionRing S))ˣ) :
          FractionalIdeal S⁰ (FractionRing S)) *
        ((K.unit : (FractionalIdeal S⁰ (FractionRing S))ˣ) :
          FractionalIdeal S⁰ (FractionRing S)) := by
    rw [unit_coe I, unit_coe J, unit_coe K]
    rw [← FractionalIdeal.coeIdeal_mul, ← FractionalIdeal.coeIdeal_mul]
    exact congrArg (fun L : IntegralUnitIdeal S ↦
      ((L : Ideal S) : FractionalIdeal S⁰ (FractionRing S))) h
  have hu : I.unit * K.unit = J.unit * K.unit := by
    apply Units.ext
    exact hfrac
  have hu' : I.unit = J.unit := by
    calc
      I.unit = (I.unit * K.unit) * K.unit⁻¹ := by simp
      _ = (J.unit * K.unit) * K.unit⁻¹ := by rw [hu]
      _ = J.unit := by simp
  apply ext
  apply FractionalIdeal.coeIdeal_injective (K := FractionRing S)
  have hval := congrArg
    (fun U : (FractionalIdeal S⁰ (FractionRing S))ˣ ↦
      (U : FractionalIdeal S⁰ (FractionRing S))) hu'
  simpa only [unit_coe] using hval

end IntegralUnitIdeal

/-- Inclusion reverses quotient cardinality for nonzero ideals in a finite
quotient ring. -/
theorem cardQuot_mono_of_le
    {S : Type*} [CommRing S] [IsDomain S] [Ring.HasFiniteQuotients S]
    {I J : Ideal S} (hI : I ≠ ⊥) (h : I ≤ J) :
    J.cardQuot ≤ I.cardQuot := by
  have hpos : 0 < I.cardQuot := Ring.HasFiniteQuotients.cardQuot_pos I hI
  have hmul := AddSubgroup.relIndex_mul_index
    (show I.toAddSubgroup ≤ J.toAddSubgroup from h)
  change I.toAddSubgroup.relIndex J.toAddSubgroup * J.cardQuot = I.cardQuot at hmul
  have hr : 0 < I.toAddSubgroup.relIndex J.toAddSubgroup :=
    Nat.pos_of_mul_pos_right (hmul ▸ hpos)
  rw [← hmul]
  exact Nat.le_mul_of_pos_left _ hr

noncomputable def principalIntegralUnitIdeal
    {S : Type*} [CommRing S] [IsDomain S]
    (I : Ideal S) (hI : I.IsPrincipal) (hI0 : I ≠ ⊥) :
    IntegralUnitIdeal S := by
  have hprincipal :
      (((I : Ideal S) : FractionalIdeal S⁰ (FractionRing S)) :
        Submodule S (FractionRing S)).IsPrincipal :=
    (IsFractionRing.coeSubmodule_isPrincipal S (FractionRing S)).mpr hI
  letI : (((I : Ideal S) : FractionalIdeal S⁰ (FractionRing S)) :
      Submodule S (FractionRing S)).IsPrincipal := hprincipal
  have hfrac0 : ((I : Ideal S) :
      FractionalIdeal S⁰ (FractionRing S)) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hI0
  refine ⟨I, IsUnit.of_mul_eq_one
    (((I : Ideal S) : FractionalIdeal S⁰ (FractionRing S))⁻¹) ?_⟩
  exact FractionalIdeal.invertible_of_principal (K := FractionRing S)
    ((I : Ideal S) : FractionalIdeal S⁰ (FractionRing S)) hfrac0

theorem principalIntegralUnitIdeal_idealClass
    {S : Type*} [CommRing S] [IsDomain S]
    (I : Ideal S) (hI : I.IsPrincipal) (hI0 : I ≠ ⊥) :
    IntegralUnitIdeal.idealClass
        (principalIntegralUnitIdeal I hI hI0) = 1 := by
  unfold IntegralUnitIdeal.idealClass
  apply ClassGroup.mk_eq_one_iff.mpr
  rw [IntegralUnitIdeal.unit_coe]
  change (((I : Ideal S) : FractionalIdeal S⁰ (FractionRing S)) :
    Submodule S (FractionRing S)).IsPrincipal
  exact (IsFractionRing.coeSubmodule_isPrincipal S
    (FractionRing S)).mpr hI

noncomputable def specialOrientedIntegralUnitIdeal
    (p q : ℕ) [Fact p.Prime]
    (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (h : ¬ IsQuadraticObstruction (p ^ 3) q) (b : Bool) :
    IntegralUnitIdeal (Zsqrtd (-(p : ℤ) ^ 3)) :=
  ⟨specialOrientedSplitIdeal p q h b,
    ⟨specialOrientedSplitUnit p q hq hq2 hqp h b,
      specialOrientedSplitUnit_coe p q hq hq2 hqp h b⟩⟩

theorem specialOrientedIntegralUnitIdeal_idealClass
    (p q : ℕ) [Fact p.Prime]
    (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (h : ¬ IsQuadraticObstruction (p ^ 3) q) (b : Bool) :
    IntegralUnitIdeal.idealClass
        (specialOrientedIntegralUnitIdeal p q hq hq2 hqp h b) =
      if b then (specialSplitPrimeClass p q hq hq2 hqp h)⁻¹
      else specialSplitPrimeClass p q hq hq2 hqp h := by
  unfold IntegralUnitIdeal.idealClass IntegralUnitIdeal.unit
  have hu : (specialOrientedIntegralUnitIdeal p q hq hq2 hqp h b).2.unit =
      specialOrientedSplitUnit p q hq hq2 hqp h b := by
    apply Units.ext
    exact (specialOrientedIntegralUnitIdeal p q hq hq2 hqp h b).2.unit_spec.trans
      (specialOrientedSplitUnit_coe p q hq hq2 hqp h b).symm
  rw [hu]
  exact specialOrientedSplitUnit_class p q hq hq2 hqp h b

theorem specialOrientedIntegralUnitIdeal_cardQuot
    (p q : ℕ) [Fact p.Prime]
    (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (h : ¬ IsQuadraticObstruction (p ^ 3) q) (b : Bool) :
    ((specialOrientedIntegralUnitIdeal p q hq hq2 hqp h b :
      IntegralUnitIdeal (Zsqrtd (-(p : ℤ) ^ 3))) :
        Ideal (Zsqrtd (-(p : ℤ) ^ 3))).cardQuot = q := by
  let : NeZero q := ⟨hq.ne_zero⟩
  exact orientedSplitIdeal_cardQuot (-(p : ℤ) ^ 3) q
    (specialSplitRoot p q h) (specialSplitRoot_sq p q h) b

theorem specialOrientedIntegralUnitIdeal_isMaximal
    (p q : ℕ) [Fact p.Prime]
    (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (h : ¬ IsQuadraticObstruction (p ^ 3) q) (b : Bool) :
    (((specialOrientedIntegralUnitIdeal p q hq hq2 hqp h b :
      IntegralUnitIdeal (Zsqrtd (-(p : ℤ) ^ 3))) :
        Ideal (Zsqrtd (-(p : ℤ) ^ 3)))).IsMaximal := by
  let : Fact q.Prime := ⟨hq⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  cases b
  · rw [show ((specialOrientedIntegralUnitIdeal p q hq hq2 hqp h false :
        IntegralUnitIdeal (Zsqrtd (-(p : ℤ) ^ 3))) :
          Ideal (Zsqrtd (-(p : ℤ) ^ 3))) =
        splitPrimeIdeal (-(p : ℤ) ^ 3) q (specialSplitRoot p q h) by
      rfl]
    rw [splitPrimeIdeal_eq_ker (-(p : ℤ) ^ 3) q
      (specialSplitRoot p q h) (specialSplitRoot_sq p q h)]
    exact RingHom.ker_isMaximal_of_surjective _
      (splitEval_surjective (-(p : ℤ) ^ 3) q
        (specialSplitRoot p q h) (specialSplitRoot_sq p q h))
  · rw [show ((specialOrientedIntegralUnitIdeal p q hq hq2 hqp h true :
        IntegralUnitIdeal (Zsqrtd (-(p : ℤ) ^ 3))) :
          Ideal (Zsqrtd (-(p : ℤ) ^ 3))) =
        splitConjugateIdeal (-(p : ℤ) ^ 3) q (specialSplitRoot p q h) by
      rfl]
    rw [splitConjugateIdeal_eq_ker (-(p : ℤ) ^ 3) q
      (specialSplitRoot p q h) (specialSplitRoot_sq p q h)]
    exact RingHom.ker_isMaximal_of_surjective _
      (splitEval_surjective (-(p : ℤ) ^ 3) q
        (-(specialSplitRoot p q h)) (by
          simpa using specialSplitRoot_sq p q h))

/-- A class outside a subgroup has an explicit split prime factor outside
that subgroup, provided the integral invertible ideal is coprime to the
conductor. -/
theorem exists_specialSplitPrimeClass_not_mem_of_idealClass_not_mem
    {p : ℕ} [Fact p.Prime]
    (H : Subgroup (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3))))
    (I : IntegralUnitIdeal (Zsqrtd (-(p : ℤ) ^ 3)))
    (hclass : IntegralUnitIdeal.idealClass I ∉ H)
    (hcop : IsCoprime (I : Ideal (Zsqrtd (-(p : ℤ) ^ 3)))
      (Ideal.span ({Zsqrtd.ofInt ((2 * p : ℕ) : ℤ)} :
        Set (Zsqrtd (-(p : ℤ) ^ 3))))) :
    ∃ q : ℕ, ∃ hq : q.Prime, ∃ hq2 : q ≠ 2, ∃ hqp : q ≠ p,
      ∃ h : ¬ IsQuadraticObstruction (p ^ 3) q,
        specialSplitPrimeClass p q hq hq2 hqp h ∉ H ∧
          q ≤ (I : Ideal (Zsqrtd (-(p : ℤ) ^ 3))).cardQuot ∧
          ∃ b : Bool, ∃ J : IntegralUnitIdeal
              (Zsqrtd (-(p : ℤ) ^ 3)),
            specialOrientedIntegralUnitIdeal p q hq hq2 hqp h b * J = I := by
  let O := Zsqrtd (-(p : ℤ) ^ 3)
  let F : Ideal O := Ideal.span
    ({Zsqrtd.ofInt ((2 * p : ℕ) : ℤ)} : Set O)
  let : Module.Free ℤ O :=
    Module.Free.of_basis (zsqrtdBasis (-(p : ℤ) ^ 3))
  let : Module.Finite ℤ O :=
    Module.Finite.of_basis (zsqrtdBasis (-(p : ℤ) ^ 3))
  let : Ring.HasFiniteQuotients O := inferInstance
  suffices ∀ n : ℕ, ∀ I : IntegralUnitIdeal O,
      (I : Ideal O).cardQuot = n →
      IntegralUnitIdeal.idealClass I ∉ H →
      IsCoprime (I : Ideal O) F →
      ∃ q : ℕ, ∃ hq : q.Prime, ∃ hq2 : q ≠ 2, ∃ hqp : q ≠ p,
        ∃ h : ¬ IsQuadraticObstruction (p ^ 3) q,
          specialSplitPrimeClass p q hq hq2 hqp h ∉ H ∧
            q ≤ (I : Ideal O).cardQuot ∧
            ∃ b : Bool, ∃ J : IntegralUnitIdeal O,
              specialOrientedIntegralUnitIdeal p q hq hq2 hqp h b * J = I by
    simpa only [O, F] using this (I : Ideal O).cardQuot I rfl hclass hcop
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro I hnorm hclassI hcopI
      have hIneTop : (I : Ideal O) ≠ ⊤ := by
        intro htop
        have hIeq : I = 1 := IntegralUnitIdeal.ext
          (htop.trans IntegralUnitIdeal.coe_one.symm)
        subst I
        exact hclassI (by simpa using H.one_mem)
      obtain ⟨P, hPmax, hIP⟩ := Ideal.exists_le_maximal (I : Ideal O) hIneTop
      have hcond : Zsqrtd.ofInt ((2 * p : ℕ) : ℤ) ∉ P := by
        intro hfP
        have hFle : F ≤ P := by
          dsimp only [F]
          exact (Ideal.span_singleton_le_iff_mem P).mpr hfP
        have htopLe : (⊤ : Ideal O) ≤ P := by
          rw [← hcopI.sup_eq]
          exact sup_le hIP hFle
        exact hPmax.ne_top (top_unique htopLe)
      have hPneBot : P ≠ ⊥ := by
        intro hPbot
        have hIbot : (I : Ideal O) = ⊥ := le_bot_iff.mp (hPbot ▸ hIP)
        have hIzero : (((I : Ideal O) :
            FractionalIdeal O⁰ (FractionRing O))) = 0 := by
          rw [hIbot]
          rfl
        exact I.2.ne_zero hIzero
      have factorStep
          (PU : IntegralUnitIdeal O)
          (hPU : (PU : Ideal O) = P) :
          ∃ J : IntegralUnitIdeal O,
            PU * J = I ∧
            n = (PU : Ideal O).cardQuot * (J : Ideal O).cardQuot ∧
            (J : Ideal O).cardQuot < n ∧
            IsCoprime (J : Ideal O) F := by
        have hIlePU : (I : Ideal O) ≤ (PU : Ideal O) := hPU ▸ hIP
        obtain ⟨J, hmul⟩ := IntegralUnitIdeal.exists_mul_eq_of_le PU I hIlePU
        have hcoeMul : (PU : Ideal O) * (J : Ideal O) = (I : Ideal O) :=
          congrArg (fun A : IntegralUnitIdeal O ↦ (A : Ideal O)) hmul
        have hcard := cardQuot_mul_of_isUnit_right
          (PU : Ideal O) (J : Ideal O) (hPU ▸ hPmax) J.2
        rw [hcoeMul, hnorm] at hcard
        have hJneBot : (J : Ideal O) ≠ ⊥ := by
          intro hJbot
          have hJzero : (((J : Ideal O) :
              FractionalIdeal O⁰ (FractionRing O))) = 0 := by
            rw [hJbot]
            rfl
          exact J.2.ne_zero hJzero
        have hPcardPos : 0 < (PU : Ideal O).cardQuot :=
          Ring.HasFiniteQuotients.cardQuot_pos _ (hPU.trans_ne hPneBot)
        have hPcardNeOne : (PU : Ideal O).cardQuot ≠ 1 := by
          intro hone
          have htop : (PU : Ideal O) = ⊤ :=
            Submodule.cardQuot_eq_one_iff.mp hone
          exact hPmax.ne_top (hPU.symm.trans htop)
        have hJcardPos : 0 < (J : Ideal O).cardQuot :=
          Ring.HasFiniteQuotients.cardQuot_pos _ hJneBot
        have hPcardOne : 1 < (PU : Ideal O).cardQuot := by omega
        have hlt : (J : Ideal O).cardQuot < n := by
          rw [hcard]
          exact lt_mul_of_one_lt_left hJcardPos hPcardOne
        have hIleJ : (I : Ideal O) ≤ (J : Ideal O) := by
          rw [← hcoeMul]
          calc
            (PU : Ideal O) * (J : Ideal O) ≤ ⊤ * (J : Ideal O) := by
              gcongr
              exact le_top
            _ = (J : Ideal O) := Ideal.top_mul _
        have hcopJ : IsCoprime (J : Ideal O) F := by
          apply Ideal.isCoprime_iff_sup_eq.mpr
          apply top_unique
          calc
            (⊤ : Ideal O) = (I : Ideal O) ⊔ F := hcopI.sup_eq.symm
            _ ≤ (J : Ideal O) ⊔ F := sup_le_sup_right hIleJ F
        exact ⟨J, hmul, hcard, hlt, hcopJ⟩
      rcases specialMaximal_isPrincipal_or_eq_orientedSplit P hPmax hcond with
        hPprincipal | ⟨q, hq, hq2, hqp, hsplit, b, hPeq⟩
      · let PU : IntegralUnitIdeal O :=
          principalIntegralUnitIdeal P hPprincipal hPneBot
        have hPU : (PU : Ideal O) = P := rfl
        obtain ⟨J, hmul, hcard, hlt, hcopJ⟩ := factorStep PU hPU
        have hclassPU : IntegralUnitIdeal.idealClass PU = 1 :=
          principalIntegralUnitIdeal_idealClass P hPprincipal hPneBot
        have hclassJ : IntegralUnitIdeal.idealClass J ∉ H := by
          intro hJH
          apply hclassI
          have hclasses := congrArg IntegralUnitIdeal.idealClass hmul
          rw [IntegralUnitIdeal.idealClass_mul, hclassPU, one_mul] at hclasses
          rw [← hclasses]
          exact hJH
        obtain ⟨q, hq, hq2, hqp, hs, hqout, hqJ, b, K, hK⟩ :=
          ih (J : Ideal O).cardQuot hlt J rfl hclassJ hcopJ
        refine ⟨q, hq, hq2, hqp, hs, hqout, hqJ.trans ?_, b, PU * K, ?_⟩
        · rw [hnorm]
          exact hlt.le
        · calc
            specialOrientedIntegralUnitIdeal p q hq hq2 hqp hs b * (PU * K) =
                PU * (specialOrientedIntegralUnitIdeal p q hq hq2 hqp hs b * K) := by
                  ac_rfl
            _ = PU * J := by rw [hK]
            _ = I := hmul
      · let PU : IntegralUnitIdeal O :=
          specialOrientedIntegralUnitIdeal p q hq hq2 hqp hsplit b
        have hPU : (PU : Ideal O) = P := by
          exact hPeq.symm
        obtain ⟨J, hmul, hcard, hlt, hcopJ⟩ := factorStep PU hPU
        let g := specialSplitPrimeClass p q hq hq2 hqp hsplit
        have hclassPU : IntegralUnitIdeal.idealClass PU =
            if b then g⁻¹ else g := by
          exact specialOrientedIntegralUnitIdeal_idealClass
            p q hq hq2 hqp hsplit b
        by_cases hg : g ∈ H
        · have hPUH : IntegralUnitIdeal.idealClass PU ∈ H := by
            rw [hclassPU]
            cases b
            · simpa using hg
            · simpa using H.inv_mem hg
          have hclassJ : IntegralUnitIdeal.idealClass J ∉ H := by
            intro hJH
            apply hclassI
            have hclasses := congrArg IntegralUnitIdeal.idealClass hmul
            rw [IntegralUnitIdeal.idealClass_mul] at hclasses
            rw [← hclasses]
            exact H.mul_mem hPUH hJH
          obtain ⟨r, hr, hr2, hrp, hs, hrout, hrJ, c, K, hK⟩ :=
            ih (J : Ideal O).cardQuot hlt J rfl hclassJ hcopJ
          refine ⟨r, hr, hr2, hrp, hs, hrout, hrJ.trans ?_, c, PU * K, ?_⟩
          · rw [hnorm]
            exact hlt.le
          · calc
              specialOrientedIntegralUnitIdeal p r hr hr2 hrp hs c * (PU * K) =
                  PU * (specialOrientedIntegralUnitIdeal p r hr hr2 hrp hs c * K) := by
                    ac_rfl
              _ = PU * J := by rw [hK]
              _ = I := hmul
        · refine ⟨q, hq, hq2, hqp, hsplit, hg, ?_, b, J, hmul⟩
          have hqcard : (PU : Ideal O).cardQuot = q :=
            specialOrientedIntegralUnitIdeal_cardQuot
              p q hq hq2 hqp hsplit b
          have hJneBot : (J : Ideal O) ≠ ⊥ := by
            intro hzero
            have : (((J : Ideal O) : FractionalIdeal O⁰ (FractionRing O))) = 0 := by
              rw [hzero]
              rfl
            exact J.2.ne_zero this
          have hJpos : 0 < (J : Ideal O).cardQuot :=
            Ring.HasFiniteQuotients.cardQuot_pos _ hJneBot
          rw [hnorm, hcard, hqcard]
          exact Nat.le_mul_of_pos_right q hJpos

/-! ## Linear lattice-point bounds for the negative quadratic norm -/

def SpecialNormBall (p K : ℕ) :=
  {z : Zsqrtd (-(p : ℤ) ^ 3) // z.norm.natAbs ≤ K}

noncomputable def finiteSpecialNormBall {p K : ℕ} (hp : 1 ≤ p) :
    Finite (SpecialNormBall p K) := by
  let s := K.sqrt
  let A := {a : ℤ // a ∈ Finset.Icc (-(s : ℤ)) (s : ℤ)}
  let f : SpecialNormBall p K → A × A := fun z ↦ by
    have hnorm : z.1.norm.natAbs =
        z.1.re.natAbs ^ 2 + p ^ 3 * z.1.im.natAbs ^ 2 := by
      rw [Zsqrtd.norm_def]
      have hd : z.1.re * z.1.re - (-(p : ℤ) ^ 3) * z.1.im * z.1.im =
          z.1.re ^ 2 + (p : ℤ) ^ 3 * z.1.im ^ 2 := by ring
      rw [hd, Int.natAbs_add_of_nonneg (sq_nonneg z.1.re)
        (mul_nonneg (by positivity) (sq_nonneg z.1.im)),
        Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow,
        Int.natAbs_pow, Int.natAbs_natCast]
    have hreSq : z.1.re.natAbs ^ 2 ≤ K := by
      calc
        z.1.re.natAbs ^ 2 ≤
            z.1.re.natAbs ^ 2 + p ^ 3 * z.1.im.natAbs ^ 2 :=
          Nat.le_add_right _ _
        _ = z.1.norm.natAbs := hnorm.symm
        _ ≤ K := z.2
    have himSq : z.1.im.natAbs ^ 2 ≤ K := by
      calc
        z.1.im.natAbs ^ 2 ≤ p ^ 3 * z.1.im.natAbs ^ 2 :=
          Nat.le_mul_of_pos_left _ (by positivity)
        _ ≤ z.1.re.natAbs ^ 2 + p ^ 3 * z.1.im.natAbs ^ 2 :=
          Nat.le_add_left _ _
        _ = z.1.norm.natAbs := hnorm.symm
        _ ≤ K := z.2
    have hreAbs : z.1.re.natAbs ≤ s := Nat.le_sqrt'.mpr hreSq
    have himAbs : z.1.im.natAbs ≤ s := Nat.le_sqrt'.mpr himSq
    have hreInt : |z.1.re| ≤ (s : ℤ) := by
      have hreCast : (z.1.re.natAbs : ℤ) ≤ (s : ℤ) := by exact_mod_cast hreAbs
      simpa using hreCast
    have himInt : |z.1.im| ≤ (s : ℤ) := by
      have himCast : (z.1.im.natAbs : ℤ) ≤ (s : ℤ) := by exact_mod_cast himAbs
      simpa using himCast
    exact
      (⟨z.1.re, Finset.mem_Icc.mpr (abs_le.mp hreInt)⟩,
       ⟨z.1.im, Finset.mem_Icc.mpr (abs_le.mp himInt)⟩)
  have hf : Function.Injective f := by
    intro z w hzw
    apply Subtype.ext
    apply Zsqrtd.ext
    · exact congrArg (fun x : A × A ↦ x.1.1) hzw
    · exact congrArg (fun x : A × A ↦ x.2.1) hzw
  let : Fintype A := Fintype.ofFinset (Finset.Icc (-(s : ℤ)) (s : ℤ))
    (fun a ↦ Iff.rfl)
  exact Finite.of_injective f hf

theorem natCard_specialNormBall_le {p K : ℕ} (hp : 1 ≤ p) (hK : 1 ≤ K) :
    Nat.card (SpecialNormBall p K) ≤ 9 * K := by
  let : Finite (SpecialNormBall p K) := finiteSpecialNormBall hp
  let s := K.sqrt
  let A := {a : ℤ // a ∈ Finset.Icc (-(s : ℤ)) (s : ℤ)}
  let f : SpecialNormBall p K → A × A := fun z ↦ by
    have hnorm : z.1.norm.natAbs =
        z.1.re.natAbs ^ 2 + p ^ 3 * z.1.im.natAbs ^ 2 := by
      rw [Zsqrtd.norm_def]
      have hd : z.1.re * z.1.re - (-(p : ℤ) ^ 3) * z.1.im * z.1.im =
          z.1.re ^ 2 + (p : ℤ) ^ 3 * z.1.im ^ 2 := by ring
      rw [hd, Int.natAbs_add_of_nonneg (sq_nonneg z.1.re)
        (mul_nonneg (by positivity) (sq_nonneg z.1.im)),
        Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow,
        Int.natAbs_pow, Int.natAbs_natCast]
    have hreSq : z.1.re.natAbs ^ 2 ≤ K := by
      calc
        z.1.re.natAbs ^ 2 ≤
            z.1.re.natAbs ^ 2 + p ^ 3 * z.1.im.natAbs ^ 2 :=
          Nat.le_add_right _ _
        _ = z.1.norm.natAbs := hnorm.symm
        _ ≤ K := z.2
    have himSq : z.1.im.natAbs ^ 2 ≤ K := by
      have hp3 : 1 ≤ p ^ 3 := one_le_pow₀ hp
      calc
        z.1.im.natAbs ^ 2 ≤ p ^ 3 * z.1.im.natAbs ^ 2 :=
          Nat.le_mul_of_pos_left _ (by positivity)
        _ ≤ z.1.re.natAbs ^ 2 + p ^ 3 * z.1.im.natAbs ^ 2 :=
          Nat.le_add_left _ _
        _ = z.1.norm.natAbs := hnorm.symm
        _ ≤ K := z.2
    have hreAbs : z.1.re.natAbs ≤ s := Nat.le_sqrt'.mpr hreSq
    have himAbs : z.1.im.natAbs ≤ s := Nat.le_sqrt'.mpr himSq
    have hreInt : |z.1.re| ≤ (s : ℤ) := by
      have hreCast : (z.1.re.natAbs : ℤ) ≤ (s : ℤ) := by exact_mod_cast hreAbs
      simpa using hreCast
    have himInt : |z.1.im| ≤ (s : ℤ) := by
      have himCast : (z.1.im.natAbs : ℤ) ≤ (s : ℤ) := by exact_mod_cast himAbs
      simpa using himCast
    exact
      (⟨z.1.re, Finset.mem_Icc.mpr (abs_le.mp hreInt)⟩,
       ⟨z.1.im, Finset.mem_Icc.mpr (abs_le.mp himInt)⟩)
  have hf : Function.Injective f := by
    intro z w hzw
    apply Subtype.ext
    apply Zsqrtd.ext
    · exact congrArg (fun x : A × A ↦ x.1.1) hzw
    · exact congrArg (fun x : A × A ↦ x.2.1) hzw
  let : Fintype A := Fintype.ofFinset (Finset.Icc (-(s : ℤ)) (s : ℤ))
    (fun a ↦ Iff.rfl)
  have hcard := Nat.card_le_card_of_injective f hf
  have hcardA : Nat.card A = 2 * s + 1 := by
    calc
      Nat.card A = (Finset.Icc (-(s : ℤ)) (s : ℤ)).card := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_of_finset' _ (fun a ↦ Iff.rfl)
      _ = 2 * s + 1 := by
        simp only [Int.card_Icc]
        have hnonneg : (0 : ℤ) ≤ (s : ℤ) + 1 - -(s : ℤ) := by omega
        have hto := Int.toNat_of_nonneg hnonneg
        have hrhs : (((2 * s + 1 : ℕ) : ℤ)) =
            (s : ℤ) + 1 - -(s : ℤ) := by push_cast; ring
        exact_mod_cast hto.trans hrhs.symm
  rw [Nat.card_prod, hcardA] at hcard
  calc
    Nat.card (SpecialNormBall p K) ≤ (2 * s + 1) * (2 * s + 1) := hcard
    _ ≤ 9 * K := by
      have hsSq : s * s ≤ K := Nat.sqrt_le K
      have hsK : s ≤ K := (Nat.sqrt_le_self K)
      nlinarith

def SpecialClassBall (p N : ℕ) [Fact p.Prime]
    (C : ClassGroup (Zsqrtd (-(p : ℤ) ^ 3))) :=
  {I : IntegralUnitIdeal (Zsqrtd (-(p : ℤ) ^ 3)) //
    IntegralUnitIdeal.idealClass I = C ∧
      (I : Ideal (Zsqrtd (-(p : ℤ) ^ 3))).cardQuot ≤ N}

noncomputable def finiteSpecialClassBall
    {p N : ℕ} [Fact p.Prime]
    (C : ClassGroup (Zsqrtd (-(p : ℤ) ^ 3))) :
    Finite (SpecialClassBall p N C) := by
  let O := Zsqrtd (-(p : ℤ) ^ 3)
  let : Module.Free ℤ O :=
    Module.Free.of_basis (zsqrtdBasis (-(p : ℤ) ^ 3))
  let : Module.Finite ℤ O :=
    Module.Finite.of_basis (zsqrtdBasis (-(p : ℤ) ^ 3))
  let : Ring.HasFiniteQuotients O := inferInstance
  let a : O := N.factorial
  have ha : a ≠ 0 := by
    intro hzero
    change (Zsqrtd.ofInt (N.factorial : ℤ) :
      Zsqrtd (-(p : ℤ) ^ 3)) = 0 at hzero
    have hz : (N.factorial : ℤ) = 0 := by
      simpa using congrArg Zsqrtd.re hzero
    have : N.factorial = 0 := by exact_mod_cast hz
    exact Nat.factorial_ne_zero N this
  let T := {J : Ideal O // a ∈ J}
  let : Finite T :=
    (Ring.HasFiniteQuotients.finite_setOfPred_mem a ha).to_subtype
  let f : SpecialClassBall p N C → T := fun I ↦ by
    have hIne : (I.1 : Ideal O) ≠ ⊥ := by
      intro hzero
      have hz : (((I.1 : Ideal O) :
          FractionalIdeal O⁰ (FractionRing O))) = 0 := by rw [hzero]; rfl
      exact I.1.2.ne_zero hz
    have hnpos : 0 < (I.1 : Ideal O).cardQuot :=
      Ring.HasFiniteQuotients.cardQuot_pos _ hIne
    have hnmem : (((I.1 : Ideal O).cardQuot : ℕ) : O) ∈
        (I.1 : Ideal O) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact Ideal.Quotient.index_eq_zero (I.1 : Ideal O)
    let hd := Nat.dvd_factorial hnpos I.2.2
    refine ⟨(I.1 : Ideal O), ?_⟩
    dsimp only [a]
    rw [hd.choose_spec, Nat.cast_mul]
    exact (I.1 : Ideal O).mul_mem_right (hd.choose : O) hnmem
  exact Finite.of_injective f (by
    intro I J hIJ
    apply Subtype.ext
    apply IntegralUnitIdeal.ext
    have hval := congrArg (fun K : T ↦ (K : Ideal O)) hIJ
    dsimp only [f] at hval
    exact hval)

/-- Ideals in one Picard class have a linear upper bound.  The constant is
the square of the norm of a fixed integral representative of the inverse
class. -/
theorem exists_natCard_specialClassBall_le
    {p : ℕ} [Fact p.Prime]
    (C : ClassGroup (Zsqrtd (-(p : ℤ) ^ 3))) :
    ∃ B : ℕ, 0 < B ∧ ∀ N : ℕ, 0 < N →
      Nat.card (SpecialClassBall p N C) ≤ B * N := by
  let O := Zsqrtd (-(p : ℤ) ^ 3)
  let : Module.Free ℤ O :=
    Module.Free.of_basis (zsqrtdBasis (-(p : ℤ) ^ 3))
  let : Module.Finite ℤ O :=
    Module.Finite.of_basis (zsqrtdBasis (-(p : ℤ) ^ 3))
  let : Ring.HasFiniteQuotients O := inferInstance
  obtain ⟨J, hJclass⟩ :=
    (IntegralUnitIdeal.idealClass_surjective
      (S := O) (C⁻¹ : ClassGroup O))
  let m := (J : Ideal O).cardQuot
  have hJne : (J : Ideal O) ≠ ⊥ := by
    intro hzero
    have hz : (((J : Ideal O) :
        FractionalIdeal O⁰ (FractionRing O))) = 0 := by rw [hzero]; rfl
    exact J.2.ne_zero hz
  have hm : 0 < m := Ring.HasFiniteQuotients.cardQuot_pos _ hJne
  refine ⟨9 * m ^ 2, by positivity, ?_⟩
  intro N hN
  have hm_mem : (m : O) ∈ (J : Ideal O) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact Ideal.Quotient.index_eq_zero (J : Ideal O)
  have hmO : (m : O) ≠ 0 := by
    intro hz
    change (Zsqrtd.ofInt (m : ℤ) :
      Zsqrtd (-(p : ℤ) ^ 3)) = 0 at hz
    have hm0Z : (m : ℤ) = 0 := by
      simpa using congrArg Zsqrtd.re hz
    have hm0 : m = 0 := by exact_mod_cast hm0Z
    omega
  let P : Ideal O := Ideal.span ({(m : O)} : Set O)
  have hPne : P ≠ ⊥ := by
    intro hzero
    have hz : (m : O) ∈ (⊥ : Ideal O) := by
      rw [← hzero]
      exact Ideal.mem_span_singleton_self (m : O)
    exact hmO (by simpa using hz)
  have hPle : P ≤ (J : Ideal O) := by
    exact (Ideal.span_singleton_le_iff_mem _).mpr hm_mem
  have hproductClass (I : SpecialClassBall p N C) :
      IntegralUnitIdeal.idealClass (I.1 * J) = 1 := by
    rw [IntegralUnitIdeal.idealClass_mul, I.2.1, hJclass,
      mul_inv_cancel]
  have hproductPrincipal (I : SpecialClassBall p N C) :
      ((I.1 * J : IntegralUnitIdeal O) : Ideal O).IsPrincipal := by
    apply ideal_isPrincipal_of_class_eq_one
      ((I.1 * J : IntegralUnitIdeal O) : Ideal O) (I.1 * J).2
    exact hproductClass I
  have hexists (I : SpecialClassBall p N C) :
      ∃ z : O,
        ((I.1 * J : IntegralUnitIdeal O) : Ideal O) =
            Ideal.span ({z} : Set O) ∧
          (Algebra.norm ℤ z).natAbs =
            ((I.1 * J : IntegralUnitIdeal O) : Ideal O).cardQuot :=
    exists_generator_norm_natAbs_eq_cardQuot _ (hproductPrincipal I)
  let z : SpecialClassBall p N C → O := fun I ↦ (hexists I).choose
  have hzspan (I : SpecialClassBall p N C) :
      ((I.1 * J : IntegralUnitIdeal O) : Ideal O) =
        Ideal.span ({z I} : Set O) := (hexists I).choose_spec.1
  have hznorm (I : SpecialClassBall p N C) :
      (Algebra.norm ℤ (z I)).natAbs =
        ((I.1 * J : IntegralUnitIdeal O) : Ideal O).cardQuot :=
    (hexists I).choose_spec.2
  have hIne (I : SpecialClassBall p N C) : (I.1 : Ideal O) ≠ ⊥ := by
    intro hzero
    have hz : (((I.1 : Ideal O) :
        FractionalIdeal O⁰ (FractionRing O))) = 0 := by rw [hzero]; rfl
    exact I.1.2.ne_zero hz
  have hPIne (I : SpecialClassBall p N C) :
      P * (I.1 : Ideal O) ≠ ⊥ := by
    intro hzero
    obtain ⟨a, haP, ha0⟩ := P.ne_bot_iff.mp hPne
    obtain ⟨b, hbI, hb0⟩ := (I.1 : Ideal O).ne_bot_iff.mp (hIne I)
    have hab : a * b ∈ P * (I.1 : Ideal O) := Ideal.mul_mem_mul haP hbI
    rw [hzero] at hab
    have hab0 : a * b = 0 := by simpa using hab
    exact (mul_ne_zero ha0 hb0) hab0
  have hnormBound (I : SpecialClassBall p N C) :
      (z I).norm.natAbs ≤ m ^ 2 * N := by
    have hle : P * (I.1 : Ideal O) ≤
        (J : Ideal O) * (I.1 : Ideal O) := by gcongr
    have hcardle := cardQuot_mono_of_le (hPIne I) hle
    have hscale : (P * (I.1 : Ideal O)).cardQuot =
        m ^ 2 * (I.1 : Ideal O).cardQuot := by
      dsimp only [P]
      rw [cardQuot_span_singleton_mul_of_ne_bot
        (zsqrtdBasis (-(p : ℤ) ^ 3)) (I.1 : Ideal O) (hIne I) hmO,
        algebraNorm_zsqrtd]
      congr 1
      simp [O, Zsqrtd.norm_def, pow_two, Int.natAbs_mul]
    calc
      (z I).norm.natAbs = (Algebra.norm ℤ (z I)).natAbs := by
        rw [algebraNorm_zsqrtd]
      _ = ((I.1 * J : IntegralUnitIdeal O) : Ideal O).cardQuot := hznorm I
      _ = ((J : Ideal O) * (I.1 : Ideal O)).cardQuot := by
        congr 2
        exact mul_comm (I.1 : Ideal O) (J : Ideal O)
      _ ≤ (P * (I.1 : Ideal O)).cardQuot := hcardle
      _ = m ^ 2 * (I.1 : Ideal O).cardQuot := hscale
      _ ≤ m ^ 2 * N := Nat.mul_le_mul_left _ I.2.2
  let f : SpecialClassBall p N C → SpecialNormBall p (m ^ 2 * N) :=
    fun I ↦ ⟨z I, hnormBound I⟩
  let : Finite (SpecialNormBall p (m ^ 2 * N)) :=
    finiteSpecialNormBall (Fact.out : Nat.Prime p).one_le
  have hf : Function.Injective f := by
    intro I K hIK
    have hz : z I = z K := congrArg Subtype.val hIK
    apply Subtype.ext
    apply IntegralUnitIdeal.mul_right_cancel I.1 K.1 J
    apply IntegralUnitIdeal.ext
    rw [hzspan I, hzspan K, hz]
  have hcard := Nat.card_le_card_of_injective f hf
  have hKN : 1 ≤ m ^ 2 * N := Nat.one_le_iff_ne_zero.mpr
    (mul_ne_zero (pow_ne_zero _ (Nat.ne_of_gt hm)) (Nat.ne_of_gt hN))
  calc
    Nat.card (SpecialClassBall p N C) ≤
        Nat.card (SpecialNormBall p (m ^ 2 * N)) := hcard
    _ ≤ 9 * (m ^ 2 * N) :=
      natCard_specialNormBall_le (Fact.out : Nat.Prime p).one_le hKN
    _ = (9 * m ^ 2) * N := by ring

/-- The class-ball upper bound can be chosen uniformly over the finite
Picard group. -/
theorem exists_uniform_natCard_specialClassBall_le
    {p : ℕ} [Fact p.Prime] :
    ∃ B : ℕ, 0 < B ∧
      ∀ (C : ClassGroup (Zsqrtd (-(p : ℤ) ^ 3))) (N : ℕ), 0 < N →
        Nat.card (SpecialClassBall p N C) ≤ B * N := by
  let : Fintype (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3))) :=
    zsqrtdClassGroupFintype (-(p : ℤ) ^ 3)
      (specialDiscriminant_neg p Fact.out)
  choose B hBpos hB using fun C :
    ClassGroup (Zsqrtd (-(p : ℤ) ^ 3)) ↦
      exists_natCard_specialClassBall_le C
  let Bsum := ∑ C : ClassGroup (Zsqrtd (-(p : ℤ) ^ 3)), B C
  have hBsum : 0 < Bsum := by
    dsimp only [Bsum]
    exact Finset.sum_pos' (fun C _ ↦ (hBpos C).le)
      ⟨1, Finset.mem_univ _, hBpos 1⟩
  refine ⟨Bsum, hBsum, ?_⟩
  intro C N hN
  calc
    Nat.card (SpecialClassBall p N C) ≤ B C * N := hB C N hN
    _ ≤ Bsum * N := Nat.mul_le_mul_right N
      (Finset.single_le_sum (fun D _ ↦ (hBpos D).le) (Finset.mem_univ C))

/-- Ideals in a fixed class and norm ball which are divisible by a specified
integral invertible ideal. -/
def SpecialDivisibleClassBall (p N : ℕ) [Fact p.Prime]
    (C : ClassGroup (Zsqrtd (-(p : ℤ) ^ 3)))
    (P : IntegralUnitIdeal (Zsqrtd (-(p : ℤ) ^ 3))) :=
  {I : SpecialClassBall p N C //
    ∃ J : IntegralUnitIdeal (Zsqrtd (-(p : ℤ) ^ 3)), P * J = I.1}

/-- Divisibility by a maximal invertible ideal of norm `q` saves a factor
`q` in the class-ball count. -/
theorem natCard_specialDivisibleClassBall_le
    {p N q B : ℕ} [Fact p.Prime]
    (C : ClassGroup (Zsqrtd (-(p : ℤ) ^ 3)))
    (P : IntegralUnitIdeal (Zsqrtd (-(p : ℤ) ^ 3)))
    (hPmax : (P : Ideal (Zsqrtd (-(p : ℤ) ^ 3))).IsMaximal)
    (hPcard : (P : Ideal (Zsqrtd (-(p : ℤ) ^ 3))).cardQuot = q)
    (hB : ∀ (D : ClassGroup (Zsqrtd (-(p : ℤ) ^ 3))) (M : ℕ),
      0 < M → Nat.card (SpecialClassBall p M D) ≤ B * M) :
    Nat.card (SpecialDivisibleClassBall p N C P) ≤ B * (N / q) := by
  let O := Zsqrtd (-(p : ℤ) ^ 3)
  let : Module.Free ℤ O :=
    Module.Free.of_basis (zsqrtdBasis (-(p : ℤ) ^ 3))
  let : Module.Finite ℤ O :=
    Module.Finite.of_basis (zsqrtdBasis (-(p : ℤ) ^ 3))
  let : Ring.HasFiniteQuotients O := inferInstance
  have hPne : (P : Ideal O) ≠ ⊥ := by
    intro hzero
    have hz : (((P : Ideal O) :
        FractionalIdeal O⁰ (FractionRing O))) = 0 := by rw [hzero]; rfl
    exact P.2.ne_zero hz
  have hqpos : 0 < q := by
    rw [← hPcard]
    exact Ring.HasFiniteQuotients.cardQuot_pos _ hPne
  have hexists (I : SpecialDivisibleClassBall p N C P) :
      ∃ J : IntegralUnitIdeal O, P * J = I.1.1 := I.2
  let J : SpecialDivisibleClassBall p N C P → IntegralUnitIdeal O :=
    fun I ↦ (hexists I).choose
  have hmul (I : SpecialDivisibleClassBall p N C P) :
      P * J I = I.1.1 := (hexists I).choose_spec
  have hJclass (I : SpecialDivisibleClassBall p N C P) :
      IntegralUnitIdeal.idealClass (J I) =
        (IntegralUnitIdeal.idealClass P)⁻¹ * C := by
    have hc := congrArg IntegralUnitIdeal.idealClass (hmul I)
    rw [IntegralUnitIdeal.idealClass_mul] at hc
    calc
      IntegralUnitIdeal.idealClass (J I) =
          (IntegralUnitIdeal.idealClass P)⁻¹ *
            (IntegralUnitIdeal.idealClass P *
              IntegralUnitIdeal.idealClass (J I)) := by simp
      _ = (IntegralUnitIdeal.idealClass P)⁻¹ *
            IntegralUnitIdeal.idealClass I.1.1 := by rw [hc]
      _ = (IntegralUnitIdeal.idealClass P)⁻¹ * C := by rw [I.1.2.1]
  have hJcard (I : SpecialDivisibleClassBall p N C P) :
      (J I : Ideal O).cardQuot ≤ N / q := by
    have hcoe : (P : Ideal O) * (J I : Ideal O) =
        (I.1.1 : Ideal O) :=
      congrArg (fun K : IntegralUnitIdeal O ↦ (K : Ideal O)) (hmul I)
    have hproduct := cardQuot_mul_of_isUnit_right
      (P : Ideal O) (J I : Ideal O) hPmax (J I).2
    have heq : q * (J I : Ideal O).cardQuot =
        (I.1.1 : Ideal O).cardQuot := by
      calc
        q * (J I : Ideal O).cardQuot =
            (P : Ideal O).cardQuot * (J I : Ideal O).cardQuot := by
              rw [hPcard]
        _ = ((P : Ideal O) * (J I : Ideal O)).cardQuot := hproduct.symm
        _ = (I.1.1 : Ideal O).cardQuot := by rw [hcoe]
    rw [Nat.le_div_iff_mul_le hqpos]
    calc
      (J I : Ideal O).cardQuot * q =
          q * (J I : Ideal O).cardQuot := Nat.mul_comm _ _
      _ = (I.1.1 : Ideal O).cardQuot := heq
      _ ≤ N := I.1.2.2
  let f : SpecialDivisibleClassBall p N C P →
      SpecialClassBall p (N / q)
        ((IntegralUnitIdeal.idealClass P)⁻¹ * C) :=
    fun I ↦ ⟨J I, hJclass I, hJcard I⟩
  let : Finite (SpecialClassBall p (N / q)
      ((IntegralUnitIdeal.idealClass P)⁻¹ * C)) :=
    finiteSpecialClassBall _
  have hf : Function.Injective f := by
    intro I K hIK
    have hJK : J I = J K := congrArg Subtype.val hIK
    apply Subtype.ext
    apply Subtype.ext
    exact (hmul I).symm.trans ((congrArg (fun L ↦ P * L) hJK).trans (hmul K))
  have hcard := Nat.card_le_card_of_injective f hf
  by_cases hdiv : 0 < N / q
  · exact hcard.trans (hB _ _ hdiv)
  · have hzero : N / q = 0 := Nat.eq_zero_of_not_pos hdiv
    have htargetEmpty : IsEmpty (SpecialClassBall p (N / q)
        ((IntegralUnitIdeal.idealClass P)⁻¹ * C)) := ⟨fun K ↦ by
      have hKne : (K.1 : Ideal O) ≠ ⊥ := by
        intro hbot
        have hz : (((K.1 : Ideal O) :
            FractionalIdeal O⁰ (FractionRing O))) = 0 := by rw [hbot]; rfl
        exact K.1.2.ne_zero hz
      have hKpos : 0 < (K.1 : Ideal O).cardQuot :=
        Ring.HasFiniteQuotients.cardQuot_pos _ hKne
      have hKbound : (K.1 : Ideal O).cardQuot ≤ 0 :=
        K.2.2.trans_eq hzero
      omega⟩
    have htargetCard : Nat.card (SpecialClassBall p (N / q)
        ((IntegralUnitIdeal.idealClass P)⁻¹ * C)) = 0 :=
      Finite.card_eq_zero_iff.mpr htargetEmpty
    rw [htargetCard] at hcard
    simpa [hzero] using hcard

/-! ## A two-dimensional family of ideals in one class -/

/-- A positive representative of every residue class congruent to `1`
modulo the rational integer `m`. -/
def specialBoxElement (p m a b : ℕ) :
    Zsqrtd (-(p : ℤ) ^ 3) :=
  ⟨(1 + m * a : ℕ), (m * b : ℕ)⟩

@[simp] theorem specialBoxElement_re (p m a b : ℕ) :
    (specialBoxElement p m a b).re = (1 + m * a : ℕ) := rfl

@[simp] theorem specialBoxElement_im (p m a b : ℕ) :
    (specialBoxElement p m a b).im = (m * b : ℕ) := rfl

theorem specialBoxElement_ne_zero (p m a b : ℕ) :
    specialBoxElement p m a b ≠ 0 := by
  intro hzero
  have hre := congrArg Zsqrtd.re hzero
  have hnonneg : 0 ≤ (m : ℤ) * (a : ℤ) :=
    mul_nonneg (by positivity) (by positivity)
  simp only [specialBoxElement_re, Zsqrtd.re_zero] at hre
  push_cast at hre
  omega

/-- The principal ideal generated by `specialBoxElement` is coprime to the
modulus `(m)`, because the generator is congruent to `1` modulo `m`. -/
theorem specialBoxElement_span_isCoprime
    (p m a b : ℕ) :
    IsCoprime
      (Ideal.span ({specialBoxElement p m a b} :
        Set (Zsqrtd (-(p : ℤ) ^ 3))))
      (Ideal.span ({Zsqrtd.ofInt (m : ℤ)} :
        Set (Zsqrtd (-(p : ℤ) ^ 3)))) := by
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]
  let w : Zsqrtd (-(p : ℤ) ^ 3) := ⟨(a : ℤ), (b : ℤ)⟩
  have hz : specialBoxElement p m a b ∈
      Ideal.span ({specialBoxElement p m a b} :
        Set (Zsqrtd (-(p : ℤ) ^ 3))) :=
    Ideal.mem_span_singleton_self _
  have hmw : -(Zsqrtd.ofInt (m : ℤ) * w) ∈
      Ideal.span ({Zsqrtd.ofInt (m : ℤ)} :
        Set (Zsqrtd (-(p : ℤ) ^ 3))) := by
    apply neg_mem
    exact (Ideal.span ({Zsqrtd.ofInt (m : ℤ)} :
      Set (Zsqrtd (-(p : ℤ) ^ 3)))).mul_mem_right w
        (Ideal.mem_span_singleton_self _)
  have hz' := (show Ideal.span ({specialBoxElement p m a b} :
      Set (Zsqrtd (-(p : ℤ) ^ 3))) ≤
        Ideal.span ({specialBoxElement p m a b} :
          Set (Zsqrtd (-(p : ℤ) ^ 3))) +
        Ideal.span ({Zsqrtd.ofInt (m : ℤ)} :
          Set (Zsqrtd (-(p : ℤ) ^ 3))) from le_sup_left) hz
  have hmw' := (show Ideal.span ({Zsqrtd.ofInt (m : ℤ)} :
      Set (Zsqrtd (-(p : ℤ) ^ 3))) ≤
        Ideal.span ({specialBoxElement p m a b} :
          Set (Zsqrtd (-(p : ℤ) ^ 3))) +
        Ideal.span ({Zsqrtd.ofInt (m : ℤ)} :
          Set (Zsqrtd (-(p : ℤ) ^ 3))) from le_sup_right) hmw
  have hone := add_mem hz' hmw'
  convert hone using 1 <;> ext <;>
    simp [specialBoxElement, w] <;> ring

theorem specialBoxElement_eq_of_associated
    {p m a b c e : ℕ} [Fact p.Prime] (hm : 0 < m)
    (h : Associated (specialBoxElement p m a b)
      (specialBoxElement p m c e)) :
    a = c ∧ b = e := by
  obtain ⟨u, hu⟩ := h
  have hunit : IsUnit (u : Zsqrtd (-(p : ℤ) ^ 3)) := u.isUnit
  have hd : (-(p : ℤ) ^ 3 : ℤ) ≤ -2 := by
    have hp := (Fact.out : Nat.Prime p).two_le
    have hp3 : 2 ≤ p ^ 3 := hp.trans
      (Nat.le_self_pow (by norm_num : 3 ≠ 0) p)
    have hp3Z : (2 : ℤ) ≤ (p : ℤ) ^ 3 := by exact_mod_cast hp3
    omega
  rcases (zsqrtd_isUnit_iff_eq_one_or_neg_one hd (u :
      Zsqrtd (-(p : ℤ) ^ 3))).mp hunit with hu1 | huneg
  · have hzeq : specialBoxElement p m a b =
        specialBoxElement p m c e := by simpa [hu1] using hu
    have hreZ := congrArg Zsqrtd.re hzeq
    have himZ := congrArg Zsqrtd.im hzeq
    change ((1 + m * a : ℕ) : ℤ) = ((1 + m * c : ℕ) : ℤ) at hreZ
    change ((m * b : ℕ) : ℤ) = ((m * e : ℕ) : ℤ) at himZ
    have hreN : 1 + m * a = 1 + m * c := by exact_mod_cast hreZ
    have himN : m * b = m * e := by exact_mod_cast himZ
    exact ⟨Nat.mul_left_cancel hm (Nat.add_left_cancel hreN),
      Nat.mul_left_cancel hm himN⟩
  · have hleft : 0 < (specialBoxElement p m a b).re := by
      change 0 < ((1 + m * a : ℕ) : ℤ)
      positivity
    have hright : 0 < (specialBoxElement p m c e).re := by
      change 0 < ((1 + m * c : ℕ) : ℤ)
      positivity
    have hu' : specialBoxElement p m a b *
        (-1 : Zsqrtd (-(p : ℤ) ^ 3)) =
          specialBoxElement p m c e := by simpa [huneg] using hu
    have hre := congrArg Zsqrtd.re hu'
    have : -(specialBoxElement p m a b).re =
        (specialBoxElement p m c e).re := by simpa using hre
    omega

theorem specialBoxElement_norm_natAbs_le
    {p m a b L : ℕ} (ha : a < L) (hb : b < L) :
    (specialBoxElement p m a b).norm.natAbs ≤
      (1 + p ^ 3) * (m + 1) ^ 2 * L ^ 2 := by
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr (by omega)
  have haL : a ≤ L := ha.le
  have hbL : b ≤ L := hb.le
  let R := (m + 1) * L
  have hre : 1 + m * a ≤ R := by
    calc
      1 + m * a ≤ 1 + m * L :=
        Nat.add_le_add_left (Nat.mul_le_mul_left m haL) 1
      _ ≤ m * L + L := by
        simpa [Nat.add_comm] using Nat.add_le_add_right hL (m * L)
      _ = R := by simp [R, add_mul, add_comm]
  have him : m * b ≤ R := by
    calc
      m * b ≤ m * L := Nat.mul_le_mul_left m hbL
      _ ≤ m * L + L := Nat.le_add_right _ _
      _ = R := by simp [R, add_mul, add_comm]
  have hnorm : (specialBoxElement p m a b).norm.natAbs =
      (1 + m * a) ^ 2 + p ^ 3 * (m * b) ^ 2 := by
    have hnormZ : (specialBoxElement p m a b).norm =
        (((1 + m * a) ^ 2 + p ^ 3 * (m * b) ^ 2 : ℕ) : ℤ) := by
      simp only [Zsqrtd.norm_def, specialBoxElement_re,
        specialBoxElement_im]
      push_cast
      ring
    rw [hnormZ, Int.natAbs_natCast]
  rw [hnorm]
  calc
    (1 + m * a) ^ 2 + p ^ 3 * (m * b) ^ 2 ≤
        R ^ 2 + p ^ 3 * R ^ 2 := by gcongr
    _ = (1 + p ^ 3) * (m + 1) ^ 2 * L ^ 2 := by
      dsimp only [R]
      ring

/-! ## Approximation away from a finite modulus -/

/-- An invertible ideal can be inverted in its class by an integral ideal
coprime to any prescribed nonzero modulus.  The proof trivializes the
invertible module after reduction modulo the modulus; a finite quotient ring
is semilocal, so its Picard group is trivial. -/
theorem exists_coprime_inverse_integralUnitIdeal
    {S : Type*} [CommRing S] [IsDomain S] [Ring.HasFiniteQuotients S]
    (I : IntegralUnitIdeal S) (F : Ideal S) (hFne : F ≠ ⊥) :
    ∃ J : IntegralUnitIdeal S,
      IntegralUnitIdeal.idealClass J =
          (IntegralUnitIdeal.idealClass I)⁻¹ ∧
        IsCoprime (J : Ideal S) F := by
  classical
  by_cases hFtop : F = ⊤
  · obtain ⟨J, hJ⟩ := IntegralUnitIdeal.idealClass_surjective
      (S := S) ((IntegralUnitIdeal.idealClass I)⁻¹)
    refine ⟨J, hJ, ?_⟩
    rw [Ideal.isCoprime_iff_sup_eq, hFtop]
    apply le_antisymm le_top
    exact le_sup_right
  · let A := S ⧸ F
    let M := (I : Ideal S)
    let T := TensorProduct S A M
    let : Nontrivial A :=
      (Ideal.Quotient.nontrivial_iff (R := S) (I := F)).mpr hFtop
    let : Finite A := Ring.HasFiniteQuotients.finiteQuotient hFne
    let : IsArtinianRing A := isArtinian_of_finite
    let : Module.Invertible S M :=
      moduleInvertibleIdealOfIsUnit (I : Ideal S) I.2
    let : Module.Invertible A T := inferInstance
    let : Module.Free A T := inferInstance
    let e : T ≃ₗ[A] A :=
      (Module.Invertible.free_iff_linearEquiv.mp (inferInstance : Module.Free A T)).some
    obtain ⟨x, hx⟩ := TensorProduct.mk_surjective S M A
      Ideal.Quotient.mk_surjective (e.symm 1)
    have hx0 : (x : S) ≠ 0 := by
      intro hxzero
      have hxzero' : x = 0 := by
        apply Subtype.ext
        exact hxzero
      have hezero : e.symm 1 = 0 := by simpa [hxzero'] using hx.symm
      have hone : (1 : A) = 0 := by
        rw [← e.apply_symm_apply 1, hezero, map_zero]
      exact one_ne_zero hone
    have hmod : (I : Ideal S) ≤
        Ideal.span ({(x : S)} : Set S) + F * (I : Ideal S) := by
      intro y hy
      let ys : M := ⟨y, hy⟩
      let a : A := e (TensorProduct.mk S A M 1 ys)
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective a
      let v : M := ys - r • x
      have hvzero : TensorProduct.mk S A M 1 v = 0 := by
        dsimp only [v]
        rw [map_sub, map_smul, hx]
        apply e.injective
        rw [map_sub, map_zero]
        change a - e (r • e.symm 1) = 0
        rw [← IsScalarTower.algebraMap_smul A r (e.symm 1), map_smul,
          e.apply_symm_apply]
        rw [smul_eq_mul, mul_one]
        change a - algebraMap S A r = 0
        rw [← hr]
        simp [A, Ideal.Quotient.algebraMap_eq]
      have hvker : v ∈ LinearMap.ker (TensorProduct.mk S A M 1) := by
        exact LinearMap.mem_ker.mpr hvzero
      rw [LinearMap.ker_tensorProductMk] at hvker
      have hvprod : (v : S) ∈ F * (I : Ideal S) := by
        rw [← Ideal.smul_eq_mul]
        exact Submodule.smul_induction_on hvker
          (fun r hrF w _ ↦ by
            change r * (w : S) ∈ F • (I : Ideal S)
            rw [Ideal.smul_eq_mul]
            exact Ideal.mul_mem_mul hrF w.2)
          (fun _ _ ha hb ↦ add_mem ha hb)
      have hspan : (r : S) * (x : S) ∈
          Ideal.span ({(x : S)} : Set S) := by
          exact (Ideal.span ({(x : S)} : Set S)).mul_mem_left r
            (Ideal.mem_span_singleton_self (x : S))
      have hvval : (v : S) = y - r * (x : S) := rfl
      have hspan' : r * (x : S) ∈
          Ideal.span ({(x : S)} : Set S) + F * (I : Ideal S) :=
        (show Ideal.span ({(x : S)} : Set S) ≤
          Ideal.span ({(x : S)} : Set S) + F * (I : Ideal S) from le_sup_left) hspan
      have hvprod' : (v : S) ∈
          Ideal.span ({(x : S)} : Set S) + F * (I : Ideal S) :=
        (show F * (I : Ideal S) ≤
          Ideal.span ({(x : S)} : Set S) + F * (I : Ideal S) from le_sup_right) hvprod
      have hadd := add_mem hspan' hvprod'
      convert hadd using 1
      rw [hvval]
      abel
    let X : IntegralUnitIdeal S := principalIntegralUnitIdeal
      (Ideal.span ({(x : S)} : Set S)) inferInstance (by
        intro hzero
        have : (x : S) ∈ (⊥ : Ideal S) := by
          rw [← hzero]
          exact Ideal.mem_span_singleton_self (x : S)
        exact hx0 (by simpa using this))
    have hXI : (X : Ideal S) ≤ (I : Ideal S) := by
      dsimp only [X, principalIntegralUnitIdeal]
      exact (Ideal.span_singleton_le_iff_mem _).mpr x.2
    obtain ⟨J, hIJ⟩ := IntegralUnitIdeal.exists_mul_eq_of_le I X hXI
    have hXclass : IntegralUnitIdeal.idealClass X = 1 := by
      apply principalIntegralUnitIdeal_idealClass
    have hclasses := congrArg IntegralUnitIdeal.idealClass hIJ
    rw [IntegralUnitIdeal.idealClass_mul, hXclass] at hclasses
    have hJclass : IntegralUnitIdeal.idealClass J =
        (IntegralUnitIdeal.idealClass I)⁻¹ := by
      calc
        IntegralUnitIdeal.idealClass J =
            1 * IntegralUnitIdeal.idealClass J := by simp
        _ = (IntegralUnitIdeal.idealClass I)⁻¹ *
            (IntegralUnitIdeal.idealClass I *
              IntegralUnitIdeal.idealClass J) := by simp
        _ = (IntegralUnitIdeal.idealClass I)⁻¹ := by rw [hclasses]; simp
    have hspanEq : (I : Ideal S) * (J : Ideal S) =
        Ideal.span ({(x : S)} : Set S) :=
      congrArg (fun K : IntegralUnitIdeal S ↦ (K : Ideal S)) hIJ
    have hmodEq : Ideal.span ({(x : S)} : Set S) +
        F * (I : Ideal S) = (I : Ideal S) := by
      apply le_antisymm
      · apply sup_le
        · exact (Ideal.span_singleton_le_iff_mem _).mpr x.2
        · exact Ideal.mul_le_right
      · exact hmod
    have hfactor : (I : Ideal S) * ((J : Ideal S) + F) =
        (I : Ideal S) * ⊤ := by
      rw [mul_add, hspanEq, mul_comm (I : Ideal S) F,
        hmodEq, Ideal.mul_top]
    have hfrac := congrArg
      (fun K : Ideal S ↦
        (K : FractionalIdeal S⁰ (FractionRing S))) hfactor
    have hfrac' :
        ((I.unit : (FractionalIdeal S⁰ (FractionRing S))ˣ) :
            FractionalIdeal S⁰ (FractionRing S)) *
          (((J : Ideal S) + F : Ideal S) :
            FractionalIdeal S⁰ (FractionRing S)) =
        ((I.unit : (FractionalIdeal S⁰ (FractionRing S))ˣ) :
            FractionalIdeal S⁰ (FractionRing S)) * 1 := by
      simpa only [FractionalIdeal.coeIdeal_mul, IntegralUnitIdeal.unit_coe,
        FractionalIdeal.coeIdeal_top] using hfrac
    have hsupFrac : (((J : Ideal S) + F : Ideal S) :
        FractionalIdeal S⁰ (FractionRing S)) = 1 := by
      calc
        (((J : Ideal S) + F : Ideal S) :
            FractionalIdeal S⁰ (FractionRing S)) =
            (((I.unit)⁻¹ : (FractionalIdeal S⁰ (FractionRing S))ˣ) :
                FractionalIdeal S⁰ (FractionRing S)) *
              (((I.unit : (FractionalIdeal S⁰ (FractionRing S))ˣ) :
                  FractionalIdeal S⁰ (FractionRing S)) *
                (((J : Ideal S) + F : Ideal S) :
                  FractionalIdeal S⁰ (FractionRing S))) := by simp
        _ = (((I.unit)⁻¹ : (FractionalIdeal S⁰ (FractionRing S))ˣ) :
                FractionalIdeal S⁰ (FractionRing S)) *
              (((I.unit : (FractionalIdeal S⁰ (FractionRing S))ˣ) :
                  FractionalIdeal S⁰ (FractionRing S)) * 1) := by rw [hfrac']
        _ = 1 := by simp
    have hsup : (J : Ideal S) + F = ⊤ := by
      apply FractionalIdeal.coeIdeal_injective (K := FractionRing S)
      simpa only [FractionalIdeal.coeIdeal_top] using hsupFrac
    exact ⟨J, hJclass, Ideal.isCoprime_iff_sup_eq.mpr hsup⟩

def SpecialCoprimeClassBall (p N : ℕ) [Fact p.Prime]
    (C : ClassGroup (Zsqrtd (-(p : ℤ) ^ 3)))
    (F : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) :=
  {I : SpecialClassBall p N C // IsCoprime (I.1 :
    Ideal (Zsqrtd (-(p : ℤ) ^ 3))) F}

/-- Every class contains a positive-density two-dimensional box of integral
invertible ideals which avoid a prescribed nonzero rational modulus. -/
theorem exists_specialCoprimeClassBall_lower
    {p : ℕ} [Fact p.Prime]
    (m : ℕ) (hm : 0 < m)
    (C : ClassGroup (Zsqrtd (-(p : ℤ) ^ 3))) :
    ∃ K : ℕ, 0 < K ∧ ∀ L : ℕ, 0 < L →
      L ^ 2 ≤ Nat.card (SpecialCoprimeClassBall p (K * L ^ 2) C
        (Ideal.span ({Zsqrtd.ofInt (m : ℤ)} :
          Set (Zsqrtd (-(p : ℤ) ^ 3))))) := by
  let O := Zsqrtd (-(p : ℤ) ^ 3)
  let : Module.Free ℤ O :=
    Module.Free.of_basis (zsqrtdBasis (-(p : ℤ) ^ 3))
  let : Module.Finite ℤ O :=
    Module.Finite.of_basis (zsqrtdBasis (-(p : ℤ) ^ 3))
  let : Ring.HasFiniteQuotients O := inferInstance
  let F : Ideal O := Ideal.span ({Zsqrtd.ofInt (m : ℤ)} : Set O)
  have hmO : (Zsqrtd.ofInt (m : ℤ) : O) ≠ 0 := by
    intro hz
    have hre := congrArg Zsqrtd.re hz
    simp only [Zsqrtd.re_ofInt, Zsqrtd.re_zero] at hre
    have hm0 : m = 0 := by exact_mod_cast hre
    omega
  have hFne : F ≠ ⊥ := by
    intro hbot
    have hz : (Zsqrtd.ofInt (m : ℤ) : O) ∈ (⊥ : Ideal O) := by
      rw [← hbot]
      exact Ideal.mem_span_singleton_self _
    exact hmO (by simpa using hz)
  obtain ⟨A, hAclass⟩ := IntegralUnitIdeal.idealClass_surjective
    (S := O) (C⁻¹ : ClassGroup O)
  obtain ⟨I, hIclass, hIcop⟩ :=
    exists_coprime_inverse_integralUnitIdeal A F hFne
  have hIclass' : IntegralUnitIdeal.idealClass I = C := by
    simpa [hAclass] using hIclass
  have hIne : (I : Ideal O) ≠ ⊥ := by
    intro hbot
    have hz : (((I : Ideal O) :
        FractionalIdeal O⁰ (FractionRing O))) = 0 := by rw [hbot]; rfl
    exact I.2.ne_zero hz
  let n := (I : Ideal O).cardQuot
  have hn : 0 < n := Ring.HasFiniteQuotients.cardQuot_pos _ hIne
  let K := n * (1 + p ^ 3) * (m + 1) ^ 2
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro L hL
  let z : Fin L × Fin L → O := fun x ↦
    specialBoxElement p m x.1 x.2
  have hz0 (x : Fin L × Fin L) : z x ≠ 0 :=
    specialBoxElement_ne_zero p m x.1 x.2
  let Q : Fin L × Fin L → IntegralUnitIdeal O := fun x ↦
    principalIntegralUnitIdeal
      (Ideal.span ({z x} : Set O)) inferInstance (by
        intro hbot
        have hzmem : z x ∈ (⊥ : Ideal O) := by
          rw [← hbot]
          exact Ideal.mem_span_singleton_self _
        exact hz0 x (by simpa using hzmem))
  have hQclass (x : Fin L × Fin L) :
      IntegralUnitIdeal.idealClass (Q x) = 1 := by
    apply principalIntegralUnitIdeal_idealClass
  have hQIclass (x : Fin L × Fin L) :
      IntegralUnitIdeal.idealClass (Q x * I) = C := by
    rw [IntegralUnitIdeal.idealClass_mul, hQclass, hIclass', one_mul]
  have hQIcard (x : Fin L × Fin L) :
      ((Q x * I : IntegralUnitIdeal O) : Ideal O).cardQuot ≤
        K * L ^ 2 := by
    have hzbound := specialBoxElement_norm_natAbs_le
      (p := p) (m := m) x.1.isLt x.2.isLt
    have hcard : ((Q x * I : IntegralUnitIdeal O) : Ideal O).cardQuot =
        (z x).norm.natAbs * n := by
      change (Ideal.span ({z x} : Set O) * (I : Ideal O)).cardQuot = _
      rw [cardQuot_span_singleton_mul_of_ne_bot
        (zsqrtdBasis (-(p : ℤ) ^ 3)) (I : Ideal O) hIne (hz0 x),
        algebraNorm_zsqrtd]
    rw [hcard]
    calc
      (z x).norm.natAbs * n ≤
          ((1 + p ^ 3) * (m + 1) ^ 2 * L ^ 2) * n :=
        Nat.mul_le_mul_right n hzbound
      _ = K * L ^ 2 := by dsimp only [K]; ring
  have hQIcop (x : Fin L × Fin L) :
      IsCoprime (((Q x * I : IntegralUnitIdeal O) : Ideal O)) F := by
    change IsCoprime (Ideal.span ({z x} : Set O) * (I : Ideal O)) F
    apply (specialBoxElement_span_isCoprime p m x.1 x.2).mul_left hIcop
  let f : Fin L × Fin L →
      SpecialCoprimeClassBall p (K * L ^ 2) C F := fun x ↦
    ⟨⟨Q x * I, hQIclass x, hQIcard x⟩, hQIcop x⟩
  let : Finite (SpecialClassBall p (K * L ^ 2) C) :=
    finiteSpecialClassBall C
  let : Finite (SpecialCoprimeClassBall p (K * L ^ 2) C F) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have hf : Function.Injective f := by
    intro x y hxy
    have hprod : Q x * I = Q y * I :=
      congrArg (fun V : SpecialCoprimeClassBall p (K * L ^ 2) C F ↦
        V.1.1) hxy
    have hQ : Q x = Q y :=
      IntegralUnitIdeal.mul_right_cancel (Q x) (Q y) I hprod
    have hspan : Ideal.span ({z x} : Set O) =
        Ideal.span ({z y} : Set O) := by
      have hcoe := congrArg (fun J : IntegralUnitIdeal O ↦ (J : Ideal O)) hQ
      exact hcoe
    have hassoc : Associated (z x) (z y) :=
      Ideal.span_singleton_eq_span_singleton.mp hspan
    have hcoords := specialBoxElement_eq_of_associated hm hassoc
    apply Prod.ext
    · exact Fin.ext hcoords.1
    · exact Fin.ext hcoords.2
  have hcard := Nat.card_le_card_of_injective f hf
  simpa [Nat.card_prod, pow_two, F] using hcard

@[ext]
structure SpecialSplitPrimeData (p : ℕ) where
  q : ℕ
  prime : q.Prime
  ne_two : q ≠ 2
  ne_p : q ≠ p
  split : ¬ IsQuadraticObstruction (p ^ 3) q

noncomputable def SpecialSplitPrimeData.integralUnitIdeal
    {p : ℕ} [Fact p.Prime] (s : SpecialSplitPrimeData p) (b : Bool) :
    IntegralUnitIdeal (Zsqrtd (-(p : ℤ) ^ 3)) :=
  specialOrientedIntegralUnitIdeal p s.q s.prime s.ne_two s.ne_p s.split b

noncomputable def SpecialSplitPrimeData.idealClass
    {p : ℕ} [Fact p.Prime] (s : SpecialSplitPrimeData p) :
    ClassGroup (Zsqrtd (-(p : ℤ) ^ 3)) :=
  specialSplitPrimeClass p s.q s.prime s.ne_two s.ne_p s.split

/-- A finite covering by explicit split-prime divisors bounds the number of
coprime ideals by the sum of the corresponding divisible-class balls. -/
theorem natCard_specialCoprimeClassBall_le_sum_divisible
    {p N : ℕ} [Fact p.Prime]
    (C : ClassGroup (Zsqrtd (-(p : ℤ) ^ 3)))
    (F : Ideal (Zsqrtd (-(p : ℤ) ^ 3)))
    (T : Finset (SpecialSplitPrimeData p))
    (hcover : ∀ I : SpecialCoprimeClassBall p N C F,
      ∃ s : SpecialSplitPrimeData p, ∃ hs : s ∈ T, ∃ b : Bool,
        ∃ J : IntegralUnitIdeal (Zsqrtd (-(p : ℤ) ^ 3)),
          s.integralUnitIdeal b * J = I.1.1) :
    Nat.card (SpecialCoprimeClassBall p N C F) ≤
      ∑ s ∈ T, ∑ b : Bool,
        Nat.card (SpecialDivisibleClassBall p N C
          (s.integralUnitIdeal b)) := by
  classical
  let O := Zsqrtd (-(p : ℤ) ^ 3)
  choose s hs b J hfactor using hcover
  let Target := Σ t : {s : SpecialSplitPrimeData p // s ∈ T},
    Σ c : Bool, SpecialDivisibleClassBall p N C
      (t.1.integralUnitIdeal c)
  let f : SpecialCoprimeClassBall p N C F → Target := fun I ↦
    ⟨⟨s I, hs I⟩, b I, ⟨I.1, J I, hfactor I⟩⟩
  have hf : Function.Injective f := by
    intro I K hIK
    apply Subtype.ext
    exact congrArg (fun V : Target ↦ V.2.2.1) hIK
  let : Finite (SpecialClassBall p N C) := finiteSpecialClassBall C
  let (t : {s : SpecialSplitPrimeData p // s ∈ T}) (c : Bool) :
      Finite (SpecialDivisibleClassBall p N C
        (t.1.integralUnitIdeal c)) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have hcard := Nat.card_le_card_of_injective f hf
  calc
    Nat.card (SpecialCoprimeClassBall p N C F) ≤ Nat.card Target := hcard
    _ = ∑ t : {s : SpecialSplitPrimeData p // s ∈ T},
        ∑ c : Bool, Nat.card (SpecialDivisibleClassBall p N C
          (t.1.integralUnitIdeal c)) := by
      dsimp only [Target]
      rw [Nat.card_sigma]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Nat.card_sigma]
    _ = ∑ s ∈ T, ∑ c : Bool,
        Nat.card (SpecialDivisibleClassBall p N C
          (s.integralUnitIdeal c)) := by
      simpa only [Finset.attach_eq_univ] using
        T.sum_attach (fun s ↦ ∑ c : Bool,
          Nat.card (SpecialDivisibleClassBall p N C
            (s.integralUnitIdeal c)))

end

end Erdos1081
