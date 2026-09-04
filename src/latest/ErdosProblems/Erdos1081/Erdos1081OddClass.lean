import ErdosProblems.Erdos1081.Erdos1081OrderCounting
import Mathlib.Data.Nat.Factors

namespace Erdos1081

open scoped nonZeroDivisors

noncomputable section

/-! ## Finite-group reduction

For a finite abelian group the subgroup of squares is the whole group as
soon as the only element of order dividing two is the identity.  Keeping
this lemma independent of quadratic orders makes the remaining arithmetic
endpoint completely explicit. -/

theorem classSquareSubgroup_eq_top_of_sq_eq_one
    {G : Type*} [CommGroup G] [Finite G]
    (h : ∀ x : G, x ^ 2 = 1 → x = 1) :
    (classSquareSubgroup : Subgroup G) = ⊤ := by
  apply top_unique
  intro y hy
  let f : G → G := fun x ↦ x ^ 2
  have hf_inj : Function.Injective f := by
    intro x z hxz
    have hs : (x / z) ^ 2 = 1 := by
      dsimp [f] at hxz
      rw [div_pow, hxz]
      simp
    have hxz' := h (x / z) hs
    exact div_eq_one.mp hxz'
  have hf_surj : Function.Surjective f :=
    Finite.injective_iff_surjective.mp hf_inj
  obtain ⟨x, rfl⟩ := hf_surj y
  exact classSquare_mem x

/-! ## Conjugation on the quadratic order and its ideals -/

def zsqrtdConjEquiv (d : ℤ) : Zsqrtd d ≃+* Zsqrtd d where
  toFun := star
  invFun := star
  left_inv := star_star
  right_inv := star_star
  map_add' := map_add (starRingEnd (Zsqrtd d))
  map_mul' := map_mul (starRingEnd (Zsqrtd d))

@[simp] theorem zsqrtdConjEquiv_apply (d : ℤ) (z : Zsqrtd d) :
    zsqrtdConjEquiv d z = star z := rfl

@[simp] theorem zsqrtdConjEquiv_symm (d : ℤ) :
    (zsqrtdConjEquiv d).symm = zsqrtdConjEquiv d := by
  ext z <;> rfl

noncomputable def zsqrtdFractionConj (d : ℤ) [IsDomain (Zsqrtd d)] :
    FractionRing (Zsqrtd d) ≃+* FractionRing (Zsqrtd d) :=
  IsFractionRing.ringEquivOfRingEquiv (zsqrtdConjEquiv d)

noncomputable def fractionalIdealConj (d : ℤ) [IsDomain (Zsqrtd d)] :
    FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d)) ≃+*
      FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d)) :=
  FractionalIdeal.ringEquivOfRingEquiv
    (FractionRing (Zsqrtd d)) (FractionRing (Zsqrtd d))
    (zsqrtdConjEquiv d)

@[simp] theorem zsqrtdFractionConj_algebraMap
    (d : ℤ) [IsDomain (Zsqrtd d)] (z : Zsqrtd d) :
    zsqrtdFractionConj d
        (algebraMap (Zsqrtd d) (FractionRing (Zsqrtd d)) z) =
      algebraMap (Zsqrtd d) (FractionRing (Zsqrtd d)) (star z) := by
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap
    (zsqrtdConjEquiv d) z

@[simp] theorem zsqrtdFractionConj_conj
    (d : ℤ) [IsDomain (Zsqrtd d)]
    (x : FractionRing (Zsqrtd d)) :
    zsqrtdFractionConj d (zsqrtdFractionConj d x) = x := by
  have hsymm : (zsqrtdFractionConj d).symm = zsqrtdFractionConj d := by
    unfold zsqrtdFractionConj
    rw [IsFractionRing.ringEquivOfRingEquiv_symm,
      zsqrtdConjEquiv_symm]
  rw [← hsymm]
  exact (zsqrtdFractionConj d).symm_apply_apply x

@[simp] theorem fractionalIdealConj_conj
    (d : ℤ) [IsDomain (Zsqrtd d)]
    (I : FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d))) :
    fractionalIdealConj d (fractionalIdealConj d I) = I := by
  have hsymm : (fractionalIdealConj d).symm = fractionalIdealConj d := by
    unfold fractionalIdealConj
    rw [FractionalIdeal.ringEquivOfRingEquiv_symm_eq,
      zsqrtdConjEquiv_symm]
  rw [← hsymm]
  exact (fractionalIdealConj d).symm_apply_apply I

@[simp] theorem fractionalIdealConj_spanSingleton
    (d : ℤ) [IsDomain (Zsqrtd d)]
    (x : FractionRing (Zsqrtd d)) :
    fractionalIdealConj d (FractionalIdeal.spanSingleton (Zsqrtd d)⁰ x) =
      FractionalIdeal.spanSingleton (Zsqrtd d)⁰
        (zsqrtdFractionConj d x) := by
  exact FractionalIdeal.ringEquivOfRingEquiv_spanSingleton
    (FractionRing (Zsqrtd d)) (FractionRing (Zsqrtd d))
    (zsqrtdConjEquiv d) x

noncomputable def idealConj (d : ℤ) (I : Ideal (Zsqrtd d)) :
    Ideal (Zsqrtd d) := I.map (starRingEnd (Zsqrtd d))

@[simp] theorem mem_idealConj_iff (d : ℤ) (I : Ideal (Zsqrtd d))
    (z : Zsqrtd d) :
    z ∈ idealConj d I ↔ star z ∈ I := by
  constructor
  · intro hz
    change z ∈ I.map (starRingEnd (Zsqrtd d)) at hz
    have hsurj : Function.Surjective (starRingEnd (Zsqrtd d)) :=
      fun x ↦ ⟨star x, by
        simpa only [starRingEnd_apply] using star_star x⟩
    rw [Ideal.mem_map_iff_of_surjective _ hsurj] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    subst z
    simpa only [starRingEnd_apply, star_star] using hw
  · intro hz
    change z ∈ I.map (starRingEnd (Zsqrtd d))
    have hsurj : Function.Surjective (starRingEnd (Zsqrtd d)) :=
      fun x ↦ ⟨star x, by
        simpa only [starRingEnd_apply] using star_star x⟩
    rw [Ideal.mem_map_iff_of_surjective _ hsurj]
    exact ⟨star z, hz, by
      simpa only [starRingEnd_apply] using star_star z⟩

@[simp] theorem idealConj_conj (d : ℤ) (I : Ideal (Zsqrtd d)) :
    idealConj d (idealConj d I) = I := by
  ext z
  simp [mem_idealConj_iff]

theorem idealConj_mul (d : ℤ) (I J : Ideal (Zsqrtd d)) :
    idealConj d (I * J) = idealConj d I * idealConj d J := by
  exact Ideal.map_mul (starRingEnd (Zsqrtd d)) I J

theorem idealConj_sup (d : ℤ) (I J : Ideal (Zsqrtd d)) :
    idealConj d (I ⊔ J) = idealConj d I ⊔ idealConj d J := by
  exact Ideal.map_sup (starRingEnd (Zsqrtd d)) I J

theorem fractionalIdealConj_coeIdeal (d : ℤ) [IsDomain (Zsqrtd d)]
    (I : Ideal (Zsqrtd d)) :
    fractionalIdealConj d
        ((I : Ideal (Zsqrtd d)) :
          FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d))) =
      ((idealConj d I : Ideal (Zsqrtd d)) :
        FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d))) := by
  ext x
  simp only [fractionalIdealConj, FractionalIdeal.ringEquivOfRingEquiv_apply,
    FractionalIdeal.mem_coeIdeal, FractionalIdeal.coe_mk,
    Submodule.mem_map, mem_idealConj_iff]
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨star z, ?_, ?_⟩
    · simpa using hz
    · exact (IsFractionRing.semilinearEquivOfRingEquiv_algebraMap
        (FractionRing (Zsqrtd d)) (FractionRing (Zsqrtd d))
        (zsqrtdConjEquiv d) z).symm
  · rintro ⟨z, hz, rfl⟩
    refine ⟨algebraMap (Zsqrtd d) (FractionRing (Zsqrtd d)) (star z),
      ⟨star z, hz, rfl⟩, ?_⟩
    calc
      _ = algebraMap (Zsqrtd d) (FractionRing (Zsqrtd d))
          (zsqrtdConjEquiv d (star z)) :=
        IsFractionRing.semilinearEquivOfRingEquiv_algebraMap
          (FractionRing (Zsqrtd d)) (FractionRing (Zsqrtd d))
          (zsqrtdConjEquiv d) (star z)
      _ = _ := by simp

@[simp] theorem idealConj_span_ofInt (d n : ℤ) :
    idealConj d (Ideal.span ({Zsqrtd.ofInt n} : Set (Zsqrtd d))) =
      Ideal.span ({Zsqrtd.ofInt n} : Set (Zsqrtd d)) := by
  ext z
  rw [mem_idealConj_iff]
  constructor
  · intro hz
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hz
    apply Ideal.mem_span_singleton.mpr
    refine ⟨star r, ?_⟩
    apply_fun star
    · simpa [mul_comm] using hr
    · exact star_injective
  · intro hz
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hz
    apply Ideal.mem_span_singleton.mpr
    refine ⟨star r, ?_⟩
    apply_fun star
    · simpa [mul_comm] using hr
    · exact star_injective

theorem span_ofInt_sup_span_ofInt_isPrincipal (d x y : ℤ) :
    (Ideal.span ({Zsqrtd.ofInt x} : Set (Zsqrtd d)) ⊔
      Ideal.span ({Zsqrtd.ofInt y} : Set (Zsqrtd d))).IsPrincipal := by
  let g : ℤ := (x.gcd y : ℕ)
  have heq : Ideal.span ({Zsqrtd.ofInt x} : Set (Zsqrtd d)) ⊔
      Ideal.span ({Zsqrtd.ofInt y} : Set (Zsqrtd d)) =
      Ideal.span ({Zsqrtd.ofInt g} : Set (Zsqrtd d)) := by
    apply le_antisymm
    · apply sup_le
      · apply (Ideal.span_singleton_le_iff_mem _).mpr
        obtain ⟨a, ha⟩ := Int.gcd_dvd_left x y
        apply Ideal.mem_span_singleton.mpr
        refine ⟨Zsqrtd.ofInt a, ?_⟩
        apply Zsqrtd.ext
        · simp only [Zsqrtd.re_ofInt, Zsqrtd.re_mul, Zsqrtd.im_ofInt,
            mul_zero, add_zero]
          change x = g * a
          rw [ha]
        · simp only [Zsqrtd.im_ofInt, Zsqrtd.im_mul, Zsqrtd.re_ofInt,
            mul_zero, zero_mul, add_zero]
      · apply (Ideal.span_singleton_le_iff_mem _).mpr
        obtain ⟨b, hb⟩ := Int.gcd_dvd_right x y
        apply Ideal.mem_span_singleton.mpr
        refine ⟨Zsqrtd.ofInt b, ?_⟩
        apply Zsqrtd.ext
        · simp only [Zsqrtd.re_ofInt, Zsqrtd.re_mul, Zsqrtd.im_ofInt,
            mul_zero, add_zero]
          change y = g * b
          rw [hb]
        · simp only [Zsqrtd.im_ofInt, Zsqrtd.im_mul, Zsqrtd.re_ofInt,
            mul_zero, zero_mul, add_zero]
    · apply (Ideal.span_singleton_le_iff_mem _).mpr
      have hxmem : Zsqrtd.ofInt x ∈
          Ideal.span ({Zsqrtd.ofInt x} : Set (Zsqrtd d)) ⊔
            Ideal.span ({Zsqrtd.ofInt y} : Set (Zsqrtd d)) :=
        le_sup_left (a := Ideal.span ({Zsqrtd.ofInt x} : Set (Zsqrtd d)))
          (b := Ideal.span ({Zsqrtd.ofInt y} : Set (Zsqrtd d)))
          (Ideal.mem_span_singleton_self _)
      have hymem : Zsqrtd.ofInt y ∈
          Ideal.span ({Zsqrtd.ofInt x} : Set (Zsqrtd d)) ⊔
            Ideal.span ({Zsqrtd.ofInt y} : Set (Zsqrtd d)) :=
        le_sup_right (a := Ideal.span ({Zsqrtd.ofInt x} : Set (Zsqrtd d)))
          (b := Ideal.span ({Zsqrtd.ofInt y} : Set (Zsqrtd d)))
          (Ideal.mem_span_singleton_self _)
      have hsum := (Ideal.span ({Zsqrtd.ofInt x} : Set (Zsqrtd d)) ⊔
        Ideal.span ({Zsqrtd.ofInt y} : Set (Zsqrtd d))).add_mem
        ((Ideal.span ({Zsqrtd.ofInt x} : Set (Zsqrtd d)) ⊔
          Ideal.span ({Zsqrtd.ofInt y} : Set (Zsqrtd d))).mul_mem_left
            (Zsqrtd.ofInt (x.gcdA y)) hxmem)
        ((Ideal.span ({Zsqrtd.ofInt x} : Set (Zsqrtd d)) ⊔
          Ideal.span ({Zsqrtd.ofInt y} : Set (Zsqrtd d))).mul_mem_left
            (Zsqrtd.ofInt (x.gcdB y)) hymem)
      have hgEq : (Zsqrtd.ofInt g : Zsqrtd d) =
          Zsqrtd.ofInt (x.gcdA y) * Zsqrtd.ofInt x +
            Zsqrtd.ofInt (x.gcdB y) * Zsqrtd.ofInt y := by
        apply Zsqrtd.ext <;> simp [g, Int.gcd_eq_gcd_ab, mul_comm]
      rw [hgEq]
      exact hsum
  rw [heq]
  exact inferInstance

theorem zsqrtd_norm_nonneg {d : ℤ} (hd : d < 0) (z : Zsqrtd d) :
    0 ≤ z.norm := by
  rw [Zsqrtd.norm_def]
  apply sub_nonneg.mpr
  simpa only [mul_assoc] using
    (mul_nonpos_of_nonpos_of_nonneg hd.le (mul_self_nonneg z.im)).trans
      (mul_self_nonneg z.re)

theorem zsqrtd_norm_pos_of_ne_zero {d : ℤ} (hd : d < 0)
    {z : Zsqrtd d} (hz : z ≠ 0) :
    0 < z.norm := by
  exact lt_of_le_of_ne (zsqrtd_norm_nonneg hd z)
    (Ne.symm ((Zsqrtd.norm_eq_zero_iff hd z).not.mpr hz))

theorem fraction_mul_conj_ne_neg_one
    {d : ℤ} (hd : d < 0) [IsDomain (Zsqrtd d)]
    (x : FractionRing (Zsqrtd d)) :
    x * zsqrtdFractionConj d x ≠ -1 := by
  let O := Zsqrtd d
  let K := FractionRing O
  let s := IsLocalization.sec O⁰ x
  let a : O := s.1
  let b : O := s.2.1
  have hb : b ≠ 0 := by
    exact (mem_nonZeroDivisors_iff_ne_zero.mp s.2.2)
  have hx : x * algebraMap O K b = algebraMap O K a := by
    exact IsLocalization.sec_spec O⁰ x
  have hconjx : zsqrtdFractionConj d x *
      algebraMap O K (star b) = algebraMap O K (star a) := by
    calc
      zsqrtdFractionConj d x * algebraMap O K (star b) =
          zsqrtdFractionConj d x *
            zsqrtdFractionConj d (algebraMap O K b) := by
        rw [zsqrtdFractionConj_algebraMap]
      _ = zsqrtdFractionConj d (x * algebraMap O K b) := by
        rw [map_mul]
      _ = zsqrtdFractionConj d (algebraMap O K a) := by rw [hx]
      _ = algebraMap O K (star a) := by
        rw [zsqrtdFractionConj_algebraMap]
  intro hneg
  have hfield : algebraMap O K (Zsqrtd.ofInt a.norm) =
      algebraMap O K (Zsqrtd.ofInt (-b.norm)) := by
    calc
      algebraMap O K (Zsqrtd.ofInt a.norm) =
          algebraMap O K a * algebraMap O K (star a) := by
        rw [← map_mul, ← Zsqrtd.norm_eq_mul_conj]
        rfl
      _ = (x * algebraMap O K b) *
          (zsqrtdFractionConj d x * algebraMap O K (star b)) := by
        rw [hx, hconjx]
      _ = (x * zsqrtdFractionConj d x) *
          (algebraMap O K b * algebraMap O K (star b)) := by ring
      _ = (-1 : K) * algebraMap O K (Zsqrtd.ofInt b.norm) := by
        rw [hneg, ← map_mul, ← Zsqrtd.norm_eq_mul_conj]
        rfl
      _ = algebraMap O K (Zsqrtd.ofInt (-b.norm)) := by
        rw [neg_one_mul, ← map_neg]
        rfl
  have horder : (Zsqrtd.ofInt a.norm : O) = Zsqrtd.ofInt (-b.norm) :=
    IsFractionRing.injective O K hfield
  have hnormEq : a.norm = -b.norm := by
    exact congrArg Zsqrtd.re horder
  have ha0 := zsqrtd_norm_nonneg hd a
  have hb0 := zsqrtd_norm_pos_of_ne_zero hd hb
  omega

namespace IntegralUnitIdeal

noncomputable def conj
    {p : ℕ} [Fact p.Prime]
    (I : IntegralUnitIdeal (Zsqrtd (-((p : ℤ) ^ 3)))) :
    IntegralUnitIdeal (Zsqrtd (-((p : ℤ) ^ 3))) := by
  let d : ℤ := -((p : ℤ) ^ 3)
  have hmap : IsUnit
      (fractionalIdealConj d
        (((I : IntegralUnitIdeal (Zsqrtd d)) : Ideal (Zsqrtd d)) :
          FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d)))) :=
    I.2.map (fractionalIdealConj d).toMonoidHom
  refine ⟨idealConj d (I : Ideal (Zsqrtd d)), ?_⟩
  rw [← fractionalIdealConj_coeIdeal]
  exact hmap

@[simp] theorem coe_conj
    {p : ℕ} [Fact p.Prime]
    (I : IntegralUnitIdeal (Zsqrtd (-((p : ℤ) ^ 3)))) :
    ((conj I : IntegralUnitIdeal (Zsqrtd (-((p : ℤ) ^ 3)))) :
      Ideal (Zsqrtd (-((p : ℤ) ^ 3)))) =
      idealConj (-((p : ℤ) ^ 3))
        (I : Ideal (Zsqrtd (-((p : ℤ) ^ 3)))) := rfl

end IntegralUnitIdeal

theorem exists_specialFractionCocycle
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3)
    (I : IntegralUnitIdeal (Zsqrtd (-((p : ℤ) ^ 3))))
    (hclass : IntegralUnitIdeal.idealClass I =
      IntegralUnitIdeal.idealClass (IntegralUnitIdeal.conj I)) :
    ∃ alpha : FractionRing (Zsqrtd (-((p : ℤ) ^ 3))),
      alpha ≠ 0 ∧
      ((I : Ideal (Zsqrtd (-((p : ℤ) ^ 3)))) :
          FractionalIdeal (Zsqrtd (-((p : ℤ) ^ 3)))⁰
            (FractionRing (Zsqrtd (-((p : ℤ) ^ 3))))) *
          FractionalIdeal.spanSingleton
            (Zsqrtd (-((p : ℤ) ^ 3)))⁰ alpha =
        (((IntegralUnitIdeal.conj I :
            IntegralUnitIdeal (Zsqrtd (-((p : ℤ) ^ 3)))) :
          Ideal (Zsqrtd (-((p : ℤ) ^ 3)))) :
          FractionalIdeal (Zsqrtd (-((p : ℤ) ^ 3)))⁰
            (FractionRing (Zsqrtd (-((p : ℤ) ^ 3))))) ∧
      alpha * zsqrtdFractionConj (-((p : ℤ) ^ 3)) alpha = 1 := by
  let d : ℤ := -((p : ℤ) ^ 3)
  let O := Zsqrtd d
  let K := FractionRing O
  let IF : FractionalIdeal O⁰ K := (I : Ideal O)
  let IbarF : FractionalIdeal O⁰ K :=
    (IntegralUnitIdeal.conj I : Ideal O)
  unfold IntegralUnitIdeal.idealClass at hclass
  obtain ⟨u, hu⟩ := ClassGroup.mk_eq_mk.mp hclass
  let alpha : K := (u : K)
  have halpha : alpha ≠ 0 := u.ne_zero
  have hfrac : IF * FractionalIdeal.spanSingleton O⁰ alpha = IbarF := by
    have h := congrArg
      (fun U : (FractionalIdeal O⁰ K)ˣ ↦ (U : FractionalIdeal O⁰ K)) hu
    simpa only [Units.val_mul, IntegralUnitIdeal.unit_coe,
      coe_toPrincipalIdeal] using h
  have hbar : IbarF * FractionalIdeal.spanSingleton O⁰
      (zsqrtdFractionConj d alpha) = IF := by
    have h := congrArg (fractionalIdealConj d) hfrac
    have hcIF : fractionalIdealConj d IF = IbarF := by
      dsimp only [IF, IbarF, O, K]
      rw [fractionalIdealConj_coeIdeal]
      rfl
    have hcIbar : fractionalIdealConj d IbarF = IF := by
      dsimp only [IF, IbarF, O, K]
      rw [fractionalIdealConj_coeIdeal]
      change (((idealConj d (idealConj d
        (I : Ideal (Zsqrtd d))) : Ideal (Zsqrtd d)) :
          FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d)))) =
        ((I : Ideal (Zsqrtd d)) :
          FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d)))
      rw [idealConj_conj]
    rw [map_mul, fractionalIdealConj_spanSingleton, hcIF, hcIbar] at h
    exact h
  have hspan : FractionalIdeal.spanSingleton O⁰
      (alpha * zsqrtdFractionConj d alpha) = 1 := by
    have hIF : IF * (FractionalIdeal.spanSingleton O⁰ alpha *
        FractionalIdeal.spanSingleton O⁰
          (zsqrtdFractionConj d alpha)) = IF := by
      calc
        IF * (FractionalIdeal.spanSingleton O⁰ alpha *
            FractionalIdeal.spanSingleton O⁰
              (zsqrtdFractionConj d alpha)) =
            (IF * FractionalIdeal.spanSingleton O⁰ alpha) *
              FractionalIdeal.spanSingleton O⁰
                (zsqrtdFractionConj d alpha) := by ring
        _ = IbarF * FractionalIdeal.spanSingleton O⁰
              (zsqrtdFractionConj d alpha) := by rw [hfrac]
        _ = IF := hbar
    let invIF : FractionalIdeal O⁰ K :=
      (((I.unit)⁻¹ : (FractionalIdeal O⁰ K)ˣ) :
        FractionalIdeal O⁰ K)
    have hinvIF : invIF * IF = 1 := by
      calc
        invIF * IF =
            (((I.unit)⁻¹ : (FractionalIdeal O⁰ K)ˣ) :
              FractionalIdeal O⁰ K) *
              (I.unit : FractionalIdeal O⁰ K) := by
                rw [IntegralUnitIdeal.unit_coe]
        _ = (((I.unit)⁻¹ * I.unit :
              (FractionalIdeal O⁰ K)ˣ) : FractionalIdeal O⁰ K) := by rfl
        _ = 1 := by simp
    have hone : FractionalIdeal.spanSingleton O⁰ alpha *
        FractionalIdeal.spanSingleton O⁰
          (zsqrtdFractionConj d alpha) = 1 := by
      calc
        FractionalIdeal.spanSingleton O⁰ alpha *
              FractionalIdeal.spanSingleton O⁰
                (zsqrtdFractionConj d alpha) =
            1 * (FractionalIdeal.spanSingleton O⁰ alpha *
              FractionalIdeal.spanSingleton O⁰
                (zsqrtdFractionConj d alpha)) := by rw [one_mul]
        _ = (invIF * IF) *
            (FractionalIdeal.spanSingleton O⁰ alpha *
              FractionalIdeal.spanSingleton O⁰
                (zsqrtdFractionConj d alpha)) := by rw [hinvIF]
        _ = invIF * (IF *
            (FractionalIdeal.spanSingleton O⁰ alpha *
              FractionalIdeal.spanSingleton O⁰
                (zsqrtdFractionConj d alpha))) := by ring
        _ = invIF * IF := by rw [hIF]
        _ = 1 := hinvIF
    rw [FractionalIdeal.spanSingleton_mul_spanSingleton] at hone
    exact hone
  obtain ⟨z, hz⟩ :=
    FractionalIdeal.spanSingleton_eq_spanSingleton.mp
      (hspan.trans FractionalIdeal.spanSingleton_one.symm)
  have hp3 : 3 ≤ p := by
    have hp2 : p ≠ 2 := by omega
    exact (Fact.out : p.Prime).two_le.lt_iff_ne.mpr hp2.symm
  have hdle : d ≤ -2 := by
    dsimp only [d]
    have hpZ : (3 : ℤ) ≤ p := by exact_mod_cast hp3
    nlinarith [sq_nonneg ((p : ℤ) ^ 1)]
  have hzpm : (z : O) = 1 ∨ (z : O) = -1 :=
    (zsqrtd_isUnit_iff_eq_one_or_neg_one hdle (z : O)).mp z.isUnit
  have hnorm : alpha * zsqrtdFractionConj d alpha = 1 := by
    rcases hzpm with hz1 | hzn1
    · rw [Units.smul_def, Algebra.smul_def, hz1, map_one, one_mul] at hz
      exact hz
    · rw [Units.smul_def, Algebra.smul_def, hzn1, map_neg, map_one, neg_mul,
        one_mul] at hz
      have hneg : alpha * zsqrtdFractionConj d alpha = -1 := by
        simpa using congrArg Neg.neg hz
      exact (fraction_mul_conj_ne_neg_one
        (d := d) (specialDiscriminant_neg p Fact.out) alpha hneg).elim
  exact ⟨alpha, halpha, hfrac, hnorm⟩

theorem exists_specialHilbert90Beta
    {p : ℕ} [Fact p.Prime]
    {alpha : FractionRing (Zsqrtd (-((p : ℤ) ^ 3)))}
    (halpha : alpha ≠ 0)
    (hnorm : alpha * zsqrtdFractionConj (-((p : ℤ) ^ 3)) alpha = 1) :
    ∃ beta : FractionRing (Zsqrtd (-((p : ℤ) ^ 3))),
      beta ≠ 0 ∧
        alpha * zsqrtdFractionConj (-((p : ℤ) ^ 3)) beta = beta := by
  let d : ℤ := -((p : ℤ) ^ 3)
  let O := Zsqrtd d
  let K := FractionRing O
  by_cases hneg : alpha = -1
  · let beta : K := algebraMap O K (Zsqrtd.sqrtd : O)
    have hsqrt : (Zsqrtd.sqrtd : O) ≠ 0 := by
      intro h
      have him := congrArg Zsqrtd.im h
      norm_num at him
    have hbeta : beta ≠ 0 :=
      by simpa only [beta, map_zero] using
        (IsFractionRing.injective O K).ne hsqrt
    refine ⟨beta, hbeta, ?_⟩
    have hconjbeta : zsqrtdFractionConj d beta = -beta := by
      dsimp only [beta]
      rw [zsqrtdFractionConj_algebraMap]
      have hs : star (Zsqrtd.sqrtd : O) = -Zsqrtd.sqrtd := by
        apply Zsqrtd.ext <;> simp
      rw [hs, map_neg]
    rw [hneg, hconjbeta]
    ring
  · let beta : K := 1 + alpha
    have hbeta : beta ≠ 0 := by
      intro hb
      dsimp only [beta] at hb
      apply hneg
      rw [eq_neg_iff_add_eq_zero]
      simpa [add_comm] using hb
    refine ⟨beta, hbeta, ?_⟩
    dsimp only [beta]
    rw [map_add, map_one]
    calc
      alpha * (1 + zsqrtdFractionConj d alpha) =
          alpha + alpha * zsqrtdFractionConj d alpha := by ring
      _ = 1 + alpha := by rw [hnorm]; ring

def zsqrtdImLinear (d : ℤ) : Zsqrtd d →ₗ[ℤ] ℤ where
  toFun := Zsqrtd.im
  map_add' := Zsqrtd.im_add
  map_smul' n z := by simp [Algebra.smul_def]

@[simp] theorem zsqrtdImLinear_apply (d : ℤ) (z : Zsqrtd d) :
    zsqrtdImLinear d z = z.im := rfl

structure SpecialIdealHermiteData (p : ℕ)
    (I : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) where
  a : ℕ
  c : ℕ
  b : ℤ
  w : Zsqrtd (-(p : ℤ) ^ 3)
  a_pos : 0 < a
  c_pos : 0 < c
  int_mem_iff : ∀ n : ℤ,
    Zsqrtd.ofInt n ∈ I ↔ (a : ℤ) ∣ n
  w_mem : w ∈ I
  w_re : w.re = b
  w_im : w.im = c
  im_dvd : ∀ z ∈ I, (c : ℤ) ∣ z.im
  decompose : ∀ z ∈ I, ∃ x y : ℤ,
    z = Zsqrtd.ofInt (x * a) + Zsqrtd.ofInt y * w

theorem exists_specialIdealHermiteData
    {p : ℕ} [Fact p.Prime]
    (I : Ideal (Zsqrtd (-(p : ℤ) ^ 3))) (hI : I ≠ ⊥) :
    Nonempty (SpecialIdealHermiteData p I) := by
  let O := Zsqrtd (-(p : ℤ) ^ 3)
  let RI : Submodule ℤ O := I.restrictScalars ℤ
  let M : Submodule ℤ ℤ := RI.map (zsqrtdImLinear (-(p : ℤ) ^ 3))
  let ag : ℤ := Submodule.IsPrincipal.generator (I.under ℤ)
  let cg : ℤ := Submodule.IsPrincipal.generator M
  let a : ℕ := ag.natAbs
  let c : ℕ := cg.natAbs
  have hUnder : I.under ℤ ≠ ⊥ := by
    obtain ⟨z, hzI, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    have hdneg : (-(p : ℤ) ^ 3 : ℤ) < 0 := by
      have hp : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
      exact neg_neg_of_pos (pow_pos hp 3)
    have hns : ∀ n : ℤ, (-(p : ℤ) ^ 3 : ℤ) ≠ n * n := by
      intro n
      exact ne_of_lt (hdneg.trans_le (mul_self_nonneg n))
    have hnorm0 : z.norm ≠ 0 := by
      exact (Zsqrtd.norm_eq_zero hns z).not.mpr hz0
    have hnormI : Zsqrtd.ofInt z.norm ∈ I := by
      rw [Zsqrtd.ofInt_eq_intCast, Zsqrtd.norm_eq_mul_conj]
      exact I.mul_mem_right _ hzI
    intro hbot
    have : z.norm ∈ (⊥ : Ideal ℤ) := by
      rw [← hbot]
      exact hnormI
    exact hnorm0 (by simpa using this)
  have hag : ag ≠ 0 := by
    intro hz
    apply hUnder
    exact (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero _).mpr hz
  have ha : 0 < a := Int.natAbs_pos.mpr hag
  have ha_assoc : Associated ag (a : ℤ) := Int.associated_natAbs ag
  have hint (n : ℤ) : Zsqrtd.ofInt n ∈ I ↔ (a : ℤ) ∣ n := by
    change n ∈ I.under ℤ ↔ _
    rw [Submodule.IsPrincipal.mem_iff_generator_dvd]
    exact ha_assoc.dvd_iff_dvd_left
  have hc_mem : (c : ℤ) ∈ M := by
    have hgen : cg ∈ M := Submodule.IsPrincipal.generator_mem M
    change ((cg.natAbs : ℕ) : ℤ) ∈ M
    rw [Int.natCast_natAbs]
    rcases abs_choice cg with h | h
    · simpa [h] using hgen
    · simpa [h] using M.neg_mem hgen
  obtain ⟨w, hw, hwim⟩ := Submodule.mem_map.mp hc_mem
  have hwI : w ∈ I := hw
  have hwim' : w.im = (c : ℤ) := by
    simpa [M, RI] using hwim
  have him_dvd (z : O) (hz : z ∈ I) : (c : ℤ) ∣ z.im := by
    have hzM : z.im ∈ M := by
      exact Submodule.mem_map_of_mem (p := RI) (f := zsqrtdImLinear (-(p : ℤ) ^ 3)) hz
    have hcg : cg ∣ z.im :=
      (Submodule.IsPrincipal.mem_iff_generator_dvd M).mp hzM
    exact (Int.associated_natAbs cg).dvd_iff_dvd_left.mp hcg
  have hcg : cg ≠ 0 := by
    intro hzero
    have hc0 : c = 0 := by simp [c, hzero]
    have himzero : ∀ z ∈ I, z.im = 0 := by
      intro z hz
      obtain ⟨k, hk⟩ := him_dvd z hz
      simpa [hc0] using hk
    have haI : Zsqrtd.ofInt (a : ℤ) ∈ I := (hint _).mpr (dvd_refl _)
    have hmul : Zsqrtd.sqrtd * Zsqrtd.ofInt (a : ℤ) ∈ I :=
      I.mul_mem_left _ haI
    have hz := himzero _ hmul
    simpa [Zsqrtd.sqrtd, ha.ne'] using hz
  have hc : 0 < c := Int.natAbs_pos.mpr hcg
  have hdecomp (z : Zsqrtd (-(p : ℤ) ^ 3)) (hz : z ∈ I) : ∃ x y : ℤ,
      z = Zsqrtd.ofInt (x * a) + Zsqrtd.ofInt y * w := by
    obtain ⟨y, hy⟩ := him_dvd z hz
    have hdiff : z - Zsqrtd.ofInt y * w ∈ I :=
      I.sub_mem hz (I.mul_mem_left _ hwI)
    have hdiffim : (z - Zsqrtd.ofInt y * w :
        Zsqrtd (-(p : ℤ) ^ 3)).im = 0 := by
      simp only [Zsqrtd.im_sub, Zsqrtd.im_mul, Zsqrtd.re_ofInt,
        Zsqrtd.im_ofInt, zero_mul, add_zero, hwim']
      rw [hy]
      ring
    have hdiffEq : z - Zsqrtd.ofInt y * w =
        Zsqrtd.ofInt (z.re - y * w.re) := by
      rw [Zsqrtd.ext_iff]
      constructor
      · simp
      · exact hdiffim
    have hmemInt : Zsqrtd.ofInt (z.re - y * w.re) ∈ I := hdiffEq ▸ hdiff
    obtain ⟨x, hx⟩ := (hint _).mp hmemInt
    refine ⟨x, y, ?_⟩
    rw [← sub_eq_iff_eq_add, hdiffEq, hx]
    congr 1
    exact mul_comm (a : ℤ) x
  refine ⟨⟨a, c, w.re, w, ha, hc, hint, hwI, rfl, hwim',
    him_dvd, hdecomp⟩⟩

def SpecialIdealHermiteData.hermiteIdeal
    {p : ℕ} {I : Ideal (Zsqrtd (-(p : ℤ) ^ 3))}
    (h : SpecialIdealHermiteData p I) :
    Ideal (Zsqrtd (-(p : ℤ) ^ 3)) :=
  Ideal.span ({Zsqrtd.ofInt (h.a : ℤ), h.w} :
    Set (Zsqrtd (-(p : ℤ) ^ 3)))

theorem SpecialIdealHermiteData.hermiteIdeal_eq
    {p : ℕ} {I : Ideal (Zsqrtd (-(p : ℤ) ^ 3))}
    (h : SpecialIdealHermiteData p I) : h.hermiteIdeal = I := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    rcases hz with (rfl | rfl)
    · exact (h.int_mem_iff _).mpr (dvd_refl _)
    · exact h.w_mem
  · intro z hz
    obtain ⟨x, y, hxy⟩ := h.decompose z hz
    rw [hxy]
    apply Ideal.add_mem
    · rw [show Zsqrtd.ofInt (x * h.a) =
          Zsqrtd.ofInt x * Zsqrtd.ofInt (h.a : ℤ) by
        ext <;> simp]
      exact h.hermiteIdeal.mul_mem_left _
        (Ideal.subset_span (Set.mem_insert _ _))
    · exact h.hermiteIdeal.mul_mem_left _
        (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem SpecialIdealHermiteData.c_dvd_a
    {p : ℕ} [Fact p.Prime]
    {I : Ideal (Zsqrtd (-(p : ℤ) ^ 3))}
    (h : SpecialIdealHermiteData p I) : (h.c : ℤ) ∣ (h.a : ℤ) := by
  have hmem : Zsqrtd.sqrtd * Zsqrtd.ofInt (h.a : ℤ) ∈ I :=
    I.mul_mem_left _ ((h.int_mem_iff _).mpr (dvd_refl _))
  have hdvd := h.im_dvd _ hmem
  simpa [Zsqrtd.sqrtd] using hdvd

theorem SpecialIdealHermiteData.c_dvd_b
    {p : ℕ} [Fact p.Prime]
    {I : Ideal (Zsqrtd (-(p : ℤ) ^ 3))}
    (h : SpecialIdealHermiteData p I) : (h.c : ℤ) ∣ h.b := by
  have hmem : Zsqrtd.sqrtd * Zsqrtd.ofInt (h.a : ℤ) ∈ I :=
    I.mul_mem_left _ ((h.int_mem_iff _).mpr (dvd_refl _))
  obtain ⟨x, y, hxy⟩ := h.decompose _ hmem
  have him := congrArg Zsqrtd.im hxy
  have hre := congrArg Zsqrtd.re hxy
  simp only [Zsqrtd.im_mul, Zsqrtd.re_sqrtd, Zsqrtd.im_ofInt,
    Zsqrtd.im_sqrtd, Zsqrtd.re_ofInt, zero_mul, one_mul, add_zero,
    Zsqrtd.im_add, Zsqrtd.re_add, Zsqrtd.re_mul] at him hre
  rw [h.w_im] at him
  rw [h.w_re] at hre
  simp only [zero_add, zero_mul, mul_zero, add_zero] at him hre
  have hy0 : y ≠ 0 := by
    intro hy
    rw [hy, zero_mul] at him
    exact h.a_pos.ne' (by exact_mod_cast him)
  have hprod : y * (x * (h.c : ℤ) + h.b) = 0 := by
    calc
      y * (x * (h.c : ℤ) + h.b) =
          x * ((h.c : ℤ) * y) + y * h.b := by ring
      _ = x * (h.a : ℤ) + y * h.b := by
        rw [mul_comm (h.c : ℤ) y, ← him]
      _ = 0 := hre.symm
  have hzero : x * (h.c : ℤ) + h.b = 0 :=
    (mul_eq_zero.mp hprod).resolve_left hy0
  refine ⟨-x, ?_⟩
  linarith

/-! ## Removing the content of a Hermite basis

The integer `c` is the common content of the two displayed basis vectors.
After dividing it out we obtain the customary ideal `(A, B + √(-p³))`.
The next lemmas perform this normalization inside the ideal monoid, so that
invertibility passes to the normalized ideal without any appeal to ideal
factorization. -/

def specialHermiteVector (p : ℕ) (B : ℤ) :
    Zsqrtd (-((p : ℤ) ^ 3)) := ⟨B, 1⟩

@[simp] theorem specialHermiteVector_re (p : ℕ) (B : ℤ) :
    (specialHermiteVector p B).re = B := rfl

@[simp] theorem specialHermiteVector_im (p : ℕ) (B : ℤ) :
    (specialHermiteVector p B).im = 1 := rfl

def normalizedHermiteIdeal (p A : ℕ) (B : ℤ) :
    Ideal (Zsqrtd (-((p : ℤ) ^ 3))) :=
  Ideal.span ({Zsqrtd.ofInt (A : ℤ), specialHermiteVector p B} :
    Set (Zsqrtd (-((p : ℤ) ^ 3))))

theorem SpecialIdealHermiteData.exists_normalization
    {p : ℕ} [Fact p.Prime]
    {I : Ideal (Zsqrtd (-((p : ℤ) ^ 3)))}
    (h : SpecialIdealHermiteData p I) :
    ∃ A : ℕ, ∃ B : ℤ,
      0 < A ∧
      h.a = h.c * A ∧
      h.b = (h.c : ℤ) * B ∧
      h.w = Zsqrtd.ofInt (h.c : ℤ) * specialHermiteVector p B ∧
      I = Ideal.span ({Zsqrtd.ofInt (h.c : ℤ)} :
          Set (Zsqrtd (-((p : ℤ) ^ 3)))) *
        normalizedHermiteIdeal p A B := by
  have hcaZ := h.c_dvd_a
  have hca : h.c ∣ h.a := by exact_mod_cast hcaZ
  obtain ⟨A, hA⟩ := hca
  obtain ⟨B, hB⟩ := h.c_dvd_b
  have hApos : 0 < A := by
    have ha := h.a_pos
    rw [hA] at ha
    exact Nat.pos_of_mul_pos_left ha
  have hw : h.w = Zsqrtd.ofInt (h.c : ℤ) * specialHermiteVector p B := by
    apply Zsqrtd.ext
    · simp [h.w_re, hB]
    · simp [h.w_im]
  refine ⟨A, B, hApos, hA, hB, hw, ?_⟩
  calc
    I = h.hermiteIdeal := h.hermiteIdeal_eq.symm
    _ = Ideal.span ({Zsqrtd.ofInt (h.c : ℤ)} :
          Set (Zsqrtd (-((p : ℤ) ^ 3)))) *
        normalizedHermiteIdeal p A B := by
      unfold SpecialIdealHermiteData.hermiteIdeal normalizedHermiteIdeal
      rw [Ideal.span_insert, Ideal.span_insert, Ideal.mul_sup,
        Ideal.span_singleton_mul_span_singleton,
        Ideal.span_singleton_mul_span_singleton]
      rw [← Ideal.span_insert]
      have haO : (Zsqrtd.ofInt (h.a : ℤ) :
          Zsqrtd (-((p : ℤ) ^ 3))) =
          Zsqrtd.ofInt (h.c : ℤ) * Zsqrtd.ofInt (A : ℤ) := by
        ext <;> simp [hA]
      rw [haO, hw]
      exact Ideal.span_insert _ _

theorem SpecialIdealHermiteData.normalized_norm_dvd
    {p : ℕ} [Fact p.Prime]
    {I : Ideal (Zsqrtd (-((p : ℤ) ^ 3)))}
    (h : SpecialIdealHermiteData p I)
    {A : ℕ} {B : ℤ}
    (hA : h.a = h.c * A)
    (hB : h.b = (h.c : ℤ) * B)
    (hw : h.w = Zsqrtd.ofInt (h.c : ℤ) * specialHermiteVector p B) :
    (A : ℤ) ∣ B ^ 2 + (p : ℤ) ^ 3 := by
  have hmem : Zsqrtd.sqrtd * h.w ∈ I := I.mul_mem_left _ h.w_mem
  obtain ⟨x, y, hxy⟩ := h.decompose _ hmem
  have hre := congrArg Zsqrtd.re hxy
  have him := congrArg Zsqrtd.im hxy
  simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_sqrtd,
    Zsqrtd.im_sqrtd, zero_mul, one_mul, Zsqrtd.re_add, Zsqrtd.im_add,
    Zsqrtd.re_ofInt, Zsqrtd.im_ofInt, mul_zero, add_zero] at hre him
  rw [h.w_im] at hre
  rw [h.w_re, hB] at hre him
  rw [h.w_im] at him
  rw [hA] at hre
  have hwre : h.w.re = (h.c : ℤ) * B := by rw [h.w_re, hB]
  have hwim : h.w.im = (h.c : ℤ) := h.w_im
  have hsre : (specialHermiteVector p B).re = B := rfl
  have hsim : (specialHermiteVector p B).im = 1 := rfl
  have hrew := congrArg Zsqrtd.re hw
  have himw := congrArg Zsqrtd.im hw
  simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_ofInt,
    Zsqrtd.im_ofInt, zero_mul, add_zero, hsre, hsim, mul_one] at hrew himw
  rw [hwre] at hrew
  rw [hwim] at himw
  have hc0 : (h.c : ℤ) ≠ 0 := by exact_mod_cast h.c_pos.ne'
  have hy : y = B := by
    apply mul_left_cancel₀ hc0
    nlinarith
  refine ⟨-x, ?_⟩
  rw [hy] at hre
  have hpform : (-(p : ℤ) ^ 3 : ℤ) * (h.c : ℤ) =
      x * ((h.c : ℤ) * A) + B * ((h.c : ℤ) * B) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hre
  apply mul_left_cancel₀ hc0
  nlinarith [hpform]

theorem SpecialIdealHermiteData.normalized_two_mul_dvd_of_conj
    {p : ℕ} [Fact p.Prime]
    {I : Ideal (Zsqrtd (-((p : ℤ) ^ 3)))}
    (h : SpecialIdealHermiteData p I)
    (hconj : idealConj (-((p : ℤ) ^ 3)) I = I)
    {A : ℕ} {B : ℤ}
    (hA : h.a = h.c * A)
    (hB : h.b = (h.c : ℤ) * B) :
    (A : ℤ) ∣ 2 * B := by
  have hstar : star h.w ∈ I := by
    have hs : star h.w ∈ idealConj (-((p : ℤ) ^ 3)) I := by
      rw [mem_idealConj_iff]
      simpa using h.w_mem
    exact (le_of_eq hconj) hs
  obtain ⟨x, y, hxy⟩ := h.decompose _ hstar
  have hre := congrArg Zsqrtd.re hxy
  have him := congrArg Zsqrtd.im hxy
  simp only [Zsqrtd.re_star, Zsqrtd.im_star,
    Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_ofInt, Zsqrtd.im_ofInt,
    Zsqrtd.re_mul, Zsqrtd.im_mul, mul_zero, zero_mul, add_zero] at hre him
  rw [h.w_re, hB] at hre
  rw [h.w_im] at him
  rw [hA] at hre
  have hc0 : (h.c : ℤ) ≠ 0 := by exact_mod_cast h.c_pos.ne'
  have hy : y = -1 := by
    apply mul_right_cancel₀ hc0
    nlinarith
  refine ⟨x, ?_⟩
  rw [hy] at hre
  simp only [Nat.cast_mul] at hre
  have heq : (h.c : ℤ) * (2 * B) =
      (h.c : ℤ) * ((A : ℤ) * x) := by
    linear_combination hre
  exact mul_left_cancel₀ hc0 heq

theorem normalizedHermiteIdeal_isUnit
    {p A : ℕ} {B : ℤ}
    {I : Ideal (Zsqrtd (-((p : ℤ) ^ 3)))}
    {c : ℕ}
    (hfactor : I = Ideal.span ({Zsqrtd.ofInt (c : ℤ)} :
        Set (Zsqrtd (-((p : ℤ) ^ 3)))) *
      normalizedHermiteIdeal p A B)
    (hI : IsUnit ((I : Ideal (Zsqrtd (-((p : ℤ) ^ 3)))) :
      FractionalIdeal (Zsqrtd (-((p : ℤ) ^ 3)))⁰
        (FractionRing (Zsqrtd (-((p : ℤ) ^ 3)))))) :
    IsUnit (((normalizedHermiteIdeal p A B :
        Ideal (Zsqrtd (-((p : ℤ) ^ 3)))) :
      FractionalIdeal (Zsqrtd (-((p : ℤ) ^ 3)))⁰
        (FractionRing (Zsqrtd (-((p : ℤ) ^ 3)))))) := by
  have hprod : IsUnit
      ((((Ideal.span ({Zsqrtd.ofInt (c : ℤ)} :
          Set (Zsqrtd (-((p : ℤ) ^ 3)))) :
            Ideal (Zsqrtd (-((p : ℤ) ^ 3)))) :
          FractionalIdeal (Zsqrtd (-((p : ℤ) ^ 3)))⁰
            (FractionRing (Zsqrtd (-((p : ℤ) ^ 3)))))) *
        ((normalizedHermiteIdeal p A B :
          Ideal (Zsqrtd (-((p : ℤ) ^ 3)))) :
          FractionalIdeal (Zsqrtd (-((p : ℤ) ^ 3)))⁰
            (FractionRing (Zsqrtd (-((p : ℤ) ^ 3)))))) := by
    rw [← FractionalIdeal.coeIdeal_mul, ← hfactor]
    exact hI
  exact (IsUnit.mul_iff.mp hprod).2

/-- A fractional multiplier stabilizing an invertible integral ideal is
already integral.  This is the cancellation argument that replaces the
usual local-Dedekind-domain criterion for a proper ideal. -/
theorem mem_one_of_spanSingleton_mul_le_self
    {S : Type*} [CommRing S] [IsDomain S]
    {I : FractionalIdeal S⁰ (FractionRing S)}
    (hI : IsUnit I) {x : FractionRing S}
    (hx : FractionalIdeal.spanSingleton S⁰ x * I ≤ I) :
    x ∈ (1 : FractionalIdeal S⁰ (FractionRing S)) := by
  have hcancel : I * I⁻¹ = 1 :=
    (FractionalIdeal.mul_inv_cancel_iff_isUnit
      (K := FractionRing S)).mpr hI
  have hle : FractionalIdeal.spanSingleton S⁰ x ≤
      (1 : FractionalIdeal S⁰ (FractionRing S)) := by
    calc
      FractionalIdeal.spanSingleton S⁰ x =
          FractionalIdeal.spanSingleton S⁰ x * (I * I⁻¹) := by
            rw [hcancel, mul_one]
      _ = (FractionalIdeal.spanSingleton S⁰ x * I) * I⁻¹ := by
            rw [mul_assoc]
      _ ≤ I * I⁻¹ := by gcongr
      _ = 1 := hcancel
  exact (FractionalIdeal.spanSingleton_le_iff_mem.mp hle)

theorem normalizedHermiteIdeal_primitive
    {p A : ℕ} [Fact p.Prime] {B k : ℤ}
    (hApos : 0 < A)
    (hnorm : B ^ 2 + (p : ℤ) ^ 3 = (A : ℤ) * k)
    (hunit : IsUnit (((normalizedHermiteIdeal p A B :
        Ideal (Zsqrtd (-((p : ℤ) ^ 3)))) :
      FractionalIdeal (Zsqrtd (-((p : ℤ) ^ 3)))⁰
        (FractionRing (Zsqrtd (-((p : ℤ) ^ 3))))))) :
    ∀ ell : ℕ, ell.Prime → ell ∣ A →
      (ell : ℤ) ∣ 2 * B → (ell : ℤ) ∣ k → False := by
  intro ell hell hellA hellB hellk
  let O := Zsqrtd (-((p : ℤ) ^ 3))
  let K := FractionRing O
  let v : O := specialHermiteVector p B
  let e : O := Zsqrtd.ofInt (ell : ℤ)
  let g : K := algebraMap O K v / algebraMap O K e
  obtain ⟨A₀, hA₀⟩ := hellA
  obtain ⟨t, ht⟩ := hellB
  obtain ⟨k₀, hk₀⟩ := hellk
  have he0 : e ≠ 0 := by
    intro he
    have hre := congrArg Zsqrtd.re he
    simp [e, hell.ne_zero] at hre
  have hme0 : algebraMap O K e ≠ 0 :=
    by simpa using (FaithfulSMul.algebraMap_injective O K).ne he0
  have hv_sq : v ^ 2 =
      Zsqrtd.ofInt (2 * B) * v -
        Zsqrtd.ofInt (B ^ 2 + (p : ℤ) ^ 3) := by
    dsimp only [v]
    rw [pow_two]
    change (⟨B, 1⟩ : Zsqrtd (-((p : ℤ) ^ 3))) * ⟨B, 1⟩ =
      (⟨2 * B, 0⟩ : Zsqrtd (-((p : ℤ) ^ 3))) * ⟨B, 1⟩ -
        ⟨B ^ 2 + (p : ℤ) ^ 3, 0⟩
    rw [Zsqrtd.ext_iff]
    constructor
    · simp
      ring
    · simp
      ring
  have hgA : g * algebraMap O K (Zsqrtd.ofInt (A : ℤ)) =
      algebraMap O K (Zsqrtd.ofInt (A₀ : ℤ) * v) := by
    dsimp only [g]
    rw [div_mul_eq_mul_div, div_eq_iff hme0]
    rw [← map_mul, ← map_mul]
    apply congrArg (algebraMap O K)
    apply Zsqrtd.ext <;> simp [e, hA₀, mul_comm, mul_left_comm, mul_assoc]
  have hgv : g * algebraMap O K v =
      algebraMap O K (Zsqrtd.ofInt t * v -
        Zsqrtd.ofInt ((A : ℤ) * k₀)) := by
    dsimp only [g]
    rw [div_mul_eq_mul_div, div_eq_iff hme0]
    rw [← map_mul, ← map_mul]
    apply congrArg (algebraMap O K)
    rw [← pow_two, hv_sq]
    rw [ht, hnorm, hk₀]
    dsimp only [e]
    simp only [Zsqrtd.ofInt_eq_intCast, Int.cast_mul]
    ring
  let J : Ideal O := normalizedHermiteIdeal p A B
  let JF : FractionalIdeal O⁰ K := (J : Ideal O)
  have hgA_mem : g * algebraMap O K (Zsqrtd.ofInt (A : ℤ)) ∈ JF := by
    rw [hgA]
    apply FractionalIdeal.mem_coeIdeal_of_mem
    exact J.mul_mem_left _
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hgv_mem : g * algebraMap O K v ∈ JF := by
    rw [hgv]
    apply FractionalIdeal.mem_coeIdeal_of_mem
    apply J.sub_mem
    · exact J.mul_mem_left _
        (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    · rw [show Zsqrtd.ofInt ((A : ℤ) * k₀) =
          Zsqrtd.ofInt k₀ * Zsqrtd.ofInt (A : ℤ) by
          ext <;> simp [mul_comm]]
      exact J.mul_mem_left _
        (Ideal.subset_span (Set.mem_insert _ _))
  have hstab : FractionalIdeal.spanSingleton O⁰ g * JF ≤ JF := by
    rw [FractionalIdeal.spanSingleton_mul_le_iff]
    intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := (FractionalIdeal.mem_coeIdeal O⁰).mp hz
    obtain ⟨r, s, hrs⟩ := Ideal.mem_span_pair.mp hz₀
    change g * algebraMap O K z₀ ∈ JF
    rw [← hrs, map_add, map_mul, map_mul, mul_add]
    have hrmem : algebraMap O K r *
        (g * algebraMap O K (Zsqrtd.ofInt (A : ℤ))) ∈ JF := by
      rw [← Algebra.smul_def]
      exact JF.1.smul_mem r hgA_mem
    have hsmem : algebraMap O K s * (g * algebraMap O K v) ∈ JF := by
      rw [← Algebra.smul_def]
      exact JF.1.smul_mem s hgv_mem
    have heq :
        g * (algebraMap O K r * algebraMap O K (Zsqrtd.ofInt (A : ℤ))) +
            g * (algebraMap O K s * algebraMap O K v) =
          algebraMap O K r *
              (g * algebraMap O K (Zsqrtd.ofInt (A : ℤ))) +
            algebraMap O K s * (g * algebraMap O K v) := by ring
    rw [heq]
    exact JF.1.add_mem hrmem hsmem
  have hgint : g ∈ (1 : FractionalIdeal O⁰ K) :=
    mem_one_of_spanSingleton_mul_le_self hunit hstab
  obtain ⟨z, hz⟩ := (FractionalIdeal.mem_one_iff O⁰).mp hgint
  have hmapped : algebraMap O K (e * z) = algebraMap O K v := by
    rw [map_mul, hz]
    dsimp only [g]
    exact mul_div_cancel₀ _ hme0
  have heq : e * z = v := (FaithfulSMul.algebraMap_injective O K) hmapped
  have him := congrArg Zsqrtd.im heq
  have helltwo : 2 ≤ ell := hell.two_le
  have him' : (ell : ℤ) * z.im = 1 := by
    dsimp only [e, v] at him
    rw [Zsqrtd.im_mul] at him
    simpa [specialHermiteVector] using him
  have hdvdZ : (ell : ℤ) ∣ (1 : ℤ) := ⟨z.im, him'.symm⟩
  have hdvdN : ell ∣ 1 := Int.natCast_dvd_natCast.mp hdvdZ
  have hell1 := Nat.dvd_one.mp hdvdN
  omega

theorem normalizedHermite_leading_eq_one_or_prime_cube
    {p A : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3)
    {B k : ℤ} (hApos : 0 < A)
    (hnorm : B ^ 2 + (p : ℤ) ^ 3 = (A : ℤ) * k)
    (htwo : (A : ℤ) ∣ 2 * B)
    (hprimitive : ∀ ell : ℕ, ell.Prime → ell ∣ A →
      (ell : ℤ) ∣ 2 * B → (ell : ℤ) ∣ k → False) :
    A = 1 ∨ A = p ^ 3 := by
  have hpne2 : p ≠ 2 := by intro h; subst p; norm_num at hp4
  have htwoA : ¬ 2 ∣ A := by
    intro h2A
    have h2A' := h2A
    obtain ⟨A₀, hA₀⟩ := h2A
    have hBodd : Odd B := by
      rw [← Int.not_even_iff_odd]
      intro hBeven
      have hB2 : (2 : ℤ) ∣ B := even_iff_two_dvd.mp hBeven
      have hBsq : (2 : ℤ) ∣ B ^ 2 := dvd_pow hB2 (by omega)
      have hAk : (2 : ℤ) ∣ (A : ℤ) * k := by
        apply dvd_mul_of_dvd_left
        exact Int.natCast_dvd_natCast.mpr h2A'
      have hp3 : (2 : ℤ) ∣ (p : ℤ) ^ 3 := by
        have heq : (p : ℤ) ^ 3 = (A : ℤ) * k - B ^ 2 := by
          linarith [hnorm]
        rw [heq]
        exact Int.dvd_sub hAk hBsq
      have hp3N : 2 ∣ p ^ 3 := by
        have := Int.natCast_dvd.mp hp3
        simpa [Int.natAbs_pow] using this
      have hp2 : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow hp3N
      rcases (Nat.dvd_prime Fact.out).mp hp2 with h | h
      · omega
      · exact hpne2 h.symm
    have hBodd' := hBodd
    obtain ⟨b, hb⟩ := hBodd
    have hpform : ∃ r : ℤ, (p : ℤ) = 4 * r + 3 := by
      refine ⟨(p / 4 : ℕ), ?_⟩
      have hm := Nat.mod_add_div p 4
      rw [hp4] at hm
      have hz : (p : ℤ) = 3 + 4 * (p / 4 : ℕ) := by exact_mod_cast hm.symm
      linarith
    obtain ⟨r, hr⟩ := hpform
    have hfourNorm : (4 : ℤ) ∣ B ^ 2 + (p : ℤ) ^ 3 := by
      refine ⟨b ^ 2 + b + 16 * r ^ 3 + 36 * r ^ 2 + 27 * r + 7, ?_⟩
      rw [hb, hr]
      ring
    have hnot4A : ¬ 4 ∣ A := by
      intro h4A
      have h4AZ : (4 : ℤ) ∣ (A : ℤ) :=
        Int.natCast_dvd_natCast.mpr h4A
      have h4B : (4 : ℤ) ∣ 2 * B := h4AZ.trans htwo
      obtain ⟨u, hu⟩ := h4B
      have hB2 : (2 : ℤ) ∣ B := ⟨u, by linarith⟩
      exact (Int.not_even_iff_odd.mpr hBodd') (even_iff_two_dvd.mpr hB2)
    have hnot2A₀ : ¬ 2 ∣ A₀ := by
      intro h
      obtain ⟨u, hu⟩ := h
      apply hnot4A
      refine ⟨u, ?_⟩
      omega
    have htwoAk : (2 : ℤ) ∣ (A₀ : ℤ) * k := by
      obtain ⟨u, hu⟩ := hfourNorm
      refine ⟨u, ?_⟩
      rw [hnorm, hA₀] at hu
      push_cast at hu
      linarith
    have htwoK : (2 : ℤ) ∣ k := by
      rcases Int.prime_two.dvd_mul.mp htwoAk with h | h
      · exact False.elim (hnot2A₀ (Int.natCast_dvd_natCast.mp h))
      · exact h
    exact hprimitive 2 Nat.prime_two h2A'
      (by exact dvd_mul_right 2 B) htwoK
  have hAprimePow : A = p ^ A.primeFactorsList.length := by
    apply Nat.eq_prime_pow_of_unique_prime_dvd hApos.ne'
    intro q hq hqA
    have hqne2 : q ≠ 2 := by
      intro h
      subst q
      exact htwoA hqA
    have hqAZ : (q : ℤ) ∣ (A : ℤ) :=
      Int.natCast_dvd_natCast.mpr hqA
    have hq2B : (q : ℤ) ∣ 2 * B := hqAZ.trans htwo
    have hqprimeZ : Prime (q : ℤ) := by
      rw [Int.prime_iff_natAbs_prime]
      simpa using hq
    have hqB : (q : ℤ) ∣ B := by
      rcases hqprimeZ.dvd_mul.mp hq2B with hq2 | hqB
      · have hq2N : q ∣ 2 := Int.natCast_dvd_natCast.mp hq2
        rcases (Nat.dvd_prime Nat.prime_two).mp hq2N with h | h
        · exact False.elim (hq.ne_one h)
        · exact False.elim (hqne2 h)
      · exact hqB
    have hqBsq : (q : ℤ) ∣ B ^ 2 := dvd_pow hqB (by omega)
    have hqAk : (q : ℤ) ∣ (A : ℤ) * k :=
      dvd_mul_of_dvd_left hqAZ k
    have hqp3 : (q : ℤ) ∣ (p : ℤ) ^ 3 := by
      have heq : (p : ℤ) ^ 3 = (A : ℤ) * k - B ^ 2 := by
        linarith [hnorm]
      rw [heq]
      exact Int.dvd_sub hqAk hqBsq
    have hqp3N : q ∣ p ^ 3 := Int.natCast_dvd_natCast.mp (by
      simpa only [Int.natCast_pow] using hqp3)
    have hqp : q ∣ p := hq.dvd_of_dvd_pow hqp3N
    rcases (Nat.dvd_prime Fact.out).mp hqp with h | h
    · exact False.elim (hq.ne_one h)
    · exact h
  let e := A.primeFactorsList.length
  have hAe : A = p ^ e := by simpa [e] using hAprimePow
  by_cases he0 : e = 0
  · left
    rw [hAprimePow]
    simp [e, he0]
  right
  have hpeB : (p ^ e : ℤ) ∣ B := by
    have hpe2B : p ^ e ∣ (2 * B).natAbs := by
      apply Int.natCast_dvd.mp
      rw [← hAe]
      exact htwo
    have hpe2B' : p ^ e ∣ 2 * B.natAbs := by
      simpa [Int.natAbs_mul] using hpe2B
    have hpcop : (p ^ e).Coprime 2 := by
      apply Nat.Coprime.pow_left
      exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr (by
        intro hp2
        rcases (Nat.dvd_prime Nat.prime_two).mp hp2 with h | h
        · exact (Fact.out : p.Prime).ne_one h
        · exact hpne2 h)
    exact Int.natCast_dvd.mpr (hpcop.dvd_of_dvd_mul_left hpe2B')
  have hpeP3 : p ^ e ∣ p ^ 3 := by
    apply Int.natCast_dvd_natCast.mp
    have hpeBsq : (p ^ e : ℤ) ∣ B ^ 2 := dvd_pow hpeB (by omega)
    have hpeNorm : (p ^ e : ℤ) ∣ B ^ 2 + (p : ℤ) ^ 3 := by
      rw [hnorm, hAe]
      exact dvd_mul_right _ _
    have hp3Z : (p ^ e : ℤ) ∣ (p : ℤ) ^ 3 :=
      by simpa using Int.dvd_sub hpeNorm hpeBsq
    simpa only [Int.natCast_pow] using hp3Z
  obtain ⟨j, hjle, hjeq⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hpeP3
  have he_le : e ≤ 3 := by
    have := Nat.pow_right_injective (Fact.out : p.Prime).two_le hjeq
    omega
  interval_cases e
  · contradiction
  · exfalso
    obtain ⟨C, hC⟩ := hpeB
    have hpk : (p : ℤ) ∣ k := by
      refine ⟨C ^ 2 + (p : ℤ), ?_⟩
      have heq := hnorm
      rw [hAe] at heq
      rw [show B = (p : ℤ) * C by simpa using hC] at heq
      push_cast at heq
      have hp0 : (p : ℤ) ≠ 0 := by
        exact_mod_cast (Fact.out : p.Prime).ne_zero
      apply mul_left_cancel₀ hp0
      calc
        (p : ℤ) * k = ((p : ℤ) * C) ^ 2 + (p : ℤ) ^ 3 := by
          simpa using heq.symm
        _ = (p : ℤ) * ((p : ℤ) * (C ^ 2 + (p : ℤ))) := by ring
    have hpB : (p : ℤ) ∣ B := ⟨C, by simpa using hC⟩
    exact hprimitive p (Fact.out : p.Prime) (by
      rw [hAe]
      exact dvd_pow_self p (by omega))
      (dvd_mul_of_dvd_right hpB 2) hpk
  · exfalso
    obtain ⟨C, hC⟩ := hpeB
    have hpk : (p : ℤ) ∣ k := by
      refine ⟨(p : ℤ) * C ^ 2 + 1, ?_⟩
      have heq := hnorm
      rw [hAe] at heq
      rw [show B = ((p : ℤ) ^ 2) * C by simpa using hC] at heq
      push_cast at heq
      have hp0 : (p : ℤ) ≠ 0 := by
        exact_mod_cast (Fact.out : p.Prime).ne_zero
      apply mul_left_cancel₀ (pow_ne_zero 2 hp0)
      calc
        (p : ℤ) ^ 2 * k =
            ((p : ℤ) ^ 2 * C) ^ 2 + (p : ℤ) ^ 3 := by
          simpa using heq.symm
        _ = (p : ℤ) ^ 2 *
            ((p : ℤ) * ((p : ℤ) * C ^ 2 + 1)) := by ring
    have hpB : (p : ℤ) ∣ B := by
      refine ⟨(p : ℤ) * C, ?_⟩
      simpa [pow_two, mul_assoc] using hC
    exact hprimitive p (Fact.out : p.Prime) (by
      rw [hAe]
      exact dvd_pow_self p (by omega))
      (dvd_mul_of_dvd_right hpB 2) hpk
  · exact hAe

theorem normalizedHermiteIdeal_isPrincipal_of_leading
    {p A : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3)
    {B : ℤ} (htwo : (A : ℤ) ∣ 2 * B)
    (hA : A = 1 ∨ A = p ^ 3) :
    (normalizedHermiteIdeal p A B).IsPrincipal := by
  rcases hA with rfl | rfl
  · have htop : normalizedHermiteIdeal p 1 B = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      have hgen : Zsqrtd.ofInt (1 : ℤ) ∈
          normalizedHermiteIdeal p 1 B :=
        Ideal.subset_span (Set.mem_insert _ _)
      simpa using hgen
    rw [htop]
    exact inferInstance
  · have hpne2 : p ≠ 2 := by intro h; subst p; norm_num at hp4
    have hpB : (p ^ 3 : ℤ) ∣ B := by
      have hp2B : p ^ 3 ∣ (2 * B).natAbs := by
        apply Int.natCast_dvd.mp
        simpa only [Int.natCast_pow] using htwo
      have hp2B' : p ^ 3 ∣ 2 * B.natAbs := by
        simpa [Int.natAbs_mul] using hp2B
      have hcop : (p ^ 3).Coprime 2 := by
        apply Nat.Coprime.pow_left
        exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr (by
          intro hp2
          rcases (Nat.dvd_prime Nat.prime_two).mp hp2 with h | h
          · exact (Fact.out : p.Prime).ne_one h
          · exact hpne2 h)
      exact Int.natCast_dvd.mpr (hcop.dvd_of_dvd_mul_left hp2B')
    obtain ⟨C, hC⟩ := hpB
    have heq : normalizedHermiteIdeal p (p ^ 3) B =
        Ideal.span ({Zsqrtd.sqrtd} :
          Set (Zsqrtd (-((p : ℤ) ^ 3)))) := by
      apply le_antisymm
      · apply Ideal.span_le.mpr
        intro z hz
        rcases hz with rfl | rfl
        · apply Ideal.mem_span_singleton.mpr
          refine ⟨-Zsqrtd.sqrtd, ?_⟩
          apply Zsqrtd.ext <;> simp <;> ring
        · apply Ideal.mem_span_singleton.mpr
          refine ⟨Zsqrtd.ofInt (-C) * Zsqrtd.sqrtd + 1, ?_⟩
          rw [hC]
          apply Zsqrtd.ext <;> simp [specialHermiteVector] <;> ring
      · apply Ideal.span_le.mpr
        intro z hz
        have hz' : z = Zsqrtd.sqrtd := by simpa using hz
        subst z
        have hv : specialHermiteVector p B ∈
            normalizedHermiteIdeal p (p ^ 3) B :=
          Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
        have hBmem : Zsqrtd.ofInt B ∈
            normalizedHermiteIdeal p (p ^ 3) B := by
          have heq : (Zsqrtd.ofInt B : Zsqrtd (-((p : ℤ) ^ 3))) =
              Zsqrtd.ofInt C * Zsqrtd.ofInt ((p ^ 3 : ℕ) : ℤ) := by
            ext <;> simp [hC, mul_comm]
          rw [heq]
          exact (normalizedHermiteIdeal p (p ^ 3) B).mul_mem_left _
            (Ideal.subset_span (Set.mem_insert _ _))
        have := (normalizedHermiteIdeal p (p ^ 3) B).sub_mem hv hBmem
        have heqv : specialHermiteVector p B - Zsqrtd.ofInt B =
            (Zsqrtd.sqrtd : Zsqrtd (-((p : ℤ) ^ 3))) := by
          apply Zsqrtd.ext <;> simp [specialHermiteVector]
        rw [heqv] at this
        exact this
    rw [heq]
    exact inferInstance

theorem idealConj_normalizedHermiteIdeal (p A : ℕ) (B : ℤ) :
    idealConj (-((p : ℤ) ^ 3)) (normalizedHermiteIdeal p A B) =
      Ideal.span ({Zsqrtd.ofInt (A : ℤ), star (specialHermiteVector p B)} :
        Set (Zsqrtd (-((p : ℤ) ^ 3)))) := by
  ext z
  rw [mem_idealConj_iff]
  constructor
  · intro hz
    obtain ⟨r, s, hrs⟩ := Ideal.mem_span_pair.mp hz
    apply Ideal.mem_span_pair.mpr
    refine ⟨star r, star s, ?_⟩
    apply_fun star
    · simpa [mul_add, star_add, star_mul, mul_comm] using hrs
    · exact star_injective
  · intro hz
    obtain ⟨r, s, hrs⟩ := Ideal.mem_span_pair.mp hz
    apply Ideal.mem_span_pair.mpr
    refine ⟨star r, star s, ?_⟩
    apply_fun star
    · simpa [mul_add, star_add, star_mul, mul_comm] using hrs
    · exact star_injective

def normalizedHermiteContentIdeal (p A : ℕ) (B k : ℤ) :
    Ideal (Zsqrtd (-((p : ℤ) ^ 3))) :=
  Ideal.span ({Zsqrtd.ofInt (A : ℤ), specialHermiteVector p B,
      star (specialHermiteVector p B), Zsqrtd.ofInt k} :
    Set (Zsqrtd (-((p : ℤ) ^ 3))))

theorem normalizedHermiteContentIdeal_eq_top
    {p A : ℕ} [Fact p.Prime] {B k : ℤ}
    (hprimitive : ∀ ell : ℕ, ell.Prime → ell ∣ A →
      (ell : ℤ) ∣ 2 * B → (ell : ℤ) ∣ k → False) :
    normalizedHermiteContentIdeal p A B k = ⊤ := by
  by_contra hH
  obtain ⟨P, hPmax, hHP⟩ := Ideal.exists_le_maximal
    (normalizedHermiteContentIdeal p A B k) hH
  obtain ⟨q, hq, hunder⟩ := exists_natPrime_under_specialMaximal P hPmax
  have hAin : Zsqrtd.ofInt (A : ℤ) ∈
      normalizedHermiteContentIdeal p A B k :=
    Ideal.subset_span (by simp)
  have hkin : Zsqrtd.ofInt k ∈
      normalizedHermiteContentIdeal p A B k :=
    Ideal.subset_span (by simp)
  have hvin : specialHermiteVector p B ∈
      normalizedHermiteContentIdeal p A B k :=
    Ideal.subset_span (by simp)
  have hsvin : star (specialHermiteVector p B) ∈
      normalizedHermiteContentIdeal p A B k :=
    Ideal.subset_span (by simp)
  have htwoEq : (Zsqrtd.ofInt (2 * B) :
      Zsqrtd (-((p : ℤ) ^ 3))) =
      specialHermiteVector p B + star (specialHermiteVector p B) := by
    apply Zsqrtd.ext <;> simp [specialHermiteVector] <;> ring
  have htwoin : Zsqrtd.ofInt (2 * B) ∈
      normalizedHermiteContentIdeal p A B k := by
    rw [htwoEq]
    exact (normalizedHermiteContentIdeal p A B k).add_mem hvin hsvin
  have hqA_Z : (q : ℤ) ∣ (A : ℤ) := by
    have : (A : ℤ) ∈ P.under ℤ := hHP hAin
    rw [hunder, Ideal.mem_span_singleton] at this
    exact this
  have hqA : q ∣ A := Int.natCast_dvd_natCast.mp hqA_Z
  have hqTwo : (q : ℤ) ∣ 2 * B := by
    have : 2 * B ∈ P.under ℤ := hHP htwoin
    rw [hunder, Ideal.mem_span_singleton] at this
    exact this
  have hqk : (q : ℤ) ∣ k := by
    have : k ∈ P.under ℤ := hHP hkin
    rw [hunder, Ideal.mem_span_singleton] at this
    exact this
  exact hprimitive q hq hqA hqTwo hqk

theorem normalizedHermiteIdeal_mul_conj
    {p A : ℕ} [Fact p.Prime] {B k : ℤ}
    (hnorm : B ^ 2 + (p : ℤ) ^ 3 = (A : ℤ) * k)
    (hprimitive : ∀ ell : ℕ, ell.Prime → ell ∣ A →
      (ell : ℤ) ∣ 2 * B → (ell : ℤ) ∣ k → False) :
    normalizedHermiteIdeal p A B *
        idealConj (-((p : ℤ) ^ 3)) (normalizedHermiteIdeal p A B) =
      Ideal.span ({Zsqrtd.ofInt (A : ℤ)} :
        Set (Zsqrtd (-((p : ℤ) ^ 3)))) := by
  let O := Zsqrtd (-((p : ℤ) ^ 3))
  let a : O := Zsqrtd.ofInt (A : ℤ)
  let v : O := specialHermiteVector p B
  let J : Ideal O := normalizedHermiteIdeal p A B
  let Jbar : Ideal O := idealConj (-((p : ℤ) ^ 3)) J
  let P : Ideal O := J * Jbar
  change P = Ideal.span ({a} : Set O)
  have hbar : Jbar = Ideal.span ({a, star v} : Set O) := by
    simpa only [Jbar, J, a, v] using idealConj_normalizedHermiteIdeal p A B
  have hva : v * star v = Zsqrtd.ofInt ((A : ℤ) * k) := by
    dsimp only [v]
    change (⟨B, 1⟩ : Zsqrtd (-((p : ℤ) ^ 3))) * star ⟨B, 1⟩ =
      ⟨(A : ℤ) * k, 0⟩
    rw [Zsqrtd.ext_iff]
    constructor
    · change B * B + (-((p : ℤ) ^ 3)) * 1 * (-1) = (A : ℤ) * k
      nlinarith [hnorm]
    · change B * (-1) + 1 * B = 0
      ring
  have hPle : P ≤ Ideal.span ({a} : Set O) := by
    dsimp only [P, J]
    rw [hbar]
    unfold normalizedHermiteIdeal
    rw [Ideal.span_pair_mul_span_pair]
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Ideal.mem_span_singleton.mpr ⟨a, by ring⟩
    · exact Ideal.mem_span_singleton.mpr ⟨star v, by ring⟩
    · exact Ideal.mem_span_singleton.mpr ⟨v, by ring⟩
    · rw [hva]
      exact Ideal.mem_span_singleton.mpr
        ⟨Zsqrtd.ofInt k, by ext <;> simp [a, mul_comm]⟩
  have hHtop := normalizedHermiteContentIdeal_eq_top
    (p := p) (A := A) (B := B) (k := k) hprimitive
  let Q : Ideal O := (P : Submodule O O).colon ({a} : Set O)
  have hHle : normalizedHermiteContentIdeal p A B k ≤ Q := by
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    change z ∈ (P : Submodule O O).colon ({a} : Set O)
    rw [Submodule.mem_colon_singleton, Algebra.smul_def]
    have haJ : a ∈ J := by
      exact Ideal.subset_span (Set.mem_insert _ _)
    have hvJ : v ∈ J := by
      exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have haBar : a ∈ Jbar := by
      rw [hbar]
      exact Ideal.subset_span (Set.mem_insert _ _)
    have hsvBar : star v ∈ Jbar := by
      rw [hbar]
      exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    rcases hz with rfl | rfl | rfl | rfl
    · exact Ideal.mul_mem_mul haJ haBar
    · exact Ideal.mul_mem_mul hvJ haBar
    · simpa [O, v, a, mul_comm] using (Ideal.mul_mem_mul haJ hsvBar)
    · have hmem := Ideal.mul_mem_mul hvJ hsvBar
      rw [hva] at hmem
      simpa [O, a, mul_comm] using hmem
  have hQtop : Q = ⊤ := by
    apply top_unique
    rw [← hHtop]
    exact hHle
  have haP : a ∈ P := by
    have hOne : (1 : O) ∈ Q := by rw [hQtop]; exact Submodule.mem_top
    change (1 : O) ∈ (P : Submodule O O).colon ({a} : Set O) at hOne
    rw [Submodule.mem_colon_singleton, Algebra.smul_def] at hOne
    simpa using hOne
  apply le_antisymm hPle
  exact (Ideal.span_singleton_le_iff_mem P).mpr haP

theorem invertible_specialIdeal_mul_conj_isPrincipal
    {p : ℕ} [Fact p.Prime]
    (I : Ideal (Zsqrtd (-((p : ℤ) ^ 3))))
    (hunit : IsUnit ((I : Ideal (Zsqrtd (-((p : ℤ) ^ 3)))) :
      FractionalIdeal (Zsqrtd (-((p : ℤ) ^ 3)))⁰
        (FractionRing (Zsqrtd (-((p : ℤ) ^ 3)))))) :
    (I * idealConj (-((p : ℤ) ^ 3)) I).IsPrincipal := by
  have hI0 : I ≠ ⊥ := FractionalIdeal.coeIdeal_ne_zero.mp hunit.ne_zero
  obtain ⟨h⟩ := exists_specialIdealHermiteData I hI0
  obtain ⟨A, B, hApos, hA, hB, hw, hfactor⟩ := h.exists_normalization
  have hJunit := normalizedHermiteIdeal_isUnit hfactor hunit
  obtain ⟨k, hnorm⟩ := h.normalized_norm_dvd hA hB hw
  have hprimitive : ∀ ell : ℕ, ell.Prime → ell ∣ A →
      (ell : ℤ) ∣ 2 * B → (ell : ℤ) ∣ k → False :=
    normalizedHermiteIdeal_primitive hApos hnorm hJunit
  have hJnorm := normalizedHermiteIdeal_mul_conj
    (p := p) (A := A) (B := B) (k := k) hnorm hprimitive
  rw [hfactor, idealConj_mul, idealConj_span_ofInt]
  rw [show
      (Ideal.span ({Zsqrtd.ofInt (h.c : ℤ)} :
          Set (Zsqrtd (-((p : ℤ) ^ 3)))) * normalizedHermiteIdeal p A B) *
        (Ideal.span ({Zsqrtd.ofInt (h.c : ℤ)} :
          Set (Zsqrtd (-((p : ℤ) ^ 3)))) *
            idealConj (-((p : ℤ) ^ 3)) (normalizedHermiteIdeal p A B)) =
        (Ideal.span ({Zsqrtd.ofInt (h.c : ℤ)} :
          Set (Zsqrtd (-((p : ℤ) ^ 3)))) *
          Ideal.span ({Zsqrtd.ofInt (h.c : ℤ)} :
            Set (Zsqrtd (-((p : ℤ) ^ 3))))) *
        (normalizedHermiteIdeal p A B *
          idealConj (-((p : ℤ) ^ 3)) (normalizedHermiteIdeal p A B)) by
      ac_rfl, hJnorm]
  exact Ideal.mem_isPrincipalSubmonoid_iff.mp
    ((Ideal.isPrincipalSubmonoid (Zsqrtd (-((p : ℤ) ^ 3)))).mul_mem
      ((Ideal.isPrincipalSubmonoid (Zsqrtd (-((p : ℤ) ^ 3)))).mul_mem
        (Ideal.span_singleton_mem_isPrincipalSubmonoid _)
        (Ideal.span_singleton_mem_isPrincipalSubmonoid _))
      (Ideal.span_singleton_mem_isPrincipalSubmonoid _))

namespace IntegralUnitIdeal

theorem idealClass_conj
    {p : ℕ} [Fact p.Prime]
    (I : IntegralUnitIdeal (Zsqrtd (-((p : ℤ) ^ 3)))) :
    idealClass (conj I) = (idealClass I)⁻¹ := by
  have hprincipal := invertible_specialIdeal_mul_conj_isPrincipal
    (p := p) (I : Ideal (Zsqrtd (-((p : ℤ) ^ 3)))) I.2
  have hproduct : idealClass (I * conj I) = 1 := by
    unfold idealClass
    apply ClassGroup.mk_eq_one_iff.mpr
    rw [unit_coe]
    change ((((I : Ideal (Zsqrtd (-((p : ℤ) ^ 3)))) *
        idealConj (-((p : ℤ) ^ 3))
          (I : Ideal (Zsqrtd (-((p : ℤ) ^ 3)))) :
          Ideal (Zsqrtd (-((p : ℤ) ^ 3)))) :
        FractionalIdeal (Zsqrtd (-((p : ℤ) ^ 3)))⁰
          (FractionRing (Zsqrtd (-((p : ℤ) ^ 3))))) :
        Submodule (Zsqrtd (-((p : ℤ) ^ 3)))
          (FractionRing (Zsqrtd (-((p : ℤ) ^ 3))))).IsPrincipal
    exact (IsFractionRing.coeSubmodule_isPrincipal
      (Zsqrtd (-((p : ℤ) ^ 3)))
      (FractionRing (Zsqrtd (-((p : ℤ) ^ 3))))).mpr hprincipal
  rw [idealClass_mul] at hproduct
  exact eq_inv_of_mul_eq_one_right hproduct

end IntegralUnitIdeal

theorem invariant_invertible_specialIdeal_isPrincipal
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3)
    (I : Ideal (Zsqrtd (-((p : ℤ) ^ 3))))
    (hunit : IsUnit ((I : Ideal (Zsqrtd (-((p : ℤ) ^ 3)))) :
      FractionalIdeal (Zsqrtd (-((p : ℤ) ^ 3)))⁰
        (FractionRing (Zsqrtd (-((p : ℤ) ^ 3))))))
    (hconj : idealConj (-((p : ℤ) ^ 3)) I = I) :
    I.IsPrincipal := by
  have hI0 : I ≠ ⊥ := by
    exact FractionalIdeal.coeIdeal_ne_zero.mp hunit.ne_zero
  obtain ⟨h⟩ := exists_specialIdealHermiteData I hI0
  obtain ⟨A, B, hApos, hA, hB, hw, hfactor⟩ := h.exists_normalization
  have hJunit := normalizedHermiteIdeal_isUnit hfactor hunit
  have hnormDvd := h.normalized_norm_dvd hA hB hw
  obtain ⟨k, hnorm⟩ := hnormDvd
  have htwo := h.normalized_two_mul_dvd_of_conj hconj hA hB
  have hprimitive : ∀ ell : ℕ, ell.Prime → ell ∣ A →
      (ell : ℤ) ∣ 2 * B → (ell : ℤ) ∣ k → False :=
    normalizedHermiteIdeal_primitive hApos hnorm hJunit
  have hleading : A = 1 ∨ A = p ^ 3 :=
    normalizedHermite_leading_eq_one_or_prime_cube hp4 hApos hnorm
      htwo hprimitive
  have hJprincipal : (normalizedHermiteIdeal p A B).IsPrincipal :=
    normalizedHermiteIdeal_isPrincipal_of_leading hp4 htwo hleading
  rw [hfactor]
  exact (Ideal.mem_isPrincipalSubmonoid_iff.mp <|
    (Ideal.isPrincipalSubmonoid (Zsqrtd (-((p : ℤ) ^ 3)))).mul_mem
      (Ideal.span_singleton_mem_isPrincipalSubmonoid _)
      (Ideal.mem_isPrincipalSubmonoid_iff.mpr hJprincipal))

theorem special_class_eq_one_of_sq_eq_one
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3)
    (C : ClassGroup (Zsqrtd (-((p : ℤ) ^ 3))))
    (hC : C ^ 2 = 1) : C = 1 := by
  let d : ℤ := -((p : ℤ) ^ 3)
  let O := Zsqrtd d
  let K := FractionRing O
  obtain ⟨I, hIclass⟩ :=
    IntegralUnitIdeal.idealClass_surjective (S := O) C
  have hCC : C * C = 1 := by simpa [pow_two] using hC
  have hCinv : C = C⁻¹ := eq_inv_of_mul_eq_one_right hCC
  have hclassConj : IntegralUnitIdeal.idealClass I =
      IntegralUnitIdeal.idealClass (IntegralUnitIdeal.conj I) := by
    calc
      IntegralUnitIdeal.idealClass I = C := hIclass
      _ = C⁻¹ := hCinv
      _ = (IntegralUnitIdeal.idealClass I)⁻¹ := by rw [hIclass]
      _ = IntegralUnitIdeal.idealClass (IntegralUnitIdeal.conj I) :=
        (IntegralUnitIdeal.idealClass_conj I).symm
  obtain ⟨alpha, halpha, hfrac, hnorm⟩ :=
    exists_specialFractionCocycle hp4 I hclassConj
  obtain ⟨beta, hbeta, hhilbert⟩ :=
    exists_specialHilbert90Beta halpha hnorm
  let IF : FractionalIdeal O⁰ K := (I : Ideal O)
  let JF : FractionalIdeal O⁰ K :=
    FractionalIdeal.spanSingleton O⁰ beta * IF
  have hfrac' : IF * FractionalIdeal.spanSingleton O⁰ alpha =
      ((IntegralUnitIdeal.conj I : Ideal O) : FractionalIdeal O⁰ K) := by
    exact hfrac
  have hJFconj : fractionalIdealConj d JF = JF := by
    calc
      fractionalIdealConj d JF =
          FractionalIdeal.spanSingleton O⁰ (zsqrtdFractionConj d beta) *
            ((IntegralUnitIdeal.conj I : Ideal O) :
              FractionalIdeal O⁰ K) := by
        dsimp only [JF, IF]
        rw [map_mul, fractionalIdealConj_spanSingleton,
          fractionalIdealConj_coeIdeal]
        rfl
      _ = FractionalIdeal.spanSingleton O⁰ (zsqrtdFractionConj d beta) *
            (IF * FractionalIdeal.spanSingleton O⁰ alpha) := by
        rw [hfrac']
      _ = FractionalIdeal.spanSingleton O⁰
            (alpha * zsqrtdFractionConj d beta) * IF := by
        calc
          FractionalIdeal.spanSingleton O⁰ (zsqrtdFractionConj d beta) *
                (IF * FractionalIdeal.spanSingleton O⁰ alpha) =
              (FractionalIdeal.spanSingleton O⁰
                  (zsqrtdFractionConj d beta) *
                FractionalIdeal.spanSingleton O⁰ alpha) * IF := by ring
          _ = FractionalIdeal.spanSingleton O⁰
                (zsqrtdFractionConj d beta * alpha) * IF := by
            rw [FractionalIdeal.spanSingleton_mul_spanSingleton]
          _ = FractionalIdeal.spanSingleton O⁰
                (alpha * zsqrtdFractionConj d beta) * IF := by
            congr 2
            exact mul_comm _ _
      _ = JF := by rw [hhilbert]
  have hspanBetaUnit : IsUnit (FractionalIdeal.spanSingleton O⁰ beta) := by
    refine IsUnit.of_mul_eq_one
      (FractionalIdeal.spanSingleton O⁰ beta⁻¹) ?_
    rw [FractionalIdeal.spanSingleton_mul_spanSingleton,
      mul_inv_cancel₀ hbeta, FractionalIdeal.spanSingleton_one]
  have hJFunit : IsUnit JF := by
    dsimp only [JF, IF]
    exact hspanBetaUnit.mul I.2
  let den : O := JF.den
  have hden : den ≠ 0 := by
    exact mem_nonZeroDivisors_iff_ne_zero.mp JF.den.2
  let gamma : O := Zsqrtd.ofInt den.norm
  have hdneg : d < 0 := specialDiscriminant_neg p Fact.out
  have hgamma : gamma ≠ 0 := by
    intro hzero
    have hre := congrArg Zsqrtd.re hzero
    have hnorm0 : den.norm = 0 := by simpa [gamma] using hre
    exact hden ((Zsqrtd.norm_eq_zero_iff hdneg den).mp hnorm0)
  let KI : Ideal O := Ideal.span ({star den} : Set O) * JF.num
  have hKIfrac : ((KI : Ideal O) : FractionalIdeal O⁰ K) =
      FractionalIdeal.spanSingleton O⁰ (algebraMap O K gamma) * JF := by
    calc
      ((KI : Ideal O) : FractionalIdeal O⁰ K) =
          ((Ideal.span ({star den} : Set O) : Ideal O) :
            FractionalIdeal O⁰ K) *
            ((JF.num : Ideal O) : FractionalIdeal O⁰ K) := by
        dsimp only [KI]
        rw [FractionalIdeal.coeIdeal_mul]
      _ = FractionalIdeal.spanSingleton O⁰
            (algebraMap O K (star den)) *
          (FractionalIdeal.spanSingleton O⁰ (algebraMap O K den) * JF) := by
        rw [FractionalIdeal.coeIdeal_span_singleton,
          ← FractionalIdeal.den_mul_self_eq_num' O⁰ K JF]
      _ = (FractionalIdeal.spanSingleton O⁰
            (algebraMap O K (star den)) *
          FractionalIdeal.spanSingleton O⁰ (algebraMap O K den)) * JF := by ring
      _ = FractionalIdeal.spanSingleton O⁰
            (algebraMap O K (star den) * algebraMap O K den) * JF := by
        rw [FractionalIdeal.spanSingleton_mul_spanSingleton]
      _ = FractionalIdeal.spanSingleton O⁰ (algebraMap O K gamma) * JF := by
        congr 2
        rw [← map_mul]
        apply congrArg (algebraMap O K)
        dsimp only [gamma]
        rw [mul_comm, ← Zsqrtd.norm_eq_mul_conj]
        rfl
  have hspanGammaUnit : IsUnit
      (FractionalIdeal.spanSingleton O⁰ (algebraMap O K gamma)) := by
    have hgammaK : algebraMap O K gamma ≠ 0 :=
      by simpa only [map_zero] using
        (IsFractionRing.injective O K).ne hgamma
    refine IsUnit.of_mul_eq_one
      (FractionalIdeal.spanSingleton O⁰ (algebraMap O K gamma)⁻¹) ?_
    rw [FractionalIdeal.spanSingleton_mul_spanSingleton,
      mul_inv_cancel₀ hgammaK, FractionalIdeal.spanSingleton_one]
  have hKIunit : IsUnit ((KI : Ideal O) : FractionalIdeal O⁰ K) := by
    rw [hKIfrac]
    exact hspanGammaUnit.mul hJFunit
  have hKIconj : idealConj d KI = KI := by
    apply FractionalIdeal.coeIdeal_injective (K := K)
    calc
      ((idealConj d KI : Ideal O) : FractionalIdeal O⁰ K) =
          fractionalIdealConj d
            ((KI : Ideal O) : FractionalIdeal O⁰ K) := by
        rw [fractionalIdealConj_coeIdeal]
      _ = fractionalIdealConj d
          (FractionalIdeal.spanSingleton O⁰ (algebraMap O K gamma) * JF) := by
        rw [hKIfrac]
      _ = FractionalIdeal.spanSingleton O⁰ (algebraMap O K gamma) * JF := by
        rw [map_mul, fractionalIdealConj_spanSingleton,
          zsqrtdFractionConj_algebraMap, hJFconj]
        have hstarGamma : star gamma = gamma := by
          dsimp only [gamma]
          rfl
        rw [hstarGamma]
      _ = ((KI : Ideal O) : FractionalIdeal O⁰ K) := hKIfrac.symm
  have hKIprincipal : KI.IsPrincipal :=
    invariant_invertible_specialIdeal_isPrincipal hp4 KI hKIunit hKIconj
  have hKIfracPrincipal :
      ((((KI : Ideal O) : FractionalIdeal O⁰ K) :
        Submodule O K)).IsPrincipal :=
    (IsFractionRing.coeSubmodule_isPrincipal O K).mpr hKIprincipal
  obtain ⟨x, hx⟩ :=
    (FractionalIdeal.isPrincipal_iff
      ((KI : Ideal O) : FractionalIdeal O⁰ K)).mp hKIfracPrincipal
  let g : K := algebraMap O K gamma
  have hg : g ≠ 0 := by
    simpa only [g, map_zero] using (IsFractionRing.injective O K).ne hgamma
  have hJFprincipal : (JF : Submodule O K).IsPrincipal := by
    apply (FractionalIdeal.isPrincipal_iff JF).mpr
    refine ⟨g⁻¹ * x, ?_⟩
    calc
      JF = 1 * JF := by rw [one_mul]
      _ = (FractionalIdeal.spanSingleton O⁰ g⁻¹ *
          FractionalIdeal.spanSingleton O⁰ g) * JF := by
        rw [FractionalIdeal.spanSingleton_mul_spanSingleton,
          inv_mul_cancel₀ hg, FractionalIdeal.spanSingleton_one]
      _ = FractionalIdeal.spanSingleton O⁰ g⁻¹ *
          (FractionalIdeal.spanSingleton O⁰ g * JF) := by ring
      _ = FractionalIdeal.spanSingleton O⁰ g⁻¹ *
          ((KI : Ideal O) : FractionalIdeal O⁰ K) := by
        rw [hKIfrac]
      _ = FractionalIdeal.spanSingleton O⁰ g⁻¹ *
          FractionalIdeal.spanSingleton O⁰ x := by rw [hx]
      _ = FractionalIdeal.spanSingleton O⁰ (g⁻¹ * x) := by
        rw [FractionalIdeal.spanSingleton_mul_spanSingleton]
  have hIFprincipal : (IF : Submodule O K).IsPrincipal := by
    obtain ⟨y, hy⟩ := (FractionalIdeal.isPrincipal_iff JF).mp hJFprincipal
    apply (FractionalIdeal.isPrincipal_iff IF).mpr
    refine ⟨beta⁻¹ * y, ?_⟩
    calc
      IF = 1 * IF := by rw [one_mul]
      _ = (FractionalIdeal.spanSingleton O⁰ beta⁻¹ *
          FractionalIdeal.spanSingleton O⁰ beta) * IF := by
        rw [FractionalIdeal.spanSingleton_mul_spanSingleton,
          inv_mul_cancel₀ hbeta, FractionalIdeal.spanSingleton_one]
      _ = FractionalIdeal.spanSingleton O⁰ beta⁻¹ * JF := by
        dsimp only [JF]
        ring
      _ = FractionalIdeal.spanSingleton O⁰ beta⁻¹ *
          FractionalIdeal.spanSingleton O⁰ y := by rw [hy]
      _ = FractionalIdeal.spanSingleton O⁰ (beta⁻¹ * y) := by
        rw [FractionalIdeal.spanSingleton_mul_spanSingleton]
  rw [← hIclass]
  unfold IntegralUnitIdeal.idealClass
  apply ClassGroup.mk_eq_one_iff.mpr
  rw [IntegralUnitIdeal.unit_coe]
  exact hIFprincipal

theorem special_classSquareSubgroup_eq_top
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    (classSquareSubgroup : Subgroup
      (ClassGroup (Zsqrtd (-((p : ℤ) ^ 3))))) = ⊤ := by
  let : Fintype (ClassGroup (Zsqrtd (-((p : ℤ) ^ 3)))) :=
    zsqrtdClassGroupFintype (-((p : ℤ) ^ 3))
      (specialDiscriminant_neg p Fact.out)
  apply classSquareSubgroup_eq_top_of_sq_eq_one
  intro C hC
  exact special_class_eq_one_of_sq_eq_one hp4 C hC

end

end Erdos1081
