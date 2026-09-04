import ErdosProblems.Erdos1081.Erdos1081Order
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

namespace Erdos1081

open scoped nonZeroDivisors
open Function

noncomputable def splitEval (d : ℤ) (q : ℕ) (r : ZMod q)
    (hr : r * r = (d : ZMod q)) : Zsqrtd d →+* ZMod q :=
  Zsqrtd.lift ⟨r, hr⟩

@[simp] theorem splitEval_ofInt (d : ℤ) (q : ℕ) (r : ZMod q)
    (hr : r * r = (d : ZMod q)) (n : ℤ) :
    splitEval d q r hr (Zsqrtd.ofInt n) = (n : ZMod q) := by
  simp [splitEval]

@[simp] theorem splitEval_sqrtd (d : ℤ) (q : ℕ) (r : ZMod q)
    (hr : r * r = (d : ZMod q)) :
    splitEval d q r hr Zsqrtd.sqrtd = r := by
  simp [splitEval]

def splitPrimeIdeal (d : ℤ) (q : ℕ) (r : ZMod q) : Ideal (Zsqrtd d) :=
  Ideal.span ({Zsqrtd.ofInt (q : ℤ),
      Zsqrtd.sqrtd - Zsqrtd.ofInt (r.val : ℤ)} :
    Set (Zsqrtd d))

def splitConjugateIdeal (d : ℤ) (q : ℕ) (r : ZMod q) :
    Ideal (Zsqrtd d) :=
  Ideal.span ({Zsqrtd.ofInt (q : ℤ),
      Zsqrtd.sqrtd + Zsqrtd.ofInt (r.val : ℤ)} :
    Set (Zsqrtd d))

theorem splitEval_surjective (d : ℤ) (q : ℕ) (r : ZMod q)
    (hr : r * r = (d : ZMod q)) :
    Function.Surjective (splitEval d q r hr) := by
  intro x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  refine ⟨(z : Zsqrtd d), ?_⟩
  simp [splitEval]

theorem splitPrimeIdeal_eq_ker (d : ℤ) (q : ℕ) (r : ZMod q)
    [NeZero q] (hr : r * r = (d : ZMod q)) :
    splitPrimeIdeal d q r = RingHom.ker (splitEval d q r hr) := by
  apply le_antisymm
  · rw [splitPrimeIdeal, Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact RingHom.mem_ker.mpr (by simp)
    · exact RingHom.mem_ker.mpr (by
        rw [map_sub, splitEval_sqrtd, splitEval_ofInt,
          Int.cast_natCast, ZMod.natCast_zmod_val]
        exact sub_self r)
  · intro z hz
    rw [RingHom.mem_ker] at hz
    have hrval : ((r.val : ℕ) : ZMod q) = r := ZMod.natCast_zmod_val r
    have hz' : ((z.re : ZMod q) + (z.im : ZMod q) *
        ((r.val : ℤ) : ZMod q)) = 0 := by
      rw [Int.cast_natCast, hrval]
      simpa [splitEval] using hz
    have hz'' : ((z.re + z.im * (r.val : ℤ) : ℤ) : ZMod q) = 0 := by
      simpa only [Int.cast_add, Int.cast_mul] using hz'
    have hdiv : (q : ℤ) ∣ z.re + z.im * (r.val : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz''
    obtain ⟨k, hk⟩ := hdiv
    have hdecomp : z =
        Zsqrtd.ofInt k * Zsqrtd.ofInt (q : ℤ) +
          Zsqrtd.ofInt z.im *
            (Zsqrtd.sqrtd - Zsqrtd.ofInt (r.val : ℤ)) := by
      ext
      · simp only [sub_eq_add_neg, Zsqrtd.re_add, Zsqrtd.re_mul,
          Zsqrtd.re_ofInt, Zsqrtd.im_ofInt, Zsqrtd.re_neg,
          Zsqrtd.re_sqrtd, mul_zero, zero_mul, add_zero, zero_add]
        nlinarith [hk]
      · simp only [sub_eq_add_neg, Zsqrtd.im_add, Zsqrtd.im_mul,
          Zsqrtd.re_ofInt, Zsqrtd.im_ofInt, Zsqrtd.im_neg,
          Zsqrtd.im_sqrtd, mul_zero, zero_mul, add_zero, zero_add]
        ring
    rw [hdecomp]
    apply (splitPrimeIdeal d q r).add_mem
    · exact (splitPrimeIdeal d q r).mul_mem_left _
        (Ideal.subset_span (Set.mem_insert _ _))
    · exact (splitPrimeIdeal d q r).mul_mem_left _
        (Ideal.subset_span (Set.mem_insert_iff.mpr
          (Or.inr (Set.mem_singleton _))))

theorem splitPrimeIdeal_cardQuot (d : ℤ) (q : ℕ) (r : ZMod q)
    [NeZero q] (hr : r * r = (d : ZMod q)) :
    (splitPrimeIdeal d q r).cardQuot = q := by
  rw [splitPrimeIdeal_eq_ker d q r hr, Submodule.cardQuot_apply]
  calc
    Nat.card (Zsqrtd d ⧸
        (RingHom.ker (splitEval d q r hr)).restrictScalars ℤ) =
        Nat.card (Zsqrtd d ⧸ RingHom.ker (splitEval d q r hr)) :=
      Nat.card_congr
        (Submodule.Quotient.restrictScalarsEquiv ℤ
          (RingHom.ker (splitEval d q r hr))).toEquiv
    _ = Nat.card (ZMod q) := Nat.card_congr
      (RingHom.quotientKerEquivOfSurjective
        (splitEval_surjective d q r hr)).toEquiv
    _ = q := Nat.card_zmod q

/-- The two explicit ideals above multiply to `(q)` whenever the two roots
are distinct modulo `q`.  The coprimality hypothesis is precisely the
unramified condition used in the later prime specialization. -/
theorem splitPrimeIdeal_mul_conjugate (d : ℤ) (q : ℕ) (r : ZMod q)
    [NeZero q] (hr : r * r = (d : ZMod q))
    (hcop : Nat.Coprime q (2 * r.val)) :
    splitPrimeIdeal d q r * splitConjugateIdeal d q r =
      Ideal.span ({Zsqrtd.ofInt (q : ℤ)} : Set (Zsqrtd d)) := by
  have hrval : ((r.val : ℕ) : ZMod q) = r := ZMod.natCast_zmod_val r
  have hcast :
      ((d - (r.val : ℤ) * (r.val : ℤ) : ℤ) : ZMod q) = 0 := by
    rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast, hrval, hr]
    exact sub_self _
  have hdiv : (q : ℤ) ∣ d - (r.val : ℤ) * (r.val : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
  obtain ⟨t, ht⟩ := hdiv
  rw [splitPrimeIdeal, splitConjugateIdeal,
    Ideal.span_pair_mul_span_pair]
  apply le_antisymm
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Ideal.mem_span_singleton'.mpr
        ⟨Zsqrtd.ofInt (q : ℤ), by ring⟩
    · exact Ideal.mem_span_singleton'.mpr
        ⟨Zsqrtd.sqrtd + Zsqrtd.ofInt (r.val : ℤ), by ring⟩
    · exact Ideal.mem_span_singleton'.mpr
        ⟨Zsqrtd.sqrtd - Zsqrtd.ofInt (r.val : ℤ), by ring⟩
    · apply Ideal.mem_span_singleton'.mpr
      refine ⟨Zsqrtd.ofInt t, ?_⟩
      ext <;>
        simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_ofInt,
          Zsqrtd.im_ofInt, Zsqrtd.re_add, Zsqrtd.im_add,
          Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_sqrtd,
          Zsqrtd.im_sqrtd, mul_zero, zero_mul, add_zero, zero_add,
          sub_zero]
      · nlinarith [ht]
      · ring
  · rw [Ideal.span_singleton_le_iff_mem]
    let I : Ideal (Zsqrtd d) := Ideal.span
      ({Zsqrtd.ofInt (q : ℤ) * Zsqrtd.ofInt (q : ℤ),
        Zsqrtd.ofInt (q : ℤ) *
          (Zsqrtd.sqrtd + Zsqrtd.ofInt (r.val : ℤ)),
        (Zsqrtd.sqrtd - Zsqrtd.ofInt (r.val : ℤ)) *
          Zsqrtd.ofInt (q : ℤ),
        (Zsqrtd.sqrtd - Zsqrtd.ofInt (r.val : ℤ)) *
          (Zsqrtd.sqrtd + Zsqrtd.ofInt (r.val : ℤ))} :
        Set (Zsqrtd d))
    change Zsqrtd.ofInt (q : ℤ) ∈ I
    have hA : Zsqrtd.ofInt (q : ℤ) * Zsqrtd.ofInt (q : ℤ) ∈ I :=
      Ideal.subset_span (by simp)
    have hB : Zsqrtd.ofInt (q : ℤ) *
        (Zsqrtd.sqrtd + Zsqrtd.ofInt (r.val : ℤ)) ∈ I :=
      Ideal.subset_span (by simp)
    have hC : (Zsqrtd.sqrtd - Zsqrtd.ofInt (r.val : ℤ)) *
        Zsqrtd.ofInt (q : ℤ) ∈ I :=
      Ideal.subset_span (by simp)
    have hbez : (1 : ℤ) =
        (q : ℤ) * q.gcdA (2 * r.val) +
          (2 * r.val : ℕ) * q.gcdB (2 * r.val) := by
      rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one]
      rfl
    norm_num [Nat.cast_mul] at hbez
    rw [ZMod.cast_eq_val] at hbez
    have hcomb : (Zsqrtd.ofInt (q : ℤ) : Zsqrtd d) =
        Zsqrtd.ofInt (q.gcdA (2 * r.val)) *
            (Zsqrtd.ofInt (q : ℤ) * Zsqrtd.ofInt (q : ℤ)) +
          Zsqrtd.ofInt (q.gcdB (2 * r.val)) *
            (Zsqrtd.ofInt (q : ℤ) *
                (Zsqrtd.sqrtd + Zsqrtd.ofInt (r.val : ℤ)) -
              (Zsqrtd.sqrtd - Zsqrtd.ofInt (r.val : ℤ)) *
                Zsqrtd.ofInt (q : ℤ)) := by
      ext <;>
        simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_sub,
          Zsqrtd.im_sub, Zsqrtd.re_mul, Zsqrtd.im_mul,
          Zsqrtd.re_ofInt, Zsqrtd.im_ofInt, Zsqrtd.re_sqrtd,
          Zsqrtd.im_sqrtd, mul_zero, zero_mul, add_zero, zero_add,
          sub_zero]
      · linear_combination (q : ℤ) * hbez
      · ring
    rw [hcomb]
    exact I.add_mem (I.mul_mem_left _ hA)
      (I.mul_mem_left _ (I.sub_mem hB hC))

/-- A simple split root therefore defines an invertible integral ideal of
the quadratic order, even though the order itself need not be Dedekind. -/
theorem splitPrimeIdeal_isUnit_coe (d : ℤ) (q : ℕ) (r : ZMod q)
    [NeZero q] [IsDomain (Zsqrtd d)] (hr : r * r = (d : ZMod q))
    (hcop : Nat.Coprime q (2 * r.val)) :
    IsUnit
      ((splitPrimeIdeal d q r : Ideal (Zsqrtd d)) :
        FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d))) := by
  have hq : Zsqrtd.ofInt (q : ℤ) ≠ (0 : Zsqrtd d) := by
    intro hzero
    have hre := congrArg Zsqrtd.re hzero
    simp only [Zsqrtd.re_ofInt, Zsqrtd.re_zero] at hre
    exact NeZero.ne q (by exact_mod_cast hre)
  refine IsUnit.of_mul_eq_one
    (((splitConjugateIdeal d q r : Ideal (Zsqrtd d)) :
        FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d))) *
      (((Ideal.span ({Zsqrtd.ofInt (q : ℤ)} : Set (Zsqrtd d)) :
          Ideal (Zsqrtd d)) :
        FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d)))⁻¹)) ?_
  rw [← mul_assoc, ← FractionalIdeal.coeIdeal_mul,
    splitPrimeIdeal_mul_conjugate d q r hr hcop,
    FractionalIdeal.coe_ideal_span_singleton_mul_inv
      (FractionRing (Zsqrtd d)) hq]

/-- The corresponding element of the Picard group, with the integral ideal
retained as its concrete representative. -/
noncomputable def splitPrimeIdealUnit (d : ℤ) (q : ℕ) (r : ZMod q)
    [NeZero q] [IsDomain (Zsqrtd d)] (hr : r * r = (d : ZMod q))
    (hcop : Nat.Coprime q (2 * r.val)) :
    (FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d)))ˣ :=
  (splitPrimeIdeal_isUnit_coe d q r hr hcop).unit

theorem splitPrimeIdealUnit_coe (d : ℤ) (q : ℕ) (r : ZMod q)
    [NeZero q] [IsDomain (Zsqrtd d)] (hr : r * r = (d : ZMod q))
    (hcop : Nat.Coprime q (2 * r.val)) :
    ((splitPrimeIdealUnit d q r hr hcop :
        (FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d)))ˣ) :
      FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d))) =
        (splitPrimeIdeal d q r : Ideal (Zsqrtd d)) :=
  (splitPrimeIdeal_isUnit_coe d q r hr hcop).unit_spec

/-- An invertible integral ideal whose Picard class is trivial is already
principal as an integral ideal.  This is the precise bridge from the class
group computation to an actual generator in the quadratic order. -/
theorem ideal_isPrincipal_of_class_eq_one
    {S : Type*} [CommRing S] [IsDomain S]
    (I : Ideal S)
    (hunit : IsUnit
      ((I : Ideal S) : FractionalIdeal S⁰ (FractionRing S)))
    (hclass : ClassGroup.mk (FractionRing S) hunit.unit = 1) :
    I.IsPrincipal := by
  have hfrac :
      ((hunit.unit : (FractionalIdeal S⁰ (FractionRing S))ˣ) :
          Submodule S (FractionRing S)).IsPrincipal :=
    ClassGroup.mk_eq_one_iff.mp hclass
  rw [hunit.unit_spec] at hfrac
  exact (IsFractionRing.coeSubmodule_isPrincipal S (FractionRing S)).mp hfrac

/-- A principal ideal has a generator whose algebra norm is its additive
index.  This form does not require Dedekind factorization. -/
theorem exists_generator_norm_natAbs_eq_cardQuot
    {S : Type*} [CommRing S] [IsDomain S]
    [Module.Free ℤ S] [Module.Finite ℤ S]
    (I : Ideal S) (hI : I.IsPrincipal) :
    ∃ z : S, I = Ideal.span ({z} : Set S) ∧
      (Algebra.norm ℤ z).natAbs = I.cardQuot := by
  let : I.IsPrincipal := hI
  obtain ⟨z, hz⟩ := Submodule.IsPrincipal.principal I
  have hzIdeal : I = Ideal.span ({z} : Set S) := by
    rw [← Ideal.submodule_span_eq]
    exact hz
  refine ⟨z, hzIdeal, ?_⟩
  rw [hzIdeal, cardQuot_span_singleton_eq_norm_natAbs]

theorem splitConjugateIdeal_eq_ker (d : ℤ) (q : ℕ) (r : ZMod q)
    [NeZero q] (hr : r * r = (d : ZMod q)) :
    splitConjugateIdeal d q r =
      RingHom.ker (splitEval d q (-r) (by simpa using hr)) := by
  let hneg : (-r) * (-r) = (d : ZMod q) := by simpa using hr
  apply le_antisymm
  · rw [splitConjugateIdeal, Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact RingHom.mem_ker.mpr (by simp)
    · exact RingHom.mem_ker.mpr (by
        rw [map_add, splitEval_sqrtd, splitEval_ofInt,
          Int.cast_natCast, ZMod.natCast_zmod_val]
        exact neg_add_cancel r)
  · intro z hz
    rw [RingHom.mem_ker] at hz
    have hrval : ((r.val : ℕ) : ZMod q) = r := ZMod.natCast_zmod_val r
    have hz' : ((z.re : ZMod q) - (z.im : ZMod q) *
        ((r.val : ℤ) : ZMod q)) = 0 := by
      rw [Int.cast_natCast, hrval, sub_eq_add_neg]
      simpa [splitEval, hneg] using hz
    have hz'' : ((z.re - z.im * (r.val : ℤ) : ℤ) : ZMod q) = 0 := by
      simpa only [Int.cast_sub, Int.cast_mul] using hz'
    have hdiv : (q : ℤ) ∣ z.re - z.im * (r.val : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz''
    obtain ⟨k, hk⟩ := hdiv
    have hdecomp : z =
        Zsqrtd.ofInt k * Zsqrtd.ofInt (q : ℤ) +
          Zsqrtd.ofInt z.im *
            (Zsqrtd.sqrtd + Zsqrtd.ofInt (r.val : ℤ)) := by
      ext
      · simp only [Zsqrtd.re_add, Zsqrtd.re_mul,
          Zsqrtd.re_ofInt, Zsqrtd.im_ofInt,
          Zsqrtd.re_sqrtd, mul_zero, zero_mul, add_zero, zero_add]
        nlinarith [hk]
      · simp only [Zsqrtd.im_add, Zsqrtd.im_mul,
          Zsqrtd.re_ofInt, Zsqrtd.im_ofInt,
          Zsqrtd.im_sqrtd, mul_zero, zero_mul, add_zero, zero_add]
        ring
    rw [hdecomp]
    apply (splitConjugateIdeal d q r).add_mem
    · exact (splitConjugateIdeal d q r).mul_mem_left _
        (Ideal.subset_span (Set.mem_insert _ _))
    · exact (splitConjugateIdeal d q r).mul_mem_left _
        (Ideal.subset_span (Set.mem_insert_iff.mpr
          (Or.inr (Set.mem_singleton _))))

theorem splitConjugateIdeal_cardQuot (d : ℤ) (q : ℕ) (r : ZMod q)
    [NeZero q] (hr : r * r = (d : ZMod q)) :
    (splitConjugateIdeal d q r).cardQuot = q := by
  rw [splitConjugateIdeal_eq_ker d q r hr, Submodule.cardQuot_apply]
  calc
    Nat.card (Zsqrtd d ⧸
        (RingHom.ker (splitEval d q (-r) (by simpa using hr))).restrictScalars ℤ) =
        Nat.card (Zsqrtd d ⧸
          RingHom.ker (splitEval d q (-r) (by simpa using hr))) :=
      Nat.card_congr
        (Submodule.Quotient.restrictScalarsEquiv ℤ
          (RingHom.ker (splitEval d q (-r) (by simpa using hr)))).toEquiv
    _ = Nat.card (ZMod q) := Nat.card_congr
      (RingHom.quotientKerEquivOfSurjective
        (splitEval_surjective d q (-r) (by simpa using hr))).toEquiv
    _ = q := Nat.card_zmod q

theorem splitConjugateIdeal_isUnit_coe (d : ℤ) (q : ℕ) (r : ZMod q)
    [NeZero q] [IsDomain (Zsqrtd d)] (hr : r * r = (d : ZMod q))
    (hcop : Nat.Coprime q (2 * r.val)) :
    IsUnit
      ((splitConjugateIdeal d q r : Ideal (Zsqrtd d)) :
        FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d))) := by
  have hq : Zsqrtd.ofInt (q : ℤ) ≠ (0 : Zsqrtd d) := by
    intro hzero
    have hre := congrArg Zsqrtd.re hzero
    simp only [Zsqrtd.re_ofInt, Zsqrtd.re_zero] at hre
    exact NeZero.ne q (by exact_mod_cast hre)
  refine IsUnit.of_mul_eq_one
    (((splitPrimeIdeal d q r : Ideal (Zsqrtd d)) :
        FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d))) *
      (((Ideal.span ({Zsqrtd.ofInt (q : ℤ)} : Set (Zsqrtd d)) :
          Ideal (Zsqrtd d)) :
        FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d)))⁻¹)) ?_
  calc
    ((splitConjugateIdeal d q r : Ideal (Zsqrtd d)) :
          FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d))) *
        (((splitPrimeIdeal d q r : Ideal (Zsqrtd d)) :
            FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d))) *
          (((Ideal.span ({Zsqrtd.ofInt (q : ℤ)} : Set (Zsqrtd d)) :
              Ideal (Zsqrtd d)) :
            FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d)))⁻¹)) =
        (((splitPrimeIdeal d q r : Ideal (Zsqrtd d)) :
            FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d))) *
          ((splitConjugateIdeal d q r : Ideal (Zsqrtd d)) :
            FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d)))) *
          (((Ideal.span ({Zsqrtd.ofInt (q : ℤ)} : Set (Zsqrtd d)) :
              Ideal (Zsqrtd d)) :
            FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d)))⁻¹) := by
              ac_rfl
    _ = 1 := by
      rw [← FractionalIdeal.coeIdeal_mul,
        splitPrimeIdeal_mul_conjugate d q r hr hcop,
        FractionalIdeal.coe_ideal_span_singleton_mul_inv
          (FractionRing (Zsqrtd d)) hq]

noncomputable def splitConjugateIdealUnit (d : ℤ) (q : ℕ) (r : ZMod q)
    [NeZero q] [IsDomain (Zsqrtd d)] (hr : r * r = (d : ZMod q))
    (hcop : Nat.Coprime q (2 * r.val)) :
    (FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d)))ˣ :=
  (splitConjugateIdeal_isUnit_coe d q r hr hcop).unit

theorem splitConjugateIdealUnit_coe (d : ℤ) (q : ℕ) (r : ZMod q)
    [NeZero q] [IsDomain (Zsqrtd d)] (hr : r * r = (d : ZMod q))
    (hcop : Nat.Coprime q (2 * r.val)) :
    ((splitConjugateIdealUnit d q r hr hcop :
        (FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d)))ˣ) :
      FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d))) =
        (splitConjugateIdeal d q r : Ideal (Zsqrtd d)) :=
  (splitConjugateIdeal_isUnit_coe d q r hr hcop).unit_spec

theorem splitConjugateIdeal_class_eq_inv (d : ℤ) (q : ℕ) (r : ZMod q)
    [NeZero q] [IsDomain (Zsqrtd d)] (hr : r * r = (d : ZMod q))
    (hcop : Nat.Coprime q (2 * r.val)) :
    ClassGroup.mk (FractionRing (Zsqrtd d))
        (splitConjugateIdealUnit d q r hr hcop) =
      (ClassGroup.mk (FractionRing (Zsqrtd d))
        (splitPrimeIdealUnit d q r hr hcop))⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← map_mul]
  apply ClassGroup.mk_eq_one_iff.mpr
  have hcoe :
      (((splitPrimeIdealUnit d q r hr hcop) *
          (splitConjugateIdealUnit d q r hr hcop) :
        (FractionalIdeal (Zsqrtd d)⁰
          (FractionRing (Zsqrtd d)))ˣ) :
          FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d))) =
        (Ideal.span ({Zsqrtd.ofInt (q : ℤ)} : Set (Zsqrtd d)) :
          Ideal (Zsqrtd d)) := by
    rw [Units.val_mul, splitPrimeIdealUnit_coe,
      splitConjugateIdealUnit_coe, ← FractionalIdeal.coeIdeal_mul,
      splitPrimeIdeal_mul_conjugate d q r hr hcop]
  rw [hcoe]
  exact (IsFractionRing.coeSubmodule_isPrincipal
    (Zsqrtd d) (FractionRing (Zsqrtd d))).mpr inferInstance

/-- The integral prime ideal selected by a sign: `false` is the chosen root
and `true` is its conjugate (hence inverse in the Picard group). -/
def orientedSplitIdeal (d : ℤ) (q : ℕ) (r : ZMod q) (b : Bool) :
    Ideal (Zsqrtd d) :=
  if b then splitConjugateIdeal d q r else splitPrimeIdeal d q r

noncomputable def orientedSplitIdealUnit
    (d : ℤ) (q : ℕ) (r : ZMod q) [NeZero q] [IsDomain (Zsqrtd d)]
    (hr : r * r = (d : ZMod q)) (hcop : Nat.Coprime q (2 * r.val))
    (b : Bool) :
    (FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d)))ˣ :=
  if b then splitConjugateIdealUnit d q r hr hcop
  else splitPrimeIdealUnit d q r hr hcop

theorem orientedSplitIdealUnit_coe
    (d : ℤ) (q : ℕ) (r : ZMod q) [NeZero q] [IsDomain (Zsqrtd d)]
    (hr : r * r = (d : ZMod q)) (hcop : Nat.Coprime q (2 * r.val))
    (b : Bool) :
    ((orientedSplitIdealUnit d q r hr hcop b :
        (FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d)))ˣ) :
      FractionalIdeal (Zsqrtd d)⁰ (FractionRing (Zsqrtd d))) =
        orientedSplitIdeal d q r b := by
  cases b <;> simp [orientedSplitIdealUnit, orientedSplitIdeal,
    splitPrimeIdealUnit_coe, splitConjugateIdealUnit_coe]

theorem orientedSplitIdeal_class
    (d : ℤ) (q : ℕ) (r : ZMod q) [NeZero q] [IsDomain (Zsqrtd d)]
    (hr : r * r = (d : ZMod q)) (hcop : Nat.Coprime q (2 * r.val))
    (b : Bool) :
    ClassGroup.mk (FractionRing (Zsqrtd d))
        (orientedSplitIdealUnit d q r hr hcop b) =
      if b then
        (ClassGroup.mk (FractionRing (Zsqrtd d))
          (splitPrimeIdealUnit d q r hr hcop))⁻¹
      else ClassGroup.mk (FractionRing (Zsqrtd d))
        (splitPrimeIdealUnit d q r hr hcop) := by
  cases b <;> simp [orientedSplitIdealUnit,
    splitConjugateIdeal_class_eq_inv]

theorem orientedSplitIdeal_cardQuot
    (d : ℤ) (q : ℕ) (r : ZMod q) [NeZero q]
    (hr : r * r = (d : ZMod q)) (b : Bool) :
    (orientedSplitIdeal d q r b).cardQuot = q := by
  cases b <;> simp [orientedSplitIdeal, splitPrimeIdeal_cardQuot,
    splitConjugateIdeal_cardQuot, hr]

theorem ofInt_mem_orientedSplitIdeal
    (d : ℤ) (q : ℕ) (r : ZMod q) (b : Bool) :
    Zsqrtd.ofInt (q : ℤ) ∈ orientedSplitIdeal d q r b := by
  cases b
  · exact Ideal.subset_span (Set.mem_insert _ _)
  · exact Ideal.subset_span (Set.mem_insert _ _)

/-- Ideals above coprime rational integers are comaximal, regardless of the
choice of conjugate above either integer. -/
theorem orientedSplitIdeal_isCoprime_of_coprime
    (d : ℤ) {q s : ℕ} (r : ZMod q) (t : ZMod s) (b c : Bool)
    (hqs : Nat.Coprime q s) :
    IsCoprime (orientedSplitIdeal d q r b)
      (orientedSplitIdeal d s t c) := by
  apply Ideal.isCoprime_iff_exists.mpr
  refine ⟨Zsqrtd.ofInt (q.gcdA s) * Zsqrtd.ofInt (q : ℤ), ?_,
    Zsqrtd.ofInt (q.gcdB s) * Zsqrtd.ofInt (s : ℤ), ?_, ?_⟩
  · exact (orientedSplitIdeal d q r b).mul_mem_left _
      (ofInt_mem_orientedSplitIdeal d q r b)
  · exact (orientedSplitIdeal d s t c).mul_mem_left _
      (ofInt_mem_orientedSplitIdeal d s t c)
  · have hbez : (1 : ℤ) =
        (q : ℤ) * q.gcdA s + (s : ℤ) * q.gcdB s := by
      rw [← Nat.gcd_eq_gcd_ab, hqs.gcd_eq_one]
      rfl
    ext <;> simp only [Zsqrtd.re_add, Zsqrtd.im_add,
      Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_ofInt,
      Zsqrtd.im_ofInt, Zsqrtd.re_one, Zsqrtd.im_one,
      mul_zero, zero_mul, add_zero, zero_add]
    linarith

/-- Chinese remaindering makes quotient cardinality multiplicative for a
finite pairwise-comaximal family, without a Dedekind-domain assumption. -/
theorem cardQuot_prod_of_pairwise_isCoprime
    {S : Type*} [CommRing S] {ι : Type*}
    (s : Finset ι) (J : ι → Ideal S)
    (hpair : (s : Set ι).Pairwise (IsCoprime on J)) :
    (∏ i ∈ s, J i).cardQuot = ∏ i ∈ s, (J i).cardQuot := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      rw [cardQuot_mul_of_coprime]
      · congr 1
        apply ih
        intro i hi j hj hij
        exact hpair (Finset.mem_insert_of_mem hi)
          (Finset.mem_insert_of_mem hj) hij
      · apply IsCoprime.prod_right
        intro i hi
        exact hpair (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi)
          (by intro hai; subst i; exact ha hi)

/-- A finite product of invertible, pairwise-comaximal integral ideals in the
trivial Picard class has a generator whose norm is the product of the
individual quotient cardinalities. -/
theorem exists_generator_norm_eq_prod_of_class_product_eq_one
    {S : Type*} [CommRing S] [IsDomain S]
    [Module.Free ℤ S] [Module.Finite ℤ S]
    {k : ℕ} (q : Fin k → ℕ) (J : Fin k → Ideal S)
    (U : Fin k → (FractionalIdeal S⁰ (FractionRing S))ˣ)
    (hcoe : ∀ i,
      ((U i : (FractionalIdeal S⁰ (FractionRing S))ˣ) :
        FractionalIdeal S⁰ (FractionRing S)) = J i)
    (hpair : ∀ i j, i ≠ j → IsCoprime (J i) (J j))
    (hcard : ∀ i, (J i).cardQuot = q i)
    (hclass : ∏ i, ClassGroup.mk (FractionRing S) (U i) = 1) :
    ∃ z : S, (Algebra.norm ℤ z).natAbs = ∏ i, q i := by
  classical
  let I : Ideal S := ∏ i, J i
  let IU : (FractionalIdeal S⁰ (FractionRing S))ˣ := ∏ i, U i
  have hcoeProd :
      ((IU : (FractionalIdeal S⁰ (FractionRing S))ˣ) :
        FractionalIdeal S⁰ (FractionRing S)) = I := by
    dsimp [IU, I]
    calc
      (((∏ i, U i :
          (FractionalIdeal S⁰ (FractionRing S))ˣ) :
        (FractionalIdeal S⁰ (FractionRing S))ˣ) :
          FractionalIdeal S⁰ (FractionRing S)) =
          ∏ i, ((U i :
            (FractionalIdeal S⁰ (FractionRing S))ˣ) :
              FractionalIdeal S⁰ (FractionRing S)) := by
        simpa using (Units.coe_prod U (Finset.univ : Finset (Fin k)))
      _ = ∏ i, ((J i : Ideal S) :
          FractionalIdeal S⁰ (FractionRing S)) :=
        Finset.prod_congr rfl fun i _ => hcoe i
      _ = ((∏ i, J i : Ideal S) :
          FractionalIdeal S⁰ (FractionRing S)) := by
        symm
        change
          (FractionalIdeal.coeIdealHom S⁰ (FractionRing S))
              ((Finset.univ : Finset (Fin k)).prod J) =
            (Finset.univ : Finset (Fin k)).prod
              (fun i =>
                (FractionalIdeal.coeIdealHom S⁰ (FractionRing S)) (J i))
        exact map_prod
          (FractionalIdeal.coeIdealHom S⁰ (FractionRing S)) J
          (Finset.univ : Finset (Fin k))
  have hunit : IsUnit
      ((I : Ideal S) : FractionalIdeal S⁰ (FractionRing S)) := by
    exact ⟨IU, hcoeProd⟩
  have hclassIU : ClassGroup.mk (FractionRing S) hunit.unit = 1 := by
    have hIUeq : hunit.unit = IU := by
      apply Units.ext
      exact hunit.unit_spec.trans hcoeProd.symm
    rw [hIUeq]
    dsimp [IU]
    rw [map_prod]
    exact hclass
  have hprincipal : I.IsPrincipal :=
    ideal_isPrincipal_of_class_eq_one I hunit hclassIU
  obtain ⟨z, _hzI, hnorm⟩ :=
    exists_generator_norm_natAbs_eq_cardQuot I hprincipal
  refine ⟨z, hnorm.trans ?_⟩
  dsimp [I]
  rw [cardQuot_prod_of_pairwise_isCoprime]
  · exact Finset.prod_congr rfl fun i _ => hcard i
  · intro i _hi j _hj hij
    exact hpair i j hij

end Erdos1081
