/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import ErdosProblems.Erdos240.External.Towers.ClassField.KummerTheory.KummerCorrespondenceProof

/-!
# The radical-degree condition for Erdős Problem 240

For any finite family of distinct rational primes, adjoining arbitrary
thirteenth roots has degree `13 ^ n` over `ℚ`.  The proof first establishes
independence of the prime power classes over `ℚ(ζ₁₃)` by taking norms and
then applying rational `p`-adic valuations.  The Kummer correspondence gives
the degree over the cyclotomic field, and a compositum estimate descends it
to `ℚ`.
-/

open Polynomial
open Towers.CField.KTheory

namespace Erdos240.Kummer

universe u

noncomputable def zmodClassHom {G : Type*} [CommGroup G]
    (q : ℕ) (g : G) (hg : g ^ q = 1) : ZMod q →+ Additive G :=
  ZMod.lift q ⟨zmultiplesHom (Additive G) (Additive.ofMul g), by
    rw [zmultiplesHom_apply]
    apply Additive.ext
    rw [toMul_zsmul]
    simpa using hg⟩

@[simp]
theorem zmodClassHom_apply_val {G : Type*} [CommGroup G]
    {q : ℕ} [NeZero q] (g : G) (hg : g ^ q = 1) (a : ZMod q) :
    (zmodClassHom q g hg a).toMul = g ^ a.val := by
  calc
    (zmodClassHom q g hg a).toMul =
        (zmodClassHom q g hg (a.val : ZMod q)).toMul :=
      congrArg (fun z : ZMod q ↦ (zmodClassHom q g hg z).toMul)
        (ZMod.natCast_zmod_val a).symm
    _ = g ^ a.val := by
      rw [show (a.val : ZMod q) = a.val • (1 : ZMod q) by simp]
      rw [map_nsmul, toMul_nsmul]
      congr 1
      rw [zmodClassHom,
        show (1 : ZMod q) = ((1 : ℤ) : ZMod q) by norm_num,
        ZMod.lift_coe, zmultiplesHom_apply]
      simp

noncomputable def primeUnit {K : Type*} [Field K] [Algebra ℚ K]
    (p : ℕ) (hp : p.Prime) : Kˣ :=
  Units.map (algebraMap ℚ K) (Units.mk0 (p : ℚ) (by
    exact_mod_cast hp.ne_zero))

noncomputable def primeClassFamilyAddHom
    {ι K : Type*} [Fintype ι] [Field K] [Algebra ℚ K]
    (q : ℕ) (p : ι → ℕ) (hp : ∀ i, (p i).Prime) :
    (ι → ZMod q) →+ Additive (PowerClassGroup K q) where
  toFun a := ∑ i, zmodClassHom q
    (powerClass q (primeUnit (p i) (hp i)))
    (power_class_pow q _) (a i)
  map_zero' := by simp
  map_add' a b := by
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]

noncomputable def primeClassFamilyHom
    {ι K : Type*} [Fintype ι] [Field K] [Algebra ℚ K]
    (q : ℕ) (p : ι → ℕ) (hp : ∀ i, (p i).Prime) :
    Multiplicative (ι → ZMod q) →* PowerClassGroup K q :=
  (primeClassFamilyAddHom q p hp).toMultiplicativeLeft

@[simp]
theorem primeClassFamilyHom_apply
    {ι K : Type*} [Fintype ι] [Field K] [Algebra ℚ K]
    {q : ℕ} [NeZero q] (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (a : Multiplicative (ι → ZMod q)) :
    primeClassFamilyHom q p hp a =
      ∏ i, powerClass q (primeUnit (K := K) (p i) (hp i)) ^
        (a.toAdd i).val := by
  change (∑ i, zmodClassHom q
    (powerClass q (primeUnit (K := K) (p i) (hp i)))
    (power_class_pow q _) (a.toAdd i)).toMul = _
  simp only [toMul_sum, zmodClassHom_apply_val]

theorem padicValRat_prod {ι : Type*} [DecidableEq ι] {p : ℕ} [Fact p.Prime]
    (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      rw [padicValRat.mul (hf a (Finset.mem_insert_self a s))]
      · rw [ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)]
      · exact Finset.prod_ne_zero_iff.mpr fun i hi ↦
          hf i (Finset.mem_insert_of_mem hi)

theorem prime_product_eq_pow_dvd_exponents
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    {q : ℕ} (e : ι → ℕ) (x : ℚ)
    (hx : x ^ q = ∏ i, (p i : ℚ) ^ e i) : ∀ i, q ∣ e i := by
  intro i
  let _ : Fact (p i).Prime := ⟨hp i⟩
  have hv := congrArg (padicValRat (p i)) hx
  rw [padicValRat.pow] at hv
  rw [padicValRat_prod Finset.univ (fun j ↦ (p j : ℚ) ^ e j)] at hv
  · simp only [padicValRat.pow] at hv
    have hval : ∀ j, padicValRat (p i) (p j : ℚ) = if j = i then 1 else 0 := by
      intro j
      split_ifs with hji
      · subst j
        exact padicValRat.self (hp i).one_lt
      · rw [padicValRat.of_nat]
        let _ : Fact (p j).Prime := ⟨hp j⟩
        have hpij : p i ≠ p j := fun h ↦ hji (hinj h).symm
        rw [padicValNat_primes hpij]
        rfl
    simp_rw [hval] at hv
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at hv
    have hd : (q : ℤ) ∣ (e i : ℤ) := ⟨padicValRat (p i) x, hv.symm⟩
    exact_mod_cast hd
  · intro j _
    exact pow_ne_zero _ (by exact_mod_cast (hp j).ne_zero)

theorem prime_product_is_not_pow_in_coprime_degree_extension
    {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    {q : ℕ} (hcop : q.Coprime (Module.finrank ℚ K))
    (e : ι → ℕ) (he : ∀ i, e i < q) (x : K)
    (hx : x ^ q = algebraMap ℚ K (∏ i, (p i : ℚ) ^ e i)) : ∀ i, e i = 0 := by
  have hn := congrArg (Algebra.norm ℚ : K → ℚ) hx
  simp only [map_pow, Algebra.norm_algebraMap] at hn
  have hprod :
      (∏ i, (p i : ℚ) ^ e i) ^ Module.finrank ℚ K =
        ∏ i, (p i : ℚ) ^ (e i * Module.finrank ℚ K) := by
    simpa only [pow_mul] using
      (Finset.prod_pow (Finset.univ : Finset ι) (Module.finrank ℚ K)
        (fun i ↦ (p i : ℚ) ^ e i)).symm
  rw [hprod] at hn
  have hd := prime_product_eq_pow_dvd_exponents p hp hinj
    (fun i ↦ e i * Module.finrank ℚ K) (Algebra.norm ℚ x) hn
  intro i
  have hqei : q ∣ e i := (hcop.dvd_mul_right).mp (hd i)
  exact Nat.eq_zero_of_dvd_of_lt hqei (he i)

theorem primeClassFamilyHom_injective
    {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {q : ℕ} [NeZero q] (hcop : q.Coprime (Module.finrank ℚ K))
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    Function.Injective (primeClassFamilyHom (K := K) q p hp) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply eq_bot_iff.mpr
  intro a ha
  change primeClassFamilyHom (K := K) q p hp a = 1 at ha
  have hclass : powerClass q
      (∏ i, primeUnit (K := K) (p i) (hp i) ^ (a.toAdd i).val) = 1 := by
    simpa only [primeClassFamilyHom_apply, map_prod, map_pow] using ha
  have hmem := (QuotientGroup.eq_one_iff
    (N := (powMonoidHom q : Kˣ →* Kˣ).range)
    (∏ i, primeUnit (K := K) (p i) (hp i) ^ (a.toAdd i).val)).mp hclass
  obtain ⟨x, hx⟩ := hmem
  have hxK := congrArg (fun u : Kˣ ↦ (u : K)) hx
  have hxK' : (x : K) ^ q =
      algebraMap ℚ K (∏ i, (p i : ℚ) ^ (a.toAdd i).val) := by
    calc
      (x : K) ^ q =
          ∏ i, ((primeUnit (K := K) (p i) (hp i) : K) ^
            (a.toAdd i).val) := by
        simpa only [powMonoidHom_apply, Units.val_pow_eq_pow_val,
          Units.coe_prod] using hxK
      _ = algebraMap ℚ K (∏ i, (p i : ℚ) ^ (a.toAdd i).val) := by
        rw [map_prod]
        apply Finset.prod_congr rfl
        intro i _
        rw [map_pow]
        rfl
  have hz := prime_product_is_not_pow_in_coprime_degree_extension
    p hp hinj hcop (fun i ↦ (a.toAdd i).val)
    (fun i ↦ (a.toAdd i).val_lt) (x : K) hxK'
  ext i
  exact (ZMod.val_injective q) (by simpa using hz i)

noncomputable def primeClassPCSubgro
    {ι K : Type*} [Fintype ι] [Field K] [Algebra ℚ K]
    (q : ℕ) [NeZero q] (p : ι → ℕ) (hp : ∀ i, (p i).Prime) : PCSubgro K q where
  carrier := (primeClassFamilyHom (K := K) q p hp).range
  finite_carrier := by
    change Set.Finite (Set.range (primeClassFamilyHom (K := K) q p hp))
    exact Set.finite_range _

theorem primeClassPCSubgro_card
    {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {q : ℕ} [NeZero q] (hcop : q.Coprime (Module.finrank ℚ K))
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    (primeClassPCSubgro (K := K) q p hp).card = q ^ Fintype.card ι := by
  rw [PCSubgro.card_eq_card]
  have hi := primeClassFamilyHom_injective (K := K) hcop p hp hinj
  change Nat.card ↑((primeClassFamilyHom (K := K) q p hp).range) =
    q ^ Fintype.card ι
  calc
    Nat.card ↑((primeClassFamilyHom (K := K) q p hp).range) =
        Nat.card (Multiplicative (ι → ZMod q)) :=
      (Nat.card_congr
        (Equiv.ofInjective (primeClassFamilyHom (K := K) q p hp) hi)).symm
    _ = q ^ Fintype.card ι := by simp [Nat.card_fun]

theorem finrank_prime_kummerField
    {ι : Type*} {K Ω : Type u} [Fintype ι] [DecidableEq ι]
    [Field K] [Field Ω] [Algebra ℚ K] [Algebra K Ω]
    [FiniteDimensional ℚ K] [IsAlgClosure K Ω]
    {q : ℕ} [NeZero q] (hroots : (primitiveRoots q K).Nonempty)
    (hcop : q.Coprime (Module.finrank ℚ K))
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    Module.finrank K
      (kummerField K Ω q (NeZero.pos q) (primeClassPCSubgro q p hp)) =
        q ^ Fintype.card ι := by
  rw [finrank_kummer_field q (NeZero.pos q) hroots,
    primeClassPCSubgro_card (K := K) hcop p hp hinj]

theorem finrank_adjoin_prime_radicals
    {ι : Type*} {K Ω : Type u} [Fintype ι] [DecidableEq ι]
    [Field K] [Field Ω] [Algebra ℚ K] [Algebra ℚ Ω] [Algebra K Ω]
    [IsScalarTower ℚ K Ω] [FiniteDimensional ℚ K] [IsAlgClosure K Ω]
    {q : ℕ} [NeZero q] (hroots : (primitiveRoots q K).Nonempty)
    (hcop : q.Coprime (Module.finrank ℚ K))
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (beta : ι → Ω)
    (hbeta : ∀ i, beta i ^ q = algebraMap ℚ Ω (p i : ℚ)) :
    Module.finrank K (IntermediateField.adjoin K (Set.range beta)) =
      q ^ Fintype.card ι := by
  classical
  let L := IntermediateField.adjoin K (Set.range beta)
  have hpow : ∀ x ∈ Set.range beta,
      x ^ q ∈ (⊥ : IntermediateField K Ω) := by
    rintro x ⟨i, rfl⟩
    rw [hbeta i]
    exact (IntermediateField.mem_bot).2
      ⟨algebraMap ℚ K (p i : ℚ), by simp [IsScalarTower.algebraMap_apply]⟩
  letI : FiniteDimensional K L :=
    dimensional_adjoin_pow q (NeZero.pos q) (Set.range beta)
      (Set.finite_range beta) hpow
  have hgen : ∀ i, powerClass q (primeUnit (p i) (hp i)) ∈
      radicalPowerClasses K Ω q L := by
    intro i
    let bi : L := ⟨beta i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
    have hbine : bi ≠ 0 := by
      intro hzero
      have hz : beta i = 0 := congrArg Subtype.val hzero
      have := hbeta i
      rw [hz, zero_pow (NeZero.ne q)] at this
      exact (map_ne_zero (algebraMap ℚ Ω)).2 (by
        exact_mod_cast (hp i).ne_zero) this.symm
    let bu : Lˣ := Units.mk0 bi hbine
    refine ⟨primeUnit (p i) (hp i), ?_, rfl⟩
    refine ⟨bu, ?_⟩
    apply Units.ext
    apply Subtype.ext
    change beta i ^ q = algebraMap K Ω (algebraMap ℚ K (p i : ℚ))
    rw [hbeta i, IsScalarTower.algebraMap_apply ℚ K Ω]
  have hB : (primeClassPCSubgro q p hp).carrier ≤
      radicalPowerClasses K Ω q L := by
    rintro b ⟨a, rfl⟩
    rw [primeClassFamilyHom_apply (K := K)]
    show (∏ i, powerClass q (primeUnit (K := K) (p i) (hp i)) ^
      (a.toAdd i).val) ∈ radicalPowerClasses K Ω q L
    classical
    induction (Finset.univ : Finset ι) using Finset.induction_on with
    | empty => simp
    | @insert i s his ih =>
        rw [Finset.prod_insert his]
        exact (radicalPowerClasses K Ω q L).mul_mem
          ((radicalPowerClasses K Ω q L).pow_mem (hgen i) _) ih
  have hKummer_le :
      kummerField K Ω q (NeZero.pos q) (primeClassPCSubgro q p hp) ≤ L := by
    let zeta : K := hroots.choose
    have hzeta : IsPrimitiveRoot zeta q :=
      (mem_primitiveRoots (NeZero.pos q)).mp hroots.choose_spec
    exact field_radical_classes K Ω q (NeZero.pos q) hzeta L
      (primeClassPCSubgro q p hp) hB
  have hlower : q ^ Fintype.card ι ≤ Module.finrank K L := by
    rw [← finrank_prime_kummerField (Ω := Ω) hroots hcop p hp hinj]
    exact IntermediateField.finrank_le_of_le_right hKummer_le
  let roots : Finset Ω := Finset.univ.image beta
  have hpow' : ∀ x ∈ roots,
      x ^ q ∈ (⊥ : IntermediateField K Ω) := by
    intro x hx
    simp only [roots, Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hpow (beta i) ⟨i, rfl⟩
  have hupper' := finrank_adjoin_finset q (NeZero.pos q) roots hpow'
  have hroots_set : (roots : Set Ω) = Set.range beta := by
    ext x
    simp [roots]
  rw [hroots_set] at hupper'
  have hcard : roots.card ≤ Fintype.card ι :=
    (Finset.card_image_le :
      (Finset.univ.image beta).card ≤ (Finset.univ : Finset ι).card)
  have hupper : Module.finrank K L ≤ q ^ Fintype.card ι :=
    hupper'.trans (Nat.pow_le_pow_right (NeZero.pos q) hcard)
  exact le_antisymm hupper hlower

theorem finrank_adjoin_prime_radicals_rat
    {ι : Type*} {Ω : Type u} [Fintype ι] [DecidableEq ι]
    [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (K : IntermediateField ℚ Ω) [hfd : FiniteDimensional ℚ K]
    {q : ℕ} [NeZero q] (hroots : (primitiveRoots q K).Nonempty)
    (hcop : q.Coprime (Module.finrank ℚ K))
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (beta : ι → Ω)
    (hbeta : ∀ i, beta i ^ q = algebraMap ℚ Ω (p i : ℚ)) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ (Set.range beta)) =
      q ^ Fintype.card ι := by
  classical
  have hmodule : (Algebra.toModule : Module ℚ K) = K.module' :=
    Subsingleton.elim _ _
  have hfd' : @FiniteDimensional ℚ K _ _ Algebra.toModule := by
    rw [hmodule]
    exact hfd
  letI : @FiniteDimensional ℚ K _ _ Algebra.toModule := hfd'
  have hcop' : q.Coprime (@Module.finrank ℚ K _ _ Algebra.toModule) := by
    rw [hmodule]
    exact hcop
  letI : IsAlgClosure K Ω :=
    { isAlgClosed := IsAlgClosure.isAlgClosed ℚ
      isAlgebraic := inferInstance }
  letI : IsScalarTower ℚ K Ω := by
    constructor
    intro r x y
    change ((↑(r • x : K) : Ω) * y) = r • ((x : Ω) * y)
    rw [Rat.smul_def, Algebra.smul_def]
    have hr : (↑(r : K) : Ω) = algebraMap ℚ Ω r := by
      rw [show (↑(r : K) : Ω) = (r : Ω) by
        exact map_ratCast (algebraMap K Ω) r]
      exact (map_ratCast (algebraMap ℚ Ω) r).symm
    calc
      (↑((r : K) * x) : Ω) * y =
          ((↑(r : K) : Ω) * (x : Ω)) * y := rfl
      _ = (algebraMap ℚ Ω r * (x : Ω)) * y := by rw [hr]
      _ = algebraMap ℚ Ω r * ((x : Ω) * y) := mul_assoc _ _ _
  let F := IntermediateField.adjoin ℚ (Set.range beta)
  let L := IntermediateField.adjoin K (Set.range beta)
  have hpowQ : ∀ x ∈ Set.range beta,
      x ^ q ∈ (⊥ : IntermediateField ℚ Ω) := by
    rintro x ⟨i, rfl⟩
    rw [hbeta i]
    exact (IntermediateField.mem_bot).2 ⟨(p i : ℚ), rfl⟩
  letI : FiniteDimensional ℚ F :=
    dimensional_adjoin_pow q (NeZero.pos q) (Set.range beta)
      (Set.finite_range beta) hpowQ
  have hpowK : ∀ x ∈ Set.range beta,
      x ^ q ∈ (⊥ : IntermediateField K Ω) := by
    rintro x ⟨i, rfl⟩
    rw [hbeta i]
    exact (IntermediateField.mem_bot).2
      ⟨algebraMap ℚ K (p i : ℚ), by simp [IsScalarTower.algebraMap_apply]⟩
  letI : FiniteDimensional K L :=
    dimensional_adjoin_pow q (NeZero.pos q) (Set.range beta)
      (Set.finite_range beta) hpowK
  have hKL : Module.finrank K L = q ^ Fintype.card ι :=
    finrank_adjoin_prime_radicals hroots hcop' p hp hinj beta hbeta
  have hcomp : L.restrictScalars ℚ = K ⊔ F :=
    IntermediateField.restrictScalars_adjoin_eq_sup ℚ K (Set.range beta)
  have hsuple : Module.finrank ℚ (L.restrictScalars ℚ) ≤
      Module.finrank ℚ K * Module.finrank ℚ F := by
    rw [hcomp]
    exact IntermediateField.finrank_sup_le K F
  have hmul : Module.finrank ℚ K * (q ^ Fintype.card ι) ≤
      Module.finrank ℚ K * Module.finrank ℚ F := by
    rw [← hKL, Module.finrank_mul_finrank ℚ K L]
    exact hsuple
  have hlower : q ^ Fintype.card ι ≤ Module.finrank ℚ F :=
    le_of_mul_le_mul_left hmul Module.finrank_pos
  let roots : Finset Ω := Finset.univ.image beta
  have hpow' : ∀ x ∈ roots,
      x ^ q ∈ (⊥ : IntermediateField ℚ Ω) := by
    intro x hx
    simp only [roots, Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hpowQ (beta i) ⟨i, rfl⟩
  have hupper' := finrank_adjoin_finset q (NeZero.pos q) roots hpow'
  have hroots_set : (roots : Set Ω) = Set.range beta := by
    ext x
    simp [roots]
  rw [hroots_set] at hupper'
  have hcard : roots.card ≤ Fintype.card ι :=
    (Finset.card_image_le :
      (Finset.univ.image beta).card ≤ (Finset.univ : Finset ι).card)
  have hupper : Module.finrank ℚ F ≤ q ^ Fintype.card ι :=
    hupper'.trans (Nat.pow_le_pow_right (NeZero.pos q) hcard)
  exact le_antisymm hupper hlower

/-- Distinct rational primes have independent thirteenth roots: adjoining any
choice of those roots to `ℚ` has the maximal possible degree. -/
theorem finrank_adjoin_thirteenthRoots_primes_rat
    {ι : Type*} {Ω : Type u} [Fintype ι] [DecidableEq ι]
    [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (beta : ι → Ω)
    (hbeta : ∀ i, beta i ^ 13 = algebraMap ℚ Ω (p i : ℚ)) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ (Set.range beta)) =
      13 ^ Fintype.card ι := by
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  letI : IsSepClosed Ω := IsSepClosed.of_isAlgClosed Ω
  letI : CharZero Ω :=
    charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  letI : NeZero (13 : Ω) := ⟨Nat.cast_ne_zero.mpr (by norm_num)⟩
  obtain ⟨zeta, hzeta⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω 13
  let K := IntermediateField.adjoin ℚ ({zeta} : Set Ω)
  let oldAlgebra : Algebra ℚ K := IntermediateField.algebra' K
  have hcyclotomicOld :
      @IsCyclotomicExtension {13} ℚ K _ _ oldAlgebra := by
    letI : Algebra ℚ K := oldAlgebra
    exact hzeta.intermediateField_adjoin_isCyclotomicExtension ℚ
  let canonicalAlgebra : Algebra ℚ K := DivisionRing.toRatAlgebra
  have hAlgebra : oldAlgebra = canonicalAlgebra :=
    Subsingleton.elim _ _
  have hcyclotomic :
      @IsCyclotomicExtension {13} ℚ K _ _ canonicalAlgebra :=
    hAlgebra ▸ hcyclotomicOld
  letI : Algebra ℚ K := canonicalAlgebra
  letI : IsCyclotomicExtension {13} ℚ K := hcyclotomic
  letI : NumberField K := IsCyclotomicExtension.numberField {13} ℚ K
  have hroots : (primitiveRoots 13 K).Nonempty :=
    ⟨IsCyclotomicExtension.zeta 13 ℚ K,
      (mem_primitiveRoots (by norm_num)).2
        (IsCyclotomicExtension.zeta_spec 13 ℚ K)⟩
  have hfinCanonical :
      @Module.finrank ℚ K _ _ Algebra.toModule = 12 := by
    rw [IsCyclotomicExtension.Rat.finrank 13 K, Nat.totient_prime]
    · norm_num
  have hModule : (Algebra.toModule : Module ℚ K) = K.module' :=
    Subsingleton.elim _ _
  have hfdCanonical :
      @FiniteDimensional ℚ K _ _ Algebra.toModule :=
    NumberField.to_finiteDimensional
  have hfdIntermediate : @FiniteDimensional ℚ K _ _ K.module' := by
    rw [← hModule]
    exact hfdCanonical
  letI : @FiniteDimensional ℚ K _ _ K.module' := hfdIntermediate
  have hfin : Module.finrank ℚ K = 12 := by
    rw [← hModule]
    exact hfinCanonical
  have hcop : (13).Coprime (Module.finrank ℚ K) := by
    rw [hfin]
    norm_num
  exact finrank_adjoin_prime_radicals_rat K hroots hcop p hp hinj beta hbeta

end Erdos240.Kummer
