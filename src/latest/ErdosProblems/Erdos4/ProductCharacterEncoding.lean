import ErdosProblems.Erdos4.ProductFourierInversion
import ErdosProblems.Erdos4.PrimitiveCharacterFamily
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Group.Pi.Units

/-!
# Encoding product characters by their primitive conductors

All local characters are lifted to their common product level. The CRT
makes this map injective. Passing to each character's canonical primitive
character remains injective because lifting back recovers the original
character. Thus no imprimitive multiplicities are introduced.
-/

open scoped BigOperators

namespace Erdos4.ProductCharacterEncoding

variable {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) [∀ p, Fact (ell p).Prime]

abbrev modulus : ℕ := ∏ p, ell p

theorem local_dvd_modulus (p : P) : ell p ∣ modulus ell :=
  Finset.dvd_prod_of_mem ell (Finset.mem_univ p)

noncomputable def character (chi : ∀ p, DirichletCharacter ℂ (ell p)) :
    DirichletCharacter ℂ (modulus ell) :=
  ∏ p, DirichletCharacter.changeLevel (local_dvd_modulus ell p) (chi p)

theorem prod_apply_unit {n : ℕ} {I : Type*} (S : Finset I)
    (chi : I → DirichletCharacter ℂ n) (u : (ZMod n)ˣ) :
    (∏ i ∈ S, chi i) (u : ZMod n) = ∏ i ∈ S, chi i (u : ZMod n) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, MulChar.mul_apply, ih]

theorem character_apply_unit (chi : ∀ p, DirichletCharacter ℂ (ell p))
    (u : (ZMod (modulus ell))ˣ) :
    character ell chi (u : ZMod (modulus ell)) =
      ProductFourierInversion.value ell chi (fun p => ZMod.unitsMap (local_dvd_modulus ell p) u) := by
  unfold character ProductFourierInversion.value
  rw [prod_apply_unit]
  apply Finset.prod_congr rfl
  intro p _hp
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, ZMod.unitsMap_val]

theorem exists_unit_lift
    (hcop : Pairwise (fun p q => (ell p).Coprime (ell q)))
    (v : ∀ p, (ZMod (ell p))ˣ) :
    ∃ u : (ZMod (modulus ell))ˣ, ∀ p,
      ZMod.unitsMap (local_dvd_modulus ell p) u = v p := by
  let e := ZMod.prodEquivPi ell hcop
  let u : (ZMod (modulus ell))ˣ :=
    Units.map e.symm.toMonoidHom (MulEquiv.piUnits.symm v)
  refine ⟨u, ?_⟩
  have hval : e (u : ZMod (modulus ell)) = fun p => (v p : ZMod (ell p)) := by
    change e (e.symm (fun p => (v p : ZMod (ell p)))) = _
    exact e.apply_symm_apply _
  intro p
  apply Units.ext
  have hh := congrFun hval p
  rw [ZMod.unitsMap_val]
  change (ZMod.prodEquivPi ell hcop) u.val p = (v p : ZMod (ell p)) at hh
  rw [ZMod.prodEquivPi_apply, ZMod.castHom_apply] at hh
  exact hh

theorem value_update (chi : ∀ p, DirichletCharacter ℂ (ell p))
    (p : P) (u : (ZMod (ell p))ˣ) :
    ProductFourierInversion.value ell chi (Function.update (fun q => (1 : (ZMod (ell q))ˣ)) p u) =
      chi p (u : ZMod (ell p)) := by
  classical
  unfold ProductFourierInversion.value
  rw [Finset.prod_eq_single p]
  · simp
  · intro q _hq hqp
    simp [Function.update_of_ne hqp]
  · simp

theorem character_injective
    (hcop : Pairwise (fun p q => (ell p).Coprime (ell q))) :
    Function.Injective (character ell) := by
  intro chi psi heq
  have hvalue : ∀ v : ∀ p, (ZMod (ell p))ˣ,
      ProductFourierInversion.value ell chi v = ProductFourierInversion.value ell psi v := by
    intro v
    obtain ⟨u, hu⟩ := exists_unit_lift ell hcop v
    have hh := congrArg (fun c : DirichletCharacter ℂ (modulus ell) => c (u : ZMod (modulus ell))) heq
    rw [character_apply_unit, character_apply_unit] at hh
    have hu' : (fun p => ZMod.unitsMap (local_dvd_modulus ell p) u) = v := funext hu
    simpa only [hu'] using hh
  funext p
  apply MulChar.ext
  intro u
  have hh := hvalue (Function.update (fun q => (1 : (ZMod (ell q))ˣ)) p u)
  simpa only [value_update] using hh

noncomputable def entry (chi : ∀ p, DirichletCharacter ℂ (ell p)) :
    PrimitiveCharacterFamily.Entry :=
  ⟨(character ell chi).conductor, (character ell chi).primitiveCharacter⟩

noncomputable def liftEntry (N : ℕ) (c : PrimitiveCharacterFamily.Entry) :
    DirichletCharacter ℂ N :=
  if h : c.1 ∣ N then DirichletCharacter.changeLevel h c.2 else 1

theorem liftEntry_entry (chi : ∀ p, DirichletCharacter ℂ (ell p)) :
    liftEntry (modulus ell) (entry ell chi) = character ell chi := by
  unfold liftEntry entry
  rw [dif_pos (character ell chi).conductor_dvd_level,
    DirichletCharacter.changeLevel_primitiveCharacter]

theorem entry_injective (hcop : Pairwise (fun p q => (ell p).Coprime (ell q))) :
    Function.Injective (entry ell) := by
  intro chi psi heq
  apply character_injective ell hcop
  have hh := congrArg (liftEntry (modulus ell)) heq
  simpa only [liftEntry_entry] using hh

theorem entry_valid (hpos : ∀ p, 0 < ell p)
    (chi : ∀ p, DirichletCharacter ℂ (ell p)) : PrimitiveCharacterFamily.Valid (entry ell chi) := by
  have hmod : 0 < modulus ell := Finset.prod_pos (fun p _hp => hpos p)
  let : NeZero (modulus ell) := ⟨hmod.ne'⟩
  exact ⟨(character ell chi).conductor_ne_zero.bot_lt,
    (character ell chi).primitiveCharacter_isPrimitive⟩

theorem pairwise_coprime_of_prime (hprime : ∀ p, (ell p).Prime)
    (hinj : Function.Injective ell) : Pairwise (fun p q => (ell p).Coprime (ell q)) := by
  intro p q hpq
  exact (Nat.coprime_primes (hprime p) (hprime q)).mpr (fun h => hpq (hinj h))

theorem conductor_dvd_support (chi : ∀ p, DirichletCharacter ℂ (ell p))
    (S : Finset P) (houtside : ∀ p, p ∉ S → chi p = 1) :
    (entry ell chi).1 ∣ ∏ p ∈ S, ell p := by
  have hmod : 0 < modulus ell := Finset.prod_pos
    (fun p _hp => (Fact.out : (ell p).Prime).pos)
  let : NeZero (modulus ell) := ⟨hmod.ne'⟩
  have hdiv : (∏ p ∈ S, ell p) ∣ modulus ell :=
    Finset.prod_dvd_prod_of_subset S Finset.univ ell (Finset.subset_univ S)
  have hfactor : (character ell chi).FactorsThrough (∏ p ∈ S, ell p) := by
    apply (DirichletCharacter.factorsThrough_iff_ker_unitsMap hdiv).mpr
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    apply Units.ext
    change character ell chi (u : ZMod (modulus ell)) = (1 : ℂ)
    rw [character_apply_unit]
    unfold ProductFourierInversion.value
    apply Finset.prod_eq_one
    intro p _hp
    change chi p ((ZMod.unitsMap (local_dvd_modulus ell p) u) : ZMod (ell p)) = 1
    by_cases hpS : p ∈ S
    · have hlocal : ell p ∣ ∏ q ∈ S, ell q := Finset.dvd_prod_of_mem ell hpS
      have hmap : ZMod.unitsMap (local_dvd_modulus ell p) u =
          ZMod.unitsMap hlocal (ZMod.unitsMap hdiv u) := by
        rw [← MonoidHom.comp_apply, ZMod.unitsMap_comp]
      rw [hmap, hu, map_one, Units.val_one, map_one]
    · rw [houtside p hpS]
      exact MulChar.one_apply_coe _
  exact (character ell chi).conductor_dvd_of_mem_conductorSet hfactor

theorem conductor_le_support (chi : ∀ p, DirichletCharacter ℂ (ell p))
    (S : Finset P) (houtside : ∀ p, p ∉ S → chi p = 1) :
    (entry ell chi).1 ≤ ∏ p ∈ S, ell p :=
  Nat.le_of_dvd (Finset.prod_pos (fun p _hp => (Fact.out : (ell p).Prime).pos))
    (conductor_dvd_support ell chi S houtside)

theorem entry_value_eq_product (chi : ∀ p, DirichletCharacter ℂ (ell p))
    (n : ℕ) (hn : n.Coprime (modulus ell)) :
    PrimitiveCharacterFamily.value (entry ell chi) n =
      ∏ p, chi p (n : ZMod (ell p)) := by
  have hprim := (character ell chi).primitiveCharacter_apply_of_isCoprime hn.isCoprime
  have hchar : character ell chi (n : ZMod (modulus ell)) =
      ∏ p, chi p (n : ZMod (ell p)) := by
    rw [← ZMod.coe_unitOfCoprime n hn, character_apply_unit]
    unfold ProductFourierInversion.value
    apply Finset.prod_congr rfl
    intro p _hp
    rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.cast_natCast (local_dvd_modulus ell p)]
  change (character ell chi).primitiveCharacter (n : ZMod (character ell chi).conductor) = _
  have hp : (character ell chi).primitiveCharacter (n : ZMod (character ell chi).conductor) =
      character ell chi (n : ZMod (modulus ell)) := by
    simpa only [Int.cast_natCast] using hprim
  exact hp.trans hchar

end Erdos4.ProductCharacterEncoding
