/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026.
Released under Apache 2.0 license.
-/

import ErdosProblems.Erdos438.LOSCover
import ErdosProblems.Erdos587.Hensel

/-!
# The odd part of the Lagarias--Odlyzko--Shearer cover

This file constructs the uniform cover of the square-sum relation modulo an
odd integer by (possibly collapsed) triangles.  Loops are retained throughout:
the source relation is `K3Rel`, while the target is the looped relation
`SquareSumRel` from `LOSCover`.
-/

open scoped BigOperators

namespace Erdos438

/-! ## A universal parametrization of square-sum triangles -/

theorem squareSumRel_iff_isSquare {m : ℕ} {x y : ZMod m} :
    SquareSumRel m x y ↔ IsSquare (x + y) := by
  simp [SquareSumRel, isSquare_iff_exists_sq, eq_comm]

/-- The elementary two-parameter square-sum triangle

`(-rs, r(r+s), s(r+s))`.

Its three edge sums are respectively `r^2`, `s^2`, and `(r+s)^2`.
-/
def parameterTriangle {R : Type*} [CommRing R] (r s : R) : Fin 3 → R
  | 0 => -r * s
  | 1 => r * (r + s)
  | 2 => s * (r + s)

@[simp] theorem parameterTriangle_zero {R : Type*} [CommRing R] (r s : R) :
    parameterTriangle r s 0 = -r * s := rfl

@[simp] theorem parameterTriangle_one {R : Type*} [CommRing R] (r s : R) :
    parameterTriangle r s 1 = r * (r + s) := rfl

@[simp] theorem parameterTriangle_two {R : Type*} [CommRing R] (r s : R) :
    parameterTriangle r s 2 = s * (r + s) := rfl

theorem parameterTriangle_isRelHom {R : Type*} [CommRing R] (r s : R) :
    RelHom K3Rel (fun x y : R => IsSquare (x + y)) (parameterTriangle r s) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [K3Rel, parameterTriangle]
  · exact ⟨r, by ring⟩
  · exact ⟨s, by ring⟩
  · exact ⟨r, by ring⟩
  · exact ⟨r + s, by ring⟩
  · exact ⟨s, by ring⟩
  · exact ⟨r + s, by ring⟩

theorem parameterTriangle_zmod_isRelHom (q : ℕ) [NeZero q]
    (r s : ZMod q) :
    RelHom K3Rel (SquareSumRel q) (parameterTriangle r s) := by
  intro i j hij
  rcases parameterTriangle_isRelHom r s hij with ⟨z, hz⟩
  exact ⟨z, by simpa [pow_two] using hz.symm⟩

/-- A triangle with two opposite vertices. -/
def oppositeTriangle (m : ℕ) (u z : ZMod m) : Fin 3 → ZMod m
  | 0 => u
  | 1 => -u
  | 2 => z

theorem oppositeTriangle_isRelHom {m : ℕ} {u z : ZMod m}
    (hplus : IsSquare (z + u)) (hminus : IsSquare (z - u)) :
    RelHom K3Rel (SquareSumRel m) (oppositeTriangle m u z) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals simp only [K3Rel, Fin.zero_eta, Fin.isValue, ne_eq,
    not_true_eq_false] at hij
  · exact ⟨0, by simp [oppositeTriangle]⟩
  · exact squareSumRel_iff_isSquare.mpr
      (by simpa [oppositeTriangle, add_comm] using hplus)
  · exact ⟨0, by simp [oppositeTriangle]⟩
  · exact squareSumRel_iff_isSquare.mpr
      (by simpa [oppositeTriangle, sub_eq_add_neg, add_comm] using hminus)
  · exact squareSumRel_iff_isSquare.mpr
      (by simpa [oppositeTriangle] using hplus)
  · exact squareSumRel_iff_isSquare.mpr
      (by simpa [oppositeTriangle, sub_eq_add_neg, add_comm] using hminus)

theorem const_isRelHom_of_isSquare_two_mul {m : ℕ} {v : ZMod m}
    (hv : IsSquare (2 * v)) :
    RelHom K3Rel (SquareSumRel m) (fun _ : Fin 3 => v) := by
  intro i j hij
  exact squareSumRel_iff_isSquare.mpr (by simpa [two_mul] using hv)

/-! ## Nonsingular square lifting -/

/-- Reduction from a positive prime power to its residue field. -/
noncomputable def primePowerReduction (p k : ℕ) (hk : 0 < k) :
    ZMod (p ^ k) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p)

/-- A unit residue modulo an odd prime power is a square as soon as its
reduction modulo the prime is a nonzero square.  This is the elementary
nonsingular Hensel step, iterated through the exponent. -/
theorem isSquare_primePower_of_reduction
    {p k : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) (hk : 0 < k)
    (x : ZMod (p ^ k))
    (hx0 : primePowerReduction p k hk x ≠ 0)
    (hxsq : IsSquare (primePowerReduction p k hk x)) :
    IsSquare x := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hredval :
      primePowerReduction p k hk x = (x.val : ZMod p) := by
    unfold primePowerReduction
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  have hpndvd : ¬p ∣ x.val := by
    intro hdiv
    apply hx0
    rw [hredval]
    exact (ZMod.natCast_eq_zero_iff x.val p).2 hdiv
  have hcopNat : x.val.Coprime p := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    exact hpndvd
  have hcopInt : IsCoprime (x.val : ℤ) (p : ℤ) := hcopNat.isCoprime
  rcases hxsq with ⟨z, hz⟩
  have hzmod : (x.val : ℤ) ≡ (z.val : ℤ) ^ 2 [ZMOD (p : ℤ)] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    rw [← hredval, hz, ZMod.natCast_zmod_val]
    simp [pow_two]
  obtain ⟨z', hz'⟩ :=
    Erdos587.exists_square_modEq_primePower_of_odd_prime hp hpodd hk hcopInt hzmod
  refine ⟨(z' : ZMod (p ^ k)), ?_⟩
  rw [← ZMod.natCast_zmod_val x]
  have heq :
      ((x.val : ℤ) : ZMod (p ^ k)) = ((z' ^ 2 : ℤ) : ZMod (p ^ k)) :=
    (ZMod.intCast_eq_intCast_iff _ _ _).2 hz'
  push_cast at heq
  simpa [pow_two] using heq

/-- Every fiber of a surjective homomorphism of finite additive groups has
cardinality `|A| / |B|`.  This small counting lemma is used repeatedly for
prime-power reduction. -/
theorem card_fiber_surjective_addMonoidHom
    {A B : Type*} [AddGroup A] [AddGroup B]
    [Fintype A] [Fintype B] [DecidableEq B]
    (f : A →+ B) (hf : Function.Surjective f) (b : B) :
    ((Finset.univ : Finset A).filter fun a => f a = b).card =
      Fintype.card A / Fintype.card B := by
  classical
  have htotal := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset A)) (t := (Finset.univ : Finset B))
    (f := f) (by simp [hf])
  have heq : ∀ y : B,
      ((Finset.univ : Finset A).filter fun a => f a = y).card =
        ((Finset.univ : Finset A).filter fun a => f a = b).card := by
    intro y
    exact AddMonoidHom.card_fiber_eq_of_mem_range f (hf y) (hf b)
  have hmul : Fintype.card B *
      ((Finset.univ : Finset A).filter fun a => f a = b).card =
        Fintype.card A := by
    calc
      Fintype.card B *
          ((Finset.univ : Finset A).filter fun a => f a = b).card =
          ∑ _y : B,
            ((Finset.univ : Finset A).filter fun a => f a = b).card := by simp
      _ = ∑ y : B,
            ((Finset.univ : Finset A).filter fun a => f a = y).card := by
          apply Finset.sum_congr rfl
          intro y hy
          exact (heq y).symm
      _ = Fintype.card A := htotal.symm
  exact Nat.eq_div_of_mul_eq_right Fintype.card_pos.ne' hmul

theorem card_primePowerReduction_fiber
    {p k : ℕ} [NeZero (p ^ k)] (hp : p.Prime) (hk : 0 < k) (a : ZMod p) :
    ((Finset.univ : Finset (ZMod (p ^ k))).filter fun x =>
      primePowerReduction p k hk x = a).card = p ^ (k - 1) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  change ((Finset.univ : Finset (ZMod (p ^ k))).filter fun x =>
      (primePowerReduction p k hk).toAddMonoidHom x = a).card = _
  rw [card_fiber_surjective_addMonoidHom
    (primePowerReduction p k hk).toAddMonoidHom
    (ZMod.castHom_surjective (dvd_pow_self p hk.ne')) a]
  simp only [ZMod.card]
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [pow_succ']
  exact Nat.mul_div_cancel_left _ hp.pos

/-! Square classes of prime-power units are detected in the residue field. -/

theorem primePowerReduction_ne_zero_iff_isUnit
    {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (x : ZMod (p ^ k)) :
    primePowerReduction p k hk x ≠ 0 ↔ IsUnit x := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hredval :
      primePowerReduction p k hk x = (x.val : ZMod p) := by
    unfold primePowerReduction
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  constructor
  · intro hne
    rw [← ZMod.natCast_zmod_val x,
      ZMod.isUnit_natCast_iff_not_dvd_pow hp hk]
    intro hdiv
    apply hne
    rw [hredval]
    exact (ZMod.natCast_eq_zero_iff x.val p).2 hdiv
  · intro hunit hzero
    have hnotdiv : ¬p ∣ x.val := by
      rw [← ZMod.natCast_zmod_val x] at hunit
      exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp hk).1 hunit
    apply hnotdiv
    rw [hredval] at hzero
    exact (ZMod.natCast_eq_zero_iff x.val p).1 hzero

theorem isSquare_unit_iff_coe {R : Type*} [CommRing R] (x : Rˣ) :
    IsSquare x ↔ IsSquare (x : R) := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(y : R), ?_⟩
    exact congrArg Units.val hy
  · rintro ⟨y, hy⟩
    have hyu : IsUnit y := by
      have hprod : IsUnit (y * y) := by
        rw [← hy]
        exact x.isUnit
      exact isUnit_of_mul_isUnit_left hprod
    refine ⟨hyu.unit, ?_⟩
    apply Units.ext
    simpa [IsUnit.unit_spec] using hy

theorem isSquare_primePower_unit_iff_reduction
    {p k : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) (hk : 0 < k)
    (x : (ZMod (p ^ k))ˣ) :
    IsSquare x ↔ IsSquare (primePowerReduction p k hk (x : ZMod (p ^ k))) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [isSquare_unit_iff_coe]
  constructor
  · exact fun h => h.map (primePowerReduction p k hk).toMonoidHom
  · intro h
    apply isSquare_primePower_of_reduction hp hpodd hk _ _ h
    exact (primePowerReduction_ne_zero_iff_isUnit hp hk _).2 x.isUnit

theorem isSquare_mul_iff_square_iff_square_finiteField
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hodd : ringChar F ≠ 2) {a b : F} (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    IsSquare (a * b) ↔ (IsSquare a ↔ IsSquare b) := by
  by_cases ha : IsSquare a <;> by_cases hb : IsSquare b
  · exact ⟨fun _ => ⟨fun _ => hb, fun _ => ha⟩, fun _ => ha.mul hb⟩
  · constructor
    · intro hab
      exfalso
      apply hb
      have hs := hab.mul ha.inv
      rw [mul_assoc, mul_comm b, ← mul_assoc, mul_inv_cancel₀ ha0, one_mul] at hs
      exact hs
    · intro hiff
      exact (hb (hiff.mp ha)).elim
  · constructor
    · intro hab
      exfalso
      apply ha
      have hs := hab.mul hb.inv
      simpa [mul_assoc, mul_comm, mul_left_comm, hb0] using hs
    · intro hiff
      exact (ha (hiff.mpr hb)).elim
  · simp only [ha, hb, iff_self]
    rw [← quadraticChar_one_iff_isSquare (mul_ne_zero ha0 hb0), map_mul,
      quadraticChar_neg_one_iff_not_isSquare.mpr ha,
      quadraticChar_neg_one_iff_not_isSquare.mpr hb]
    norm_num

theorem isSquare_mul_iff_square_iff_square_primePowerUnits
    {p k : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) (hk : 0 < k)
    (a b : (ZMod (p ^ k))ˣ) :
    IsSquare (a * b) ↔ (IsSquare a ↔ IsSquare b) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  simp_rw [isSquare_primePower_unit_iff_reduction hp hpodd hk]
  simp only [Units.val_mul]
  rw [map_mul]
  apply isSquare_mul_iff_square_iff_square_finiteField
    ((ZMod.ringChar_zmod_n p).substr hpodd)
  · exact (primePowerReduction_ne_zero_iff_isUnit hp hk _).2 a.isUnit
  · exact (primePowerReduction_ne_zero_iff_isUnit hp hk _).2 b.isUnit

/-- In a finite prime field of odd characteristic, some nonzero square becomes
a nonsquare after adding one.  A short induction through the standard
representatives avoids any character-sum calculation. -/
theorem exists_square_add_one_nonsquare
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    ∃ a : ZMod p, a ≠ 0 ∧ IsSquare a ∧ ¬IsSquare (1 + a) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := FiniteField.exists_nonsquare
    ((ZMod.ringChar_zmod_n p).substr hpodd)
  by_contra hnone
  have hstep : ∀ a : ZMod p, a ≠ 0 → IsSquare a → IsSquare (1 + a) := by
    intro a ha hsa
    by_contra hnext
    exact hnone ⟨a, ha, hsa, hnext⟩
  have hall : ∀ n : ℕ, n < p → IsSquare (n : ZMod p) := by
    intro n hn
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
        by_cases hn0 : n = 0
        · subst n
          exact ⟨1, by simp⟩
        · have hnlt : n < p := lt_trans (Nat.lt_succ_self n) hn
          have hncast : (n : ZMod p) ≠ 0 := by
            intro hz
            have hdvd : p ∣ n := (ZMod.natCast_eq_zero_iff n p).1 hz
            exact (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hn0) hnlt) hdvd
          simpa [Nat.cast_succ, add_comm] using hstep (n : ZMod p) hncast (ih hnlt)
  apply hx
  rw [← ZMod.natCast_zmod_val x]
  exact hall x.val x.val_lt

/-! ## Labelwise uniform covers -/

section Rooted

variable {V : Type*} [Fintype V] [DecidableEq V]

def rootedMultiplicity (F : Multiset (Fin 3 → V)) (i : Fin 3) (x : V) : ℕ :=
  (F.filter fun f => f i = x).card

def RootUniform (F : Multiset (Fin 3 → V)) (d : ℕ) : Prop :=
  ∀ i x, rootedMultiplicity F i x = d

theorem fiberCard_eq_sum_rootIndicator (f : Fin 3 → V) (x : V) :
    fiberCard f x = ∑ i : Fin 3, if f i = x then 1 else 0 := by
  unfold fiberCard
  rw [Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter]

theorem coverMultiplicity_eq_sum_rootedMultiplicity
    (F : Multiset (Fin 3 → V)) (x : V) :
    coverMultiplicity F x = ∑ i : Fin 3, rootedMultiplicity F i x := by
  classical
  induction F using Multiset.induction_on with
  | empty => simp [coverMultiplicity, rootedMultiplicity]
  | @cons f F ih =>
      simp only [coverMultiplicity, Multiset.map_cons, Multiset.sum_cons]
      change fiberCard f x + coverMultiplicity F x = _
      rw [ih]
      rw [fiberCard_eq_sum_rootIndicator, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : f i = x <;> simp [rootedMultiplicity, h] <;> omega

theorem RootUniform.uniformCover {F : Multiset (Fin 3 → V)} {d : ℕ}
    (hF : RootUniform F d) : UniformCover F (3 * d) := by
  intro x
  rw [coverMultiplicity_eq_sum_rootedMultiplicity]
  apply (Finset.sum_congr rfl fun i _ => hF i x).trans
  rw [Finset.sum_const]
  change Fintype.card (Fin 3) * d = 3 * d
  rfl

end Rooted

/-! ## The primitive parameter family over a prime power -/

noncomputable section

attribute [local instance] Classical.propDecidable

section BroadGeneric

variable (R : Type*) [CommRing R]

abbrev leftProductSolutions (x : R) :=
  {p : R × R // IsUnit p.1 ∧ -p.1 * p.2 = x}

abbrev rightProductSolutions (x : R) :=
  {p : R × R // IsUnit p.2 ∧ -p.1 * p.2 = x}

abbrev broadProductSolutions (x : R) :=
  {p : R × R // (IsUnit p.1 ∨ IsUnit p.2) ∧ -p.1 * p.2 = x}

noncomputable def leftProductEquiv (x : R) :
    Rˣ ≃ leftProductSolutions R x where
  toFun u := ⟨((u : R), -(↑(u⁻¹) : R) * x), u.isUnit, by simp⟩
  invFun p := p.property.1.unit
  left_inv u := by
    apply Units.ext
    simp [IsUnit.unit_spec]
  right_inv := by
    rintro ⟨⟨a, b⟩, ha, hab⟩
    apply Subtype.ext
    apply Prod.ext
    · simp [IsUnit.unit_spec]
    · change -(↑(ha.unit⁻¹) : R) * x = b
      apply_fun (fun y => a * y) using ha.mul_right_injective
      have hmul : a * (↑(ha.unit⁻¹) : R) = 1 := by
        simpa [IsUnit.unit_spec] using congrArg Units.val ha.unit.mul_inv
      calc
        a * (-((↑(ha.unit⁻¹) : R)) * x) =
            -(a * (↑(ha.unit⁻¹) : R)) * x := by ring
        _ = -x := by rw [hmul]; simp
        _ = a * b := by rw [← hab]; ring

noncomputable def rightProductEquiv (x : R) :
    Rˣ ≃ rightProductSolutions R x where
  toFun u := ⟨(-(↑(u⁻¹) : R) * x, (u : R)), u.isUnit, by
    simp [mul_assoc, mul_comm, mul_left_comm]⟩
  invFun p := p.property.1.unit
  left_inv u := by
    apply Units.ext
    simp [IsUnit.unit_spec]
  right_inv := by
    rintro ⟨⟨a, b⟩, hb, hab⟩
    apply Subtype.ext
    apply Prod.ext
    · change -(↑(hb.unit⁻¹) : R) * x = a
      apply_fun (fun y => y * b) using hb.mul_left_injective
      calc
        (-((↑(hb.unit⁻¹) : R)) * x) * b = -x := by
          rw [mul_assoc, mul_comm x b, ← mul_assoc]
          simp [IsUnit.unit_spec]
        _ = a * b := by rw [← hab]; ring
    · simp [IsUnit.unit_spec]

noncomputable def leftEquivBroadOfUnit (x : R) (hx : IsUnit x) :
    leftProductSolutions R x ≃ broadProductSolutions R x where
  toFun p := ⟨p.1, Or.inl p.property.1, p.property.2⟩
  invFun := by
    rintro ⟨⟨a, b⟩, habu, hab⟩
    refine ⟨(a, b), ?_, hab⟩
    have hp : IsUnit (-a * b) := hab.symm ▸ hx
    have hp' : IsUnit (-(a * b)) := by simpa only [neg_mul] using hp
    exact isUnit_of_mul_isUnit_left ((IsUnit.neg_iff _).mp hp')
  left_inv p := rfl
  right_inv := by
    rintro ⟨⟨a, b⟩, habu, hab⟩
    apply Subtype.ext
    rfl

noncomputable def sumEquivBroadOfNotUnit (x : R) (hx : ¬IsUnit x) :
    Sum (leftProductSolutions R x) (rightProductSolutions R x) ≃
      broadProductSolutions R x where
  toFun
    | Sum.inl p => ⟨p.1, Or.inl p.property.1, p.property.2⟩
    | Sum.inr p => ⟨p.1, Or.inr p.property.1, p.property.2⟩
  invFun := by
    rintro ⟨⟨a, b⟩, habu, hab⟩
    classical
    by_cases ha : IsUnit a
    · exact Sum.inl ⟨(a, b), ha, hab⟩
    · exact Sum.inr ⟨(a, b), habu.resolve_left ha, hab⟩
  left_inv := by
    rintro (p | p)
    · classical
      rcases p with ⟨⟨a, b⟩, ha, hab⟩
      simp only
      split
      · exact congrArg Sum.inl (Subtype.ext rfl)
      · rename_i hna
        exact (hna ha).elim
    · classical
      rcases p with ⟨⟨a, b⟩, hb, hab⟩
      simp only
      split
      · rename_i hunit
        exfalso
        apply hx
        rw [← hab]
        exact hunit.neg.mul hb
      · exact congrArg Sum.inr (Subtype.ext rfl)
  right_inv := by
    rintro ⟨⟨a, b⟩, habu, hab⟩
    apply Subtype.ext
    classical
    by_cases ha : IsUnit a <;> simp [ha]

theorem card_broadProductSolutions [Fintype R] [DecidableEq R] (x : R) :
    Fintype.card (broadProductSolutions R x) =
      if IsUnit x then Fintype.card Rˣ else 2 * Fintype.card Rˣ := by
  classical
  by_cases hx : IsUnit x
  · rw [if_pos hx]
    calc
      Fintype.card (broadProductSolutions R x) =
          Fintype.card (leftProductSolutions R x) :=
        Fintype.card_congr (leftEquivBroadOfUnit R x hx).symm
      _ = Fintype.card Rˣ :=
        Fintype.card_congr (leftProductEquiv R x).symm
  · rw [if_neg hx]
    calc
      Fintype.card (broadProductSolutions R x) =
          Fintype.card (Sum (leftProductSolutions R x) (rightProductSolutions R x)) :=
        Fintype.card_congr (sumEquivBroadOfNotUnit R x hx).symm
      _ = Fintype.card (leftProductSolutions R x) +
          Fintype.card (rightProductSolutions R x) := Fintype.card_sum
      _ = Fintype.card Rˣ + Fintype.card Rˣ := by
        rw [Fintype.card_congr (leftProductEquiv R x).symm,
          Fintype.card_congr (rightProductEquiv R x).symm]
      _ = 2 * Fintype.card Rˣ := by omega

end BroadGeneric

section BroadPrimePower

noncomputable def broadParams (p k : ℕ) [NeZero (p ^ k)] (hk : 0 < k) :
    Finset (ZMod (p ^ k) × ZMod (p ^ k)) :=
  Finset.univ.filter fun rs =>
    primePowerReduction p k hk rs.1 ≠ 0 ∨
      primePowerReduction p k hk rs.2 ≠ 0

noncomputable def broadFamily (p k : ℕ) [NeZero (p ^ k)] (hk : 0 < k) :
    Multiset (Fin 3 → ZMod (p ^ k)) :=
  (broadParams p k hk).val.map fun rs => parameterTriangle rs.1 rs.2

abbrev broadLabelSolutions (p k : ℕ) (hk : 0 < k)
    (i : Fin 3) (x : ZMod (p ^ k)) :=
  {rs : ZMod (p ^ k) × ZMod (p ^ k) //
    (primePowerReduction p k hk rs.1 ≠ 0 ∨
      primePowerReduction p k hk rs.2 ≠ 0) ∧
    parameterTriangle rs.1 rs.2 i = x}

theorem broadFamily_isRelCover
    {p k : ℕ} [NeZero (p ^ k)] (hk : 0 < k) :
    IsRelCover K3Rel (SquareSumRel (p ^ k)) (broadFamily p k hk) := by
  intro f hf
  simp only [broadFamily, Multiset.mem_map] at hf
  obtain ⟨rs, hrs, rfl⟩ := hf
  exact parameterTriangle_zmod_isRelHom _ rs.1 rs.2

theorem broadFamily_rootedMultiplicity_eq_card
    {p k : ℕ} [NeZero (p ^ k)] (hk : 0 < k)
    (i : Fin 3) (x : ZMod (p ^ k)) :
    rootedMultiplicity (broadFamily p k hk) i x =
      Fintype.card (broadLabelSolutions p k hk i x) := by
  classical
  simp only [rootedMultiplicity, broadFamily, broadParams]
  rw [Multiset.filter_map, Multiset.card_map]
  simp [Function.comp_def, and_comm]
  rw [Fintype.card_subtype]
  congr 1
  ext rs
  simp [and_comm]

theorem broadFamily_rootedMultiplicity_zero
    {p k : ℕ} [NeZero (p ^ k)] (hp : p.Prime) (hk : 0 < k)
    (x : ZMod (p ^ k)) :
    rootedMultiplicity (broadFamily p k hk) 0 x =
      Fintype.card (broadProductSolutions (ZMod (p ^ k)) x) := by
  classical
  rw [broadFamily_rootedMultiplicity_eq_card hk]
  apply Fintype.card_congr
  exact Equiv.subtypeEquiv (Equiv.refl _) (by
    intro rs
    simp only [Equiv.refl_apply, parameterTriangle_zero, neg_mul]
    rw [primePowerReduction_ne_zero_iff_isUnit hp hk,
      primePowerReduction_ne_zero_iff_isUnit hp hk])

def parameterSwap01Equiv {R : Type*} [AddGroup R] : R × R ≃ R × R where
  toFun rs := (-rs.1, rs.1 + rs.2)
  invFun rs := (-rs.1, rs.1 + rs.2)
  left_inv rs := by ext <;> simp
  right_inv rs := by ext <;> simp

def parameterSwap02Equiv {R : Type*} [AddGroup R] : R × R ≃ R × R where
  toFun rs := (rs.1 + rs.2, -rs.2)
  invFun rs := (rs.1 + rs.2, -rs.2)
  left_inv rs := by ext <;> simp
  right_inv rs := by ext <;> simp

theorem reduction_admissible_swap01
    {p k : ℕ} (hk : 0 < k) (r s : ZMod (p ^ k)) :
    (primePowerReduction p k hk (-r) ≠ 0 ∨
      primePowerReduction p k hk (r + s) ≠ 0) ↔
    (primePowerReduction p k hk r ≠ 0 ∨
      primePowerReduction p k hk s ≠ 0) := by
  by_cases hr : primePowerReduction p k hk r = 0
  · simp [map_neg, map_add, hr]
  · simp [map_neg, map_add, hr]

theorem reduction_admissible_swap02
    {p k : ℕ} (hk : 0 < k) (r s : ZMod (p ^ k)) :
    (primePowerReduction p k hk (r + s) ≠ 0 ∨
      primePowerReduction p k hk (-s) ≠ 0) ↔
    (primePowerReduction p k hk r ≠ 0 ∨
      primePowerReduction p k hk s ≠ 0) := by
  by_cases hs : primePowerReduction p k hk s = 0
  · simp [map_neg, map_add, hs]
  · simp [map_neg, map_add, hs]

noncomputable def broadLabelOneEquivZero
    {p k : ℕ} (hk : 0 < k) (x : ZMod (p ^ k)) :
    broadLabelSolutions p k hk 1 x ≃ broadLabelSolutions p k hk 0 x :=
  Equiv.subtypeEquiv parameterSwap01Equiv (by
    rintro ⟨r, s⟩
    constructor
    · rintro ⟨hadm, hout⟩
      refine ⟨(reduction_admissible_swap01 hk r s).2 hadm, ?_⟩
      simpa [parameterSwap01Equiv, parameterTriangle] using hout
    · rintro ⟨hadm, hout⟩
      refine ⟨(reduction_admissible_swap01 hk r s).1 hadm, ?_⟩
      simpa [parameterSwap01Equiv, parameterTriangle] using hout)

noncomputable def broadLabelTwoEquivZero
    {p k : ℕ} (hk : 0 < k) (x : ZMod (p ^ k)) :
    broadLabelSolutions p k hk 2 x ≃ broadLabelSolutions p k hk 0 x :=
  Equiv.subtypeEquiv parameterSwap02Equiv (by
    rintro ⟨r, s⟩
    constructor
    · rintro ⟨hadm, hout⟩
      refine ⟨(reduction_admissible_swap02 hk r s).2 hadm, ?_⟩
      calc
        parameterTriangle
            (parameterSwap02Equiv (r, s)).1
            (parameterSwap02Equiv (r, s)).2 0 =
            parameterTriangle r s 2 := by
          simp [parameterSwap02Equiv, parameterTriangle]
          ring
        _ = x := hout
    · rintro ⟨hadm, hout⟩
      refine ⟨(reduction_admissible_swap02 hk r s).1 hadm, ?_⟩
      calc
        parameterTriangle r s 2 =
            parameterTriangle
              (parameterSwap02Equiv (r, s)).1
              (parameterSwap02Equiv (r, s)).2 0 := by
          simp [parameterSwap02Equiv, parameterTriangle]
          ring
        _ = x := hout)

theorem card_broadLabelOne_eq_zero
    {p k : ℕ} [NeZero (p ^ k)] (hk : 0 < k) (x : ZMod (p ^ k)) :
    Fintype.card (broadLabelSolutions p k hk 1 x) =
      Fintype.card (broadLabelSolutions p k hk 0 x) :=
  Fintype.card_congr (broadLabelOneEquivZero hk x)

theorem card_broadLabelTwo_eq_zero
    {p k : ℕ} [NeZero (p ^ k)] (hk : 0 < k) (x : ZMod (p ^ k)) :
    Fintype.card (broadLabelSolutions p k hk 2 x) =
      Fintype.card (broadLabelSolutions p k hk 0 x) :=
  Fintype.card_congr (broadLabelTwoEquivZero hk x)

theorem broadFamily_rootedMultiplicity_one_eq_zero
    {p k : ℕ} [NeZero (p ^ k)] (hk : 0 < k) (x : ZMod (p ^ k)) :
    rootedMultiplicity (broadFamily p k hk) 1 x =
      rootedMultiplicity (broadFamily p k hk) 0 x := by
  rw [broadFamily_rootedMultiplicity_eq_card hk,
    broadFamily_rootedMultiplicity_eq_card hk,
    card_broadLabelOne_eq_zero hk]

theorem broadFamily_rootedMultiplicity_two_eq_zero
    {p k : ℕ} [NeZero (p ^ k)] (hk : 0 < k) (x : ZMod (p ^ k)) :
    rootedMultiplicity (broadFamily p k hk) 2 x =
      rootedMultiplicity (broadFamily p k hk) 0 x := by
  rw [broadFamily_rootedMultiplicity_eq_card hk,
    broadFamily_rootedMultiplicity_eq_card hk,
    card_broadLabelTwo_eq_zero hk]

theorem broadFamily_rootedMultiplicity
    {p k : ℕ} [NeZero (p ^ k)] (hp : p.Prime) (hk : 0 < k)
    (i : Fin 3) (x : ZMod (p ^ k)) :
    rootedMultiplicity (broadFamily p k hk) i x =
      if IsUnit x then Fintype.card (ZMod (p ^ k))ˣ
      else 2 * Fintype.card (ZMod (p ^ k))ˣ := by
  classical
  have h0 := broadFamily_rootedMultiplicity_zero hp hk x
  rw [card_broadProductSolutions] at h0
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  · exact h0
  · exact (broadFamily_rootedMultiplicity_one_eq_zero hk x).trans h0
  · exact (broadFamily_rootedMultiplicity_two_eq_zero hk x).trans h0

theorem broadFamily_coverMultiplicity
    {p k : ℕ} [NeZero (p ^ k)] (hp : p.Prime) (hk : 0 < k)
    (x : ZMod (p ^ k)) :
    coverMultiplicity (broadFamily p k hk) x =
      if IsUnit x then 3 * Fintype.card (ZMod (p ^ k))ˣ
      else 6 * Fintype.card (ZMod (p ^ k))ˣ := by
  classical
  rw [coverMultiplicity_eq_sum_rootedMultiplicity]
  simp_rw [broadFamily_rootedMultiplicity hp hk]
  by_cases hx : IsUnit x
  · simp [hx]
  · simp [hx]
    omega

end BroadPrimePower

end

/-! ## Coprime products

The six permutations are used in the product construction.  Averaging over
them is exactly what makes aggregate (rather than labelwise) uniformity
multiply under CRT.
-/

def fin3Permutations : Multiset (Fin 3 → Fin 3) :=
  ([
    (fun i : Fin 3 ↦ ⟨i.val, by omega⟩),
    (fun i : Fin 3 ↦ ⟨(i.val + 1) % 3, by omega⟩),
    (fun i : Fin 3 ↦ ⟨(i.val + 2) % 3, by omega⟩),
    (fun i : Fin 3 ↦ ⟨2 * i.val % 3, by omega⟩),
    (fun i : Fin 3 ↦ ⟨(2 * i.val + 1) % 3, by omega⟩),
    (fun i : Fin 3 ↦ ⟨(2 * i.val + 2) % 3, by omega⟩)
  ] : List (Fin 3 → Fin 3))

theorem fin3Permutations_pair_count (f : Fin 3 → α) (g : Fin 3 → β)
    [DecidableEq α] [DecidableEq β] (x : α) (y : β) :
    (fin3Permutations.map fun σ ↦
      (Finset.univ.filter fun i : Fin 3 ↦ f i = x ∧ g (σ i) = y).card).sum =
      2 * fiberCard f x * fiberCard g y := by
  have h3 : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  by_cases hf0 : f 0 = x <;> by_cases hf1 : f 1 = x <;> by_cases hf2 : f 2 = x <;>
    by_cases hg0 : g 0 = y <;> by_cases hg1 : g 1 = y <;> by_cases hg2 : g 2 = y <;>
    simp [fin3Permutations, fiberCard, h3, Finset.filter_insert,
      Finset.filter_singleton, hf0, hf1, hf2, hg0, hg1, hg2]

theorem fin3Permutations_injective :
    ∀ σ ∈ fin3Permutations, Function.Injective σ := by
  decide

def crtPermutedMaps {m n : ℕ} (h : m.Coprime n)
    (f : Fin 3 → ZMod m) (g : Fin 3 → ZMod n) :
    Multiset (Fin 3 → ZMod (m * n)) :=
  fin3Permutations.map fun σ i ↦
    (ZMod.chineseRemainder h).symm (f i, g (σ i))

def crtAggregate {m n : ℕ} (h : m.Coprime n)
    (Fm : Multiset (Fin 3 → ZMod m)) (Fn : Multiset (Fin 3 → ZMod n)) :
    Multiset (Fin 3 → ZMod (m * n)) :=
  Fm.bind fun f ↦ Fn.bind fun g ↦ crtPermutedMaps h f g

theorem coverMultiplicity_crtPermutedMaps {m n : ℕ} (h : m.Coprime n)
    [NeZero m] [NeZero n]
    (f : Fin 3 → ZMod m) (g : Fin 3 → ZMod n) (z : ZMod (m * n)) :
    coverMultiplicity (crtPermutedMaps h f g) z =
      2 * fiberCard f (ZMod.chineseRemainder h z).1 *
        fiberCard g (ZMod.chineseRemainder h z).2 := by
  simpa [crtPermutedMaps, coverMultiplicity, fiberCard, RingEquiv.symm_apply_eq,
    Prod.ext_iff] using
    fin3Permutations_pair_count f g (ZMod.chineseRemainder h z).1
      (ZMod.chineseRemainder h z).2

theorem coverMultiplicity_bind {A V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (F : Multiset A) (G : A → Multiset (V → W)) (w : W) :
    coverMultiplicity (F.bind G) w =
      (F.map fun a ↦ coverMultiplicity (G a) w).sum := by
  simp [coverMultiplicity, Multiset.map_bind, Multiset.sum_bind]

theorem coverMultiplicity_crtAggregate {m n : ℕ} (h : m.Coprime n)
    [NeZero m] [NeZero n]
    (Fm : Multiset (Fin 3 → ZMod m)) (Fn : Multiset (Fin 3 → ZMod n))
    (z : ZMod (m * n)) :
    coverMultiplicity (crtAggregate h Fm Fn) z =
      2 * coverMultiplicity Fm (ZMod.chineseRemainder h z).1 *
        coverMultiplicity Fn (ZMod.chineseRemainder h z).2 := by
  rw [crtAggregate, coverMultiplicity_bind]
  simp_rw [coverMultiplicity_bind, coverMultiplicity_crtPermutedMaps]
  simp [coverMultiplicity, Multiset.sum_map_mul_left,
    Multiset.sum_map_mul_right, mul_assoc, mul_comm, mul_left_comm]

theorem crtAggregate_uniform {m n Dm Dn : ℕ} (h : m.Coprime n)
    [NeZero m] [NeZero n]
    {Fm : Multiset (Fin 3 → ZMod m)} {Fn : Multiset (Fin 3 → ZMod n)}
    (hm : UniformCover Fm Dm) (hn : UniformCover Fn Dn) :
    UniformCover (crtAggregate h Fm Fn) (2 * Dm * Dn) := by
  intro z
  rw [coverMultiplicity_crtAggregate h Fm Fn z, hm, hn]

theorem crtAggregate_isRelCover {m n : ℕ} (h : m.Coprime n)
    {Fm : Multiset (Fin 3 → ZMod m)} {Fn : Multiset (Fin 3 → ZMod n)}
    (hm : IsRelCover K3Rel (SquareSumRel m) Fm)
    (hn : IsRelCover K3Rel (SquareSumRel n) Fn) :
    IsRelCover K3Rel (SquareSumRel (m * n)) (crtAggregate h Fm Fn) := by
  intro k hk
  rw [crtAggregate, Multiset.mem_bind] at hk
  rcases hk with ⟨f, hf, hk⟩
  rw [Multiset.mem_bind] at hk
  rcases hk with ⟨g, hg, hk⟩
  rw [crtPermutedMaps, Multiset.mem_map] at hk
  rcases hk with ⟨σ, hσ, rfl⟩
  intro i j hij
  rw [squareSumRel_chineseRemainder h]
  simp only [RingEquiv.apply_symm_apply]
  exact ⟨hm f hf hij,
    hn g hg (fun hEq ↦ hij (fin3Permutations_injective σ hσ hEq))⟩

/-! ## Assembly from prime powers -/

/-- A positive uniform triangle cover, packaged together with the
nonzeroness of its modulus. -/
def HasPositiveTriangleCover (n : ℕ) : Prop :=
  ∃ hn : n ≠ 0,
    letI : NeZero n := ⟨hn⟩
    ∃ D : ℕ, 0 < D ∧ ∃ F : Multiset (Fin 3 → ZMod n),
      UniformCover F D ∧ IsRelCover K3Rel (SquareSumRel n) F

theorem hasPositiveTriangleCover_one : HasPositiveTriangleCover 1 := by
  refine ⟨one_ne_zero, 3, by omega, {fun _ : Fin 3 ↦ (0 : ZMod 1)}, ?_, ?_⟩
  · intro x
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    simp [coverMultiplicity, fiberCard]
  · intro f hf
    simp only [Multiset.mem_singleton] at hf
    subst f
    intro i j hij
    exact ⟨0, by simp [SquareSumRel]⟩

theorem HasPositiveTriangleCover.mul {m n : ℕ}
    (hm : HasPositiveTriangleCover m) (hn : HasPositiveTriangleCover n)
    (hcop : m.Coprime n) : HasPositiveTriangleCover (m * n) := by
  rcases hm with ⟨hm0, Dm, hDm, Fm, hFmU, hFmR⟩
  rcases hn with ⟨hn0, Dn, hDn, Fn, hFnU, hFnR⟩
  letI : NeZero m := ⟨hm0⟩
  letI : NeZero n := ⟨hn0⟩
  refine ⟨mul_ne_zero hm0 hn0, 2 * Dm * Dn, by positivity,
    crtAggregate hcop Fm Fn, crtAggregate_uniform hcop hFmU hFnU,
    crtAggregate_isRelCover hcop hFmR hFnR⟩

theorem hasPositiveTriangleCover_finset_prod
    {I : Type*} [DecidableEq I] (s : Finset I) (q : I → ℕ)
    (hpair : Set.Pairwise (↑s : Set I) (Function.onFun Nat.Coprime q))
    (hq : ∀ i ∈ s, HasPositiveTriangleCover (q i)) :
    HasPositiveTriangleCover (∏ i ∈ s, q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasPositiveTriangleCover_one
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      apply HasPositiveTriangleCover.mul (hq a (by simp))
      · apply ih
        · intro i hi j hj hij
          exact hpair (by simp [hi]) (by simp [hj]) hij
        · intro i hi
          exact hq i (by simp [hi])
      · rw [Nat.coprime_prod_right_iff]
        intro i hi
        exact hpair (by simp) (by simp [hi]) (by
          intro hai
          subst i
          exact ha hi)

theorem odd_hasPositiveTriangleCover_of_primePowers
    (hprimePower : ∀ (p k : ℕ), p.Prime → p ≠ 2 → 0 < k →
      HasPositiveTriangleCover (p ^ k))
    (v : ℕ) (hv0 : v ≠ 0) (hvodd : Odd v) :
    HasPositiveTriangleCover v := by
  have hprod := hasPositiveTriangleCover_finset_prod
    (s := v.primeFactors) (q := fun p ↦ p ^ v.factorization p)
    (by
      intro p hp q hq hpq
      apply Nat.Coprime.pow
      exact (Nat.coprime_primes
        (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hq)).2 hpq)
    (by
      intro p hp
      have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      apply hprimePower p (v.factorization p) hpprime
      · intro hp2
        subst p
        exact (hvodd.not_two_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
      · exact hpprime.factorization_pos_of_dvd hv0
          (Nat.dvd_of_mem_primeFactors hp))
  rwa [← Nat.prod_primeFactors_pow_factorization hv0] at hprod

theorem odd_uniform_triangle_cover_of_primePowers
    (hprimePower : ∀ (p k : ℕ), p.Prime → p ≠ 2 → 0 < k →
      HasPositiveTriangleCover (p ^ k))
    (v : ℕ) [NeZero v] (hvodd : Odd v) :
    ∃ D : ℕ, 0 < D ∧ ∃ F : Multiset (Fin 3 → ZMod v),
      UniformCover F D ∧ IsRelCover K3Rel (SquareSumRel v) F := by
  rcases odd_hasPositiveTriangleCover_of_primePowers hprimePower v
    (NeZero.ne v) hvodd with ⟨_, D, hD, F, hFU, hFR⟩
  exact ⟨D, hD, F, hFU, hFR⟩

/-! ## The exceptional prime three -/

namespace Prime3

variable {q h : ℕ} [NeZero q]

def red (hq : 3 ∣ q) : ZMod q →+* ZMod 3 :=
  ZMod.castHom hq (ZMod 3)

def fiber (hq : 3 ∣ q) (a : ZMod 3) : Finset (ZMod q) :=
  Finset.univ.filter fun x ↦ red hq x = a

def triA (x : ZMod q) : Fin 3 → ZMod q := ![x, -x, -x]

def triB (u z : ZMod q) : Fin 3 → ZMod q := ![u, -u, z]

def familyA (hq : 3 ∣ q) (h : ℕ) : Multiset (Fin 3 → ZMod q) :=
  h • ((fiber hq 1).val.map triA)

def familyB (hq : 3 ∣ q) : Multiset (Fin 3 → ZMod q) :=
  (((fiber hq 0).product (fiber hq 1)).val.map fun p ↦ triB p.1 p.2)

def cover (hq : 3 ∣ q) (h : ℕ) : Multiset (Fin 3 → ZMod q) :=
  familyA hq h + familyB hq

lemma triA_relHom (hq : 3 ∣ q)
    (unitSquare : ∀ w : ZMod q, red hq w = 1 → IsSquare w)
    {x : ZMod q} (hx : x ∈ fiber hq 1) :
    RelHom K3Rel (SquareSumRel q) (triA x) := by
  have hx' : red hq x = 1 := (Finset.mem_filter.mp hx).2
  have hneg : red hq (-x + -x) = 1 := by
    calc
      red hq (-x + -x) = (-1 : ZMod 3) + -1 := by simp [hx']
      _ = 1 := by decide
  have hs : IsSquare (-x + -x) := unitSquare _ hneg
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [K3Rel, triA, squareSumRel_iff_isSquare]

lemma triB_relHom (hq : 3 ∣ q)
    (unitSquare : ∀ w : ZMod q, red hq w = 1 → IsSquare w)
    {u z : ZMod q} (hu : u ∈ fiber hq 0) (hz : z ∈ fiber hq 1) :
    RelHom K3Rel (SquareSumRel q) (triB u z) := by
  have hu' : red hq u = 0 := (Finset.mem_filter.mp hu).2
  have hz' : red hq z = 1 := (Finset.mem_filter.mp hz).2
  have hp : red hq (u + z) = 1 := by simp [map_add, hu', hz']
  have hm : red hq (-u + z) = 1 := by simp [map_add, map_neg, hu', hz']
  have hsp : IsSquare (u + z) := unitSquare _ hp
  have hsm : IsSquare (-u + z) := unitSquare _ hm
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [K3Rel, triB, squareSumRel_iff_isSquare, add_comm]

lemma cover_isRelCover (hq : 3 ∣ q)
    (unitSquare : ∀ w : ZMod q, red hq w = 1 → IsSquare w) :
    IsRelCover K3Rel (SquareSumRel q) (cover hq h) := by
  intro f hf
  rw [cover, Multiset.mem_add] at hf
  rcases hf with hf | hf
  · rw [familyA, Multiset.mem_nsmul] at hf
    rcases hf with ⟨_, hf⟩
    rw [Multiset.mem_map] at hf
    rcases hf with ⟨x, hx, rfl⟩
    exact triA_relHom hq unitSquare hx
  · rw [familyB, Multiset.mem_map] at hf
    rcases hf with ⟨p, hp, rfl⟩
    change p ∈ (fiber hq 0).product (fiber hq 1) at hp
    rcases p with ⟨u, z⟩
    rw [Finset.product_eq_sprod, Finset.mem_product] at hp
    exact triB_relHom hq unitSquare hp.1 hp.2

lemma fiberCard_triA (x v : ZMod q) :
    fiberCard (triA x) v =
      (if x = v then 1 else 0) + 2 * (if -x = v then 1 else 0) := by
  rw [fiberCard, Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_three]
  simp [triA]
  by_cases hv : -x = v <;> simp [hv] <;> rfl

lemma fiberCard_triB (u z v : ZMod q) :
    fiberCard (triB u z) v =
      (if u = v then 1 else 0) + (if -u = v then 1 else 0) +
        (if z = v then 1 else 0) := by
  rw [fiberCard, Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_three]
  simp [triB]
  rfl

lemma coverMultiplicity_familyA (hq : 3 ∣ q) (h : ℕ) (v : ZMod q) :
    coverMultiplicity (familyA hq h) v =
      h * ∑ x ∈ fiber hq 1, fiberCard (triA x) v := by
  rw [coverMultiplicity, familyA, Multiset.map_nsmul, Multiset.sum_nsmul,
    Multiset.map_map]
  rfl

lemma coverMultiplicity_familyB (hq : 3 ∣ q) (v : ZMod q) :
    coverMultiplicity (familyB hq) v =
      ∑ p ∈ (fiber hq 0).product (fiber hq 1),
        fiberCard (triB p.1 p.2) v := by
  rw [coverMultiplicity, familyB, Multiset.map_map, Finset.product_eq_sprod]
  rfl

lemma familyA_count (hq : 3 ∣ q) (h : ℕ) (v : ZMod q) :
    coverMultiplicity (familyA hq h) v =
      h * ((if v ∈ fiber hq 1 then 1 else 0) +
        2 * (if -v ∈ fiber hq 1 then 1 else 0)) := by
  rw [coverMultiplicity_familyA]
  simp_rw [fiberCard_triA]
  rw [Finset.sum_add_distrib]
  simp_rw [neg_eq_iff_eq_neg]
  simp

lemma familyB_count (hq : 3 ∣ q) (v : ZMod q) :
    coverMultiplicity (familyB hq) v =
      (fiber hq 1).card * (if v ∈ fiber hq 0 then 1 else 0) +
      (fiber hq 1).card * (if -v ∈ fiber hq 0 then 1 else 0) +
      (fiber hq 0).card * (if v ∈ fiber hq 1 then 1 else 0) := by
  rw [coverMultiplicity_familyB, Finset.product_eq_sprod, Finset.sum_product]
  simp_rw [fiberCard_triB, Finset.sum_add_distrib]
  simp_rw [neg_eq_iff_eq_neg]
  simp

lemma coverMultiplicity_add (F G : Multiset (Fin 3 → ZMod q)) (v : ZMod q) :
    coverMultiplicity (F + G) v =
      coverMultiplicity F v + coverMultiplicity G v := by
  simp [coverMultiplicity]

theorem cover_uniform (hq : 3 ∣ q)
    (hfiber : ∀ a : ZMod 3, (fiber hq a).card = h) :
    UniformCover (cover hq h) (2 * h) := by
  intro v
  rw [cover, coverMultiplicity_add, familyA_count, familyB_count,
    hfiber, hfiber]
  have hv : red hq v = 0 ∨ red hq v = 1 ∨ red hq v = 2 := by
    exact (by decide : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = 2) _
  have h01 : (0 : ZMod 3) ≠ 1 := by decide
  have h02 : (0 : ZMod 3) ≠ 2 := by decide
  have h10 : (1 : ZMod 3) ≠ 0 := by decide
  have h12 : (1 : ZMod 3) ≠ 2 := by decide
  have h20 : (2 : ZMod 3) ≠ 0 := by decide
  have h21 : (2 : ZMod 3) ≠ 1 := by decide
  rcases hv with hv | hv | hv
  · have hn : red hq (-v) = 0 := by simp [hv]
    simp [fiber, hv, hn, h01, h02, h10, h12, h20, h21]
    ring
  · have hn : red hq (-v) = 2 := by
      calc
        red hq (-v) = -(red hq v) := map_neg (red hq) v
        _ = 2 := by rw [hv]; decide
    simp [fiber, hv, hn, h01, h02, h10, h12, h20, h21]
    ring
  · have hn : red hq (-v) = 1 := by
      calc
        red hq (-v) = -(red hq v) := map_neg (red hq) v
        _ = 1 := by rw [hv]; decide
    simp [fiber, hv, hn, h01, h02, h10, h12, h20, h21]
    ring

lemma fiber_card_eq (hq : 3 ∣ q) (a b : ZMod 3) :
    (fiber hq a).card = (fiber hq b).card := by
  obtain ⟨d, hd⟩ := ZMod.castHom_surjective hq (b - a)
  change red hq d = b - a at hd
  apply Finset.card_bij (fun x _ ↦ x + d)
  · intro x hx
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [map_add, hx, hd]
    ring
  · intro x _ y _ hxy
    exact add_right_cancel hxy
  · intro y hy
    refine ⟨y - d, ?_, ?_⟩
    · simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [map_sub, hy, hd]
      ring
    · simp

lemma three_mul_fiber_card (hq : 3 ∣ q) :
    3 * (fiber hq 0).card = q := by
  have htotal := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (ZMod q)))
    (t := (Finset.univ : Finset (ZMod 3)))
    (f := red hq) (by simp)
  rw [Finset.card_univ, ZMod.card] at htotal
  change q = ∑ b : ZMod 3, (fiber hq b).card at htotal
  rw [← (ZMod.finEquiv 3).toEquiv.sum_comp] at htotal
  rw [Fin.sum_univ_three] at htotal
  norm_num at htotal
  rw [fiber_card_eq hq 1 0,
    fiber_card_eq hq ((ZMod.finEquiv 3) 2) 0] at htotal
  omega

lemma power_three_fiber_card {k : ℕ} (hk : 1 ≤ k) (a : ZMod 3) :
    let hq : 3 ∣ 3 ^ k := dvd_pow_self 3 (by omega)
    (fiber hq a).card = 3 ^ (k - 1) := by
  let hq : 3 ∣ 3 ^ k := dvd_pow_self 3 (by omega)
  have hpow : 3 ^ k = 3 * 3 ^ (k - 1) := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    simp [pow_succ']
  have h0 : (fiber hq 0).card = 3 ^ (k - 1) := by
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3)
    exact (three_mul_fiber_card hq).trans hpow
  exact (fiber_card_eq hq a 0).trans h0

theorem power_three_uniform_triangle_cover {k : ℕ} (hk : 1 ≤ k)
    (unitSquare : ∀ w : ZMod (3 ^ k),
      red (dvd_pow_self 3 (by omega)) w = 1 → IsSquare w) :
    ∃ F : Multiset (Fin 3 → ZMod (3 ^ k)),
      UniformCover F (2 * 3 ^ (k - 1)) ∧
      IsRelCover K3Rel (SquareSumRel (3 ^ k)) F := by
  let hq : 3 ∣ 3 ^ k := dvd_pow_self 3 (by omega)
  refine ⟨cover hq (3 ^ (k - 1)), cover_uniform hq ?_, ?_⟩
  · intro a
    exact power_three_fiber_card hk a
  · apply cover_isRelCover hq
    intro w hw
    exact unitSquare w hw

end Prime3

theorem threePower_hasPositiveTriangleCover {k : ℕ} (hk : 0 < k) :
    HasPositiveTriangleCover (3 ^ k) := by
  letI : NeZero (3 ^ k) := ⟨pow_ne_zero _ (by norm_num)⟩
  obtain ⟨F, hFU, hFR⟩ := Prime3.power_three_uniform_triangle_cover hk (by
    intro w hw
    have hred : primePowerReduction 3 k hk w = 1 := by
      simpa [Prime3.red, primePowerReduction] using hw
    apply isSquare_primePower_of_reduction
      (p := 3) (k := k) (by norm_num) (by norm_num) hk w
    · rw [hred]
      exact one_ne_zero
    · rw [hred]
      exact ⟨1, by simp⟩)
  exact ⟨pow_ne_zero _ (by norm_num), 2 * 3 ^ (k - 1), by positivity,
    F, hFU, hFR⟩

/-! ## The exceptional prime five -/

namespace Prime5

section AbstractFivePowerCover

variable {V : Type*} [Fintype V] [DecidableEq V] [AddCommGroup V]

def mainMap (u x : V) : Fin 3 → V
  | 0 => u
  | 1 => x
  | 2 => -x

def loopMap (y : V) : Fin 3 → V := fun _ => y

def basicFamily (N Q : Finset V) : Multiset (Fin 3 → V) :=
  (N ×ˢ Q).val.map fun p => mainMap p.1 p.2

def coverFamily (N Q R : Finset V) (t : ℕ) : Multiset (Fin 3 → V) :=
  3 • basicFamily N Q +
    R.val.bind (fun y => Multiset.replicate (2 * t) (loopMap y))

theorem fiberCard_mainMap (u x z : V) :
    fiberCard (mainMap u x) z =
      (if u = z then 1 else 0) + (if x = z then 1 else 0) +
        (if -x = z then 1 else 0) := by
  rw [fiberCard, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fin.sum_univ_three]
  simp [mainMap]
  rfl

theorem fiberCard_loopMap (y z : V) :
    fiberCard (loopMap y) z = if y = z then 3 else 0 := by
  by_cases h : y = z <;> simp [fiberCard, loopMap, h]

theorem coverMultiplicity_basicFamily (N Q : Finset V) (z : V) :
    coverMultiplicity (basicFamily N Q) z =
      (if z ∈ N then Q.card else 0) +
      (if z ∈ Q then N.card else 0) +
      (if -z ∈ Q then N.card else 0) := by
  classical
  unfold coverMultiplicity basicFamily
  rw [Multiset.map_map]
  change (∑ p ∈ N ×ˢ Q, fiberCard (mainMap p.1 p.2) z) = _
  rw [Finset.sum_product]
  simp_rw [fiberCard_mainMap]
  simp only [Finset.sum_add_distrib]
  by_cases hn : z ∈ N <;> by_cases hq : z ∈ Q <;>
    by_cases hm : -z ∈ Q <;> simp [hn, hq, hm, neg_eq_iff_eq_neg]

theorem coverMultiplicity_loopFamily (R : Finset V) (t : ℕ) (z : V) :
    coverMultiplicity
        (R.val.bind (fun y => Multiset.replicate (2 * t) (loopMap y))) z =
      if z ∈ R then 6 * t else 0 := by
  classical
  simp only [coverMultiplicity, Multiset.map_bind, Multiset.sum_bind,
    Multiset.map_replicate, Multiset.sum_replicate, fiberCard_loopMap]
  by_cases hz : z ∈ R
  · simp [hz, mul_assoc, mul_comm, mul_left_comm]
  · simp [hz]

theorem coverMultiplicity_coverFamily (N Q R : Finset V) (t : ℕ) (z : V) :
    coverMultiplicity (coverFamily N Q R t) z =
      3 * ((if z ∈ N then Q.card else 0) +
        (if z ∈ Q then N.card else 0) +
        (if -z ∈ Q then N.card else 0)) +
      (if z ∈ R then 6 * t else 0) := by
  classical
  change
    (Multiset.map (fun f => fiberCard f z)
      (3 • basicFamily N Q +
        R.val.bind (fun y => Multiset.replicate (2 * t) (loopMap y)))).sum = _
  rw [Multiset.map_add, Multiset.sum_add, Multiset.map_nsmul, Multiset.sum_nsmul]
  change 3 * coverMultiplicity (basicFamily N Q) z +
    coverMultiplicity
      (R.val.bind (fun y => Multiset.replicate (2 * t) (loopMap y))) z = _
  rw [coverMultiplicity_basicFamily, coverMultiplicity_loopFamily]

theorem coverFamily_uniform
    (N Q R : Finset V) (t : ℕ)
    (hN : N.card = t) (hQ : Q.card = 2 * t)
    (hpart : ∀ z : V, z ∈ N ∨ z ∈ Q ∨ z ∈ R)
    (hNQ : Disjoint N Q) (hNR : Disjoint N R) (hQR : Disjoint Q R)
    (hnegQ : ∀ z : V, -z ∈ Q ↔ z ∈ Q) :
    UniformCover (coverFamily N Q R t) (6 * t) := by
  intro z
  rw [coverMultiplicity_coverFamily, hN, hQ]
  rcases hpart z with hzN | hzQ | hzR
  · have hzQ : z ∉ Q := fun hz => Finset.disjoint_left.mp hNQ hzN hz
    have hzR : z ∉ R := fun hz => Finset.disjoint_left.mp hNR hzN hz
    have hneg : -z ∉ Q := by simpa [hnegQ] using hzQ
    simp [hzN, hzQ, hzR, hneg]
    omega
  · have hzN : z ∉ N := fun hz => Finset.disjoint_left.mp hNQ hz hzQ
    have hzR : z ∉ R := fun hz => Finset.disjoint_left.mp hQR hzQ hz
    have hneg : -z ∈ Q := (hnegQ z).2 hzQ
    simp [hzN, hzQ, hzR, hneg]
    omega
  · have hzN : z ∉ N := fun hz => Finset.disjoint_left.mp hNR hz hzR
    have hzQ : z ∉ Q := fun hz => Finset.disjoint_left.mp hQR hz hzR
    have hneg : -z ∉ Q := by simpa [hnegQ] using hzQ
    simp [hzN, hzQ, hzR, hneg]

theorem coverFamily_isRelCover
    (N Q R : Finset V) (S : V → V → Prop)
    (hmain : ∀ u ∈ N, ∀ x ∈ Q, RelHom K3Rel S (mainMap u x))
    (hloop : ∀ y ∈ R, RelHom K3Rel S (loopMap y)) :
    IsRelCover K3Rel S (coverFamily N Q R t) := by
  intro f hf
  simp only [coverFamily, Multiset.mem_add, Multiset.mem_nsmul,
    basicFamily, Multiset.mem_map, Finset.mem_product, Finset.mem_val,
    Multiset.mem_bind, Multiset.mem_replicate] at hf
  rcases hf with ⟨_, p, hp, rfl⟩ | ⟨y, hy, _, rfl⟩
  · exact hmain p.1 hp.1 p.2 hp.2
  · exact hloop y hy

end AbstractFivePowerCover

def reduction (k : ℕ) : ZMod (5 ^ (k + 1)) →+* ZMod 5 :=
  ZMod.castHom (by simp [pow_succ]) (ZMod 5)

def fiber (k : ℕ) (a : ZMod 5) : Finset (ZMod (5 ^ (k + 1))) :=
  Finset.univ.filter fun z => reduction k z = a

theorem reduction_surjective (k : ℕ) : Function.Surjective (reduction k) := by
  exact ZMod.castHom_surjective (by simp [pow_succ])

theorem fiber_card (k : ℕ) (a : ZMod 5) :
    (fiber k a).card = 5 ^ k := by
  classical
  have hsame : ∀ b : ZMod 5, (fiber k b).card = (fiber k a).card := by
    intro b
    exact AddMonoidHom.card_fiber_eq_of_mem_range (reduction k).toAddMonoidHom
      (reduction_surjective k b) (reduction_surjective k a)
  have hsum :
      Fintype.card (ZMod (5 ^ (k + 1))) =
        ∑ b : ZMod 5, (fiber k b).card := by
    rw [← Finset.card_univ]
    apply Finset.card_eq_sum_card_fiberwise
    intro z hz
    simp
  rw [ZMod.card] at hsum
  simp_rw [hsame] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hcard : (Finset.univ : Finset (ZMod 5)).card = 5 := by simp
  rw [hcard] at hsum
  have hp : 5 ^ (k + 1) = 5 * 5 ^ k := by simp [pow_succ, Nat.mul_comm]
  omega

theorem fiber_disjoint (k : ℕ) {a b : ZMod 5} (hab : a ≠ b) :
    Disjoint (fiber k a) (fiber k b) := by
  apply Finset.disjoint_left.mpr
  intro z hza hzb
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hza hzb
  exact hab (hza.symm.trans hzb)

def nonunitResidues (k : ℕ) : Finset (ZMod (5 ^ (k + 1))) :=
  fiber k 0

def squareUnitResidues (k : ℕ) : Finset (ZMod (5 ^ (k + 1))) :=
  fiber k 1 ∪ fiber k 4

def nonsquareUnitResidues (k : ℕ) : Finset (ZMod (5 ^ (k + 1))) :=
  fiber k 2 ∪ fiber k 3

theorem nonunitResidues_card (k : ℕ) :
    (nonunitResidues k).card = 5 ^ k := fiber_card k 0

theorem squareUnitResidues_card (k : ℕ) :
    (squareUnitResidues k).card = 2 * 5 ^ k := by
  rw [squareUnitResidues, Finset.card_union_of_disjoint
      (fiber_disjoint k (by decide : (1 : ZMod 5) ≠ 4)),
    fiber_card, fiber_card]
  omega

theorem residue_partition (k : ℕ) (z : ZMod (5 ^ (k + 1))) :
    z ∈ nonunitResidues k ∨ z ∈ squareUnitResidues k ∨
      z ∈ nonsquareUnitResidues k := by
  have hcases : ∀ r : ZMod 5, r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by
    decide
  rcases hcases (reduction k z) with h | h | h | h | h
  · exact Or.inl (by simpa [nonunitResidues, fiber] using h)
  · exact Or.inr (Or.inl (by simp [squareUnitResidues, fiber, h]))
  · exact Or.inr (Or.inr (by simp [nonsquareUnitResidues, fiber, h]))
  · exact Or.inr (Or.inr (by simp [nonsquareUnitResidues, fiber, h]))
  · exact Or.inr (Or.inl (by simp [squareUnitResidues, fiber, h]))

theorem residue_disjoint_NQ (k : ℕ) :
    Disjoint (nonunitResidues k) (squareUnitResidues k) := by
  rw [nonunitResidues, squareUnitResidues, Finset.disjoint_union_right]
  exact ⟨fiber_disjoint k (by decide : (0 : ZMod 5) ≠ 1),
    fiber_disjoint k (by decide : (0 : ZMod 5) ≠ 4)⟩

theorem residue_disjoint_NR (k : ℕ) :
    Disjoint (nonunitResidues k) (nonsquareUnitResidues k) := by
  rw [nonunitResidues, nonsquareUnitResidues, Finset.disjoint_union_right]
  exact ⟨fiber_disjoint k (by decide : (0 : ZMod 5) ≠ 2),
    fiber_disjoint k (by decide : (0 : ZMod 5) ≠ 3)⟩

theorem residue_disjoint_QR (k : ℕ) :
    Disjoint (squareUnitResidues k) (nonsquareUnitResidues k) := by
  rw [squareUnitResidues, nonsquareUnitResidues, Finset.disjoint_union_left,
    Finset.disjoint_union_right, Finset.disjoint_union_right]
  exact ⟨⟨fiber_disjoint k (by decide : (1 : ZMod 5) ≠ 2),
      fiber_disjoint k (by decide : (1 : ZMod 5) ≠ 3)⟩,
    ⟨fiber_disjoint k (by decide : (4 : ZMod 5) ≠ 2),
      fiber_disjoint k (by decide : (4 : ZMod 5) ≠ 3)⟩⟩

theorem neg_mem_squareUnitResidues_iff (k : ℕ)
    (z : ZMod (5 ^ (k + 1))) :
    -z ∈ squareUnitResidues k ↔ z ∈ squareUnitResidues k := by
  simp only [squareUnitResidues, fiber, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [map_neg]
  change (-reduction k z = (1 : ZMod 5) ∨ -reduction k z = (4 : ZMod 5)) ↔
    (reduction k z = (1 : ZMod 5) ∨ reduction k z = (4 : ZMod 5))
  have h : ∀ r : ZMod 5, (-r = 1 ∨ -r = 4) ↔ (r = 1 ∨ r = 4) := by decide
  exact h _

def UnitSquareLift (k : ℕ) : Prop :=
  ∀ z : ZMod (5 ^ (k + 1)), reduction k z ≠ 0 →
    IsSquare (reduction k z) → IsSquare z

theorem unitSquareLift (k : ℕ) : UnitSquareLift k := by
  intro z hz0 hsq
  apply isSquare_primePower_of_reduction
    (p := 5) (k := k + 1) (by norm_num) (by norm_num) (by omega) z
  · simpa [reduction, primePowerReduction] using hz0
  · simpa [reduction, primePowerReduction] using hsq

theorem squareSumRel_of_reduction_square {k : ℕ} (hLift : UnitSquareLift k)
    (a b : ZMod (5 ^ (k + 1)))
    (hne : reduction k (a + b) ≠ 0)
    (hsq : IsSquare (reduction k (a + b))) :
    SquareSumRel (5 ^ (k + 1)) a b := by
  rcases hLift (a + b) hne hsq with ⟨w, hw⟩
  exact ⟨w, by simpa [pow_two] using hw.symm⟩

theorem mainMap_isRelHom {k : ℕ} (hLift : UnitSquareLift k)
    {u x : ZMod (5 ^ (k + 1))} (hu : u ∈ nonunitResidues k)
    (hx : x ∈ squareUnitResidues k) :
    RelHom K3Rel (SquareSumRel (5 ^ (k + 1))) (mainMap u x) := by
  simp only [nonunitResidues, squareUnitResidues, fiber, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_union] at hu hx
  have hplus : SquareSumRel (5 ^ (k + 1)) u x := by
    apply squareSumRel_of_reduction_square hLift
    · simp only [map_add, hu, zero_add]
      rcases hx with hx | hx <;> rw [hx] <;> decide
    · simp only [map_add, hu, zero_add]
      rcases hx with hx | hx <;> rw [hx] <;> decide
  have hminus : SquareSumRel (5 ^ (k + 1)) u (-x) := by
    apply squareSumRel_of_reduction_square hLift
    · simp only [map_add, map_neg, hu, zero_add]
      rcases hx with hx | hx <;> rw [hx] <;> decide
    · simp only [map_add, map_neg, hu, zero_add]
      rcases hx with hx | hx <;> rw [hx] <;> decide
  have hzero : SquareSumRel (5 ^ (k + 1)) x (-x) := ⟨0, by simp⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [K3Rel] at hij
  all_goals simp only [mainMap]
  · exact hplus
  · exact hminus
  · exact squareSumRel_comm.mpr hplus
  · exact hzero
  · exact squareSumRel_comm.mpr hminus
  · exact squareSumRel_comm.mpr hzero

theorem loopMap_isRelHom {k : ℕ} (hLift : UnitSquareLift k)
    {y : ZMod (5 ^ (k + 1))} (hy : y ∈ nonsquareUnitResidues k) :
    RelHom K3Rel (SquareSumRel (5 ^ (k + 1))) (loopMap y) := by
  simp only [nonsquareUnitResidues, fiber, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and] at hy
  intro i j hij
  apply squareSumRel_of_reduction_square hLift
  · simp only [loopMap, map_add]
    rcases hy with hy | hy <;> rw [hy] <;> decide
  · simp only [loopMap, map_add]
    rcases hy with hy | hy <;> rw [hy] <;> decide

theorem power_five_uniform_relCover (k : ℕ) :
    ∃ F : Multiset (Fin 3 → ZMod (5 ^ (k + 1))),
      UniformCover F (6 * 5 ^ k) ∧
        IsRelCover K3Rel (SquareSumRel (5 ^ (k + 1))) F := by
  let F := coverFamily (nonunitResidues k) (squareUnitResidues k)
    (nonsquareUnitResidues k) (5 ^ k)
  refine ⟨F, ?_, ?_⟩
  · exact coverFamily_uniform _ _ _ _ (nonunitResidues_card k)
      (squareUnitResidues_card k) (residue_partition k)
      (residue_disjoint_NQ k) (residue_disjoint_NR k)
      (residue_disjoint_QR k) (neg_mem_squareUnitResidues_iff k)
  · exact coverFamily_isRelCover _ _ _ _
      (fun u hu x hx => mainMap_isRelHom (unitSquareLift k) hu hx)
      (fun y hy => loopMap_isRelHom (unitSquareLift k) hy)

end Prime5

theorem fivePower_hasPositiveTriangleCover {k : ℕ} (hk : 0 < k) :
    HasPositiveTriangleCover (5 ^ k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  obtain ⟨F, hFU, hFR⟩ := Prime5.power_five_uniform_relCover j
  exact ⟨pow_ne_zero _ (by norm_num), 6 * 5 ^ j, by positivity, F, hFU, hFR⟩

/-! ## Uniform unit supplements for prime powers p^k, p ≥ 7 -/


theorem finiteField_isSquare_mul_iff
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    IsSquare (a * b) ↔ (IsSquare a ↔ IsSquare b) := by
  constructor
  · intro hab
    constructor
    · intro haSq
      have h := hab.mul haSq.inv
      have heq : a * b * a⁻¹ = b := by
        rw [mul_comm a b, mul_assoc, mul_inv_cancel₀ ha, mul_one]
      rwa [heq] at h
    · intro hbSq
      have h := hab.mul hbSq.inv
      have heq : a * b * b⁻¹ = a := by rw [mul_assoc, mul_inv_cancel₀ hb, mul_one]
      rwa [heq] at h
  · intro hsame
    by_cases haSq : IsSquare a
    · exact haSq.mul (hsame.mp haSq)
    · have hbSq : ¬IsSquare b := by
        intro h
        exact haSq (hsame.mpr h)
      apply (quadraticChar_one_iff_isSquare (mul_ne_zero ha hb)).mp
      rw [map_mul, quadraticChar_neg_one_iff_not_isSquare.mpr haSq,
        quadraticChar_neg_one_iff_not_isSquare.mpr hbSq]
      norm_num

theorem isSquare_mul_inv_iff_of_isSquare
    {G : Type*} [CommGroup G] (x t : G) (ht : IsSquare t) :
    IsSquare (x * t⁻¹) ↔ IsSquare x := by
  constructor
  · intro h
    have := h.mul ht
    simpa [mul_assoc] using this
  · intro h
    exact h.mul ht.inv

theorem isSquare_coe_unit_iff
    {R : Type*} [CommMonoid R] (u : Rˣ) :
    IsSquare (u : R) ↔ IsSquare u := by
  constructor
  · rintro ⟨r, hr⟩
    have hrUnit : IsUnit r := by
      apply isUnit_of_mul_isUnit_left
      rw [← hr]
      exact u.isUnit
    refine ⟨hrUnit.unit, Units.ext ?_⟩
    simp only [Units.val_mul, IsUnit.unit_spec]
    exact hr
  · exact fun h => h.map (Units.coeHom R)

noncomputable def primePowerReductionUnit (p k : ℕ) (hk : 0 < k) :
    (ZMod (p ^ k))ˣ →* (ZMod p)ˣ :=
  ZMod.unitsMap (dvd_pow_self p hk.ne')

theorem primePowerReductionUnit_coe
    (p k : ℕ) (hk : 0 < k) [NeZero (p ^ k)] (u : (ZMod (p ^ k))ˣ) :
    ((primePowerReductionUnit p k hk u : (ZMod p)ˣ) : ZMod p) =
      primePowerReduction p k hk (u : ZMod (p ^ k)) := by
  simp [primePowerReductionUnit, primePowerReduction, ZMod.unitsMap_val,
    ZMod.castHom_apply]

theorem isSquare_unit_primePower_iff_reduction
    {p k : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) (hk : 0 < k)
    (u : (ZMod (p ^ k))ˣ) :
    IsSquare u ↔ IsSquare (primePowerReductionUnit p k hk u) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  constructor
  · exact fun h => h.map (primePowerReductionUnit p k hk)
  · intro h
    apply (isSquare_coe_unit_iff u).mp
    apply isSquare_primePower_of_reduction hp hpodd hk
    · rw [← primePowerReductionUnit_coe]
      exact Units.ne_zero _
    · rw [← primePowerReductionUnit_coe]
      exact (isSquare_coe_unit_iff _).mpr h

theorem isSquare_unit_primePower_mul_iff
    {p k : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) (hk : 0 < k)
    (a b : (ZMod (p ^ k))ˣ) :
    IsSquare (a * b) ↔ (IsSquare a ↔ IsSquare b) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  rw [isSquare_unit_primePower_iff_reduction hp hpodd hk,
    isSquare_unit_primePower_iff_reduction hp hpodd hk,
    isSquare_unit_primePower_iff_reduction hp hpodd hk, map_mul]
  rw [← isSquare_coe_unit_iff, ← isSquare_coe_unit_iff, ← isSquare_coe_unit_iff]
  simp only [Units.val_mul]
  exact finiteField_isSquare_mul_iff (Units.ne_zero _) (Units.ne_zero _)

theorem isSquare_unit_mul_inv_iff_not
    {p k : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) (hk : 0 < k)
    (x t : (ZMod (p ^ k))ˣ) (ht : ¬IsSquare t) :
    IsSquare (x * t⁻¹) ↔ ¬IsSquare x := by
  rw [isSquare_unit_primePower_mul_iff hp hpodd hk, isSquare_inv]
  simp [ht]

theorem isSquare_unit_inv_mul_iff_of_isSquare
    {G : Type*} [CommGroup G] (x t : G) (ht : IsSquare t) :
    IsSquare (t⁻¹ * x) ↔ IsSquare x := by
  simpa [mul_comm] using isSquare_mul_inv_iff_of_isSquare x t ht

theorem isSquare_unit_inv_mul_iff_not
    {p k : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) (hk : 0 < k)
    (x t : (ZMod (p ^ k))ˣ) (ht : ¬IsSquare t) :
    IsSquare (t⁻¹ * x) ↔ ¬IsSquare x := by
  simpa [mul_comm] using isSquare_unit_mul_inv_iff_not hp hpodd hk x t ht

theorem exists_unit_sq_ne_one_neg_one
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∃ w : (ZMod p)ˣ, w ^ 2 ≠ 1 ∧ w ^ 2 ≠ -1 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  classical
  let bad : Finset (ZMod p)ˣ := Finset.univ.filter fun w => w ^ 2 = 1 ∨ w ^ 2 = -1
  have hbadcard : bad.card ≤ 4 := by
    by_cases hi : ∃ i : (ZMod p)ˣ, i ^ 2 = -1
    · rcases hi with ⟨i, hi⟩
      have hsub : bad ⊆ {1, -1, i, -i} := by
        intro w hw
        simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hw
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases hw with h | h
        · have hsq : w ^ 2 = (1 : (ZMod p)ˣ) ^ 2 := by simpa using h
          rcases Units.sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · have hsq : w ^ 2 = i ^ 2 := h.trans hi.symm
          rcases Units.sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hwi | hwi
          · exact Or.inr (Or.inr (Or.inl hwi))
          · exact Or.inr (Or.inr (Or.inr hwi))
      calc
        bad.card ≤ ({1, -1, i, -i} : Finset (ZMod p)ˣ).card := Finset.card_le_card hsub
        _ ≤ 4 := by
          have h1 := Finset.card_insert_le (1 : (ZMod p)ˣ) {-1, i, -i}
          have h2 := Finset.card_insert_le (-1 : (ZMod p)ˣ) {i, -i}
          have h3 := Finset.card_insert_le i ({-i} : Finset (ZMod p)ˣ)
          simp only [Finset.card_singleton] at h1 h2 h3
          omega
    · have hsub : bad ⊆ {1, -1} := by
        intro w hw
        simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hw
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases hw with h | h
        · have hsq : w ^ 2 = (1 : (ZMod p)ˣ) ^ 2 := by simpa using h
          exact Units.sq_eq_sq_iff_eq_or_eq_neg.mp hsq
        · exact False.elim (hi ⟨w, h⟩)
      calc
        bad.card ≤ ({1, -1} : Finset (ZMod p)ˣ).card := Finset.card_le_card hsub
        _ ≤ 4 := by
          have h1 := Finset.card_insert_le (1 : (ZMod p)ˣ) {-1}
          simp only [Finset.card_singleton] at h1
          omega
  have hnot : ¬(Finset.univ : Finset (ZMod p)ˣ) ⊆ bad := by
    intro hsub
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ, ZMod.card_units_eq_totient, Nat.totient_prime hp] at hle
    omega
  rw [Finset.not_subset] at hnot
  rcases hnot with ⟨w, hwuniv, hwbad⟩
  refine ⟨w, ?_⟩
  simpa only [bad, Finset.mem_filter, Finset.mem_univ, true_and, not_or] using hwbad

theorem isUnit_primePower_of_reduction_ne_zero
    {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (x : ZMod (p ^ k))
    (hx : primePowerReduction p k hk x ≠ 0) : IsUnit x := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_natCast_iff_not_dvd_pow hp hk]
  intro hdiv
  apply hx
  unfold primePowerReduction
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  exact (ZMod.natCast_eq_zero_iff x.val p).2 hdiv

theorem exists_nonzero_square_with_square_one_add
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∃ a : ZMod p, a ≠ 0 ∧ 1 + a ≠ 0 ∧ IsSquare a ∧ IsSquare (1 + a) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  rcases exists_unit_sq_ne_one_neg_one hp hp7 with ⟨w, hw1, hwm1⟩
  let wr : ZMod p := w
  let x : ZMod p := (wr - wr⁻¹) / 2
  let y : ZMod p := (wr + wr⁻¹) / 2
  have hp2 : p ≠ 2 := by omega
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have hple : p ≤ 2 := Nat.le_of_dvd (by omega) hdiv
    omega
  have hwr : wr ≠ 0 := Units.ne_zero w
  have hx : x ≠ 0 := by
    intro hx0
    have hnum : wr - wr⁻¹ = 0 := by
      apply (div_eq_zero_iff).mp hx0 |>.resolve_right htwo
    have heq : wr = wr⁻¹ := sub_eq_zero.mp hnum
    apply hw1
    apply Units.ext
    change wr ^ 2 = (1 : ZMod p)
    calc
      wr ^ 2 = wr * wr := pow_two wr
      _ = wr * wr⁻¹ := congrArg (fun z => wr * z) heq
      _ = 1 := mul_inv_cancel₀ hwr
  have hy : y ≠ 0 := by
    intro hy0
    have hnum : wr + wr⁻¹ = 0 := by
      apply (div_eq_zero_iff).mp hy0 |>.resolve_right htwo
    have heq : wr = -wr⁻¹ := eq_neg_of_add_eq_zero_left hnum
    apply hwm1
    apply Units.ext
    change wr ^ 2 = (-1 : ZMod p)
    calc
      wr ^ 2 = wr * wr := pow_two wr
      _ = wr * (-wr⁻¹) := congrArg (fun z => wr * z) heq
      _ = -1 := by rw [mul_neg, mul_inv_cancel₀ hwr]
  have hyx : y ^ 2 = 1 + x ^ 2 := by
    dsimp only [x, y]
    field_simp
    ring
  refine ⟨x ^ 2, pow_ne_zero 2 hx, ?_, IsSquare.sq x, ?_⟩
  · rw [← hyx]
    exact pow_ne_zero 2 hy
  · rw [← hyx]
    exact IsSquare.sq y

section Orbit

variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]

def squareUnitFinset : Finset Rˣ :=
  Finset.univ.filter fun u => IsSquare u

def unitOrbit (tau : Fin 3 → Rˣ) : Multiset (Fin 3 → R) :=
  squareUnitFinset.val.map fun (u : Rˣ) i => ((u * tau i : Rˣ) : R)

def unitConstOrbit (c : Rˣ) : Multiset (Fin 3 → R) :=
  squareUnitFinset.val.map fun (u : Rˣ) _ => ((c * u : Rˣ) : R)

def twiceConstOrbit : Multiset (Fin 3 → R) :=
  squareUnitFinset.val.map fun (u : Rˣ) _ => (2 : R) * (u : R)

theorem rootedMultiplicity_unitOrbit (tau : Fin 3 → Rˣ) (i : Fin 3) (x : R) :
    rootedMultiplicity (unitOrbit tau) i x =
      ((squareUnitFinset : Finset Rˣ).filter fun u => ((u * tau i : Rˣ) : R) = x).card := by
  rw [rootedMultiplicity, unitOrbit, Multiset.filter_map]
  simp only [Multiset.card_map]
  change (Multiset.filter (fun u : Rˣ => ((u * tau i : Rˣ) : R) = x)
      squareUnitFinset.val).card =
    (((squareUnitFinset : Finset Rˣ).filter fun u => ((u * tau i : Rˣ) : R) = x).val).card
  rfl

theorem rootedMultiplicity_twiceConstOrbit (i : Fin 3) (x : R) :
    rootedMultiplicity (twiceConstOrbit : Multiset (Fin 3 → R)) i x =
      ((squareUnitFinset : Finset Rˣ).filter fun (u : Rˣ) => (2 : R) * (u : R) = x).card := by
  rw [rootedMultiplicity, twiceConstOrbit, Multiset.filter_map]
  simp only [Multiset.card_map]
  change (Multiset.filter (fun u : Rˣ => (2 : R) * (u : R) = x)
      squareUnitFinset.val).card =
    (((squareUnitFinset : Finset Rˣ).filter fun (u : Rˣ) =>
      (2 : R) * (u : R) = x).val).card
  rfl

theorem rootedMultiplicity_unitOrbit_coe (tau : Fin 3 → Rˣ) (i : Fin 3) (x : Rˣ) :
    rootedMultiplicity (unitOrbit tau) i (x : R) =
      if IsSquare (x * (tau i)⁻¹) then 1 else 0 := by
  rw [rootedMultiplicity_unitOrbit]
  classical
  let u : Rˣ := x * (tau i)⁻¹
  change ((squareUnitFinset : Finset Rˣ).filter fun z =>
      ((z * tau i : Rˣ) : R) = (x : R)).card = if IsSquare u then 1 else 0
  by_cases hu : IsSquare u
  · rw [if_pos hu]
    have hset : ((squareUnitFinset : Finset Rˣ).filter fun z =>
        ((z * tau i : Rˣ) : R) = (x : R)) = {u} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        squareUnitFinset, u]
      constructor
      · intro h
        apply Units.ext
        have heq := congrArg (fun y : R => y * (((tau i)⁻¹ : Rˣ) : R)) h.2
        simpa [u, mul_assoc] using heq
      · intro h
        subst z
        refine ⟨hu, ?_⟩
        simp [mul_assoc]
    rw [hset]
    simp
  · rw [if_neg hu]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_of_forall_notMem
    intro z h
    simp only [Finset.mem_filter, squareUnitFinset, Finset.mem_univ, true_and] at h
    apply hu
    have hz : z = u := by
      apply Units.ext
      have heq := congrArg (fun y : R => y * (((tau i)⁻¹ : Rˣ) : R)) h.2
      simpa [u, mul_assoc] using heq
    simpa [hz] using h.1

theorem rootedMultiplicity_unitConstOrbit_coe (c : Rˣ) (i : Fin 3) (x : Rˣ) :
    rootedMultiplicity (unitConstOrbit c) i (x : R) =
      if IsSquare (c⁻¹ * x) then 1 else 0 := by
  have hrewrite : unitConstOrbit c = unitOrbit (fun _ => c) := by
    apply Multiset.map_congr rfl
    intro u hu
    funext j
    simp [mul_comm]
  rw [hrewrite, rootedMultiplicity_unitOrbit_coe]
  congr 2
  simp [mul_comm]

theorem rootedMultiplicity_unitOrbit_nonunit (tau : Fin 3 → Rˣ) (i : Fin 3) (x : R)
    (hx : ¬IsUnit x) : rootedMultiplicity (unitOrbit tau) i x = 0 := by
  rw [rootedMultiplicity_unitOrbit]
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_of_forall_notMem
  intro u hu
  simp only [Finset.mem_filter] at hu
  apply hx
  rw [← hu.2]
  exact (u * tau i).isUnit

theorem rootedMultiplicity_unitConstOrbit_nonunit (c : Rˣ) (i : Fin 3) (x : R)
    (hx : ¬IsUnit x) : rootedMultiplicity (unitConstOrbit c) i x = 0 := by
  have hrewrite : unitConstOrbit c = unitOrbit (fun _ => c) := by
    apply Multiset.map_congr rfl
    intro u hu
    funext j
    simp [mul_comm]
  rw [hrewrite]
  exact rootedMultiplicity_unitOrbit_nonunit _ _ _ hx

theorem rootedMultiplicity_add (F G : Multiset (Fin 3 → R)) (i : Fin 3) (x : R) :
    rootedMultiplicity (F + G) i x =
      rootedMultiplicity F i x + rootedMultiplicity G i x := by
  simp [rootedMultiplicity]


def orbitSixCover (tau : Fin 3 → Rˣ) (c : Rˣ) : Multiset (Fin 3 → R) :=
  unitOrbit tau + unitOrbit tau + unitOrbit tau + unitConstOrbit c

def orbitThreeCover (tau : Fin 3 → Rˣ) (c : Rˣ) : Multiset (Fin 3 → R) :=
  unitOrbit tau + unitConstOrbit c

theorem orbitSixCover_unit
    (tau : Fin 3 → Rˣ) (c x : Rˣ)
    (h0 : IsSquare (x * (tau 0)⁻¹) ↔ ¬IsSquare x)
    (h1 : IsSquare (x * (tau 1)⁻¹) ↔ IsSquare x)
    (h2 : IsSquare (x * (tau 2)⁻¹) ↔ IsSquare x)
    (hc : IsSquare (c⁻¹ * x) ↔ ¬IsSquare x) :
    coverMultiplicity (orbitSixCover tau c) (x : R) = 6 := by
  rw [coverMultiplicity_eq_sum_rootedMultiplicity]
  simp only [orbitSixCover, rootedMultiplicity_add]
  rw [Fin.sum_univ_three]
  by_cases hx : IsSquare x <;>
    simp [rootedMultiplicity_unitOrbit_coe, rootedMultiplicity_unitConstOrbit_coe,
      h0, h1, h2, hc, hx]

theorem orbitSixCover_unit_alt
    (tau : Fin 3 → Rˣ) (c x : Rˣ)
    (h0 : IsSquare (x * (tau 0)⁻¹) ↔ IsSquare x)
    (h1 : IsSquare (x * (tau 1)⁻¹) ↔ ¬IsSquare x)
    (h2 : IsSquare (x * (tau 2)⁻¹) ↔ ¬IsSquare x)
    (hc : IsSquare (c⁻¹ * x) ↔ IsSquare x) :
    coverMultiplicity (orbitSixCover tau c) (x : R) = 6 := by
  rw [coverMultiplicity_eq_sum_rootedMultiplicity]
  simp only [orbitSixCover, rootedMultiplicity_add]
  rw [Fin.sum_univ_three]
  by_cases hx : IsSquare x <;>
    simp [rootedMultiplicity_unitOrbit_coe, rootedMultiplicity_unitConstOrbit_coe,
      h0, h1, h2, hc, hx]

theorem orbitSixCover_nonunit (tau : Fin 3 → Rˣ) (c : Rˣ) (x : R)
    (hx : ¬IsUnit x) : coverMultiplicity (orbitSixCover tau c) x = 0 := by
  rw [coverMultiplicity_eq_sum_rootedMultiplicity]
  simp [orbitSixCover, rootedMultiplicity_add,
    rootedMultiplicity_unitOrbit_nonunit _ _ _ hx,
    rootedMultiplicity_unitConstOrbit_nonunit _ _ _ hx]

theorem orbitThreeCover_unit
    (tau : Fin 3 → Rˣ) (c x : Rˣ)
    (h0 : IsSquare (x * (tau 0)⁻¹) ↔ IsSquare x)
    (h1 : IsSquare (x * (tau 1)⁻¹) ↔ IsSquare x)
    (h2 : IsSquare (x * (tau 2)⁻¹) ↔ IsSquare x)
    (hc : IsSquare (c⁻¹ * x) ↔ ¬IsSquare x) :
    coverMultiplicity (orbitThreeCover tau c) (x : R) = 3 := by
  rw [coverMultiplicity_eq_sum_rootedMultiplicity]
  simp only [orbitThreeCover, rootedMultiplicity_add]
  rw [Fin.sum_univ_three]
  by_cases hx : IsSquare x <;>
    simp [rootedMultiplicity_unitOrbit_coe, rootedMultiplicity_unitConstOrbit_coe,
      h0, h1, h2, hc, hx]

theorem orbitThreeCover_unit_alt
    (tau : Fin 3 → Rˣ) (c x : Rˣ)
    (h0 : IsSquare (x * (tau 0)⁻¹) ↔ ¬IsSquare x)
    (h1 : IsSquare (x * (tau 1)⁻¹) ↔ ¬IsSquare x)
    (h2 : IsSquare (x * (tau 2)⁻¹) ↔ ¬IsSquare x)
    (hc : IsSquare (c⁻¹ * x) ↔ IsSquare x) :
    coverMultiplicity (orbitThreeCover tau c) (x : R) = 3 := by
  rw [coverMultiplicity_eq_sum_rootedMultiplicity]
  simp only [orbitThreeCover, rootedMultiplicity_add]
  rw [Fin.sum_univ_three]
  by_cases hx : IsSquare x <;>
    simp [rootedMultiplicity_unitOrbit_coe, rootedMultiplicity_unitConstOrbit_coe,
      h0, h1, h2, hc, hx]

theorem orbitThreeCover_nonunit (tau : Fin 3 → Rˣ) (c : Rˣ) (x : R)
    (hx : ¬IsUnit x) : coverMultiplicity (orbitThreeCover tau c) x = 0 := by
  rw [coverMultiplicity_eq_sum_rootedMultiplicity]
  simp [orbitThreeCover, rootedMultiplicity_add,
    rootedMultiplicity_unitOrbit_nonunit _ _ _ hx,
    rootedMultiplicity_unitConstOrbit_nonunit _ _ _ hx]

def UnitSupplement (F : Multiset (Fin 3 → R)) (D : ℕ) : Prop :=
  ∀ x, coverMultiplicity F x = if IsUnit x then D else 0

theorem orbitSixCover_unitSupplement
    (tau : Fin 3 → Rˣ) (c : Rˣ)
    (h0 : ∀ x : Rˣ, IsSquare (x * (tau 0)⁻¹) ↔ ¬IsSquare x)
    (h1 : ∀ x : Rˣ, IsSquare (x * (tau 1)⁻¹) ↔ IsSquare x)
    (h2 : ∀ x : Rˣ, IsSquare (x * (tau 2)⁻¹) ↔ IsSquare x)
    (hc : ∀ x : Rˣ, IsSquare (c⁻¹ * x) ↔ ¬IsSquare x) :
    UnitSupplement (orbitSixCover tau c) 6 := by
  intro x
  by_cases hx : IsUnit x
  · rw [if_pos hx]
    rcases hx with ⟨u, rfl⟩
    exact orbitSixCover_unit tau c u (h0 u) (h1 u) (h2 u) (hc u)
  · rw [if_neg hx]
    exact orbitSixCover_nonunit tau c x hx

theorem orbitSixCover_unitSupplement_alt
    (tau : Fin 3 → Rˣ) (c : Rˣ)
    (h0 : ∀ x : Rˣ, IsSquare (x * (tau 0)⁻¹) ↔ IsSquare x)
    (h1 : ∀ x : Rˣ, IsSquare (x * (tau 1)⁻¹) ↔ ¬IsSquare x)
    (h2 : ∀ x : Rˣ, IsSquare (x * (tau 2)⁻¹) ↔ ¬IsSquare x)
    (hc : ∀ x : Rˣ, IsSquare (c⁻¹ * x) ↔ IsSquare x) :
    UnitSupplement (orbitSixCover tau c) 6 := by
  intro x
  by_cases hx : IsUnit x
  · rw [if_pos hx]
    rcases hx with ⟨u, rfl⟩
    exact orbitSixCover_unit_alt tau c u (h0 u) (h1 u) (h2 u) (hc u)
  · rw [if_neg hx]
    exact orbitSixCover_nonunit tau c x hx

theorem orbitThreeCover_unitSupplement
    (tau : Fin 3 → Rˣ) (c : Rˣ)
    (h0 : ∀ x : Rˣ, IsSquare (x * (tau 0)⁻¹) ↔ IsSquare x)
    (h1 : ∀ x : Rˣ, IsSquare (x * (tau 1)⁻¹) ↔ IsSquare x)
    (h2 : ∀ x : Rˣ, IsSquare (x * (tau 2)⁻¹) ↔ IsSquare x)
    (hc : ∀ x : Rˣ, IsSquare (c⁻¹ * x) ↔ ¬IsSquare x) :
    UnitSupplement (orbitThreeCover tau c) 3 := by
  intro x
  by_cases hx : IsUnit x
  · rw [if_pos hx]
    rcases hx with ⟨u, rfl⟩
    exact orbitThreeCover_unit tau c u (h0 u) (h1 u) (h2 u) (hc u)
  · rw [if_neg hx]
    exact orbitThreeCover_nonunit tau c x hx

theorem orbitThreeCover_unitSupplement_alt
    (tau : Fin 3 → Rˣ) (c : Rˣ)
    (h0 : ∀ x : Rˣ, IsSquare (x * (tau 0)⁻¹) ↔ ¬IsSquare x)
    (h1 : ∀ x : Rˣ, IsSquare (x * (tau 1)⁻¹) ↔ ¬IsSquare x)
    (h2 : ∀ x : Rˣ, IsSquare (x * (tau 2)⁻¹) ↔ ¬IsSquare x)
    (hc : ∀ x : Rˣ, IsSquare (c⁻¹ * x) ↔ IsSquare x) :
    UnitSupplement (orbitThreeCover tau c) 3 := by
  intro x
  by_cases hx : IsUnit x
  · rw [if_pos hx]
    rcases hx with ⟨u, rfl⟩
    exact orbitThreeCover_unit_alt tau c u (h0 u) (h1 u) (h2 u) (hc u)
  · rw [if_neg hx]
    exact orbitThreeCover_nonunit tau c x hx

theorem isRelHom_square_scale {m : ℕ} [NeZero m]
    (f : Fin 3 → ZMod m) (hf : RelHom K3Rel (SquareSumRel m) f)
    (u : ZMod m) (hu : IsSquare u) :
    RelHom K3Rel (SquareSumRel m) (fun i => u * f i) := by
  intro i j hij
  rcases hf hij with ⟨z, hz⟩
  rcases hu with ⟨w, rfl⟩
  refine ⟨w * z, ?_⟩
  rw [mul_pow, hz]
  ring

theorem unitOrbit_isRelCover {m : ℕ} [NeZero m]
    (tau : Fin 3 → (ZMod m)ˣ)
    (htau : RelHom K3Rel (SquareSumRel m) (fun i => (tau i : ZMod m))) :
    IsRelCover K3Rel (SquareSumRel m) (unitOrbit tau) := by
  intro f hf
  rw [unitOrbit, Multiset.mem_map] at hf
  rcases hf with ⟨u, hu, rfl⟩
  apply isRelHom_square_scale _ htau
  simp only [squareUnitFinset, Finset.mem_val, Finset.mem_filter, Finset.mem_univ,
    true_and] at hu
  exact hu.map (Units.coeHom (ZMod m))

theorem unitConstOrbit_two_isRelCover {m : ℕ} [NeZero m]
    (c : (ZMod m)ˣ) (hc : (c : ZMod m) = 2) :
    IsRelCover K3Rel (SquareSumRel m) (unitConstOrbit c) := by
  intro f hf
  rw [unitConstOrbit, Multiset.mem_map] at hf
  rcases hf with ⟨u, hu, rfl⟩
  apply const_isRelHom_of_isSquare_two_mul
  simp only [squareUnitFinset, Finset.mem_val, Finset.mem_filter, Finset.mem_univ,
    true_and] at hu
  rcases hu with ⟨w, hw⟩
  refine ⟨2 * (w : ZMod m), ?_⟩
  have hwu := congrArg (fun z : (ZMod m)ˣ => (z : ZMod m)) hw
  simp only [Units.val_mul] at hwu
  change 2 * ((c : ZMod m) * (u : ZMod m)) =
    (2 * (w : ZMod m)) * (2 * (w : ZMod m))
  rw [hc, hwu]
  ring

theorem orbitSixCover_isRelCover {m : ℕ} [NeZero m]
    (tau : Fin 3 → (ZMod m)ˣ)
    (htau : RelHom K3Rel (SquareSumRel m) (fun i => (tau i : ZMod m)))
    (c : (ZMod m)ˣ) (hc : (c : ZMod m) = 2) :
    IsRelCover K3Rel (SquareSumRel m) (orbitSixCover tau c) := by
  intro f hf
  simp only [orbitSixCover, Multiset.mem_add] at hf
  rcases hf with ((hf | hf) | hf) | hf
  · exact unitOrbit_isRelCover tau htau f hf
  · exact unitOrbit_isRelCover tau htau f hf
  · exact unitOrbit_isRelCover tau htau f hf
  · exact unitConstOrbit_two_isRelCover c hc f hf

theorem orbitThreeCover_isRelCover {m : ℕ} [NeZero m]
    (tau : Fin 3 → (ZMod m)ˣ)
    (htau : RelHom K3Rel (SquareSumRel m) (fun i => (tau i : ZMod m)))
    (c : (ZMod m)ˣ) (hc : (c : ZMod m) = 2) :
    IsRelCover K3Rel (SquareSumRel m) (orbitThreeCover tau c) := by
  intro f hf
  simp only [orbitThreeCover, Multiset.mem_add] at hf
  rcases hf with hf | hf
  · exact unitOrbit_isRelCover tau htau f hf
  · exact unitConstOrbit_two_isRelCover c hc f hf

theorem primePower_orbitSix_NQQ_N
    {p k : ℕ} [NeZero (p ^ k)] (hp : p.Prime) (hpodd : p ≠ 2) (hk : 0 < k)
    (tau : Fin 3 → (ZMod (p ^ k))ˣ)
    (htau : RelHom K3Rel (SquareSumRel (p ^ k))
      (fun i => (tau i : ZMod (p ^ k))))
    (c : (ZMod (p ^ k))ˣ) (hcval : (c : ZMod (p ^ k)) = 2)
    (ht0 : ¬IsSquare (tau 0)) (ht1 : IsSquare (tau 1))
    (ht2 : IsSquare (tau 2)) (hc : ¬IsSquare c) :
    UnitSupplement (orbitSixCover tau c) 6 ∧
      IsRelCover K3Rel (SquareSumRel (p ^ k)) (orbitSixCover tau c) := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  refine ⟨orbitSixCover_unitSupplement tau c ?_ ?_ ?_ ?_,
    orbitSixCover_isRelCover tau htau c hcval⟩
  · intro x
    exact isSquare_unit_mul_inv_iff_not hp hpodd hk x (tau 0) ht0
  · intro x
    exact isSquare_mul_inv_iff_of_isSquare x (tau 1) ht1
  · intro x
    exact isSquare_mul_inv_iff_of_isSquare x (tau 2) ht2
  · intro x
    exact isSquare_unit_inv_mul_iff_not hp hpodd hk x c hc

theorem primePower_orbitThree_QQQ_N
    {p k : ℕ} [NeZero (p ^ k)] (hp : p.Prime) (hpodd : p ≠ 2) (hk : 0 < k)
    (tau : Fin 3 → (ZMod (p ^ k))ˣ)
    (htau : RelHom K3Rel (SquareSumRel (p ^ k))
      (fun i => (tau i : ZMod (p ^ k))))
    (c : (ZMod (p ^ k))ˣ) (hcval : (c : ZMod (p ^ k)) = 2)
    (ht0 : IsSquare (tau 0)) (ht1 : IsSquare (tau 1))
    (ht2 : IsSquare (tau 2)) (hc : ¬IsSquare c) :
    UnitSupplement (orbitThreeCover tau c) 3 ∧
      IsRelCover K3Rel (SquareSumRel (p ^ k)) (orbitThreeCover tau c) := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  refine ⟨orbitThreeCover_unitSupplement tau c ?_ ?_ ?_ ?_,
    orbitThreeCover_isRelCover tau htau c hcval⟩
  · intro x
    exact isSquare_mul_inv_iff_of_isSquare x (tau 0) ht0
  · intro x
    exact isSquare_mul_inv_iff_of_isSquare x (tau 1) ht1
  · intro x
    exact isSquare_mul_inv_iff_of_isSquare x (tau 2) ht2
  · intro x
    exact isSquare_unit_inv_mul_iff_not hp hpodd hk x c hc

theorem primePower_orbitSix_QNN_Q
    {p k : ℕ} [NeZero (p ^ k)] (hp : p.Prime) (hpodd : p ≠ 2) (hk : 0 < k)
    (tau : Fin 3 → (ZMod (p ^ k))ˣ)
    (htau : RelHom K3Rel (SquareSumRel (p ^ k))
      (fun i => (tau i : ZMod (p ^ k))))
    (c : (ZMod (p ^ k))ˣ) (hcval : (c : ZMod (p ^ k)) = 2)
    (ht0 : IsSquare (tau 0)) (ht1 : ¬IsSquare (tau 1))
    (ht2 : ¬IsSquare (tau 2)) (hc : IsSquare c) :
    UnitSupplement (orbitSixCover tau c) 6 ∧
      IsRelCover K3Rel (SquareSumRel (p ^ k)) (orbitSixCover tau c) := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  refine ⟨orbitSixCover_unitSupplement_alt tau c ?_ ?_ ?_ ?_,
    orbitSixCover_isRelCover tau htau c hcval⟩
  · intro x
    exact isSquare_mul_inv_iff_of_isSquare x (tau 0) ht0
  · intro x
    exact isSquare_unit_mul_inv_iff_not hp hpodd hk x (tau 1) ht1
  · intro x
    exact isSquare_unit_mul_inv_iff_not hp hpodd hk x (tau 2) ht2
  · intro x
    exact isSquare_unit_inv_mul_iff_of_isSquare x c hc

theorem primePower_orbitThree_NNN_Q
    {p k : ℕ} [NeZero (p ^ k)] (hp : p.Prime) (hpodd : p ≠ 2) (hk : 0 < k)
    (tau : Fin 3 → (ZMod (p ^ k))ˣ)
    (htau : RelHom K3Rel (SquareSumRel (p ^ k))
      (fun i => (tau i : ZMod (p ^ k))))
    (c : (ZMod (p ^ k))ˣ) (hcval : (c : ZMod (p ^ k)) = 2)
    (ht0 : ¬IsSquare (tau 0)) (ht1 : ¬IsSquare (tau 1))
    (ht2 : ¬IsSquare (tau 2)) (hc : IsSquare c) :
    UnitSupplement (orbitThreeCover tau c) 3 ∧
      IsRelCover K3Rel (SquareSumRel (p ^ k)) (orbitThreeCover tau c) := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  refine ⟨orbitThreeCover_unitSupplement_alt tau c ?_ ?_ ?_ ?_,
    orbitThreeCover_isRelCover tau htau c hcval⟩
  · intro x
    exact isSquare_unit_mul_inv_iff_not hp hpodd hk x (tau 0) ht0
  · intro x
    exact isSquare_unit_mul_inv_iff_not hp hpodd hk x (tau 1) ht1
  · intro x
    exact isSquare_unit_mul_inv_iff_not hp hpodd hk x (tau 2) ht2
  · intro x
    exact isSquare_unit_inv_mul_iff_of_isSquare x c hc

theorem exists_primePower_unitSupplement_of_two_nonsquare
    {p k : ℕ} [NeZero (p ^ k)] (hp : p.Prime) (hp7 : 7 ≤ p) (hk : 0 < k)
    (h2 : ¬IsSquare (2 : ZMod p)) :
    ∃ (F : Multiset (Fin 3 → ZMod (p ^ k))) (D : ℕ),
      0 < D ∧ UnitSupplement F D ∧
        IsRelCover K3Rel (SquareSumRel (p ^ k)) F := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  have hpodd : p ≠ 2 := by omega
  rcases exists_nonzero_square_with_square_one_add hp hp7 with
    ⟨a, ha0, h1a0, haSq, h1aSq⟩
  obtain ⟨aq, haq⟩ := ZMod.castHom_surjective (dvd_pow_self p hk.ne') a
  have haqred : primePowerReduction p k hk aq = a := by
    simpa [primePowerReduction] using haq
  have h1aqred : primePowerReduction p k hk (1 + aq) = 1 + a := by
    rw [map_add, map_one, haqred]
  have haqUnit : IsUnit aq :=
    isUnit_primePower_of_reduction_ne_zero hp hk aq (haqred ▸ ha0)
  have h1aqUnit : IsUnit (1 + aq) :=
    isUnit_primePower_of_reduction_ne_zero hp hk (1 + aq) (h1aqred ▸ h1a0)
  have haqSq : IsSquare aq :=
    isSquare_primePower_of_reduction hp hpodd hk aq
      (haqred ▸ ha0) (haqred ▸ haSq)
  have h1aqSq : IsSquare (1 + aq) :=
    isSquare_primePower_of_reduction hp hpodd hk (1 + aq)
      (h1aqred ▸ h1a0) (h1aqred ▸ h1aSq)
  let au : (ZMod (p ^ k))ˣ := haqUnit.unit
  let bu : (ZMod (p ^ k))ˣ := h1aqUnit.unit
  let tau : Fin 3 → (ZMod (p ^ k))ˣ
    | 0 => -au
    | 1 => bu
    | 2 => au * bu
  have hauSq : IsSquare au := by
    apply (isSquare_coe_unit_iff au).mp
    simpa [au, IsUnit.unit_spec] using haqSq
  have hbuSq : IsSquare bu := by
    apply (isSquare_coe_unit_iff bu).mp
    simpa [bu, IsUnit.unit_spec] using h1aqSq
  have htau1 : IsSquare (tau 1) := by simpa [tau] using hbuSq
  have htau2 : IsSquare (tau 2) := by
    simpa [tau] using hauSq.mul hbuSq
  have htauRel : RelHom K3Rel (SquareSumRel (p ^ k))
      (fun i => (tau i : ZMod (p ^ k))) := by
    have heq : (fun i => (tau i : ZMod (p ^ k))) = parameterTriangle 1 aq := by
      funext i
      fin_cases i <;> simp [tau, au, bu, parameterTriangle, IsUnit.unit_spec]
    rw [heq]
    intro i j hij
    exact parameterTriangle_zmod_isRelHom (p ^ k) 1 aq hij
  have hpnotdiv2 : ¬p ∣ 2 := by
    intro hdiv
    have hple := Nat.le_of_dvd (by omega) hdiv
    omega
  have htwoUnit : IsUnit (2 : ZMod (p ^ k)) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow hp hk).2 hpnotdiv2
  let c : (ZMod (p ^ k))ˣ := htwoUnit.unit
  have hcval : (c : ZMod (p ^ k)) = 2 := by simp [c, IsUnit.unit_spec]
  have hcNSq : ¬IsSquare c := by
    intro hc
    apply h2
    have hc' : IsSquare (c : ZMod (p ^ k)) := (isSquare_coe_unit_iff c).mpr hc
    have hred := hc'.map (primePowerReduction p k hk)
    have hmap : primePowerReduction p k hk (2 : ZMod (p ^ k)) = (2 : ZMod p) := by
      exact map_ofNat (primePowerReduction p k hk) 2
    rw [hcval, hmap] at hred
    exact hred
  by_cases ht0 : IsSquare (tau 0)
  · refine ⟨orbitThreeCover tau c, 3, by omega, ?_⟩
    exact primePower_orbitThree_QQQ_N hp hpodd hk tau htauRel c hcval
      ht0 htau1 htau2 hcNSq
  · refine ⟨orbitSixCover tau c, 6, by omega, ?_⟩
    exact primePower_orbitSix_NQQ_N hp hpodd hk tau htauRel c hcval
      ht0 htau1 htau2 hcNSq

theorem exists_primePower_unitSupplement_of_two_square
    {p k : ℕ} [NeZero (p ^ k)] (hp : p.Prime) (hp7 : 7 ≤ p) (hk : 0 < k)
    (h2 : IsSquare (2 : ZMod p)) :
    ∃ (F : Multiset (Fin 3 → ZMod (p ^ k))) (D : ℕ),
      0 < D ∧ UnitSupplement F D ∧
        IsRelCover K3Rel (SquareSumRel (p ^ k)) F := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  have hpodd : p ≠ 2 := by omega
  rcases exists_square_add_one_nonsquare hp hpodd with ⟨a, ha0, haSq, h1aNSq⟩
  have h1a0 : 1 + a ≠ 0 := by
    intro hzero
    apply h1aNSq
    rw [hzero]
    exact IsSquare.zero
  obtain ⟨aq, haq⟩ := ZMod.castHom_surjective (dvd_pow_self p hk.ne') a
  have haqred : primePowerReduction p k hk aq = a := by
    simpa [primePowerReduction] using haq
  have h1aqred : primePowerReduction p k hk (1 + aq) = 1 + a := by
    rw [map_add, map_one, haqred]
  have haqUnit : IsUnit aq :=
    isUnit_primePower_of_reduction_ne_zero hp hk aq (haqred ▸ ha0)
  have h1aqUnit : IsUnit (1 + aq) :=
    isUnit_primePower_of_reduction_ne_zero hp hk (1 + aq) (h1aqred ▸ h1a0)
  have haqSq : IsSquare aq :=
    isSquare_primePower_of_reduction hp hpodd hk aq
      (haqred ▸ ha0) (haqred ▸ haSq)
  have h1aqNSq : ¬IsSquare (1 + aq) := by
    intro hs
    apply h1aNSq
    have hred := hs.map (primePowerReduction p k hk)
    rwa [h1aqred] at hred
  let au : (ZMod (p ^ k))ˣ := haqUnit.unit
  let bu : (ZMod (p ^ k))ˣ := h1aqUnit.unit
  let tau : Fin 3 → (ZMod (p ^ k))ˣ
    | 0 => -au
    | 1 => bu
    | 2 => au * bu
  have hauSq : IsSquare au := by
    apply (isSquare_coe_unit_iff au).mp
    simpa [au, IsUnit.unit_spec] using haqSq
  have hbuNSq : ¬IsSquare bu := by
    intro h
    apply h1aqNSq
    simpa [bu, IsUnit.unit_spec] using (isSquare_coe_unit_iff bu).mpr h
  have htau1 : ¬IsSquare (tau 1) := by simpa [tau] using hbuNSq
  have htau2 : ¬IsSquare (tau 2) := by
    intro h
    have hiff := (isSquare_unit_primePower_mul_iff hp hpodd hk au bu).mp
      (by simpa [tau] using h)
    exact hbuNSq (hiff.mp hauSq)
  have htauRel : RelHom K3Rel (SquareSumRel (p ^ k))
      (fun i => (tau i : ZMod (p ^ k))) := by
    have heq : (fun i => (tau i : ZMod (p ^ k))) = parameterTriangle 1 aq := by
      funext i
      fin_cases i <;> simp [tau, au, bu, parameterTriangle, IsUnit.unit_spec]
    rw [heq]
    intro i j hij
    exact parameterTriangle_zmod_isRelHom (p ^ k) 1 aq hij
  have hpnotdiv2 : ¬p ∣ 2 := by
    intro hdiv
    have hple := Nat.le_of_dvd (by omega) hdiv
    omega
  have htwoUnit : IsUnit (2 : ZMod (p ^ k)) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow hp hk).2 hpnotdiv2
  let c : (ZMod (p ^ k))ˣ := htwoUnit.unit
  have hcval : (c : ZMod (p ^ k)) = 2 := by simp [c, IsUnit.unit_spec]
  have hcSq : IsSquare c := by
    apply (isSquare_coe_unit_iff c).mp
    rw [hcval]
    have hmap : primePowerReduction p k hk (2 : ZMod (p ^ k)) = (2 : ZMod p) :=
      map_ofNat (primePowerReduction p k hk) 2
    have htwo0 : (2 : ZMod p) ≠ 0 := by
      intro hzero
      have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
      exact hpnotdiv2 hdiv
    exact isSquare_primePower_of_reduction hp hpodd hk (2 : ZMod (p ^ k))
      (by rw [hmap]; exact htwo0)
      (by rwa [hmap])
  by_cases ht0 : IsSquare (tau 0)
  · refine ⟨orbitSixCover tau c, 6, by omega, ?_⟩
    exact primePower_orbitSix_QNN_Q hp hpodd hk tau htauRel c hcval
      ht0 htau1 htau2 hcSq
  · refine ⟨orbitThreeCover tau c, 3, by omega, ?_⟩
    exact primePower_orbitThree_NNN_Q hp hpodd hk tau htauRel c hcval
      ht0 htau1 htau2 hcSq

theorem exists_primePower_unitSupplement
    {p k : ℕ} [NeZero (p ^ k)] (hp : p.Prime) (hp7 : 7 ≤ p) (hk : 0 < k) :
    ∃ (F : Multiset (Fin 3 → ZMod (p ^ k))) (D : ℕ),
      0 < D ∧ UnitSupplement F D ∧
        IsRelCover K3Rel (SquareSumRel (p ^ k)) F := by
  classical
  by_cases h2 : IsSquare (2 : ZMod p)
  · exact exists_primePower_unitSupplement_of_two_square hp hp7 hk h2
  · exact exists_primePower_unitSupplement_of_two_nonsquare hp hp7 hk h2

/-! ## Completion of the prime-power construction -/

/-- For primes at least seven, scale the primitive family and the unit-only
supplement so that their two incidence profiles add to a constant profile. -/
theorem largePrimePower_hasPositiveTriangleCover
    {p k : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hk : 0 < k) :
    HasPositiveTriangleCover (p ^ k) := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨H, D, hD, hHU, hHR⟩ :=
    exists_primePower_unitSupplement hp hp7 hk
  let phi := Fintype.card (ZMod (p ^ k))ˣ
  let F : Multiset (Fin 3 → ZMod (p ^ k)) :=
    D • broadFamily p k hk + (3 * phi) • H
  have hphi : 0 < phi := by
    dsimp only [phi]
    exact Fintype.card_pos
  refine ⟨pow_ne_zero _ hp.ne_zero, 6 * phi * D, by positivity, F, ?_, ?_⟩
  · intro x
    change coverMultiplicity
      (D • broadFamily p k hk + (3 * phi) • H) x = 6 * phi * D
    rw [coverMultiplicity, Multiset.map_add, Multiset.sum_add,
      Multiset.map_nsmul, Multiset.sum_nsmul,
      Multiset.map_nsmul, Multiset.sum_nsmul]
    change D * coverMultiplicity (broadFamily p k hk) x +
      (3 * phi) * coverMultiplicity H x = 6 * phi * D
    rw [broadFamily_coverMultiplicity hp hk, hHU x]
    by_cases hx : IsUnit x
    · simp only [if_pos hx]
      dsimp only [phi]
      ring
    · simp only [if_neg hx]
      dsimp only [phi]
      ring
  · intro f hf
    change f ∈ D • broadFamily p k hk + (3 * phi) • H at hf
    simp only [Multiset.mem_add, Multiset.mem_nsmul] at hf
    rcases hf with ⟨_, hf⟩ | ⟨_, hf⟩
    · exact broadFamily_isRelCover hk f hf
    · exact hHR f hf

/-- Every positive power of an odd prime has a positive uniform triangle cover. -/
theorem oddPrimePower_hasPositiveTriangleCover
    (p k : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hk : 0 < k) :
    HasPositiveTriangleCover (p ^ k) := by
  by_cases hp3 : p = 3
  · subst p
    exact threePower_hasPositiveTriangleCover hk
  by_cases hp5 : p = 5
  · subst p
    exact fivePower_hasPositiveTriangleCover hk
  have hp7 : 7 ≤ p := by
    have hp2 : 2 ≤ p := hp.two_le
    obtain ⟨m, hm⟩ := hp.odd_of_ne_two hpodd
    omega
  exact largePrimePower_hasPositiveTriangleCover hp hp7 hk

/-- The Lagarias--Odlyzko--Shearer uniform triangle-cover lemma for every odd
modulus, including repeated vertices (loops) in the triangle maps. -/
theorem odd_uniform_triangle_cover (v : ℕ) [NeZero v] (hvodd : Odd v) :
    ∃ D : ℕ, 0 < D ∧ ∃ F : Multiset (Fin 3 → ZMod v),
      UniformCover F D ∧ IsRelCover K3Rel (SquareSumRel v) F := by
  exact odd_uniform_triangle_cover_of_primePowers
    oddPrimePower_hasPositiveTriangleCover v hvodd

end Orbit
end Erdos438
