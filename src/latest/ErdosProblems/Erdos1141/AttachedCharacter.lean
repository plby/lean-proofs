import Mathlib

/-!
# Jacobi characters at arbitrary multiple moduli

The original public interface remains available to other formalizations.
All results in this module are elementary; no prime-existence theorem is assumed.
-/

namespace Erdos1141

/-- A lightweight paper-facing formalization of “`χ` is a quadratic character modulo `m`”.

This interface is retained for the Jacobi-symbol construction and its users in other problems. -/
structure QuadraticCharacterMod (m : ℕ) where
  toFun : ℕ → ℤ
  periodic : ∀ {a b : ℕ}, Nat.ModEq m a b → toFun a = toFun b
  map_non_coprime : ∀ {a : ℕ}, ¬ Nat.Coprime a m → toFun a = 0
  map_coprime : ∀ {a : ℕ}, Nat.Coprime a m → toFun a = 1 ∨ toFun a = -1
  map_mul : ∀ {a b : ℕ}, Nat.Coprime a m → Nat.Coprime b m →
    toFun (a * b) = toFun a * toFun b

instance {m : ℕ} : CoeFun (QuadraticCharacterMod m) (fun _ ↦ ℕ → ℤ) :=
  ⟨QuadraticCharacterMod.toFun⟩

/-- A quadratic character modulo `m` takes the value `1` at `1`. -/
lemma QuadraticCharacterMod.map_one {m : ℕ} (χ : QuadraticCharacterMod m) : χ 1 = 1 := by
  have hcop : Nat.Coprime 1 m := by
    simp
  rcases χ.map_coprime hcop with h1 | h1
  · exact h1
  · have : False := by
      have hmul : χ (1 * 1) = χ 1 * χ 1 := χ.map_mul (a := 1) (b := 1) hcop hcop
      have hbad : (-1 : ℤ) = 1 := by
        rw [h1] at hmul
        norm_num at hmul
      norm_num at hbad
    exact this.elim

/-- A unit of `ZMod m` has a representative coprime to `m`. -/
lemma natCoprime_val_of_isUnit_zmod {m : ℕ} [NeZero m] {a : ZMod m} (ha : IsUnit a) :
    Nat.Coprime a.val m := by
  rw [← ha.unit_spec]
  exact ZMod.val_coe_unit_coprime ha.unit

/-- A nonunit of `ZMod m` has no representative coprime to `m`. -/
lemma not_natCoprime_val_of_not_isUnit_zmod {m : ℕ} [NeZero m] {a : ZMod m}
    (ha : ¬ IsUnit a) : ¬ Nat.Coprime a.val m := by
  intro hcop
  apply ha
  simpa [ZMod.natCast_zmod_val a] using (ZMod.isUnit_iff_coprime a.val m).2 hcop

/-- Repackage a paper-facing quadratic character as a `DirichletCharacter` over `ℂ`. -/
def QuadraticCharacterMod.toDirichletCharacterComplex {m : ℕ} [NeZero m]
    (χ : QuadraticCharacterMod m) : DirichletCharacter ℂ m where
  toFun a := (χ a.val : ℂ)
  map_one' := by
    have hperiodic : χ ((1 : ZMod m).val) = χ 1 := by
      apply χ.periodic
      rw [← ZMod.natCast_eq_natCast_iff]
      simp
    rw [hperiodic]
    simpa using congrArg (fun z : ℤ => (z : ℂ)) χ.map_one
  map_mul' := by
    intro a b
    by_cases ha : IsUnit a
    · by_cases hb : IsUnit b
      · have hcopa : Nat.Coprime a.val m := natCoprime_val_of_isUnit_zmod ha
        have hcopb : Nat.Coprime b.val m := natCoprime_val_of_isUnit_zmod hb
        have hperiodic : χ ((a * b).val) = χ (a.val * b.val) := by
          apply χ.periodic
          rw [← ZMod.natCast_eq_natCast_iff]
          calc
            (((a * b).val : ℕ) : ZMod m) = a * b := by
              simp
            _ = ((a.val : ZMod m) * (b.val : ZMod m)) := by
              simp
            _ = ((a.val * b.val : ℕ) : ZMod m) := by simp
        have hperiodicC : (χ ((a * b).val) : ℂ) = (χ (a.val * b.val) : ℂ) :=
          congrArg (fun z : ℤ => (z : ℂ)) hperiodic
        rw [hperiodicC]
        simpa using congrArg (fun z : ℤ => (z : ℂ)) (χ.map_mul hcopa hcopb)
      · have hnon : ¬ IsUnit (a * b) := by
          intro hab
          exact hb (isUnit_of_mul_isUnit_right hab)
        have hzero_mul : χ ((a * b).val) = 0 :=
          χ.map_non_coprime (not_natCoprime_val_of_not_isUnit_zmod hnon)
        have hzero_b : χ b.val = 0 :=
          χ.map_non_coprime (not_natCoprime_val_of_not_isUnit_zmod hb)
        simp [hzero_mul, hzero_b]
    · have hnon : ¬ IsUnit (a * b) := by
        intro hab
        exact ha (isUnit_of_mul_isUnit_left hab)
      have hzero_mul : χ ((a * b).val) = 0 :=
        χ.map_non_coprime (not_natCoprime_val_of_not_isUnit_zmod hnon)
      have hzero_a : χ a.val = 0 :=
        χ.map_non_coprime (not_natCoprime_val_of_not_isUnit_zmod ha)
      simp [hzero_mul, hzero_a]
  map_nonunit' := by
    intro a ha
    have hzero : χ a.val = 0 :=
      χ.map_non_coprime (not_natCoprime_val_of_not_isUnit_zmod ha)
    simp [hzero]

@[simp] lemma QuadraticCharacterMod.toDirichletCharacterComplex_apply {m : ℕ} [NeZero m]
    (χ : QuadraticCharacterMod m) (a : ZMod m) :
    χ.toDirichletCharacterComplex a = (χ a.val : ℂ) := rfl

@[simp] lemma QuadraticCharacterMod.toDirichletCharacterComplex_apply_nat
    {m n : ℕ} [NeZero m] (χ : QuadraticCharacterMod m) :
    χ.toDirichletCharacterComplex (n : ZMod m) = (χ n : ℂ) := by
  change ((χ ((n : ZMod m).val) : ℂ) = (χ n : ℂ))
  simpa [ZMod.val_natCast] using
    congrArg (fun z : ℤ => (z : ℂ)) (χ.periodic (Nat.mod_modEq n m))

/-- The associated complex Dirichlet character is quadratic. -/
lemma QuadraticCharacterMod.toDirichletCharacterComplex_isQuadratic
    {m : ℕ} [NeZero m] (χ : QuadraticCharacterMod m) :
    MulChar.IsQuadratic (χ.toDirichletCharacterComplex) := by
  intro a
  by_cases ha : IsUnit a
  · have hcop : Nat.Coprime a.val m := natCoprime_val_of_isUnit_zmod ha
    rcases χ.map_coprime hcop with h1 | hneg
    · right
      left
      simp [h1]
    · right
      right
      simp [hneg]
  · left
    have hcop : ¬ Nat.Coprime a.val m := not_natCoprime_val_of_not_isUnit_zmod ha
    simp [χ.map_non_coprime hcop]

/-- If the associated complex Dirichlet character takes the value `1` at a natural number,
then the original integer-valued character also takes the value `1` there. -/
lemma QuadraticCharacterMod.eq_one_of_toDirichletCharacterComplex_apply_nat_eq_one
    {m n : ℕ} [NeZero m] (χ : QuadraticCharacterMod m)
    (hχ : χ.toDirichletCharacterComplex (n : ZMod m) = (1 : ℂ)) :
    χ n = 1 := by
  have happly : χ.toDirichletCharacterComplex (n : ZMod m) = (χ n : ℂ) :=
    χ.toDirichletCharacterComplex_apply_nat (n := n)
  have hχ' : (χ n : ℂ) = (1 : ℂ) := by
    rw [← happly]
    exact hχ
  by_cases hcop : Nat.Coprime n m
  · rcases χ.map_coprime hcop with h1 | hneg
    · exact h1
    · exfalso
      rw [hneg] at hχ'
      norm_num at hχ'
  · exfalso
    rw [χ.map_non_coprime hcop] at hχ'
    norm_num at hχ'

/-- If `4*d ∣ m`, then `d ∣ m`. -/
lemma d_dvd_of_four_d_dvd {d m : ℕ} (hdvd : 4 * d ∣ m) : d ∣ m := by
  exact dvd_trans (show d ∣ 4 * d by exact ⟨4, by ac_rfl⟩) hdvd

/-- If `4*d ∣ m`, then `2 ∣ m`. -/
lemma two_dvd_of_four_d_dvd {d m : ℕ} (hdvd : 4 * d ∣ m) : 2 ∣ m := by
  exact dvd_trans (show 2 ∣ 4 * d by exact ⟨2 * d, by ac_rfl⟩) hdvd

/-- The quadratic character attached to `d`, viewed modulo any multiple `m` of `4*d`.

On integers coprime to `m` it is the Jacobi symbol `jacobiSym d`; on non-coprime integers it
is `0`.  The congruence invariance modulo `m` comes from `jacobiSym.mod_right`.

This public construction is also used by the formalization of Erdős Problem 1140. -/
def attachedQuadraticCharacter (d m : ℕ) (hdvd : 4 * d ∣ m) :
    QuadraticCharacterMod m where
  toFun n := if Nat.Coprime n m then jacobiSym (d : ℤ) n else 0
  periodic := by
    intro a b hmod
    have hcop : Nat.Coprime a m ↔ Nat.Coprime b m := by
      rw [Nat.coprime_iff_gcd_eq_one, Nat.coprime_iff_gcd_eq_one, hmod.gcd_eq]
    by_cases ha : Nat.Coprime a m
    · have hb : Nat.Coprime b m := hcop.mp ha
      have hmod' : Nat.ModEq (4 * d) a b := hmod.of_dvd hdvd
      have ha2 : Nat.Coprime a 2 := ha.coprime_dvd_right (two_dvd_of_four_d_dvd hdvd)
      have hb2 : Nat.Coprime b 2 := hb.coprime_dvd_right (two_dvd_of_four_d_dvd hdvd)
      have haOdd : Odd a := (Nat.coprime_two_right).1 ha2
      have hbOdd : Odd b := (Nat.coprime_two_right).1 hb2
      have hJ : jacobiSym (d : ℤ) a = jacobiSym (d : ℤ) b := by
        calc
          jacobiSym (d : ℤ) a = jacobiSym (d : ℤ) (a % (4 * d)) := by
            simpa using jacobiSym.mod_right (d : ℤ) haOdd
          _ = jacobiSym (d : ℤ) (b % (4 * d)) := by
            simpa using congrArg (fun t : ℕ ↦ jacobiSym (d : ℤ) t) hmod'
          _ = jacobiSym (d : ℤ) b := by
            simpa using (jacobiSym.mod_right (d : ℤ) hbOdd).symm
      rw [if_pos ha, if_pos hb]
      exact hJ
    · have hb : ¬ Nat.Coprime b m := mt hcop.mpr ha
      rw [if_neg ha, if_neg hb]
  map_non_coprime := by
    intro a ha
    rw [if_neg ha]
  map_coprime := by
    intro a ha
    have had : Nat.Coprime a d := ha.coprime_dvd_right (d_dvd_of_four_d_dvd hdvd)
    have hgcd : Int.gcd (d : ℤ) a = 1 := by
      simpa [Int.gcd_eq_natAbs, Nat.gcd_comm] using had.gcd_eq_one
    rw [if_pos ha]
    exact jacobiSym.eq_one_or_neg_one (a := (d : ℤ)) (b := a) hgcd
  map_mul := by
    intro a b ha hb
    have ha2 : Nat.Coprime a 2 := ha.coprime_dvd_right (two_dvd_of_four_d_dvd hdvd)
    have hb2 : Nat.Coprime b 2 := hb.coprime_dvd_right (two_dvd_of_four_d_dvd hdvd)
    have haOdd : Odd a := (Nat.coprime_two_right).1 ha2
    have hbOdd : Odd b := (Nat.coprime_two_right).1 hb2
    have ha0 : a ≠ 0 := by
      intro h0
      rw [h0] at haOdd
      norm_num at haOdd
    have hb0 : b ≠ 0 := by
      intro h0
      rw [h0] at hbOdd
      norm_num at hbOdd
    split_ifs at * with hab
    · exact jacobiSym.mul_right' (d : ℤ) ha0 hb0
    · exact (hab (Nat.coprime_mul_iff_left.2 ⟨ha, hb⟩)).elim

@[simp] lemma attachedQuadraticCharacter_apply_coprime {d m n : ℕ}
    (hdvd : 4 * d ∣ m) (hn : Nat.Coprime n m) :
    attachedQuadraticCharacter d m hdvd n = jacobiSym (d : ℤ) n := by
  simp [attachedQuadraticCharacter, hn]

@[simp] lemma attachedQuadraticCharacter_apply_not_coprime {d m n : ℕ}
    (hdvd : 4 * d ∣ m) (hn : ¬ Nat.Coprime n m) :
    attachedQuadraticCharacter d m hdvd n = 0 := by
  simp [attachedQuadraticCharacter, hn]

end Erdos1141
