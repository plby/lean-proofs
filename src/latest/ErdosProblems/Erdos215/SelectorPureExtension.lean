/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos215.SelectorPrimeExtension
import ErdosProblems.Erdos215.SelectorReconstruct
import ErdosProblems.Erdos215.SelectorFlipRoot

/-!
# The pure nontrivial-prime extension

This file carries out the finite prime-extension step when every prime in the
denominator is congruent to one modulo four.  We keep the source's splitting

`d = u * p^a`, `p*d = p^(a+1) * u`, `(p,u)=1`

explicit.  The first lemmas identify the distinguished `p`-primary component
among *all* `PrimaryComponent`s of the enlarged denominator.  This avoids any
dependence on an ordering of a factorization list in the consistency proof.
-/

namespace Erdos215.Selector.PurePrimeExtension

open Erdos215.Selector
open Erdos215.Selector.Modular
open Erdos215.Selector.Final
open Erdos215.Selector.Reconstruct
open Erdos215.Selector.Separation
open Erdos215.Selector.PrimeExtension
open Erdos215.Selector.PartialGood

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- The old pure denominator in the `p`-primary splitting. -/
def oldDenom (p u a : ℕ) : ℕ := u * p ^ a

/-- The enlarged denominator, in the literal order required by
`PrimeExtends`. -/
def newDenom (p u a : ℕ) : ℕ := p * oldDenom p u a

lemma newDenom_eq (p u a : ℕ) :
    newDenom p u a = p ^ (a + 1) * u := by
  simp only [newDenom, oldDenom, pow_succ]
  ac_rfl

lemma oldDenom_ne_zero {p u a : ℕ} (hp : p ≠ 0) (hu : u ≠ 0) :
    oldDenom p u a ≠ 0 := by
  exact Nat.mul_ne_zero hu (pow_ne_zero _ hp)

lemma newDenom_ne_zero {p u a : ℕ} (hp : p ≠ 0) (hu : u ≠ 0) :
    newDenom p u a ≠ 0 := by
  exact Nat.mul_ne_zero hp (oldDenom_ne_zero hp hu)

/-- The full `p^(a+1)` component of the enlarged denominator. -/
def newPrimeComponent (p u a : ℕ) (hp : p.Prime)
    (hcop : Nat.Coprime p u) : PrimaryComponent (newDenom p u a) where
  p := p
  a := a + 1
  D := u
  prime := hp
  exp_pos := Nat.succ_pos a
  factor := newDenom_eq p u a
  coprime := hcop.pow_left (a + 1)

@[simp] lemma newPrimeComponent_q (p u a : ℕ) (hp : p.Prime)
    (hcop : Nat.Coprime p u) :
    (newPrimeComponent p u a hp hcop).q = p ^ (a + 1) := rfl

@[simp] lemma newPrimeComponent_D (p u a : ℕ) (hp : p.Prime)
    (hcop : Nat.Coprime p u) :
    (newPrimeComponent p u a hp hcop).D = u := rfl

private lemma prime_pow_coprime_pow_of_ne {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Nat.Coprime (p ^ a) (q ^ b) := by
  exact (hp.coprime_iff_not_dvd.mpr (fun h ↦
    hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h))).pow a b

/-- Any primary component of `u*p^(a+1)` based at `p` is the whole
`p^(a+1)` component.  The proof uses only coprime cancellation, rather than
factorization exponents. -/
theorem component_q_eq_newPrimePower
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (c : PrimaryComponent (newDenom p u a)) (hcp : c.p = p) :
    c.q = p ^ (a + 1) := by
  let q := p ^ (a + 1)
  have hcbase : c.q = p ^ c.a := by simp only [PrimaryComponent.q, hcp]
  have hcu : Nat.Coprime c.q u := by
    rw [hcbase]
    exact hcop.pow_left c.a
  have hcq : c.q ∣ q := by
    apply hcu.dvd_of_dvd_mul_right
    have hdiv : c.q ∣ newDenom p u a := c.q_dvd
    simpa only [newDenom_eq, q] using hdiv
  have hpD : Nat.Coprime p c.D := by
    have hpq : p ∣ c.q := by
      rw [hcbase]
      exact dvd_pow_self p c.exp_pos.ne'
    exact c.coprime.of_dvd_left hpq
  have hqD : Nat.Coprime q c.D := hpD.pow_left (a + 1)
  have hqc : q ∣ c.q := by
    apply hqD.dvd_of_dvd_mul_right
    have hdiv : q ∣ newDenom p u a := by
      rw [newDenom_eq]
      exact dvd_mul_right q u
    rw [c.factor_q] at hdiv
    exact hdiv
  exact Nat.dvd_antisymm hcq hqc

/-- Every other full primary component divides the complementary factor
`u`. -/
theorem component_q_dvd_complement
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (c : PrimaryComponent (newDenom p u a)) (hcp : c.p ≠ p) :
    c.q ∣ u := by
  have hprimeCop : Nat.Coprime c.p p := by
    exact c.prime.coprime_iff_not_dvd.mpr (fun h ↦
      hcp ((Nat.prime_dvd_prime_iff_eq c.prime hp).mp h))
  have hpowCop : Nat.Coprime c.q (p ^ (a + 1)) := by
    simpa only [PrimaryComponent.q] using hprimeCop.pow c.a (a + 1)
  apply hpowCop.dvd_of_dvd_mul_left
  have hdiv : c.q ∣ newDenom p u a := c.q_dvd
  simpa only [newDenom_eq] using hdiv

/-- Exhaustive primary-component classification for the enlarged pure
denominator. -/
theorem component_classification
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (c : PrimaryComponent (newDenom p u a)) :
    (c.p = p ∧ c.q = p ^ (a + 1)) ∨ (c.p ≠ p ∧ c.q ∣ u) := by
  by_cases hcp : c.p = p
  · exact Or.inl ⟨hcp, component_q_eq_newPrimePower hp hcop c hcp⟩
  · exact Or.inr ⟨hcp, component_q_dvd_complement hp hcop c hcp⟩

lemma complement_ne_zero {p u : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u) :
    u ≠ 0 := by
  intro hu
  subst u
  simp only [Nat.coprime_zero_right] at hcop
  exact hp.ne_one hcop

/-- Canonical finite representative of a residue. -/
def residueFin {n : ℕ} (hn : n ≠ 0) (x : ZMod n) : Fin n :=
  ⟨x.val, by
    let _ : NeZero n := ⟨hn⟩
    exact ZMod.val_lt x⟩

@[simp] lemma residueFin_cast {n : ℕ} (hn : n ≠ 0) (x : ZMod n) :
    (((residueFin hn x : Fin n) : ℕ) : ZMod n) = x := by
  let _ : NeZero n := ⟨hn⟩
  exact ZMod.natCast_zmod_val x

lemma residueFin_injective {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (residueFin hn : ZMod n → Fin n) := by
  intro x y hxy
  have := congrArg (fun z : Fin n ↦ (((z : ℕ) : ZMod n))) hxy
  simpa only [residueFin_cast] using this

/-- Reduction of a root along a divisor of its modulus. -/
def reduceRootOfDvd {m n : ℕ} (h : m ∣ n) (lam : Root n) : Root m :=
  ⟨ZMod.castHom h (ZMod m) lam.1, by
    rw [← map_pow, lam.property]
    rw [map_neg, map_one]⟩

@[simp] lemma reduceRootOfDvd_coe {m n : ℕ} (h : m ∣ n) (lam : Root n) :
    (reduceRootOfDvd h lam : ZMod m) = ZMod.castHom h (ZMod m) lam.1 := rfl

/-- The old denominator divides the enlarged denominator. -/
lemma oldDenom_dvd_newDenom (p u a : ℕ) :
    oldDenom p u a ∣ newDenom p u a := by
  exact dvd_mul_left _ p

/-- Reduction of an enlarged root to the old denominator. -/
def oldRoot (p u a : ℕ) (lam : Root (newDenom p u a)) :
    Root (oldDenom p u a) :=
  reduceRootOfDvd (oldDenom_dvd_newDenom p u a) lam

/-- The canonical old lift copied to all `p²` residue cosets. -/
def copiedLift (p u a : ℕ) (s : LiftData (oldDenom p u a)) :
    LiftData (newDenom p u a) :=
  primeCopyLift p s

theorem copiedLift_primeExtends {p u a : ℕ} (hp : 0 < p)
    (s : LiftData (oldDenom p u a)) :
    PrimeExtends p hp s (copiedLift p u a s) := by
  exact primeCopy_primeExtends p hp s

/-- The explicit quotient guide which moves an input into class zero modulo
`p`; this is the source's function `r` in (4.11). -/
def oldShiftGuide (p u : ℕ) {N : ℕ} (i : Fin N) : ℕ :=
  shiftGuide p u 0 i

lemma oldShiftGuide_zero {p u N : ℕ} (hp : 0 < p)
    (i : Fin N) (hi : i.1 % p = 0) :
    oldShiftGuide p u i = 0 := by
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  have hz : (((⟨0, hp⟩ : Fin p) : ℕ) : ZMod p) = 0 := by
    change ((0 : ℕ) : ZMod p) = 0
    simp
  have h := shiftGuide_zero_mod (u := u) (target := ⟨0, hp⟩) i hi
  rw [hz] at h
  exact h

/-- Raw formula (4.12), before goodness is proved: extend the copied old
line map from the old input class to all inputs. -/
def oldLineExtension (p u a : ℕ) (hp : p ≠ 0) (hu : u ≠ 0)
    (s : LiftData (oldDenom p u a))
    (lam : Root (newDenom p u a)) (jtilde : Fin (newDenom p u a)) :
    Fin (newDenom p u a) → Fin (newDenom p u a) :=
  partialGoodExtension (newDenom p u a) u (oldDenom p u a)
    (oldShiftGuide p u) (inducedFamily (newDenom_ne_zero hp hu)
      (copiedLift p u a s) lam jtilde)

lemma oldLineExtension_eq_on_old_input
    {p u a : ℕ} (hp : 0 < p) (hu : u ≠ 0)
    (s : LiftData (oldDenom p u a))
    (lam : Root (newDenom p u a)) (jtilde i : Fin (newDenom p u a))
    (hi : i.1 % p = 0) :
    oldLineExtension p u a hp.ne' hu s lam jtilde i =
      inducedFamily (newDenom_ne_zero hp.ne' hu)
        (copiedLift p u a s) lam jtilde i := by
  apply partialGoodExtension_eq_on_distinguished
    (oldShiftGuide p u)
    (inducedFamily (newDenom_ne_zero hp.ne' hu) (copiedLift p u a s) lam jtilde)
    (fun x hx ↦ oldShiftGuide_zero hp x hx) i hi

lemma prime_dvd_newDenom (p u a : ℕ) : p ∣ newDenom p u a := by
  exact dvd_mul_right p (oldDenom p u a)

/-- Reduction of an enlarged root modulo the new prime. -/
def primeRoot (p u a : ℕ) (lam : Root (newDenom p u a)) : Root p :=
  reduceRootOfDvd (prime_dvd_newDenom p u a) lam

/-- The line label reduced modulo the new prime. -/
def primeLabel (p : ℕ) {N : ℕ} (jtilde : Fin N) : ZMod p := jtilde.1

lemma primeRoot_isUnit {p u a : ℕ} (lam : Root (newDenom p u a)) :
    IsUnit (primeRoot p u a lam : ZMod p) :=
  root_isUnit (primeRoot p u a lam)

/-- For an odd prime, the two opposite reductions of a root have invertible
difference. -/
lemma primeRoot_sub_neg_isUnit {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (lam : Root (newDenom p u a)) :
    IsUnit ((primeRoot p u a lam : ZMod p) -
      -(primeRoot p u a lam : ZMod p)) := by
  have hcop2 : Nat.Coprime 2 p := by
    exact Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr (fun h ↦
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)))
  have htwo : IsUnit (2 : ZMod p) :=
    (ZMod.isUnit_iff_coprime 2 p).2 hcop2
  have hprod := htwo.mul (primeRoot_isUnit (p := p) (u := u) (a := a) lam)
  convert hprod using 1 <;> ring

/-- The distinguished source residue (4.10), now as a `Fin p`.  The same
formula gives zero for an old line label, so no case split is needed. -/
def distinguishedClass (p u a : ℕ) (hp : p.Prime)
    (lam : Root (newDenom p u a)) (jtilde : Fin (newDenom p u a)) : Fin p :=
  residueFin hp.ne_zero
    (distinguishedResidue (primeRoot p u a lam) (primeLabel p jtilde))

@[simp] lemma distinguishedClass_cast (p u a : ℕ) (hp : p.Prime)
    (lam : Root (newDenom p u a)) (jtilde : Fin (newDenom p u a)) :
    ((distinguishedClass p u a hp lam jtilde : ℕ) : ZMod p) =
      distinguishedResidue (primeRoot p u a lam) (primeLabel p jtilde) := by
  exact residueFin_cast hp.ne_zero _

lemma distinguishedClass_eq_zero_of_oldLabel
    {p u a : ℕ} (hp : p.Prime)
    (lam : Root (newDenom p u a)) (jtilde : Fin (newDenom p u a))
    (hj : jtilde.1 % p = 0) :
    distinguishedClass p u a hp lam jtilde = ⟨0, hp.pos⟩ := by
  let : NeZero p := ⟨hp.ne_zero⟩
  apply Fin.ext
  have hlabel : primeLabel p jtilde = 0 := by
    change ((jtilde.1 : ℕ) : ZMod p) = 0
    rw [← ZMod.natCast_mod jtilde.1 p, hj]
    simp
  simp only [distinguishedClass, distinguishedResidue, hlabel, neg_zero, zero_mul]
  simp [residueFin]

/-- The canonical quotient guide carrying an arbitrary argument to the
line's distinguished source class. -/
def lineShiftGuide (p u a : ℕ) (hp : p.Prime)
    (lam : Root (newDenom p u a)) (jtilde : Fin (newDenom p u a))
    (i : Fin (newDenom p u a)) : ℕ :=
  shiftGuide p u (distinguishedClass p u a hp lam jtilde : ZMod p) i

lemma lineShiftGuide_eq_old_of_oldLabel
    {p u a : ℕ} (hp : p.Prime)
    (lam : Root (newDenom p u a)) (jtilde : Fin (newDenom p u a))
    (hj : jtilde.1 % p = 0) :
    lineShiftGuide p u a hp lam jtilde = oldShiftGuide p u := by
  let : NeZero p := ⟨hp.ne_zero⟩
  funext i
  simp [lineShiftGuide, oldShiftGuide,
    distinguishedClass_eq_zero_of_oldLabel hp lam jtilde hj]

/-- Remove the least base-`p` digit and retain the next `a` digits.  On one
fixed residue class modulo `p`, this is exactly the input of the permutation
`ρ` in (4.14). -/
def primaryDigit (p a : ℕ) (hp : p.Prime) {N : ℕ} (i : Fin N) :
    Fin (p ^ a) :=
  ⟨(i.1 / p) % p ^ a, Nat.mod_lt _ (pow_pos hp.pos a)⟩

@[simp] lemma primaryDigit_val (p a : ℕ) (hp : p.Prime) {N : ℕ}
    (i : Fin N) :
    (primaryDigit p a hp i : ℕ) = (i.1 / p) % p ^ a := rfl

/-- The canonical representative of a line label modulo the enlarged
`p`-power. -/
def primaryLabelRepresentative (p a : ℕ) {N : ℕ} (jtilde : Fin N) : ℕ :=
  jtilde.1 % p ^ (a + 1)

lemma primaryPower_dvd_label_sub (p a : ℕ) {N : ℕ} (jtilde : Fin N) :
    (p ^ (a + 1) : ℤ) ∣
      (jtilde.1 : ℤ) - primaryLabelRepresentative p a jtilde := by
  simp only [primaryLabelRepresentative]
  have hnat : p ^ (a + 1) ∣ jtilde.1 - jtilde.1 % p ^ (a + 1) :=
    Nat.dvd_sub_mod jtilde.1
  obtain ⟨k, hk⟩ := hnat
  refine ⟨(k : ℤ), ?_⟩
  rw [← Int.ofNat_sub (Nat.mod_le _ _), hk]
  push_cast
  rfl

/-- The `p^(a+1)`-coordinate in (4.14), including its indispensable line
constant. -/
def primaryDistinguishedValue
    (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (rho : Equiv.Perm (Fin (p ^ a)))
    (lam : Root (newDenom p u a)) (jtilde i : Fin (newDenom p u a)) :
    ZMod (p ^ (a + 1)) :=
  let cP := newPrimeComponent p u a hp hcop
  (((rho (primaryDigit p a hp i) : Fin (p ^ a)) : ℕ) : ZMod cP.q) -
    cP.reduce lam * cP.localQuotient
      ((jtilde.1 : ℤ) - primaryLabelRepresentative p a jtilde)

/-- The localized quotient for the complementary factor `u` in
`newDenom = u*p^(a+1)`. -/
def complementLocalQuotient (p u a : ℕ) (z : ℤ) : ZMod u :=
  localizedQuotient u ((p ^ (a + 1) : ZMod u))⁻¹ z

lemma complementPower_isUnit {p u a : ℕ} (hcop : Nat.Coprime p u) :
    IsUnit (p ^ (a + 1) : ZMod u) := by
  simpa using ((ZMod.isUnit_iff_coprime (p ^ (a + 1)) u).2
    (hcop.pow_left (a + 1)))

lemma complementLocalQuotient_mul_power
    {p u a : ℕ} (hu : u ≠ 0) (hcop : Nat.Coprime p u) (z : ℤ) :
    complementLocalQuotient p u a z * (p ^ (a + 1) : ZMod u) =
      (z / (u : ℤ) : ℤ) := by
  simp only [complementLocalQuotient, localizedQuotient, mul_assoc]
  rw [ZMod.inv_mul_of_unit _ (complementPower_isUnit hcop)]
  simp

/-- Flip only the enlarged `p^(a+1)` coordinate of a global root. -/
def flippedRoot (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam : Root (newDenom p u a)) : Root (newDenom p u a) :=
  (newPrimeComponent p u a hp hcop).flipRoot lam

@[simp] lemma newPrimeComponent_reduce_flippedRoot
    (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam : Root (newDenom p u a)) :
    (newPrimeComponent p u a hp hcop).reduce
        (flippedRoot p u a hp hcop lam) =
      -(newPrimeComponent p u a hp hcop).reduce lam := by
  exact PrimaryComponent.reduce_flipRoot _ _

@[simp] lemma primeRoot_flippedRoot
    (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam : Root (newDenom p u a)) :
    (primeRoot p u a (flippedRoot p u a hp hcop lam) : ZMod p) =
      -(primeRoot p u a lam : ZMod p) := by
  let cP := newPrimeComponent p u a hp hcop
  let down : ZMod cP.q →+* ZMod p :=
    ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero a)) (ZMod p)
  have hcomp : down.comp cP.reduce =
      ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p) :=
    RingHom.ext_zmod _ _
  change ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p)
      (flippedRoot p u a hp hcop lam).1 =
    -ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p) lam.1
  rw [← DFunLike.congr_fun hcomp, ← DFunLike.congr_fun hcomp]
  change down (cP.reduce (flippedRoot p u a hp hcop lam)) =
    -down (cP.reduce lam)
  rw [newPrimeComponent_reduce_flippedRoot]
  exact map_neg down _

lemma reduce_flippedRoot_eq_of_other_component
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (c : PrimaryComponent (newDenom p u a)) (hcp : c.p ≠ p)
    (lam : Root (newDenom p u a)) :
    c.reduce (flippedRoot p u a hp hcop lam) = c.reduce lam := by
  exact PrimaryComponent.reduce_flipRoot_eq_of_q_dvd_D
    (newPrimeComponent p u a hp hcop) c
    (component_q_dvd_complement hp hcop c hcp) lam

/-- The old auxiliary line label through the point of the original line at
the specified argument.  In residues this is
`J + i*(lambda-flip(lambda))`. -/
def auxiliaryLabel
    (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam : Root (newDenom p u a)) (jtilde i : Fin (newDenom p u a)) :
    Fin (newDenom p u a) :=
  residueFin (newDenom_ne_zero hp.ne_zero
    (complement_ne_zero hp hcop))
    ((((jtilde : ℕ) : ZMod (newDenom p u a)) +
      (((i : ℕ) : ZMod (newDenom p u a)) *
        ((lam : ZMod (newDenom p u a)) -
          (flippedRoot p u a hp hcop lam : ZMod (newDenom p u a))))))

@[simp] lemma auxiliaryLabel_cast
    (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam : Root (newDenom p u a)) (jtilde i : Fin (newDenom p u a)) :
    (((auxiliaryLabel p u a hp hcop lam jtilde i : ℕ) :
        ZMod (newDenom p u a))) =
      ((jtilde : ℕ) : ZMod (newDenom p u a)) +
        ((i : ℕ) : ZMod (newDenom p u a)) *
          ((lam : ZMod (newDenom p u a)) -
            (flippedRoot p u a hp hcop lam : ZMod (newDenom p u a))) := by
  exact residueFin_cast _ _

lemma lineCell_auxiliaryLabel
    (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam : Root (newDenom p u a)) (jtilde i : Fin (newDenom p u a)) :
    lineCell (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
        (flippedRoot p u a hp hcop lam)
        (auxiliaryLabel p u a hp hcop lam jtilde i) i =
      lineCell (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
        lam jtilde i := by
  let hn : newDenom p u a ≠ 0 :=
    newDenom_ne_zero (a := a) hp.ne_zero (complement_ne_zero hp hcop)
  apply fin_eq_of_zmod_cast_eq hn
  simp only [lineCell, lineResidue_cast, auxiliaryLabel_cast]
  ring

lemma auxiliaryLabel_relation
    (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam : Root (newDenom p u a)) (jtilde i : Fin (newDenom p u a)) :
    ((i : ℕ) : ZMod (newDenom p u a)) *
        ((lam : ZMod (newDenom p u a)) -
          (flippedRoot p u a hp hcop lam : ZMod (newDenom p u a))) =
      -((((jtilde : ℕ) : ZMod (newDenom p u a)) -
        ((auxiliaryLabel p u a hp hcop lam jtilde i : ℕ) :
          ZMod (newDenom p u a)))) := by
  rw [auxiliaryLabel_cast]
  ring

lemma complement_dvd_label_sub_auxiliary
    (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam : Root (newDenom p u a)) (jtilde i : Fin (newDenom p u a)) :
    (u : ℤ) ∣ (jtilde.1 : ℤ) -
      (auxiliaryLabel p u a hp hcop lam jtilde i).1 := by
  let cP := newPrimeComponent p u a hp hcop
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ u).mp
  have hrel := congrArg cP.reduceComplement
    (auxiliaryLabel_relation p u a hp hcop lam jtilde i)
  simp only [map_mul, map_sub, map_neg, map_natCast] at hrel
  simp only [flippedRoot] at hrel
  rw [PrimaryComponent.reduceComplement_flipRoot, sub_self, mul_zero] at hrel
  push_cast at hrel ⊢
  exact neg_eq_zero.mp hrel.symm

/-- At the distinguished argument the auxiliary line label is old, i.e. is
divisible by `p`.  This is equation (4.10) with the flipped root. -/
lemma auxiliaryLabel_isOld
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcop : Nat.Coprime p u)
    (lam : Root (newDenom p u a)) (jtilde i : Fin (newDenom p u a))
    (hi : i.1 % p = (distinguishedClass p u a hp lam jtilde : ℕ)) :
    (auxiliaryLabel p u a hp hcop lam jtilde i : ℕ) % p = 0 := by
  have hiCast : ((i.1 : ℕ) : ZMod p) =
      distinguishedResidue (primeRoot p u a lam) (primeLabel p jtilde) := by
    calc
      ((i.1 : ℕ) : ZMod p) = ((i.1 % p : ℕ) : ZMod p) := by
        exact (ZMod.natCast_mod i.1 p).symm
      _ = (((distinguishedClass p u a hp lam jtilde : ℕ) : ℕ) : ZMod p) := by
        rw [hi]
      _ = distinguishedResidue (primeRoot p u a lam) (primeLabel p jtilde) :=
        distinguishedClass_cast p u a hp lam jtilde
  have hunit := primeRoot_sub_neg_isUnit hp hp2 lam
  have hrel := distinguishedResidue_relation
    (primeRoot p u a lam) (primeLabel p jtilde) hunit
  have hcast :
      (((auxiliaryLabel p u a hp hcop lam jtilde i : ℕ) : ℕ) : ZMod p) = 0 := by
    have haux := congrArg
      (ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p))
      (auxiliaryLabel_cast p u a hp hcop lam jtilde i)
    simp only [map_add, map_mul, map_sub, map_natCast] at haux
    have hflip :
        ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p)
            (flippedRoot p u a hp hcop lam).1 =
          -ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p) lam.1 := by
      exact primeRoot_flippedRoot p u a hp hcop lam
    change (((auxiliaryLabel p u a hp hcop lam jtilde i : ℕ) : ℕ) : ZMod p) = 0
    rw [haux, hiCast, hflip]
    change primeLabel p jtilde +
      distinguishedResidue (primeRoot p u a lam) (primeLabel p jtilde) *
        ((primeRoot p u a lam : ZMod p) - -(primeRoot p u a lam : ZMod p)) = 0
    rw [hrel]
    exact add_neg_cancel _
  exact Nat.dvd_iff_mod_eq_zero.mp ((ZMod.natCast_eq_zero_iff
    (auxiliaryLabel p u a hp hcop lam jtilde i : ℕ) p).mp hcast)

/-- If the entire enlarged `p`-power divides an input difference, the two
canonical auxiliary old labels coincide.  The `p`-coordinate vanishes by
the input hypothesis and the complementary coordinate vanishes because the
flipped root is unchanged there. -/
lemma auxiliaryLabel_eq_of_primaryPower_dvd_indexDiff
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam : Root (newDenom p u a)) (jtilde i₁ i₂ : Fin (newDenom p u a))
    (hpow : p ^ (a + 1) ∣ indexDiff i₁ i₂) :
    auxiliaryLabel p u a hp hcop lam jtilde i₁ =
      auxiliaryLabel p u a hp hcop lam jtilde i₂ := by
  let cP := newPrimeComponent p u a hp hcop
  have hmod : i₁.1 ≡ i₂.1 [MOD p ^ (a + 1)] := by
    rw [Nat.modEq_iff_dvd]
    have hz : (p ^ (a + 1) : ℤ) ∣
        (i₂.1 : ℤ) - (i₁.1 : ℤ) := by
      rw [← Int.natAbs_dvd_natAbs]
      have habs : Int.natAbs ((i₂.1 : ℤ) - i₁.1) =
          Int.natAbs ((i₁.1 : ℤ) - i₂.1) := by
        rw [show ((i₂.1 : ℤ) - i₁.1) = -((i₁.1 : ℤ) - i₂.1) by ring,
          Int.natAbs_neg]
      rw [Int.natAbs_pow, Int.natAbs_natCast, habs]
      exact hpow
    exact_mod_cast hz
  have hiq : (i₁.1 : ZMod cP.q) = (i₂.1 : ZMod cP.q) := by
    exact (ZMod.natCast_eq_natCast_iff _ _ cP.q).2 hmod
  apply fin_eq_of_zmod_cast_eq
    (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
  rw [auxiliaryLabel_cast, auxiliaryLabel_cast]
  congr 1
  apply cP.split.injective
  apply Prod.ext
  · rw [cP.split_fst_eq_reduce, cP.split_fst_eq_reduce]
    simp only [map_mul, map_sub, map_natCast]
    rw [hiq]
  · rw [cP.split_snd_eq_reduceComplement, cP.split_snd_eq_reduceComplement]
    simp only [map_mul, map_sub, map_natCast]
    change _ * (cP.reduceComplement lam - cP.reduceComplement (cP.flipRoot lam)) =
      _ * (cP.reduceComplement lam - cP.reduceComplement (cP.flipRoot lam))
    rw [cP.reduceComplement_flipRoot, sub_self, mul_zero, mul_zero]

/-- The complementary CRT coordinate of (4.13), using the canonical root
which is flipped only at the new prime power. -/
def complementDistinguishedValue
    (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (s : LiftData (oldDenom p u a))
    (lam : Root (newDenom p u a)) (jtilde i : Fin (newDenom p u a)) :
    ZMod u :=
  let cP := newPrimeComponent p u a hp hcop
  let mu := flippedRoot p u a hp hcop lam
  let jt := auxiliaryLabel p u a hp hcop lam jtilde i
  (show ZMod u from cP.reduceComplement
      (((oldLineExtension p u a hp.ne_zero (complement_ne_zero hp hcop)
        s mu jt i : Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a))) -
    (show ZMod u from cP.reduceComplement lam) * complementLocalQuotient p u a
      ((jtilde.1 : ℤ) - (jt.1 : ℤ))

/-- CRT combination of (4.13) and (4.14) on the distinguished input class. -/
def distinguishedValue
    (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (rho : Equiv.Perm (Fin (p ^ a)))
    (s : LiftData (oldDenom p u a))
    (lam : Root (newDenom p u a)) (jtilde i : Fin (newDenom p u a)) :
    Fin (newDenom p u a) :=
  let cP := newPrimeComponent p u a hp hcop
  residueFin (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
    (cP.combine
      (primaryDistinguishedValue p u a hp hcop rho lam jtilde i)
      (complementDistinguishedValue p u a hp hcop s lam jtilde i))

@[simp] lemma distinguishedValue_split
    (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (rho : Equiv.Perm (Fin (p ^ a)))
    (s : LiftData (oldDenom p u a))
    (lam : Root (newDenom p u a)) (jtilde i : Fin (newDenom p u a)) :
    (newPrimeComponent p u a hp hcop).split
        ((((distinguishedValue p u a hp hcop rho s lam jtilde i :
          Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a))) =
      (primaryDistinguishedValue p u a hp hcop rho lam jtilde i,
        complementDistinguishedValue p u a hp hcop s lam jtilde i) := by
  rw [distinguishedValue, residueFin_cast]
  exact PrimaryComponent.split_combine _ _ _

/-- Formula (4.15): extend the distinguished-class values to a full line
map by the same explicit partial-good extension used in Lemma 4.8. -/
def newLineExtension
    (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (rho : Equiv.Perm (Fin (p ^ a)))
    (s : LiftData (oldDenom p u a))
    (lam : Root (newDenom p u a)) (jtilde : Fin (newDenom p u a)) :
    Fin (newDenom p u a) → Fin (newDenom p u a) :=
  partialGoodExtension (newDenom p u a) u (oldDenom p u a)
    (lineShiftGuide p u a hp lam jtilde)
    (distinguishedValue p u a hp hcop rho s lam jtilde)

lemma lineShiftGuide_zero_on_distinguished
    {p u a : ℕ} (hp : p.Prime)
    (lam : Root (newDenom p u a)) (jtilde i : Fin (newDenom p u a))
    (hi : i.1 % p = (distinguishedClass p u a hp lam jtilde : ℕ)) :
    lineShiftGuide p u a hp lam jtilde i = 0 := by
  exact shiftGuide_zero_mod (u := u)
    (distinguishedClass p u a hp lam jtilde) i hi

lemma newLineExtension_eq_on_distinguished
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (rho : Equiv.Perm (Fin (p ^ a)))
    (s : LiftData (oldDenom p u a))
    (lam : Root (newDenom p u a)) (jtilde i : Fin (newDenom p u a))
    (hi : i.1 % p = (distinguishedClass p u a hp lam jtilde : ℕ)) :
    newLineExtension p u a hp hcop rho s lam jtilde i =
      distinguishedValue p u a hp hcop rho s lam jtilde i := by
  apply partialGoodExtension_eq_on_distinguished
    (lineShiftGuide p u a hp lam jtilde)
    (distinguishedValue p u a hp hcop rho s lam jtilde)
    (fun x hx ↦ lineShiftGuide_zero_on_distinguished hp lam jtilde x hx)
    i hi

/-- The complete raw line family at the enlarged denominator. -/
def extendedFamily
    (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (rho : Equiv.Perm (Fin (p ^ a)))
    (s : LiftData (oldDenom p u a)) : RawLineFamily (newDenom p u a) :=
  fun lam jtilde ↦
    if jtilde.1 % p = 0 then
      oldLineExtension p u a hp.ne_zero (complement_ne_zero hp hcop) s lam jtilde
    else
      newLineExtension p u a hp hcop rho s lam jtilde

lemma extendedFamily_old
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (rho : Equiv.Perm (Fin (p ^ a)))
    (s : LiftData (oldDenom p u a))
    (lam : Root (newDenom p u a)) (jtilde : Fin (newDenom p u a))
    (hj : jtilde.1 % p = 0) :
    extendedFamily p u a hp hcop rho s lam jtilde =
      oldLineExtension p u a hp.ne_zero (complement_ne_zero hp hcop) s lam jtilde := by
  simp only [extendedFamily, if_pos hj]

lemma extendedFamily_new
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (rho : Equiv.Perm (Fin (p ^ a)))
    (s : LiftData (oldDenom p u a))
    (lam : Root (newDenom p u a)) (jtilde : Fin (newDenom p u a))
    (hj : jtilde.1 % p ≠ 0) :
    extendedFamily p u a hp hcop rho s lam jtilde =
      newLineExtension p u a hp hcop rho s lam jtilde := by
  simp only [extendedFamily, if_neg hj]

/-- The target line label of the line through an old cell. -/
def oldCellLineLabel
    (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam : Root (newDenom p u a)) (i j : Fin (oldDenom p u a)) :
    Fin (newDenom p u a) :=
  cellLineLabel (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop)) lam
    (oldIndex p hp.pos i) (oldIndex p hp.pos j)

lemma oldIndex_mod_prime
    {p d : ℕ} (hp : 0 < p) (i : Fin d) :
    (oldIndex p hp i : ℕ) % p = 0 := by
  simp only [oldIndex, Nat.mul_mod_right]

lemma oldCellLineLabel_isOld
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam : Root (newDenom p u a)) (i j : Fin (oldDenom p u a)) :
    (oldCellLineLabel p u a hp hcop lam i j : ℕ) % p = 0 := by
  let N := newDenom p u a
  let jt := oldCellLineLabel p u a hp hcop lam i j
  have hcast : ((jt.1 : ℕ) : ZMod p) = 0 := by
    have hlabel := congrArg (ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p))
      (cellLineLabel_cast
        (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop)) lam
        (oldIndex p hp.pos i) (oldIndex p hp.pos j))
    change ((jt.1 : ℕ) : ZMod p) = 0
    simp only [map_sub, map_mul, map_natCast] at hlabel
    have hi0 : (((oldIndex p hp.pos i : ℕ) : ℕ) : ZMod p) = 0 := by
      apply (ZMod.natCast_eq_zero_iff _ p).2
      exact Nat.dvd_mul_right p i.1
    have hj0 : (((oldIndex p hp.pos j : ℕ) : ℕ) : ZMod p) = 0 := by
      apply (ZMod.natCast_eq_zero_iff _ p).2
      exact Nat.dvd_mul_right p j.1
    rw [hi0, hj0, mul_zero, sub_zero] at hlabel
    exact hlabel
  exact Nat.dvd_iff_mod_eq_zero.mp
    ((ZMod.natCast_eq_zero_iff jt.1 p).mp hcast)

/-- On every root line through an old cell, the enlarged family retains the
copied old induced-family value. -/
lemma extendedFamily_eq_copied_on_old_cell
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (rho : Equiv.Perm (Fin (p ^ a)))
    (s : LiftData (oldDenom p u a))
    (lam : Root (newDenom p u a)) (i j : Fin (oldDenom p u a)) :
    extendedFamily p u a hp hcop rho s lam
        (oldCellLineLabel p u a hp hcop lam i j) (oldIndex p hp.pos i) =
      inducedFamily (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
        (copiedLift p u a s) lam
        (oldCellLineLabel p u a hp hcop lam i j) (oldIndex p hp.pos i) := by
  rw [extendedFamily_old hp hcop rho s lam
    (oldCellLineLabel p u a hp hcop lam i j)
    (oldCellLineLabel_isOld hp hcop lam i j)]
  exact oldLineExtension_eq_on_old_input hp.pos (complement_ne_zero hp hcop)
    s lam (oldCellLineLabel p u a hp hcop lam i j) (oldIndex p hp.pos i)
    (oldIndex_mod_prime hp.pos i)

/-- At an old cell, the target attached to every target root is exactly the
line equation satisfied by the copied old integral lifts. -/
lemma cellTarget_extendedFamily_oldCell
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (rho : Equiv.Perm (Fin (p ^ a)))
    (s : LiftData (oldDenom p u a))
    (lam : Root (newDenom p u a)) (i j : Fin (oldDenom p u a)) :
    cellTarget (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
        (extendedFamily p u a hp hcop rho s) lam
        (oldIndex p hp.pos i) (oldIndex p hp.pos j) =
      ((s.k i j : ℤ) : ZMod (newDenom p u a)) +
        (lam : ZMod (newDenom p u a)) *
          ((s.l i j : ℤ) : ZMod (newDenom p u a)) := by
  let hn : newDenom p u a ≠ 0 :=
    newDenom_ne_zero (a := a) hp.ne_zero (complement_ne_zero hp hcop)
  let I := oldIndex p hp.pos i
  let J := oldIndex p hp.pos j
  let jt := oldCellLineLabel p u a hp hcop lam i j
  have hfamily := congrArg (fun z : Fin (newDenom p u a) ↦
      (((z : Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a)))
    (extendedFamily_eq_copied_on_old_cell hp hcop rho s lam i j)
  have hinduced := inducedFamily_formula hn (copiedLift p u a s) lam jt I
  have hcell : lineCell hn lam jt I = J := lineCell_cellLineLabel hn lam I J
  change lineResidue hn lam jt I = J at hcell
  have hk : (copiedLift p u a s).k I J = s.k i j := by
    exact (primeCopy_primeExtends p hp.pos s i j).1
  have hl : (copiedLift p u a s).l I J = s.l i j := by
    exact (primeCopy_primeExtends p hp.pos s i j).2
  change lineTarget hn (extendedFamily p u a hp hcop rho s) lam jt I = _
  simp only [lineTarget]
  rw [hfamily, hinduced]
  simp only [lineValue, hcell, hk, hl]
  ring

/-- Two opposite-root cell equations determine the reconstructed residues
uniquely. -/
lemma reconstructed_eq_of_opposite_cellTargets
    {d : ℕ} (hd : d ≠ 0) (hodd : Nat.Coprime 2 d)
    (F : RawLineFamily d) (lam₀ : Root d) (i j : Fin d) (k l : ZMod d)
    (hplus : cellTarget hd F lam₀ i j = k + (lam₀ : ZMod d) * l)
    (hminus : cellTarget hd F (negRoot lam₀) i j =
      k + (negRoot lam₀ : ZMod d) * l) :
    reconstructedK hd F lam₀ i j = k ∧ reconstructedL hd F lam₀ i j = l := by
  have hunit := root_sub_negRoot_isUnit hodd lam₀
  have hinv := ZMod.inv_mul_of_unit
    ((lam₀ : ZMod d) - (negRoot lam₀ : ZMod d)) hunit
  have hl : reconstructedL hd F lam₀ i j = l := by
    simp only [reconstructedL, hplus, hminus]
    calc
      ((lam₀ : ZMod d) - (negRoot lam₀ : ZMod d))⁻¹ *
          ((k + (lam₀ : ZMod d) * l) -
            (k + (negRoot lam₀ : ZMod d) * l)) =
          (((lam₀ : ZMod d) - (negRoot lam₀ : ZMod d))⁻¹ *
            ((lam₀ : ZMod d) - (negRoot lam₀ : ZMod d))) * l := by ring
      _ = l := by rw [hinv, one_mul]
  refine ⟨?_, hl⟩
  simp only [reconstructedK, hplus, hl]
  ring

/-- A cell of the enlarged residue square belongs to the literally embedded
old square precisely when both coordinates are divisible by `p`. -/
def IsOldCell (p : ℕ) {N : ℕ} (i j : Fin N) : Prop :=
  i.1 % p = 0 ∧ j.1 % p = 0

private lemma exists_oldIndex_of_zero_mod (p : ℕ) (hp : 0 < p) {d : ℕ}
    (x : Fin (p * d)) (hx : x.1 % p = 0) :
    ∃ i : Fin d, x = oldIndex p hp i := by
  have hpx : p ∣ x.1 := Nat.dvd_iff_mod_eq_zero.mpr hx
  have hlt : x.1 / p < d := by
    apply (Nat.div_lt_iff_lt_mul hp).2
    have hxlt : x.1 < p * d := x.2
    simpa only [Nat.mul_comm] using hxlt
  refine ⟨⟨x.1 / p, hlt⟩, ?_⟩
  apply Fin.ext
  change x.1 = p * (x.1 / p)
  exact (Nat.mul_div_cancel' hpx).symm

/-- Reconstruction from a good consistent family can retain all copied old
integral lifts literally, provided the family has the copied line targets on
old cells. -/
theorem reconstruct_preserving_oldCells
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (hodd : Nat.Coprime 2 (newDenom p u a))
    (C : CompleteComponents (newDenom p u a))
    (hroot : ConflictRootLineProperty (newDenom p u a))
    (F : RawLineFamily (newDenom p u a))
    (hgood : FamilyGood F) (hcons : FamilyConsistent F)
    (lam₀ : Root (newDenom p u a))
    (s : LiftData (oldDenom p u a))
    (htarget : ∀ (lam : Root (newDenom p u a))
      (i j : Fin (oldDenom p u a)),
      cellTarget (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
          F lam (oldIndex p hp.pos i) (oldIndex p hp.pos j) =
        ((s.k i j : ℤ) : ZMod (newDenom p u a)) +
          (lam : ZMod (newDenom p u a)) *
            ((s.l i j : ℤ) : ZMod (newDenom p u a))) :
    ∃ t : LiftData (newDenom p u a),
      PrimeExtends p hp.pos s t ∧ t.Separated := by
  let hn : newDenom p u a ≠ 0 :=
    newDenom_ne_zero (a := a) hp.ne_zero (complement_ne_zero hp hcop)
  let old := copiedLift p u a s
  let r := residueSolution_of_consistent hn hodd F hcons lam₀
    (primaryReductionsDetect_of_complete C hn)
    (rootSignsCovered_of_odd hodd lam₀)
  have hk : ∀ I J, IsOldCell p I J → ((old.k I J : ℤ) :
      ZMod (newDenom p u a)) = r.k I J := by
    intro I J hIJ
    obtain ⟨i, hi⟩ := exists_oldIndex_of_zero_mod p hp.pos I hIJ.1
    obtain ⟨j, hj⟩ := exists_oldIndex_of_zero_mod p hp.pos J hIJ.2
    subst I
    subst J
    have holdk : old.k (oldIndex p hp.pos i) (oldIndex p hp.pos j) = s.k i j :=
      (copiedLift_primeExtends hp.pos s i j).1
    have holdl : old.l (oldIndex p hp.pos i) (oldIndex p hp.pos j) = s.l i j :=
      (copiedLift_primeExtends hp.pos s i j).2
    have hrec := reconstructed_eq_of_opposite_cellTargets hn hodd F lam₀
      (oldIndex p hp.pos i) (oldIndex p hp.pos j)
      (((old.k (oldIndex p hp.pos i) (oldIndex p hp.pos j) : ℤ) :
        ZMod (newDenom p u a)))
      (((old.l (oldIndex p hp.pos i) (oldIndex p hp.pos j) : ℤ) :
        ZMod (newDenom p u a)))
      (by simpa only [holdk, holdl] using htarget lam₀ i j)
      (by simpa only [holdk, holdl] using htarget (negRoot lam₀) i j)
    change ((old.k (oldIndex p hp.pos i) (oldIndex p hp.pos j) : ℤ) :
      ZMod (newDenom p u a)) = reconstructedK hn F lam₀
        (oldIndex p hp.pos i) (oldIndex p hp.pos j)
    exact hrec.1.symm
  have hl : ∀ I J, IsOldCell p I J → ((old.l I J : ℤ) :
      ZMod (newDenom p u a)) = r.l I J := by
    intro I J hIJ
    obtain ⟨i, hi⟩ := exists_oldIndex_of_zero_mod p hp.pos I hIJ.1
    obtain ⟨j, hj⟩ := exists_oldIndex_of_zero_mod p hp.pos J hIJ.2
    subst I
    subst J
    have holdk : old.k (oldIndex p hp.pos i) (oldIndex p hp.pos j) = s.k i j :=
      (copiedLift_primeExtends hp.pos s i j).1
    have holdl : old.l (oldIndex p hp.pos i) (oldIndex p hp.pos j) = s.l i j :=
      (copiedLift_primeExtends hp.pos s i j).2
    have hrec := reconstructed_eq_of_opposite_cellTargets hn hodd F lam₀
      (oldIndex p hp.pos i) (oldIndex p hp.pos j)
      (((old.k (oldIndex p hp.pos i) (oldIndex p hp.pos j) : ℤ) :
        ZMod (newDenom p u a)))
      (((old.l (oldIndex p hp.pos i) (oldIndex p hp.pos j) : ℤ) :
        ZMod (newDenom p u a)))
      (by simpa only [holdk, holdl] using htarget lam₀ i j)
      (by simpa only [holdk, holdl] using htarget (negRoot lam₀) i j)
    change ((old.l (oldIndex p hp.pos i) (oldIndex p hp.pos j) : ℤ) :
      ZMod (newDenom p u a)) = reconstructedL hn F lam₀
        (oldIndex p hp.pos i) (oldIndex p hp.pos j)
    exact hrec.2.symm
  let t := liftDataOfResidueSolutionPreserving r old (IsOldCell p)
  have hrealize : inducedFamily hn t = F :=
    inducedFamily_liftDataOfResidueSolutionPreserving r old (IsOldCell p) hk hl
  refine ⟨t, ?_, separated_of_inducedFamily_eq_good hn hodd hroot t hrealize hgood⟩
  intro i j
  have hpres := liftDataOfResidueSolutionPreserving_eq_old r old (IsOldCell p)
    (oldIndex p hp.pos i) (oldIndex p hp.pos j)
    ⟨oldIndex_mod_prime hp.pos i, oldIndex_mod_prime hp.pos j⟩
  have hcopy := copiedLift_primeExtends hp.pos s i j
  exact ⟨hpres.1.trans hcopy.1, hpres.2.trans hcopy.2⟩

/-- Once goodness and consistency of the explicit family are established,
the resulting selector is a literal separated prime extension. -/
theorem purePrimeExtension_of_family
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (hodd : Nat.Coprime 2 (newDenom p u a))
    (C : CompleteComponents (newDenom p u a))
    (hroot : ConflictRootLineProperty (newDenom p u a))
    (rho : Equiv.Perm (Fin (p ^ a)))
    (s : LiftData (oldDenom p u a))
    (hgood : FamilyGood (extendedFamily p u a hp hcop rho s))
    (hcons : FamilyConsistent (extendedFamily p u a hp hcop rho s))
    (lam₀ : Root (newDenom p u a)) :
    ∃ t : LiftData (newDenom p u a),
      PrimeExtends p hp.pos s t ∧ t.Separated := by
  apply reconstruct_preserving_oldCells hp hcop hodd C hroot
    (extendedFamily p u a hp hcop rho s) hgood hcons lam₀ s
  exact cellTarget_extendedFamily_oldCell hp hcop rho s

end

end Erdos215.Selector.PurePrimeExtension
