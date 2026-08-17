/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos215.SelectorPartialGood

/-!
The explicit residue shifts used in the nontrivial prime-extension step of
Jackson--Mauldin.  Keeping the chosen digit in `0, ..., p-1` records the
literal representatives required by (4.11), (S6), and (S7).
-/

namespace Erdos215.Selector.PrimeExtension

open Erdos215.Selector
open Erdos215.Selector.PartialGood

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- Reduction of a finite index to its source class modulo `p`. -/
def sourceClass (p : ℕ) {N : ℕ} (i : Fin N) : ZMod p := i.1

/-- The chosen digit `a` for the shift `u*a` carrying `source` to `target`
modulo `p`. -/
def shiftDigit (p u : ℕ) (target source : ZMod p) : ℕ :=
  ((target - source) * (u : ZMod p)⁻¹).val

lemma shiftDigit_lt {p u : ℕ} (hp : p.Prime) (target source : ZMod p) :
    shiftDigit p u target source < p := by
  let _ : NeZero p := ⟨hp.ne_zero⟩
  exact ZMod.val_lt _

@[simp] lemma shiftDigit_cast {p u : ℕ} (hp : p.Prime)
    (target source : ZMod p) :
    (shiftDigit p u target source : ZMod p) =
      (target - source) * (u : ZMod p)⁻¹ := by
  let _ : NeZero p := ⟨hp.ne_zero⟩
  exact ZMod.natCast_zmod_val _

lemma source_add_shiftDigit {p u : ℕ} (hp : p.Prime)
    (hu : Nat.Coprime u p) (target source : ZMod p) :
    source + (u : ZMod p) * (shiftDigit p u target source : ℕ) = target := by
  have hu' : IsUnit (u : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime]
    exact hu
  rw [shiftDigit_cast hp]
  calc
    source + (u : ZMod p) * ((target - source) * (u : ZMod p)⁻¹) =
        source + (target - source) * ((u : ZMod p) * (u : ZMod p)⁻¹) := by ring
    _ = target := by rw [ZMod.mul_inv_of_unit _ hu']; ring

lemma shiftDigit_eq_zero_of_eq {p u : ℕ} (target source : ZMod p)
    (h : source = target) : shiftDigit p u target source = 0 := by
  simp [shiftDigit, h]

/-- The Nat-valued guide function supplied to Lemma 4.8. -/
def shiftGuide {N : ℕ} (p u : ℕ) (target : ZMod p) (i : Fin N) : ℕ :=
  shiftDigit p u target (sourceClass p i)

lemma shiftGuide_constant {N p u : ℕ} (target : ZMod p) (i j : Fin N)
    (h : sourceClass p i = sourceClass p j) :
    shiftGuide p u target i = shiftGuide p u target j := by
  simp [shiftGuide, h]

lemma shiftGuide_zero {N p u : ℕ} (target : ZMod p) (i : Fin N)
    (h : sourceClass p i = target) : shiftGuide p u target i = 0 := by
  exact shiftDigit_eq_zero_of_eq target _ h

lemma shiftGuide_carries {N p u : ℕ} (hp : p.Prime) (hu : Nat.Coprime u p)
    (target : ZMod p) (i : Fin N) :
    sourceClass p i + (u : ZMod p) * (shiftGuide p u target i : ℕ) = target := by
  exact source_add_shiftDigit hp hu target (sourceClass p i)

lemma shiftGuide_constant_mod {N p u : ℕ}
    (target : ZMod p) (i j : Fin N) (h : i.1 % p = j.1 % p) :
    shiftGuide p u target i = shiftGuide p u target j := by
  apply shiftGuide_constant target i j
  unfold sourceClass
  have hcast : ((i.1 : ℕ) : ZMod p) = ((j.1 : ℕ) : ZMod p) := by
    rw [← ZMod.natCast_mod i.1 p, ← ZMod.natCast_mod j.1 p, h]
  exact hcast

lemma shiftGuide_zero_mod {N p u : ℕ} (target : Fin p)
    (i : Fin N) (h : i.1 % p = target.1) :
    shiftGuide p u (target : ZMod p) i = 0 := by
  apply shiftGuide_zero (target : ZMod p) i
  unfold sourceClass
  have hcast : ((i.1 : ℕ) : ZMod p) = ((target.1 : ℕ) : ZMod p) := by
    rw [← ZMod.natCast_mod i.1 p, h]
  exact hcast

lemma partialGoodShift_shiftGuide_mod {N p u n : ℕ} (hp : p.Prime)
    (hn : 0 < n) (hu : Nat.Coprime u p) (hN : N = u * p ^ n)
    (target : Fin p) (i : Fin N) :
    (partialGoodShift N u (shiftGuide p u (target : ZMod p)) i).1 % p = target.1 := by
  have hpN : p ∣ N := by
    rw [hN]
    exact dvd_mul_of_dvd_right (dvd_pow_self p (Nat.ne_of_gt hn)) u
  have hcarry := shiftGuide_carries hp hu (target : ZMod p) i
  have hcast :
      (((partialGoodShift N u (shiftGuide p u (target : ZMod p)) i).1 : ℕ) :
          ZMod p) = (target : ZMod p) := by
    change (((i.1 + u * shiftGuide p u (target : ZMod p) i) % N : ℕ) : ZMod p) = _
    calc
      (((i.1 + u * shiftGuide p u (target : ZMod p) i) % N : ℕ) : ZMod p) =
          ((((i.1 + u * shiftGuide p u (target : ZMod p) i) % N) % p : ℕ) :
            ZMod p) := by
              symm
              exact ZMod.natCast_mod _ _
      _ = (((i.1 + u * shiftGuide p u (target : ZMod p) i) % p : ℕ) :
          ZMod p) := by rw [Nat.mod_mod_of_dvd _ hpN]
      _ = ((i.1 + u * shiftGuide p u (target : ZMod p) i : ℕ) : ZMod p) :=
        ZMod.natCast_mod _ _
      _ = (target : ZMod p) := by
        push_cast
        exact hcarry
  have hv := congrArg ZMod.val hcast
  rw [ZMod.val_natCast,
    ZMod.val_natCast_of_lt target.2] at hv
  exact hv

/-- Lemma 4.8 specialized to the canonical least nonnegative shift guide
from (4.11). -/
theorem exists_goodPerm_to_target
    {N u d p n : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hcop : Nat.Coprime p u) (hpd : N = p * d) (hN : N = u * p ^ n)
    (target : Fin p) (pi : Fin N → Fin N)
    (hpartial : PartialGoodOnClass N p target.1 pi) :
    ∃ sigma : Equiv.Perm (Fin N), GoodPerm N sigma ∧
      ∀ i : Fin N, i.1 % p = target.1 → sigma i = pi i := by
  let q : Fin N → ℕ := shiftGuide p u (target : ZMod p)
  apply exists_goodPerm_extending_partial hp hn hcop hpd hN q pi
  · intro i j hij
    exact shiftGuide_constant_mod (target : ZMod p) i j hij
  · intro i hi
    exact shiftGuide_zero_mod target i hi
  · intro i
    exact partialGoodShift_shiftGuide_mod hp hn hcop.symm hN target i
  · exact hpartial

/-- Scaling both old arguments by the new prime scales their capped
difference by exactly that prime. -/
lemma indexDiff_oldIndex (p : ℕ) (hp : 0 < p) {d : ℕ} (i j : Fin d) :
    indexDiff (oldIndex p hp i) (oldIndex p hp j) = p * indexDiff i j := by
  simp only [indexDiff, oldIndex]
  push_cast
  rw [← mul_sub, Int.natAbs_mul]
  simp

/-- Hence the surviving modulus on the old residue class is literally the
old surviving modulus. -/
lemma survivingModulus_oldIndex (p : ℕ) (hp : 0 < p) {d : ℕ} (i j : Fin d) :
    survivingModulus (p * d)
        (indexDiff (oldIndex p hp i) (oldIndex p hp j)) =
      survivingModulus d (indexDiff i j) := by
  rw [indexDiff_oldIndex]
  simp only [survivingModulus, Nat.gcd_mul_left]
  exact Nat.mul_div_mul_left d (Nat.gcd d (indexDiff i j)) hp

lemma exists_oldIndex_of_mod_eq_zero (p : ℕ) (hp : 0 < p) {d : ℕ}
    (x : Fin (p * d)) (hx : x.1 % p = 0) :
    ∃ i : Fin d, x = oldIndex p hp i := by
  have hpx : p ∣ x.1 := Nat.dvd_iff_mod_eq_zero.mpr hx
  have hlt : x.1 / p < d := by
    apply (Nat.div_lt_iff_lt_mul hp).2
    simpa only [Nat.mul_comm d p] using x.2
  let i : Fin d := ⟨x.1 / p, hlt⟩
  refine ⟨i, ?_⟩
  apply Fin.ext
  change x.1 = p * (x.1 / p)
  exact (Nat.mul_div_cancel' hpx).symm

private lemma int_dvd_sub_iff_natModEq (m a b : ℕ) :
    (m : ℤ) ∣ (a : ℤ) - (b : ℤ) ↔ a ≡ b [MOD m] := by
  rw [Nat.modEq_iff_dvd]
  constructor <;> intro h <;> simpa only [neg_sub] using dvd_neg.mpr h

/-- Any formula on the old class which reduces to a good old map is
partially good at the enlarged denominator.  This is the exact scaling
argument used immediately after (4.9). -/
lemma partialGoodOnOldClass_of_reduces_good
    (p : ℕ) (hp : 0 < p) {d : ℕ} (F : Fin d → Fin d)
    (hF : GoodMap d F) (f : Fin (p * d) → Fin (p * d))
    (hreduce : ∀ i : Fin d, (f (oldIndex p hp i)).1 ≡ (F i).1 [MOD d]) :
    PartialGoodOnClass (p * d) p 0 f := by
  intro x y hx hy hxy
  obtain ⟨i, rfl⟩ := exists_oldIndex_of_mod_eq_zero p hp x hx
  obtain ⟨j, rfl⟩ := exists_oldIndex_of_mod_eq_zero p hp y hy
  have hij : i ≠ j := by
    intro h
    apply hxy
    exact congrArg (oldIndex p hp) h
  rw [survivingModulus_oldIndex]
  let M := survivingModulus d (indexDiff i j)
  have hMd : M ∣ d := survivingModulus_dvd _ _
  intro hbad
  have hbadmod : (f (oldIndex p hp i)).1 ≡
      (f (oldIndex p hp j)).1 [MOD M] :=
    (int_dvd_sub_iff_natModEq _ _ _).mp hbad
  have hiF := (hreduce i).of_dvd hMd
  have hjF := (hreduce j).of_dvd hMd
  have hFF : (F i).1 ≡ (F j).1 [MOD M] :=
    hiF.symm.trans (hbadmod.trans hjF)
  exact hF i j hij ((int_dvd_sub_iff_natModEq _ _ _).mpr hFF)

/-- The distinguished source class in (4.10).  The coefficient is
`lambda - (-lambda)` rather than an abbreviated division by `2*lambda`. -/
def distinguishedResidue {p : ℕ} (lam j : ZMod p) : ZMod p :=
  -j * (lam - -lam)⁻¹

lemma distinguishedResidue_relation {p : ℕ} (lam j : ZMod p)
    (hunit : IsUnit (lam - -lam)) :
    distinguishedResidue lam j * (lam - -lam) = -j := by
  simp only [distinguishedResidue]
  rw [mul_assoc, ZMod.inv_mul_of_unit _ hunit, mul_one]

lemma distinguishedResidue_unique {p : ℕ} (lam j x : ZMod p)
    (hunit : IsUnit (lam - -lam))
    (hx : x * (lam - -lam) = -j) :
    x = distinguishedResidue lam j := by
  apply hunit.mul_right_cancel
  rw [hx, distinguishedResidue_relation lam j hunit]

/-- Algebraic core of (S6)--(S7): the two distinguished source classes add
to the original source class. -/
lemma distinguishedResidue_add_of_opposite
    {p : ℕ} (lam₁ lam₂ j₁ j₂ i : ZMod p)
    (hunit : IsUnit (lam₁ - -lam₁))
    (hopposite : lam₂ = -lam₁)
    (hline : i * (lam₁ - lam₂) = -(j₁ - j₂)) :
    distinguishedResidue lam₁ j₁ + distinguishedResidue lam₂ j₂ = i := by
  have h₁ := distinguishedResidue_relation lam₁ j₁ hunit
  have hunit₂ : IsUnit (lam₂ - -lam₂) := by
    rw [hopposite]
    simp only [neg_neg]
    have heq : -lam₁ - lam₁ = -(lam₁ - -lam₁) := by ring
    rw [heq]
    exact hunit.neg
  have h₂ := distinguishedResidue_relation lam₂ j₂ hunit₂
  apply hunit.mul_right_cancel
  rw [add_mul]
  rw [h₁]
  have hcoeff₂ : lam₂ - -lam₂ = -(lam₁ - -lam₁) := by
    rw [hopposite]
    ring
  have ht₂ : distinguishedResidue lam₂ j₂ * (lam₁ - -lam₁) = j₂ := by
    rw [hcoeff₂] at h₂
    calc
      distinguishedResidue lam₂ j₂ * (lam₁ - -lam₁) =
          -(distinguishedResidue lam₂ j₂ * -(lam₁ - -lam₁)) := by ring
      _ = -(-j₂) := congrArg Neg.neg h₂
      _ = j₂ := neg_neg _
  rw [ht₂]
  rw [hopposite] at hline
  simp only [sub_neg_eq_add] at hline
  linear_combination -hline

/-- Exact equality of the two pairs of chosen digits in (S7). -/
lemma shiftDigit_cross_eq
    {p u : ℕ} (hp : p.Prime)
    (lam₁ lam₂ j₁ j₂ i : ZMod p)
    (hunit : IsUnit (lam₁ - -lam₁))
    (hopposite : lam₂ = -lam₁)
    (hline : i * (lam₁ - lam₂) = -(j₁ - j₂)) :
    let t₁ := distinguishedResidue lam₁ j₁
    let t₂ := distinguishedResidue lam₂ j₂
    shiftDigit p u t₁ i = shiftDigit p u 0 t₂ ∧
      shiftDigit p u t₂ i = shiftDigit p u 0 t₁ := by
  dsimp only
  have hsum := distinguishedResidue_add_of_opposite
    lam₁ lam₂ j₁ j₂ i hunit hopposite hline
  constructor
  · have hcast :
        (shiftDigit p u (distinguishedResidue lam₁ j₁) i : ZMod p) =
          (shiftDigit p u 0 (distinguishedResidue lam₂ j₂) : ZMod p) := by
      rw [shiftDigit_cast hp, shiftDigit_cast hp]
      congr 1
      linear_combination hsum
    have hv := congrArg ZMod.val hcast
    rw [ZMod.val_natCast_of_lt (shiftDigit_lt hp _ _),
      ZMod.val_natCast_of_lt (shiftDigit_lt hp _ _)] at hv
    exact hv
  · have hcast :
        (shiftDigit p u (distinguishedResidue lam₂ j₂) i : ZMod p) =
          (shiftDigit p u 0 (distinguishedResidue lam₁ j₁) : ZMod p) := by
      rw [shiftDigit_cast hp, shiftDigit_cast hp]
      congr 1
      linear_combination hsum
    have hv := congrArg ZMod.val hcast
    rw [ZMod.val_natCast_of_lt (shiftDigit_lt hp _ _),
      ZMod.val_natCast_of_lt (shiftDigit_lt hp _ _)] at hv
    exact hv

/-- The two total chosen shifts in (S6) have the same literal sum. -/
lemma shiftDigit_cross_sum
    {p u : ℕ} (hp : p.Prime)
    (lam₁ lam₂ j₁ j₂ i : ZMod p)
    (hunit : IsUnit (lam₁ - -lam₁))
    (hopposite : lam₂ = -lam₁)
    (hline : i * (lam₁ - lam₂) = -(j₁ - j₂)) :
    let t₁ := distinguishedResidue lam₁ j₁
    let t₂ := distinguishedResidue lam₂ j₂
    shiftDigit p u t₁ i + shiftDigit p u 0 t₁ =
      shiftDigit p u t₂ i + shiftDigit p u 0 t₂ := by
  dsimp only
  obtain ⟨h₁, h₂⟩ := shiftDigit_cross_eq (u := u) hp lam₁ lam₂ j₁ j₂ i
    hunit hopposite hline
  rw [h₁, h₂]
  omega

end

end Erdos215.Selector.PrimeExtension
