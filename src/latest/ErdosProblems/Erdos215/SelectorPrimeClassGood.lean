/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos215.SelectorPrimeExtension

namespace Erdos215.Selector.PrimeClassGood

open Erdos215.Selector

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- After restricting an index to one class modulo `p`, divide away the
mandatory factor `p` and retain its next `a` base-`p` digits. -/
def classDigit (p a : ℕ) (hp : 0 < p) {N : ℕ} (i : Fin N) : Fin (p ^ a) :=
  ⟨(i.1 / p) % p ^ a, Nat.mod_lt _ (pow_pos hp a)⟩

/-- Absolute difference of the integer quotients after dividing by `p`. -/
def quotientDiff (p : ℕ) {N : ℕ} (i j : Fin N) : ℕ :=
  Int.natAbs (((i.1 / p : ℕ) : ℤ) - ((j.1 / p : ℕ) : ℤ))

private lemma natMod_intModEq (m x : ℕ) :
    ((x % m : ℕ) : ℤ) ≡ (x : ℤ) [ZMOD (m : ℤ)] := by
  rw [Int.modEq_iff_dvd]
  have h : (x : ℤ) = (x % m : ℕ) + (m : ℤ) * (x / m : ℕ) := by
    exact_mod_cast (Nat.mod_add_div x m).symm
  use (x / m : ℕ)
  omega

private lemma gcd_natAbs_sub_eq_of_intModEq
    {m x y x' y' : ℕ}
    (h : ((x : ℤ) - (y : ℤ)) ≡ ((x' : ℤ) - (y' : ℤ)) [ZMOD (m : ℤ)]) :
    Nat.gcd m (Int.natAbs ((x : ℤ) - (y : ℤ))) =
      Nat.gcd m (Int.natAbs ((x' : ℤ) - (y' : ℤ))) := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    rw [← Int.natCast_dvd_natCast]
    apply Int.dvd_natAbs.mpr
    have hgM : ((Nat.gcd m (Int.natAbs ((x : ℤ) - (y : ℤ))) : ℕ) : ℤ) ∣
        (m : ℤ) := by
      exact_mod_cast Nat.gcd_dvd_left m (Int.natAbs ((x : ℤ) - (y : ℤ)))
    have hgxy : ((Nat.gcd m (Int.natAbs ((x : ℤ) - (y : ℤ))) : ℕ) : ℤ) ∣
        (x : ℤ) - (y : ℤ) := by
      rw [← Int.dvd_natAbs]
      exact_mod_cast Nat.gcd_dvd_right m (Int.natAbs ((x : ℤ) - (y : ℤ)))
    rw [Int.modEq_iff_dvd] at h
    have hz := hgxy.add (hgM.trans h)
    have heq : (x : ℤ) - (y : ℤ) +
        ((x' : ℤ) - (y' : ℤ) - ((x : ℤ) - (y : ℤ))) =
          (x' : ℤ) - (y' : ℤ) := by ring
    rw [heq] at hz
    exact hz
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    rw [← Int.natCast_dvd_natCast]
    apply Int.dvd_natAbs.mpr
    have hgM : ((Nat.gcd m (Int.natAbs ((x' : ℤ) - (y' : ℤ))) : ℕ) : ℤ) ∣
        (m : ℤ) := by
      exact_mod_cast Nat.gcd_dvd_left m (Int.natAbs ((x' : ℤ) - (y' : ℤ)))
    have hgxy : ((Nat.gcd m (Int.natAbs ((x' : ℤ) - (y' : ℤ))) : ℕ) : ℤ) ∣
        (x' : ℤ) - (y' : ℤ) := by
      rw [← Int.dvd_natAbs]
      exact_mod_cast Nat.gcd_dvd_right m (Int.natAbs ((x' : ℤ) - (y' : ℤ)))
    rw [Int.modEq_iff_dvd] at h
    simpa only [sub_sub_cancel] using hgxy.sub (hgM.trans h)

lemma indexDiff_eq_mul_quotientDiff_of_same_class
    {N p : ℕ} (_hp : 0 < p) (i j : Fin N) (hsame : i.1 % p = j.1 % p) :
    indexDiff i j = p * quotientDiff p i j := by
  simp only [indexDiff, quotientDiff]
  have hi : (i.1 : ℤ) = (i.1 % p : ℕ) + (p : ℤ) * (i.1 / p : ℕ) := by
    exact_mod_cast (Nat.mod_add_div i.1 p).symm
  have hj : (j.1 : ℤ) = (j.1 % p : ℕ) + (p : ℤ) * (j.1 / p : ℕ) := by
    exact_mod_cast (Nat.mod_add_div j.1 p).symm
  rw [hi, hj, hsame]
  ring_nf
  rw [← mul_sub, Int.natAbs_mul, Int.natAbs_natCast]

lemma gcd_indexDiff_classDigit
    {N p a : ℕ} (hp : 0 < p) (i j : Fin N) :
    Nat.gcd (p ^ a)
        (indexDiff (classDigit p a hp i) (classDigit p a hp j)) =
      Nat.gcd (p ^ a) (quotientDiff p i j) := by
  apply gcd_natAbs_sub_eq_of_intModEq
  exact (natMod_intModEq (p ^ a) (i.1 / p)).sub
    (natMod_intModEq (p ^ a) (j.1 / p))

lemma survivingModulus_classDigit
    {N p a : ℕ} (hp : 0 < p) (i j : Fin N) :
    survivingModulus (p ^ a)
        (indexDiff (classDigit p a hp i) (classDigit p a hp j)) =
      p ^ a / Nat.gcd (p ^ a) (quotientDiff p i j) := by
  simp only [survivingModulus, gcd_indexDiff_classDigit hp i j]

private lemma gcd_mul_complement_dvd
    {m u q : ℕ} (hcop : Nat.Coprime m u) :
    Nat.gcd (m * u) q ∣ u * Nat.gcd m q := by
  let x := Nat.gcd (m * u) q
  have hfactor : Nat.gcd x m * Nat.gcd x u = x := by
    apply (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hcop).2
    exact Nat.gcd_dvd_left _ _
  have hxm : Nat.gcd x m ∣ Nat.gcd m q := by
    apply Nat.dvd_gcd
    · exact Nat.gcd_dvd_right _ _
    · exact (Nat.gcd_dvd_left x m).trans (Nat.gcd_dvd_right (m * u) q)
  have hxu : Nat.gcd x u ∣ u := Nat.gcd_dvd_right _ _
  change x ∣ u * Nat.gcd m q
  rw [← hfactor]
  simpa [Nat.mul_comm] using Nat.mul_dvd_mul hxm hxu

/-- In the branch where the full new `p`-power does not divide the input
difference, the surviving modulus of the quotient digit divides the full
surviving modulus.  This is the exact divisibility needed to apply goodness
of the auxiliary permutation on `Fin (p^a)`. -/
lemma survivingModulus_classDigit_dvd
    {N p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (hN : N = p ^ (a + 1) * u) (i j : Fin N)
    (hsame : i.1 % p = j.1 % p) :
    survivingModulus (p ^ a)
        (indexDiff (classDigit p a hp.pos i) (classDigit p a hp.pos j)) ∣
      survivingModulus N (indexDiff i j) := by
  let m := p ^ a
  let q := quotientDiff p i j
  let g₀ := Nat.gcd m q
  let gx := Nat.gcd (m * u) q
  have hcopMU : Nat.Coprime m u := hcop.pow_left a
  have hx : gx ∣ u * g₀ := by
    exact gcd_mul_complement_dvd hcopMU
  have hg₀m : g₀ ∣ m := Nat.gcd_dvd_left _ _
  have hxmu : gx ∣ m * u := by
    exact Nat.gcd_dvd_left _ _
  have hdiv : m / g₀ ∣ (m * u) / gx := by
    rw [Nat.dvd_div_iff_mul_dvd hxmu]
    have hmul := Nat.mul_dvd_mul_left (m / g₀) hx
    have hprod : (m / g₀) * (u * g₀) = m * u := by
      calc
        (m / g₀) * (u * g₀) = u * (g₀ * (m / g₀)) := by ac_rfl
        _ = u * m := by rw [Nat.mul_div_cancel' hg₀m]
        _ = m * u := Nat.mul_comm _ _
    rw [hprod] at hmul
    simpa [Nat.mul_comm] using hmul
  rw [survivingModulus_classDigit hp.pos i j]
  have hidx := indexDiff_eq_mul_quotientDiff_of_same_class hp.pos i j hsame
  simp only [survivingModulus, hN, hidx, pow_succ]
  simpa [m, q, g₀, gx, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
    Nat.gcd_mul_left, Nat.mul_div_mul_left _ _ hp.pos] using hdiv

/-- If the full new `p`-power has already been cancelled by the input
difference, only the complementary factor `u` can remain in the required
surviving modulus. -/
lemma survivingModulus_dvd_complement_of_primePower_dvd
    {N p u a delta : ℕ} (hp : p.Prime)
    (hN : N = p ^ (a + 1) * u) (hpow : p ^ (a + 1) ∣ delta) :
    survivingModulus N delta ∣ u := by
  have hpN : p ^ (a + 1) ∣ N := by rw [hN]; exact dvd_mul_right _ _
  have hpg : p ^ (a + 1) ∣ Nat.gcd N delta := Nat.dvd_gcd hpN hpow
  have hgN : Nat.gcd N delta ∣ N := Nat.gcd_dvd_left _ _
  have hdiv : N / Nat.gcd N delta ∣ N / p ^ (a + 1) :=
    Nat.div_dvd_div_left hgN hpg
  have hquot : N / p ^ (a + 1) = u := by
    rw [hN]
    simpa [Nat.mul_comm] using Nat.mul_div_left u (pow_pos hp.pos (a + 1))
  rw [hquot] at hdiv
  exact hdiv

private lemma int_dvd_sub_iff_natModEq (m x y : ℕ) :
    (m : ℤ) ∣ (x : ℤ) - (y : ℤ) ↔ x ≡ y [MOD m] := by
  rw [Nat.modEq_iff_dvd]
  constructor <;> intro h <;> simpa only [neg_sub] using dvd_neg.mpr h

lemma classDigit_ne_of_not_primePower_dvd
    {N p a : ℕ} (hp : p.Prime) (i j : Fin N)
    (hsame : i.1 % p = j.1 % p)
    (hnot : ¬p ^ (a + 1) ∣ indexDiff i j) :
    classDigit p a hp.pos i ≠ classDigit p a hp.pos j := by
  intro hdigit
  have hg : Nat.gcd (p ^ a) (quotientDiff p i j) = p ^ a := by
    rw [← gcd_indexDiff_classDigit hp.pos i j, hdigit]
    simp [indexDiff]
  have hq : p ^ a ∣ quotientDiff p i j := by
    rw [← hg]
    exact Nat.gcd_dvd_right _ _
  apply hnot
  rw [indexDiff_eq_mul_quotientDiff_of_same_class hp.pos i j hsame, pow_succ]
  simpa [Nat.mul_comm] using Nat.mul_dvd_mul_left p hq

/-- The `p`-primary branch of partial goodness for a map on one class
modulo `p`.  Its output modulo `p^(a+1)` is a fixed translate of a good
permutation applied to `classDigit`.  Unless the input difference has already
cancelled the whole `p^(a+1)`, that coordinate alone rules out a bad output
congruence modulo the full surviving modulus. -/
lemma not_dvd_output_sub_of_primePower_formula
    {N p u a target correction : ℕ}
    (hp : p.Prime) (hcop : Nat.Coprime p u)
    (hN : N = p ^ (a + 1) * u)
    (rho : Equiv.Perm (Fin (p ^ a))) (hrho : GoodPerm (p ^ a) rho)
    (f : Fin N → Fin N)
    (hout : ∀ i : Fin N, i.1 % p = target →
      (f i).1 ≡ (rho (classDigit p a hp.pos i)).1 + correction
        [MOD p ^ (a + 1)])
    (i j : Fin N) (hi : i.1 % p = target) (hj : j.1 % p = target)
    (hnot : ¬p ^ (a + 1) ∣ indexDiff i j) :
    ¬(survivingModulus N (indexDiff i j) : ℤ) ∣
      (((f i).1 : ℕ) : ℤ) - (((f j).1 : ℕ) : ℤ) := by
  have hsame : i.1 % p = j.1 % p := hi.trans hj.symm
  let di := classDigit p a hp.pos i
  let dj := classDigit p a hp.pos j
  have hdigit : di ≠ dj :=
    classDigit_ne_of_not_primePower_dvd hp i j hsame hnot
  let M₀ := survivingModulus (p ^ a) (indexDiff di dj)
  let M := survivingModulus N (indexDiff i j)
  have hM₀M : M₀ ∣ M := by
    exact survivingModulus_classDigit_dvd hp hcop hN i j hsame
  have hM₀pow : M₀ ∣ p ^ (a + 1) := by
    exact (survivingModulus_dvd _ _).trans (by
      rw [pow_succ]
      exact dvd_mul_right (p ^ a) p)
  intro hbad
  have hbadM₀ : (M₀ : ℤ) ∣
      (((f i).1 : ℕ) : ℤ) - (((f j).1 : ℕ) : ℤ) := by
    exact (Int.natCast_dvd_natCast.mpr hM₀M).trans hbad
  have hfi := (hout i hi).of_dvd hM₀pow
  have hfj := (hout j hj).of_dvd hM₀pow
  have hfij : (f i).1 ≡ (f j).1 [MOD M₀] :=
    (int_dvd_sub_iff_natModEq M₀ _ _).mp hbadM₀
  have hrmod : (rho di).1 ≡ (rho dj).1 [MOD M₀] := by
    exact Nat.ModEq.add_right_cancel'
      correction (hfi.symm.trans (hfij.trans hfj))
  exact hrho di dj hdigit ((int_dvd_sub_iff_natModEq M₀ _ _).mpr hrmod)

lemma survivingModulus_indexDiff_dvd_complement
    {N p u a : ℕ} (hp : p.Prime)
    (hN : N = p ^ (a + 1) * u) (i j : Fin N)
    (hpow : p ^ (a + 1) ∣ indexDiff i j) :
    survivingModulus N (indexDiff i j) ∣ u :=
  survivingModulus_dvd_complement_of_primePower_dvd hp hN hpow

end

end Erdos215.Selector.PrimeClassGood
