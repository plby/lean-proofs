import ErdosProblems.Erdos1141.BurgessPrimeMoment
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Products of local quadratic characters

The Chinese remainder interface is independent of the moment order.
-/

namespace Pollack17.Burgess

open scoped BigOperators

def primeModulus (s : Finset ℕ) : ℕ := ∏ p ∈ s, p

theorem primeModulus_pos (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    0 < primeModulus s := Finset.prod_pos (fun p hp => (hs p hp).pos)

theorem primeSet_pairwise (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Pairwise (fun p r : s => Nat.Coprime (p : ℕ) (r : ℕ)) := by
  intro p r hpr
  exact (hs p p.property).coprime_iff_not_dvd.mpr fun hdvd =>
    hpr (Subtype.ext ((Nat.prime_dvd_prime_iff_eq (hs p p.property)
      (hs r r.property)).mp hdvd))

noncomputable def primeCRT (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ZMod (primeModulus s) ≃+* (∀ p : s, ZMod (p : ℕ)) := by
  have hprod : primeModulus s = ∏ p : s, (p : ℕ) :=
    (Finset.prod_attach s (fun p : ℕ => p)).symm
  exact (ZMod.ringEquivCongr hprod).trans
    (ZMod.prodEquivPi (fun p : s => (p : ℕ)) (primeSet_pairwise s hs))

theorem primeCRT_natCast (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (n : ℕ) (p : s) :
    primeCRT s hs (n : ZMod (primeModulus s)) p = (n : ZMod (p : ℕ)) := by
  simp [primeCRT]

noncomputable def localChar (p : ℕ) (hp : p.Prime) (x : ZMod p) : ℝ :=
  @qchar p ⟨hp⟩ x

noncomputable def productChar (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (x : ZMod (primeModulus s)) : ℝ :=
  ∏ p : s, localChar p (hs p p.property) (primeCRT s hs x p)

theorem productChar_mul (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (a b : ZMod (primeModulus s)) :
    productChar s hs (a * b) = productChar s hs a * productChar s hs b := by
  simp [productChar, localChar, qchar, map_mul, Finset.prod_mul_distrib]

theorem abs_localChar_le_one (p : ℕ) (hp : p.Prime) (x : ZMod p) :
    |localChar p hp x| ≤ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  rcases quadraticChar_isQuadratic (ZMod p) x with h | h | h <;>
    norm_num [localChar, qchar, h]

theorem abs_productChar_le_one (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (x : ZMod (primeModulus s)) : |productChar s hs x| ≤ 1 := by
  rw [productChar, Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) fun p _ =>
    abs_localChar_le_one p (hs p p.property) _

theorem productChar_complete_correlation (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeModulus s)] [(p : s) → NeZero (p : ℕ)] {n : ℕ} (v : Fin n → ℕ) :
    (∑ x : ZMod (primeModulus s),
        productChar s hs (∏ i : Fin n, (x + v i))) =
      ∏ p : s, ∑ y : ZMod (p : ℕ),
        localChar p (hs p p.property) (∏ i : Fin n, (y + v i)) := by
  let e := primeCRT s hs
  calc
    _ = ∑ y : (∀ p : s, ZMod (p : ℕ)),
        ∏ p : s, localChar p (hs p p.property) (∏ i : Fin n, (y p + v i)) := by
      rw [← e.toEquiv.sum_comp]
      apply Finset.sum_congr rfl
      intro x _
      rw [productChar]
      apply Fintype.prod_congr
      intro p
      congr 1
      simp [e]
    _ = _ := by rw [Fintype.prod_sum]

theorem prod_prime_gcd (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (d : ℕ) :
    (∏ p ∈ s, p.gcd d) = (primeModulus s).gcd d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [primeModulus]
  | @insert p s hp ih =>
    have hs' : ∀ r ∈ s, r.Prime := fun r hr => hs r (Finset.mem_insert_of_mem hr)
    have hpp : p.Prime := hs p (Finset.mem_insert_self p s)
    have hcop : p.Coprime (primeModulus s) := Nat.Coprime.prod_right fun r hr =>
      hpp.coprime_iff_not_dvd.mpr fun hdvd =>
        hp ((Nat.prime_dvd_prime_iff_eq hpp (hs' r hr)).mp hdvd ▸ hr)
    rw [Finset.prod_insert hp, ih hs']
    rw [show primeModulus (insert p s) = p * primeModulus s from Finset.prod_insert hp]
    rw [Nat.gcd_comm (p * primeModulus s), hcop.gcd_mul d,
      Nat.gcd_comm d p, Nat.gcd_comm d (primeModulus s)]

end Pollack17.Burgess
