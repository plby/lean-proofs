import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos1188

open scoped BigOperators

universe u
variable {ι : Type u} [DecidableEq ι]

/-- Products of subsets of pairwise-coprime integers greater than one uniquely
determine their support. -/
theorem coprime_subsetProduct_injective
    (q : ι → ℕ)
    (hq : ∀ i, 2 ≤ q i)
    (hcop : Pairwise (Function.onFun Nat.Coprime q)) :
    Function.Injective (fun J : Finset ι => ∏ j ∈ J, q j) := by
  intro A B hprod
  apply Finset.ext
  intro i
  constructor
  · intro hiA
    by_contra hiB
    have hdivA : q i ∣ ∏ j ∈ A, q j := Finset.dvd_prod_of_mem q hiA
    have hdivB : q i ∣ ∏ j ∈ B, q j := by simpa [hprod] using hdivA
    have hcopB : (q i).Coprime (∏ j ∈ B, q j) := by
      apply Nat.Coprime.prod_right
      intro j hjB
      apply hcop
      intro hij
      subst j
      exact hiB hjB
    have hone : q i = 1 := by
      calc
        q i = Nat.gcd (q i) (∏ j ∈ B, q j) :=
          (Nat.gcd_eq_left_iff_dvd.mpr hdivB).symm
        _ = 1 := hcopB
    have hqi := hq i
    omega
  · intro hiB
    by_contra hiA
    have hdivB : q i ∣ ∏ j ∈ B, q j := Finset.dvd_prod_of_mem q hiB
    have hdivA : q i ∣ ∏ j ∈ A, q j := by simpa [hprod] using hdivB
    have hcopA : (q i).Coprime (∏ j ∈ A, q j) := by
      apply Nat.Coprime.prod_right
      intro j hjA
      apply hcop
      intro hij
      subst j
      exact hiA hjA
    have hone : q i = 1 := by
      calc
        q i = Nat.gcd (q i) (∏ j ∈ A, q j) :=
          (Nat.gcd_eq_left_iff_dvd.mpr hdivA).symm
        _ = 1 := hcopA
    have hqi := hq i
    omega

end Erdos1188
