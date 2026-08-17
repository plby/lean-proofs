/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos215.SelectorComponents
import ErdosProblems.Erdos215.SelectorFactorization

/-!
The canonical complete list of primary components of a nonzero denominator.

This is the low-level factorization package used by the final selector
extension.  For every `p ∈ d.primeFactors` it records the full factor
`p ^ d.factorization p`, with complementary factor `ordCompl[p] d`.
-/

namespace Erdos215.Selector

open Modular

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- The full primary component of `d` belonging to the prime factor `p`. -/
def completePrimaryComponent (d : ℕ) (hd : d ≠ 0)
    (p : d.primeFactors) : PrimaryComponent d where
  p := p
  a := d.factorization p
  D := ordCompl[(p : ℕ)] d
  prime := Nat.prime_of_mem_primeFactors p.2
  exp_pos := (Nat.prime_of_mem_primeFactors p.2).factorization_pos_of_dvd hd
    (Nat.dvd_of_mem_primeFactors p.2)
  factor := (Nat.ordProj_mul_ordCompl_eq_self d p).symm
  coprime := (Nat.coprime_ordCompl
    (Nat.prime_of_mem_primeFactors p.2) hd).pow_left _

@[simp] theorem completePrimaryComponent_p (d : ℕ) (hd : d ≠ 0)
    (p : d.primeFactors) :
    (completePrimaryComponent d hd p).p = p := rfl

@[simp] theorem completePrimaryComponent_a (d : ℕ) (hd : d ≠ 0)
    (p : d.primeFactors) :
    (completePrimaryComponent d hd p).a = d.factorization p := rfl

@[simp] theorem completePrimaryComponent_D (d : ℕ) (hd : d ≠ 0)
    (p : d.primeFactors) :
    (completePrimaryComponent d hd p).D =
      d / ((p : ℕ) ^ d.factorization p) := rfl

@[simp] theorem completePrimaryComponent_q (d : ℕ) (hd : d ≠ 0)
    (p : d.primeFactors) :
    (completePrimaryComponent d hd p).q =
      (p : ℕ) ^ d.factorization p := rfl

/-- The canonical component list, ordered by `Finset.toList`. -/
def completeComponentList (d : ℕ) (hd : d ≠ 0) :
    List (PrimaryComponent d) :=
  (Finset.univ : Finset d.primeFactors).toList.map
    (completePrimaryComponent d hd)

/-- Every nonzero natural number has a complete decomposition into its full
pairwise-coprime primary factors. -/
def completeComponents (d : ℕ) (hd : d ≠ 0) : CompleteComponents d where
  components := completeComponentList d hd
  pairwise := by
    rw [completeComponentList, List.pairwise_map]
    apply List.Nodup.pairwise_of_forall_ne (Finset.nodup_toList _)
    intro p hp q hq hpq
    simpa only [completePrimaryComponent_q] using
      d.pairwise_coprime_pow_primeFactors_factorization hpq
  product_eq := by
    simp only [completeComponentList, List.map_map, Finset.prod_map_toList,
      Function.comp_apply, completePrimaryComponent_q]
    exact (Nat.prod_primeFactors_coe_pow_factorization hd).symm

/-- Membership in the canonical list is exactly membership through a prime
factor index. -/
theorem mem_completeComponentList_iff {d : ℕ} {hd : d ≠ 0}
    (c : PrimaryComponent d) :
    c ∈ completeComponentList d hd ↔
      ∃ p : d.primeFactors, completePrimaryComponent d hd p = c := by
  simp [completeComponentList]

/-- Any predicate satisfied by every prime divisor of `d` is satisfied by
the prime underlying every component in the canonical decomposition. -/
theorem completeComponents_component_property
    {d : ℕ} (hd : d ≠ 0) (P : ℕ → Prop)
    (hP : ∀ p : ℕ, p.Prime → p ∣ d → P p)
    (c : PrimaryComponent d)
    (hc : c ∈ (completeComponents d hd).components) : P c.p := by
  change c ∈ completeComponentList d hd at hc
  obtain ⟨p, rfl⟩ := (mem_completeComponentList_iff (hd := hd) c).mp hc
  exact hP p (Nat.prime_of_mem_primeFactors p.2)
    (Nat.dvd_of_mem_primeFactors p.2)

/-- In particular, a prime-divisor congruence hypothesis transfers to all
canonical primary components. -/
theorem completeComponents_component_mod_four_eq_one
    {d : ℕ} (hd : d ≠ 0)
    (hp1 : ∀ p : ℕ, p.Prime → p ∣ d → p % 4 = 1)
    (c : PrimaryComponent d)
    (hc : c ∈ (completeComponents d hd).components) :
    c.p % 4 = 1 :=
  completeComponents_component_property hd (fun p ↦ p % 4 = 1)
    hp1 c hc

/-- Every primary component of the nontrivial part is supported at a prime
congruent to `1 mod 4`.  This includes the vacuous case where that part is
one and hence has no components. -/
theorem completeComponents_nontrivialPart_component_mod_four_eq_one
    (d : ℕ) (hd : d ≠ 0)
    (c : PrimaryComponent (nontrivialPart d))
    (hc : c ∈
      (completeComponents (nontrivialPart d)
        (nontrivialPart_ne_zero d hd)).components) :
    c.p % 4 = 1 := by
  refine completeComponents_component_mod_four_eq_one
    (nontrivialPart_ne_zero d hd) ?_ c hc
  intro p hp hpd
  exact ((prime_dvd_nontrivialPart_iff d p hd hp).mp hpd).2

/-- The nontrivial denominator part is odd, also when it is equal to one. -/
theorem coprime_two_nontrivialPart (d : ℕ) (hd : d ≠ 0) :
    Nat.Coprime 2 (nontrivialPart d) := by
  apply Nat.prime_two.coprime_iff_not_dvd.mpr
  intro htwo
  have hmod : 2 % 4 = 1 :=
    ((prime_dvd_nontrivialPart_iff d 2 hd Nat.prime_two).mp htwo).2
  norm_num at hmod

end

end Erdos215.Selector
