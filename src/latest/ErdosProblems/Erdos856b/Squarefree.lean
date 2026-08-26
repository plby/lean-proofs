import ErdosProblems.Erdos856b.Basic

/-! # The exact squarefree correspondence between common LCMs and common unions -/

namespace Erdos856b

open scoped BigOperators

theorem primeFactors_lcm {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (Nat.lcm a b).primeFactors = a.primeFactors ∪ b.primeFactors := by
  ext p
  by_cases hp : p.Prime
  · simp [Nat.mem_primeFactors, hp, ha, hb, Nat.lcm_ne_zero ha hb, hp.dvd_lcm]
  · simp [Nat.mem_primeFactors, hp]

theorem squarefree_lcm {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    Squarefree (Nat.lcm a b) := by
  apply Nat.squarefree_of_factorization_le_one (Nat.lcm_ne_zero ha.ne_zero hb.ne_zero)
  intro p
  rw [Nat.factorization_lcm ha.ne_zero hb.ne_zero]
  change max (a.factorization p) (b.factorization p) ≤ 1
  exact max_le (ha.natFactorization_le_one p) (hb.natFactorization_le_one p)

theorem lcm_eq_prod_union {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    Nat.lcm a b = ∏ p ∈ a.primeFactors ∪ b.primeFactors, p := by
  rw [← primeFactors_lcm ha.ne_zero hb.ne_zero]
  exact (Nat.prod_primeFactors_of_squarefree (squarefree_lcm ha hb)).symm

theorem squarefree_eq_of_primeFactors_eq {a b : ℕ} (ha : Squarefree a)
    (hb : Squarefree b) (h : a.primeFactors = b.primeFactors) : a = b := by
  rw [← Nat.prod_primeFactors_of_squarefree ha, ← Nat.prod_primeFactors_of_squarefree hb, h]

/-- For squarefree integers the correspondence preserves both the forbidden configuration
and the requirement that its `k` members are distinct. -/
theorem lcmFree_iff_unionFree_primeFactors {k : ℕ} {A : Finset ℕ}
    (hA : ∀ a ∈ A, Squarefree a) :
    LcmFree k A ↔ UnionFree k (A.image Nat.primeFactors) := by
  classical
  constructor
  · intro hfree b hbinj hb hbad
    obtain ⟨u, hu⟩ := hbad
    choose a ha heq using fun i => Finset.mem_image.mp (hb i)
    have hainj : Function.Injective a := by
      intro i j hij
      apply hbinj
      rw [← heq i, ← heq j, hij]
    apply hfree a hainj ha
    refine ⟨∏ p ∈ u, p, fun i j hij => ?_⟩
    rw [lcm_eq_prod_union (hA _ (ha i)) (hA _ (ha j)), heq i, heq j, hu i j hij]
  · intro hfree a hainj ha hbad
    obtain ⟨m, hm⟩ := hbad
    have hbinj : Function.Injective (fun i => (a i).primeFactors) := by
      intro i j hij
      apply hainj
      exact squarefree_eq_of_primeFactors_eq (hA _ (ha i)) (hA _ (ha j)) hij
    apply hfree (fun i => (a i).primeFactors) hbinj
      (fun i => Finset.mem_image_of_mem _ (ha i))
    refine ⟨m.primeFactors, fun i j hij => ?_⟩
    rw [← primeFactors_lcm (hA _ (ha i)).ne_zero (hA _ (ha j)).ne_zero, hm i j hij]

end Erdos856b
