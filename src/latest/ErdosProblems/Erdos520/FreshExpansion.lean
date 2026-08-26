import ErdosProblems.Erdos520.Model
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Sups
import Mathlib.NumberTheory.SmoothNumbers

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset
open scoped BigOperators

namespace Erdos
namespace Problem520

/-- Primes in the half-open arithmetic block `(a, b]`. -/
def freshPrimes (a b : ℕ) : Finset ℕ :=
  (b + 1).primesBelow.filter fun p => a < p

theorem mem_freshPrimes {a b p : ℕ} :
    p ∈ freshPrimes a b ↔ p.Prime ∧ a < p ∧ p ≤ b := by
  simp [freshPrimes, Nat.mem_primesBelow,
    and_comm, and_left_comm, and_assoc]

theorem primesBelow_succ_eq_union_freshPrimes {a b : ℕ} (hab : a ≤ b) :
    (b + 1).primesBelow = (a + 1).primesBelow ∪ freshPrimes a b := by
  ext p
  simp only [Nat.mem_primesBelow, mem_freshPrimes, Finset.mem_union]
  constructor
  · rintro ⟨hpb, hp⟩
    by_cases hpa : p < a + 1
    · exact Or.inl ⟨hpa, hp⟩
    · exact Or.inr ⟨hp, by omega, by omega⟩
  · rintro (⟨hpa, hp⟩ | ⟨hp, _hap, hpb⟩)
    · exact ⟨lt_of_lt_of_le hpa (Nat.add_le_add_right hab 1), hp⟩
    · exact ⟨by omega, hp⟩

theorem primesBelow_succ_disjoint_freshPrimes (a b : ℕ) :
    Disjoint (a + 1).primesBelow (freshPrimes a b) := by
  rw [Finset.disjoint_left]
  intro p hpold hpfresh
  have hold := (Nat.mem_primesBelow.mp hpold).1
  have hfresh := (mem_freshPrimes.mp hpfresh).2.1
  omega

theorem freshPrimes_pred_self {p : ℕ} (hp : 0 < p) :
    freshPrimes (p - 1) p = if p.Prime then {p} else ∅ := by
  classical
  split_ifs with hprime
  · ext q
    simp only [mem_freshPrimes, Finset.mem_singleton]
    constructor
    · rintro ⟨_hqprime, hlow, hhigh⟩
      omega
    · rintro rfl
      exact ⟨hprime, by omega, le_rfl⟩
  · ext q
    simp only [mem_freshPrimes, Finset.notMem_empty, iff_false]
    rintro ⟨hqprime, hlow, hhigh⟩
    have : q = p := by omega
    exact hprime (this ▸ hqprime)

/-- Squarefree integer represented by a subset of a fresh prime block. -/
def freshProduct (S : Finset ℕ) : ℕ :=
  ∏ p ∈ S, p

@[simp] theorem freshProduct_empty : freshProduct ∅ = 1 := by
  simp [freshProduct]

@[simp] theorem freshProduct_singleton (p : ℕ) : freshProduct {p} = p := by
  simp [freshProduct]

theorem freshProduct_squarefree {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (freshProduct S) := by
  unfold freshProduct
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (hS p hp) (hS q hq)).2 hpq)
  · intro p hp
    exact (hS p hp).squarefree

theorem freshProduct_primeFactors {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) :
    (freshProduct S).primeFactors = S := by
  exact Nat.primeFactors_prod hS

/-- Walsh character of a finite set of prime coordinates. -/
def freshCharacter (omega : Omega) (S : Finset ℕ) : ℝ :=
  ∏ p ∈ S, ε omega p

@[simp] theorem freshCharacter_empty (omega : Omega) :
    freshCharacter omega ∅ = 1 := by simp [freshCharacter]

@[simp] theorem freshCharacter_singleton (omega : Omega) (p : ℕ) :
    freshCharacter omega {p} = ε omega p := by simp [freshCharacter]

@[simp] theorem f_freshProduct (omega : Omega) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) :
    f omega (freshProduct S) = freshCharacter omega S := by
  rw [f_eq_prod_primeFactors_of_squarefree omega (freshProduct_squarefree hS),
    freshProduct_primeFactors hS]
  rfl

/-- Finite smooth partial sum with all prime factors at most `y`. -/
noncomputable def Ψ (omega : Omega) (z y : ℕ) : ℝ :=
  ∑ n ∈ Nat.smoothNumbersUpTo z (y + 1), f omega n

/-- Strict-cutoff variant with all prime factors less than `p`. -/
noncomputable def Ψ' (omega : Omega) (z p : ℕ) : ℝ :=
  ∑ n ∈ Nat.smoothNumbersUpTo z p, f omega n

/-- Subsets of the primes at most `y` whose squarefree product is at most
`z`.  These sets give a duplicate-free finite parametrization of the terms
which can contribute to `Ψ`. -/
def squarefreeSmoothSets (z y : ℕ) : Finset (Finset ℕ) :=
  ((y + 1).primesBelow.powerset).filter fun S => freshProduct S ≤ z

theorem mem_squarefreeSmoothSets {z y : ℕ} {S : Finset ℕ} :
    S ∈ squarefreeSmoothSets z y ↔
      S ⊆ (y + 1).primesBelow ∧ freshProduct S ≤ z := by
  simp [squarefreeSmoothSets]

/-- Pairs consisting of a subset of the fresh primes `(a,b]` and a subset of
the old primes `≤ a`, subject to the common product cutoff `z`. -/
def freshOldPairs (z a b : ℕ) : Finset (Σ _ : Finset ℕ, Finset ℕ) :=
  (freshPrimes a b).powerset.sigma fun S =>
    squarefreeSmoothSets (z / freshProduct S) a

theorem mem_freshOldPairs {z a b : ℕ} {x : Σ _ : Finset ℕ, Finset ℕ} :
    x ∈ freshOldPairs z a b ↔
      x.1 ⊆ freshPrimes a b ∧
      x.2 ⊆ (a + 1).primesBelow ∧
      freshProduct x.2 ≤ z / freshProduct x.1 := by
  simp [freshOldPairs, Finset.mem_sigma, mem_squarefreeSmoothSets]

theorem freshProduct_pos_of_primes {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) :
    0 < freshProduct S := by
  exact Nat.pos_of_ne_zero <| Finset.prod_ne_zero_iff.mpr fun p hp =>
    (hS p hp).ne_zero

/-- Splitting a squarefree smooth number into its old and fresh prime factors
is a bijective reindexing of the corresponding Walsh sum. -/
theorem sum_freshOldPairs_eq_sum_squarefreeSmoothSets
    (omega : Omega) (z : ℕ) {a b : ℕ} (hab : a ≤ b) :
    (∑ x ∈ freshOldPairs z a b,
        freshCharacter omega x.1 * freshCharacter omega x.2) =
      ∑ U ∈ squarefreeSmoothSets z b, freshCharacter omega U := by
  classical
  let old : Finset ℕ := (a + 1).primesBelow
  let new : Finset ℕ := freshPrimes a b
  have holdnew : Disjoint old new := by
    simpa [old, new] using! primesBelow_succ_disjoint_freshPrimes a b
  exact Finset.sum_bij
    (fun x _hx => x.1 ∪ x.2)
    (fun x hx => by
      rw [mem_freshOldPairs] at hx
      rw [mem_squarefreeSmoothSets]
      have hdisj : Disjoint x.1 x.2 :=
        holdnew.symm.mono hx.1 hx.2.1
      constructor
      · rw [primesBelow_succ_eq_union_freshPrimes hab]
        rw [Finset.union_comm ((a + 1).primesBelow) (freshPrimes a b)]
        exact Finset.union_subset_union hx.1 hx.2.1
      · have hprime : ∀ p ∈ x.1, p.Prime := fun p hp =>
          (mem_freshPrimes.mp (hx.1 hp)).1
        have hpos := freshProduct_pos_of_primes hprime
        have hmul : freshProduct x.2 * freshProduct x.1 ≤ z :=
          (Nat.le_div_iff_mul_le hpos).mp hx.2.2
        simpa [freshProduct, Finset.prod_union hdisj, Nat.mul_comm] using! hmul)
    (fun x₁ hx₁ x₂ hx₂ hEq => by
      rw [mem_freshOldPairs] at hx₁ hx₂
      change x₁.1 ⊆ new ∧ x₁.2 ⊆ old ∧
        freshProduct x₁.2 ≤ z / freshProduct x₁.1 at hx₁
      change x₂.1 ⊆ new ∧ x₂.2 ⊆ old ∧
        freshProduct x₂.2 ≤ z / freshProduct x₂.1 at hx₂
      have hEq' : x₁.1 ∪ x₁.2 = x₂.1 ∪ x₂.2 := by
        simpa only using! hEq
      have hfirst : x₁.1 = x₂.1 := by
        ext p
        constructor
        · intro hp
          have hpnew : p ∈ new := hx₁.1 hp
          have hpunion : p ∈ x₂.1 ∪ x₂.2 := by
            rw [← hEq']
            exact Finset.mem_union_left _ hp
          rcases Finset.mem_union.mp hpunion with hp' | hp'
          · exact hp'
          · exact (Finset.disjoint_left.mp holdnew (hx₂.2.1 hp') hpnew).elim
        · intro hp
          have hpnew : p ∈ new := hx₂.1 hp
          have hpunion : p ∈ x₁.1 ∪ x₁.2 := by
            rw [hEq']
            exact Finset.mem_union_left _ hp
          rcases Finset.mem_union.mp hpunion with hp' | hp'
          · exact hp'
          · exact (Finset.disjoint_left.mp holdnew (hx₁.2.1 hp') hpnew).elim
      have hsecond : x₁.2 = x₂.2 := by
        ext p
        constructor
        · intro hp
          have hpold : p ∈ old := hx₁.2.1 hp
          have hpunion : p ∈ x₂.1 ∪ x₂.2 := by
            rw [← hEq']
            exact Finset.mem_union_right _ hp
          rcases Finset.mem_union.mp hpunion with hp' | hp'
          · exact (Finset.disjoint_left.mp holdnew hpold (hx₂.1 hp')).elim
          · exact hp'
        · intro hp
          have hpold : p ∈ old := hx₂.2.1 hp
          have hpunion : p ∈ x₁.1 ∪ x₁.2 := by
            rw [hEq']
            exact Finset.mem_union_right _ hp
          rcases Finset.mem_union.mp hpunion with hp' | hp'
          · exact (Finset.disjoint_left.mp holdnew hpold (hx₁.1 hp')).elim
          · exact hp'
      cases x₁ with
      | mk S₁ T₁ =>
          cases x₂ with
          | mk S₂ T₂ =>
              simp only at hfirst hsecond
              cases hfirst
              cases hsecond
              rfl)
    (fun U hU => by
      rw [mem_squarefreeSmoothSets] at hU
      let S := U ∩ new
      let T := U ∩ old
      have hUeq : S ∪ T = U := by
        ext p
        simp only [S, T, Finset.mem_union, Finset.mem_inter]
        constructor
        · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
        · intro hp
          have hpall := hU.1 hp
          rw [primesBelow_succ_eq_union_freshPrimes hab] at hpall
          rcases Finset.mem_union.mp hpall with hpold | hpnew
          · exact Or.inr ⟨hp, hpold⟩
          · exact Or.inl ⟨hp, hpnew⟩
      have hSsub : S ⊆ new := Finset.inter_subset_right
      have hTsub : T ⊆ old := Finset.inter_subset_right
      have hdisj : Disjoint S T := holdnew.symm.mono hSsub hTsub
      have hprime : ∀ p ∈ S, p.Prime := fun p hp =>
        (mem_freshPrimes.mp (hSsub hp)).1
      have hpos := freshProduct_pos_of_primes hprime
      refine ⟨⟨S, T⟩, ?_, hUeq⟩
      rw [mem_freshOldPairs]
      refine ⟨hSsub, hTsub, (Nat.le_div_iff_mul_le hpos).mpr ?_⟩
      have hprod : freshProduct (S ∪ T) ≤ z := by
        rw [hUeq]
        exact hU.2
      simpa [freshProduct, Finset.prod_union hdisj, Nat.mul_comm] using! hprod)
    (fun x hx => by
      rw [mem_freshOldPairs] at hx
      have hdisj : Disjoint x.1 x.2 :=
        holdnew.symm.mono hx.1 hx.2.1
      simp only [freshCharacter]
      exact (Finset.prod_union hdisj).symm)

/-- A smooth squarefree sum is a finite Walsh polynomial indexed by subsets
of the available primes. -/
theorem Ψ_eq_sum_squarefreeSmoothSets (omega : Omega) (z y : ℕ) :
    Ψ omega z y =
      ∑ S ∈ squarefreeSmoothSets z y, freshCharacter omega S := by
  classical
  unfold Ψ
  rw [← Finset.sum_filter_of_ne (p := Squarefree) (fun n _hn hfn => by
    by_contra hn
    exact hfn (f_eq_zero_of_not_squarefree omega hn))]
  exact Finset.sum_bij
    (fun n _hn => n.primeFactors)
    (fun n hn => by
      rw [Finset.mem_filter] at hn
      rw [mem_squarefreeSmoothSets]
      have hsmooth := (Nat.mem_smoothNumbersUpTo.mp hn.1).2
      exact ⟨Nat.primeFactors_subset_of_mem_smoothNumbers hsmooth,
        by simpa [freshProduct, Nat.prod_primeFactors_of_squarefree hn.2] using!
          (Nat.mem_smoothNumbersUpTo.mp hn.1).1⟩)
    (fun n₁ hn₁ n₂ hn₂ hEq => by
      rw [Finset.mem_filter] at hn₁ hn₂
      calc
        n₁ = freshProduct n₁.primeFactors := by
          simp [freshProduct, Nat.prod_primeFactors_of_squarefree hn₁.2]
        _ = freshProduct n₂.primeFactors := congrArg freshProduct hEq
        _ = n₂ := by
          simp [freshProduct, Nat.prod_primeFactors_of_squarefree hn₂.2])
    (fun S hS => by
      rw [mem_squarefreeSmoothSets] at hS
      have hprime : ∀ p ∈ S, p.Prime := fun p hp =>
        Nat.prime_of_mem_primesBelow (hS.1 hp)
      refine ⟨freshProduct S, ?_, ?_⟩
      · rw [Finset.mem_filter, Nat.mem_smoothNumbersUpTo]
        refine ⟨⟨hS.2, ?_⟩, freshProduct_squarefree hprime⟩
        exact Nat.mem_smoothNumbers_of_primeFactors_subset
          (by
            exact Finset.prod_ne_zero_iff.mpr fun p hp =>
              (hprime p hp).ne_zero)
          (by
            rw [freshProduct_primeFactors hprime]
            exact hS.1.trans (Finset.filter_subset _ _))
      · exact freshProduct_primeFactors hprime)
    (fun n hn => by
      rw [Finset.mem_filter] at hn
      exact f_eq_prod_primeFactors_of_squarefree omega hn.2)

theorem Ψ'_eq_Ψ_pred (omega : Omega) (z : ℕ) {p : ℕ} (hp : 0 < p) :
    Ψ' omega z p = Ψ omega z (p - 1) := by
  simp only [Ψ', Ψ, Nat.sub_add_cancel hp]

/-- Coefficient of a fresh Walsh character after removing the primes in `S`. -/
noncomputable def freshCoefficient
    (omega : Omega) (z a : ℕ) (S : Finset ℕ) : ℝ :=
  Ψ omega (z / freshProduct S) a

/-- The Walsh expansion appearing on the right-hand side of equation (18). -/
noncomputable def freshWalshExpansion
    (omega : Omega) (z a b : ℕ) : ℝ :=
  ∑ S ∈ (freshPrimes a b).powerset,
    freshCharacter omega S * freshCoefficient omega z a S

/-- Equation (18): revealing the primes in `(a,b]` turns the smooth sum into
a Walsh polynomial in precisely those fresh Rademacher coordinates. -/
theorem Ψ_eq_freshWalshExpansion
    (omega : Omega) (z : ℕ) {a b : ℕ} (hab : a ≤ b) :
    Ψ omega z b = freshWalshExpansion omega z a b := by
  rw [Ψ_eq_sum_squarefreeSmoothSets]
  symm
  unfold freshWalshExpansion freshCoefficient
  simp_rw [Ψ_eq_sum_squarefreeSmoothSets, Finset.mul_sum]
  rw [Finset.sum_sigma']
  exact sum_freshOldPairs_eq_sum_squarefreeSmoothSets omega z hab

/-- Adding a single prime coordinate gives the martingale increment used in
equation (17). -/
theorem Ψ_prime_recurrence (omega : Omega) (z : ℕ) {p : ℕ}
    (hp : 0 < p) (hprime : p.Prime) :
    Ψ omega z p =
      Ψ omega z (p - 1) + ε omega p * Ψ omega (z / p) (p - 1) := by
  rw [Ψ_eq_freshWalshExpansion omega z (Nat.pred_le p)]
  unfold freshWalshExpansion freshCoefficient
  simp only [Nat.pred_eq_sub_one]
  rw [freshPrimes_pred_self hp, if_pos hprime]
  rw [show ({p} : Finset ℕ) = insert p ∅ by simp,
    Finset.sum_powerset_insert (s := ∅) (by simp)]
  simp

/-- At a nonprime cutoff the smooth sum does not change. -/
theorem Ψ_nonprime_recurrence (omega : Omega) (z : ℕ) {p : ℕ}
    (hp : 0 < p) (hprime : ¬p.Prime) :
    Ψ omega z p = Ψ omega z (p - 1) := by
  rw [Ψ_eq_freshWalshExpansion omega z (Nat.pred_le p)]
  unfold freshWalshExpansion freshCoefficient
  simp only [Nat.pred_eq_sub_one]
  rw [freshPrimes_pred_self hp, if_neg hprime]
  simp

theorem Ψ_recurrence (omega : Omega) (z : ℕ) {p : ℕ} (hp : 0 < p) :
    Ψ omega z p = Ψ omega z (p - 1) +
      if p.Prime then ε omega p * Ψ omega (z / p) (p - 1) else 0 := by
  by_cases hprime : p.Prime
  · simp only [if_pos hprime]
    exact Ψ_prime_recurrence omega z hp hprime
  · simp only [if_neg hprime, add_zero]
    exact Ψ_nonprime_recurrence omega z hp hprime

end Problem520
end Erdos
