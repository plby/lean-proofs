import ErdosProblems.Erdos964.Basic

/-!
# Counting independent local residue choices

This CRT statement permits a different finite set of allowed residues
at each prime. It is used for root classes with an additional coprimality
restriction in the semiprime second sum.
-/

namespace Erdos964

open scoped BigOperators Function

def squarefreeLocalRoots (d : ℕ) (S : ℕ → Finset ℕ) : Finset ℕ :=
  (Finset.range d).filter (fun n => ∀ p ∈ d.primeFactors, n % p ∈ S p)

theorem squarefree_dvd_iff_primeFactors (d n : ℕ) (hd : Squarefree d) :
    d ∣ n ↔ ∀ p ∈ d.primeFactors, p ∣ n := by
  constructor
  · intro h p hp
    exact (Nat.dvd_of_mem_primeFactors hp).trans h
  · intro h
    by_cases hn : n = 0
    · rw [hn]
      exact dvd_zero d
    · rw [← Nat.prod_primeFactors_of_squarefree hd]
      apply (Nat.prod_primeFactors_dvd_iff hn).mpr
      intro p hp
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, h p hp, hn⟩

theorem squarefree_coprime_iff_primeFactors (d n : ℕ) (hd : Squarefree d) :
    d.Coprime n ↔ ∀ p ∈ d.primeFactors, p.Coprime n := by
  have h : (∏ p ∈ d.primeFactors, p).Coprime n ↔
      ∀ p ∈ d.primeFactors, p.Coprime n := Nat.coprime_prod_left_iff
  simpa only [Nat.prod_primeFactors_of_squarefree hd] using h

theorem squarefreeLocalRoots_card (d : ℕ) (hd : Squarefree d) (S : ℕ → Finset ℕ)
    (hS : ∀ p ∈ d.primeFactors, S p ⊆ Finset.range p) :
    (squarefreeLocalRoots d S).card = ∏ p ∈ d.primeFactors, (S p).card := by
  classical
  let I := {p : ℕ // p ∈ d.primeFactors}
  let Choices := ∀ p : I, {n : ℕ // n ∈ S p.1}
  let l : List I := (Finset.univ : Finset I).toList
  let m : I → ℕ := fun p => p.1
  have hprime (p : I) : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  have hco : l.Pairwise (Nat.Coprime on m) := by
    apply Finset.univ.nodup_toList.pairwise_of_forall_ne
    intro p _ q _ hpq
    exact (Nat.coprime_primes (hprime p) (hprime q)).mpr
      (fun heq => hpq (Subtype.ext heq))
  have hprod : (l.map m).prod = d := by
    dsimp only [l]
    rw [Finset.prod_map_toList]
    change (∏ p : d.primeFactors, (p : ℕ)) = d
    exact (Finset.prod_coe_sort (f := fun p : ℕ => p) (s := d.primeFactors)).trans
      (Nat.prod_primeFactors_of_squarefree hd)
  have hm : ∀ p ∈ l, m p ≠ 0 := fun p _ => (hprime p).ne_zero
  let crt : Choices → ℕ := fun f =>
    Nat.chineseRemainderOfList (fun p => (f p).1) m l hco
  have hcrtlt (f : Choices) : crt f < d := by
    have h := Nat.chineseRemainderOfList_lt_prod (fun p => (f p).1) m l hco hm
    rwa [hprod] at h
  have hres (f : Choices) (p : I) : crt f % p.1 = (f p).1 := by
    have h := (Nat.chineseRemainderOfList (fun p => (f p).1) m l hco).property
      p (by simp [l])
    change crt f ≡ (f p).1 [MOD p.1] at h
    have hflt := Finset.mem_range.mp (hS p.1 p.2 (f p).2)
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hflt] using h
  have hmem (f : Choices) : crt f ∈ squarefreeLocalRoots d S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (hcrtlt f), ?_⟩
    intro p hp
    rw [hres f ⟨p, hp⟩]
    exact (f ⟨p, hp⟩).2
  have hinj : Function.Injective crt := by
    intro f g hfg
    funext p
    apply Subtype.ext
    rw [← hres f p, ← hres g p, hfg]
  have hsurj (n : ℕ) (hn : n ∈ squarefreeLocalRoots d S) : ∃ f : Choices, crt f = n := by
    have hn' := Finset.mem_filter.mp hn
    let f : Choices := fun p => ⟨n % p.1, hn'.2 p.1 p.2⟩
    refine ⟨f, ?_⟩
    have hmod : n ≡ crt f [MOD (l.map m).prod] :=
      Nat.chineseRemainderOfList_modEq_unique (fun p => (f p).1) m l hco
        (fun p _ => by simp [f, m, Nat.ModEq])
    rw [hprod] at hmod
    have hnt := Finset.mem_range.mp hn'.1
    have heq : n = crt f := by
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt hnt, Nat.mod_eq_of_lt (hcrtlt f)] using hmod
    exact heq.symm
  have hcard : (Finset.univ : Finset Choices).card = (squarefreeLocalRoots d S).card := by
    apply Finset.card_bij (fun f _ => crt f)
    · exact fun f _ => hmem f
    · exact fun _ _ _ _ h => hinj h
    · intro n hn
      obtain ⟨f, hf⟩ := hsurj n hn
      exact ⟨f, Finset.mem_univ f, hf⟩
  have hcard' : (squarefreeLocalRoots d S).card = ∏ p : I, (S p.1).card := by
    simpa only [Choices, Finset.card_univ, Fintype.card_pi, Fintype.card_coe] using hcard.symm
  exact hcard'.trans (Finset.prod_coe_sort
    (f := fun p : ℕ => (S p).card) (s := d.primeFactors))

end Erdos964
