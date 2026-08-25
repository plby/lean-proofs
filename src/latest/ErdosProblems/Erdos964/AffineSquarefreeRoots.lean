import ErdosProblems.Erdos964.AffinePrimeRoots

/-!
# Squarefree root multiplicities by CRT

The roots of the product of the affine forms modulo a squarefree integer
are the independent choices of roots modulo its prime divisors. For the
normalized triple this gives the exact local factor `3^ω(d)`.
-/

namespace Erdos964

open scoped BigOperators Function

theorem affine_product_modEq (A B : Fin 3 → ℕ) {q n m : ℕ} (h : n ≡ m [MOD q]) :
    (∏ i, (A i * n + B i)) ≡ (∏ i, (A i * m + B i)) [MOD q] := by
  rw [← ZMod.natCast_eq_natCast_iff] at h ⊢
  simp only [Nat.cast_prod, Nat.cast_add, Nat.cast_mul]
  rw [h]

theorem affineProductRoots_card_squarefree (A B : Fin 3 → ℕ) (d : ℕ) (hd : Squarefree d) :
    (affineProductRoots A B d).card =
      ∏ p ∈ d.primeFactors, (affineProductRoots A B p).card := by
  classical
  let I := {p : ℕ // p ∈ d.primeFactors}
  let Choices := ∀ p : I, {n : ℕ // n ∈ affineProductRoots A B p.1}
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
  have hres (f : Choices) (p : I) : crt f ≡ (f p).1 [MOD p.1] :=
    (Nat.chineseRemainderOfList (fun p => (f p).1) m l hco).property p (by simp [l])
  have hmem (f : Choices) : crt f ∈ affineProductRoots A B d := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (hcrtlt f), ?_⟩
    apply Nat.modEq_zero_iff_dvd.mp
    rw [← hprod]
    apply (Nat.modEq_list_map_prod_iff hco).mpr
    intro p _
    exact (affine_product_modEq A B (hres f p)).trans
      (Nat.modEq_zero_iff_dvd.mpr (Finset.mem_filter.mp (f p).2).2)
  have hinj : Function.Injective crt := by
    intro f g hfg
    funext p
    apply Subtype.ext
    have hmod : (f p).1 ≡ (g p).1 [MOD p.1] := by
      have h := (hres f p).symm
      rw [hfg] at h
      exact h.trans (hres g p)
    have hflt := Finset.mem_range.mp (Finset.mem_filter.mp (f p).2).1
    have hglt := Finset.mem_range.mp (Finset.mem_filter.mp (g p).2).1
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hflt, Nat.mod_eq_of_lt hglt] using hmod
  have hsurj (n : ℕ) (hn : n ∈ affineProductRoots A B d) : ∃ f : Choices, crt f = n := by
    have hn' := Finset.mem_filter.mp hn
    have hlocal (p : I) : n % p.1 ∈ affineProductRoots A B p.1 := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (Nat.mod_lt n (hprime p).pos), ?_⟩
      have hpn := (Nat.dvd_of_mem_primeFactors p.2).trans hn'.2
      have hmod : n % p.1 ≡ n [MOD p.1] := by simp [Nat.ModEq]
      exact Nat.modEq_zero_iff_dvd.mp
        ((affine_product_modEq A B hmod).trans (Nat.modEq_zero_iff_dvd.mpr hpn))
    let f : Choices := fun p => ⟨n % p.1, hlocal p⟩
    refine ⟨f, ?_⟩
    have hmod : n ≡ crt f [MOD (l.map m).prod] :=
      Nat.chineseRemainderOfList_modEq_unique (fun p => (f p).1) m l hco
        (fun p _ => by simp [f, m, Nat.ModEq])
    rw [hprod] at hmod
    have hnt := Finset.mem_range.mp hn'.1
    have heq : n = crt f := by
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt hnt, Nat.mod_eq_of_lt (hcrtlt f)] using hmod
    exact heq.symm
  have hcard : (Finset.univ : Finset Choices).card = (affineProductRoots A B d).card := by
    apply Finset.card_bij (fun f _ => crt f)
    · exact fun f _ => hmem f
    · exact fun _ _ _ _ h => hinj h
    · intro n hn
      obtain ⟨f, hf⟩ := hsurj n hn
      exact ⟨f, Finset.mem_univ f, hf⟩
  have hcard' : (affineProductRoots A B d).card =
      ∏ p : I, (affineProductRoots A B p.1).card := by
    simpa only [Choices, Finset.card_univ, Fintype.card_pi, Fintype.card_coe] using hcard.symm
  change (affineProductRoots A B d).card =
    ∏ p : d.primeFactors, (affineProductRoots A B p.1).card at hcard'
  exact hcard'.trans (Finset.prod_coe_sort
    (f := fun p : ℕ => (affineProductRoots A B p).card) (s := d.primeFactors))

theorem normalized_affineProductRoots_card_squarefree (A B : Fin 3 → ℕ) (v d : ℕ)
    (hd : Squarefree d) (hdM : d.Coprime (affineNormalizationModulus A B)) :
    (affineProductRoots (fun i => A i * affineNormalizationModulus A B)
      (fun i => A i * v + B i) d).card = 3 ^ d.primeFactors.card := by
  rw [affineProductRoots_card_squarefree _ _ d hd]
  have hlocal (p : ℕ) (hp : p ∈ d.primeFactors) :
      (affineProductRoots (fun i => A i * affineNormalizationModulus A B)
        (fun i => A i * v + B i) p).card = 3 := by
    have hpprime := Nat.prime_of_mem_primeFactors hp
    apply normalized_affineProductRoots_card A B v p hpprime
    exact hpprime.coprime_iff_not_dvd.mp (hdM.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp))
  rw [Finset.prod_congr rfl hlocal]
  simp

end Erdos964
