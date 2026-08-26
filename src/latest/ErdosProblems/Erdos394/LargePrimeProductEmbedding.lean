import ErdosProblems.Erdos394.PrimeWeightedBlockLower

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Injective embedding of selected-modulus/large-prime pairs
-/

open Nat Finset

namespace Erdos394

/-- A prime above every prime in `P` cannot be confused with the selected
prime product. Thus representations `ell·∏T` are unique. -/
theorem largePrime_mul_primeProduct_injective
    (P T U : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hTP : T ⊆ P) (hUP : U ⊆ P) {y ell r : ℕ}
    (hPupper : ∀ p ∈ P, p ≤ y)
    (hell : ell.Prime) (hr : r.Prime) (hyell : y < ell) (hyr : y < r)
    (heq : ell * primeProduct T = r * primeProduct U) :
    T = U ∧ ell = r := by
  have helldvd : ell ∣ r * primeProduct U := by
    rw [← heq]
    exact dvd_mul_right ell (primeProduct T)
  rcases hell.dvd_mul.mp helldvd with hellr | hellq
  · have hellEq : ell = r :=
      (Nat.prime_dvd_prime_iff_eq hell hr).mp hellr
    subst r
    have hqeq : primeProduct T = primeProduct U := by
      exact Nat.eq_of_mul_eq_mul_left hell.pos heq
    exact ⟨primeProduct_injective_on_prime_sets
      (fun p hp ↦ hprime p (hTP hp))
      (fun p hp ↦ hprime p (hUP hp)) hqeq, rfl⟩
  · rw [primeProduct] at hellq
    obtain ⟨p, hpU, hellp⟩ :=
      (_root_.Prime.dvd_finsetProd_iff hell.prime (fun p : ℕ ↦ p)).mp hellq
    have heqPrime : ell = p :=
      (Nat.prime_dvd_prime_iff_eq hell (hprime p (hUP hpU))).mp hellp
    have hpY := hPupper p (hUP hpU)
    omega

/-- Finite set of shifted-good primes for a selected modulus. -/
noncomputable def shiftedGoodPrimeSet
    (P : Finset ℕ) (K Y A U : ℕ) (hprime : ∀ p ∈ P, p.Prime) : Finset ℕ := by
  classical
  exact (largePrimeInterval A U).filter (fun ell ↦
    if hcop : ell.Coprime (primeProduct P) then
      ZMod.unitOfCoprime ell hcop ∉
        globalShiftedRootBadUnitSet P K Y hprime
    else False)

/-- The indicator-form shifted-good mass is exactly a sum over its support. -/
theorem shiftedGoodPrimeTMass_eq_sum_set
    (P : Finset ℕ) (K Y A U : ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    shiftedGoodPrimeTMass P K Y A U hprime =
      ∑ ell ∈ shiftedGoodPrimeSet P K Y A U hprime,
        (t K (ell * primeProduct P) : ℝ) := by
  classical
  unfold shiftedGoodPrimeTMass shiftedGoodPrimeSet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ell hell
  by_cases hcop : ell.Coprime (primeProduct P)
  · by_cases hgood : ZMod.unitOfCoprime ell hcop ∉
        globalShiftedRootBadUnitSet P K Y hprime
    · simp [hcop, hgood]
    · have hbad : ZMod.unitOfCoprime ell hcop ∈
          globalShiftedRootBadUnitSet P K Y hprime := not_not.mp hgood
      simp [hcop, hbad]
  · simp [hcop]

/-- Nested large-prime constructions over selected subsets inject into the
ordinary `t_K` sum whenever all represented integers lie in `[1,X]`. -/
theorem sum_selected_largePrime_t_le_full_sum
    (K X y : ℕ) (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hPupper : ∀ p ∈ P, p ≤ y)
    (outer : Finset (Finset ℕ)) (L : Finset ℕ → Finset ℕ)
    (houter : ∀ T ∈ outer, T ⊆ P)
    (hLprime : ∀ T ∈ outer, ∀ ell ∈ L T, ell.Prime)
    (hLlarge : ∀ T ∈ outer, ∀ ell ∈ L T, y < ell)
    (hLX : ∀ T ∈ outer, ∀ ell ∈ L T,
      0 < ell * primeProduct T ∧ ell * primeProduct T ≤ X) :
    (∑ T ∈ outer, ∑ ell ∈ L T,
      (t K (ell * primeProduct T) : ℝ)) ≤
      ∑ n ∈ Finset.Icc 1 X, (t K n : ℝ) := by
  classical
  let pairs := outer.sigma L
  let g : (T : Finset ℕ) × Nat → ℕ := fun z ↦ z.snd * primeProduct z.fst
  have hginj : Set.InjOn g (↑pairs) := by
    intro a ha b hb hab
    have ha' := Finset.mem_sigma.mp ha
    have hb' := Finset.mem_sigma.mp hb
    have huniq := largePrime_mul_primeProduct_injective P a.fst b.fst hprime
      (houter a.fst ha'.1) (houter b.fst hb'.1) hPupper
      (hLprime a.fst ha'.1 a.snd ha'.2)
      (hLprime b.fst hb'.1 b.snd hb'.2)
      (hLlarge a.fst ha'.1 a.snd ha'.2)
      (hLlarge b.fst hb'.1 b.snd hb'.2) hab
    apply Sigma.ext huniq.1
    exact heq_of_eq huniq.2
  have himage : pairs.image g ⊆ Finset.Icc 1 X := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
    have ha' := Finset.mem_sigma.mp ha
    exact Finset.mem_Icc.mpr (hLX a.fst ha'.1 a.snd ha'.2)
  calc
    (∑ T ∈ outer, ∑ ell ∈ L T,
      (t K (ell * primeProduct T) : ℝ)) =
        ∑ a ∈ pairs, (t K (g a) : ℝ) := by
      exact Finset.sum_sigma' outer L
        (fun T ell ↦ (t K (ell * primeProduct T) : ℝ))
    _ = ∑ n ∈ pairs.image g, (t K n : ℝ) := by
      rw [Finset.sum_image hginj]
    _ ≤ ∑ n ∈ Finset.Icc 1 X, (t K n : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro n hn hnot
      positivity

end Erdos394
