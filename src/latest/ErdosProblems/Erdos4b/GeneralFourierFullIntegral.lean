/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierSupportCutoff
import ErdosProblems.Erdos4b.GeneralFourierPresievedProduct

/-!
# Exact full Euler-integral representation of compact Selberg profiles

Finite-prime integrals stabilize because the original profiles have
compact support. Their dominated-convergence limit is therefore equal
to the same finite arithmetic coefficient sum.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology ContDiff

def boundedFourierPrimes (B : ℕ) : Finset Nat.Primes := (Nat.primesLE B).subtype Nat.Prime

theorem mem_boundedFourierPrimes (B : ℕ) (p : Nat.Primes) :
    p ∈ boundedFourierPrimes B ↔ p.val ≤ B := by
  rcases p with ⟨p, hp⟩
  simpa only [Nat.mem_primesLE, hp, and_true] using!
    (Finset.mem_subtype (p := Nat.Prime) (s := Nat.primesLE B) (a := ⟨p, hp⟩))

def selectedFourierPrimeCutoff (select : ℕ → Bool) (Q : Finset Nat.Primes) : Finset ℕ :=
  (Q.filter (fun p : Nat.Primes ↦ select p.val)).image (fun p : Nat.Primes ↦ p.val)

theorem selectedFourierPrimeCutoff_prime (select : ℕ → Bool) (Q : Finset Nat.Primes) :
    ∀ p ∈ selectedFourierPrimeCutoff select Q, p.Prime := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  exact q.property

theorem selectedFourierPrimeCutoff_filter_eq
    (select : ℕ → Bool) (B : ℕ) {Q : Finset Nat.Primes} (hQ : boundedFourierPrimes B ⊆ Q) :
    (selectedFourierPrimeCutoff select Q).filter (· ≤ B) =
      selectedFourierPrimeCutoff select (boundedFourierPrimes B) := by
  ext n
  constructor
  · intro hn
    obtain ⟨hnP, hnB⟩ := Finset.mem_filter.mp hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hnP
    exact Finset.mem_image.mpr ⟨p,
      Finset.mem_filter.mpr
        ⟨(mem_boundedFourierPrimes B p).mpr hnB, (Finset.mem_filter.mp hp).2⟩, rfl⟩
  · intro hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hpB, hpselect⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hQ hpB, hpselect⟩, rfl⟩,
        (mem_boundedFourierPrimes B p).mp hpB⟩

theorem prod_selectedFourierPrimeCutoff {ι : Type*} [Fintype ι]
    (select : ℕ → Bool) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) (Q : Finset Nat.Primes) :
    (∏ p ∈ selectedFourierPrimeCutoff select Q, doubledFourierPrimeFactor edges companion s p) =
      ∏ p ∈ Q, selectedDoubledFourierPrimeFactor select edges companion s p := by
  classical
  rw [prod_selectedDoubledFourierPrimeFactor]
  exact Finset.prod_image (fun p hp q hq h ↦ Subtype.ext h)

theorem exists_doubledFourierTensor_halfPlane {ι : Type*} [Finite ι]
    (L : (ι ⊕ ι) → Bool → ℝ) (hL : ∀ i b, 0 < L i b) :
    ∃ σ > 1, ∀ i b, σ - 1 ≤ (L i b)⁻¹ := by
  let _ : Fintype ι := Fintype.ofFinite ι
  let M : ℝ := (∑ ib : (ι ⊕ ι) × Bool, L ib.1 ib.2) + 1
  have hsum : 0 ≤ ∑ ib : (ι ⊕ ι) × Bool, L ib.1 ib.2 :=
    Finset.sum_nonneg fun ib hib ↦ (hL ib.1 ib.2).le
  have hM : 0 < M := by dsimp [M]; linarith
  refine ⟨1 + M⁻¹, by have := inv_pos.mpr hM; linarith, ?_⟩
  intro i b
  have hi : L i b ≤ M := by
    have h := Finset.single_le_sum (s := (Finset.univ : Finset ((ι ⊕ ι) × Bool)))
      (f := fun ib ↦ L ib.1 ib.2) (fun ib hib ↦ (hL ib.1 ib.2).le) (Finset.mem_univ (i, b))
    dsimp [M]
    linarith
  have hinv := (inv_le_inv₀ hM (hL i b)).mpr hi
  simpa only [add_sub_cancel_left] using hinv

theorem exists_compactProfileTensor_fullEuler_integral
    {ι : Type*} [Fintype ι]
    (select : ℕ → Bool) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (hedges : ∀ p : Nat.Primes, ∀ ij ∈ edges p, companion p = true)
    (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ)
    (hcompact : ∀ ib, HasCompactSupport (laplaceFourierProfile (f ib)))
    (L : (ι ⊕ ι) → Bool → ℝ) (hL : ∀ i b, 0 < L i b) :
    ∃ B : ℕ,
      cutoffSelbergProfileTensorSum (selectedFourierPrimeCutoff select (boundedFourierPrimes B))
        edges companion (fun ib ↦ laplaceFourierProfile (f ib)) L =
      ∫ ξ, (∏' p : Nat.Primes, selectedDoubledFourierPrimeFactor select edges companion
        (doubledFourierTensorExponents L ξ) p) * doubledFourierTensor f ξ := by
  classical
  obtain ⟨B, hB⟩ := exists_cutoffSelbergProfileTensorSum_stabilization
    (fun ib ↦ laplaceFourierProfile (f ib)) hcompact L hL
  obtain ⟨σ, hσ, hσL⟩ := exists_doubledFourierTensor_halfPlane L hL
  refine ⟨B, ?_⟩
  have hlimit := tendsto_integral_selectedDoubledFourierPrimeProducts volume select edges companion
    (doubledFourierTensorExponents L) (continuous_doubledFourierTensorExponents L)
    (doubledFourierTensor f) (integrable_doubledFourierTensor f) hσ
    (fun ξ i b ↦ by rw [doubledFourierTensorExponents_re]; exact hσL i b)
  have heventual : ∀ᶠ Q : Finset Nat.Primes in atTop,
      (∫ ξ, (∏ p ∈ Q, selectedDoubledFourierPrimeFactor select edges companion
        (doubledFourierTensorExponents L ξ) p) * doubledFourierTensor f ξ) =
      cutoffSelbergProfileTensorSum (selectedFourierPrimeCutoff select (boundedFourierPrimes B))
        edges companion (fun ib ↦ laplaceFourierProfile (f ib)) L := by
    filter_upwards [eventually_ge_atTop (boundedFourierPrimes B)] with Q hQ
    have hP := selectedFourierPrimeCutoff_prime select Q
    have hE : ∀ p ∈ selectedFourierPrimeCutoff select Q, ∀ ij ∈ edges p, companion p = true :=
      fun p hp ↦ hedges ⟨p, hP p hp⟩
    have hfinite := cutoffSelbergProfileTensorSum_eq_integral_finiteEulerProduct
      (selectedFourierPrimeCutoff select Q) hP edges companion hE f L hL
    simp_rw [prod_selectedFourierPrimeCutoff select edges companion] at hfinite
    rw [← hfinite, ← hB (selectedFourierPrimeCutoff select Q) hP edges companion,
      selectedFourierPrimeCutoff_filter_eq select B hQ]
  have hconstant := tendsto_const_nhds.congr' (Filter.EventuallyEq.symm heventual)
  exact (tendsto_nhds_unique hlimit hconstant).symm

theorem exists_smoothCompactProfileTensor_fullEuler_integral
    {ι : Type*} [Fintype ι]
    (select : ℕ → Bool) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (hedges : ∀ p : Nat.Primes, ∀ ij ∈ edges p, companion p = true)
    (F : ((ι ⊕ ι) × Bool) → ℝ → ℂ)
    (hcompact : ∀ ib, HasCompactSupport (F ib)) (hsmooth : ∀ ib, ContDiff ℝ ∞ (F ib))
    (L : (ι ⊕ ι) → Bool → ℝ) (hL : ∀ i b, 0 < L i b) :
    ∃ f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ,
      (∀ ib t, laplaceFourierProfile (f ib) t = F ib t) ∧
      ∃ B : ℕ,
        cutoffSelbergProfileTensorSum (selectedFourierPrimeCutoff select (boundedFourierPrimes B))
          edges companion F L =
        ∫ ξ, (∏' p : Nat.Primes, selectedDoubledFourierPrimeFactor select edges companion
          (doubledFourierTensorExponents L ξ) p) * doubledFourierTensor f ξ := by
  classical
  choose f hf using fun ib ↦ exists_schwartz_laplaceFourierProfile (F ib) (hcompact ib) (hsmooth ib)
  have hprofile : (fun ib ↦ laplaceFourierProfile (f ib)) = F := by
    funext ib t
    exact hf ib t
  have hcompact' : ∀ ib, HasCompactSupport (laplaceFourierProfile (f ib)) := by
    change ∀ ib, HasCompactSupport ((fun ib ↦ laplaceFourierProfile (f ib)) ib)
    rw [hprofile]
    exact hcompact
  obtain ⟨B, hB⟩ := exists_compactProfileTensor_fullEuler_integral
    select edges companion hedges f hcompact' L hL
  exact ⟨f, hf, B, by simpa only [hprofile] using hB⟩

end

end Erdos4b
