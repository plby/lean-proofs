import Util.Bernays.PrimeFactorConcentration

/-!
# One negligible exceptional set for all form classes of a discriminant
-/

open Filter Topology
open scoped Classical

namespace Bernays

theorem finiteUnion_card_div_tendsto_zero {α ι : Type*} [DecidableEq α] [Fintype ι]
    (F : ι → ℕ → Finset α) (s : ℕ → ℝ) (hs : ∀ N, 0 ≤ s N)
    (hF : ∀ i, Tendsto (fun N => ((F i N).card : ℝ) / s N) atTop (𝓝 0)) :
    Tendsto (fun N => ((Finset.univ.biUnion fun i => F i N).card : ℝ) / s N) atTop (𝓝 0) := by
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hF i)
  simp only [Finset.sum_const_zero] at hsum
  apply squeeze_zero (fun N => div_nonneg (Nat.cast_nonneg _) (hs N)) _ hsum
  intro N
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (hs N)
  exact_mod_cast Finset.card_biUnion_le

noncomputable def squareExceptionalValues {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) (k N : ℕ) : Finset ℕ := by
  letI := quadraticOrderIsDomain hD
  letI := quadraticOrderClassGroupFintype hD
  let G := ClassGroup (QuadraticAlgebra ℤ d b)
  letI : Fintype (Subgroup (classSquareSubgroup : Subgroup G)) := Fintype.ofFinite _
  exact Finset.univ.biUnion fun H : Subgroup (classSquareSubgroup : Subgroup G) =>
    if H = ⊤ then ∅ else
      fewPrimeFactorValues (fun p : ℕ => discriminantCharacter (b ^ 2 + 4 * d) hD.ne p = -1)
        (squareBadPrime hD H) k N

theorem squareExceptionalValues_div_scale_tendsto_zero {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) (k : ℕ) :
    Tendsto (fun N : ℕ => ((squareExceptionalValues hD k N).card : ℝ) / scale N) atTop (𝓝 0) := by
  letI := quadraticOrderIsDomain hD
  letI := quadraticOrderClassGroupFintype hD
  let G := ClassGroup (QuadraticAlgebra ℤ d b)
  letI : Fintype (Subgroup (classSquareSubgroup : Subgroup G)) := Fintype.ofFinite _
  apply finiteUnion_card_div_tendsto_zero _ (fun N => scale N)
    (fun N => div_nonneg (Nat.cast_nonneg N) (Real.sqrt_nonneg _))
  intro H
  by_cases hH : H = ⊤
  · simp only [if_pos hH, Finset.card_empty, Nat.cast_zero, zero_div]
    exact tendsto_const_nhds
  · simp only [if_neg hH]
    exact squareBadPrime_few_values_limit hD H hH k

theorem mem_squareExceptionalValues {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ H : Subgroup (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b))),
      H ≠ ⊤ → ∀ k N n : ℕ,
      n ∈ fewPrimeFactorValues (fun p : ℕ => discriminantCharacter (b ^ 2 + 4 * d) hD.ne p = -1)
        (squareBadPrime hD H) k N → n ∈ squareExceptionalValues hD k N := by
  letI := quadraticOrderIsDomain hD
  intro H hH k N n hn
  letI := quadraticOrderClassGroupFintype hD
  letI : Fintype (Subgroup (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b)))) :=
    Fintype.ofFinite _
  unfold squareExceptionalValues
  exact Finset.mem_biUnion.mpr ⟨H, Finset.mem_univ _, by simpa only [if_neg hH] using hn⟩

theorem missing_same_genus_mem_exceptional {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (I : InvertibleIdeal (QuadraticAlgebra ℤ d b)),
      IsCoprime (I : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      ∀ C : ClassGroup (QuadraticAlgebra ℤ d b),
      (QuotientGroup.mk' (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b)))) I.idealClass =
        (QuotientGroup.mk' (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b)))) C →
      (∀ J : InvertibleIdeal (QuadraticAlgebra ℤ d b),
        (J : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot →
        J.idealClass ≠ C) →
      ∀ N : ℕ, (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot ∈
        localValues (fun p : ℕ => discriminantCharacter (b ^ 2 + 4 * d) hD.ne p = -1) N →
      (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot ∈ squareExceptionalValues hD
        (Nat.card (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b)))) N := by
  letI := quadraticOrderIsDomain hD
  intro I hIF C hIC hmiss N hIN
  obtain ⟨k, P, hPI, hP⟩ := exists_goodMaximal_tuple hD I hIF
  have hclass : (∏ i, (P i).idealClass) = I.idealClass := by
    rw [← InvertibleIdeal.idealClass_prod, hPI]
  obtain ⟨H, hH, hfew⟩ := exists_squareSubgroup_of_missing_ideal_class hD P hP C
    (hclass ▸ hIC) (by simpa only [hPI] using hmiss)
  apply mem_squareExceptionalValues hD H hH _ N _
  apply Finset.mem_filter.mpr
  refine ⟨hIN, ?_⟩
  have hcount := badPrimeFactors_card_le_outside_coordinates hD P hP H
  rw [hPI] at hcount
  exact (hcount.trans_lt hfew).le

end Bernays
