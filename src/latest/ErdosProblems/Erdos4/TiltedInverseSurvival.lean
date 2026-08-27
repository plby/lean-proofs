import ErdosProblems.Erdos4.TiltedBlockLower
import ErdosProblems.Erdos4.EulerDensity

/-! Block importance weights are bounded by an explicit exponential. -/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT RandomResidueSieve Filter

theorem prime_reciprocal_sum_eq (x : ℕ) :
    prime_summatory (fun p => (p : ℝ)⁻¹) 1 (x : ℝ) = ∑ p ∈ x.primesLE, 1 / (p : ℝ) := by
  rw [prime_summatory, Nat.floor_natCast]
  have hset : (Finset.Icc 1 x).filter Nat.Prime = x.primesLE := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesLE]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨h.2.one_le, h.1⟩, h.2⟩⟩
  rw [hset]
  simp only [one_div]

universe u

theorem exists_indexed_prime_reciprocal_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      ∀ (P : Type u) [Fintype P] [DecidableEq P] (ell : P → ℕ)
        [∀ p, Fact (ell p).Prime], Function.Injective ell → (∀ p, ell p ≤ x) →
      (∑ p, 1 / (ell p : ℝ)) ≤ C * Real.log (Real.log (x : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := (prime_reciprocal_upper.comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).exists_pos
  refine ⟨C, hC, ?_⟩
  have hlogs := Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [hb.bound, hlogs.eventually (eventually_ge_atTop 0)] with x hbound hlogs
  change 0 ≤ Real.log (Real.log (x : ℝ)) at hlogs
  intro P _ _ ell _ hinj hupper
  have hsum : (∑ p ∈ x.primesLE, 1 / (p : ℝ)) ≤ C * Real.log (Real.log (x : ℝ)) := by
    have hn : 0 ≤ ∑ p ∈ x.primesLE, 1 / (p : ℝ) := Finset.sum_nonneg (fun p _ => by positivity)
    simpa only [Function.comp_apply, prime_reciprocal_sum_eq, Real.norm_eq_abs,
      abs_of_nonneg hn, abs_of_nonneg hlogs] using hbound
  have hsub : Finset.univ.image ell ⊆ x.primesLE := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact Nat.mem_primesLE.mpr ⟨hupper i, Fact.out⟩
  calc
    _ = ∑ p ∈ Finset.univ.image ell, 1 / (p : ℝ) :=
      (Finset.sum_image (fun i _ j _ hij => hinj hij)).symm
    _ ≤ ∑ p ∈ x.primesLE, 1 / (p : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    _ ≤ _ := hsum

variable {P : Type*} [Fintype P] [DecidableEq P]
  (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

theorem inverse_block_survival_le (hinj : Function.Injective ell) (τ : ℝ) (hτ : 0 ≤ τ)
    (T : Finset ℕ) {K Y : ℕ} (hY : 1 ≤ Y) (hT : T.card ≤ K)
    (hbound : ∀ n ∈ T, n ≤ Y) (hsmall : ∀ l, 2 * K + 1 ≤ ell l)
    (hsq : Squarefree (∏ n ∈ T, n))
    (hcomplete : ∀ p ∈ (∏ n ∈ T, n).primeFactors, ∃ l, ell l = p) :
    1 / (sieveLaw ell τ hτ).prob (fun a => Survives ell a T) ≤
      Real.exp (τ * K * Real.log Y + (4 * (K : ℝ) + 2) * ∑ l, 1 / (ell l : ℝ)) := by
  let N := ∏ n ∈ T, n
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hsq.ne_zero.bot_lt
  have hN : N ≤ Y ^ K := by
    calc
      _ ≤ ∏ _n ∈ T, Y := Finset.prod_le_prod' hbound
      _ = Y ^ T.card := Finset.prod_const Y
      _ ≤ _ := Nat.pow_le_pow_right hY hT
  have hlogN : Real.log (N : ℝ) ≤ (K : ℝ) * Real.log Y := by
    have hh := Real.log_le_log hNpos (by exact_mod_cast hN : (N : ℝ) ≤ (Y : ℝ) ^ K)
    simpa only [Real.log_pow] using hh
  let H := (4 * (K : ℝ) + 2) * ∑ l, 1 / (ell l : ℝ)
  have htilt : Real.exp (-(τ * K * Real.log Y)) ≤ (N : ℝ) ^ (-τ) := by
    rw [Real.rpow_def_of_pos hNpos]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hlogN hτ]
  have hprob : Real.exp (-(τ * K * Real.log Y + H)) ≤
      (sieveLaw ell τ hτ).prob (fun a => Survives ell a T) := by
    calc
      _ = Real.exp (-(τ * K * Real.log Y)) * Real.exp (-H) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ (N : ℝ) ^ (-τ) * Real.exp (-H) :=
        mul_le_mul_of_nonneg_right htilt (Real.exp_pos _).le
      _ ≤ _ := sieveLaw_block_lower ell hinj τ hτ T hT hsmall hsq hcomplete
  have hh := one_div_le_one_div_of_le (Real.exp_pos _) hprob
  simpa only [one_div, ← Real.exp_neg, neg_neg, H] using hh

end Erdos4.Tilted
