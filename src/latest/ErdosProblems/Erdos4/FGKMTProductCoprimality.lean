import ErdosProblems.Erdos4.FGKMTDivisorProbability
import ErdosProblems.Erdos4.FGKMTQuantitativeTail
import ErdosProblems.Erdos4.FGKMTSupport
import Mathlib.NumberTheory.PrimeCounting

/-! Quantitative removal of shared prime factors from the product divisor law. -/

open scoped BigOperators

namespace Erdos4.FGKMT

namespace FiniteLaw

variable {Ω I : Type*} [Fintype Ω] [Fintype I]

theorem prob_mono_support (μ : FiniteLaw Ω) {E F : Ω → Prop}
    (h : ∀ o, 0 < μ.weight o → E o → F o) : μ.prob E ≤ μ.prob F := by
  classical
  rw [prob_eq_mean, prob_eq_mean]
  apply mean_mono_support
  intro o ho
  by_cases he : E o
  · simp only [if_pos he, if_pos (h o ho he), le_refl]
  · simp only [if_neg he]
    split_ifs <;> norm_num

theorem prob_exists_le (μ : FiniteLaw Ω) (E : I → Ω → Prop) :
    μ.prob (fun o => ∃ i, E i o) ≤ ∑ i, μ.prob (E i) := by
  simpa only [Finset.mem_univ, true_and] using μ.prob_exists_finset_le Finset.univ E

theorem prob_false (μ : FiniteLaw Ω) : μ.prob (fun _ => False) = 0 := by
  classical
  simp [prob]

end FiniteLaw

variable (I : Type*) [Fintype I] [DecidableEq I]

theorem rationalProduct_prime_collision (W : ℕ) {b : ℝ} (hb : 0 ≤ b)
    {R : ℕ} (hR : 1 ≤ R) {p : ℕ} (hp : p.Prime) :
    (FiniteLaw.independent (fun _ : I => rationalSquareLaw W b R hR)).prob
      (fun a => ∃ i j : I, i ≠ j ∧ p ∣ (a i : ℕ) ∧ p ∣ (a j : ℕ)) ≤
        (Fintype.card I : ℝ) ^ 2 * (((p : ℝ) - 1)⁻¹) ^ 2 := by
  classical
  let μ := FiniteLaw.independent (fun _ : I => rationalSquareLaw W b R hR)
  have hpoint (i j : I) : μ.prob (fun a => i ≠ j ∧ p ∣ (a i : ℕ) ∧ p ∣ (a j : ℕ)) ≤
      (((p : ℝ) - 1)⁻¹) ^ 2 := by
    by_cases hij : i = j
    · subst j
      simp only [ne_eq, not_true_eq_false, false_and, FiniteLaw.prob_false]
      positivity
    · have hh := (μ.prob_mono (fun (a : I → Fin (R + 1))
        (h : i ≠ j ∧ p ∣ (a i : ℕ) ∧ p ∣ (a j : ℕ)) => h.2)).trans
        (rationalProduct_pair_divisor_probability I W hb hR hij hp.pos)
      simpa only [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one] using hh
  calc
    _ ≤ ∑ i : I, μ.prob (fun a => ∃ j : I, i ≠ j ∧ p ∣ (a i : ℕ) ∧ p ∣ (a j : ℕ)) :=
      μ.prob_exists_le _
    _ ≤ ∑ i : I, ∑ j : I, μ.prob (fun a => i ≠ j ∧ p ∣ (a i : ℕ) ∧ p ∣ (a j : ℕ)) :=
      Finset.sum_le_sum (fun i _ => μ.prob_exists_le _)
    _ ≤ ∑ _i : I, ∑ _j : I, (((p : ℝ) - 1)⁻¹) ^ 2 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpoint i j))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem rationalProduct_bad_coprime_imp_collision (W : ℕ) (b : ℝ)
    {R K : ℕ} (hR : 1 ≤ R)
    (hpre : ∀ p : ℕ, p.Prime → p ≤ K → p ∣ W)
    (a : I → Fin (R + 1))
    (ha : 0 < (FiniteLaw.independent (fun _ : I => rationalSquareLaw W b R hR)).weight a)
    (hbad : ¬Pairwise (fun i j => (a i : ℕ).Coprime (a j : ℕ))) :
    ∃ p ∈ (Nat.primesLE R).filter (fun p => K < p),
      ∃ i j : I, i ≠ j ∧ p ∣ (a i : ℕ) ∧ p ∣ (a j : ℕ) := by
  classical
  by_contra hnone
  apply hbad
  intro i j hij
  by_contra hnc
  obtain ⟨p, hp, hpi, hpj⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
  have hsupport := rationalSquareLaw_support W b hR (a i)
    (FiniteLaw.independent_support (fun _ : I => rationalSquareLaw W b R hR) a ha i)
  have hpos : 0 < (a i : ℕ) := Nat.pos_of_ne_zero hsupport.1.ne_zero
  have hpR : p ≤ R := (Nat.le_of_dvd hpos hpi).trans (by have hh := (a i).isLt; omega)
  have hKp : K < p := by
    by_contra hle
    have hpW := hpre p hp (by omega)
    have hpcop := hsupport.2.of_dvd hpi hpW
    exact hp.ne_one (by simpa using hpcop)
  exact hnone ⟨p, Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpR, hp⟩, hKp⟩,
    i, j, hij, hpi, hpj⟩

theorem rationalProduct_bad_coprime_probability (W : ℕ) {b : ℝ} (hb : 0 ≤ b)
    {R K : ℕ} (hR : 1 ≤ R) (hK : 2 ≤ K)
    (hpre : ∀ p : ℕ, p.Prime → p ≤ K → p ∣ W) :
    (FiniteLaw.independent (fun _ : I => rationalSquareLaw W b R hR)).prob
      (fun a => ¬Pairwise (fun i j => (a i : ℕ).Coprime (a j : ℕ))) ≤
        (Fintype.card I : ℝ) ^ 2 / ((K - 1 : ℕ) : ℝ) := by
  classical
  let μ := FiniteLaw.independent (fun _ : I => rationalSquareLaw W b R hR)
  let P := (Nat.primesLE R).filter (fun p => K < p)
  have hpoint : μ.prob (fun a => ¬Pairwise (fun i j => (a i : ℕ).Coprime (a j : ℕ))) ≤
      μ.prob (fun a => ∃ p ∈ P, ∃ i j : I, i ≠ j ∧ p ∣ (a i : ℕ) ∧ p ∣ (a j : ℕ)) :=
    μ.prob_mono_support (fun a ha hbad => rationalProduct_bad_coprime_imp_collision I W b hR hpre a ha hbad)
  calc
    _ ≤ μ.prob (fun a => ∃ p ∈ P, ∃ i j : I, i ≠ j ∧ p ∣ (a i : ℕ) ∧ p ∣ (a j : ℕ)) := hpoint
    _ ≤ ∑ p ∈ P, μ.prob (fun a => ∃ i j : I, i ≠ j ∧ p ∣ (a i : ℕ) ∧ p ∣ (a j : ℕ)) :=
      μ.prob_exists_finset_le P _
    _ ≤ ∑ p ∈ P, (Fintype.card I : ℝ) ^ 2 * (((p : ℝ) - 1)⁻¹) ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      exact rationalProduct_prime_collision I W hb hR
        (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1)
    _ = (Fintype.card I : ℝ) ^ 2 * ∑ p ∈ P, (((p : ℝ) - 1)⁻¹) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (Fintype.card I : ℝ) ^ 2 * (((K - 1 : ℕ) : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_left (finite_shifted_reciprocal_square_tail hK P
        (fun p hp => (Finset.mem_filter.mp hp).2)) (sq_nonneg _)
    _ = _ := by rw [div_eq_mul_inv]

end Erdos4.FGKMT
