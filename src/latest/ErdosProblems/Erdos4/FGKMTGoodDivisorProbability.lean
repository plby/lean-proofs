import ErdosProblems.Erdos4.FGKMTProductCoprimality

/-! Positive mass of coprime divisor tuples below a logarithmic product cutoff. -/

open scoped BigOperators

namespace Erdos4.FGKMT

theorem FiniteLaw.prob_and_lower {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (E F : Ω → Prop) :
    μ.prob E - μ.prob (fun o => ¬F o) ≤ μ.prob (fun o => E o ∧ F o) := by
  classical
  rw [FiniteLaw.prob_eq_mean, FiniteLaw.prob_eq_mean, FiniteLaw.prob_eq_mean, ← FiniteLaw.mean_sub]
  apply FiniteLaw.mean_mono
  intro o
  by_cases he : E o <;> by_cases hf : F o <;> simp [he, hf]

theorem rationalProduct_good_probability (I : Type*) [Fintype I] [DecidableEq I]
    (W : ℕ) {b : ℝ} (hb : 0 < b) {R K : ℕ} (hR : 1 ≤ R) (hK : 2 ≤ K)
    (hpre : ∀ p : ℕ, p.Prime → p ≤ K → p ∣ W) {L : ℝ} (hL : 0 < L) :
    1 - (Fintype.card I : ℝ) * rationalMass W b R / (b * rationalSquareMass W b R * L) -
      (Fintype.card I : ℝ) ^ 2 / ((K - 1 : ℕ) : ℝ) ≤
      (FiniteLaw.independent (fun _ : I => rationalSquareLaw W b R hR)).prob
        (fun a => (∑ i, Real.log (a i : ℕ)) ≤ L ∧
          Pairwise (fun i j => (a i : ℕ).Coprime (a j : ℕ))) := by
  let μ := FiniteLaw.independent (fun _ : I => rationalSquareLaw W b R hR)
  have hlog := rationalProduct_small_log_probability I W hb hR hL
  have hcop := rationalProduct_bad_coprime_probability I W hb.le hR hK hpre
  have hand := μ.prob_and_lower (fun a => (∑ i, Real.log (a i : ℕ)) ≤ L)
    (fun a => Pairwise (fun i j => (a i : ℕ).Coprime (a j : ℕ)))
  linarith

theorem rationalProduct_good_probability_half (I : Type*) [Fintype I] [DecidableEq I]
    (W : ℕ) {b : ℝ} (hb : 0 < b) {R K : ℕ} (hR : 1 ≤ R) (hK : 2 ≤ K)
    (hpre : ∀ p : ℕ, p.Prime → p ≤ K → p ∣ W) {L : ℝ} (hL : 0 < L)
    (hmean : (Fintype.card I : ℝ) * rationalMass W b R ≤
      (1 / 4) * (b * rationalSquareMass W b R * L))
    (hcollision : 4 * Fintype.card I ^ 2 ≤ K - 1) :
    (1 / 2 : ℝ) ≤
      (FiniteLaw.independent (fun _ : I => rationalSquareLaw W b R hR)).prob
        (fun a => (∑ i, Real.log (a i : ℕ)) ≤ L ∧
          Pairwise (fun i j => (a i : ℕ).Coprime (a j : ℕ))) := by
  have hM := zero_lt_one.trans_le (one_le_rationalSquareMass W b hR)
  have hden : 0 < b * rationalSquareMass W b R * L := by positivity
  have hm : (Fintype.card I : ℝ) * rationalMass W b R /
      (b * rationalSquareMass W b R * L) ≤ 1 / 4 := (div_le_iff₀ hden).mpr hmean
  have hKpos : (0 : ℝ) < (K - 1 : ℕ) := by exact_mod_cast (by omega : 0 < K - 1)
  have hc : (Fintype.card I : ℝ) ^ 2 / ((K - 1 : ℕ) : ℝ) ≤ 1 / 4 := by
    apply (div_le_iff₀ hKpos).mpr
    have hh : (4 : ℝ) * (Fintype.card I : ℝ) ^ 2 ≤ (K - 1 : ℕ) := by exact_mod_cast hcollision
    linarith
  have hh := rationalProduct_good_probability I W hb hR hK hpre hL
  linarith

end Erdos4.FGKMT
