import ErdosProblems.Erdos4.FGKMTRationalLinearLaw
import ErdosProblems.Erdos4.FGKMTMixedCoprimality
import ErdosProblems.Erdos4.FGKMTGoodDivisorProbability

/-!
The product law for a core of squared profile factors and two unsquared
face factors. All outcomes belong to a common finite interval.
-/

open scoped BigOperators

namespace Erdos4.FGKMT

variable (I : Type*) [Fintype I] [DecidableEq I]

noncomputable def mixedDivisorMarginal (W : ℕ) {b : ℝ} (hb : 0 ≤ b)
    {R T : ℕ} (hR : 1 ≤ R) (hT : 1 ≤ T) (hTR : T ≤ R) :
    I ⊕ Fin 2 → FiniteLaw (Fin (R + 1))
  | Sum.inl _ => rationalSquareLaw W b R hR
  | Sum.inr _ => rationalFaceLaw W hb hT hTR

noncomputable def mixedDivisorLaw (W : ℕ) {b : ℝ} (hb : 0 ≤ b)
    {R T : ℕ} (hR : 1 ≤ R) (hT : 1 ≤ T) (hTR : T ≤ R) :
    FiniteLaw ((I ⊕ Fin 2) → Fin (R + 1)) :=
  FiniteLaw.independent (mixedDivisorMarginal I W hb hR hT hTR)

omit [Fintype I] [DecidableEq I] in
theorem mixedDivisorMarginal_support (W : ℕ) {b : ℝ} (hb : 0 ≤ b)
    {R T : ℕ} (hR : 1 ≤ R) (hT : 1 ≤ T) (hTR : T ≤ R)
    (i : I ⊕ Fin 2) (n : Fin (R + 1))
    (hn : 0 < (mixedDivisorMarginal I W hb hR hT hTR i).weight n) :
    Squarefree (n : ℕ) ∧ (n : ℕ).Coprime W := by
  cases i with
  | inl i => exact rationalSquareLaw_support W b hR n hn
  | inr i =>
    have hs := rationalFaceLaw_support W hb hT hTR n hn
    exact ⟨hs.1, hs.2.1⟩

omit [Fintype I] [DecidableEq I] in
theorem mixedDivisorMarginal_prob_divisor_le (W : ℕ) {b : ℝ} (hb : 0 ≤ b)
    {R T : ℕ} (hR : 1 ≤ R) (hT : 1 ≤ T) (hTR : T ≤ R)
    (i : I ⊕ Fin 2) {d : ℕ} (hd : 0 < d) :
    (mixedDivisorMarginal I W hb hR hT hTR i).prob (fun n => d ∣ (n : ℕ)) ≤
      (d.totient : ℝ)⁻¹ := by
  cases i with
  | inl i => exact rationalSquareLaw_prob_divisor_le W hb hR hd
  | inr i => exact rationalFaceLaw_prob_divisor_le W hb hT hTR hd

theorem mixedDivisorLaw_bad_coprime_probability (W : ℕ) {b : ℝ} (hb : 0 ≤ b)
    {R T K : ℕ} (hR : 1 ≤ R) (hT : 1 ≤ T) (hTR : T ≤ R) (hK : 2 ≤ K)
    (hpre : ∀ p : ℕ, p.Prime → p ≤ K → p ∣ W) :
    (mixedDivisorLaw I W hb hR hT hTR).prob
      (fun a => ¬Pairwise (fun i j => (a i : ℕ).Coprime (a j : ℕ))) ≤
        ((Fintype.card I : ℝ) + 2) ^ 2 / ((K - 1 : ℕ) : ℝ) := by
  have hh := independent_bad_coprime_probability
    (mixedDivisorMarginal I W hb hR hT hTR) hK
    (fun i n hn =>
      ⟨Nat.pos_of_ne_zero (mixedDivisorMarginal_support I W hb hR hT hTR i n hn).1.ne_zero,
        (mixedDivisorMarginal_support I W hb hR hT hTR i n hn).2⟩) hpre
    (fun i p hp => mixedDivisorMarginal_prob_divisor_le I W hb hR hT hTR i hp.pos)
  simpa only [mixedDivisorLaw, Fintype.card_sum, Fintype.card_fin,
    Nat.cast_add, Nat.cast_ofNat] using hh

noncomputable def mixedCoreLog {R : ℕ} (a : (I ⊕ Fin 2) → Fin (R + 1)) : ℝ :=
  ∑ i : I, Real.log (a (Sum.inl i) : ℕ)

theorem mixedDivisorLaw_core_probability (W : ℕ) {b : ℝ} (hb : 0 < b)
    {R T : ℕ} (hR : 1 ≤ R) (hT : 1 ≤ T) (hTR : T ≤ R) {L : ℝ} (hL : 0 < L) :
    1 - (Fintype.card I : ℝ) * rationalMass W b R / (b * rationalSquareMass W b R * L) ≤
      (mixedDivisorLaw I W hb.le hR hT hTR).prob (fun a => mixedCoreLog I a ≤ L) := by
  let f : I ⊕ Fin 2 → Fin (R + 1) → ℝ := fun i n =>
    match i with
    | Sum.inl _ => Real.log (n : ℕ)
    | Sum.inr _ => 0
  have hf : ∀ i n, 0 ≤ f i n := by
    intro i n
    cases i with
    | inl _ => exact Real.log_natCast_nonneg n
    | inr _ => exact le_rfl
  have hh := FiniteLaw.independent_sum_good
    (mixedDivisorMarginal I W hb.le hR hT hTR) f hf hL
  have hsum (a : (I ⊕ Fin 2) → Fin (R + 1)) :
      (∑ i, f i (a i)) = mixedCoreLog I a := by
    simp only [Fintype.sum_sum_type, f, Finset.sum_const_zero, add_zero, mixedCoreLog]
  have hmean :
      (∑ i, (mixedDivisorMarginal I W hb.le hR hT hTR i).mean (f i)) ≤
        (Fintype.card I : ℝ) * (rationalMass W b R / (b * rationalSquareMass W b R)) := by
    simp only [Fintype.sum_sum_type, mixedDivisorMarginal, f, FiniteLaw.mean_const,
      Finset.sum_const_zero, add_zero]
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      Finset.sum_le_sum (s := (Finset.univ : Finset I))
        (fun _ _ => rationalSquareLaw_mean_log_le W hb hR)
  simp_rw [hsum] at hh
  have hdiv := div_le_div_of_nonneg_right hmean hL.le
  have heq : (Fintype.card I : ℝ) * (rationalMass W b R / (b * rationalSquareMass W b R)) / L =
      (Fintype.card I : ℝ) * rationalMass W b R / (b * rationalSquareMass W b R * L) := by ring
  rw [heq] at hdiv
  exact (sub_le_sub_left hdiv 1).trans hh

theorem mixedDivisorLaw_good_probability (W : ℕ) {b : ℝ} (hb : 0 < b)
    {R T K : ℕ} (hR : 1 ≤ R) (hT : 1 ≤ T) (hTR : T ≤ R) (hK : 2 ≤ K)
    (hpre : ∀ p : ℕ, p.Prime → p ≤ K → p ∣ W) {L : ℝ} (hL : 0 < L) :
    1 - (Fintype.card I : ℝ) * rationalMass W b R / (b * rationalSquareMass W b R * L) -
      ((Fintype.card I : ℝ) + 2) ^ 2 / ((K - 1 : ℕ) : ℝ) ≤
      (mixedDivisorLaw I W hb.le hR hT hTR).prob
        (fun a => mixedCoreLog I a ≤ L ∧ Pairwise (fun i j => (a i : ℕ).Coprime (a j : ℕ))) := by
  have hlog := mixedDivisorLaw_core_probability I W hb hR hT hTR hL
  have hcop := mixedDivisorLaw_bad_coprime_probability I W hb.le hR hT hTR hK hpre
  have hand := (mixedDivisorLaw I W hb.le hR hT hTR).prob_and_lower
    (fun a => mixedCoreLog I a ≤ L) (fun a => Pairwise (fun i j => (a i : ℕ).Coprime (a j : ℕ)))
  linarith

theorem mixedDivisorLaw_good_probability_half (W : ℕ) {b : ℝ} (hb : 0 < b)
    {R T K : ℕ} (hR : 1 ≤ R) (hT : 1 ≤ T) (hTR : T ≤ R) (hK : 2 ≤ K)
    (hpre : ∀ p : ℕ, p.Prime → p ≤ K → p ∣ W) {L : ℝ} (hL : 0 < L)
    (hmean : (Fintype.card I : ℝ) * rationalMass W b R ≤
      (1 / 4) * (b * rationalSquareMass W b R * L))
    (hcollision : 4 * (Fintype.card I + 2) ^ 2 ≤ K - 1) :
    (1 / 2 : ℝ) ≤ (mixedDivisorLaw I W hb.le hR hT hTR).prob
      (fun a => mixedCoreLog I a ≤ L ∧ Pairwise (fun i j => (a i : ℕ).Coprime (a j : ℕ))) := by
  have hM := zero_lt_one.trans_le (one_le_rationalSquareMass W b hR)
  have hden : 0 < b * rationalSquareMass W b R * L := by positivity
  have hm : (Fintype.card I : ℝ) * rationalMass W b R /
      (b * rationalSquareMass W b R * L) ≤ 1 / 4 := (div_le_iff₀ hden).mpr hmean
  have hKpos : (0 : ℝ) < (K - 1 : ℕ) := by exact_mod_cast (by omega : 0 < K - 1)
  have hc : ((Fintype.card I : ℝ) + 2) ^ 2 / ((K - 1 : ℕ) : ℝ) ≤ 1 / 4 := by
    apply (div_le_iff₀ hKpos).mpr
    have hh : (4 : ℝ) * ((Fintype.card I : ℝ) + 2) ^ 2 ≤ (K - 1 : ℕ) := by exact_mod_cast hcollision
    linarith
  have hh := mixedDivisorLaw_good_probability I W hb hR hT hTR hK hpre hL
  linarith

end Erdos4.FGKMT
