import ErdosProblems.Erdos4.FGKMTMixedDivisorLaw
import Mathlib.Data.Fin.SuccPred

/-! Unnormalizing the mixed law gives an actual positive divisor sum. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical

theorem FiniteLaw.map_weight_apply {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (μ : FiniteLaw Ω) (f : Ω → Λ) (hf : Function.Injective f) (o : Ω) :
    (μ.map f).weight (f o) = μ.weight o := by
  classical
  change (∑ a, μ.weight a * (if f o = f a then 1 else 0)) = μ.weight o
  simp [hf.eq_iff]

theorem rationalFaceLaw_weight (W : ℕ) {b : ℝ} (hb : 0 ≤ b)
    {T R : ℕ} (hT : 1 ≤ T) (hTR : T ≤ R) (n : Fin (R + 1)) :
    (rationalFaceLaw W hb hT hTR).weight n =
      (if (n : ℕ) ≤ T then logarithmicReciprocal b n * squarefreeHarmonicWeight W n else 0) /
        rationalMass W b T := by
  classical
  by_cases hn : (n : ℕ) ≤ T
  · rw [if_pos hn]
    let m : Fin (T + 1) := ⟨n, Nat.lt_succ_of_le hn⟩
    have heq : Fin.castLE (Nat.succ_le_succ hTR) m = n := Fin.ext rfl
    have hh := FiniteLaw.map_weight_apply (rationalLinearLaw W hb T hT)
      (Fin.castLE (Nat.succ_le_succ hTR)) (Fin.castLE_injective _) m
    simpa only [rationalFaceLaw, heq, rationalLinearLaw, m] using hh
  · rw [if_neg hn, zero_div]
    apply le_antisymm _ ((rationalFaceLaw W hb hT hTR).nonneg n)
    by_contra hpos
    exact hn (rationalFaceLaw_support W hb hT hTR n (lt_of_not_ge hpos)).2.2

variable (I : Type*) [Fintype I] [DecidableEq I]

noncomputable def mixedDivisorNumerator (W : ℕ) (b : ℝ) (T : ℕ) {R : ℕ}
    (a : (I ⊕ Fin 2) → Fin (R + 1)) : ℝ :=
  (∏ i : I, logarithmicReciprocal b (a (Sum.inl i)) ^ 2 * squarefreeHarmonicWeight W (a (Sum.inl i))) *
    ∏ j : Fin 2, if (a (Sum.inr j) : ℕ) ≤ T then
      logarithmicReciprocal b (a (Sum.inr j)) * squarefreeHarmonicWeight W (a (Sum.inr j)) else 0

noncomputable def mixedDivisorMass (W : ℕ) (b : ℝ) (R T : ℕ) : ℝ :=
  rationalSquareMass W b R ^ Fintype.card I * rationalMass W b T ^ 2

omit [DecidableEq I] in
theorem mixedDivisorMass_pos (W : ℕ) {b : ℝ} (hb : 0 ≤ b)
    {R T : ℕ} (hR : 1 ≤ R) (hT : 1 ≤ T) : 0 < mixedDivisorMass I W b R T := by
  have hM := zero_lt_one.trans_le (one_le_rationalSquareMass W b hR)
  have hA := zero_lt_one.trans_le (one_le_rationalMass hb W hT)
  unfold mixedDivisorMass
  positivity

theorem mixedDivisorLaw_weight (W : ℕ) {b : ℝ} (hb : 0 ≤ b)
    {R T : ℕ} (hR : 1 ≤ R) (hT : 1 ≤ T) (hTR : T ≤ R)
    (a : (I ⊕ Fin 2) → Fin (R + 1)) :
    (mixedDivisorLaw I W hb hR hT hTR).weight a =
      mixedDivisorNumerator I W b T a / mixedDivisorMass I W b R T := by
  classical
  change (∏ i, (mixedDivisorMarginal I W hb hR hT hTR i).weight (a i)) = _
  rw [Fintype.prod_sum_type]
  simp only [mixedDivisorMarginal, rationalSquareLaw, rationalFaceLaw_weight,
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact div_mul_div_comm _ _ _ _

theorem mixedDivisorLaw_prob_eq (W : ℕ) {b : ℝ} (hb : 0 ≤ b)
    {R T : ℕ} (hR : 1 ≤ R) (hT : 1 ≤ T) (hTR : T ≤ R)
    (E : ((I ⊕ Fin 2) → Fin (R + 1)) → Prop) :
    (mixedDivisorLaw I W hb hR hT hTR).prob E =
      (∑ a ∈ Finset.univ.filter E, mixedDivisorNumerator I W b T a) /
        mixedDivisorMass I W b R T := by
  classical
  unfold FiniteLaw.prob
  simp_rw [mixedDivisorLaw_weight]
  have hpoint (a : (I ⊕ Fin 2) → Fin (R + 1)) :
      (if E a then mixedDivisorNumerator I W b T a / mixedDivisorMass I W b R T else 0) =
        (if E a then mixedDivisorNumerator I W b T a else 0) / mixedDivisorMass I W b R T := by
    split_ifs <;> simp
  simp_rw [hpoint]
  rw [← Finset.sum_div, ← Finset.sum_filter]

def MixedDivisorGood (W T : ℕ) (L : ℝ) {R : ℕ}
    (a : (I ⊕ Fin 2) → Fin (R + 1)) : Prop :=
  (∀ i, Squarefree (a i : ℕ) ∧ (a i : ℕ).Coprime W) ∧
    (∀ j : Fin 2, (a (Sum.inr j) : ℕ) ≤ T) ∧ mixedCoreLog I a ≤ L ∧
      Pairwise (fun i j => (a i : ℕ).Coprime (a j : ℕ))

theorem mixedDivisorLaw_good_support (W : ℕ) {b : ℝ} (hb : 0 ≤ b)
    {R T : ℕ} (hR : 1 ≤ R) (hT : 1 ≤ T) (hTR : T ≤ R) (L : ℝ)
    (a : (I ⊕ Fin 2) → Fin (R + 1))
    (ha : 0 < (mixedDivisorLaw I W hb hR hT hTR).weight a)
    (hgood : mixedCoreLog I a ≤ L ∧ Pairwise (fun i j => (a i : ℕ).Coprime (a j : ℕ))) :
    MixedDivisorGood I W T L a := by
  have hs := FiniteLaw.independent_support (mixedDivisorMarginal I W hb hR hT hTR) a ha
  refine ⟨fun i => mixedDivisorMarginal_support I W hb hR hT hTR i (a i) (hs i), ?_, hgood⟩
  intro j
  exact (rationalFaceLaw_support W hb hT hTR (a (Sum.inr j)) (hs (Sum.inr j))).2.2

/-- At least half the full independent mass remains in the genuine
squarefree, coprime core-and-two-faces sum. -/
theorem mixedDivisor_good_mass_half (W : ℕ) {b : ℝ} (hb : 0 < b)
    {R T K : ℕ} (hR : 1 ≤ R) (hT : 1 ≤ T) (hTR : T ≤ R) (hK : 2 ≤ K)
    (hpre : ∀ p : ℕ, p.Prime → p ≤ K → p ∣ W) {L : ℝ} (hL : 0 < L)
    (hmean : (Fintype.card I : ℝ) * rationalMass W b R ≤
      (1 / 4) * (b * rationalSquareMass W b R * L))
    (hcollision : 4 * (Fintype.card I + 2) ^ 2 ≤ K - 1) :
    mixedDivisorMass I W b R T / 2 ≤
      ∑ a ∈ Finset.univ.filter (MixedDivisorGood I W T L (R := R)), mixedDivisorNumerator I W b T a := by
  classical
  have hprob := mixedDivisorLaw_good_probability_half I W hb hR hT hTR hK hpre hL hmean hcollision
  have hmono := (mixedDivisorLaw I W hb.le hR hT hTR).prob_mono_support
    (fun a ha hgood => mixedDivisorLaw_good_support I W hb.le hR hT hTR L a ha hgood)
  have hh := hprob.trans hmono
  rw [mixedDivisorLaw_prob_eq] at hh
  have hmul := (le_div_iff₀ (mixedDivisorMass_pos I W hb.le hR hT)).mp hh
  linarith

end Erdos4.FGKMT
