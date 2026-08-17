/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos636.External.Erdos88.PermutationConcentration

open scoped BigOperators

namespace Erdos88
namespace FiniteSliceConcentration

open Classical Finset

/-- Uniform averaging preserves a pointwise absolute-difference bound. -/
lemma abs_uniformExpectation_sub_uniformExpectation_le
    {β : Type*} [Fintype β] [Nonempty β]
    (f g : β → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (h : ∀ x, |f x - g x| ≤ a) :
    |Concentration.uniformExpectation f -
        Concentration.uniformExpectation g| ≤ a := by
  have hc : (0 : ℝ) < Fintype.card β := by
    exact_mod_cast Fintype.card_pos
  rw [Concentration.uniformExpectation, Concentration.uniformExpectation,
    ← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hc]
  calc
    |∑ x : β, (f x - g x)| / Fintype.card β ≤
        (∑ x : β, |f x - g x|) / Fintype.card β := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (∑ _x : β, a) / Fintype.card β := by
      gcongr with x
      exact h x
    _ = a := by
      simp

/-- Separate the first coordinate of a dependent finite tuple when summing. -/
lemma sum_finTuple_cons {K : ℕ} {Ω : Fin (K + 1) → Type*}
    [∀ k, Fintype (Ω k)] (g : (∀ k, Ω k) → ℝ) :
    ∑ x, g x = ∑ x₀ : Ω 0, ∑ x : ∀ k : Fin K, Ω k.succ,
      g (Fin.cons x₀ x) := by
  rw [← (Fin.consEquiv Ω).sum_comp g]
  rw [Fintype.sum_prod_type]
  rfl

/-- Uniform expectation on a finite dependent tuple is iterated uniform
expectation after separating the first coordinate. -/
lemma uniformExpectation_finTuple_cons {K : ℕ}
    {Ω : Fin (K + 1) → Type*} [∀ k, Fintype (Ω k)]
    [∀ k, Nonempty (Ω k)] (g : (∀ k, Ω k) → ℝ) :
    Concentration.uniformExpectation g =
    Concentration.uniformExpectation (fun x : ∀ k : Fin K, Ω k.succ =>
        Concentration.uniformExpectation (fun x₀ : Ω 0 =>
          g (Fin.cons x₀ x))) := by
  simp only [Concentration.uniformExpectation]
  rw [sum_finTuple_cons, Finset.sum_comm]
  rw [Fintype.card_pi, Fintype.card_pi, Fin.prod_univ_succ]
  push_cast
  calc
    (∑ x : ∀ k : Fin K, Ω k.succ,
        ∑ x₀ : Ω 0, g (Fin.cons x₀ x)) /
          ((Fintype.card (Ω 0) : ℝ) *
            (∏ k : Fin K, (Fintype.card (Ω k.succ) : ℝ))) =
        ((∑ x : ∀ k : Fin K, Ω k.succ,
            ∑ x₀ : Ω 0, g (Fin.cons x₀ x)) /
              Fintype.card (Ω 0)) /
            (∏ k : Fin K, (Fintype.card (Ω k.succ) : ℝ)) := by
      rw [div_div]
    _ = (∑ x : ∀ k : Fin K, Ω k.succ,
          (∑ x₀ : Ω 0, g (Fin.cons x₀ x)) /
            Fintype.card (Ω 0)) /
        (∏ k : Fin K, (Fintype.card (Ω k.succ) : ℝ)) := by
      rw [Finset.sum_div]

/-- A tuple of independent permutations, one for each bucket. -/
abbrev PermutationProduct {K : ℕ} (N : Fin K → ℕ) :=
  ∀ k, Equiv.Perm (Fin (N k))

/-- A statistic on a product of permutations only uses the first `L k`
images in bucket `k`. -/
def PermutationProductPrefixDependent {K : ℕ}
    {N L : Fin K → ℕ} (hLN : ∀ k, L k ≤ N k)
    (F : PermutationProduct N → ℝ) : Prop :=
  ∀ σ τ, (∀ k (i : Fin (L k)),
    σ k (Fin.castLE (hLN k) i) = τ k (Fin.castLE (hLN k) i)) →
      F σ = F τ

/-- Changing one bucket permutation by a left transposition changes the
statistic by at most `a`.  The explicit second tuple avoids dependent
`Function.update` casts. -/
def PermutationProductSwitchLipschitz {K : ℕ} {N : Fin K → ℕ}
    (F : PermutationProduct N → ℝ) (a : ℝ) : Prop :=
  ∀ σ τ (k : Fin K) (p q : Fin (N k)),
    τ k = Equiv.swap p q * σ k →
    (∀ j, j ≠ k → τ j = σ j) →
    |F σ - F τ| ≤ a

/-- Exact exponential-moment tensorization for independent permutation
buckets.  Bucket `k` exposes its first `L k` images, so the total variance
proxy is `(∑ k, L k) * a²`. -/
theorem permutationProduct_exp_moment_bound :
    ∀ (K : ℕ) (N L : Fin K → ℕ) (hLN : ∀ k, L k ≤ N k)
      (F : PermutationProduct N → ℝ) (a lam : ℝ),
      0 ≤ a →
      PermutationProductPrefixDependent hLN F →
      PermutationProductSwitchLipschitz F a →
      ∑ σ, Real.exp (lam *
          (Concentration.uniformExpectation F - F σ)) ≤
        Fintype.card (PermutationProduct N) *
          Real.exp ((∑ k, (L k : ℝ)) * a ^ 2 * lam ^ 2 / 2) := by
  intro K
  induction K with
  | zero =>
      intro N L hLN F a lam ha hprefix hswitch
      let σ₀ : PermutationProduct N := fun k => Fin.elim0 k
      have hconst : ∀ σ, F σ = F σ₀ := by
        intro σ
        apply hprefix
        intro k
        exact Fin.elim0 k
      have hmean : Concentration.uniformExpectation F = F σ₀ := by
        rw [Concentration.uniformExpectation]
        simp_rw [hconst]
        simp
      simp [hmean, hconst]
  | succ K ih =>
      intro N L hLN F a lam ha hprefix hswitch
      let Ntail : Fin K → ℕ := fun k => N k.succ
      let Ltail : Fin K → ℕ := fun k => L k.succ
      let B : PermutationProduct Ntail → ℝ := fun τ =>
        Concentration.uniformExpectation (fun σ₀ : Equiv.Perm (Fin (N 0)) =>
          F (Fin.cons σ₀ τ))
      have hmean : Concentration.uniformExpectation F =
          Concentration.uniformExpectation B := by
        simpa only [B, Ntail] using uniformExpectation_finTuple_cons F
      have hBprefix : PermutationProductPrefixDependent
          (fun k => hLN k.succ) B := by
        intro σ τ hστ
        apply congrArg (fun f : Equiv.Perm (Fin (N 0)) → ℝ =>
          Concentration.uniformExpectation f)
        funext σ₀
        apply hprefix
        intro k
        refine Fin.cases ?_ (fun j => ?_) k
        · intro i
          rfl
        · intro i
          simpa [Ntail, Ltail] using hστ j i
      have hBswitch : PermutationProductSwitchLipschitz B a := by
        intro σ τ k p q hk hsame
        apply abs_uniformExpectation_sub_uniformExpectation_le _ _ a ha
        intro σ₀
        apply hswitch (Fin.cons σ₀ σ) (Fin.cons σ₀ τ) k.succ p q
        · simpa [Ntail] using hk
        · intro j hj
          cases j using Fin.cases with
          | zero => rfl
          | succ i =>
              simp only [Fin.cons_succ]
              exact hsame i (fun hik => hj (congrArg Fin.succ hik))
      have houter :
          ∑ τ, Real.exp (lam *
              (Concentration.uniformExpectation B - B τ)) ≤
            Fintype.card (PermutationProduct Ntail) *
              Real.exp ((∑ k, (Ltail k : ℝ)) * a ^ 2 * lam ^ 2 / 2) := by
        exact ih Ntail Ltail (fun k => hLN k.succ) B a lam ha
          hBprefix hBswitch
      have hinner (τ : PermutationProduct Ntail) :
          ∑ σ₀ : Equiv.Perm (Fin (N 0)),
              Real.exp (lam * (B τ - F (Fin.cons σ₀ τ))) ≤
            Fintype.card (Equiv.Perm (Fin (N 0))) *
              Real.exp ((L 0 : ℝ) * a ^ 2 * lam ^ 2 / 2) := by
        apply permReveal_exp_moment_bound (L 0) (N 0)
          (fun σ₀ => F (Fin.cons σ₀ τ)) a lam ha
        apply permRevealBounded_of_prefix_of_switch (hLN 0)
        · intro σ ρ hσρ
          apply hprefix
          intro k
          refine Fin.cases ?_ (fun j => ?_) k
          · intro i
            simpa using hσρ i
          · intro i
            rfl
        · intro σ p q
          apply hswitch (Fin.cons σ τ)
            (Fin.cons (Equiv.swap p q * σ) τ) 0 p q
          · rfl
          · intro j hj
            cases j using Fin.cases with
            | zero => exact (hj rfl).elim
            | succ i => rfl
      rw [sum_finTuple_cons, Finset.sum_comm, hmean]
      calc
        ∑ τ : PermutationProduct Ntail,
            ∑ σ₀ : Equiv.Perm (Fin (N 0)),
              Real.exp (lam *
                (Concentration.uniformExpectation B -
                  F (Fin.cons σ₀ τ))) =
            ∑ τ : PermutationProduct Ntail,
              (Real.exp (lam *
                  (Concentration.uniformExpectation B - B τ)) *
                ∑ σ₀ : Equiv.Perm (Fin (N 0)),
                  Real.exp (lam * (B τ - F (Fin.cons σ₀ τ)))) := by
          apply Finset.sum_congr rfl
          intro τ _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro σ₀ _
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ ∑ τ : PermutationProduct Ntail,
              (Real.exp (lam *
                  (Concentration.uniformExpectation B - B τ)) *
                (Fintype.card (Equiv.Perm (Fin (N 0))) *
                  Real.exp ((L 0 : ℝ) * a ^ 2 * lam ^ 2 / 2))) := by
          apply Finset.sum_le_sum
          intro τ _
          exact mul_le_mul_of_nonneg_left (hinner τ) (Real.exp_nonneg _)
        _ = (Fintype.card (Equiv.Perm (Fin (N 0))) *
                Real.exp ((L 0 : ℝ) * a ^ 2 * lam ^ 2 / 2)) *
              ∑ τ : PermutationProduct Ntail,
                Real.exp (lam *
                  (Concentration.uniformExpectation B - B τ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro τ _
          ring
        _ ≤ (Fintype.card (Equiv.Perm (Fin (N 0))) *
                Real.exp ((L 0 : ℝ) * a ^ 2 * lam ^ 2 / 2)) *
              (Fintype.card (PermutationProduct Ntail) *
                Real.exp ((∑ k, (Ltail k : ℝ)) * a ^ 2 * lam ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_left houter (by positivity)
        _ = Fintype.card (PermutationProduct N) *
              Real.exp ((∑ k, (L k : ℝ)) * a ^ 2 * lam ^ 2 / 2) := by
          simp only [PermutationProduct, Fintype.card_pi, Fin.prod_univ_succ,
            Fin.sum_univ_succ, Ntail, Ltail]
          push_cast
          calc
            ((Fintype.card (Equiv.Perm (Fin (N 0))) : ℝ) *
                Real.exp ((L 0 : ℝ) * a ^ 2 * lam ^ 2 / 2)) *
                ((∏ k : Fin K,
                    (Fintype.card (Equiv.Perm (Fin (N k.succ))) : ℝ)) *
                  Real.exp ((∑ k : Fin K, (L k.succ : ℝ)) *
                    a ^ 2 * lam ^ 2 / 2)) =
                ((Fintype.card (Equiv.Perm (Fin (N 0))) : ℝ) *
                  ∏ k : Fin K,
                    (Fintype.card (Equiv.Perm (Fin (N k.succ))) : ℝ)) *
                  (Real.exp ((L 0 : ℝ) * a ^ 2 * lam ^ 2 / 2) *
                    Real.exp ((∑ k : Fin K, (L k.succ : ℝ)) *
                      a ^ 2 * lam ^ 2 / 2)) := by ring
            _ = ((Fintype.card (Equiv.Perm (Fin (N 0))) : ℝ) *
                  ∏ k : Fin K,
                    (Fintype.card (Equiv.Perm (Fin (N k.succ))) : ℝ)) *
                Real.exp ((L 0 : ℝ) * a ^ 2 * lam ^ 2 / 2 +
                  (∑ k : Fin K, (L k.succ : ℝ)) *
                    a ^ 2 * lam ^ 2 / 2) := by
              rw [Real.exp_add]
            _ = ((Fintype.card (Equiv.Perm (Fin (N 0))) : ℝ) *
                  ∏ k : Fin K,
                    (Fintype.card (Equiv.Perm (Fin (N k.succ))) : ℝ)) *
                Real.exp (((L 0 : ℝ) +
                  ∑ k : Fin K, (L k.succ : ℝ)) *
                    a ^ 2 * lam ^ 2 / 2) := by
              congr 1
              ring

/-- One-sided lower-tail bound for a prefix statistic on a product of
independent permutation buckets. -/
theorem permutationProduct_lower_tail {K : ℕ} {N L : Fin K → ℕ}
    (hLN : ∀ k, L k ≤ N k) (F : PermutationProduct N → ℝ) (a t : ℝ)
    (hL : 0 < ∑ k, L k) (ha : 0 < a) (ht : 0 ≤ t)
    (hprefix : PermutationProductPrefixDependent hLN F)
    (hswitch : PermutationProductSwitchLipschitz F a) :
    ((Finset.univ.filter fun σ =>
        t ≤ Concentration.uniformExpectation F - F σ).card : ℝ) ≤
      Fintype.card (PermutationProduct N) *
        Real.exp (-t ^ 2 / (2 * (∑ k, L k) * a ^ 2)) := by
  classical
  let V : ℝ := (∑ k, L k : ℕ) * a ^ 2
  let lam : ℝ := t / V
  have hV : 0 < V := by
    dsimp [V]
    positivity
  have hlam : 0 ≤ lam := div_nonneg ht hV.le
  have hmom := permutationProduct_exp_moment_bound K N L hLN F a lam
    ha.le hprefix hswitch
  let A : Finset (PermutationProduct N) := Finset.univ.filter fun σ =>
    t ≤ Concentration.uniformExpectation F - F σ
  have hsub : A ⊆ Finset.univ.filter (fun σ =>
      Real.exp (lam * t) ≤ Real.exp (lam *
        (Concentration.uniformExpectation F - F σ))) := by
    intro σ hσ
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hσ hlam)
  have hcard : (A.card : ℝ) ≤
      ((Finset.univ.filter (fun σ =>
        Real.exp (lam * t) ≤ Real.exp (lam *
          (Concentration.uniformExpectation F - F σ)))).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hmarkov : (A.card : ℝ) * Real.exp (lam * t) ≤
      ∑ σ, Real.exp (lam *
        (Concentration.uniformExpectation F - F σ)) := by
    refine le_trans (mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)) ?_
    exact Concentration.counting_markov
      (Ω := PermutationProduct N)
      (fun σ => Real.exp (lam *
        (Concentration.uniformExpectation F - F σ)))
      (Real.exp (lam * t)) (Real.exp_pos _) (fun _ => Real.exp_nonneg _)
  have hcombined : (A.card : ℝ) * Real.exp (lam * t) ≤
      Fintype.card (PermutationProduct N) *
        Real.exp (V * lam ^ 2 / 2) := by
    exact hmarkov.trans (by simpa [V] using hmom)
  change (A.card : ℝ) ≤ _
  calc
    (A.card : ℝ) ≤
        (Fintype.card (PermutationProduct N) *
          Real.exp (V * lam ^ 2 / 2)) / Real.exp (lam * t) :=
      (le_div_iff₀ (Real.exp_pos (lam * t))).2 hcombined
    _ = Fintype.card (PermutationProduct N) *
        Real.exp (-t ^ 2 / (2 * (∑ k, L k) * a ^ 2)) := by
      rw [mul_div_assoc]
      rw [← Real.exp_sub]
      congr 1
      dsimp [lam, V]
      field_simp
      ring

/-- Two-sided Azuma--Hoeffding bound on a product of independent uniform
permutation buckets. -/
theorem permutationProduct_two_sided_tail {K : ℕ} {N L : Fin K → ℕ}
    (hLN : ∀ k, L k ≤ N k) (F : PermutationProduct N → ℝ) (a t : ℝ)
    (hL : 0 < ∑ k, L k) (ha : 0 < a) (ht : 0 ≤ t)
    (hprefix : PermutationProductPrefixDependent hLN F)
    (hswitch : PermutationProductSwitchLipschitz F a) :
    ((Finset.univ.filter fun σ =>
        t ≤ |F σ - Concentration.uniformExpectation F|).card : ℝ) ≤
      2 * Fintype.card (PermutationProduct N) *
        Real.exp (-t ^ 2 / (2 * (∑ k, L k) * a ^ 2)) := by
  classical
  let G : PermutationProduct N → ℝ := fun σ => -F σ
  have hGprefix : PermutationProductPrefixDependent hLN G := by
    intro σ τ h
    simp only [G]
    rw [hprefix σ τ h]
  have hGswitch : PermutationProductSwitchLipschitz G a := by
    intro σ τ k p q hk hsame
    calc
      |G σ - G τ| = |-(F σ - F τ)| := by
        congr 1
        simp only [G]
        ring
      _ = |F σ - F τ| := abs_neg _
      _ ≤ a := hswitch σ τ k p q hk hsame
  have hGmean : Concentration.uniformExpectation G =
      -Concentration.uniformExpectation F := by
    simp only [G, Concentration.uniformExpectation, Finset.sum_neg_distrib]
    ring
  let A : Finset (PermutationProduct N) := Finset.univ.filter fun σ =>
    t ≤ Concentration.uniformExpectation F - F σ
  let B : Finset (PermutationProduct N) := Finset.univ.filter fun σ =>
    t ≤ F σ - Concentration.uniformExpectation F
  have hA : (A.card : ℝ) ≤ Fintype.card (PermutationProduct N) *
      Real.exp (-t ^ 2 / (2 * (∑ k, L k) * a ^ 2)) := by
    simpa [A] using permutationProduct_lower_tail hLN F a t hL ha ht
      hprefix hswitch
  have hB : (B.card : ℝ) ≤ Fintype.card (PermutationProduct N) *
      Real.exp (-t ^ 2 / (2 * (∑ k, L k) * a ^ 2)) := by
    have h := permutationProduct_lower_tail hLN G a t hL ha ht
      hGprefix hGswitch
    have hset :
        Finset.univ.filter (fun σ =>
          t ≤ Concentration.uniformExpectation G - G σ) = B := by
      ext σ
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hGmean]
      simp only [G]
      constructor <;> intro hσ <;> linarith
    rw [← hset]
    exact h
  have hsubset :
      Finset.univ.filter (fun σ =>
        t ≤ |F σ - Concentration.uniformExpectation F|) ⊆ A ∪ B := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    rw [le_abs] at hσ
    rw [Finset.mem_union]
    rcases hσ with hσ | hσ
    · right
      simpa [B] using hσ
    · left
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      linarith
  calc
    ((Finset.univ.filter fun σ =>
        t ≤ |F σ - Concentration.uniformExpectation F|).card : ℝ) ≤
        ((A ∪ B).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ (A.card : ℝ) + B.card := by
      exact_mod_cast Finset.card_union_le A B
    _ ≤ 2 * Fintype.card (PermutationProduct N) *
        Real.exp (-t ^ 2 / (2 * (∑ k, L k) * a ^ 2)) := by
      linarith

/-- Probability-normalized form of the two-sided product-permutation tail. -/
theorem permutationProduct_two_sided_probability {K : ℕ}
    {N L : Fin K → ℕ} (hLN : ∀ k, L k ≤ N k)
    (F : PermutationProduct N → ℝ) (a t : ℝ)
    (hL : 0 < ∑ k, L k) (ha : 0 < a) (ht : 0 ≤ t)
    (hprefix : PermutationProductPrefixDependent hLN F)
    (hswitch : PermutationProductSwitchLipschitz F a) :
    Concentration.uniformProbability (fun σ =>
        t ≤ |F σ - Concentration.uniformExpectation F|) ≤
      2 * Real.exp (-t ^ 2 / (2 * (∑ k, L k) * a ^ 2)) := by
  have hcard : (0 : ℝ) < Fintype.card (PermutationProduct N) := by
    exact_mod_cast Fintype.card_pos
  rw [Concentration.uniformProbability]
  apply (div_le_iff₀ hcard).2
  calc
    ((Finset.univ.filter fun σ =>
        t ≤ |F σ - Concentration.uniformExpectation F|).card : ℝ) ≤
        2 * Fintype.card (PermutationProduct N) *
          Real.exp (-t ^ 2 / (2 * (∑ k, L k) * a ^ 2)) :=
      permutationProduct_two_sided_tail hLN F a t hL ha ht hprefix hswitch
    _ = (2 * Real.exp (-t ^ 2 / (2 * (∑ k, L k) * a ^ 2))) *
        Fintype.card (PermutationProduct N) := by
      ring

end FiniteSliceConcentration
end Erdos88
