import ErdosProblems.Erdos4.FGKMTLawOperations

/-! Elementary moment and Markov estimates for finite product laws. -/

open scoped BigOperators

namespace Erdos4.FGKMT.FiniteLaw

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

theorem independent_mean_coordinate (μ : I → FiniteLaw Ω) (i : I) (f : Ω → ℝ) :
    (independent μ).mean (fun a => f (a i)) = (μ i).mean f := by
  classical
  have hh := independent_mean_prod μ (fun j o => if j = i then f o else 1)
  have hmean (j : I) : (μ j).mean (fun o => if j = i then f o else 1) =
      if j = i then (μ j).mean f else 1 := by
    by_cases hji : j = i
    · simp only [if_pos hji]
    · simp only [if_neg hji, mean_const]
  simp_rw [hmean] at hh
  simpa only [Finset.prod_ite_eq', Finset.mem_univ, if_true, mean_const, Finset.prod_ite_eq,
    dite_true] using hh

theorem independent_mean_sum (μ : I → FiniteLaw Ω) (f : I → Ω → ℝ) :
    (independent μ).mean (fun a => ∑ i, f i (a i)) = ∑ i, (μ i).mean (f i) := by
  rw [mean_finset_sum]
  exact Finset.sum_congr rfl (fun i _ => independent_mean_coordinate μ i (f i))

theorem independent_mean_pair (μ : I → FiniteLaw Ω) {i j : I} (hij : i ≠ j)
    (f g : Ω → ℝ) :
    (independent μ).mean (fun a => f (a i) * g (a j)) = (μ i).mean f * (μ j).mean g := by
  classical
  have hh := independent_mean_prod μ
    (fun k o => (if k = i then f o else 1) * (if k = j then g o else 1))
  have hmean (k : I) : (μ k).mean (fun o =>
      (if k = i then f o else 1) * (if k = j then g o else 1)) =
      (if k = i then (μ i).mean f else 1) * (if k = j then (μ j).mean g else 1) := by
    by_cases hki : k = i
    · subst k
      simp [hij]
    · by_cases hkj : k = j
      · subst k
        simp [hij.symm]
      · simp only [if_neg hki, if_neg hkj, mul_one, mean_const]
  simp_rw [hmean] at hh
  simpa only [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq,
    Finset.mem_univ, if_true] using hh

theorem independent_prob_pair (μ : I → FiniteLaw Ω) {i j : I} (hij : i ≠ j)
    (E F : Ω → Prop) :
    (independent μ).prob (fun a => E (a i) ∧ F (a j)) = (μ i).prob E * (μ j).prob F := by
  classical
  rw [prob_eq_mean]
  calc
    _ = (independent μ).mean (fun a => (if E (a i) then 1 else 0) * (if F (a j) then 1 else 0)) := by
      apply mean_congr
      intro a
      by_cases hE : E (a i) <;> by_cases hF : F (a j) <;> simp [hE, hF]
    _ = (μ i).mean (fun o => if E o then 1 else 0) * (μ j).mean (fun o => if F o then 1 else 0) :=
      independent_mean_pair μ hij (fun o : Ω => if E o then 1 else 0)
        (fun o : Ω => if F o then 1 else 0)
    _ = _ := by rw [← prob_eq_mean, ← prob_eq_mean]

theorem independent_sum_tail (μ : I → FiniteLaw Ω) (f : I → Ω → ℝ)
    (hf : ∀ i o, 0 ≤ f i o) {L : ℝ} (hL : 0 < L) :
    (independent μ).prob (fun a => L < ∑ i, f i (a i)) ≤
      (∑ i, (μ i).mean (f i)) / L := by
  have hh := (independent μ).prob_le_of_lower (fun a => L < ∑ i, f i (a i))
    (fun a => ∑ i, f i (a i)) hL
    (fun a => Finset.sum_nonneg (fun i _ => hf i (a i))) (fun a ha => ha.le)
  rw [independent_mean_sum] at hh
  exact hh

theorem independent_sum_good (μ : I → FiniteLaw Ω) (f : I → Ω → ℝ)
    (hf : ∀ i o, 0 ≤ f i o) {L : ℝ} (hL : 0 < L) :
    1 - (∑ i, (μ i).mean (f i)) / L ≤
      (independent μ).prob (fun a => ∑ i, f i (a i) ≤ L) := by
  have hh := independent_sum_tail μ f hf hL
  have hcompl := (independent μ).prob_compl (fun a => L < ∑ i, f i (a i))
  simp only [not_lt] at hcompl
  linarith

end Erdos4.FGKMT.FiniteLaw
