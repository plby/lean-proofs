import ErdosProblems.Erdos4.FGKMTProductMoments

/-! An elementary exponential lower-tail bound for weighted independent source assignments. -/

open scoped BigOperators

namespace Erdos4.FGKMT

theorem exp_neg_le_one_sub_two_thirds {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    Real.exp (-s) ≤ 1 - (2 / 3) * s := by
  have hden : 0 < 1 + s := by linarith
  calc
    _ = 1 / Real.exp s := by rw [Real.exp_neg, one_div]
    _ ≤ 1 / (1 + s) := one_div_le_one_div_of_le hden
      (by simpa only [add_comm] using Real.add_one_le_exp s)
    _ ≤ _ := by
      apply (div_le_iff₀ hden).mpr
      have hh := mul_nonneg hs0 (by linarith : 0 ≤ 1 - 2 * s)
      nlinarith

namespace FiniteLaw

open Classical

theorem mean_exp_ite {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (E : Ω → Prop)
    [DecidablePred E] (t : ℝ) :
    μ.mean (fun o => Real.exp (if E o then t else 0)) =
      1 + μ.prob E * (Real.exp t - 1) := by
  have hpoint : ∀ o, Real.exp (if E o then t else 0) =
      1 + (Real.exp t - 1) * (if E o then (1 : ℝ) else 0) := by
    intro o
    by_cases he : E o <;> simp [he]
  rw [μ.mean_congr hpoint, mean_add, mean_const, mean_const_mul, ← prob_eq_mean]
  ring

theorem independent_weighted_lower_tail {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]
    (μ : I → FiniteLaw Ω) (E : I → Ω → Prop) [∀ i, DecidablePred (E i)]
    (b : I → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hb0 : ∀ i, 0 ≤ b i) (hb : ∀ i, b i ≤ δ) :
    let M := ∑ i, (μ i).prob (E i) * b i
    (independent μ).prob (fun a => (∑ i, if E i (a i) then b i else 0) < M / 2) ≤
      Real.exp (-M / (12 * δ)) := by
  let M := ∑ i, (μ i).prob (E i) * b i
  let t := 1 / (2 * δ)
  let S := fun (a : I → Ω) => ∑ i, if E i (a i) then b i else 0
  have ht : 0 < t := by dsimp only [t]; positivity
  have hlocal : ∀ i, (μ i).mean (fun o => Real.exp (-t * (if E i o then b i else 0))) ≤
      Real.exp (-(2 / 3) * t * ((μ i).prob (E i) * b i)) := by
    intro i
    have hs0 : 0 ≤ t * b i := mul_nonneg ht.le (hb0 i)
    have hs1 : t * b i ≤ 1 / 2 := by
      have hh := mul_le_mul_of_nonneg_left (hb i) ht.le
      have heq : t * δ = 1 / 2 := by dsimp only [t]; field_simp
      exact hh.trans_eq heq
    have hexp := exp_neg_le_one_sub_two_thirds hs0 hs1
    have hmean : (μ i).mean (fun o => Real.exp (-t * (if E i o then b i else 0))) =
        1 + (μ i).prob (E i) * (Real.exp (-(t * b i)) - 1) := by
      have heq : (fun o => Real.exp (-t * (if E i o then b i else 0))) =
          (fun o => Real.exp (if E i o then -(t * b i) else 0)) := by
        funext o
        by_cases he : E i o <;> simp [he]
      rw [heq, mean_exp_ite]
    rw [hmean]
    have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right hexp 1) ((μ i).prob_nonneg (E i))
    calc
      _ ≤ 1 + (-(2 / 3) * t * ((μ i).prob (E i) * b i)) := by nlinarith
      _ ≤ _ := by simpa only [add_comm] using
        Real.add_one_le_exp (-(2 / 3) * t * ((μ i).prob (E i) * b i))
  have hmean : (independent μ).mean (fun a => Real.exp (-t * S a)) ≤
      Real.exp (-(2 / 3) * t * M) := by
    have hpoint : ∀ a, Real.exp (-t * S a) =
        ∏ i, Real.exp (-t * (if E i (a i) then b i else 0)) := by
      intro a
      dsimp only [S]
      rw [Finset.mul_sum, Real.exp_sum]
    rw [(independent μ).mean_congr hpoint,
      independent_mean_prod μ (fun i o => Real.exp (-t * (if E i o then b i else 0)))]
    calc
      _ ≤ ∏ i, Real.exp (-(2 / 3) * t * ((μ i).prob (E i) * b i)) :=
        Finset.prod_le_prod (fun i _ => (μ i).mean_nonneg (fun o => (Real.exp_pos _).le))
          (fun i _ => hlocal i)
      _ = _ := by rw [← Real.exp_sum, ← Finset.mul_sum]
  have htail := (independent μ).prob_le_of_lower (fun a => S a < M / 2)
    (fun a => Real.exp (-t * S a)) (Real.exp_pos (-t * (M / 2)))
    (fun a => (Real.exp_pos _).le) (fun a ha => Real.exp_le_exp.mpr (by
      have hh := mul_le_mul_of_nonpos_left ha.le (neg_nonpos.mpr ht.le)
      exact hh))
  change (independent μ).prob (fun a => S a < M / 2) ≤ _
  calc
    _ ≤ (independent μ).mean (fun a => Real.exp (-t * S a)) / Real.exp (-t * (M / 2)) := htail
    _ ≤ Real.exp (-(2 / 3) * t * M) / Real.exp (-t * (M / 2)) :=
      div_le_div_of_nonneg_right hmean (Real.exp_pos _).le
    _ = Real.exp (-M / (12 * δ)) := by
      rw [← Real.exp_sub]
      congr 1
      dsimp only [t]
      ring

end FiniteLaw

end Erdos4.FGKMT
