/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos284.Assembly
import ErdosProblems.Erdos284.EfficientWitness

/-!
# Exact cardinalities from the efficient construction

Choose `N = floor (c(k+1))`, construct a representation above `N`, and pad
its cardinality to exactly `k+1`.  The construction-size limit `e-1` gives
the sharp condition `c < 1/(e-1)`.
-/

open Filter Finset
open scoped Topology Real

namespace Erdos284

noncomputable section

attribute [local instance] Classical.propDecidable

private theorem representation_nonempty {A : Finset ℕ}
    (hsum : UnitFractions.rec_sum A = 1) : A.Nonempty := by
  by_contra hA
  rw [Finset.not_nonempty_iff_eq_empty] at hA
  simp [hA, UnitFractions.rec_sum] at hsum

/-- Pad any representation above `N` to `K` terms, provided `K < 2(N+1)`. -/
theorem padRepresentationToCard_of_lt_two_mul
    {N K : ℕ} {A : Finset ℕ}
    (hzero : 0 ∉ A) (hsum : UnitFractions.rec_sum A = 1)
    (hbelow : ∀ a ∈ A, N < a)
    (hcard : A.card ≤ K) (hK : K < 2 * (N + 1)) :
    ∃ E : Finset ℕ,
      FinsetRepresentation K E ∧ ∀ a ∈ E, N < a := by
  let hAne : A.Nonempty := representation_nonempty hsum
  let n : ℕ := A.max' hAne
  let m : ℕ := K - A.card
  have hnA : n ∈ A := Finset.max'_mem A hAne
  have hnmax : ∀ a ∈ A, a ≤ n := fun a ha ↦ Finset.le_max' A a ha
  have hnpos : 0 < n := by
    have := hbelow n hnA
    omega
  have hAlower : N + 1 ≤ A.card := by
    have hden : (0 : ℝ) < (N + 1 : ℕ) := by positivity
    have hbound := UnitFractions.rec_sum_le_card_div (A := A)
      (M := ((N + 1 : ℕ) : ℝ)) hden (fun d hd ↦ by
        exact_mod_cast (Nat.succ_le_iff.mpr (hbelow d hd)))
    have hsumR : (UnitFractions.rec_sum A : ℝ) = 1 := by
      rw [hsum]
      norm_num
    rw [hsumR, le_div_iff₀ hden] at hbound
    norm_num at hbound
    exact_mod_cast hbound
  have hdeficit : m < n := by
    have hnlarge : N + 1 ≤ n := Nat.succ_le_iff.mpr (hbelow n hnA)
    dsimp [m]
    omega
  have hspec := Erdos285.Proposition7.padAt_spec
    hnA hnmax hzero hdeficit
  refine ⟨Erdos285.Proposition7.padAt A n m, ?_, ?_⟩
  · refine ⟨?_, hspec.2.2.1, ?_⟩
    · rw [hspec.1]
      dsimp [m]
      omega
    · simpa [m] using hspec.2.1.trans hsum
  · intro a ha
    rw [Erdos285.Proposition7.padAt, Finset.mem_union] at ha
    rcases ha with ha | ha
    · exact hbelow a (Finset.mem_of_mem_erase ha)
    · have hat : n ≤ a := by
        by_cases hm : m = 0
        · rw [hm] at ha
          simp [Erdos285.Proposition7.paddingTerms] at ha
          omega
        · exact (Erdos285.Proposition7.paddingTerms_above hnpos
            (Nat.pos_of_ne_zero hm) ha).le
      exact (hbelow n hnA).trans_le hat

/-- For every constant below the predicted extremal ratio, all sufficiently
large cardinalities have a representation whose first denominator is at
least that constant times the cardinality. -/
theorem eventually_exact_card_above
    {c : ℝ} (hcpos : 0 < c) (hchalf : (1 : ℝ) / 2 < c)
    (hctarget : c < 1 / (Real.exp 1 - 1)) :
    ∀ᶠ k : ℕ in atTop, ∃ E : Finset ℕ,
      FinsetRepresentation (k + 1) E ∧
        ∀ a ∈ E, lowerCutoff c k < a := by
  let N : ℕ → ℕ := lowerCutoff c
  have hNtop : Tendsto N atTop atTop := lowerCutoff_tendsto_atTop hcpos
  have hNratio : Tendsto (fun k : ℕ ↦ (N k : ℝ) / (k + 1 : ℕ))
      atTop (nhds c) := lowerCutoff_ratio_tendsto hcpos.le
  have hboundN := constructionBound_ratio_tendsto.comp hNtop
  have hboundK : Tendsto
      (fun k : ℕ ↦ (constructionBound (N k) : ℝ) / (k + 1 : ℕ))
      atTop (nhds ((Real.exp 1 - 1) * c)) := by
    have hprod := hboundN.mul hNratio
    have heq :
        (fun k : ℕ ↦
          (((fun n : ℕ ↦ (constructionBound n : ℝ) / (n : ℝ)) ∘ N) k) *
            ((N k : ℝ) / (k + 1 : ℕ))) =ᶠ[atTop]
          (fun k : ℕ ↦ (constructionBound (N k) : ℝ) / (k + 1 : ℕ)) := by
      filter_upwards [hNtop.eventually (eventually_gt_atTop 0)] with k hNk
      have hN0 : (N k : ℝ) ≠ 0 := by exact_mod_cast hNk.ne'
      have hk0 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      simp only [Function.comp_apply]
      field_simp
    simpa using hprod.congr' heq
  have hexpm1 : 0 < Real.exp 1 - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr zero_lt_one)
  have hlimit : (Real.exp 1 - 1) * c < 1 := by
    simpa [mul_comm] using (lt_div_iff₀ hexpm1).mp hctarget
  have hboundlt : ∀ᶠ k : ℕ in atTop,
      (constructionBound (N k) : ℝ) / (k + 1 : ℕ) < 1 :=
    (tendsto_order.1 hboundK).2 1 hlimit
  have hwitness : ∀ᶠ k : ℕ in atTop, ∃ A : Finset ℕ,
      0 ∉ A ∧ UnitFractions.rec_sum A = 1 ∧
      (∀ d ∈ A, N k < d) ∧ A.card ≤ constructionBound (N k) :=
    hNtop.eventually eventually_exists_efficient_representation
  have hhalf : ∀ᶠ k : ℕ in atTop,
      (1 : ℝ) / 2 < (N k : ℝ) / (k + 1 : ℕ) :=
    (tendsto_order.1 hNratio).1 ((1 : ℝ) / 2) hchalf
  filter_upwards [hwitness, hboundlt, hhalf] with k hw hbound hhalfk
  rcases hw with ⟨A, hzero, hsum, hbelow, hAcard⟩
  have hconstruct : constructionBound (N k) < k + 1 := by
    have hkpos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
    have := (div_lt_one hkpos).mp hbound
    exact_mod_cast this
  have hcard : A.card ≤ k + 1 := hAcard.trans hconstruct.le
  have htwice : k + 1 < 2 * (N k + 1) := by
    have hkpos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
    have hh := (lt_div_iff₀ hkpos).mp hhalfk
    have hreal : ((k + 1 : ℕ) : ℝ) < 2 * (N k : ℝ) := by nlinarith
    have hnat : k + 1 < 2 * N k := by exact_mod_cast hreal
    omega
  exact padRepresentationToCard_of_lt_two_mul
    hzero hsum hbelow hcard htwice

end

end Erdos284

#print axioms Erdos284.padRepresentationToCard_of_lt_two_mul
#print axioms Erdos284.eventually_exact_card_above
