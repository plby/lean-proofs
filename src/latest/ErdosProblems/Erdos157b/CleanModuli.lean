import ErdosProblems.Erdos157b.LevelComparisons

/-! Polynomial congruences from the clean single-summand tail. -/

namespace Erdos157.Binary

open Erdos157.Elementary

open Polynomial AuxiliaryModuli

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

noncomputable def segmentProduct (s n : ℕ) : K[X] := ∏ j ∈ Finset.range n, factor K (s + j)

theorem segmentProduct_natDegree (s n : ℕ) : (segmentProduct K s n).natDegree = n * (2 * s + n) := by
  have hsum : ∑ j ∈ Finset.range n, (2 * (s + j) + 1) = n * (2 * s + n) := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  unfold segmentProduct
  rw [Polynomial.natDegree_prod_of_monic]
  · simpa only [factor_natDegree] using hsum
  · intro j _; exact factor_monic K _

theorem segmentProduct_dvd (s n : ℕ) {f : K[X]}
    (hf : ∀ j < n, factor K (s + j) ∣ f) : segmentProduct K s n ∣ f := by
  apply Finset.prod_dvd_of_coprime
  · intro i _ j _ hij
    apply factor_coprime
    omega
  · intro j hj
    exact hf j (Finset.mem_range.mp hj)

theorem segmentProduct_interval_degree_add (s t : ℕ) (hst : s ≤ t) :
    (segmentProduct K s (t - s)).natDegree + s ^ 2 = t ^ 2 := by
  rw [segmentProduct_natDegree]
  have h := Nat.sub_add_cancel hst
  nlinarith

theorem clean_segment_dvd_of_encoded_pair_eq (τ : MaskChoice K) (ω : IntegerParameters K)
    (f₁ f₂ f₃ f₄ : Label K)
    (heq : encoded K τ ω f₁ + encoded K τ ω f₂ = encoded K τ ω f₃ + encoded K τ ω f₄) :
    segmentProduct K (max f₂.level f₄.level + 2)
      (min f₁.level f₃.level - (max f₂.level f₄.level + 2)) ∣ f₁.polynomial - f₃.polynomial := by
  apply segmentProduct_dvd
  intro j hj
  have hmin₁ := Nat.min_le_left f₁.level f₃.level
  have hmin₃ := Nat.min_le_right f₁.level f₃.level
  have hmax₂ := Nat.le_max_left f₂.level f₄.level
  have hmax₄ := Nat.le_max_right f₂.level f₄.level
  have hr := clean_residue_eq_of_encoded_pair_eq K τ ω f₁ f₂ f₃ f₄
    (max f₂.level f₄.level + 2 + j) (by omega) (by omega) (by omega) (by omega) heq
  have hv := congrArg Units.val hr
  simp only [labelResidue_val] at hv
  exact AdjoinRoot.mk_eq_mk.mp hv

theorem clean_segment_degree_le_of_distinct (τ : MaskChoice K) (ω : IntegerParameters K)
    (f₁ f₂ f₃ f₄ : Label K) (hne : f₁ ≠ f₃)
    (heq : encoded K τ ω f₁ + encoded K τ ω f₂ = encoded K τ ω f₃ + encoded K τ ω f₄) :
    (segmentProduct K (max f₂.level f₄.level + 2)
      (min f₁.level f₃.level - (max f₂.level f₄.level + 2))).natDegree ≤
      max (levelDegree f₁.level) (levelDegree f₃.level) := by
  have hpoly : f₁.polynomial - f₃.polynomial ≠ 0 := by
    intro h
    exact hne (Label.polynomial_injective (sub_eq_zero.mp h))
  have hd := Polynomial.natDegree_le_of_dvd (clean_segment_dvd_of_encoded_pair_eq K τ ω f₁ f₂ f₃ f₄ heq) hpoly
  have hs := Polynomial.natDegree_sub_le f₁.polynomial f₃.polynomial
  rw [Label.natDegree, Label.natDegree] at hs
  exact hd.trans hs

end Erdos157.Binary
