import ErdosProblems.Erdos888.UpperBound
import ErdosProblems.Erdos1102

/-!
# The four-element case of Erdős Problem 121

The existing formalization of Erdős Problem 888 bounds squarefree sets
satisfying a multiplicative four-point rigidity condition.  This file records
the elementary bridge from a square-product-free set to that condition.
-/

open Filter
open scoped BigOperators

namespace Erdos121

set_option autoImplicit false

lemma isSquare_of_mul_self_mul_isSquare {x y : ℕ} (hx : 0 < x)
    (h : IsSquare (x * x * y)) : IsSquare y := by
  obtain ⟨t, ht⟩ := h
  have hdiv : x ^ 2 ∣ t ^ 2 := by
    refine ⟨y, ?_⟩
    simpa [pow_two, mul_assoc] using ht.symm
  have hxt : x ∣ t :=
    (Nat.pow_dvd_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hdiv
  obtain ⟨u, rfl⟩ := hxt
  refine ⟨u, ?_⟩
  have hcancel : x ^ 2 * y = x ^ 2 * (u * u) := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using ht
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hx 2) hcancel

lemma eq_of_squarefree_mul_isSquare {a b : ℕ}
    (ha : Squarefree a) (hb : Squarefree b) (hab : IsSquare (a * b)) :
    a = b := by
  obtain ⟨t, ht⟩ := hab
  have htSq : t * t ∣ a * b := by rw [ht]
  have haT : a ∣ t := by
    rw [← ha.dvd_pow_iff_dvd (by norm_num : (2 : ℕ) ≠ 0)]
    rw [pow_two, ← ht]
    exact dvd_mul_right a b
  have htB : t ∣ b :=
    Squarefree.dvd_of_squarefree_of_mul_dvd_mul_right ha htSq
  have haB : a ∣ b := haT.trans htB
  have hbT : b ∣ t := by
    rw [← hb.dvd_pow_iff_dvd (by norm_num : (2 : ℕ) ≠ 0)]
    rw [pow_two, ← ht]
    exact dvd_mul_left b a
  have htA : t ∣ a :=
    Squarefree.dvd_of_squarefree_of_mul_dvd_mul_right hb (by simpa [Nat.mul_comm] using htSq)
  exact Nat.dvd_antisymm haB (hbT.trans htA)

/-- A squarefree set with no four distinct elements of square product
satisfies the four-point rigidity condition used in Erdős Problem 888. -/
theorem requiredCondition_of_squarefree_of_no_four {A : Finset ℕ} {N : ℕ}
    (hA : A ⊆ Finset.Ioc 0 N)
    (hsf : ∀ a ∈ A, Squarefree a)
    (hno : ∀ S : Finset ℕ, S ⊆ A → S.card = 4 →
      ¬ IsSquare (S.prod id)) :
    Erdos888.RequiredCondition A N := by
  refine ⟨hA, ?_⟩
  intro a ha b hb c hc d hd hab hbc hcd hsquare
  have haPos : 0 < a := (Finset.mem_Ioc.mp (hA ha)).1
  have hbPos : 0 < b := (Finset.mem_Ioc.mp (hA hb)).1
  have hcPos : 0 < c := (Finset.mem_Ioc.mp (hA hc)).1
  by_cases heqab : a = b
  · subst b
    have hcdSquare : IsSquare (c * d) := by
      apply isSquare_of_mul_self_mul_isSquare haPos
      simpa [mul_assoc] using hsquare
    have heqcd : c = d :=
      eq_of_squarefree_mul_isSquare (hsf c hc) (hsf d hd) hcdSquare
    subst d
    rfl
  by_cases heqbc : b = c
  · subst c
    have hadSquare : IsSquare (a * d) := by
      apply isSquare_of_mul_self_mul_isSquare hbPos
      simpa [mul_assoc, mul_left_comm, mul_comm] using hsquare
    have heqad : a = d :=
      eq_of_squarefree_mul_isSquare (hsf a ha) (hsf d hd) hadSquare
    have heqab' : a = b := Nat.le_antisymm hab (heqad ▸ hcd)
    exact (heqab heqab').elim
  by_cases heqcd : c = d
  · subst d
    have habSquare : IsSquare (a * b) := by
      apply isSquare_of_mul_self_mul_isSquare hcPos
      simpa [mul_assoc, mul_left_comm, mul_comm] using hsquare
    have heqab' : a = b :=
      eq_of_squarefree_mul_isSquare (hsf a ha) (hsf b hb) habSquare
    exact (heqab heqab').elim
  have hablt : a < b := lt_of_le_of_ne hab heqab
  have hbclt : b < c := lt_of_le_of_ne hbc heqbc
  have hcdlt : c < d := lt_of_le_of_ne hcd heqcd
  have hac : a ≠ c := ne_of_lt (hablt.trans hbclt)
  have had : a ≠ d := ne_of_lt (hablt.trans (hbclt.trans hcdlt))
  have hbd : b ≠ d := ne_of_lt (hbclt.trans hcdlt)
  let S : Finset ℕ := {a, b, c, d}
  have hSA : S ⊆ A := by
    simpa only [S, Finset.insert_subset_iff, Finset.singleton_subset_iff]
      using And.intro ha (And.intro hb (And.intro hc hd))
  have hScard : S.card = 4 := by
    simp [S, heqab, hac, had, heqbc, hbd, heqcd]
  apply False.elim
  apply hno S hSA hScard
  simpa [S, heqab, hac, had, heqbc, hbd, heqcd, mul_assoc] using hsquare

/-- A deliberately coarse positive-density consequence of the squarefree
counting theorem already formalized for Erdős Problem 1102. -/
theorem eventually_squarefree_count_ge :
    ∀ᶠ N : ℕ in atTop,
      (1 / 5 : ℝ) * N ≤ ((Finset.Icc 1 N).filter Squarefree).card := by
  classical
  obtain ⟨N₀, hN₀⟩ := Erdos1102b.SF_density_lower_bound (1 / 8 : ℝ) (by norm_num)
  have hpiSq : Real.pi ^ 2 < 16 := by
    nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hfrac : (3 / 8 : ℝ) < 6 / Real.pi ^ 2 := by
    rw [lt_div_iff₀ (sq_pos_of_pos Real.pi_pos)]
    nlinarith
  filter_upwards [eventually_ge_atTop N₀, eventually_gt_atTop 0] with N hN hNpos
  have hdensity :
      6 / Real.pi ^ 2 - 1 / 8 ≤
        (((Finset.Icc 1 N).filter Squarefree).card : ℝ) / N := by
    have heq :
        (Finset.Icc 1 N).filter Squarefree =
          (Finset.Icc 1 N).filter (fun x => x ∈ Erdos1102b.SF) := by
      ext x
      rw [Finset.mem_filter, Finset.mem_filter]
      rfl
    rw [heq]
    exact hN₀ N hN
  have hdensity' :
      (1 / 5 : ℝ) ≤
        (((Finset.Icc 1 N).filter Squarefree).card : ℝ) / N := by
    exact le_trans (by nlinarith [hfrac]) hdensity
  rwa [le_div_iff₀ (by positivity)] at hdensity'

/-- The comparison scale from Erdős Problem 888 is sublinear. -/
theorem erdos888_scale_isLittleO_natCast :
    Erdos888.scale =o[atTop] (fun N : ℕ => (N : ℝ)) := by
  have hratioReal :
      Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x)
        atTop (nhds 0) :=
    (Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).tendsto_div_nhds_zero
  have hratio :
      Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
        atTop (nhds 0) :=
    hratioReal.comp tendsto_natCast_atTop_atTop
  refine (Asymptotics.isLittleO_iff_tendsto' ?_).2 ?_
  · filter_upwards [eventually_gt_atTop 0] with N hN
    intro hzero
    exact False.elim ((by positivity : (0 : ℝ) < N).ne' hzero)
  · apply hratio.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    simp only [Erdos888.scale]
    field_simp

/-- The squarefree extremal function occurring in the Erdős 888
formalization is eventually at most one tenth of the ambient interval. -/
theorem eventually_squarefreeExtremalSize_le_tenth :
    ∀ᶠ N : ℕ in atTop,
      (Erdos888.squarefreeExtremalSize N : ℝ) ≤ (1 / 10 : ℝ) * N := by
  have hsmall :
      (fun N : ℕ => (Erdos888.squarefreeExtremalSize N : ℝ))
        =o[atTop] (fun N : ℕ => (N : ℝ)) :=
    Erdos888.squarefreeExtremalSize_isBigO_scale.trans_isLittleO
      erdos888_scale_isLittleO_natCast
  have hbound := hsmall.bound (by norm_num : (0 : ℝ) < 1 / 10)
  filter_upwards [hbound] with N hN
  rw [Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (Erdos888.squarefreeExtremalSize N : ℝ)),
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (N : ℝ))] at hN
  exact hN

end Erdos121
