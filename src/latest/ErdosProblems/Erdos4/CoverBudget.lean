import ErdosProblems.Erdos4.SelectedResidueCover

/-!
# Exceptional targets and the finite fresh-prime budget

Bad targets are charged their full preliminary survival probability.
Every other target is charged its conditional noncoverage bound. The
resulting numerical budget is sufficient for an actual residue cover.
-/

open scoped BigOperators

namespace Erdos4.CoverBudget

open AffineTuples ConditionalTupleMoments ConditionalCovering

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

theorem hitting_ratio_le_one (h : Fin k → ℕ) (p Y : ℕ) (μ : ℕ → ℝ) (q : ℕ)
    (hμ : ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ n) (a : ∀ l, ZMod (ell l)) :
    hittingMass ell h p Y μ q a / tupleMass ell h p Y μ a ≤ 1 := by
  by_cases hX : tupleMass ell h p Y μ a = 0
  · rw [hX, div_zero]
    exact zero_le_one
  · apply (div_le_one (lt_of_le_of_ne (tupleMass_nonneg ell h p Y μ hμ a) (Ne.symm hX))).mpr
    exact hittingMass_le_tupleMass ell h p Y μ q hμ a

theorem miss_le_one (h : Fin k → ℕ) (sources : Finset ℕ) (Y : ℕ)
    (μ : ℕ → ℕ → ℝ) (q : ℕ)
    (hμ : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ p n) (a : ∀ l, ZMod (ell l)) :
    miss ell h sources Y μ q a ≤ 1 := by
  apply Finset.prod_le_one
  · intro p _hp
    exact sub_nonneg.mpr (hitting_ratio_le_one ell h p Y (μ p) q (hμ p p.property) a)
  · intro p _hp
    have hr : 0 ≤ hittingMass ell h p Y (μ p) q a / tupleMass ell h p Y (μ p) a :=
      div_nonneg (hittingMass_nonneg ell h p Y (μ p) q (hμ p p.property) a)
        (tupleMass_nonneg ell h p Y (μ p) (hμ p p.property) a)
    linarith

theorem mean_miss_le_one (h : Fin k → ℕ) (sources : Finset ℕ) (Y : ℕ)
    (μ : ℕ → ℕ → ℝ) (q : ℕ)
    (hμ : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ p n) :
    mean ell q (miss ell h sources Y μ q) ≤ 1 :=
  (mean_mono ell q _ (fun _ => 1) (miss_le_one ell h sources Y μ q hμ)).trans_eq
    (mean_const ell q 1)

theorem target_sum_le (h : Fin k → ℕ) (sources targets bad : Finset ℕ) (Y : ℕ)
    (μ : ℕ → ℕ → ℝ) (hμ : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ p n)
    {β : ℝ} (hβ : 0 ≤ β)
    (hgood : ∀ q ∈ targets, q ∉ bad → mean ell q (miss ell h sources Y μ q) ≤ β) :
    (∑ q ∈ targets, mean ell q (miss ell h sources Y μ q)) ≤ bad.card + β * targets.card := by
  classical
  have hpoint : ∀ q ∈ targets, mean ell q (miss ell h sources Y μ q) ≤
      (if q ∈ bad then 1 else 0) + β := by
    intro q hq
    by_cases hbad : q ∈ bad
    · rw [if_pos hbad]
      exact (mean_miss_le_one ell h sources Y μ q hμ).trans (by linarith)
    · rw [if_neg hbad, zero_add]
      exact hgood q hq hbad
  have hb : (targets.filter (fun q => q ∈ bad)).card ≤ bad.card :=
    Finset.card_le_card (fun q hq => (Finset.mem_filter.mp hq).2)
  calc
    _ ≤ ∑ q ∈ targets, ((if q ∈ bad then (1 : ℝ) else 0) + β) := Finset.sum_le_sum hpoint
    _ = ((targets.filter (fun q => q ∈ bad)).card : ℝ) + β * targets.card := by
      rw [Finset.sum_add_distrib]
      simp [mul_comm]
      congr 1
    _ ≤ _ := add_le_add (by exact_mod_cast hb) le_rfl

theorem exists_cover_of_exceptional_budget (sieve : Finset ℕ) [∀ l : sieve, Fact (l : ℕ).Prime]
    (h : Fin k → ℕ) (sources targets bad reserve : Finset ℕ) (Y : ℕ)
    (μ : ℕ → ℕ → ℝ) (hY : 1 ≤ Y)
    (hμ : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ p n)
    (hprime : ∀ p ∈ sources, p.Prime) (hreserve : ∀ p ∈ reserve, p.Prime)
    (hdisjoint : Disjoint sieve sources) (hfresh : Disjoint (sieve ∪ sources) reserve)
    {β : ℝ} (hβ : 0 ≤ β)
    (hgood : ∀ q ∈ targets, q ∉ bad →
      mean (fun l : sieve => (l : ℕ)) q (miss (fun l : sieve => (l : ℕ)) h sources Y μ q) ≤ β)
    (hbudget : UnitFourier.unitDensity (fun l : sieve => (l : ℕ)) *
      (bad.card + β * targets.card) < reserve.card + 1) :
    ∃ cover : Erdos4.PartialResidueCover targets, cover.primes = (sieve ∪ sources) ∪ reserve := by
  apply SelectedResidueCover.exists_cover_with_reserve sieve h sources targets reserve Y μ hY hμ
    hprime hreserve hdisjoint hfresh
  exact (mul_le_mul_of_nonneg_left
    (target_sum_le (fun l : sieve => (l : ℕ)) h sources targets bad Y μ hμ hβ hgood)
    (UnitFourier.unitDensity_pos (fun l : sieve => (l : ℕ))).le).trans_lt hbudget

end Erdos4.CoverBudget
