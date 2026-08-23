/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1149.
https://www.erdosproblems.com/forum/thread/1149

Informal authors:
- Vitaly Bergelson
- Florian Karl Richter

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1149.md
-/
/-
Erdős Problem 1149, resolved by Bergelson and Richter (2017).

Problem page: https://www.erdosproblems.com/1149
Source: V. Bergelson and F. K. Richter,
"On the density of coprime tuples of the form
(n, floor(f_1(n)), ..., floor(f_k(n)))", arXiv:1611.08044.

The detailed mathematical proof and the formalization map are in
`tex/1149.tex`.
-/

import Util.Density
import ErdosProblems.Erdos1149.Mobius
import ErdosProblems.Erdos1149.Sieve
import ErdosProblems.Erdos1149.Sublinear
import ErdosProblems.Erdos1149.SuperlinearSieve

namespace Erdos1149

open Filter

/-- The positive integers appearing in Erdős Problem 1149. -/
def coprimePowerFloorSet (α : ℝ) : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ Nat.Coprime n ⌊Real.rpow (n : ℝ) α⌋₊}

/-- Rewrite the repository's natural-density quotient as a filtered prefix
cardinality. -/
lemma partialDensity_eq_card_filter_range (S : Set ℕ)
    [DecidablePred (· ∈ S)] (N : ℕ) :
    S.partialDensity Set.univ N =
      (((Finset.range N).filter fun n ↦ n ∈ S).card : ℝ) / N := by
  classical
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter,
    Set.ncard_Iio_nat]
  have hset : S ∩ Set.Iio N =
      ↑((Finset.range N).filter fun n ↦ n ∈ S) := by
    ext n
    simp [and_comm]
  rw [hset, Set.ncard_coe_finset]

/-- Prefix-card convergence is exactly `Set.HasDensity` on `ℕ`. -/
lemma hasDensity_iff_tendsto_card_filter_range (S : Set ℕ)
    [DecidablePred (· ∈ S)] (d : ℝ) :
    S.HasDensity d ↔
      Tendsto
        (fun N ↦ (((Finset.range N).filter fun n ↦ n ∈ S).card : ℝ) / N)
        atTop (nhds d) := by
  rw [Set.HasDensity]
  exact tendsto_congr' (Eventually.of_forall fun N ↦
    partialDensity_eq_card_filter_range S N)

/-- The exact-one event for the power-floor gcd is the coprimality predicate
in the statement of the problem. -/
lemma exactOneEvent_powerFloorGCD_iff (α : ℝ) (n : ℕ) :
    exactOneEvent (powerFloorGCD α) n ↔ n ∈ coprimePowerFloorSet α := by
  simp only [exactOneEvent, powerFloorGCD, coprimePowerFloorSet,
    Set.mem_ofPred_eq]
  rw [Nat.coprime_iff_gcd_eq_one]
  omega

/-- Transfer the normalized exact-one count supplied by the sieve modules
to the repository's set-density formulation. -/
theorem hasDensity_of_powerFloorGCD_exactOne_tendsto (α : ℝ)
    (h : Tendsto (prefixRatio (exactOneEvent (powerFloorGCD α))) atTop
      (nhds (6 / Real.pi ^ 2))) :
    (coprimePowerFloorSet α).HasDensity (6 / Real.pi ^ 2) := by
  classical
  rw [hasDensity_iff_tendsto_card_filter_range]
  convert h using 1
  funext N
  rw [prefixRatio]
  unfold prefixCount
  congr 1

/-- The density theorem in the elementary inverse-power-block regime. -/
theorem erdos_1149_of_lt_one (α : ℝ) (hα_pos : 0 < α) (hα_one : α < 1) :
    (coprimePowerFloorSet α).HasDensity (6 / Real.pi ^ 2) := by
  exact hasDensity_of_powerFloorGCD_exactOne_tendsto α
    (sublinear_exactOne_tendsto α hα_pos hα_one)

/-- The density theorem in the superlinear regime, expressed through the
two quantitative monomial-discrepancy estimates constructed below. -/
theorem erdos_1149_of_one_lt_of_powerSaving
    (α : ℝ) (hα_one : 1 < α)
    (η₁ C₁ : ℝ) (hη₁_pos : 0 < η₁) (hη₁_one : η₁ < 1) (hC₁ : 0 ≤ C₁)
    (hprefix : MonomialPrefixPowerSaving α (α - 1) η₁ C₁)
    (η₂ C₂ : ℝ) (hη₂_pos : 0 < η₂) (hC₂ : 0 ≤ C₂)
    (hinterval : MonomialIntervalPowerSaving (α - 1) (α + 1) η₂ C₂) :
    (coprimePowerFloorSet α).HasDensity (6 / Real.pi ^ 2) := by
  exact hasDensity_of_powerFloorGCD_exactOne_tendsto α
    (superlinear_exactOne_tendsto_of_powerSaving α hα_one
      η₁ C₁ hη₁_pos hη₁_one hC₁ hprefix
      η₂ C₂ hη₂_pos hC₂ hinterval)

/-- A noninteger real exponent lies strictly on one side of `1`. -/
lemma lt_one_or_one_lt_of_not_integer (α : ℝ)
    (hα : α ∉ Set.range ((↑) : ℤ → ℝ)) : α < 1 ∨ 1 < α := by
  have hne : α ≠ 1 := by
    intro h
    apply hα
    exact ⟨(1 : ℤ), by simpa using h.symm⟩
  exact lt_or_gt_of_ne hne

/-- Subtracting one preserves the property of not being an integer. -/
lemma sub_one_not_integer {α : ℝ}
    (hα : α ∉ Set.range ((↑) : ℤ → ℝ)) :
    α - 1 ∉ Set.range ((↑) : ℤ → ℝ) := by
  rintro ⟨z, hz⟩
  apply hα
  refine ⟨z + 1, ?_⟩
  calc
    (((z + 1 : ℤ) : ℝ)) = (z : ℝ) + 1 := by push_cast; ring
    _ = (α - 1) + 1 := by rw [hz]
    _ = α := by ring

/-- Erdős Problem 1149 (Bergelson--Richter, 2017): for every positive
noninteger real exponent, the integers `n ≥ 1` coprime to `⌊n^α⌋` have
natural density `6 / π²`. -/
theorem erdos_1149 (α : ℝ) (hα_pos : 0 < α)
    (hα_nonint : α ∉ Set.range ((↑) : ℤ → ℝ)) :
    (coprimePowerFloorSet α).HasDensity (6 / Real.pi ^ 2) := by
  rcases lt_one_or_one_lt_of_not_integer α hα_nonint with hα_one | hα_one
  · exact erdos_1149_of_lt_one α hα_pos hα_one
  · have hA_prefix : 0 ≤ α - 1 := by linarith
    obtain ⟨η₁, C₁, hη₁_pos, hη₁_one, hC₁, hprefix⟩ :=
      exists_monomialPrefixPowerSaving hα_pos hα_nonint hA_prefix
    have hβ_pos : 0 < α - 1 := sub_pos.mpr hα_one
    have hβ_nonint : α - 1 ∉ Set.range ((↑) : ℤ → ℝ) :=
      sub_one_not_integer hα_nonint
    have hA_interval : 0 ≤ α + 1 := by linarith
    obtain ⟨η₂, C₂, hη₂_pos, _hη₂_one, hC₂, hinterval⟩ :=
      exists_monomialIntervalPowerSaving hβ_pos hβ_nonint hA_interval
    exact erdos_1149_of_one_lt_of_powerSaving α hα_one
      η₁ C₁ hη₁_pos hη₁_one hC₁ hprefix
      η₂ C₂ hη₂_pos hC₂ hinterval

end Erdos1149

#print axioms Erdos1149.erdos_1149
