/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Informal source license: CC BY-NC-ND 4.0. This is a new Lean formalization. -/
/-
Informal proof: Steve Fan, building on Vitaly Bergelson and David Simmons.
Formal proof: OpenAI Codex.
Source: https://arxiv.org/abs/2607.14071v3
No pre-existing formalization of this problem was used.
-/
import ErdosProblems.Erdos254.DyadicPartition
import ErdosProblems.Erdos254.ThreeComponent

/-!
# Erdős Problem 254

Steve Fan, "Strongly complete sets and a conjecture of Erdős",
arXiv:2607.14071v3, Corollary 1.2.
https://arxiv.org/abs/2607.14071v3
https://www.erdosproblems.com/254

The proof includes the exceptional-phase countability, deterministic deletion,
dyadic partition, compact-group, finite-support, three-component, and piecewise
Bohr sumset inputs. The latter is proved through scalar spectral measures,
Wiener's estimate, correspondence measures, and finite-pattern embeddings.

`fan_six_per_dyadic` is the stronger selected result. `erdos254` states the
original implication with an explicit eventual bound and distinct summands.
-/

namespace Erdos254

open Filter Set
open scoped BigOperators

/-- Fan's six-per-dyadic-block strong-completeness theorem, in circle notation. -/
theorem stronglyComplete_of_six_per_dyadic {A : Set ℕ}
    (hcount : ∀ᶠ k in atTop, 6 ≤ (dyadicBlock A k).card)
    (hdiv : PhaseDivergent A) : IsStronglyComplete A := by
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp hcount
  obtain ⟨B₁, B₂, C, hUnion, h₁₂, h₁C, h₂C, hi₁, hi₂, hiC, hd₁, hd₂, hdC, hCdiv⟩ :=
    dyadic_three_component_partition hk₀ hdiv
  have hstrong := three_component_stronglyComplete h₁₂ h₁C h₂C hi₁ hi₂ hiC hd₁ hd₂ hdC hCdiv
  rw [hUnion] at hstrong
  exact hstrong.mono sdiff_subset

/-- The selected result with its real, noninteger phase quantifier and literal
dyadic interval cardinalities. -/
theorem fan_six_per_dyadic (A : Set ℕ)
    (hcount : ∀ᶠ k in atTop, 6 ≤ (A ∩ Ioc (2 ^ k) (2 ^ (k + 1))).ncard)
    (hdiv : ∀ θ : ℝ, θ ∉ Set.range (fun z : ℤ ↦ (z : ℝ)) →
      ¬ Summable (fun a : A ↦ distToNearestInt ((a : ℝ) * θ))) :
    IsStronglyComplete A := by
  apply stronglyComplete_of_six_per_dyadic
  · simpa only [dyadicBlock_card] using hcount
  · apply phaseDivergent_of_unit_interval
    intro θ hθ₀ hθ₁
    have hnot : θ ∉ Set.range (fun z : ℤ ↦ (z : ℝ)) := by
      rintro ⟨z, hz⟩
      rw [← hz] at hθ₀ hθ₁
      change (0 : ℝ) < (z : ℝ) at hθ₀
      change (z : ℝ) < (1 : ℝ) at hθ₁
      have hz₀ : (0 : ℤ) < z := by exact_mod_cast hθ₀
      have hz₁ : z < (1 : ℤ) := by exact_mod_cast hθ₁
      omega
    simpa only [mul_comm θ] using hdiv θ hnot

/-- The original hypotheses actually give strong completeness. -/
theorem erdos_254_stronglyComplete (A : Set ℕ)
    (hcount : Tendsto (fun x : ℕ ↦
      (A ∩ Icc 1 (2 * x)).ncard - (A ∩ Icc 1 x).ncard) atTop atTop)
    (hdiv : ∀ θ : ℝ, 0 < θ → θ < 1 →
      ¬ Summable (fun a : A ↦ distToNearestInt (θ * (a : ℝ)))) :
    IsStronglyComplete A :=
  stronglyComplete_of_six_per_dyadic (eventually_dyadic_count_ge hcount 6)
    (phaseDivergent_of_unit_interval hdiv)

/-- Erdős Problem 254: every sufficiently large natural number is a sum of
distinct elements of `A`. No intermediate completeness claim is assumed. -/
theorem erdos254 (A : Set ℕ)
    (hcount : Tendsto (fun x : ℕ ↦
      (A ∩ Icc 1 (2 * x)).ncard - (A ∩ Icc 1 x).ncard) atTop atTop)
    (hdiv : ∀ θ : ℝ, 0 < θ → θ < 1 →
      ¬ Summable (fun a : A ↦ distToNearestInt (θ * (a : ℝ)))) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ F : Finset ℕ, (F : Set ℕ) ⊆ A ∧ ∑ a ∈ F, a = n :=
  eventually_atTop.mp (erdos_254_stronglyComplete A hcount hdiv).isComplete

/-- The canonical statement of Erdős problem 254. -/
theorem erdos_254 (A : Set ℕ)
    (hcount : Tendsto (fun x : ℕ ↦
      (A ∩ Icc 1 (2 * x)).ncard - (A ∩ Icc 1 x).ncard) atTop atTop)
    (hdiv : ∀ θ : ℝ, 0 < θ → θ < 1 →
      ¬ Summable (fun a : A ↦ distToNearestInt (θ * (a : ℝ)))) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ F : Finset ℕ, (F : Set ℕ) ⊆ A ∧ ∑ a ∈ F, a = n :=
  erdos254 A hcount hdiv

#print axioms fan_six_per_dyadic
-- 'Erdos254.fan_six_per_dyadic' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms erdos254
-- 'Erdos254.erdos254' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos254
