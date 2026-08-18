import ErdosProblems.Erdos140.RelativeChangSanders

/-!
# Staged selection for weighted dissociativity

This file isolates the finite greedy selection used in Sanders' relative
Chang argument.  At stage `j`, the permitted Riesz-product loss is
`j / (2 * (k + 1))`.
-/

noncomputable section

open Finset Function Real
open scoped BigOperators ComplexConjugate NNReal

namespace Erdos140.RelativeChangSanders

variable {G : Type*} [Fintype G] [AddCommGroup G]

/-- Weighted dissociativity is monotone in its permitted exponential loss. -/
theorem IsWeightedDissociated.mono_threshold
    {mu : G → ℝ} {K L : ℝ} {Delta : Finset (AddChar G ℂ)}
    (hKL : K ≤ L) (hDelta : IsWeightedDissociated mu K Delta) :
    IsWeightedDissociated mu L Delta := by
  intro u hu
  exact (hDelta u hu).trans (Real.exp_le_exp.mpr hKL)

/-- Sanders' staged greedy selection.  The selected set is dissociated at
the threshold associated to its size, while adjoining any unused element
fails at the next stage's threshold. -/
theorem exists_weightedDissociated_staged_selection
    (mu : G → ℝ) (S : Finset (AddChar G ℂ)) (k : ℕ)
    (_hmu_nonneg : ∀ x, 0 ≤ mu x)
    (hmu_sum : ∑ x : G, mu x = 1)
    (hcard : ∀ Delta : Finset (AddChar G ℂ), Delta ⊆ S →
      IsWeightedDissociated mu 1 Delta → Delta.card ≤ k) :
    ∃ Delta : Finset (AddChar G ℂ),
      Delta ⊆ S ∧
      Delta.card ≤ k ∧
      IsWeightedDissociated mu
        ((Delta.card : ℝ) / (2 * ((k + 1 : ℕ) : ℝ))) Delta ∧
      ∀ gamma ∈ S \ Delta,
        ¬IsWeightedDissociated mu
          (((Delta.card + 1 : ℕ) : ℝ) / (2 * ((k + 1 : ℕ) : ℝ)))
          (Delta ∪ {gamma}) := by
  classical
  let candidates : Finset (Finset (AddChar G ℂ)) :=
    S.powerset.filter fun Delta ↦
      Delta.card ≤ k ∧
        IsWeightedDissociated mu
          ((Delta.card : ℝ) / (2 * ((k + 1 : ℕ) : ℝ))) Delta
  have hempty_dissociated : IsWeightedDissociated mu 0
      (∅ : Finset (AddChar G ℂ)) := by
    intro u hu
    simpa [hmu_sum]
  have hempty : (∅ : Finset (AddChar G ℂ)) ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.empty_subset S, Nat.zero_le k, ?_⟩
    simpa using hempty_dissociated
  let sizes : Finset ℕ := candidates.image Finset.card
  have hsizes : sizes.Nonempty := by
    refine ⟨0, ?_⟩
    exact Finset.mem_image.mpr ⟨∅, hempty, rfl⟩
  let m : ℕ := sizes.max' hsizes
  have hm : m ∈ sizes := sizes.max'_mem hsizes
  obtain ⟨Delta, hDelta_candidate, hDelta_card⟩ :=
    Finset.mem_image.mp hm
  have hDelta_parts := Finset.mem_filter.mp hDelta_candidate
  have hDelta_subset : Delta ⊆ S := Finset.mem_powerset.mp hDelta_parts.1
  have hDelta_card_le : Delta.card ≤ k := hDelta_parts.2.1
  have hDelta_dissociated :
      IsWeightedDissociated mu
        ((Delta.card : ℝ) / (2 * ((k + 1 : ℕ) : ℝ))) Delta :=
    hDelta_parts.2.2
  have hmaximal (D : Finset (AddChar G ℂ)) (hD : D ∈ candidates) :
      D.card ≤ Delta.card := by
    have hD_size : D.card ∈ sizes := Finset.mem_image.mpr ⟨D, hD, rfl⟩
    calc
      D.card ≤ m := Finset.le_max' sizes D.card hD_size
      _ = Delta.card := hDelta_card.symm
  refine ⟨Delta, hDelta_subset, hDelta_card_le, hDelta_dissociated, ?_⟩
  intro gamma hgamma
  intro hnext
  have hgammaS : gamma ∈ S := (Finset.mem_sdiff.mp hgamma).1
  have hgamma_not_mem : gamma ∉ Delta := (Finset.mem_sdiff.mp hgamma).2
  have hcard_union : (Delta ∪ {gamma}).card = Delta.card + 1 := by
    simpa [Finset.union_comm] using
      (Finset.card_insert_of_notMem hgamma_not_mem)
  have hunion_subset : Delta ∪ {gamma} ⊆ S := by
    exact Finset.union_subset hDelta_subset (by simpa using hgammaS)
  have hthreshold_le_one :
      (((Delta.card + 1 : ℕ) : ℝ) / (2 * ((k + 1 : ℕ) : ℝ))) ≤ 1 := by
    have hdenom_pos : (0 : ℝ) < 2 * ((k + 1 : ℕ) : ℝ) := by positivity
    rw [div_le_iff₀ hdenom_pos]
    norm_num only [one_mul, Nat.cast_add, Nat.cast_one]
    have hDelta_card_le_real : (Delta.card : ℝ) ≤ k := by
      exact_mod_cast hDelta_card_le
    linarith
  have hunion_dissociated_one :
      IsWeightedDissociated mu 1 (Delta ∪ {gamma}) :=
    hnext.mono_threshold hthreshold_le_one
  have hunion_card_le : (Delta ∪ {gamma}).card ≤ k :=
    hcard (Delta ∪ {gamma}) hunion_subset hunion_dissociated_one
  have hunion_candidate : Delta ∪ {gamma} ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨hunion_subset, hunion_card_le, ?_⟩
    simpa [Finset.card_insert_of_notMem hgamma_not_mem] using hnext
  have := hmaximal (Delta ∪ {gamma}) hunion_candidate
  omega

#print axioms IsWeightedDissociated.mono_threshold
#print axioms exists_weightedDissociated_staged_selection

end Erdos140.RelativeChangSanders
