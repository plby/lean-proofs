/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterBlue

/-!
# Translated annuli and separated centers

This file packages the deterministic implication used in Hunter's blue
progression argument.  If all local pieces lie in a ball of radius `ρ`, a
three-term progression meeting pieces with centers `i₀,i₁,i₂` forces the
second difference of those centers to have norm at most `4 * ρ`.  A center
separation hypothesis therefore puts all three points in one piece, where
the thin-annulus estimate applies.
-/

namespace Erdos984

section NormedSpace

variable {E ι : Type*} [NormedAddCommGroup E]

/-- Translation of a set, written so membership exposes the canonical local
coordinate `x - center`. -/
def translatedSet (center : E) (S : Set E) : Set E :=
  {x | x - center ∈ S}

@[simp] lemma mem_translatedSet {center x : E} {S : Set E} :
    x ∈ translatedSet center S ↔ x - center ∈ S := Iff.rfl

/-- A local family is contained in radius `ρ` about the origin. -/
def UniformlyLocalized (A : ι → Set E) (ρ : ℝ) : Prop :=
  ∀ i u, u ∈ A i → ‖u‖ ≤ ρ

/-- Hunter's center condition, in the exact one-sided form needed below. -/
def CenterThreeSeparated (center : ι → E) (ρ : ℝ) : Prop :=
  ∀ i₀ i₁ i₂,
    ‖center i₀ - center i₁ - center i₁ + center i₂‖ ≤ 4 * ρ →
      i₀ = i₁ ∧ i₁ = i₂

/-- Localized fibers around three-separated centers cannot be mixed by a
three-term progression. -/
lemma crossThreeSeparated_translated_of_localized
    (center : ι → E) (A : ι → Set E) {ρ : ℝ} {v : E}
    (hlocal : UniformlyLocalized A ρ)
    (hsep : CenterThreeSeparated center ρ) :
    CrossThreeSeparated (fun i ↦ translatedSet (center i) (A i)) v := by
  intro i₀ i₁ i₂ x h₀ h₁ h₂
  have hb₀ : ‖x - center i₀‖ ≤ ρ := hlocal i₀ _ h₀
  have hb₁ : ‖(x + v) - center i₁‖ ≤ ρ := hlocal i₁ _ h₁
  have hb₂ : ‖((x + v) + v) - center i₂‖ ≤ ρ := hlocal i₂ _ h₂
  apply hsep i₀ i₁ i₂
  have hid : center i₀ - center i₁ - center i₁ + center i₂ =
      -(x - center i₀) + ((x + v) - center i₁) +
        ((x + v) - center i₁) - (((x + v) + v) - center i₂) := by
    abel
  rw [hid]
  calc
    ‖-(x - center i₀) + ((x + v) - center i₁) +
        ((x + v) - center i₁) - (((x + v) + v) - center i₂)‖
        ≤ ‖-(x - center i₀) + ((x + v) - center i₁) +
            ((x + v) - center i₁)‖ + ‖((x + v) + v) - center i₂‖ :=
          norm_sub_le _ _
    _ ≤ (‖-(x - center i₀) + ((x + v) - center i₁)‖ +
          ‖(x + v) - center i₁‖) + ‖((x + v) + v) - center i₂‖ := by
          gcongr
          exact norm_add_le _ _
    _ ≤ ((‖-(x - center i₀)‖ + ‖(x + v) - center i₁‖) +
          ‖(x + v) - center i₁‖) + ‖((x + v) + v) - center i₂‖ := by
          gcongr
          exact norm_add_le _ _
    _ ≤ 4 * ρ := by
      rw [norm_neg]
      nlinarith

/-- Translation preserves the step in the thin-annulus obstruction. -/
lemma stepThreeFree_translated_squaredAnnulus
    [InnerProductSpace ℝ E] {center v : E} {radius width : ℝ}
    (hthin : width < squaredNorm v) :
    StepThreeFree
      (translatedSet center {u | InSquaredAnnulus radius width u}) v := by
  intro x h₀ h₁ h₂
  have heq₁ : (x + v) - center = (x - center) + v := by abel
  have heq₂ : ((x + v) + v) - center = ((x - center) + v) + v := by abel
  apply not_three_mem_squaredAnnulus hthin
  refine ⟨h₀, ?_, ?_⟩
  · change InSquaredAnnulus radius width ((x + v) - center) at h₁
    rwa [heq₁] at h₁
  · change InSquaredAnnulus radius width (((x + v) + v) - center) at h₂
    rwa [heq₂] at h₂

/-- The deterministic no-blue-`3` conclusion for a union of selected
translated squared annuli. -/
lemma stepThreeFree_iUnion_translated_squaredAnnulus
    [InnerProductSpace ℝ E] (center : ι → E) (radius width : ι → ℝ)
    {J : Set ι} {ρ : ℝ} {v : E}
    (hlocal : UniformlyLocalized
      (fun i ↦ {u : E | InSquaredAnnulus (radius i) (width i) u}) ρ)
    (hsep : CenterThreeSeparated center ρ)
    (hthin : ∀ i ∈ J, width i < squaredNorm v) :
    StepThreeFree
      (⋃ i ∈ J, translatedSet (center i)
        {u : E | InSquaredAnnulus (radius i) (width i) u}) v := by
  apply stepThreeFree_biUnion
  · exact crossThreeSeparated_translated_of_localized center _ hlocal hsep
  · intro i hi
    exact stepThreeFree_translated_squaredAnnulus (hthin i hi)

end NormedSpace

end Erdos984
