/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterTorusAnnulus

/-!
# Separated projected annuli contain no blue three-term progression

The preceding file handles one projected annulus.  This file proves that
Hunter's coordinatewise second-difference separation of the centers keeps a
three-term progression from mixing three different translates, and then
combines the two statements for an arbitrary selected union.
-/

namespace Erdos984

noncomputable section

/-- Every local Euclidean fiber is contained in the coordinate box of
radius `ρ`. -/
def TorusUniformlyLocalized {D ι : Type*} [Fintype D]
    (A : ι → Set (EuclideanSpace ℝ D)) (ρ : ℝ) : Prop :=
  ∀ i u, u ∈ A i → ∀ r, |u r| ≤ ρ

/-- Coordinatewise form of Hunter's center separation property. -/
def TorusCenterThreeSeparated {D ι : Type*}
    (center : ι → UnitAddTorus D) (ρ : ℝ) : Prop :=
  ∀ i₀ i₁ i₂,
    (∀ r, ‖(center i₀ - center i₁ - center i₁ + center i₂) r‖ ≤ 4 * ρ) →
      i₀ = i₁ ∧ i₁ = i₂

/-- Localized quotient images around separated torus centers cannot be
mixed by a three-term progression. -/
lemma crossThreeSeparated_torusTranslatedImage
    {D ι : Type*} [Fintype D] (center : ι → UnitAddTorus D)
    (A : ι → Set (EuclideanSpace ℝ D)) {ρ : ℝ} {v : UnitAddTorus D}
    (hlocal : TorusUniformlyLocalized A ρ)
    (hsep : TorusCenterThreeSeparated center ρ) :
    CrossThreeSeparated (fun i ↦ torusTranslatedImage (center i) (A i)) v := by
  intro i₀ i₁ i₂ x hx₀ hx₁ hx₂
  obtain ⟨u₀, hu₀, hx₀⟩ := hx₀
  obtain ⟨u₁, hu₁, hx₁⟩ := hx₁
  obtain ⟨u₂, hu₂, hx₂⟩ := hx₂
  have hq₀ : euclideanToTorus u₀ = x - center i₀ := by
    rw [hx₀]
    abel
  have hq₁ : euclideanToTorus u₁ = (x + v) - center i₁ := by
    rw [hx₁]
    abel
  have hq₂ : euclideanToTorus u₂ = ((x + v) + v) - center i₂ := by
    rw [hx₂]
    abel
  have hcenters : center i₀ - center i₁ - center i₁ + center i₂ =
      -(euclideanToTorus (u₀ - u₁ - u₁ + u₂)) := by
    simp only [map_add, map_sub, hq₀, hq₁, hq₂]
    abel
  apply hsep i₀ i₁ i₂
  intro r
  rw [hcenters]
  simp only [Pi.neg_apply, norm_neg]
  change ‖(((u₀ - u₁ - u₁ + u₂) r : ℝ) : UnitAddCircle)‖ ≤ 4 * ρ
  calc
    ‖(((u₀ - u₁ - u₁ + u₂) r : ℝ) : UnitAddCircle)‖ ≤
        ‖(u₀ - u₁ - u₁ + u₂) r‖ := QuotientAddGroup.norm_mk_le_norm
    _ = |u₀ r - u₁ r - u₁ r + u₂ r| := by
      simp only [PiLp.sub_apply, PiLp.add_apply, Real.norm_eq_abs]
    _ ≤ 4 * ρ := abs_second_difference_le
      (hlocal i₀ u₀ hu₀ r) (hlocal i₁ u₁ hu₁ r)
      (hlocal i₂ u₂ hu₂ r)

/-- The selected union of translated projected squared annuli is three-free
for every step whose centered lift is wider than each selected annulus. -/
lemma stepThreeFree_iUnion_torusTranslated_squaredAnnulus
    {D ι : Type*} [Fintype D]
    (center : ι → UnitAddTorus D) (radius width : ι → ℝ)
    {J : Set ι} {ρ : ℝ} {v : UnitAddTorus D}
    (hlocal : TorusUniformlyLocalized
      (fun i ↦ {u : EuclideanSpace ℝ D |
        InSquaredAnnulus (radius i) (width i) u}) ρ)
    (hsep : TorusCenterThreeSeparated center ρ)
    (hnowrap : 4 * ρ < 1)
    (hthin : ∀ i ∈ J, width i < squaredNorm (centeredTorusLift v)) :
    StepThreeFree
      (⋃ i ∈ J, torusTranslatedImage (center i)
        {u : EuclideanSpace ℝ D |
          InSquaredAnnulus (radius i) (width i) u}) v := by
  apply stepThreeFree_biUnion
  · exact crossThreeSeparated_torusTranslatedImage center _ hlocal hsep
  · intro i hi
    exact stepThreeFree_torusTranslated_squaredAnnulus
      (center i) v (hlocal i) hnowrap (hthin i hi)

/-- The blue subset of the torus determined by a selected family of
translated projected annuli. -/
def torusAnnulusBlueSet {D ι : Type*} [Fintype D]
    (center : ι → UnitAddTorus D) (radius width : ι → ℝ)
    (J : Set ι) : Set (UnitAddTorus D) :=
  ⋃ i ∈ J, torusTranslatedImage (center i)
    {u : EuclideanSpace ℝ D | InSquaredAnnulus (radius i) (width i) u}

/-- Pull back the annular blue set along the additive orbit of `θ`. -/
noncomputable def torusAnnulusColor {D ι : Type*} [Fintype D]
    (center : ι → UnitAddTorus D) (radius width : ι → ℝ)
    (J : Set ι) (θ : UnitAddTorus D) : ℕ → Bool := by
  classical
  exact orbitColor θ (torusAnnulusBlueSet center radius width J)

@[simp] lemma torusAnnulusColor_eq_false_iff
    {D ι : Type*} [Fintype D]
    {center : ι → UnitAddTorus D} {radius width : ι → ℝ}
    {J : Set ι} {θ : UnitAddTorus D} {n : ℕ} :
    torusAnnulusColor center radius width J θ n = false ↔
      additiveOrbit θ n ∈ torusAnnulusBlueSet center radius width J := by
  classical
  simp [torusAnnulusColor]

/-- Complete deterministic blue half of Hunter's finite coloring: center
separation and the absence of a small torus multiple imply that the orbit
coloring has no blue three-term progression in `[0,N)`. -/
lemma torusAnnulusColor_avoids_false_three
    {D ι : Type*} [Fintype D]
    (center : ι → UnitAddTorus D) (radius width : ι → ℝ)
    (J : Set ι) (θ : UnitAddTorus D) (N : ℕ) {ρ : ℝ}
    (hlocal : TorusUniformlyLocalized
      (fun i ↦ {u : EuclideanSpace ℝ D |
        InSquaredAnnulus (radius i) (width i) u}) ρ)
    (hsep : TorusCenterThreeSeparated center ρ)
    (hnowrap : 4 * ρ < 1)
    (hstep : ∀ d : ℕ, 0 < d → d < N → ∀ i ∈ J,
      width i < squaredNorm (centeredTorusLift (d • θ))) :
    AvoidsColorAP (torusAnnulusColor center radius width J θ) false N 3 := by
  classical
  apply orbitColor_avoids_false_three θ
    (torusAnnulusBlueSet center radius width J) N
  intro d hd hdN
  exact stepThreeFree_iUnion_torusTranslated_squaredAnnulus
    center radius width hlocal hsep hnowrap (hstep d hd hdN)

end

end Erdos984
