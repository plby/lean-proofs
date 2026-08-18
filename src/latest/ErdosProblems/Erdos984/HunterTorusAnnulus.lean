/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterBlue
import ErdosProblems.Erdos984.HunterTorus

/-!
# The no-wrap thin-annulus argument on the torus

This is the torus version of Hunter's deterministic annulus lemma.  Three
points in one translated projected annulus have Euclidean representatives
whose second difference is an integral vector.  If all coordinates are at
most `ρ` in absolute value and `4 * ρ < 1`, that integral vector is zero.
-/

namespace Erdos984

noncomputable section

/-- Translate the quotient image of a Euclidean set inside the unit torus. -/
def torusTranslatedImage {D : Type*} (center : UnitAddTorus D)
    (S : Set (EuclideanSpace ℝ D)) : Set (UnitAddTorus D) :=
  {x | ∃ u ∈ S, x = center + euclideanToTorus u}

@[simp] lemma mem_torusTranslatedImage {D : Type*} {center x : UnitAddTorus D}
    {S : Set (EuclideanSpace ℝ D)} :
    x ∈ torusTranslatedImage center S ↔
      ∃ u ∈ S, x = center + euclideanToTorus u := Iff.rfl

lemma abs_second_difference_le {a₀ a₁ a₂ ρ : ℝ}
    (h₀ : |a₀| ≤ ρ) (h₁ : |a₁| ≤ ρ) (h₂ : |a₂| ≤ ρ) :
    |a₀ - a₁ - a₁ + a₂| ≤ 4 * ρ := by
  calc
    |a₀ - a₁ - a₁ + a₂| ≤ |a₀ - a₁ - a₁| + |a₂| :=
      abs_add_le _ _
    _ ≤ (|a₀ - a₁| + |a₁|) + |a₂| := by
      gcongr
      exact abs_sub _ _
    _ ≤ ((|a₀| + |a₁|) + |a₁|) + |a₂| := by
      gcongr
      exact abs_sub _ _
    _ ≤ 4 * ρ := by linarith

/-- A sufficiently localized projected squared annulus is three-free for a
torus step whose centered lift is larger than the annulus width. -/
lemma stepThreeFree_torusTranslated_squaredAnnulus
    {D : Type*} [Fintype D] (center v : UnitAddTorus D)
    {radius width ρ : ℝ}
    (hlocal : ∀ u : EuclideanSpace ℝ D,
      InSquaredAnnulus radius width u → ∀ i, |u i| ≤ ρ)
    (hnowrap : 4 * ρ < 1)
    (hthin : width < squaredNorm (centeredTorusLift v)) :
    StepThreeFree
      (torusTranslatedImage center
        {u : EuclideanSpace ℝ D | InSquaredAnnulus radius width u}) v := by
  intro x hx₀ hx₁ hx₂
  obtain ⟨u₀, hu₀, hx₀⟩ := hx₀
  obtain ⟨u₁, hu₁, hx₁⟩ := hx₁
  obtain ⟨u₂, hu₂, hx₂⟩ := hx₂
  have hq₀ : euclideanToTorus u₀ = x - center := by
    rw [hx₀]
    abel
  have hq₁ : euclideanToTorus u₁ = (x + v) - center := by
    rw [hx₁]
    abel
  have hq₂ : euclideanToTorus u₂ = ((x + v) + v) - center := by
    rw [hx₂]
    abel
  have hsecondMap :
      euclideanToTorus (u₀ - u₁ - u₁ + u₂) = 0 := by
    simp only [map_add, map_sub, hq₀, hq₁, hq₂]
    abel
  have hsecondSmall : ∀ i, |(u₀ - u₁ - u₁ + u₂) i| < 1 := by
    intro i
    have hb := abs_second_difference_le
      (hlocal u₀ hu₀ i) (hlocal u₁ hu₁ i) (hlocal u₂ hu₂ i)
    exact hb.trans_lt hnowrap
  have hsecond : u₀ - u₁ - u₁ + u₂ = 0 :=
    eq_zero_of_euclideanToTorus_eq_zero_of_coordinate_abs_lt_one
      hsecondMap hsecondSmall
  let s : EuclideanSpace ℝ D := u₁ - u₀
  have hu₁eq : u₁ = u₀ + s := by
    dsimp [s]
    abel
  have hu₂eq : u₂ = (u₀ + s) + s := by
    have hrewrite : u₀ - u₁ - u₁ + u₂ =
        u₂ - ((u₀ + (u₁ - u₀)) + (u₁ - u₀)) := by
      abel
    rw [hrewrite] at hsecond
    have hz := sub_eq_zero.mp hsecond
    simpa [s] using hz
  have hstepMap : euclideanToTorus s = v := by
    dsimp [s]
    simp only [map_sub, hq₀, hq₁]
    abel
  have hmin : squaredNorm (centeredTorusLift v) ≤ squaredNorm s :=
    centeredTorusLift_squaredNorm_le_of_map_eq hstepMap
  have hthin' : width < squaredNorm s := hthin.trans_le hmin
  apply not_three_mem_squaredAnnulus hthin'
  refine ⟨hu₀, ?_, ?_⟩
  · rwa [← hu₁eq]
  · rwa [← hu₂eq]

end

end Erdos984
