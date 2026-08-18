/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterRadial

/-!
# Hunter's blue set with radial labels

This specializes the abstract torus-annulus construction to the independent
labels `e_j ∈ {0,…,K}`.  It proves both sides needed later: a uniform
large-step condition rules out blue three-term progressions, while matching
the unique radial label of a nearby orbit point makes that point blue.
-/

namespace Erdos984

noncomputable section

/-- Squared radius selected by a label in `Fin (K+1)`. -/
def hunterSquaredRadius {K : ℕ} {ι : Type*}
    (Δ : ℝ) (label : ι → Fin (K + 1)) (j : ι) : ℝ :=
  radialSquaredRadius Δ (label j)

/-- Squared annulus width selected by a label in `Fin (K+1)`. -/
def hunterSquaredWidth {K : ℕ} {ι : Type*}
    (Δ : ℝ) (label : ι → Fin (K + 1)) (j : ι) : ℝ :=
  radialSquaredWidth Δ (label j)

def hunterRadialBlueSet {D ι : Type*} [Fintype D] {K : ℕ}
    (center : ι → UnitAddTorus D) (Δ : ℝ)
    (label : ι → Fin (K + 1)) : Set (UnitAddTorus D) :=
  torusAnnulusBlueSet center (hunterSquaredRadius Δ label)
    (hunterSquaredWidth Δ label) Set.univ

noncomputable def hunterRadialColor {D ι : Type*} [Fintype D] {K : ℕ}
    (center : ι → UnitAddTorus D) (Δ : ℝ)
    (label : ι → Fin (K + 1)) (θ : UnitAddTorus D) : ℕ → Bool :=
  torusAnnulusColor center (hunterSquaredRadius Δ label)
    (hunterSquaredWidth Δ label) Set.univ θ

@[simp] lemma hunterRadialColor_eq_false_iff
    {D ι : Type*} [Fintype D] {K : ℕ}
    {center : ι → UnitAddTorus D} {Δ : ℝ}
    {label : ι → Fin (K + 1)} {θ : UnitAddTorus D} {n : ℕ} :
    hunterRadialColor center Δ label θ n = false ↔
      additiveOrbit θ n ∈ hunterRadialBlueSet center Δ label := by
  exact torusAnnulusColor_eq_false_iff

/-- A nearby point is blue when the center's label matches its unique
radial bin. -/
lemma mem_hunterRadialBlueSet_of_label_eq_radialBin
    {D ι : Type*} [Fintype D] {K : ℕ}
    {center : ι → UnitAddTorus D} {Δ : ℝ}
    (hΔ : 0 < Δ) {label : ι → Fin (K + 1)} {j : ι}
    {u : EuclideanSpace ℝ D} {x : UnitAddTorus D}
    (hx : x = center j + euclideanToTorus u)
    (hlabel : (label j : ℕ) = radialBin Δ u) :
    x ∈ hunterRadialBlueSet center Δ label := by
  have hbin := radialBin_spec hΔ u
  rw [← hlabel] at hbin
  have hann := inSquaredAnnulus_of_inRadialBin hΔ.le hbin
  change x ∈ ⋃ i ∈ (Set.univ : Set ι),
    torusTranslatedImage (center i)
      {w : EuclideanSpace ℝ D |
        InSquaredAnnulus (hunterSquaredRadius Δ label i)
          (hunterSquaredWidth Δ label i) w}
  refine Set.mem_iUnion.mpr ⟨j, ?_⟩
  refine Set.mem_iUnion.mpr ⟨Set.mem_univ j, ?_⟩
  exact ⟨u, hann, hx⟩

/-- Deterministic no-blue-`3` theorem for the radial-label construction. -/
lemma hunterRadialColor_avoids_false_three
    {D ι : Type*} [Fintype D] {K : ℕ}
    (center : ι → UnitAddTorus D) (Δ ρ : ℝ)
    (label : ι → Fin (K + 1)) (θ : UnitAddTorus D) (N : ℕ)
    (hΔ : 0 ≤ Δ) (hK : radialLower Δ (K + 1) ≤ ρ)
    (hsep : TorusCenterThreeSeparated center ρ)
    (hnowrap : 4 * ρ < 1)
    (hstep : ∀ d : ℕ, 0 < d → d < N →
      radialSquaredWidth Δ K < squaredNorm (centeredTorusLift (d • θ))) :
    AvoidsColorAP (hunterRadialColor center Δ label θ) false N 3 := by
  apply torusAnnulusColor_avoids_false_three
  · exact radial_annuli_uniformlyLocalized label hΔ hK
  · exact hsep
  · exact hnowrap
  · intro d hd hdN i _hi
    have hlabel : (label i : ℕ) ≤ K := by omega
    exact (radialSquaredWidth_mono hlabel).trans_lt
      (hstep d hd hdN)

end

end Erdos984
