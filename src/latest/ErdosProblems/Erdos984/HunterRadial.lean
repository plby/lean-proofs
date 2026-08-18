/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterTorusBlue

/-!
# Radial bins for Hunter's projected annuli

The paper uses norm annuli `[hΔ,(h+1)Δ)`.  The parallelogram lemma is
most convenient for squared norms, so we record the exact conversion: the
corresponding squared radius is `(hΔ)^2` and its squared width is
`(2h+1)Δ^2`.  We also define and characterize the unique radial bin by a
natural floor.
-/

namespace Erdos984

noncomputable section

def radialLower (Δ : ℝ) (h : ℕ) : ℝ := (h : ℝ) * Δ

def radialSquaredRadius (Δ : ℝ) (h : ℕ) : ℝ :=
  (radialLower Δ h) ^ 2

def radialSquaredWidth (Δ : ℝ) (h : ℕ) : ℝ :=
  ((2 * h + 1 : ℕ) : ℝ) * Δ ^ 2

def InRadialBin {E : Type*} [Norm E] (Δ : ℝ) (h : ℕ) (u : E) : Prop :=
  radialLower Δ h ≤ ‖u‖ ∧ ‖u‖ < radialLower Δ (h + 1)

lemma radial_square_identity (Δ : ℝ) (h : ℕ) :
    (radialLower Δ (h + 1)) ^ 2 =
      radialSquaredRadius Δ h + radialSquaredWidth Δ h := by
  simp only [radialLower, radialSquaredRadius, radialSquaredWidth, Nat.cast_add,
    Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- A norm radial bin lies in the corresponding closed squared annulus. -/
lemma inSquaredAnnulus_of_inRadialBin
    {E : Type*} [NormedAddCommGroup E] {Δ : ℝ} {h : ℕ} {u : E}
    (hΔ : 0 ≤ Δ) (hu : InRadialBin Δ h u) :
    InSquaredAnnulus (radialSquaredRadius Δ h)
      (radialSquaredWidth Δ h) u := by
  have hlower : 0 ≤ radialLower Δ h := by
    exact mul_nonneg (Nat.cast_nonneg _) hΔ
  have hupper : 0 ≤ radialLower Δ (h + 1) := by
    exact mul_nonneg (Nat.cast_nonneg _) hΔ
  constructor
  · rw [radialSquaredRadius, squaredNorm]
    exact (sq_le_sq₀ hlower (norm_nonneg _)).2 hu.1
  · rw [squaredNorm, ← radial_square_identity]
    exact ((sq_lt_sq₀ (norm_nonneg _) hupper).2 hu.2).le

/-- The unique natural radial-bin index. -/
def radialBin {E : Type*} [Norm E] (Δ : ℝ) (u : E) : ℕ :=
  ⌊‖u‖ / Δ⌋₊

lemma radialBin_spec {E : Type*} [NormedAddCommGroup E]
    {Δ : ℝ} (hΔ : 0 < Δ) (u : E) :
    InRadialBin Δ (radialBin Δ u) u := by
  have hq : 0 ≤ ‖u‖ / Δ := div_nonneg (norm_nonneg _) hΔ.le
  have hfloor : ((radialBin Δ u : ℕ) : ℝ) ≤ ‖u‖ / Δ := by
    exact Nat.floor_le hq
  have hnext : ‖u‖ / Δ < ((radialBin Δ u + 1 : ℕ) : ℝ) := by
    simpa only [radialBin, Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one (‖u‖ / Δ))
  constructor
  · rw [radialLower]
    exact (le_div_iff₀ hΔ).mp hfloor
  · rw [radialLower]
    exact (div_lt_iff₀ hΔ).mp (by simpa using hnext)

lemma radialBin_unique {E : Type*} [NormedAddCommGroup E]
    {Δ : ℝ} (hΔ : 0 < Δ) {u : E} {h : ℕ}
    (hu : InRadialBin Δ h u) : radialBin Δ u = h := by
  have hq : 0 ≤ ‖u‖ / Δ := div_nonneg (norm_nonneg _) hΔ.le
  apply (Nat.floor_eq_iff hq).2
  constructor
  · rw [le_div_iff₀ hΔ]
    exact hu.1
  · rw [div_lt_iff₀ hΔ]
    simpa [radialLower] using hu.2

lemma radialBin_le {E : Type*} [NormedAddCommGroup E]
    {Δ : ℝ} (hΔ : 0 < Δ) {u : E} {K : ℕ}
    (hu : ‖u‖ < radialLower Δ (K + 1)) :
    radialBin Δ u ≤ K := by
  have hq : 0 ≤ ‖u‖ / Δ := div_nonneg (norm_nonneg _) hΔ.le
  have hdiv : ‖u‖ / Δ < (K + 1 : ℕ) := by
    rw [div_lt_iff₀ hΔ]
    simpa [radialLower] using hu
  have : radialBin Δ u < K + 1 := (Nat.floor_lt hq).2 hdiv
  omega

/-- Every selected radial annulus with index at most `K` is contained in a
coordinate box once `(K+1)Δ ≤ ρ`. -/
lemma radial_annuli_uniformlyLocalized
    {D ι : Type*} [Fintype D] (label : ι → Fin (K + 1))
    {Δ ρ : ℝ} (hΔ : 0 ≤ Δ)
    (hK : radialLower Δ (K + 1) ≤ ρ) :
    TorusUniformlyLocalized
      (fun j ↦ {u : EuclideanSpace ℝ D |
        InSquaredAnnulus (radialSquaredRadius Δ (label j))
          (radialSquaredWidth Δ (label j)) u}) ρ := by
  intro j u hu r
  have hcoord : |u r| ≤ ‖u‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u r
  have hupper0 : 0 ≤ radialLower Δ ((label j : ℕ) + 1) :=
    mul_nonneg (Nat.cast_nonneg _) hΔ
  have hsquares : ‖u‖ ^ 2 ≤
      (radialLower Δ ((label j : ℕ) + 1)) ^ 2 := by
    rw [radial_square_identity]
    exact hu.2
  have hnorm : ‖u‖ ≤ radialLower Δ ((label j : ℕ) + 1) :=
    (sq_le_sq₀ (norm_nonneg _) hupper0).1 hsquares
  have hlabel : (label j : ℕ) + 1 ≤ K + 1 := by omega
  have hradial : radialLower Δ ((label j : ℕ) + 1) ≤
      radialLower Δ (K + 1) := by
    dsimp [radialLower]
    gcongr
  exact hcoord.trans (hnorm.trans (hradial.trans hK))

lemma radialSquaredWidth_mono {h K : ℕ} (hhK : h ≤ K) {Δ : ℝ} :
    radialSquaredWidth Δ h ≤ radialSquaredWidth Δ K := by
  dsimp [radialSquaredWidth]
  gcongr

end

end Erdos984
