import Wikipedia.HopfProblem.CanonicalBundle
import Wikipedia.HopfProblem.CuspVolumeCoordinates

/-!
# The trivial canonical bundle of the cusp quotient

This supplies the canonical-bundle assertion of Proposition 4.5(e) for
the constructed cusp filling: its genuine inverse-Jacobian line bundle
has a nowhere-zero holomorphic section and a global holomorphic,
base-preserving, fibrewise linear trivialization.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspQuotient

open ToricCharts ToricSpace

local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

/-- Volume charts on the already constructed complex quotient. Their
transition identity is proved from the actual covering and twisted action. -/
def volumeAtlas :
    letI := chartedSpace C ε hε hε1 hC hR
    CanonicalBundle.ConstantVolumeAtlas (QuotientSpace C ε) (QuotientSpace C ε) := by
  letI := chartedSpace C ε hε hε1 hC hR
  letI := isManifold C ε hε hε1 hC hR
  exact {
    chart := chartAt (CoordinateSpace 3)
    chart_mem_maximalAtlas := fun x => IsManifold.chart_mem_maximalAtlas x
    indexAt := id
    mem_source := mem_chart_source (CoordinateSpace 3)
    coefficient := volumeCoefficient C ε hε hε1 hC hR
    coefficient_ne_zero := volumeCoefficient_ne_zero C ε hε hε1 hC hR
    jacobian_eq := chart_transition_det_fderiv C ε hε hε1 hC hR }

/-- The actual canonical line bundle on the cusp filling. -/
abbrev canonicalBundle :=
  letI := chartedSpace C ε hε hε1 hC hR
  (volumeAtlas C ε hε hε1 hC hR).core

/-- The descended nowhere-vanishing holomorphic volume form. -/
def canonicalVolume (x : QuotientSpace C ε) :
    (canonicalBundle C ε hε hε1 hC hR).Fiber x :=
  letI := chartedSpace C ε hε hε1 hC hR
  (volumeAtlas C ε hε hε1 hC hR).volumeSection x

theorem canonicalVolume_ne_zero (x : QuotientSpace C ε) :
    canonicalVolume C ε hε hε1 hC hR x ≠ 0 := by
  let := chartedSpace C ε hε hε1 hC hR
  exact (volumeAtlas C ε hε hε1 hC hR).volumeSection_ne_zero x

theorem canonicalVolume_holomorphic :
    letI := chartedSpace C ε hε hε1 hC hR
    ContMDiff I₃ ((I₃).prod I₁) ω
      (fun x => (⟨x, canonicalVolume C ε hε hε1 hC hR x⟩ :
        (canonicalBundle C ε hε hε1 hC hR).TotalSpace)) := by
  let := chartedSpace C ε hε hε1 hC hR
  exact (volumeAtlas C ε hε hε1 hC hR).volumeSection_holomorphic

/-- In each actual quotient chart, the descended volume has the signed
coefficient of the toric chart used for that covering lift. -/
theorem canonicalVolume_in_coordinates (i x : QuotientSpace C ε) :
    letI := chartedSpace C ε hε hε1 hC hR
    (volumeAtlas C ε hε hε1 hC hR).inCoordinates i x
      (canonicalVolume C ε hε hε1 hC hR x) =
      volumeCoefficient C ε hε hε1 hC hR i • CanonicalBundle.volume := by
  let := chartedSpace C ε hε hε1 hC hR
  exact (volumeAtlas C ε hε hε1 hC hR).volumeSection_inCoordinates i x

/-- Pullback through the genuine covering map recovers the toric volume
in source coordinates, including along the central fibre. -/
theorem canonicalVolume_pullback_quotientMap (a : Tube (disc ε)) (y : QuotientSpace C ε) :
    letI := chartedSpace C ε hε hε1 hC hR
    ∀ z ∈ (chartAt (CoordinateSpace 3) a).target,
      quotientMap C ε ((chartAt (CoordinateSpace 3) a).symm z) ∈
        (chartAt (CoordinateSpace 3) y).source →
      ((volumeAtlas C ε hε hε1 hC hR).inCoordinates y
        (quotientMap C ε ((chartAt (CoordinateSpace 3) a).symm z))
        (canonicalVolume C ε hε hε1 hC hR
          (quotientMap C ε ((chartAt (CoordinateSpace 3) a).symm z)))).compContinuousLinearMap
        (fderiv ℂ (chartAt (CoordinateSpace 3) y ∘ quotientMap C ε ∘
          (chartAt (CoordinateSpace 3) a).symm) z) =
      ((preferredTriangle (a : Space)).rays.det : ℂ) • CanonicalBundle.volume := by
  let := chartedSpace C ε hε hε1 hC hR
  intro z hz hy
  rw [canonicalVolume_in_coordinates, CanonicalBundle.pullback_eq_det_smul,
    quotientMap_chart_det_fderiv C ε hε hε1 hC hR a y z hz hy, smul_smul]
  rw [div_mul_cancel₀ _ (volumeCoefficient_ne_zero C ε hε hε1 hC hR y)]

/-- The triviality conclusion is a biholomorphism of the canonical bundle
total space with the trivial line bundle, not a proposition used as input. -/
def canonicalTrivialization :
    letI := chartedSpace C ε hε hε1 hC hR
    Diffeomorph ((I₃).prod I₁) ((I₃).prod I₁)
      (canonicalBundle C ε hε hε1 hC hR).TotalSpace (QuotientSpace C ε × ℂ) ω :=
  letI := chartedSpace C ε hε hε1 hC hR
  (volumeAtlas C ε hε hε1 hC hR).globalTrivialization

@[simp] theorem canonicalTrivialization_fst
    (p : (canonicalBundle C ε hε hε1 hC hR).TotalSpace) :
    (canonicalTrivialization C ε hε hε1 hC hR p).1 = p.1 := rfl

theorem canonicalTrivialization_add (x : QuotientSpace C ε)
    (v w : (canonicalBundle C ε hε hε1 hC hR).Fiber x) :
    (canonicalTrivialization C ε hε hε1 hC hR ⟨x, v + w⟩).2 =
      (canonicalTrivialization C ε hε hε1 hC hR ⟨x, v⟩).2 +
        (canonicalTrivialization C ε hε hε1 hC hR ⟨x, w⟩).2 := by
  let := chartedSpace C ε hε hε1 hC hR
  exact (volumeAtlas C ε hε hε1 hC hR).globalTrivialization_add x v w

theorem canonicalTrivialization_smul (x : QuotientSpace C ε) (c : ℂ)
    (v : (canonicalBundle C ε hε hε1 hC hR).Fiber x) :
    (canonicalTrivialization C ε hε hε1 hC hR ⟨x, c • v⟩).2 =
      c • (canonicalTrivialization C ε hε hε1 hC hR ⟨x, v⟩).2 := by
  let := chartedSpace C ε hε hε1 hC hR
  exact (volumeAtlas C ε hε hε1 hC hR).globalTrivialization_smul x c v

end Wikipedia.HopfProblem.CuspQuotient
