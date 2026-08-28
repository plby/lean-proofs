import Wikipedia.NoExoticSixSphere.ProductSphereLevelEquations
import Wikipedia.NoExoticSixSphere.CenteredChartCoordinates
import Wikipedia.NoExoticSixSphere.CircleCylinderNativeFiber

/-!
# The circle double's genuine ambient regular equations

The ambient inclusion is the literal product-sphere inclusion. Both sphere
equations and the original doubled map's centered target coordinates
define its regular level. Their full differential is surjective at every
point of the native fiber, retaining both original radial directions.
-/

noncomputable section

open Function Module
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

abbrev HilbertAmbient (m : ℕ) := WithLp 2 (V × EuclideanSpace ℝ (Fin (m + 1)))

abbrev NormalModel (n : ℕ) := WithLp 2 (ℝ × WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n)))

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

local instance : Fact (finrank ℝ V = 1 + 1) := ⟨finrank_euclideanSpace_fin⟩
local instance : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

def ambientInclusion (p : Fiber d) : HilbertAmbient m :=
  ProductSphereLevelEquations.inclusion p.val

def ambientEquations (a : Sphere 1 × Sphere m) : HilbertAmbient m → NormalModel n :=
  ProductSphereLevelEquations.equations a
    (CenteredChartCoordinates.coordinates (map d)
      (modelChartPartialDiffeomorph (I := 𝓡 n) b) b)

theorem ambientEquations_zero (a : Sphere 1 × Sphere m) (p : Fiber d) :
    ambientEquations d a (ambientInclusion d p) = 0 := by
  rw [ambientEquations, ambientInclusion, ProductSphereLevelEquations.equations_inclusion,
    CenteredChartCoordinates.coordinates_eq_zero (map d) _ b p.property]
  rfl

theorem contDiffAt_ambientEquations (a : Sphere 1 × Sphere m) (p : Fiber d) :
    ContDiffAt ℝ ∞ (ambientEquations d a) (ambientInclusion d p) := by
  apply ProductSphereLevelEquations.contDiffAt_equations (m := 1) (n := m)
  apply CenteredChartCoordinates.contMDiffAt_coordinates (map d) _ b (contMDiff_map d p.val)
  rw [p.property]
  exact mem_extChartAt_source b

theorem surjective_fderiv_ambientEquations (a : Sphere 1 × Sphere m) (p : Fiber d) :
    Surjective (fderiv ℝ (ambientEquations d a) (ambientInclusion d p)) := by
  have hc : map d p.val ∈ (modelChartPartialDiffeomorph (I := 𝓡 n) b).source := by
    rw [p.property]
    exact mem_extChartAt_source b
  apply ProductSphereLevelEquations.surjective_fderiv_equations (m := 1) (n := m)
  · exact CenteredChartCoordinates.contMDiffAt_coordinates (map d) _ b
      (contMDiff_map d p.val) hc
  · exact CenteredChartCoordinates.surjective_mfderiv_coordinates (map d) _ b
      (contMDiff_map d p.val) hc (regular_map d p.val p.property)

theorem contMDiff_ambientInclusion (k : ℕ) (hd : m = n + k) :
    letI := fiberAtlas d k hd;
    ContMDiff (𝓡 (k + 1)) 𝓘(ℝ, HilbertAmbient m) ∞ (ambientInclusion d) := by
  let := fiberAtlas d k hd
  exact (ProductSphereLevelEquations.contMDiff_inclusion (m := 1) (n := m)).comp
    (regularFiber_contMDiff_subtype_val (map d) (contMDiff_map d) b (regular_map d)
      (k + 1) (dimension_eq k hd))

theorem injective_mfderiv_ambientInclusion (k : ℕ) (hd : m = n + k) (p : Fiber d) :
    letI := fiberAtlas d k hd;
    Injective (mfderiv (𝓡 (k + 1)) 𝓘(ℝ, HilbertAmbient m) (ambientInclusion d) p) := by
  let := fiberAtlas d k hd
  change Injective (mfderiv (𝓡 (k + 1)) 𝓘(ℝ, HilbertAmbient m)
    (ProductSphereLevelEquations.inclusion ∘ (Subtype.val : Fiber d → Sphere 1 × Sphere m)) p)
  rw [mfderiv_comp p
    ((ProductSphereLevelEquations.contMDiff_inclusion (m := 1) (n := m)).mdifferentiableAt
      (by simp))
    ((regularFiber_contMDiff_subtype_val (map d) (contMDiff_map d) b (regular_map d)
      (k + 1) (dimension_eq k hd)).mdifferentiableAt (by simp))]
  exact (ProductSphereLevelEquations.inclusionDifferential_injective (m := 1) (n := m) p.val).comp
    (regularFiber_injective_mfderiv_subtype_val (map d) (contMDiff_map d) b (regular_map d)
      (k + 1) (dimension_eq k hd) p)

end NoExoticSixSphere.CircleCylinder
