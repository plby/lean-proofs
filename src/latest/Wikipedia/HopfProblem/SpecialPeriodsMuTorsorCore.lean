import Wikipedia.HopfProblem.SpecialPeriodsTriangleActions
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientBasic

/-!
# Affine data over the actual triangle action

This file records affine cocycles over the already constructed action of
the genuine free product on the upper half-plane.  It contains no existence
assertion for a special period function.  The concrete affine cocycle is
constructed from the two substitutions in a separate file.

A precisely invariant patch is an actual open subset upstairs, together
with its actual returning subgroup.  These data support extension of a
local affine-equivariant function to the entire saturation of the patch.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor

/-- An affine cocycle over the actual geometric triangle action.  The
multiplicative coefficient is a unit, not an assumed nonvanishing scalar. -/
structure AffineCocycle where
  scale : TriangleGroup → ℍ → ℂˣ
  shift : TriangleGroup → ℍ → ℂ
  scale_one : ∀ z, scale 1 z = 1
  shift_one : ∀ z, shift 1 z = 0
  scale_mul : ∀ g h z,
    scale (g * h) z = scale g (triangleGeometricRepresentation h z) * scale h z
  shift_mul : ∀ g h z,
    shift (g * h) z =
      (scale g (triangleGeometricRepresentation h z) : ℂ) * shift h z +
        shift g (triangleGeometricRepresentation h z)
  scale_holomorphic : ∀ g,
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => (scale g z : ℂ))
  shift_holomorphic : ∀ g, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (shift g)

namespace AffineCocycle

variable (c : AffineCocycle)

/-- The actual fibrewise affine substitution. -/
def fibreMap (g : TriangleGroup) (z : ℍ) (u : ℂ) : ℂ :=
  (c.scale g z : ℂ) * u + c.shift g z

@[simp] theorem fibreMap_one (z : ℍ) (u : ℂ) : c.fibreMap 1 z u = u := by
  simp only [fibreMap, c.scale_one, c.shift_one, Units.val_one, one_mul, add_zero]

theorem fibreMap_mul (g h : TriangleGroup) (z : ℍ) (u : ℂ) :
    c.fibreMap (g * h) z u =
      c.fibreMap g (triangleGeometricRepresentation h z) (c.fibreMap h z u) := by
  simp only [fibreMap, c.scale_mul, c.shift_mul, Units.val_mul]
  ring

theorem fibreMap_inv (g : TriangleGroup) (z : ℍ) (u : ℂ) :
    c.fibreMap g⁻¹ (triangleGeometricRepresentation g z) (c.fibreMap g z u) = u := by
  rw [← c.fibreMap_mul, inv_mul_cancel, c.fibreMap_one]

theorem fibreMap_injective (g : TriangleGroup) (z : ℍ) :
    Function.Injective (c.fibreMap g z) := by
  intro u v huv
  exact mul_left_cancel₀ (c.scale g z).ne_zero (add_right_cancel huv)

theorem fibreMap_sub (g : TriangleGroup) (z : ℍ) (u v : ℂ) :
    c.fibreMap g z u - c.fibreMap g z v = (c.scale g z : ℂ) * (u - v) := by
  simp only [fibreMap]
  ring

/-- Affine equivariance is imposed only where the local function lives. -/
def EquivariantOn (f : ℍ → ℂ) (V : Set ℍ) : Prop :=
  ∀ g z, z ∈ V → f (triangleGeometricRepresentation g z) = c.fibreMap g z (f z)

/-- Differences of affine sections satisfy the associated linear law. -/
theorem sub_equivariantOn {f h : ℍ → ℂ} {V : Set ℍ}
    (hf : c.EquivariantOn f V) (hh : c.EquivariantOn h V) (g : TriangleGroup)
    (z : ℍ) (hz : z ∈ V) :
    f (triangleGeometricRepresentation g z) - h (triangleGeometricRepresentation g z) =
      (c.scale g z : ℂ) * (f z - h z) := by
  rw [hf g z hz, hh g z hz, c.fibreMap_sub]

end AffineCocycle

/-- An actual open set with no returning translate outside its stated
stabilizer.  The generic structure is instantiated by proved triangle
covering, elliptic, and cusp neighbourhoods. -/
structure PreciselyInvariantPatch where
  sheet : TopologicalSpace.Opens ℍ
  stabilizer : Subgroup TriangleGroup
  mapsTo : ∀ g : stabilizer,
    MapsTo (triangleGeometricRepresentation (g : TriangleGroup)) sheet sheet
  returning : ∀ g : TriangleGroup,
    ((triangleGeometricRepresentation g '' (sheet : Set ℍ)) ∩ sheet).Nonempty →
      g ∈ stabilizer

namespace PreciselyInvariantPatch

variable (P : PreciselyInvariantPatch)

/-- The literal union of all triangle translates of the sheet. -/
def saturation : Set ℍ :=
  {z | ∃ g : TriangleGroup, ∃ x : ℍ, x ∈ P.sheet ∧
    triangleGeometricRepresentation g x = z}

theorem mem_saturation (x : ℍ) (hx : x ∈ P.sheet) : x ∈ P.saturation :=
  ⟨1, x, hx, by simp⟩

theorem saturation_invariant (g : TriangleGroup) (z : ℍ) :
    triangleGeometricRepresentation g z ∈ P.saturation ↔ z ∈ P.saturation := by
  constructor
  · rintro ⟨h, x, hx, he⟩
    refine ⟨g⁻¹ * h, x, hx, ?_⟩
    rw [map_mul]
    change triangleGeometricRepresentation g⁻¹ (triangleGeometricRepresentation h x) = z
    rw [he, map_inv]
    exact (triangleGeometricRepresentation g).symm_apply_apply z
  · rintro ⟨h, x, hx, rfl⟩
    exact ⟨g * h, x, hx, by simp⟩

theorem saturation_isOpen : IsOpen P.saturation := by
  have he : P.saturation = ⋃ g : TriangleGroup,
      triangleGeometricRepresentation g '' (P.sheet : Set ℍ) := by
    ext z
    simp only [saturation, mem_iUnion, mem_image]
    rfl
  rw [he]
  exact isOpen_iUnion fun g => (triangleGeometricBiholomorph g).toHomeomorph.isOpenMap
    _ P.sheet.isOpen

/-- The saturation is the full inverse image of its actual quotient image. -/
theorem saturation_eq_preimage_image :
    P.saturation = triangleOrbitProjection ⁻¹' (triangleOrbitProjection '' P.sheet) := by
  ext z
  constructor
  · rintro ⟨g, x, hx, rfl⟩
    exact ⟨x, hx, (triangleOrbitProjection_smul g x).symm⟩
  · rintro ⟨x, hx, he⟩
    obtain ⟨g, hg⟩ := (triangleOrbitProjection_eq_iff z x).mp he.symm
    exact ⟨g, x, hx, hg⟩

theorem stabilizer_mem_iff (g : TriangleGroup) (x : ℍ) (hx : x ∈ P.sheet) :
    triangleGeometricRepresentation g x ∈ P.sheet ↔ g ∈ P.stabilizer := by
  constructor
  · intro hgx
    exact P.returning g ⟨_, ⟨x, hx, rfl⟩, hgx⟩
  · intro hg
    exact P.mapsTo ⟨g, hg⟩ hx

/-- A holomorphic seed satisfying the actual returning-group equations. -/
structure Seed (c : AffineCocycle) where
  toFun : ℍ → ℂ
  holomorphic : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω toFun P.sheet
  equivariant : ∀ g : P.stabilizer, ∀ z ∈ P.sheet,
    toFun (triangleGeometricRepresentation (g : TriangleGroup) z) =
      c.fibreMap g z (toFun z)

end PreciselyInvariantPatch

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor
