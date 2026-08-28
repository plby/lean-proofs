import Wikipedia.HopfProblem.HolomorphicMeromorphicSphereCoordinateBasic
import Wikipedia.HopfProblem.HolomorphicMeromorphicSphereRepresentative

/-!
# The affine coordinate in the genuine meromorphic field of the sphere

The coordinate is glued as a section of the original fraction-stalk sheaf:
it is the holomorphic affine coordinate on the finite chart, and the
reciprocal of the holomorphic reciprocal coordinate on the infinity chart.
The coordinate transition proves local fraction representability, including
at infinity. Its ordinary representative on the finite chart is literally
the identity function.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereNative

open RiemannSphere HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

/-- The original affine coordinate, as an actual fraction germ at every point. -/
def coordinateGerm (p : RiemannSphere) : Germ 𝓘(ℂ) RiemannSphere p := by
  classical
  exact if hf : p ∈ finiteChart then
    sectionGerm 𝓘(ℂ) RiemannSphere finiteChart ⟨p, hf⟩ finiteCoordinate
  else
    (sectionGerm 𝓘(ℂ) RiemannSphere infinityChart
      ⟨p, (chart_cover p).resolve_left hf⟩ infinityCoordinate)⁻¹

theorem coordinateGerm_finite (p : RiemannSphere) (hf : p ∈ finiteChart) :
    coordinateGerm p = sectionGerm 𝓘(ℂ) RiemannSphere finiteChart
      ⟨p, hf⟩ finiteCoordinate := by
  classical
  simp only [coordinateGerm, dif_pos hf]

theorem coordinateGerm_infinity (p : RiemannSphere) (hi : p ∈ infinityChart) :
    coordinateGerm p = (sectionGerm 𝓘(ℂ) RiemannSphere infinityChart
      ⟨p, hi⟩ infinityCoordinate)⁻¹ := by
  classical
  by_cases hf : p ∈ finiteChart
  · rw [coordinateGerm_finite p hf]
    exact finite_germ_eq_inverse_infinity p hf hi
  · simp only [coordinateGerm, dif_neg hf]

/-- The native global meromorphic coordinate. Its local representations
are constructed on the original affine charts. -/
def coordinate : Function 𝓘(ℂ) RiemannSphere :=
  ⟨fun x => coordinateGerm x.val, by
    intro x
    rcases chart_cover x.val with hf | hi
    · refine ⟨finiteChart, hf, homOfLE le_top, finiteCoordinate, 1, ?_, ?_⟩
      · intro y
        rw [map_one]
        exact one_ne_zero
      · intro y
        change coordinateGerm y.val = fraction 𝓘(ℂ) RiemannSphere finiteChart
          finiteCoordinate 1 y
        rw [coordinateGerm_finite y.val y.property]
        simp only [fraction, map_one, div_one]
    · refine ⟨infinityChart, hi, homOfLE le_top, 1, infinityCoordinate,
        infinityCoordinate_germ_ne_zero, ?_⟩
      intro y
      change coordinateGerm y.val = fraction 𝓘(ℂ) RiemannSphere infinityChart
        1 infinityCoordinate y
      rw [coordinateGerm_infinity y.val y.property]
      simp only [fraction, map_one, one_div]⟩

@[simp] theorem coordinate_apply (x : (⊤ : Opens RiemannSphere)) :
    coordinate x = coordinateGerm x.val := rfl

/-- On the finite chart this is the literal native holomorphic coordinate. -/
theorem coordinate_restrict_finite :
    restrict 𝓘(ℂ) RiemannSphere (le_top : finiteChart ≤ ⊤) coordinate =
      ofHolomorphic 𝓘(ℂ) RiemannSphere finiteChart finiteCoordinate := by
  apply section_ext
  intro x
  rw [restrict_apply, coordinate_apply, ofHolomorphic_apply]
  exact coordinateGerm_finite x.val x.property

/-- The representation at infinity has a holomorphic denominator with
nonzero germ, not a denominator assumed to have nonzero value. -/
theorem coordinate_restrict_infinity :
    restrict 𝓘(ℂ) RiemannSphere (le_top : infinityChart ≤ ⊤) coordinate =
      ofFraction 𝓘(ℂ) RiemannSphere infinityChart 1 infinityCoordinate
        infinityCoordinate_germ_ne_zero := by
  apply section_ext
  intro x
  rw [restrict_apply, coordinate_apply, ofFraction_apply]
  rw [coordinateGerm_infinity x.val x.property]
  simp only [fraction, map_one, one_div]

theorem coordinate_finite_holomorphicGerm (z : ℂ) :
    ofHolomorphicGerm 𝓘(ℂ) RiemannSphere (z : RiemannSphere)
        (holomorphicGerm 𝓘(ℂ) RiemannSphere finiteChart
          ⟨(z : RiemannSphere), coe_mem_finiteChart z⟩ finiteCoordinate) =
      coordinate ⟨(z : RiemannSphere), trivial⟩ := by
  change sectionGerm 𝓘(ℂ) RiemannSphere finiteChart
    ⟨(z : RiemannSphere), coe_mem_finiteChart z⟩ finiteCoordinate =
      coordinateGerm (z : RiemannSphere)
  exact (coordinateGerm_finite (z : RiemannSphere) (coe_mem_finiteChart z)).symm

/-- The genuine meromorphic coordinate has the expected ordinary value
at every point of the actual finite affine chart. -/
@[simp] theorem coordinate_finiteValue (z : ℂ) :
    SphereRepresentative.finiteValue coordinate z = z := by
  let x : (⊤ : Opens RiemannSphere) := ⟨(z : RiemannSphere), trivial⟩
  let y : finiteChart := ⟨(z : RiemannSphere), coe_mem_finiteChart z⟩
  have hv := value_eq_of_holomorphicGerm 𝓘(ℂ) RiemannSphere coordinate x
    (holomorphicGerm 𝓘(ℂ) RiemannSphere finiteChart y finiteCoordinate)
    (coordinate_finite_holomorphicGerm z)
  have he := HolomorphicFunctionSheaf.stalkEval_germ 𝓘(ℂ) RiemannSphere finiteChart
    (z : RiemannSphere) (coe_mem_finiteChart z) finiteCoordinate
  exact hv.trans he

end Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereNative
