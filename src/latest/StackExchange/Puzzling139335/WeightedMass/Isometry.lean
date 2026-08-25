import StackExchange.Puzzling139335.WeightedMass.Basic
import StackExchange.Puzzling139335.Definitions
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Invariance of the weighted area under congruences

The density giving interior points weight one and frontier points weight one half
is invariant under homeomorphisms.  Its integral is therefore invariant under
measure-preserving homeomorphisms.  In particular, congruent planar sets have the
same weighted area, with no zero-area hypothesis on their frontiers.
-/

open Set MeasureTheory
open scoped ENNReal

namespace Puzzling139335

section Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The interior/frontier density is transported pointwise by a homeomorphism. -/
@[simp] theorem weightedDensity_image_homeomorph
    (e : X ≃ₜ Y) (P : Set X) (x : X) :
    weightedDensity (e '' P) (e x) = weightedDensity P x := by
  simp only [weightedDensity, ← e.image_interior, ← e.image_frontier,
    Pi.add_apply, Set.indicator_image e.injective, Function.comp_def]

/-- The equivalent preimage formulation of pointwise density invariance. -/
theorem weightedDensity_preimage_homeomorph
    (e : X ≃ₜ Y) (P : Set Y) (x : X) :
    weightedDensity (e ⁻¹' P) x = weightedDensity P (e x) := by
  have h := weightedDensity_image_homeomorph e (e ⁻¹' P) x
  rw [e.image_preimage] at h
  exact h.symm

variable [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

/-- A measure-preserving homeomorphism preserves weighted mass even when the
frontier has positive measure. -/
theorem weightedMass_image_homeomorph (e : X ≃ₜ Y)
    {μ : Measure X} {ν : Measure Y} (he : MeasurePreserving e μ ν) (P : Set X) :
    weightedMass ν (e '' P) = weightedMass μ P := by
  unfold weightedMass
  rw [← he.lintegral_comp_emb e.toMeasurableEquiv.measurableEmbedding]
  simp only [weightedDensity_image_homeomorph]

end Homeomorph

/-- An affine Euclidean isometry preserves volume, including when it reverses
orientation. -/
theorem affineIsometry_measurePreserving
    (e : Plane ≃ᵃⁱ[ℝ] Plane) :
    MeasurePreserving e volume volume := by
  have he : (fun x => e.linearIsometryEquiv x + e 0) = e := by
    funext x
    simpa only [vadd_eq_add, add_zero] using (e.map_vadd 0 x).symm
  rw [← he]
  exact (measurePreserving_add_right volume (e 0)).comp e.linearIsometryEquiv.measurePreserving

/-- Ordinary volume is likewise unchanged by an affine Euclidean isometry. -/
theorem volume_image_affineIsometry
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (P : Set Plane) : volume (e '' P) = volume P := by
  have h := (affineIsometry_measurePreserving e).measure_preimage_emb
    e.toHomeomorph.toMeasurableEquiv.measurableEmbedding (e '' P)
  rw [Set.preimage_image_eq _ e.injective] at h
  exact h.symm

/-- An affine Euclidean isometry preserves the weighted area of every set. -/
theorem weightedMass_image_affineIsometry
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (P : Set Plane) :
    weightedMass volume (e '' P) = weightedMass volume P :=
  weightedMass_image_homeomorph e.toHomeomorph (affineIsometry_measurePreserving e) P

/-- Congruent planar regions have equal ordinary volume. -/
theorem Congruent.volume_eq {P Q : Set Plane} (h : Congruent P Q) :
    volume P = volume Q := by
  obtain ⟨e, rfl⟩ := h
  exact (volume_image_affineIsometry e P).symm

/-- Congruent planar regions have equal weighted area, regardless of the area
of their frontiers. -/
theorem Congruent.weightedMass_eq {P Q : Set Plane} (h : Congruent P Q) :
    weightedMass volume P = weightedMass volume Q := by
  obtain ⟨e, rfl⟩ := h
  exact (weightedMass_image_affineIsometry e P).symm

end Puzzling139335
