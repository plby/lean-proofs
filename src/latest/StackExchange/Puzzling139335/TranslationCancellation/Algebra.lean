import StackExchange.Puzzling139335.WeightedMass.Isometry
import StackExchange.Puzzling139335.TranslationCancellation.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Translation and dihedral cancellation

For the kernel argument, composition is written in the forward direction:
`f x + f (g x)`.  For transported densities, the image convention is used:
the density of the image by `g` is `f (g.symm x)`.
-/

open MeasureTheory

namespace Puzzling139335

/-- An almost-everywhere sign change under a measure-preserving map gives
almost-everywhere invariance under its square. -/
theorem ae_comp_square_eq_self_of_ae_add_comp_eq_zero
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {g : X → X}
    (hg : MeasurePreserving g μ μ) {f : X → ℝ}
    (hanti : (fun x => f x + f (g x)) =ᵐ[μ] 0) :
    (fun x => f (g (g x))) =ᵐ[μ] f := by
  filter_upwards [hanti, hg.quasiMeasurePreserving.ae hanti] with x hx hxg
  change f x + f (g x) = 0 at hx
  change f (g x) + f (g (g x)) = 0 at hxg
  linarith

/-- The operator `f ↦ f + f ∘ g` has trivial kernel on integrable functions
when the square of `g` is a nonzero translation. -/
theorem integrable_eq_zero_of_ae_add_comp_affineIsometry
    (g : Plane ≃ᵃⁱ[ℝ] Plane) {v : Plane} (hv : v ≠ 0)
    (hg2 : ∀ x, g (g x) = x + v) {f : Plane → ℝ}
    (hf : Integrable f volume)
    (hanti : (fun x => f x + f (g x)) =ᵐ[volume] 0) :
    f =ᵐ[volume] 0 := by
  apply integrable_eq_zero_of_ae_add_invariant hv hf
  simpa only [hg2] using
    ae_comp_square_eq_self_of_ae_add_comp_eq_zero
      (affineIsometry_measurePreserving g) hanti

/-- The dihedral commutation law turns invariance of the two-density sum
into a sign change of the difference between the transported densities. -/
theorem dihedral_difference_ae_add_comp_eq_zero
    (g h : Plane ≃ᵃⁱ[ℝ] Plane)
    (hcomm : ∀ x, h (g x) = g.symm (h x)) {f : Plane → ℝ}
    (hF : (fun x => f (h x) + f (g.symm (h x))) =ᵐ[volume]
      (fun x => f x + f (g.symm x))) :
    (fun x => (f (g.symm x) - f (h x)) +
      (f (g.symm (g x)) - f (h (g x)))) =ᵐ[volume] 0 := by
  filter_upwards [hF] with x hx
  simp only [g.symm_apply_apply, hcomm, Pi.zero_apply]
  change f (h x) + f (g.symm (h x)) = f x + f (g.symm x) at hx
  linarith

/-- Commutation with the inverse of `g` suffices for cancellation of the
two-density sum. -/
theorem dihedral_density_cancellation_of_commute
    (g h : Plane ≃ᵃⁱ[ℝ] Plane) {v : Plane} (hv : v ≠ 0)
    (hg2 : ∀ x, g (g x) = x + v)
    (hcomm : ∀ x, h (g x) = g.symm (h x)) {f : Plane → ℝ}
    (hf : Integrable f volume)
    (hF : (fun x => f (h x) + f (g.symm (h x))) =ᵐ[volume]
      (fun x => f x + f (g.symm x))) :
    (fun x => f (g.symm x)) =ᵐ[volume] (fun x => f (h x)) := by
  have hu : Integrable (fun x => f (g.symm x) - f (h x)) volume :=
    ((affineIsometry_measurePreserving g.symm).integrable_comp_of_integrable hf).sub
      ((affineIsometry_measurePreserving h).integrable_comp_of_integrable hf)
  have hz := integrable_eq_zero_of_ae_add_comp_affineIsometry g hv hg2 hu
    (dihedral_difference_ae_add_comp_eq_zero g h hcomm hF)
  filter_upwards [hz] with x hx
  exact sub_eq_zero.mp hx

/-- If an involution conjugates `g` to its inverse and preserves
`f + f ∘ g⁻¹`, the image densities under `g` and the involution agree almost
everywhere.  The square of `g` must be a nonzero translation. -/
theorem dihedral_density_cancellation
    (g h : Plane ≃ᵃⁱ[ℝ] Plane) {v : Plane} (hv : v ≠ 0)
    (hg2 : ∀ x, g (g x) = x + v)
    (hh : ∀ x, h (h x) = x)
    (hconj : ∀ x, h (g (h x)) = g.symm x) {f : Plane → ℝ}
    (hf : Integrable f volume)
    (hF : (fun x => f (h x) + f (g.symm (h x))) =ᵐ[volume]
      (fun x => f x + f (g.symm x))) :
    (fun x => f (g.symm x)) =ᵐ[volume] (fun x => f (h.symm x)) := by
  have hcomm : ∀ x, h (g x) = g.symm (h x) := by
    intro x
    simpa only [hh x] using hconj (h x)
  have heq := dihedral_density_cancellation_of_commute g h hv hg2 hcomm hf hF
  filter_upwards [heq] with x hx
  have hsymm : h.symm x = h x := by
    apply h.injective
    simp only [h.apply_symm_apply, hh]
  simpa only [hsymm] using hx

end Puzzling139335
