import StackExchange.Puzzling139335.TranslationCancellation.Algebra
import StackExchange.Puzzling139335.TranslationCancellation.Density
import StackExchange.Puzzling139335.TranslationCancellation.Union

/-!
# Dihedral cancellation identifies actual Jordan images

The symmetry of the sum of two weighted densities implies equality of the
image densities almost everywhere. Closed regular regions are determined by
that equality, so the conclusion identifies the actual sets, including their
frontiers. The final corollaries derive the density symmetry from symmetry of
the union, provided the common outer contacts form a null set.
-/

open Set MeasureTheory

namespace Puzzling139335

/-- At any target point, the density of an isometric image is the original
density evaluated at the inverse image. -/
theorem weightedDensityReal_image_affineIsometry_apply
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (P : Set Plane) (x : Plane) :
    weightedDensityReal (e '' P) x = weightedDensityReal P (e.symm x) := by
  simpa only [e.apply_symm_apply] using
    weightedDensityReal_image_affineIsometry e P (e.symm x)

/-- If an involution conjugates `g` to its inverse and preserves the sum of a
Jordan region's density and its `g`-image density, the `g`-image and the
involution's image are equal as sets. -/
theorem IsJordanRegion.image_eq_of_dihedral_density_symmetry
    {P : Set Plane} (hP : IsJordanRegion P)
    (g h : Plane ≃ᵃⁱ[ℝ] Plane) {v : Plane} (hv : v ≠ 0)
    (hg2 : ∀ x, g (g x) = x + v)
    (hh : ∀ x, h (h x) = x)
    (hconj : ∀ x, h (g (h x)) = g.symm x)
    (hF : (fun x => weightedDensityReal P (h x) +
      weightedDensityReal (g '' P) (h x)) =ᵐ[volume]
        (fun x => weightedDensityReal P x + weightedDensityReal (g '' P) x)) :
    g '' P = h '' P := by
  have hF' : (fun x => weightedDensityReal P (h x) +
      weightedDensityReal P (g.symm (h x))) =ᵐ[volume]
        (fun x => weightedDensityReal P x + weightedDensityReal P (g.symm x)) := by
    simpa only [weightedDensityReal_image_affineIsometry_apply] using hF
  have heq := dihedral_density_cancellation g h hv hg2 hh hconj
    hP.integrable_weightedDensityReal hF'
  have hρ : weightedDensityReal (g '' P) =ᵐ[volume]
      weightedDensityReal (h '' P) := by
    filter_upwards [heq] with x hx
    simpa only [weightedDensityReal_image_affineIsometry_apply] using hx
  have hclosed (e : Plane ≃ᵃⁱ[ℝ] Plane) : IsClosed (e '' P) :=
    e.toHomeomorph.isClosedMap P hP.isClosed
  have hreg (e : Plane ≃ᵃⁱ[ℝ] Plane) :
      closure (interior (e '' P)) = e '' P := by
    change closure (interior (e.toHomeomorph '' P)) = e.toHomeomorph '' P
    rw [← e.toHomeomorph.image_interior, ← e.toHomeomorph.image_closure,
      hP.closure_interior]
  exact Puzzling139335.eq_of_weightedDensityReal_ae
    (hclosed g) (hclosed h) (hreg g) (hreg h) hρ

/-- Symmetry of the actual two-piece union gives the required density
symmetry when the common contacts on its outer frontier have zero area. -/
theorem IsJordanRegion.image_eq_of_dihedral_union_symmetry
    {P : Set Plane} (hP : IsJordanRegion P)
    (g h : Plane ≃ᵃⁱ[ℝ] Plane) {v : Plane} (hv : v ≠ 0)
    (hg2 : ∀ x, g (g x) = x + v)
    (hh : ∀ x, h (h x) = x)
    (hconj : ∀ x, h (g (h x)) = g.symm x)
    (hdisj : Disjoint (interior P) (interior (g '' P)))
    (hunion : h '' (P ∪ g '' P) = P ∪ g '' P)
    (hcontact : volume (P ∩ g '' P ∩ frontier (P ∪ g '' P)) = 0) :
    g '' P = h '' P := by
  apply hP.image_eq_of_dihedral_density_symmetry g h hv hg2 hh hconj
  have hQclosed : IsClosed (g '' P) := g.toHomeomorph.isClosedMap P hP.isClosed
  have hQreg : closure (interior (g '' P)) = g '' P := by
    change closure (interior (g.toHomeomorph '' P)) = g.toHomeomorph '' P
    rw [← g.toHomeomorph.image_interior, ← g.toHomeomorph.image_closure,
      hP.closure_interior]
  have hsum := weightedDensityReal_union_ae hP.isClosed hQclosed
    hP.closure_interior hQreg hdisj volume hcontact
  have hsumh := (affineIsometry_measurePreserving h).quasiMeasurePreserving.ae hsum
  filter_upwards [hsum, hsumh] with x hx hxh
  have hρh : weightedDensityReal (P ∪ g '' P) (h x) =
      weightedDensityReal (P ∪ g '' P) x := by
    have heq := weightedDensityReal_image_affineIsometry h (P ∪ g '' P) x
    rwa [hunion] at heq
  exact hxh.symm.trans (hρh.trans hx)

/-- For a proper Jordan cut the common outer contacts are its two endpoints;
any finite set of such contacts suffices for dihedral cancellation. -/
theorem IsJordanRegion.image_eq_of_dihedral_union_symmetry_of_finite
    {P : Set Plane} (hP : IsJordanRegion P)
    (g h : Plane ≃ᵃⁱ[ℝ] Plane) {v : Plane} (hv : v ≠ 0)
    (hg2 : ∀ x, g (g x) = x + v)
    (hh : ∀ x, h (h x) = x)
    (hconj : ∀ x, h (g (h x)) = g.symm x)
    (hdisj : Disjoint (interior P) (interior (g '' P)))
    (hunion : h '' (P ∪ g '' P) = P ∪ g '' P)
    (hcontact : (P ∩ g '' P ∩ frontier (P ∪ g '' P)).Finite) :
    g '' P = h '' P :=
  hP.image_eq_of_dihedral_union_symmetry g h hv hg2 hh hconj hdisj hunion
    (hcontact.measure_zero volume)

end Puzzling139335
