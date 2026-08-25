import StackExchange.Puzzling139335.Basic
import StackExchange.Puzzling139335.JordanTransport
import StackExchange.Puzzling139335.SquareSymmetry.Basic

/-!
# Changing the square's orientation

Applying one actual symmetry of the square to all four pieces preserves
every dissection hypothesis and the protected-center property.
-/

open Set

namespace Puzzling139335.SquareDissection

noncomputable section

/-- Apply a square-preserving Euclidean isometry to the whole dissection. -/
def map (d : SquareDissection) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' unitSquare = unitSquare) : SquareDissection where
  piece i := e '' d.piece i
  jordan i := (d.jordan i).image_homeomorph e.toHomeomorph
  congruent i j := by
    obtain ⟨g, hg⟩ := d.congruent i j
    refine ⟨(e.symm.trans g).trans e, ?_⟩
    calc
      (e.symm.trans g).trans e '' (e '' d.piece i) = e '' (g '' d.piece i) := by
        simp [Set.image_image, Function.comp_def]
      _ = e '' d.piece j := by rw [hg]
  covers := by
    rw [← image_iUnion, d.covers, he]
  disjoint_interiors := by
    intro i j hij
    rw [interior_image_affineIsometry, interior_image_affineIsometry]
    exact (Set.disjoint_image_iff e.injective).mpr (d.disjoint_interiors hij)

@[simp] theorem map_piece (d : SquareDissection) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' unitSquare = unitSquare) (i : Fin 4) :
    (d.map e he).piece i = e '' d.piece i := rfl

@[simp] theorem map_hasProtectedCenter (d : SquareDissection)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' unitSquare = unitSquare) :
    (d.map e he).HasProtectedCenter ↔ d.HasProtectedCenter := by
  have hfix := SquareSymmetry.center_fixed_of_preserves_square e he
  change (∃ i, squareCenter ∈ interior (e '' d.piece i)) ↔
    ∃ i, squareCenter ∈ interior (d.piece i)
  apply exists_congr
  intro i
  simpa only [hfix] using
    (mem_interior_image_affineIsometry e (P := d.piece i) (p := squareCenter))

end

end Puzzling139335.SquareDissection
