import StackExchange.Puzzling139335.RectangularHull.Congruence
import StackExchange.Puzzling139335.Transform

/-!
# Transport of common rectangular frames for a square dissection

The actual dissection is transformed by `SquareDissection.map`, whose
definition preserves the Jordan, congruence, coverage, and disjointness
conditions. Its protected-center equivalence is `map_hasProtectedCenter`.
This file transports the associated rectangular hulls and their common
ordered edge lengths, and also supports relabeling the four pieces.
-/

open Set

namespace Puzzling139335.RectangularHull

/-- Apply a square symmetry to all actual pieces and all of their frames. -/
noncomputable def CommonFrames.mapSquareIsometry {d : SquareDissection}
    (F : CommonFrames d) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' unitSquare = unitSquare) : CommonFrames (d.map e he) where
  frame i := (F.frame i).map e
  hull_eq i := (F.frame i).image_convexHull_eq_map_carrier e (F.hull_eq i)
  first_length_eq i j := by
    simpa only [Frame.map_first, LinearIsometryEquiv.norm_map] using F.first_length_eq i j
  second_length_eq i j := by
    simpa only [Frame.map_second, LinearIsometryEquiv.norm_map] using F.second_length_eq i j

@[simp] theorem CommonFrames.mapSquareIsometry_frame {d : SquareDissection}
    (F : CommonFrames d) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' unitSquare = unitSquare) (i : Fin 4) :
    (F.mapSquareIsometry e he).frame i = (F.frame i).map e := rfl

@[simp] theorem CommonFrames.mapSquareIsometry_first_norm {d : SquareDissection}
    (F : CommonFrames d) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' unitSquare = unitSquare) (i : Fin 4) :
    ‖((F.mapSquareIsometry e he).frame i).first‖ = ‖(F.frame i).first‖ := by
  simp only [mapSquareIsometry_frame, Frame.map_first, LinearIsometryEquiv.norm_map]

@[simp] theorem CommonFrames.mapSquareIsometry_second_norm {d : SquareDissection}
    (F : CommonFrames d) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' unitSquare = unitSquare) (i : Fin 4) :
    ‖((F.mapSquareIsometry e he).frame i).second‖ = ‖(F.frame i).second‖ := by
  simp only [mapSquareIsometry_frame, Frame.map_second, LinearIsometryEquiv.norm_map]

theorem CommonFrames.mapSquareIsometry_carrier {d : SquareDissection}
    (F : CommonFrames d) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' unitSquare = unitSquare) (i : Fin 4) :
    ((F.mapSquareIsometry e he).frame i).carrier = e '' (F.frame i).carrier :=
  (F.frame i).map_carrier e

theorem CommonFrames.mapSquareIsometry_vertices {d : SquareDissection}
    (F : CommonFrames d) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' unitSquare = unitSquare) (i : Fin 4) :
    ((F.mapSquareIsometry e he).frame i).vertices = e '' (F.frame i).vertices :=
  (F.frame i).map_vertices e

@[simp] theorem CommonFrames.mapSquareIsometry_center {d : SquareDissection}
    (F : CommonFrames d) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' unitSquare = unitSquare) (i : Fin 4) :
    ((F.mapSquareIsometry e he).frame i).center = e (F.frame i).center :=
  (F.frame i).map_center e

/-- Relabel the frames along with the actual dissection pieces. -/
def CommonFrames.reindex {d : SquareDissection} (F : CommonFrames d)
    (σ : Equiv.Perm (Fin 4)) : CommonFrames (d.reindex σ) where
  frame i := F.frame (σ i)
  hull_eq i := F.hull_eq (σ i)
  first_length_eq i j := F.first_length_eq (σ i) (σ j)
  second_length_eq i j := F.second_length_eq (σ i) (σ j)

@[simp] theorem CommonFrames.reindex_frame {d : SquareDissection}
    (F : CommonFrames d) (σ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    (F.reindex σ).frame i = F.frame (σ i) := rfl

end Puzzling139335.RectangularHull
