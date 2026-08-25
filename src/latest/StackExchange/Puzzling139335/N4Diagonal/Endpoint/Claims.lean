import StackExchange.Puzzling139335.N4Diagonal.Endpoint.Claims.Coordinates
import StackExchange.Puzzling139335.N4Diagonal.Endpoint.Claims.Interlacing

/-!
# Mixed endpoints force interlacing of actual pieces

A prototype containing the origin and bottom and left contacts beyond
their respective midpoints cannot have a disjoint congruent copy which
places its bottom endpoint at corner one or three with the prescribed
center preimage. The four actual placement choices force alternating
contacts with the prototype or its anti-diagonal reflection.
-/

open Set

namespace Puzzling139335.N4Diagonal.Endpoint

open ThreeCorners ReflectionSeparation

noncomputable section

/-- All four actual placements of a mixed endpoint contradict boundary
interlacing for the prototype, its anti-diagonal image, and the placed copy. -/
theorem mixed_endpoint_placement_impossible {P : Set Plane} {u v : ℝ}
    (hP : IsJordanRegion P) (hPS : P ⊆ unitSquare)
    (hzero : (0 : Plane) ∈ P) (hB : !₂[u, 0] ∈ P) (hC : !₂[0, v] ∈ P)
    (hu : (1 / 2 : ℝ) < u) (hu1 : u < 1)
    (hv : (1 / 2 : ℝ) < v) (hv1 : v < 1)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (heS : e '' P ⊆ unitSquare)
    (hdisP : Disjoint (interior P) (interior (e '' P)))
    (hdisH : Disjoint (interior (e '' P)) (interior (antiDiagonal '' P)))
    (j : Fin 4) (hj : j = 1 ∨ j = 3) (heB : e !₂[u, 0] = corner j)
    (hecenter : e (!₂[u, 0] + (1 / 2 : ℝ) •
      (ray (Real.pi / 2) + perpRay (Real.pi / 2))) = squareCenter) : False := by
  have heJ : IsJordanRegion (e '' P) := hP.image_homeomorph e.toHomeomorph
  have hHJ : IsJordanRegion (antiDiagonal '' P) :=
    hP.image_homeomorph antiDiagonal.toHomeomorph
  have hHS : antiDiagonal '' P ⊆ unitSquare := by
    rintro x ⟨p, hp, rfl⟩
    exact antiDiagonal_mem_unitSquare.mpr (hPS hp)
  have hPzero : (!₂[0, 0] : Plane) ∈ P := by
    have hz : (!₂[0, 0] : Plane) = 0 := by
      ext i
      fin_cases i <;> rfl
    rwa [hz]
  have hHone : (!₂[1, 1] : Plane) ∈ antiDiagonal '' P := by
    refine ⟨0, hzero, ?_⟩
    ext i
    fin_cases i <;> simp
  have hHB : (!₂[1, 1 - u] : Plane) ∈ antiDiagonal '' P := by
    refine ⟨!₂[u, 0], hB, ?_⟩
    ext i
    fin_cases i <;> simp
  have hHC : (!₂[1 - v, 1] : Plane) ∈ antiDiagonal '' P := by
    refine ⟨!₂[0, v], hC, ?_⟩
    ext i
    fin_cases i <;> simp
  have hezero : e 0 ∈ e '' P := mem_image_of_mem e hzero
  have hecorner : corner j ∈ e '' P := heB ▸ mem_image_of_mem e hB
  rcases hj with rfl | rfl
  · have heone : (!₂[1, 0] : Plane) ∈ e '' P := by
      simpa [corner, Fin.ext_iff] using hecorner
    rcases origin_images_of_endpoint_at_one e u heB hecenter with hright | hbottom
    · have heright : (!₂[1, u] : Plane) ∈ e '' P := hright ▸ hezero
      exact right_side_interlacing_impossible (a := 0) (b := 1 - u) (c := u) (d := 1)
        heJ hHJ heS hHS hdisH
        (by norm_num) (by linarith) (by linarith) hu1 (by norm_num)
        heone heright hHB hHone
    · have hebottom : (!₂[1 - u, 0] : Plane) ∈ e '' P := hbottom ▸ hezero
      exact RectangularHull.bottom_side_interlacing_impossible
        (a := 0) (b := 1 - u) (c := u) (d := 1) hP heJ hPS heS hdisP
        (by norm_num) (by linarith) (by linarith) hu1 (by norm_num)
        hPzero hB hebottom heone
  · have hethree : (!₂[0, 1] : Plane) ∈ e '' P := by
      simpa [corner, Fin.ext_iff] using hecorner
    rcases origin_images_of_endpoint_at_three e u heB hecenter with hleft | htop
    · have heleft : (!₂[0, 1 - u] : Plane) ∈ e '' P := hleft ▸ hezero
      exact left_side_interlacing_impossible (a := 0) (b := 1 - u) (c := v) (d := 1)
        hP heJ hPS heS hdisP
        (by norm_num) (by linarith) (by linarith) hv1 (by norm_num)
        hPzero hC heleft hethree
    · have hetop : (!₂[u, 1] : Plane) ∈ e '' P := htop ▸ hezero
      exact top_side_interlacing_impossible (a := 0) (b := 1 - v) (c := u) (d := 1)
        heJ hHJ heS hHS hdisH
        (by norm_num) (by linarith) (by linarith) hu1 (by norm_num)
        hethree hetop hHC hHone

end

end Puzzling139335.N4Diagonal.Endpoint
