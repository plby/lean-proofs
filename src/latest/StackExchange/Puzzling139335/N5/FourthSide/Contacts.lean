import StackExchange.Puzzling139335.N5.FaceNormals
import StackExchange.Puzzling139335.N5.FourthSide.NormalPairs
import StackExchange.Puzzling139335.PlaneIsometries.Matrix

/-!
# Two actual side contacts force a source corner to the top right

Two distinct points on a square side give a genuine two-point supporting
level in the source. The classification of the two perpendicular unit rows
then gives a common actual maximizer at the source point `B` or `C`.
No polygonality or interval structure is assumed for either contact set.
-/

open Set

namespace Puzzling139335.N5.FourthSide

open PlaneIsometries

theorem affine_coordinate (g : Plane ≃ᵃⁱ[ℝ] Plane) (p : Plane) (i : Fin 2) :
    g p i = linearMatrix g i 0 * p 0 + linearMatrix g i 1 * p 1 + g 0 i := by
  rw [affine_apply_eq_matrix_coordinates g p]
  fin_cases i <;> rfl

theorem coordinate_le_one {p : Plane} (hp : p ∈ unitSquare) (i : Fin 2) :
    p i ≤ 1 := by
  fin_cases i
  · exact hp.1.2
  · exact hp.2.2

/-- Every nontrivial upper-side contact set pulls back to two distinct
source points attaining the same supporting level. -/
theorem hasTwoPointSupport_of_upper_contact {P : Set Plane}
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (hfit : g '' P ⊆ unitSquare) {i : Fin 2}
    (hcontact : (g '' P ∩ {p : Plane | p i = 1}).Nontrivial) :
    HasTwoPointSupport P (linearMatrix g i 0) (linearMatrix g i 1) := by
  obtain ⟨X, ⟨⟨x, hx, hgx⟩, hX⟩, Y, ⟨⟨y, hy, hgy⟩, hY⟩, hXY⟩ := hcontact
  change X i = 1 at hX
  change Y i = 1 at hY
  have hxy : x ≠ y := by
    intro heq
    exact hXY (hgx.symm.trans ((congrArg g heq).trans hgy))
  have hxlevel : g x i = 1 := by simpa only [hgx] using hX
  have hylevel : g y i = 1 := by simpa only [hgy] using hY
  refine ⟨1 - g 0 i, x, y, hx, hy, hxy, ?_, ?_, ?_⟩
  · intro p hp
    have hb := coordinate_le_one (hfit (mem_image_of_mem g hp)) i
    rw [affine_coordinate] at hb
    linarith
  · rw [affine_coordinate] at hxlevel
    linarith
  · rw [affine_coordinate] at hylevel
    linarith

/-- If an actual source point maximizes the row normal, it maps onto the
corresponding square side whenever that side has any contact at all. -/
theorem coordinate_eq_one_of_maximizer {P : Set Plane}
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (hfit : g '' P ⊆ unitSquare)
    {i : Fin 2} {p : Plane} (hp : p ∈ P)
    (hcontact : (g '' P ∩ {q : Plane | q i = 1}).Nonempty)
    (hmax : ∀ q ∈ P,
      linearMatrix g i 0 * q 0 + linearMatrix g i 1 * q 1 ≤
      linearMatrix g i 0 * p 0 + linearMatrix g i 1 * p 1) :
    g p i = 1 := by
  obtain ⟨q, ⟨⟨x, hx, hgx⟩, hqi⟩⟩ := hcontact
  change q i = 1 at hqi
  have hxi : g x i = 1 := by simpa only [hgx] using hqi
  have hb := coordinate_le_one (hfit (mem_image_of_mem g hp)) i
  have hm := hmax x hx
  have hxp := affine_coordinate g x i
  have hpp := affine_coordinate g p i
  linarith

theorem image_eq_top_right_of_row_maximizers {P : Set Plane}
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (hfit : g '' P ⊆ unitSquare) {p : Plane}
    (hp : p ∈ P)
    (hR : (g '' P ∩ {q : Plane | q 0 = 1}).Nonempty)
    (hT : (g '' P ∩ {q : Plane | q 1 = 1}).Nonempty)
    (hmaxR : ∀ q ∈ P,
      linearMatrix g 0 0 * q 0 + linearMatrix g 0 1 * q 1 ≤
      linearMatrix g 0 0 * p 0 + linearMatrix g 0 1 * p 1)
    (hmaxT : ∀ q ∈ P,
      linearMatrix g 1 0 * q 0 + linearMatrix g 1 1 * q 1 ≤
      linearMatrix g 1 0 * p 0 + linearMatrix g 1 1 * p 1) :
    g p = corner 2 := by
  apply plane_ext
  · simpa [corner, Fin.ext_iff] using
      coordinate_eq_one_of_maximizer g hfit hp hR hmaxR
  · simpa [corner, Fin.ext_iff] using
      coordinate_eq_one_of_maximizer g hfit hp hT hmaxT

/-- The two perpendicular unit normals of actual right/top contacts put
either `B` or `C` at their common square corner. -/
theorem two_side_contacts_place_B_or_C {P : Set Plane} {C : Plane} {c s : ℝ}
    (hP : P ⊆ unitSquare) (hbelow : P ⊆ {p | p 1 ≤ p 0})
    (hA : corner 0 ∈ P) (hB : corner 1 ∈ P) (hC : C ∈ P)
    (hcs : c ^ 2 + s ^ 2 = 1) (hs : 0 < s) (hsc : s < c)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' P ⊆ unitSquare)
    (hform : CornerFrameFormula e C c s)
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (hfit : g '' P ⊆ unitSquare)
    (hR : (g '' P ∩ {p : Plane | p 0 = 1}).Nontrivial)
    (hT : (g '' P ∩ {p : Plane | p 1 = 1}).Nontrivial) :
    g (corner 1) = corner 2 ∨ g C = corner 2 := by
  have huR : linearMatrix g 0 0 ^ 2 + linearMatrix g 0 1 ^ 2 = 1 := by
    simpa [pow_two] using linearMatrix_row_dot g 0 0
  have huT : linearMatrix g 1 0 ^ 2 + linearMatrix g 1 1 ^ 2 = 1 := by
    simpa [pow_two] using linearMatrix_row_dot g 1 1
  have horth : linearMatrix g 0 0 * linearMatrix g 1 0 +
      linearMatrix g 0 1 * linearMatrix g 1 1 = 0 := by
    simpa using linearMatrix_row_dot g 0 1
  have hallowR := allowedNormal_of_corner_frame hP hbelow hA hB hC hcs hs hsc
    e he hform huR (hasTwoPointSupport_of_upper_contact g hfit hR)
  have hallowT := allowedNormal_of_corner_frame hP hbelow hA hB hC hcs hs hsc
    e he hform huT (hasTwoPointSupport_of_upper_contact g hfit hT)
  have hcorner := corner_support_inequalities_of_frame e he hform
  have hBRight : ∀ p ∈ P, (1 : ℝ) * p 0 + 0 * p 1 ≤
      1 * corner 1 0 + 0 * corner 1 1 := by
    intro p hp
    simpa [corner, Fin.ext_iff] using (hP hp).1.2
  have hBBottom : ∀ p ∈ P, (0 : ℝ) * p 0 + (-1) * p 1 ≤
      0 * corner 1 0 + (-1) * corner 1 1 := by
    intro p hp
    simpa [corner, Fin.ext_iff] using neg_nonpos.mpr (hP hp).2.1
  have hCe : ∀ p ∈ P, c * p 0 + s * p 1 ≤ c * C 0 + s * C 1 := by
    intro p hp
    nlinarith only [(hcorner p hp).1]
  have hCf : ∀ p ∈ P, (-s) * p 0 + c * p 1 ≤ (-s) * C 0 + c * C 1 := by
    intro p hp
    nlinarith only [(hcorner p hp).2]
  rcases orthogonal_allowed_classification (hs.trans hsc) hs hcs
      hallowR hallowT huR huT horth with
    ⟨ha, hb, hd, hf⟩ | ⟨ha, hb, hd, hf⟩ |
    ⟨ha, hb, hd, hf⟩ | ⟨ha, hb, hd, hf⟩
  · left
    exact image_eq_top_right_of_row_maximizers g hfit hB hR.nonempty hT.nonempty
      (by simpa only [ha, hb] using hBRight)
      (by simpa only [hd, hf] using hBBottom)
  · left
    exact image_eq_top_right_of_row_maximizers g hfit hB hR.nonempty hT.nonempty
      (by simpa only [ha, hb] using hBBottom)
      (by simpa only [hd, hf] using hBRight)
  · right
    exact image_eq_top_right_of_row_maximizers g hfit hC hR.nonempty hT.nonempty
      (by simpa only [ha, hb] using hCe)
      (by simpa only [hd, hf] using hCf)
  · right
    exact image_eq_top_right_of_row_maximizers g hfit hC hR.nonempty hT.nonempty
      (by simpa only [ha, hb] using hCf)
      (by simpa only [hd, hf] using hCe)

end Puzzling139335.N5.FourthSide
