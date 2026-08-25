import StackExchange.Puzzling139335.ReflectionSeparation
import StackExchange.Puzzling139335.SquareSymmetry.Dissection
import StackExchange.Puzzling139335.SquareSymmetry.Eight
import StackExchange.Puzzling139335.Transform

/-!
# A repeated intrinsic pair cannot occupy the same physical square side

The statement uses an actual congruence between two dissection pieces.
After normalizing the common side, endpoint rigidity leaves the identity
or the reflection in its perpendicular bisector.  The identity contradicts
disjoint interiors; reflection separation contradicts ownership of both
endpoints.  No sector or boundary regularity assumption is needed.
-/

open Set

namespace Puzzling139335.N7

open SquareSymmetry ReflectionSeparation

noncomputable section

/-- Put an ordered counterclockwise square side on the bottom side. -/
def sideFrame (a : Fin 4) : Plane ≃ᵃⁱ[ℝ] Plane :=
  if a = 0 ∨ a = 2 then cornerFlip a else (cornerFlip a).trans diagonal

theorem sideFrame_first (a : Fin 4) : sideFrame a (corner a) = corner 0 := by
  fin_cases a <;> ext k <;> fin_cases k <;>
    norm_num [sideFrame, cornerFlipPoint, corner, Fin.ext_iff, Fin.val_add]

theorem sideFrame_second (a : Fin 4) :
    sideFrame a (corner (a + 1)) = corner 1 := by
  fin_cases a <;> ext k <;> fin_cases k <;>
    norm_num [sideFrame, cornerFlipPoint, corner, Fin.ext_iff, Fin.val_add]

theorem sideFrame_image_square (a : Fin 4) :
    sideFrame a '' unitSquare = unitSquare := by
  unfold sideFrame
  split
  · exact cornerFlip_image_unitSquare a
  · calc
      ((cornerFlip a).trans diagonal) '' unitSquare =
          diagonal '' (cornerFlip a '' unitSquare) := by
        simp only [image_image, AffineIsometryEquiv.coe_trans, Function.comp_def]
      _ = unitSquare := by
        rw [cornerFlip_image_unitSquare, diagonal_image_unitSquare]

/-- A square symmetry preserving the bottom side has just these two
coordinate actions. -/
theorem bottom_side_stabilizer (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hS : e '' unitSquare = unitSquare)
    (hends : e '' {corner 0, corner 1} = {corner 0, corner 1}) :
    (∀ p, e p = p) ∨ (∀ p, e p = vertical p) := by
  have hy (a : Fin 4) (ha : a = 0 ∨ a = 1) : e (corner a) 1 = 0 := by
    have hm : e (corner a) ∈ ({corner 0, corner 1} : Set Plane) := by
      rw [← hends]
      exact mem_image_of_mem e (by rcases ha with rfl | rfl <;> simp)
    rcases hm with hm | hm
    · rw [hm]
      norm_num [corner, Fin.ext_iff]
    · rw [Set.mem_singleton_iff.mp hm]
      norm_num [corner, Fin.ext_iff]
  have hzero := hy 0 (Or.inl rfl)
  have hone := hy 1 (Or.inr rfl)
  obtain ⟨b, hform | hform⟩ := coordinate_forms_of_maps_square_into_square e hS.subset
  · fin_cases b
    · left
      intro p
      rw [hform]
      ext k
      fin_cases k <;> norm_num [cornerFlipPoint, corner, Fin.ext_iff]
    · right
      intro p
      exact hform p
    · simpa [hform, cornerFlipPoint, corner, Fin.ext_iff] using hzero
    · simpa [hform, cornerFlipPoint, corner, Fin.ext_iff] using hzero
  · fin_cases b
    · simpa [hform, cornerFlipPoint, corner, Fin.ext_iff] using hone
    · simpa [hform, cornerFlipPoint, corner, Fin.ext_iff] using hone
    · simpa [hform, cornerFlipPoint, corner, Fin.ext_iff] using hzero
    · simpa [hform, cornerFlipPoint, corner, Fin.ext_iff] using hzero

/-- Actual congruent copies cannot use the same bottom-side pair. -/
theorem no_bottom_side_stabilizing_pair (d : SquareDissection)
    {i j : Fin 4} (hij : i ≠ j) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece i = d.piece j)
    (hends : e '' {corner 0, corner 1} = {corner 0, corner 1})
    (hBL : corner 0 ∈ d.piece i) (hBR : corner 1 ∈ d.piece i) : False := by
  have hS := d.side_congruence_preserves_square i j 0 0 e he hends
  rcases bottom_side_stabilizer e hS hends with hid | hvertical
  · have hpieces : d.piece i = d.piece j := by
      simpa [hid] using he
    obtain ⟨p, hp⟩ := (d.jordan i).interior_nonempty
    exact Set.disjoint_left.mp (d.disjoint_interiors hij) hp (hpieces ▸ hp)
  · have hreflected : vertical '' d.piece i = d.piece j := by
      simpa only [hvertical] using he
    have hleft := vertical_left_of_bottom_left (d.jordan i) hreflected
      (d.disjoint_interiors hij) hBL
    have hbad := hleft hBR
    norm_num [corner, Fin.ext_iff] at hbad

/-- The same physical side is excluded in every orientation of the square. -/
theorem no_side_stabilizing_pair (d : SquareDissection)
    {i j : Fin 4} (hij : i ≠ j) (a : Fin 4) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece i = d.piece j)
    (hends : e '' {corner a, corner (a + 1)} = {corner a, corner (a + 1)})
    (ha : corner a ∈ d.piece i) (ha' : corner (a + 1) ∈ d.piece i) : False := by
  let f := sideFrame a
  let D := d.map f (sideFrame_image_square a)
  let g := (f.symm.trans e).trans f
  have hfg (p : Plane) : g (f p) = f (e p) := by
    simp [g]
  have hpieces : g '' D.piece i = D.piece j := by
    change g '' (f '' d.piece i) = f '' d.piece j
    rw [image_image, ← he, image_image]
    congr 1
    funext p
    exact hfg p
  have hfends : f '' {corner a, corner (a + 1)} = {corner 0, corner 1} := by
    rw [image_pair, sideFrame_first, sideFrame_second]
  have hgends : g '' {corner 0, corner 1} = {corner 0, corner 1} := by
    calc
      g '' {corner 0, corner 1} = g '' (f '' {corner a, corner (a + 1)}) := by
        rw [hfends]
      _ = f '' (e '' {corner a, corner (a + 1)}) := by
        rw [image_image, image_image]
        congr 1
        funext p
        exact hfg p
      _ = {corner 0, corner 1} := by rw [hends, hfends]
  apply no_bottom_side_stabilizing_pair D hij g hpieces hgends
  · change corner 0 ∈ f '' d.piece i
    exact ⟨corner a, ha, sideFrame_first a⟩
  · change corner 1 ∈ f '' d.piece i
    exact ⟨corner (a + 1), ha', sideFrame_second a⟩

end

end Puzzling139335.N7
