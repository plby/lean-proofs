import ErdosProblems.Erdos73.TileSubdivision
import ErdosProblems.Erdos73.MonochromaticRectangle

/-! Monochromatic centres in a prescribed, explicitly bounded tiled wall subdivision. -/

namespace Erdos73
noncomputable section
open scoped Classical
open SimpleGraph Finset

namespace BrickTileArray

variable {c r C R c' r' : ℕ} (A : BrickTileArray c r C R)

def select (f : Fin r' → Fin r) (g : Fin (2 * c') → Fin (2 * c))
    (hf : StrictMono f) (hg : StrictMono g) : BrickTileArray c' r' C R where
  row := A.row ∘ f
  column := A.column ∘ g
  row_strictMono := A.row_strictMono.comp hf
  column_strictMono := A.column_strictMono.comp hg
  row_bound := fun i => A.row_bound (f i)
  column_bound := fun j => A.column_bound (g j)

theorem select_point (f : Fin r' → Fin r) (g : Fin (2 * c') → Fin (2 * c))
    (hf : StrictMono f) (hg : StrictMono g) (z : Fin r' × Fin (2 * c')) :
    (A.select f g hf hg).point z = A.point (f z.1, g z.2) := by
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    rw [point_row, point_row]
    rfl
  · apply Fin.ext
    rw [point_column, point_column]
    rfl

include A in
theorem exists_monochromatic_selection (color : ElementaryWallVertex C R → Bool)
    (hc : 4 * c' ≤ 2 * c) (hr : 2 ^ (2 * c) * r' ≤ r) :
    ∃ B : BrickTileArray c' r' C R, ∃ b : Bool, ∀ z, color (B.point z) = b := by
  obtain ⟨rows, cols, b, hrows, hcols, hcolor⟩ := exists_monochromatic_rectangle
    (fun i j => color (A.point (i, j))) r' (2 * c')
    (by simp only [Fintype.card_fin]; omega) (by simpa only [Fintype.card_fin] using hr)
  obtain ⟨f, _, hfmem, hf⟩ := exists_rank_ordered_selection rows Fin.val
    (fun _ _ _ _ he => Fin.ext he) r' hrows
  obtain ⟨g, _, hgmem, hg⟩ := exists_rank_ordered_selection cols Fin.val
    (fun _ _ _ _ he => Fin.ext he) (2 * c') hcols
  have hf' : StrictMono f := fun _ _ hij => hf hij
  have hg' : StrictMono g := fun _ _ hij => hg hij
  refine ⟨A.select f g hf' hg', b, ?_⟩
  intro z
  rw [A.select_point]
  exact hcolor _ (hfmem z.1) _ (hgmem z.2)

end BrickTileArray

def standardBrickTileArray (c r C R : ℕ) (hc : 16 * c ≤ C) (hr : 12 * r ≤ R) :
    BrickTileArray c r C R where
  row := Fin.val
  column := Fin.val
  row_strictMono := fun _ _ hij => hij
  column_strictMono := fun _ _ hij => hij
  row_bound := fun i => by have hi := i.isLt; omega
  column_bound := fun j => by have hj := j.isLt; omega

theorem exists_monochromatic_tileArray {C R : ℕ}
    (color : ElementaryWallVertex C R → Bool) (c r : ℕ)
    (hc : 32 * c ≤ C) (hr : 12 * (2 ^ (4 * c) * r) ≤ R) :
    ∃ A : BrickTileArray c r C R, ∃ b : Bool, ∀ z, color (A.point z) = b := by
  let B := standardBrickTileArray (2 * c) (2 ^ (4 * c) * r) C R (by omega) hr
  exact B.exists_monochromatic_selection color (by omega)
    (by rw [show 2 * (2 * c) = 4 * c by omega])

end
end Erdos73
