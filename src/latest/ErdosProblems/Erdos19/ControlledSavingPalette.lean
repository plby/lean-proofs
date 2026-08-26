import ErdosProblems.Erdos19.LargeCoverageColors
import ErdosProblems.Erdos19.MediumPaletteControl
import ErdosProblems.Erdos19.ReservedPaletteEmbedding
import ErdosProblems.Erdos19.SavingFloorParameters

/-! # Lifting the saved coloring and isolating its special colors -/

namespace Erdos19.SetHypergraph

open Finset

attribute [local instance] Classical.propDecidable

theorem exists_lifted_controlled_saving_palette (n w B m R : ℕ)
    (hw : 0 < w) (hB : 0 < B) (hnw : w ≤ n) (hnB : B ≤ n)
    (H : SetHypergraph (Fin n)) (hlinear : H.IsLinear)
    (color : H.EdgeColoring (Fin (n - n / B)))
    (palette : Finset (Fin (n - n / B))) (hcard : palette.card = n / B)
    (hcontrol : H.HasControlledMediumPalette color palette R (16 * (n / (16 * w))) (n / w))
    (hm : n - n / B ≤ m) :
    ∃ c : H.EdgeColoring (Fin m), ∃ S : Finset (Fin m), S.Nonempty ∧
      S.card ≤ n / B + 4 * w ^ 2 ∧ H.IsCoverBoundedColoring c (n / w) ∧
      (∀ a, a ∉ S → (H.coveredVertices {e | c e = a}).ncard ≤ n / w) ∧
      ∀ e : H, c e ∉ S → R ≤ e.1.ncard := by
  classical
  have h16 : 16 * (n / (16 * w)) ≤ n / w :=
    mul_floor_le_div_of_den_le n (16 * w) 16 w hw le_rfl
  have hbounded : H.IsCoverBoundedColoring color (n / w) := by
    intro a
    by_cases ha : a ∈ palette
    · exact Or.inr (hcontrol.2.1 a ha)
    · rcases hcontrol.2.2 a ha with hsingle | hsmall
      · exact Or.inl hsingle
      · exact Or.inr (hsmall.trans h16)
  let j : Fin (n - n / B) ↪ Fin m :=
    ⟨Fin.castLE hm, fun _ _ h ↦ Fin.ext (congrArg (fun z : Fin m ↦ z.val) h)⟩
  let c := color.mapEmbedding j
  have hbounded' : H.IsCoverBoundedColoring c (n / w) := hbounded.mapEmbedding color _ j
  let P := palette.map j
  let S := P ∪ H.largeCoverageColors c (n / w)
  have hpos : 0 < palette.card := by
    rw [hcard]
    exact (Nat.le_div_iff_mul_le hB).mpr (by simpa using hnB)
  have hS : S.Nonempty := by
    obtain ⟨a, ha⟩ := card_pos.mp hpos
    exact ⟨j a, mem_union_left _ (mem_map.mpr ⟨a, ha, rfl⟩)⟩
  have hsize : S.card ≤ n / B + 4 * w ^ 2 := by
    have hsum := card_union_le P (H.largeCoverageColors c (n / w))
    have hheavy := H.largeCoverageColors_card_le_constant n w hw hnw hlinear c hbounded'
    have hP : P.card = n / B := by simpa only [P, card_map] using hcard
    dsimp only [S]
    omega
  refine ⟨c, S, hS, hsize, hbounded', ?_, ?_⟩
  · intro a ha
    by_contra h
    exact ha (mem_union_right _ (mem_filter.mpr ⟨mem_univ _, by omega⟩))
  · intro e he
    by_contra h
    have hmem := hcontrol.1 e (Nat.lt_of_not_ge h)
    apply he
    exact mem_union_left _ (mem_map.mpr ⟨color e, hmem, rfl⟩)

#print axioms exists_lifted_controlled_saving_palette

end Erdos19.SetHypergraph
