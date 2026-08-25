import StackExchange.Puzzling139335.N6.TwoDouble.RemainingOwners
import StackExchange.Puzzling139335.N6.TwoDouble.ThreeCornered
import StackExchange.Puzzling139335.GeometricReduction
import StackExchange.Puzzling139335.N4Dispatch.FiniteRouting

/-!
# Labeling the two remaining owners in the horizontal case

The two right corners have actual owners outside the horizontal pair. If
one remaining piece owned both, the proved three-cornered obstruction
would apply. Thus they have distinct owners, and at most the transposition
of pieces two and three is needed to label them.
-/

open Set

namespace Puzzling139335.N6.TwoDouble

noncomputable section

/-- The genuine remaining owners can be labeled bottom-right and top-right.
All retained geometric properties concern the constructed, reindexed
dissection. Its intrinsic type bound is derived again from its protected
center, with no invariance claim for chosen prototype placements. -/
theorem exists_horizontal_ordered_owners (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    (hU : d.usedCornerTypes.card ≤ 3)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hcount : d.cornerTileCount 0 = 1)
    (hH : ReflectionSeparation.horizontal '' d.piece 0 = d.piece 1) :
    ∃ D : SquareDissection, D.HasProtectedCenter ∧ D.cornerIncidenceCount = 6 ∧
      D.usedCornerTypes.card ≤ 3 ∧ corner 0 ∈ D.piece 0 ∧ corner 1 ∈ D.piece 0 ∧
      D.cornerTileCount 0 = 1 ∧
      ReflectionSeparation.horizontal '' D.piece 0 = D.piece 1 ∧
      corner 1 ∈ D.piece 2 ∧ corner 2 ∈ D.piece 3 := by
  let σ : Equiv.Perm (Fin 4) := Equiv.swap 2 3
  have hσ0 : σ 0 = 0 := by simp [σ, Equiv.swap_apply_def]
  have hσ1 : σ 1 = 1 := by simp [σ, Equiv.swap_apply_def]
  have hσ2 : σ 2 = 3 := by simp [σ]
  have hσ3 : σ 3 = 2 := by simp [σ]
  let D := d.reindex σ
  have hDpiece (k : Fin 4) : D.piece k = d.piece (σ k) := rfl
  have hD0 : D.piece 0 = d.piece 0 := by rw [hDpiece, hσ0]
  have hD1 : D.piece 1 = d.piece 1 := by rw [hDpiece, hσ1]
  have hD2 : D.piece 2 = d.piece 3 := by rw [hDpiece, hσ2]
  have hD3 : D.piece 3 = d.piece 2 := by rw [hDpiece, hσ3]
  have hcD : D.HasProtectedCenter := (d.reindex_hasProtectedCenter σ).mpr hc
  have hND : D.cornerIncidenceCount = 6 := by
    change (d.reindex σ).cornerIncidenceCount = 6
    rw [SquareDissection.reindex_cornerIncidenceCount, hN]
  have hUD : D.usedCornerTypes.card ≤ 3 := D.usedCornerTypes_card_le_three hcD
  have hBLD : corner 0 ∈ D.piece 0 := by rw [hD0]; exact hBL
  have hBRD : corner 1 ∈ D.piece 0 := by rw [hD0]; exact hBR
  have hcountD : D.cornerTileCount 0 = 1 := by
    change (d.reindex σ).cornerTileCount 0 = 1
    rw [SquareDissection.reindex_cornerTileCount, hcount]
  have hHD : ReflectionSeparation.horizontal '' D.piece 0 = D.piece 1 := by
    rw [hD0, hD1]
    exact hH
  obtain ⟨hbottom, htop⟩ := horizontal_remaining_owners d hc hN hBL hBR hcount hH
  rcases hbottom with hBR2 | hBR3
  · rcases htop with hTR2 | hTR3
    · exact (normalized_three_cornered_impossible d hc hN hU hBL hBR hH hBR2 hTR2).elim
    · exact ⟨d, hc, hN, d.usedCornerTypes_card_le_three hc, hBL, hBR, hcount,
        hH, hBR2, hTR3⟩
  · have hBR2D : corner 1 ∈ D.piece 2 := by rw [hD2]; exact hBR3
    rcases htop with hTR2 | hTR3
    · have hTR3D : corner 2 ∈ D.piece 3 := by rw [hD3]; exact hTR2
      exact ⟨D, hcD, hND, hUD, hBLD, hBRD, hcountD, hHD, hBR2D, hTR3D⟩
    · have hTR2D : corner 2 ∈ D.piece 2 := by rw [hD2]; exact hTR3
      exact (normalized_three_cornered_impossible D hcD hND hUD hBLD hBRD hHD
        hBR2D hTR2D).elim

/-- The same actual normalization with the original type bound discharged. -/
theorem exists_horizontal_ordered_owners_of_protected (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hcount : d.cornerTileCount 0 = 1)
    (hH : ReflectionSeparation.horizontal '' d.piece 0 = d.piece 1) :
    ∃ D : SquareDissection, D.HasProtectedCenter ∧ D.cornerIncidenceCount = 6 ∧
      D.usedCornerTypes.card ≤ 3 ∧ corner 0 ∈ D.piece 0 ∧ corner 1 ∈ D.piece 0 ∧
      D.cornerTileCount 0 = 1 ∧
      ReflectionSeparation.horizontal '' D.piece 0 = D.piece 1 ∧
      corner 1 ∈ D.piece 2 ∧ corner 2 ∈ D.piece 3 :=
  exists_horizontal_ordered_owners d hc hN (d.usedCornerTypes_card_le_three hc)
    hBL hBR hcount hH

end

end Puzzling139335.N6.TwoDouble
