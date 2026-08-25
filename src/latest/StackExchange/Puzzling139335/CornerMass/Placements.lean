import StackExchange.Puzzling139335.CornerMass.Dissection

/-!
# Corner weights for specified actual placements

The weighted corner identity works for any supplied family of congruences
from a Jordan prototype to the four actual pieces. In particular, using
this theorem after a normalization does not change the chosen intrinsic
labels through a new arbitrary choice of placements.
-/

open Set Metric MeasureTheory
open scoped ENNReal BigOperators

namespace Puzzling139335

theorem localMass_toReal_image_affineIsometry (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (P : Set Plane) (v : Plane) (r : ℝ) :
    (localMass (e '' P) (e v) r).toReal = (localMass P v r).toReal :=
  congrArg ENNReal.toReal (localMass_image_affineIsometry e P v r)

namespace SquareDissection

noncomputable section

theorem sum_localMass_toReal_eq_volume (d : SquareDissection) (v : Plane) (r : ℝ) :
    ∑ i, (localMass (d.piece i) v r).toReal =
      (volume (unitSquare ∩ ball v r)).toReal := by
  have hfinite : ∀ i ∈ (Finset.univ : Finset (Fin 4)),
      localMass (d.piece i) v r ≠ ∞ := fun i _ => (localMass_lt_top _ _ _).ne
  rw [← ENNReal.toReal_sum hfinite, d.sum_localMass_eq_volume]

open Classical in
/-- Positive real corner weights for a specified prototype and specified
actual placements. No canonical choice of congruences is made here. -/
theorem exists_positive_corner_weights_of_placements (d : SquareDissection)
    (P : Set Plane) (hP : IsJordanRegion P)
    (e : Fin 4 → Plane ≃ᵃⁱ[ℝ] Plane) (he : ∀ i, e i '' P = d.piece i) :
    ∃ m : Plane → ℝ,
      (∀ v ∈ P, 0 < m v) ∧
      ∀ j k : Fin 4,
        (∑ i, if corner j ∈ d.piece i then m ((e i).symm (corner j)) else 0) =
          ∑ i, if corner k ∈ d.piece i then m ((e i).symm (corner k)) else 0 := by
  classical
  obtain ⟨r, hr, hrad⟩ := d.exists_corner_radius
  have htransport (i j : Fin 4) :
      localMass P ((e i).symm (corner j)) r =
        localMass (d.piece i) (corner j) r := by
    simpa only [he i, (e i).apply_symm_apply] using
      (localMass_image_affineIsometry (e i) P ((e i).symm (corner j)) r).symm
  have hsum (j : Fin 4) :
      (∑ i, if corner j ∈ d.piece i then
        (localMass P ((e i).symm (corner j)) r).toReal else 0) =
          (volume (unitSquare ∩ ball (corner j) r)).toReal := by
    calc
      (∑ i, if corner j ∈ d.piece i then
          (localMass P ((e i).symm (corner j)) r).toReal else 0) =
          ∑ i, (localMass (d.piece i) (corner j) r).toReal := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hji : corner j ∈ d.piece i
        · rw [if_pos hji, htransport i j]
        · simp only [if_neg hji, d.localMass_eq_zero_of_corner_not_mem hrad j i hji,
            ENNReal.toReal_zero]
      _ = (volume (unitSquare ∩ ball (corner j) r)).toReal :=
        d.sum_localMass_toReal_eq_volume (corner j) r
  refine ⟨fun v => (localMass P v r).toReal, ?_, ?_⟩
  · intro v hv
    exact ENNReal.toReal_pos_iff.mpr ⟨localMass_pos hP hv hr, localMass_lt_top _ _ _⟩
  · intro j k
    exact (hsum j).trans ((congrArg ENNReal.toReal
      (volume_square_inter_ball_corner_eq j k r)).trans (hsum k).symm)

end

end SquareDissection

end Puzzling139335
