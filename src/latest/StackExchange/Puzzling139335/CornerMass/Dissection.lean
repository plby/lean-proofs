import StackExchange.Puzzling139335.CornerMass.Isometry
import StackExchange.Puzzling139335.CornerMass.Radius
import StackExchange.Puzzling139335.Mass

/-!
# Local mass identities for actual square corners

Restricting the already proved almost-everywhere density identity to a
ball gives exact local mass additivity. For a common corner radius, only
incident pieces contribute. Their masses can then be transported to the
intrinsic corner types in the prototype.
-/

open Set Metric MeasureTheory
open scoped ENNReal BigOperators

namespace Puzzling139335.SquareDissection

noncomputable section

/-- The weighted masses of all pieces inside any ball add to the ordinary
area of the square inside that ball. -/
theorem sum_localMass_eq_volume (d : SquareDissection) (v : Plane) (r : ℝ) :
    ∑ i, localMass (d.piece i) v r = volume (unitSquare ∩ ball v r) := by
  calc
    ∑ i, localMass (d.piece i) v r =
        ∫⁻ x in ball v r, ∑ i, weightedDensity (d.piece i) x ∂volume :=
      (lintegral_finsetSum Finset.univ
        (fun i _ => measurable_weightedDensity (d.piece i))).symm
    _ = ∫⁻ x in ball v r, unitSquare.indicator (fun _ => (1 : ℝ≥0∞)) x ∂volume :=
      lintegral_congr_ae (ae_restrict_of_ae d.density_sum_ae)
    _ = (volume.restrict (ball v r)) unitSquare := by
      rw [lintegral_indicator_const measurableSet_unitSquare, one_mul]
    _ = volume (unitSquare ∩ ball v r) :=
      Measure.restrict_apply measurableSet_unitSquare

theorem localMass_eq_zero_of_corner_not_mem (d : SquareDissection) {r : ℝ}
    (hr : d.IsCornerRadius r) (j i : Fin 4) (hji : corner j ∉ d.piece i) :
    localMass (d.piece i) (corner j) r = 0 :=
  localMass_eq_zero_of_disjoint (d.jordan i).isClosed (hr j i hji)

open scoped Classical in
/-- The sum of local masses of the intrinsic types occurring at one physical corner. -/
def cornerTypeMassSum (d : SquareDissection) (j : Fin 4) (r : ℝ) : ℝ≥0∞ :=
  ∑ i, if corner j ∈ d.piece i then
    localMass (d.piece 0) (d.intrinsicCorner i j) r else 0

theorem cornerTypeMassSum_eq_volume (d : SquareDissection) {r : ℝ}
    (hr : d.IsCornerRadius r) (j : Fin 4) :
    d.cornerTypeMassSum j r = volume (unitSquare ∩ ball (corner j) r) := by
  classical
  calc
    d.cornerTypeMassSum j r = ∑ i, localMass (d.piece i) (corner j) r := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hji : corner j ∈ d.piece i
      · rw [if_pos hji]
        exact d.localMass_intrinsicCorner i j r
      · rw [if_neg hji, d.localMass_eq_zero_of_corner_not_mem hr j i hji]
    _ = volume (unitSquare ∩ ball (corner j) r) :=
      d.sum_localMass_eq_volume (corner j) r

/-- Equal-radius local masses at all four physical square corners agree. -/
theorem cornerTypeMassSum_eq (d : SquareDissection) {r : ℝ}
    (hr : d.IsCornerRadius r) (j k : Fin 4) :
    d.cornerTypeMassSum j r = d.cornerTypeMassSum k r := by
  rw [d.cornerTypeMassSum_eq_volume hr j, d.cornerTypeMassSum_eq_volume hr k]
  exact volume_square_inter_ball_corner_eq j k r

/-- A single positive radius gives the corner mass identities at every
smaller positive radius. -/
theorem exists_cornerMass_radius (d : SquareDissection) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r ≤ ε →
      ∀ j k : Fin 4, d.cornerTypeMassSum j r = d.cornerTypeMassSum k r := by
  obtain ⟨ε, hε, hrad⟩ := d.exists_corner_radius
  exact ⟨ε, hε, fun _ _ hr j k => d.cornerTypeMassSum_eq (hrad.mono hr) j k⟩

theorem localMass_pos_of_mem_usedCornerTypes (d : SquareDissection)
    {v : Plane} (hv : v ∈ d.usedCornerTypes) {r : ℝ} (hr : 0 < r) :
    0 < localMass (d.piece 0) v r :=
  localMass_pos (d.jordan 0) (d.usedCornerTypes_subset hv) hr

end

end Puzzling139335.SquareDissection
