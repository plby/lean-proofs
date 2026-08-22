/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRadialLabelWord
import ErdosProblems.Erdos1165.AnnularSpatialSplice

/-! Geometric membership facts for the two auxiliary spatial annuli. -/

open Set

namespace Erdos1165.AnnularSpatialSpliceMembership

open AnnularRadialLabelWord AnnularSpatialSplice
  LiteralRealAnnulus PotentialEuclideanGeometry
  TerminalProfileBoundarySeparation TerminalSpliceProfileGeometry ThickPoint

noncomputable section

theorem mem_disc_eight_mul_of_radius_upper
    {r0 : ℝ} {y : Point} (hr0 : 0 ≤ r0)
    (hyUpper : euclideanRadius y ≤ 5 * r0) :
    y ∈ disc 0 (8 * r0) := by
  change latticeDistance 0 y ≤ 8 * r0
  rw [RadialHarnackSpecialization.latticeDistance_zero_eq_euclideanRadius]
  exact hyUpper.trans (mul_le_mul_of_nonneg_right (by norm_num) hr0)

theorem not_mem_discBoundary_eight_mul_of_radius_upper
    {r0 : ℝ} {y : Point} (hr0 : 1 ≤ r0)
    (hyUpper : euclideanRadius y ≤ 5 * r0) :
    y ∉ discBoundary 0 (8 * r0) := by
  apply not_mem_discBoundary_of_mem_disc_of_add_one_le (r := 5 * r0)
  · change latticeDistance 0 y ≤ 5 * r0
    rw [RadialHarnackSpecialization.latticeDistance_zero_eq_euclideanRadius]
    exact hyUpper
  · nlinarith

theorem not_mem_disc_inner_of_radius_lower
    {rInner r0 : ℝ} {y : Point} (hr0 : 0 < r0)
    (hrInner : rInner ≤ r0)
    (hyLower : 2 * r0 ≤ euclideanRadius y) :
    y ∉ disc 0 rInner := by
  intro hinner
  have hinnerRadius : euclideanRadius y ≤ rInner := by
    change latticeDistance 0 y ≤ rInner at hinner
    rwa [RadialHarnackSpecialization.latticeDistance_zero_eq_euclideanRadius]
      at hinner
  have hstrict : r0 < 2 * r0 := by nlinarith
  exact (not_le_of_gt hstrict)
    (hyLower.trans (hinnerRadius.trans hrInner))

theorem initial_start_mem_annulus
    {n : ℕ} (hn : 1 ≤ n) (hlarge : 3 ≤ (n : ℝ))
    {x : Point} (hx : x ∈ candidateBox n) :
    -x ∈ literalRealAnnulus (scaleRadius n 1)
      (8 * scaleRadius n 0) ⌈8 * scaleRadius n 0⌉₊ := by
  have hnRadius : (n : ℝ) ≤ scaleRadius n 1 :=
    natCast_le_scaleRadius_one n hn
  have hr1three : (3 : ℝ) ≤ scaleRadius n 1 := hlarge.trans hnRadius
  have hr1le : scaleRadius n 1 ≤ scaleRadius n 0 :=
    scaleRadius_antitone_of_le (by omega) (by omega)
  have hgeom := candidate_neg_euclideanRadius_bounds hx
  have hr0one : (1 : ℝ) ≤ scaleRadius n 0 :=
    (show (1 : ℝ) ≤ 3 by norm_num).trans (hr1three.trans hr1le)
  apply (mem_literalRealAnnulus_iff
    (mul_nonneg (by norm_num) (zero_le_one.trans hr0one)) (Nat.le_ceil _)).mpr
  exact ⟨mem_disc_eight_mul_of_radius_upper (zero_le_one.trans hr0one) hgeom.2,
    not_mem_discBoundary_eight_mul_of_radius_upper hr0one hgeom.2,
    not_mem_disc_inner_of_radius_lower (zero_lt_one.trans_le hr0one)
      hr1le hgeom.1⟩

theorem final_start_mem_annulus
    {n : ℕ} (hn : 2 ≤ n) {z : Point}
    (hz : z ∈ radialBoundary n 0 ⟨0, by omega⟩) :
    z ∈ literalRealAnnulus (scaleRadius n 1)
      (32 * scaleRadius n 0) ⌈32 * scaleRadius n 0⌉₊ := by
  apply mem_literalRealAnnulus_of_mem_intermediate_discBoundary
    (rMiddle := scaleRadius n 0)
  · have hpos : 0 < scaleRadius n 1 := by
      simp only [scaleRadius_of_le (by omega : 1 ≤ n), regularRadius]
      positivity
    have hmono : scaleRadius n 1 ≤ scaleRadius n 0 :=
      scaleRadius_antitone_of_le (by omega) (by omega)
    exact mul_pos (by norm_num) (lt_of_lt_of_le hpos hmono) |>.le
  · exact Nat.le_ceil _
  · simpa using scaleRadius_add_one_le_previous hn (by omega : 0 < 1)
      (by omega : 1 ≤ n + 1)
  · have hmono : scaleRadius n 1 ≤ scaleRadius n 0 :=
      scaleRadius_antitone_of_le (by omega) (by omega)
    have hnat : (n : ℝ) ≤ scaleRadius n 1 :=
      natCast_le_scaleRadius_one n (by omega)
    have htwo : (2 : ℝ) ≤ scaleRadius n 0 := by
      have htwoNat : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      exact htwoNat.trans (hnat.trans hmono)
    linarith
  · exact hz

end

end Erdos1165.AnnularSpatialSpliceMembership
