import Wikipedia.NoExoticSixSphere.CircleCylinderCollarBranches

/-!
# A common closed collar window in the original endpoint germs

Continuity of the two explicit clock branches gives one positive width
less than one on which both branches stay in their respective original
constant endpoint neighborhoods. The width is derived from the supplied
regular cylinder; no extra collar assumption is introduced.
-/

noncomputable section

open Set Topology
open scoped Manifold

namespace NoExoticSixSphere.CircleCylinder

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

theorem exists_collar_width : ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
    ∀ s ∈ Icc (-ε) ε, branchClock true s ∈ d.leftTimes ∧
      branchClock false s ∈ d.rightTimes := by
  let U : Set ℝ := (branchClock true) ⁻¹' d.leftTimes ∩
    (branchClock false) ⁻¹' d.rightTimes
  have hU : U ∈ 𝓝 (0 : ℝ) := by
    apply ((d.leftTimes.isOpen.preimage (continuous_branchClock true)).inter
      (d.rightTimes.isOpen.preimage (continuous_branchClock false))).mem_nhds
    constructor
    · change branchClock true 0 ∈ d.leftTimes
      rw [branchClock_zero]
      exact d.left_mem
    · change branchClock false 0 ∈ d.rightTimes
      rw [branchClock_zero]
      exact d.right_mem
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨min (r / 2) (1 / 2), lt_min (half_pos hr) (by norm_num),
    (min_le_right _ _).trans_lt (by norm_num), ?_⟩
  intro s hs
  apply hsub
  rw [Metric.mem_ball, Real.dist_eq, sub_zero]
  exact (abs_le.mpr hs).trans_lt ((min_le_left _ _).trans_lt (half_lt_self hr))

def collarWidth : ℝ := (exists_collar_width d).choose

theorem collarWidth_pos : 0 < collarWidth d := (exists_collar_width d).choose_spec.1

theorem collarWidth_lt_one : collarWidth d < 1 := (exists_collar_width d).choose_spec.2.1

abbrev CollarInterval := Icc (-collarWidth d) (collarWidth d)

theorem left_branchClock_mem (s : CollarInterval d) : branchClock true s.val ∈ d.leftTimes :=
  ((exists_collar_width d).choose_spec.2.2 s.val s.property).1

theorem right_branchClock_mem (s : CollarInterval d) : branchClock false s.val ∈ d.rightTimes :=
  ((exists_collar_width d).choose_spec.2.2 s.val s.property).2

theorem map_left_collarBranch (s : CollarInterval d) (x : Sphere m) :
    map d (collarBranch (collarWidth_lt_one d) true s, x) = d.leftMap x := by
  change d.map (clock (collarBranch (collarWidth_lt_one d) true s), x) = d.leftMap x
  rw [clock_collarBranch]
  exact d.left_eq _ (left_branchClock_mem d s) x

theorem map_right_collarBranch (s : CollarInterval d) (x : Sphere m) :
    map d (collarBranch (collarWidth_lt_one d) false s, x) = d.rightMap x := by
  change d.map (clock (collarBranch (collarWidth_lt_one d) false s), x) = d.rightMap x
  rw [clock_collarBranch]
  exact d.right_eq _ (right_branchClock_mem d s) x

end NoExoticSixSphere.CircleCylinder
