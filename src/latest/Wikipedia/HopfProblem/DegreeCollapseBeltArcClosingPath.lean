import Wikipedia.HopfProblem.DegreeCollapseNativeBeltArc
import Wikipedia.HopfProblem.DegreeCollapseMinimumLevelPaths
import Wikipedia.HopfProblem.DegreeCollapseMinimumBranchPlacement

/-!
# A return path closing the local belt-crossing arc without further belt crossings

Both sides of the short native belt arc reach the same minimum. The proved
minimum-level path construction joins its endpoints inside that basin. No
point of the return path lies on the original belt, since belt points tend
to the distinct one-handle critical point. This constructs the two pieces
needed for a loop; a smooth embedded circle is not yet asserted.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

open Classical in
theorem AdaptedSurgeryWindows.exists_belt_arc_closing_path
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : criticalPoints E f) (hp : nativeMorseIndex E f p = 0)
    (hq : nativeMorseIndex E f q = 1)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (hbranches : ∀ w : sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
      Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere w).val) atTop (𝓝 p.val))
    {d : ℕ} (hlow : ∀ r : criticalPoints E f, f r ≤ S.toSurgeryWindows.upper q →
      nativeMorseIndex E f r ≤ d) (hdim : 1 + d < Module.finrank ℝ E) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      (∀ s : ℝ, 0 < |s| → |s| ≤ r →
        Tendsto (fun t => S.flow t (nativeBeltArc S q u v s)) atTop (𝓝 p.val)) ∧
      JoinedIn {z : M | f z = S.toSurgeryWindows.upper q ∧
        Tendsto (fun t => S.flow t z) atTop (𝓝 p.val) ∧
        z ∉ range (Subtype.val ∘ (S.data q).surgery.beltSphere)}
        (nativeBeltArc S q u v r) (nativeBeltArc S q u v (-r)) := by
  obtain ⟨ε, hε, hε1, hbasin⟩ :=
    S.exists_two_sided_belt_branch_in_minimum_basin hf p q hp u v hbranches
  let r : ℝ := ε / 2
  have hr : 0 < r := half_pos hε
  have hrε : r < ε := half_lt_self hε
  have hr1 : r < 1 := hrε.trans_le hε1
  have hall (s : ℝ) (hs : 0 < |s|) (hsr : |s| ≤ r) :
      Tendsto (fun t => S.flow t (nativeBeltArc S q u v s)) atTop (𝓝 p.val) :=
    hbasin s hs (hsr.trans_lt hrε)
  have hpa : f p < S.toSurgeryWindows.upper q :=
    (S.forward_limit_below_regular_level hf (S.data q).lower_regular
      ((S.data q).surgery.attachingSphere u) (hbranches u)).trans
        ((S.toSurgeryWindows.lower_lt_value q).trans (S.toSurgeryWindows.value_lt_upper q))
  have hplus : |r| = r := abs_of_pos hr
  have hminus : |-r| = r := by rw [abs_neg, hplus]
  have hpath := S.joinedIn_level_minimum_basin hf p hp hpa (S.data q).upper_regular hlow hdim
    (nativeBeltArc_height S q u v (by rw [hplus]; exact hr1.le))
    (nativeBeltArc_height S q u v (by rw [hminus]; exact hr1.le))
    (hall r (hplus.symm ▸ hr) (hplus.le))
    (hall (-r) (hminus.symm ▸ hr) (hminus.le))
  have hpq : p ≠ q := by
    intro heq
    have hh := hp
    rw [heq, hq] at hh
    exact Nat.one_ne_zero hh
  refine ⟨r, hr, hr1, hall, hpath.mono ?_⟩
  intro z hz
  refine ⟨hz.1, hz.2, ?_⟩
  rintro ⟨w, hw⟩
  have hqz := (S.belt_basin_iff hf q ((S.data q).surgery.beltSphere w)).mpr ⟨w, rfl⟩
  have hvalue : ((S.data q).surgery.beltSphere w).val = z := hw
  rw [hvalue] at hqz
  exact hpq (Subtype.ext (tendsto_nhds_unique hz.2 hqz))

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
