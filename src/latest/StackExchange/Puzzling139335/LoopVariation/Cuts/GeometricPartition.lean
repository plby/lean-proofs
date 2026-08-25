import StackExchange.Puzzling139335.LoopVariation.Cuts
import StackExchange.Puzzling139335.LoopVariation.Geometric.Arc
import StackExchange.Puzzling139335.LoopVariation.Geometric.Loop
import Wikipedia.SchoenfliesTheorem.TwoArcs

/-!
# Finite Jordan partitions in terms of geometric arc sets

Strictly ordered cuts of a Jordan-loop parametrization define genuine arcs.
Their intrinsic variations can therefore replace the interval variations in
the finite-cut estimate.  The first interval stops before the loop closes; every
other interval starts after zero, so even the last interval is injective.
-/

open Set unitInterval

namespace Puzzling139335.LoopVariation

open ArcVariation Schoenflies

noncomputable section

/-- Every component of a strict partition of a Jordan loop into at least two
intervals is a genuine arc, parametrized continuously and injectively by the
corresponding restriction of the original loop. -/
theorem loop_partition_piece_parametrization
    {f : ℝ → Plane} {t : ℕ → ℝ} {m i : ℕ}
    (hf : IsLoop f) (hm : 2 ≤ m) (ht : StrictMonoOn t (Icc 0 m))
    (ht0 : t 0 = 0) (htm : t m = 1) (hi : i < m) :
    IsArc (f '' Icc (t i) (t (i + 1))) ∧
      ContinuousOn f (Icc (t i) (t (i + 1))) ∧
      InjOn f (Icc (t i) (t (i + 1))) := by
  have hi_mem : i ∈ Icc 0 m := ⟨Nat.zero_le i, hi.le⟩
  have hisucc_mem : i + 1 ∈ Icc 0 m := ⟨by omega, by omega⟩
  have hzero_mem : 0 ∈ Icc 0 m := ⟨le_rfl, Nat.zero_le m⟩
  have hm_mem : m ∈ Icc 0 m := ⟨Nat.zero_le m, le_rfl⟩
  have hpoint_mem (j : ℕ) (hj : j ∈ Icc 0 m) : t j ∈ I := by
    constructor
    · rw [← ht0]
      exact ht.monotoneOn hzero_mem hj hj.1
    · rw [← htm]
      exact ht.monotoneOn hj hm_mem hj.2
  have hti : t i ∈ I := hpoint_mem i hi_mem
  have htis : t (i + 1) ∈ I := hpoint_mem (i + 1) hisucc_mem
  have hstep : t i < t (i + 1) := ht hi_mem hisucc_mem (by omega)
  have hfi : InjOn f (Icc (t i) (t (i + 1))) := by
    by_cases hi0 : i = 0
    · have hright : t (i + 1) < 1 := by
        rw [← htm]
        exact ht hisucc_mem hm_mem (by omega)
      exact hf.injective_on_middle hti htis hright.ne
    · have hleft : 0 < t i := by
        rw [← ht0]
        exact ht hzero_mem hi_mem (by omega)
      exact (hf.injective_on_back hti hleft).mono
        (Icc_subset_Icc le_rfl htis.2)
  have hfu : InjOn f (uIcc (t i) (t (i + 1))) := by
    simpa only [uIcc_of_le hstep.le] using hfi
  have hA : IsArc (f '' Icc (t i) (t (i + 1))) := by
    simpa only [uIcc_of_le hstep.le] using
      isArc_subarc hf.continuousOn hfu hti htis hstep.ne
  exact ⟨hA, hf.continuousOn.mono (Icc_subset_Icc hti.1 htis.2), hfi⟩

/-- A Jordan curve cut into `m ≥ 2` arcs has intrinsic cyclic variation between
the sum of the intrinsic arc variations and that sum plus `m * ε`. -/
theorem loopVariation_partition_bounds
    {C : Set Plane} {f : ℝ → Plane} {t : ℕ → ℝ} {m : ℕ} {ε : ℝ}
    (hf : IsLoop f) (himage : f '' I = C) (hm : 2 ≤ m)
    (ht : StrictMonoOn t (Icc 0 m)) (ht0 : t 0 = 0) (htm : t m = 1)
    (hε : 0 < ε) :
    (∑ i ∈ Finset.range m, arcVariation ε (f '' Icc (t i) (t (i + 1)))) ≤
        loopVariation ε C ∧
      loopVariation ε C ≤
        (∑ i ∈ Finset.range m, arcVariation ε (f '' Icc (t i) (t (i + 1)))) +
          (m : ℝ) * ε := by
  have hsum :
      (∑ i ∈ Finset.range m, arcVariation ε (f '' Icc (t i) (t (i + 1)))) =
        cutSum ε f t m := by
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨hA, hfc, hfi⟩ := loop_partition_piece_parametrization
      hf hm ht ht0 htm (Finset.mem_range.mp hi)
    exact arcVariation_eq_of_parametrization ε hA hfc hfi rfl
  have hC : IsJordanCurve C := ⟨f, hf, himage⟩
  have hloop : loopVariation ε C = loopVariationOn ε f (Icc (0 : ℝ) 1) :=
    loopVariation_eq_of_parametrization ε hC zero_lt_one
      hf.continuousOn hf.closes hf.injOn himage
  have hcont : ContinuousOn f (Icc (t 0) (t m)) := by
    simpa only [ht0, htm] using hf.continuousOn
  have hclose : f (t 0) = f (t m) := by
    simpa only [ht0, htm] using hf.closes
  have hcuts := loop_partition_estimates_of_continuousOn
    (show 0 < m by omega) hε ht.monotoneOn hcont hclose
  rw [hsum, hloop]
  simpa only [ht0, htm] using hcuts

end

end Puzzling139335.LoopVariation
