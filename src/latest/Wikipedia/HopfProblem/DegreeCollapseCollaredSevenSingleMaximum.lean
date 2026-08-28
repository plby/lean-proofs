import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenMorseCancellation
import Wikipedia.HopfProblem.DegreeCollapseSinglePositiveCritical
import Wikipedia.HopfProblem.DegreeCollapseNativeDiskBoundary

/-!
# Recognize the original smooth zero boundary from one positive critical point

The terminal Morse criterion constructs an actual smooth neighborhood of
the whole literal positive half. Restriction of that chart gives a
diffeomorphism from the literal standard six-sphere to the state's
original native zero boundary. The criterion is not assumed to hold for
the current filling: constructing the required finite cancellation
sequence remains separate work.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open NoExoticSixSphere GLOrthonormalization
open Wikipedia.SmoothSixDPoincare ManifoldMorse MorseCancellation

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}

theorem ExcellentMorsePresentation.nonempty_native_half_disk_of_single_positive_critical
    (P : S.ExcellentMorsePresentation) (p : S.Space)
    (hp : p ∈ criticalPoints (Vector 7) P.function) (hpos : 0 < P.function p)
    (hunique : ∀ x ∈ criticalPoints (Vector 7) P.function, 0 < P.function x → x = p) :
    Nonempty (NativeSublevelDisk 7 (Vector 7) (fun x => -S.time x) 0) := by
  have hd : Nonempty (NativeSublevelDisk 7 (Vector 7) (fun x => -P.function x) 0) := by
    simpa using nonempty_native_superlevel_disk_of_unique_positive_critical P.smooth hpos hunique
      P.morse hp (RegularTimeMorse.regular_zero_not_critical P.regular)
  obtain ⟨d⟩ := hd
  refine ⟨{
    chart := d.chart
    closedBall_source := d.closedBall_source
    image_closedBall := ?_
    image_sphere := ?_ }⟩
  · rw [d.image_closedBall]
    ext x
    change -P.function x ≤ 0 ↔ -S.time x ≤ 0
    simpa only [neg_nonpos] using P.nonnegative_iff x
  · rw [d.image_sphere]
    ext x
    change -P.function x = 0 ↔ -S.time x = 0
    simpa only [neg_eq_zero] using P.zero_iff x

def nativeHalfDiskBoundaryDiffeomorph
    (d : NativeSublevelDisk 7 (Vector 7) (fun x => -S.time x) 0) :
    letI := S.zeroAtlas;
    Diffeomorph (𝓡 6) (𝓡 6) (Sphere 6) S.Zero ∞ := by
  let := S.zeroAtlas
  let : IsManifold (𝓡 6) ∞ S.Zero := S.zero_isManifold
  let : Fact (Module.finrank ℝ (Hemisphere.Ambient 7) = 6 + 1) := ⟨by simp⟩
  have hlevel (v : Sphere 6) : -S.time (d.chart v.val) = 0 := by
    have h : d.chart v.val ∈ d.chart '' sphere (0 : Hemisphere.Ambient 7) 1 :=
      ⟨v.val, v.property, rfl⟩
    rwa [d.image_sphere] at h
  have hzero (v : Sphere 6) : S.time (d.chart v.val) = 0 := neg_eq_zero.mp (hlevel v)
  have hinverse (x : S.Zero) : d.chart.symm x.val ∈ sphere (0 : Hemisphere.Ambient 7) 1 :=
    d.inverse_mem_sphere_of_level (by rw [x.property, neg_zero])
  have htarget (x : S.Zero) : x.val ∈ d.chart.target :=
    d.mem_target_of_level (by rw [x.property, neg_zero])
  have hforward : ContMDiff (𝓡 6) (𝓡 7) ∞ (fun v : Sphere 6 => d.chart v.val) :=
    d.chart.contMDiffOn_toFun.comp_contMDiff (contMDiff_coe_sphere (n := 6))
      (fun v => d.closedBall_source (sphere_subset_closedBall v.property))
  have hbackward : ContMDiff (𝓡 6) 𝓘(ℝ, Hemisphere.Ambient 7) ∞
      (fun x : S.Zero => d.chart.symm x.val) :=
    d.chart.contMDiffOn_invFun.comp_contMDiff
      (regularFiber_contMDiff_subtype_val S.zeroTimeMap S.time_smooth 0 S.time_regular 6 (by simp))
      htarget
  refine {
    toFun := fun v => ⟨d.chart v.val, hzero v⟩
    invFun := fun x => ⟨d.chart.symm x.val, hinverse x⟩
    left_inv := fun v => Subtype.ext
      (d.chart.left_inv' (d.closedBall_source (sphere_subset_closedBall v.property)))
    right_inv := fun x => Subtype.ext (d.chart.right_inv' (htarget x))
    contMDiff_toFun := ?_
    contMDiff_invFun := hbackward.codRestrict_sphere hinverse }
  exact (regularFiber_contMDiff_iff_ambient
    S.zeroTimeMap S.time_smooth 0 S.time_regular 6 (by simp) _).mpr hforward

theorem ExcellentMorsePresentation.nonempty_zero_sphere_diffeomorph_of_single_positive_critical
    (P : S.ExcellentMorsePresentation) (p : S.Space)
    (hp : p ∈ criticalPoints (Vector 7) P.function) (hpos : 0 < P.function p)
    (hunique : ∀ x ∈ criticalPoints (Vector 7) P.function, 0 < P.function x → x = p) :
    letI := S.zeroAtlas;
    Nonempty (Diffeomorph (𝓡 6) (𝓡 6) (Sphere 6) S.Zero ∞) := by
  let := S.zeroAtlas
  obtain ⟨d⟩ := P.nonempty_native_half_disk_of_single_positive_critical p hp hpos hunique
  exact ⟨nativeHalfDiskBoundaryDiffeomorph d⟩

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState
