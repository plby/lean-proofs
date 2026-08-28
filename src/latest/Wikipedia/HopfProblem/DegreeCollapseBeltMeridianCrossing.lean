import Wikipedia.HopfProblem.DegreeCollapseBeltMeridianDisk
import Wikipedia.HopfProblem.DegreeCollapseBeltComplementDiffeomorph

/-!
# The actual meridian disk meets the entire belt only at its center

Injectivity of the original inverse Morse chart detects the zero negative
coordinate. Thus the statement concerns the full belt, and equivalently
the whole forward basin on the actual upper level, not just a local sheet.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open DiskShrinking

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] {f : M → ℝ}

theorem nativeBeltMeridianDisk_belt_eq_iff (S : AdaptedSurgeryWindows E f)
    (q : criticalPoints E f) (v w : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (s : unitInterval) (hs : (s : ℝ) ≤ 1 / 2) (hs0 : 0 < (s : ℝ))
    (x : (S.data q).chart.NegativeCoordinates) :
    nativeBeltMeridianDisk S q v s hs x = (S.data q).surgery.beltSphere w ↔
      x = 0 ∧ v = w := by
  constructor
  · intro h
    have he : nativeBeltMeridianDisk S q v s hs x =
        nativeBeltMeridianDisk S q w s hs 0 :=
      h.trans (nativeBeltMeridianDisk_zero S q w s hs).symm
    have hc := (S.data q).chart.splitChart.symm.toPartialEquiv.injOn
      (nativeBeltDiskCoordinates_mem_target S q v s hs x)
      (nativeBeltDiskCoordinates_mem_target S q w s hs 0) (congrArg Subtype.val he)
    have hfst : (S.data q).radius • boundedRadialDiskMap (s : ℝ) x =
        (S.data q).radius • boundedRadialDiskMap (s : ℝ) 0 := congrArg Prod.fst hc
    have hx : x = 0 := boundedRadialDiskMap_injective hs0
      (smul_right_injective _ (S.data q).radius_pos.ne' hfst)
    rw [hx, nativeBeltMeridianDisk_zero] at h
    exact ⟨hx, (S.data q).belt_isClosedEmbedding.injective h⟩
  · rintro ⟨rfl, rfl⟩
    exact nativeBeltMeridianDisk_zero S q v s hs

theorem nativeBeltMeridianDisk_mem_belt_iff (S : AdaptedSurgeryWindows E f)
    (q : criticalPoints E f) (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (s : unitInterval) (hs : (s : ℝ) ≤ 1 / 2) (hs0 : 0 < (s : ℝ))
    (x : (S.data q).chart.NegativeCoordinates) :
    nativeBeltMeridianDisk S q v s hs x ∈ range (S.data q).surgery.beltSphere ↔ x = 0 := by
  constructor
  · rintro ⟨w, hw⟩
    exact ((nativeBeltMeridianDisk_belt_eq_iff S q v w s hs hs0 x).mp hw.symm).1
  · intro hx
    exact ⟨v, ((nativeBeltMeridianDisk_belt_eq_iff S q v v s hs hs0 x).mpr ⟨hx, rfl⟩).symm⟩

theorem nativeBeltMeridianDisk_forward_basin_iff (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : criticalPoints E f)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (s : unitInterval) (hs : (s : ℝ) ≤ 1 / 2) (hs0 : 0 < (s : ℝ))
    (x : (S.data q).chart.NegativeCoordinates) :
    Tendsto (fun t => S.flow t (nativeBeltMeridianDisk S q v s hs x).val) atTop (𝓝 q.val) ↔
      x = 0 :=
  (S.belt_basin_iff hf q _).trans (nativeBeltMeridianDisk_mem_belt_iff S q v s hs hs0 x)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
