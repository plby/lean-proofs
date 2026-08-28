import Wikipedia.SmoothSixDPoincare.BeltTubeCoordinates
import Wikipedia.SmoothSixDPoincare.TransportedMorseAttachment
import Wikipedia.SmoothSixDPoincare.MorseAttachingTransport

/-!
# Exact belt-tube localization of the original moved attaching core

The standard description of the entire core image, together with the local
parametrization, determines the original source point of every crossing.
Consequently, the inverse image of a smaller closed belt tube is exactly the
original small closed chart disk. This also separates the complementary disk
from every strictly smaller tube.
-/

noncomputable section

open Set Function Metric Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p q : M}
  (d : MorseSurgeryData E f p) (d' : MorseSurgeryData E f q)

open Classical in
def movedAttachingCore (b : d.UpperLevel ≃ₜ d'.LowerLevel)
    (e : d.UpperLevel ≃ₜ d.UpperLevel) :
    C(PuncturedHandle.UnitSphere d'.chart.NegativeCoordinates, d.UpperLevel) :=
  ⟨fun u => e (b.symm (d'.surgery.attachingSphere u)),
    e.continuous.comp (b.symm.continuous.comp d'.surgery.attachingSphere.continuous)⟩

open Classical in
def movedAttachingFace (b : d.UpperLevel ≃ₜ d'.LowerLevel)
    (e : d.UpperLevel ≃ₜ d.UpperLevel)
    (R : (PuncturedHandle.UnitSphere d'.chart.NegativeCoordinates ×
        MorseHandle.UnitDisk d'.chart.PositiveCoordinates) ≃ₜ
      (PuncturedHandle.UnitSphere d'.chart.NegativeCoordinates ×
        MorseHandle.UnitDisk d'.chart.PositiveCoordinates)) :
    C(PuncturedHandle.UnitSphere d'.chart.NegativeCoordinates ×
      MorseHandle.UnitDisk d'.chart.PositiveCoordinates, d.UpperLevel) :=
  ⟨fun z => e (b.symm (d'.attachingFace (R z))),
    e.continuous.comp (b.symm.continuous.comp (d'.attachingFace.continuous.comp R.continuous))⟩

open Classical in
theorem attachingFace_core (u : PuncturedHandle.UnitSphere d'.chart.NegativeCoordinates) :
    d'.attachingFace (u, ⟨0, by simp⟩) = d'.surgery.attachingSphere u := by
  rw [d'.attaching_eq]
  rfl

open Classical in
theorem movedAttachingFace_core (b : d.UpperLevel ≃ₜ d'.LowerLevel)
    (e : d.UpperLevel ≃ₜ d.UpperLevel)
    (R : (PuncturedHandle.UnitSphere d'.chart.NegativeCoordinates ×
        MorseHandle.UnitDisk d'.chart.PositiveCoordinates) ≃ₜ
      (PuncturedHandle.UnitSphere d'.chart.NegativeCoordinates ×
        MorseHandle.UnitDisk d'.chart.PositiveCoordinates))
    (hR : ∀ u, R (u, (⟨0, by simp⟩ : MorseHandle.UnitDisk d'.chart.PositiveCoordinates)) =
      (u, ⟨0, by simp⟩)) (u : PuncturedHandle.UnitSphere d'.chart.NegativeCoordinates) :
    d.movedAttachingFace d' b e R (u, ⟨0, by simp⟩) = d.movedAttachingCore d' b e u := by
  change e (b.symm (d'.attachingFace (R (u, ⟨0, by simp⟩)))) = _
  rw [hR, d'.attachingFace_core]
  rfl

open Classical in
theorem range_movedAttachingCore (n : ℕ)
    [Fact (Module.finrank ℝ d'.chart.NegativeCoordinates = n + 1)]
    (b : d.UpperLevel ≃ₜ d'.LowerLevel) (e : d.UpperLevel ≃ₜ d.UpperLevel) :
    range (d.movedAttachingCore d' b e) = range (e ∘ d.transportedAttachingSphere d' n b) := by
  let S := SphereCoordinates.standardParametrization d'.chart.NegativeCoordinates n
  have hpoint (x : Hemisphere.Sphere n) :
      e (d.transportedAttachingSphere d' n b x) = d.movedAttachingCore d' b e (S x) := rfl
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨x, rfl⟩ := S.surjective u
    exact ⟨x, hpoint x⟩
  · rintro ⟨x, rfl⟩
    exact ⟨S x, (hpoint x).symm⟩

variable [T2Space M]

open Classical in
theorem movedAttachingFace_injective (b : d.UpperLevel ≃ₜ d'.LowerLevel)
    (e : d.UpperLevel ≃ₜ d.UpperLevel)
    (R : (PuncturedHandle.UnitSphere d'.chart.NegativeCoordinates ×
        MorseHandle.UnitDisk d'.chart.PositiveCoordinates) ≃ₜ
      (PuncturedHandle.UnitSphere d'.chart.NegativeCoordinates ×
        MorseHandle.UnitDisk d'.chart.PositiveCoordinates)) :
    Injective (d.movedAttachingFace d' b e R) :=
  e.injective.comp (b.symm.injective.comp (d'.attachingFace_injective.comp R.injective))

open Classical in
theorem movedAttachingCore_injective (b : d.UpperLevel ≃ₜ d'.LowerLevel)
    (e : d.UpperLevel ≃ₜ d.UpperLevel) : Injective (d.movedAttachingCore d' b e) :=
  e.injective.comp (b.symm.injective.comp d'.attaching_isClosedEmbedding.injective)

open Classical in
/-- Every point in the small tube has its exact original core parameter determined. -/
theorem normalizedCore_belt_point_iff
    (b : d.UpperLevel ≃ₜ d'.LowerLevel) (e : d.UpperLevel ≃ₜ d.UpperLevel)
    (Φ : d.chart.NegativeCoordinates → PuncturedHandle.UnitSphere d'.chart.NegativeCoordinates)
    (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) {δ ρ : ℝ}
    (hstandard : ∀ z : d.beltSurgerySource, ‖z.val.2‖ ≤ δ →
      ((d.beltSurgeryHomeomorph z).val ∈ range (d.movedAttachingCore d' b e) ↔ z.val.1 = v))
    (hlocal : ∀ x ∈ closedBall (0 : d.chart.NegativeCoordinates) ρ,
      ∃ hz : (v, x) ∈ d.beltSurgerySource,
        d.movedAttachingCore d' b e (Φ x) = (d.beltSurgeryHomeomorph ⟨(v, x), hz⟩).val)
    (u : PuncturedHandle.UnitSphere d'.chart.NegativeCoordinates) (z : d.beltSurgerySource)
    (hzδ : ‖z.val.2‖ ≤ δ) (hzρ : ‖z.val.2‖ ≤ ρ) :
    d.movedAttachingCore d' b e u = (d.beltSurgeryHomeomorph z).val ↔
      z.val.1 = v ∧ u = Φ z.val.2 := by
  obtain ⟨hx, hpoint⟩ := hlocal z.val.2 (mem_closedBall_zero_iff.mpr hzρ)
  have hpoint' (hzv : z.val.1 = v) :
      d.movedAttachingCore d' b e (Φ z.val.2) = (d.beltSurgeryHomeomorph z).val := by
    have heq : (⟨(v, z.val.2), hx⟩ : d.beltSurgerySource) = z :=
      Subtype.ext (Prod.ext hzv.symm rfl)
    exact hpoint.trans (congrArg (fun w : d.beltSurgerySource =>
      (d.beltSurgeryHomeomorph w).val) heq)
  constructor
  · intro hu
    have hzv := (hstandard z hzδ).mp ⟨u, hu⟩
    exact ⟨hzv, d.movedAttachingCore_injective d' b e (hu.trans (hpoint' hzv).symm)⟩
  · rintro ⟨hzv, rfl⟩
    exact hpoint' hzv

open Classical in
/-- The full core preimage of a closed tube is exactly the small original closed disk. -/
theorem normalizedCore_mem_closedBeltTube_iff
    (b : d.UpperLevel ≃ₜ d'.LowerLevel) (e : d.UpperLevel ≃ₜ d.UpperLevel)
    (Φ : d.chart.NegativeCoordinates → PuncturedHandle.UnitSphere d'.chart.NegativeCoordinates)
    (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) {δ ρ s : ℝ}
    (hstandard : ∀ z : d.beltSurgerySource, ‖z.val.2‖ ≤ δ →
      ((d.beltSurgeryHomeomorph z).val ∈ range (d.movedAttachingCore d' b e) ↔ z.val.1 = v))
    (hlocal : ∀ x ∈ closedBall (0 : d.chart.NegativeCoordinates) ρ,
      ∃ hz : (v, x) ∈ d.beltSurgerySource,
        d.movedAttachingCore d' b e (Φ x) = (d.beltSurgeryHomeomorph ⟨(v, x), hz⟩).val)
    (hsδ : s ≤ δ) (hsρ : s ≤ ρ)
    (u : PuncturedHandle.UnitSphere d'.chart.NegativeCoordinates) :
    d.movedAttachingCore d' b e u ∈ d.closedBeltTube s ↔
      u ∈ Φ '' closedBall (0 : d.chart.NegativeCoordinates) s := by
  constructor
  · intro hu
    obtain ⟨z, hz, hzu⟩ := (d.mem_closedBeltTube_iff_exists s _).mp hu
    have heq := (d.normalizedCore_belt_point_iff d' b e Φ v hstandard hlocal u z
      (hz.trans hsδ) (hz.trans hsρ)).mp hzu.symm
    exact ⟨z.val.2, mem_closedBall_zero_iff.mpr hz, heq.2.symm⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hz, heq⟩ := hlocal x (closedBall_subset_closedBall hsρ hx)
    rw [heq, d.beltSurgeryHomeomorph_mem_closedBeltTube_iff]
    exact mem_closedBall_zero_iff.mp hx

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
