import Wikipedia.SmoothSixDPoincare.CompactFaceAvoidance
import Wikipedia.SmoothSixDPoincare.BeltClosedDiskTube

/-!
# A compact belt-avoiding image misses a whole closed native belt tube

The zero section is the original belt. Uniform compact-base avoidance for
the native closed normal disk gives a positive tube radius strictly below
one, with disjointness in the actual original upper level.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

open Classical in
theorem beltClosedDiskMap_zero (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.beltClosedDiskMap (⟨0, by simp⟩, v) = d.surgery.beltSphere v := by
  rw [d.belt_eq]
  exact d.chart.beltNeighborhoodHomeomorph_zero d.radius d.radius_pos d.block v

open Classical in
theorem exists_closedBeltTube_avoiding_compact [T2Space M] {K : Set d.UpperLevel}
    (hK : IsCompact K) (havoid : Disjoint K (range d.surgery.beltSphere)) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ Disjoint K (d.closedBeltTube s) := by
  let F : C(PuncturedHandle.UnitSphere d.chart.PositiveCoordinates ×
      MorseHandle.UnitDisk d.chart.NegativeCoordinates, d.UpperLevel) :=
    ⟨fun z => d.beltClosedDiskMap
      (⟨z.2.val, mem_closedBall_zero_iff.mp z.2.property⟩, z.1),
      d.beltClosedDiskMap.continuous.comp
        (((continuous_subtype_val.comp continuous_snd).subtype_mk _).prodMk continuous_fst)⟩
  have hcore (v) : F (v, ⟨0, by simp⟩) ∉ K := by
    change d.beltClosedDiskMap (⟨0, by simp⟩, v) ∉ K
    rw [d.beltClosedDiskMap_zero]
    exact disjoint_right.mp havoid ⟨v, rfl⟩
  obtain ⟨a, ha, ha₁, hthin⟩ := exists_uniform_face_avoidance_radius F hK.isClosed hcore
  have hs₁ : a / 2 < 1 := (half_lt_self ha).trans_le ha₁
  refine ⟨a / 2, half_pos ha, hs₁, disjoint_left.mpr ?_⟩
  intro y hyK hyTube
  rw [d.closedBeltTube_eq_beltClosedDiskMap_image hs₁] at hyTube
  obtain ⟨⟨u, v⟩, hu, rfl⟩ := hyTube
  let w : MorseHandle.UnitDisk d.chart.NegativeCoordinates :=
    ⟨u.val, mem_closedBall_zero_iff.mpr u.property⟩
  exact hthin v w (hu.trans (half_le_self ha.le)) hyK

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
