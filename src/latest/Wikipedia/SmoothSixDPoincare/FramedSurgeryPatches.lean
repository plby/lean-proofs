import Wikipedia.SmoothSixDPoincare.SmoothClosedFace
import Wikipedia.SmoothSixDPoincare.SmoothOpenSurgeryExchange
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# The actual two open patches of surgery on a framed face

The old patch removes precisely the original attaching core. Its overlap
map is the given face map, while the new patch uses the proved radial
exchange. Both overlap parametrizations are open embeddings.
-/

noncomputable section

open Set Function Topology TopologicalSpace Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

open PuncturedHandle

def openUnitDisk (E : Type*) [NormedAddCommGroup E] : Opens E :=
  ⟨ball 0 1, isOpen_ball⟩

abbrev Overlap (E F : Type*) [NormedAddCommGroup E] [NormedAddCommGroup F] :=
  UnitSphere E × openPuncturedDisk F

abbrev NewPatch (E F : Type*) [NormedAddCommGroup E] [NormedAddCommGroup F] :=
  openUnitDisk E × UnitSphere F

variable {E F G H X : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)

def coreMap : C(UnitSphere E, X) :=
  A.map.comp ⟨fun u => (u, ⟨0, by simp⟩), continuous_id.prodMk continuous_const⟩

theorem isClosed_core : IsClosed (range (coreMap A)) :=
  (isCompact_range (coreMap A).continuous).isClosed

def oldPatch : Opens X := ⟨(range (coreMap A))ᶜ, (isClosed_core A).isOpen_compl⟩

omit [FiniteDimensional ℝ E] [T2Space X] in
theorem face_mem_core_iff (u : UnitSphere E) (v : MorseHandle.UnitDisk F) :
    A.map (u, v) ∈ range (coreMap A) ↔ v.val = 0 := by
  constructor
  · rintro ⟨w, hw⟩
    have h := A.closedEmbedding.injective hw
    exact (congrArg (fun z : UnitSphere E × MorseHandle.UnitDisk F => z.2.val) h).symm
  · intro hv
    refine ⟨u, ?_⟩
    apply congrArg A.map
    exact Prod.ext rfl (Subtype.ext hv.symm)

def oldOverlap (z : Overlap E F) : oldPatch A :=
  ⟨A.map (z.1, ⟨z.2.val, mem_closedBall_zero_iff.mpr z.2.property.2.le⟩),
    fun h => z.2.property.1 ((face_mem_core_iff A _ _).mp h)⟩

theorem oldOverlap_coe (z : Overlap E F) :
    (oldOverlap A z).val =
      A.map (z.1, ⟨z.2.val, mem_closedBall_zero_iff.mpr z.2.property.2.le⟩) := rfl

theorem oldOverlap_isOpenEmbedding : IsOpenEmbedding (oldOverlap A) := by
  let s : Overlap E F → A.chart.source := fun z =>
    ⟨(z.1, z.2.val), A.source ⟨mem_univ _, mem_closedBall_zero_iff.mpr z.2.property.2.le⟩⟩
  have hraw : IsOpenEmbedding (fun z : Overlap E F => (z.1, z.2.val)) :=
    IsOpenEmbedding.id.prodMap (openPuncturedDisk F).isOpen.isOpenEmbedding_subtypeVal
  have hs : IsOpenEmbedding s :=
    IsOpenEmbedding.of_comp s A.chart.open_source.isOpenEmbedding_subtypeVal hraw
  have hchart := A.chart.toOpenPartialHomeomorph.isOpenEmbedding_restrict.comp hs
  have heq : (fun z : Overlap E F => (oldOverlap A z).val) =
      A.chart.source.domRestrict A.chart ∘ s := by
    funext z
    exact (A.point z.1 ⟨z.2.val, mem_closedBall_zero_iff.mpr z.2.property.2.le⟩).symm
  apply IsOpenEmbedding.of_comp (oldOverlap A) (oldPatch A).isOpen.isOpenEmbedding_subtypeVal
  change IsOpenEmbedding (fun z : Overlap E F => (oldOverlap A z).val)
  rw [heq]
  exact hchart

section NewOverlap

variable (m n : ℕ) [Fact (Module.finrank ℝ E = m + 1)]
  [Fact (Module.finrank ℝ F = n + 1)]

def newOverlap (z : Overlap E F) : NewPatch E F :=
  (⟨(openExchange m n z).1.val,
    mem_ball_zero_iff.mpr (openExchange m n z).1.property.2⟩, (openExchange m n z).2)

omit [FiniteDimensional ℝ E] in
theorem newOverlap_fst (z : Overlap E F) :
    (newOverlap m n z).1.val = ‖z.2.val‖ • z.1.val := rfl

omit [FiniteDimensional ℝ E] in
theorem newOverlap_snd (z : Overlap E F) :
    (newOverlap m n z).2.val = ‖z.2.val‖⁻¹ • z.2.val := rfl

omit [FiniteDimensional ℝ E] in
theorem newOverlap_isOpenEmbedding : IsOpenEmbedding (newOverlap (E := E) (F := F) m n) := by
  let j : openPuncturedDisk E → openUnitDisk E :=
    fun u => ⟨u.val, mem_ball_zero_iff.mpr u.property.2⟩
  have hj : IsOpenEmbedding j :=
    IsOpenEmbedding.of_comp j (openUnitDisk E).isOpen.isOpenEmbedding_subtypeVal
      (openPuncturedDisk E).isOpen.isOpenEmbedding_subtypeVal
  exact (hj.prodMap IsOpenEmbedding.id).comp (openExchange m n).toHomeomorph.isOpenEmbedding

end NewOverlap

end Wikipedia.SmoothSixDPoincare.FramedSurgery
