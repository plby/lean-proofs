import Wikipedia.SmoothSixDPoincare.FramedSurgeryBoundary

/-!
# Compactness of the actual framed-surgery boundary

The complement of a half-radius open tube and the new half-radius closed
piece give an explicit compact cover. The transition identities establish
that these are exhaustive in the actual boundary quotient.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

open PuncturedHandle

variable {E F G H X : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)

def innerTube : Set X := A.map '' {p | ‖p.2.val‖ < (1 / 2 : ℝ)}

omit [FiniteDimensional ℝ E] [T2Space X] in
theorem face_mem_innerTube_iff (u : UnitSphere E) (v : MorseHandle.UnitDisk F) :
    A.map (u, v) ∈ innerTube A ↔ ‖v.val‖ < (1 / 2 : ℝ) := by
  constructor
  · rintro ⟨p, hp, heq⟩
    have hpq := A.closedEmbedding.injective heq
    subst p
    exact hp
  · intro h
    exact ⟨(u, v), h, rfl⟩

omit [FiniteDimensional ℝ E] [T2Space X] in
theorem innerTube_eq_chart_image : innerTube A =
    A.chart '' ((univ : Set (UnitSphere E)) ×ˢ ball (0 : F) (1 / 2)) := by
  ext x
  constructor
  · rintro ⟨⟨u, v⟩, hv, rfl⟩
    exact ⟨(u, v.val), ⟨mem_univ _, mem_ball_zero_iff.mpr hv⟩, A.point u v⟩
  · rintro ⟨⟨u, v⟩, ⟨_, hv⟩, rfl⟩
    have hv' := mem_ball_zero_iff.mp hv
    let w : MorseHandle.UnitDisk F := ⟨v, mem_closedBall_zero_iff.mpr (by linarith)⟩
    exact ⟨(u, w), hv', (A.point u w).symm⟩

omit [FiniteDimensional ℝ E] [T2Space X] in
theorem isOpen_innerTube : IsOpen (innerTube A) := by
  rw [innerTube_eq_chart_image]
  apply A.chart.toOpenPartialHomeomorph.isOpen_image_of_subset_source
    (isOpen_univ.prod isOpen_ball)
  rintro ⟨u, v⟩ ⟨_, hv⟩
  apply A.source
  refine ⟨mem_univ _, mem_closedBall_zero_iff.mpr ?_⟩
  have hv' := mem_ball_zero_iff.mp hv
  linarith

omit [FiniteDimensional ℝ E] [T2Space X] in
theorem core_subset_innerTube : range (coreMap A) ⊆ innerTube A := by
  rintro x ⟨u, rfl⟩
  apply (face_mem_innerTube_iff A u ⟨0, by simp⟩).mpr
  norm_num

def oldCompactMap : C({x : X // x ∉ innerTube A}, oldPatch A) :=
  ⟨fun x => ⟨x.val, fun h => x.property (core_subset_innerTube A h)⟩,
    continuous_subtype_val.subtype_mk _⟩

def newCompactMap : C(closedBall (0 : E) (1 / 2) × UnitSphere F, NewPatch E F) :=
  ⟨fun p => (⟨p.1.val, mem_ball_zero_iff.mpr
    ((mem_closedBall_zero_iff.mp p.1.property).trans_lt (by norm_num))⟩, p.2),
    ((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd⟩

variable (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]

theorem compact_cover (q : Boundary A n) :
    q ∈ range ((oldMap A n).comp (oldCompactMap A)) ∪
      range ((newMap A n).comp (newCompactMap (E := E) (F := F))) := by
  obtain (⟨x, rfl⟩ | ⟨y, rfl⟩) := cover A n q
  · by_cases hx : x.val ∈ innerTube A
    · obtain ⟨⟨u, v⟩, hv, hmap⟩ := hx
      change ‖v.val‖ < (1 / 2 : ℝ) at hv
      have hv0 : v.val ≠ 0 := by
        intro hzero
        apply x.property
        rw [← hmap]
        exact (face_mem_core_iff A u v).mpr hzero
      let z : Overlap E F := (u, ⟨v.val, hv0, by linarith⟩)
      have hz : oldOverlap A z = x := Subtype.ext hmap
      have hsmall : ‖(newOverlap m n z).1.val‖ ≤ (1 / 2 : ℝ) := by
        change ‖(openExchange m n z).1.val‖ ≤ _
        rw [norm_openExchange_fst]
        exact hv.le
      let p : closedBall (0 : E) (1 / 2) × UnitSphere F :=
        (⟨(newOverlap m n z).1.val, mem_closedBall_zero_iff.mpr hsmall⟩,
          (newOverlap m n z).2)
      refine Or.inr ⟨p, ?_⟩
      change newMap A n (newOverlap m n z) = oldMap A n x
      exact (overlap_identification A n z).symm.trans (congrArg (oldMap A n) hz)
    · exact Or.inl ⟨⟨x.val, hx⟩, rfl⟩
  · by_cases hy : ‖y.1.val‖ ≤ (1 / 2 : ℝ)
    · exact Or.inr ⟨(⟨y.1.val, mem_closedBall_zero_iff.mpr hy⟩, y.2), rfl⟩
    · have hy0 : y.1.val ≠ 0 := by
        intro hzero
        apply hy
        simp [hzero]
      let v : openPuncturedDisk E :=
        ⟨y.1.val, hy0, mem_ball_zero_iff.mp y.1.property⟩
      let z : Overlap E F := (openExchange m n).symm (v, y.2)
      have hznew : newOverlap m n z = y := by
        have h := (openExchange m n).apply_symm_apply (v, y.2)
        exact congrArg (fun p : openPuncturedDisk E × UnitSphere F =>
          ((⟨p.1.val, mem_ball_zero_iff.mpr p.1.property.2⟩ : openUnitDisk E), p.2)) h
      have hzNorm : ‖z.2.val‖ = ‖y.1.val‖ := by
        have h := norm_openExchange_fst m n z.1 z.2
        change ‖(newOverlap m n z).1.val‖ = ‖z.2.val‖ at h
        rw [hznew] at h
        exact h.symm
      have hout : (oldOverlap A z).val ∉ innerTube A := by
        intro hin
        have h := (face_mem_innerTube_iff A z.1
          ⟨z.2.val, mem_closedBall_zero_iff.mpr z.2.property.2.le⟩).mp hin
        rw [hzNorm] at h
        exact hy h.le
      refine Or.inl ⟨⟨(oldOverlap A z).val, hout⟩, ?_⟩
      change oldMap A n (oldOverlap A z) = newMap A n y
      exact (overlap_identification A n z).trans (congrArg (newMap A n) hznew)

instance boundaryCompactSpace [CompactSpace X] [FiniteDimensional ℝ F] :
    CompactSpace (Boundary A n) := by
  let _ : CompactSpace {x : X // x ∉ innerTube A} :=
    isCompact_iff_compactSpace.mp (isOpen_innerTube A).isClosed_compl.isCompact
  have hOld := isCompact_range ((oldMap A n).comp (oldCompactMap A)).continuous
  have hNew := isCompact_range ((newMap A n).comp
    (newCompactMap (E := E) (F := F))).continuous
  apply isCompact_univ_iff.mp
  have heq : range ((oldMap A n).comp (oldCompactMap A)) ∪
      range ((newMap A n).comp (newCompactMap (E := E) (F := F))) = univ :=
    eq_univ_of_forall (compact_cover A n)
  rw [← heq]
  exact hOld.union hNew

end Wikipedia.SmoothSixDPoincare.FramedSurgery
