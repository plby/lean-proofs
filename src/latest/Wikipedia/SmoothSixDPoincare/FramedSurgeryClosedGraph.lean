import Wikipedia.SmoothSixDPoincare.FramedSurgeryPatches
import Wikipedia.SmoothSixDPoincare.OpenGluingOverlap

/-!
# The prescribed surgery overlap has closed graph

The overlap graph is the restriction of a compact radial correspondence.
Its radius-zero limit lies on the removed attaching core, and its radius-one
limit lies outside the new open disk. Thus neither produces a missing limit
point inside the two surgery patches.
-/

noncomputable section

open Set Function Topology TopologicalSpace Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

open PuncturedHandle

section Radial

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def closedPoint (u : UnitSphere V) (r : Icc (0 : ℝ) 1) : MorseHandle.UnitDisk V :=
  ⟨r.val • u.val, mem_closedBall_zero_iff.mpr (by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg r.property.1,
      mem_sphere_zero_iff_norm.mp u.property, mul_one]
    exact r.property.2)⟩

theorem norm_closedPoint (u : UnitSphere V) (r : Icc (0 : ℝ) 1) :
    ‖(closedPoint u r).val‖ = r.val := by
  change ‖r.val • u.val‖ = r.val
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg r.property.1,
    mem_sphere_zero_iff_norm.mp u.property, mul_one]

end Radial

variable {E F G H X : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)

def closedGraphMap : C(UnitSphere E × Icc (0 : ℝ) 1 × UnitSphere F,
    X × (E × UnitSphere F)) := by
  refine ⟨fun q => (A.map (q.1, closedPoint q.2.2 q.2.1),
    ((closedPoint q.1 q.2.1).val, q.2.2)), ?_⟩
  have hr : Continuous (fun q : UnitSphere E × Icc (0 : ℝ) 1 × UnitSphere F =>
      q.2.1.val) := continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have hu : Continuous (fun q : UnitSphere E × Icc (0 : ℝ) 1 × UnitSphere F =>
      q.1.val) := continuous_subtype_val.comp continuous_fst
  have hw : Continuous (fun q : UnitSphere E × Icc (0 : ℝ) 1 × UnitSphere F =>
      q.2.2.val) := continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  exact (A.map.continuous.comp (continuous_fst.prodMk ((hr.smul hw).subtype_mk _))).prodMk
    ((hr.smul hu).prodMk (continuous_snd.comp continuous_snd))

def patchAmbientMap : C(oldPatch A × NewPatch E F, X × (E × UnitSphere F)) :=
  ⟨fun p => (p.1.val, (p.2.1.val, p.2.2)),
    (continuous_subtype_val.comp continuous_fst).prodMk
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
        (continuous_snd.comp continuous_snd))⟩

variable (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]

omit [FiniteDimensional ℝ F] in
theorem overlap_graph_eq :
    range (fun z : Overlap E F => (oldOverlap A z, newOverlap m n z)) =
      patchAmbientMap A ⁻¹' range (closedGraphMap A) := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    let r : Icc (0 : ℝ) 1 := ⟨‖z.2.val‖, norm_nonneg _, z.2.property.2.le⟩
    let w : UnitSphere F := (openExchange m n z).2
    refine ⟨(z.1, r, w), ?_⟩
    apply Prod.ext
    · change A.map (z.1, closedPoint w r) =
        A.map (z.1, ⟨z.2.val, mem_closedBall_zero_iff.mpr z.2.property.2.le⟩)
      apply congrArg A.map
      refine Prod.ext rfl ?_
      apply Subtype.ext
      change ‖z.2.val‖ • (‖z.2.val‖⁻¹ • z.2.val) = z.2.val
      exact smul_inv_smul₀ (norm_ne_zero_iff.mpr z.2.property.1) _
    · rfl
  · rintro ⟨⟨u, r, w⟩, h⟩
    have hx : A.map (u, closedPoint w r) = p.1.val := congrArg Prod.fst h
    have ha : (closedPoint u r).val = p.2.1.val := congrArg (fun q => q.2.1) h
    have hw : w = p.2.2 := congrArg (fun q => q.2.2) h
    have hr0 : r.val ≠ 0 := by
      intro hr
      apply p.1.property
      refine ⟨u, ?_⟩
      change A.map (u, ⟨0, _⟩) = p.1.val
      rw [← hx]
      apply congrArg A.map
      refine Prod.ext rfl ?_
      apply Subtype.ext
      simp only [closedPoint, hr, zero_smul]
    have hr1 : r.val < 1 := by
      rw [← norm_closedPoint u r, ha]
      exact mem_ball_zero_iff.mp p.2.1.property
    let v : openPuncturedDisk F :=
      ⟨(closedPoint w r).val, norm_ne_zero_iff.mp (by rw [norm_closedPoint]; exact hr0),
        by rw [norm_closedPoint]; exact hr1⟩
    refine ⟨(u, v), ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      exact hx
    · apply Prod.ext
      · apply Subtype.ext
        change ‖(closedPoint w r).val‖ • u.val = p.2.1.val
        rw [norm_closedPoint]
        exact ha
      · apply Subtype.ext
        change ‖(closedPoint w r).val‖⁻¹ • (r.val • w.val) = p.2.2.val
        rw [norm_closedPoint, inv_smul_smul₀ hr0]
        exact congrArg Subtype.val hw

theorem isClosed_overlap_graph :
    IsClosed (range (fun z : Overlap E F => (oldOverlap A z, newOverlap m n z))) := by
  rw [overlap_graph_eq A n]
  exact (isCompact_range (closedGraphMap A).continuous).isClosed.preimage
    (patchAmbientMap A).continuous

end Wikipedia.SmoothSixDPoincare.FramedSurgery
