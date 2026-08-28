import Wikipedia.NoExoticSixSphere.SphereFourTubeOldBand

/-!
# The actual time collar of the tube exterior

The original boundary and the new `S³ × S³` boundary have a combined
collar for the actual modified time. The old zero points are unchanged,
and the new zero points are exactly the unit normal tube points. This
is a collar construction, not a claim about exterior connectivity.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereFourTube

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse

variable {M B : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [TopologicalSpace B] [T2Space M]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞)

theorem exists_modified_time_collar (hΦ : Φ.source = univ)
    (t τ : C(M, ℝ)) (C : TimeCollar t B)
    (hpos : ∀ x ∈ Φ.target, 0 < t x)
    (hout : ∀ x ∉ closedRegion Φ 2, τ x = t x)
    (hinner : ∀ p : Sphere 3 × Vector 4, ‖p.2‖ ≤ 3 / 2 → τ (Φ p) = ‖p.2‖ ^ 2 - 1)
    (houter : ∀ p : Sphere 3 × Vector 4, 1 < ‖p.2‖ → 0 < τ (Φ p)) :
    ∃ D : TimeCollar τ (B ⊕ (Sphere 3 × Sphere 3)), D.width ≤ C.width ∧
      (∀ b : B, (D.zeroPoint (Sum.inl b)).val = (C.zeroPoint b).val) ∧
      ∀ s v : Sphere 3, (D.zeroPoint (Sum.inr (s, v))).val = Φ (s, v.val) := by
  obtain ⟨δ, hδ, hδw, hδhalf, hOld, -, hsplit⟩ :=
    exists_separated_time_bands Φ hΦ t τ hpos hout houter C.width C.width_pos
  obtain ⟨hU, hV, hdisj, hcover⟩ := timeBand_disjoint_open_cover Φ hΦ t τ δ hOld hsplit
  obtain ⟨eU, hUt, hUi⟩ := exists_old_time_coordinates Φ t τ C δ hδw hOld hout
  obtain ⟨eV, hVt, hVi⟩ := exists_inner_time_coordinates Φ hΦ τ hinner
    (Wikipedia.HopfProblem.SphereHomology.basePoint 3) δ hδhalf
  obtain ⟨e, het, heU, heV⟩ := TimeBandSumCoordinates.exists_time_coordinates τ δ
    (oldTimeBand t τ δ) (innerTimeBand Φ τ δ) hU hV hdisj hcover eU eV hUt hVt
  let D : TimeCollar τ (B ⊕ (Sphere 3 × Sphere 3)) :=
    { width := δ, width_pos := hδ, continuous_time := τ.continuous,
      coordinates := e, coordinate_time := het }
  let z : Ioo (-δ) δ := ⟨0, neg_lt_zero.mpr hδ, hδ⟩
  refine ⟨D, hδw, ?_, ?_⟩
  · intro b
    have hzero : e (eU.symm (z, b)).val = (z, Sum.inl b) := by
      rw [heU, eU.apply_symm_apply]
    change (e.symm (z, Sum.inl b)).val = (C.zeroPoint b).val
    rw [← hzero, e.symm_apply_apply, hUi]
    rfl
  · intro s v
    have hzero : e (eV.symm (z, (s, v))).val = (z, Sum.inr (s, v)) := by
      rw [heV, eV.apply_symm_apply]
    change (e.symm (z, Sum.inr (s, v))).val = Φ (s, v.val)
    rw [← hzero, e.symm_apply_apply, hVi]
    simp [SphereRadialHeightCoordinates.point, z]

theorem exists_collared_regular_time_modification [CompactSpace M] [IsManifold (𝓡 7) ∞ M]
    (hΦ : Φ.source = univ) (t : C(M, ℝ)) (C : TimeCollar t B)
    (ht : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ t)
    (hreg : ∀ x, t x = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) t x))
    (hpos : ∀ x ∈ Φ.target, 0 < t x) :
    ∃ (τ : C(M, ℝ)) (D : TimeCollar τ (B ⊕ (Sphere 3 × Sphere 3))),
      ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ τ ∧
      (∀ x, τ x = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) τ x)) ∧
      (∀ x ∉ closedRegion Φ 2, τ x = t x) ∧
      (∀ p : Sphere 3 × Vector 4, ‖p.2‖ ≤ 3 / 2 → τ (Φ p) = ‖p.2‖ ^ 2 - 1) ∧
      (∀ x, 0 ≤ τ x ↔ 0 ≤ t x ∧ x ∉ openRegion Φ 1) ∧
      D.width ≤ C.width ∧
      (∀ b : B, (D.zeroPoint (Sum.inl b)).val = (C.zeroPoint b).val) ∧
      ∀ s v : Sphere 3, (D.zeroPoint (Sum.inr (s, v))).val = Φ (s, v.val) := by
  obtain ⟨τ, hτ, hτreg, hout, hinner, houter, -, hhalf⟩ :=
    exists_regular_time_modification Φ hΦ t ht hreg hpos
  obtain ⟨D, hw, hOld, hNew⟩ :=
    exists_modified_time_collar Φ hΦ t τ C hpos hout hinner houter
  exact ⟨τ, D, hτ, hτreg, hout, hinner, hhalf, hw, hOld, hNew⟩

end NoExoticSixSphere.SphereFourTube
