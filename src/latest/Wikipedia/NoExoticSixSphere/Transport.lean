import Wikipedia.NoExoticSixSphere.Definitions

/-!
# Transporting a smooth atlas along a homeomorphism

Transport changes the smooth structure on the source. It does not show that a
homeomorphism is smooth for an independently specified source atlas.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere

universe u v

section Transport

variable {n : ℕ} {M : Type u} {N : Type v}
  [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]

/-- Pull back the target atlas. The pre-existing topology on the source is retained. -/
@[instance_reducible]
def pullbackAtlas (e : M ≃ₜ N) : ChartedSpace (EuclideanSpace ℝ (Fin n)) M where
  atlas := e.transOpenPartialHomeomorph '' atlas (EuclideanSpace ℝ (Fin n)) N
  chartAt x := e.transOpenPartialHomeomorph (chartAt (EuclideanSpace ℝ (Fin n)) (e x))
  mem_chart_source x := mem_chart_source (EuclideanSpace ℝ (Fin n)) (e x)
  chart_mem_atlas _x := ⟨_, chart_mem_atlas _ _, rfl⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] in
/-- Transport leaves coordinate changes unchanged. -/
theorem pullback_transition (e : M ≃ₜ N)
    (f g : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin n))) :
    (e.transOpenPartialHomeomorph f).symm.trans (e.transOpenPartialHomeomorph g) =
      f.symm.trans g := by
  simp only [Homeomorph.transOpenPartialHomeomorph_eq_trans,
    OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
    ← Homeomorph.symm_toOpenPartialHomeomorph]
  rw [← OpenPartialHomeomorph.trans_assoc e.symm.toOpenPartialHomeomorph
    e.toOpenPartialHomeomorph g, ← Homeomorph.trans_toOpenPartialHomeomorph]
  simp

/-- A pulled-back smooth atlas is smooth. This does not assert that it agrees with
any other atlas on the same source space. -/
theorem pullback_isManifold (e : M ≃ₜ N) [IsManifold (𝓡 n) ∞ N] :
    letI := pullbackAtlas (n := n) e
    IsManifold (𝓡 n) ∞ M := by
  let _ := pullbackAtlas (n := n) e
  refine { compatible := ?_ }
  rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
  rw [pullback_transition]
  exact (contDiffGroupoid ∞ (𝓡 n)).compatible hf hg

/-- The preferred extended chart in the pulled-back atlas. -/
theorem pullback_extChartAt_apply (e : M ≃ₜ N) (x y : M) :
    letI := pullbackAtlas (n := n) e
    extChartAt (𝓡 n) x y = extChartAt (𝓡 n) (e x) (e y) :=
  rfl

/-- The inverse extended chart in the pulled-back atlas. -/
theorem pullback_extChartAt_symm_apply (e : M ≃ₜ N) (x : M)
    (y : EuclideanSpace ℝ (Fin n)) :
    letI := pullbackAtlas (n := n) e
    (extChartAt (𝓡 n) x).symm y = e.symm ((extChartAt (𝓡 n) (e x)).symm y) :=
  rfl

/-- The transporting map is smooth for the atlas it pulls back. -/
theorem pullback_contMDiff (e : M ≃ₜ N) :
    letI := pullbackAtlas (n := n) e
    ContMDiff (𝓡 n) (𝓡 n) ∞ e := by
  let _ := pullbackAtlas (n := n) e
  intro x
  refine contMDiffAt_iff.mpr ⟨e.continuous.continuousAt, ?_⟩
  have h := (contMDiffAt_iff.mp
    ((contMDiff_id : ContMDiff (𝓡 n) (𝓡 n) ∞ (id : N → N)) (e x))).2
  simpa only [Function.comp_def, pullback_extChartAt_symm_apply,
    pullback_extChartAt_apply, Homeomorph.apply_symm_apply, id_eq] using h

/-- The inverse transporting map is smooth for the pulled-back atlas as well. -/
theorem pullback_symm_contMDiff (e : M ≃ₜ N) :
    letI := pullbackAtlas (n := n) e
    ContMDiff (𝓡 n) (𝓡 n) ∞ e.symm := by
  let _ := pullbackAtlas (n := n) e
  intro y
  refine contMDiffAt_iff.mpr ⟨e.symm.continuous.continuousAt, ?_⟩
  have h := (contMDiffAt_iff.mp
    ((contMDiff_id : ContMDiff (𝓡 n) (𝓡 n) ∞ (id : N → N)) y)).2
  simpa only [Function.comp_def, pullback_extChartAt_apply,
    Homeomorph.apply_symm_apply, id_eq] using h

/-- A homeomorphism becomes a diffeomorphism after pulling back the target atlas.
The source atlas here is `pullbackAtlas e`, not an arbitrary given smooth atlas. -/
def pullbackDiffeomorph (e : M ≃ₜ N) :
    letI := pullbackAtlas (n := n) e
    M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N := by
  let _ := pullbackAtlas (n := n) e
  exact
    { toEquiv := e.toEquiv
      contMDiff_toFun := pullback_contMDiff (n := n) e
      contMDiff_invFun := pullback_symm_contMDiff (n := n) e }

end Transport

/-- Classification in the base universe suffices in every universe: transport the
given atlas to the small standard sphere, classify that atlas, and transport back.
This is only a universe reduction; its classification premise remains unproved. -/
theorem sixSphereRigidity_universeLift (h : SixSphereRigidity.{0}) :
    SixSphereRigidity.{u} := by
  intro M _ _ _ he
  obtain ⟨e⟩ := he
  obtain ⟨d⟩ := h (Sphere 6) inferInstance (pullbackAtlas (n := 6) e.symm)
    (pullback_isManifold (n := 6) e.symm) ⟨Homeomorph.refl _⟩
  -- The two occurrences of `Sphere 6` have different atlases. Pass the charted-space
  -- arguments explicitly, so typeclass inference cannot replace the transported one.
  let inverse := @Diffeomorph.symm ℝ _
    _ _ _  _ _ _  _ _  _ _  (𝓡 6) (𝓡 6)
    (Sphere 6) _ (pullbackAtlas (n := 6) e.symm) M _ _ ∞
    (pullbackDiffeomorph (n := 6) e.symm)
  exact ⟨@Diffeomorph.trans ℝ _
    _ _ _  _ _ _  _ _ _  _ _  _ _  _ _  (𝓡 6) (𝓡 6) (𝓡 6)
    M _ _ (Sphere 6) _ (pullbackAtlas (n := 6) e.symm) (Sphere 6) _ _ ∞ inverse d⟩

end NoExoticSixSphere
