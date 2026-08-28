import Wikipedia.HopfProblem.DegreeCollapseFourBasinParameterUnit
import Wikipedia.HopfProblem.DegreeCollapseCommonCutFourPrescribedSlide

/-!
# The prescribed four-handle slide retains the exact original basin parametrization

Canonicalize the central sphere only inside the construction. The old and
canonical maps have the same image and differ on homology by an integral
unit. Compensate for this unit before making the slide, so restoring the
exact old central map retains the requested coefficient. No canonical
orbit formula is an input.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

local notation "S₃" => Hemisphere.Sphere 3

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_common_cut_four_family_slide
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (hdim : Module.finrank ℝ E = 7)
    (q : criticalPoints E f) (hq : nativeMorseIndex E f q = 4)
    (hprefix : ∀ j : Fin S.toSurgeryWindows.count, 0 < j.val →
      f (S.toSurgeryWindows.point j) ≤ f q →
      Module.finrank ℝ (S.data (S.toSurgeryWindows.point j)).chart.NegativeCoordinates = 3 ∨
      Module.finrank ℝ (S.data (S.toSurgeryWindows.point j)).chart.NegativeCoordinates = 4)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hal : a < S.toSurgeryWindows.lower q)
    (hband : ∀ y, f y ∈ Icc a (S.toSurgeryWindows.lower q) → y ∉ criticalPoints E f)
    {n : ℕ} (p : Fin n → criticalPoints E f) (i : Fin n)
    (hp : ∀ j, nativeMorseIndex E f (p j) = 4)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (αq : C(S₃, {y : M // f y = a})) (α : Fin n → C(S₃, {y : M // f y = a}))
    (hfamily : IsNativeFourBasinFamily S hf ha (Fin.cases q p)
      (Fin.cases αq (fun j => α j)))
    (k : ℤ) (hk : k = 1 ∨ k = -1)
    (ε : criticalPoints E f → ℝ) (hε : ∀ z, 0 < ε z) :
    ∃ T : AdaptedSurgeryWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
      (∀ z, (T.data z).radius < ε z) ∧
      (∀ z ∈ criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
      ∃ Γ : Fin n → C(S₃, {y : M // f y = a}),
        IsNativeFourBasinFamily T hf ha (Fin.cases q p) (Fin.cases αq (fun j => Γ j)) ∧
        (∀ j, j ≠ i → Γ j = α j) ∧
        (threeSectionClass (Γ i) = threeSectionClass (α i) + k • threeSectionClass αq) ∧
        ∀ z : M, f z ≤ f q →
          (∀ x, Tendsto (fun t => T.flow t x) atBot (𝓝 z) ↔
            Tendsto (fun t => S.flow t x) atBot (𝓝 z)) ∧
          (∀ x, Tendsto (fun t => S.flow t x) atBot (𝓝 z) →
            range (fun t => T.flow t x) = range (fun t => S.flow t x)) ∧
          ∀ v, Tendsto (fun t => T.flow t z) atTop (𝓝 v) ↔
            Tendsto (fun t => S.flow t z) atTop (𝓝 v) := by
  let _ := RegularLevel.chartedSpace hf ha
  obtain ⟨βq, hβs, hβe, hβi, hrange, horbit, -⟩ :=
    S.exists_canonical_four_basin_sphere hf q hq ha αq (Hemisphere.point true ⟨0, by simp⟩)
      (hfamily.2.2.2.2 0)
  have hβfamily := nativeFourBasinFamily_replace_zero S hf ha q p αq βq α hfamily
    hrange hβs hβe hβi
  obtain ⟨u, hu, hunit⟩ := same_image_three_section_classes_unit αq βq
    (hfamily.2.1 0).isEmbedding hβe.isEmbedding hrange
  have hku : k * u = 1 ∨ k * u = -1 := by
    rcases hk with rfl | rfl <;> rcases hu with rfl | rfl <;> norm_num
  obtain ⟨T, hcharts, hradii, hgerms, Γ, hΓ, hother, hclass, hkeep⟩ :=
    S.exists_common_cut_four_prescribed_slide hf hm hdim q hq hprefix ha hal hband p i hp hhigh
      βq α hβfamily horbit (k * u) hku ε hε
  have hrestored := nativeFourBasinFamily_replace_zero T hf ha q p βq αq Γ hΓ
    hrange.symm (hfamily.1 0) (hfamily.2.1 0) (hfamily.2.2.1 0)
  have hcancel : (k * u) * u = k := by
    rcases hu with rfl | rfl <;> ring
  refine ⟨T, hcharts, hradii, hgerms, Γ, hrestored, hother, ?_, hkeep⟩
  rw [hclass, hunit, ← mul_smul, hcancel]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

