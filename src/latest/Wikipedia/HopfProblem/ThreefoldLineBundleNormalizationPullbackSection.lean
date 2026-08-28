import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNativeIso

/-!
# A nowhere-zero section from an actual analytic bundle trivialization

The section is the inverse image of the literal constant vector one under
the original fibrewise linear maps. Its total-space map is the original
inverse analytic diffeomorphism composed with the genuine constant-one
section of the native trivial bundle.
-/

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicPicard.NormalizationPullback

open PeriodTorusLineBundleClassificationNative

variable {M E H : Type*} [TopologicalSpace M] [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace H] [ChartedSpace H M]
    {I : ModelWithCorners ℂ E H}

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- The literal constant-one section is analytic for the original topology
and bundle charts of the native trivial line bundle. -/
theorem trivialOneSection_holomorphic (I : ModelWithCorners ℂ E H) :
    ContMDiff I (I.prod I₁) ω
      (fun x : M => (⟨x, (1 : ℂ)⟩ : TotalSpace ℂ (Bundle.Trivial M ℂ))) := by
  intro x
  apply Bundle.contMDiffAt_totalSpace.mpr
  exact ⟨contMDiffAt_id, contMDiffAt_const⟩

variable {V : M → Type*}
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V]

/-- The actual fibrewise inverse image of the vector one. -/
def nonvanishingSection (e : AnalyticBundleIso I V (Bundle.Trivial M ℂ)) (x : M) :
    V x :=
  (e.fiberEquiv x).symm (1 : ℂ)

/-- Its image under the original fibre map is exactly the vector one. -/
@[simp] theorem nonvanishingSection_image
    (e : AnalyticBundleIso I V (Bundle.Trivial M ℂ)) (x : M) :
    e.fiberEquiv x (nonvanishingSection e x) = (1 : ℂ) :=
  (e.fiberEquiv x).apply_symm_apply (1 : ℂ)

/-- No vector in this section is zero, since its actual linear image is one. -/
theorem nonvanishingSection_ne_zero
    (e : AnalyticBundleIso I V (Bundle.Trivial M ℂ)) (x : M) :
    nonvanishingSection e x ≠ 0 := by
  intro h
  have h1 := congrArg (e.fiberEquiv x) h
  rw [nonvanishingSection_image, map_zero] at h1
  exact one_ne_zero h1

/-- The actual total-space section is the original inverse bundle map
applied to the native constant-one section. -/
theorem nonvanishingSection_totalSpace
    (e : AnalyticBundleIso I V (Bundle.Trivial M ℂ)) (x : M) :
    (⟨x, nonvanishingSection e x⟩ : TotalSpace ℂ V) =
      e.diffeomorph.symm (⟨x, (1 : ℂ)⟩ : TotalSpace ℂ (Bundle.Trivial M ℂ)) :=
  (e.symm_map_fiber x (1 : ℂ)).symm

/-- The section is holomorphic in the original total-space atlas, by
composition with the genuine inverse analytic bundle diffeomorphism. -/
theorem nonvanishingSection_holomorphic
    (e : AnalyticBundleIso I V (Bundle.Trivial M ℂ)) :
    ContMDiff I (I.prod I₁) ω
      (fun x => (⟨x, nonvanishingSection e x⟩ : TotalSpace ℂ V)) := by
  have hfun : (fun x => (⟨x, nonvanishingSection e x⟩ : TotalSpace ℂ V)) =
      (fun x => e.diffeomorph.symm
        (⟨x, (1 : ℂ)⟩ : TotalSpace ℂ (Bundle.Trivial M ℂ))) :=
    funext (nonvanishingSection_totalSpace e)
  rw [hfun]
  exact e.diffeomorph.symm.contMDiff.comp (trivialOneSection_holomorphic (M := M) I)

end Wikipedia.HopfProblem.HolomorphicPicard.NormalizationPullback
