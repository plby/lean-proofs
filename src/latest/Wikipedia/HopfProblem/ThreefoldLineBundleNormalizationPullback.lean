import Wikipedia.HopfProblem.PeriodTorusLineBundleChernNativePullbackIso
import Wikipedia.HopfProblem.ThreefoldLineBundleNormalizationPullbackSection

/-!
# Native analytic pullbacks and the original trivial line bundle

Mathlib's pullback retains its original total-space topology and preferred
bundle charts. Its existing analytic-bundle instance and the already proved
pullback of analytic fibre-linear isomorphisms are used without modification.
The pullback of the original trivial bundle is analytically trivial by the
identity on every complex fibre, as verified in those original native charts.
-/

noncomputable section

open Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicPicard.NormalizationPullback

open PeriodTorusLineBundleClassificationNative

variable {M N E H E' H' : Type*}
    [TopologicalSpace M] [TopologicalSpace N]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] [TopologicalSpace H']
    [ChartedSpace H M] [ChartedSpace H' N]
    {I : ModelWithCorners ℂ E H} {J : ModelWithCorners ℂ E' H'}

local notation "I₁" => modelWithCornersSelf ℂ ℂ

section Holomorphic

variable (V : M → Type*) [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V I]

/-- The original pullback family has Mathlib's native holomorphic vector-bundle
structure along the actual holomorphic map. -/
theorem isHolomorphic (f : ContMDiffMap J I N M ω) :
    ContMDiffVectorBundle ω ℂ ((f : N → M) *ᵖ V) J :=
  ContMDiffVectorBundle.pullback ℂ V J f

end Holomorphic

variable (f : ContMDiffMap J I N M ω)

/-- The original pullback and trivial fibres are identified by the literal
identity complex-linear equivalence. -/
def trivialFiberEquiv (x : N) :
    ((f : N → M) *ᵖ (Bundle.Trivial M ℂ)) x ≃ₗ[ℂ] Bundle.Trivial N ℂ x :=
  LinearEquiv.refl ℂ ℂ

/-- Analyticity of the fibre identity is checked in the actual preferred
pullback and trivial bundle charts. -/
theorem trivialTo_holomorphic :
    ContMDiff (J.prod I₁) (J.prod I₁) ω
      (fun v : TotalSpace ℂ ((f : N → M) *ᵖ (Bundle.Trivial M ℂ)) =>
        (⟨v.proj, trivialFiberEquiv f v.proj v.2⟩ :
          TotalSpace ℂ (Bundle.Trivial N ℂ))) := by
  intro v
  have hid : ContMDiffAt (J.prod I₁) (J.prod I₁) ω id v := contMDiffAt_id
  rw [Bundle.contMDiffAt_totalSpace] at hid ⊢
  exact hid

/-- The reverse fibre identity is analytic for the original pullback topology
and preferred charts, not a topology transported from the trivial bundle. -/
theorem trivialFrom_holomorphic :
    ContMDiff (J.prod I₁) (J.prod I₁) ω
      (fun v : TotalSpace ℂ (Bundle.Trivial N ℂ) =>
        (⟨v.proj, (trivialFiberEquiv f v.proj).symm v.2⟩ :
          TotalSpace ℂ ((f : N → M) *ᵖ (Bundle.Trivial M ℂ)))) := by
  intro v
  have hid : ContMDiffAt (J.prod I₁) (J.prod I₁) ω id v := contMDiffAt_id
  rw [Bundle.contMDiffAt_totalSpace] at hid ⊢
  exact hid

/-- The actual analytic, fibrewise complex-linear trivialization of the native
pullback of the original trivial line bundle. -/
def trivialIso :
    AnalyticBundleIso J ((f : N → M) *ᵖ (Bundle.Trivial M ℂ)) (Bundle.Trivial N ℂ) :=
  AnalyticBundleIso.ofFiberEquiv (trivialFiberEquiv f)
    (trivialTo_holomorphic f) (trivialFrom_holomorphic f)

@[simp] theorem trivialIso_apply
    (v : TotalSpace ℂ ((f : N → M) *ᵖ (Bundle.Trivial M ℂ))) :
    (trivialIso f).diffeomorph v = ⟨v.proj, id (α := ℂ) v.2⟩ := rfl

@[simp] theorem trivialIso_symm_apply (v : TotalSpace ℂ (Bundle.Trivial N ℂ)) :
    (trivialIso f).diffeomorph.symm v = ⟨v.proj, v.2⟩ := rfl

@[simp] theorem trivialIso_fiberEquiv_apply (x : N)
    (v : ((f : N → M) *ᵖ (Bundle.Trivial M ℂ)) x) :
    (trivialIso f).fiberEquiv x v = id (α := ℂ) v := rfl

variable {f} {V : M → Type*}
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V]

/-- Pull back a given actual analytic trivialization and compose with the
native trivial-pullback identification. -/
def ofIsoToTrivial (e : AnalyticBundleIso I V (Bundle.Trivial M ℂ))
    (f : ContMDiffMap J I N M ω) :
    AnalyticBundleIso J ((f : N → M) *ᵖ V) (Bundle.Trivial N ℂ) :=
  (e.pullback f).trans (trivialIso f)

/-- The construction retains the original fibre-linear map over the actual
image point of the base map. -/
@[simp] theorem ofIsoToTrivial_apply (e : AnalyticBundleIso I V (Bundle.Trivial M ℂ))
    (f : ContMDiffMap J I N M ω) (v : TotalSpace ℂ ((f : N → M) *ᵖ V)) :
    (ofIsoToTrivial e f).diffeomorph v = ⟨v.proj, e.fiberEquiv (f v.proj) v.2⟩ := rfl

end Wikipedia.HopfProblem.HolomorphicPicard.NormalizationPullback
