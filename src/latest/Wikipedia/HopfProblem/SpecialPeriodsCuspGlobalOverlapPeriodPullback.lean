import Wikipedia.HopfProblem.PeriodFamily
import Wikipedia.HopfProblem.CuspPuncturedCovering
import Wikipedia.HopfProblem.SpecialPeriodsEllipticFillingRestriction

/-!
# Actual period-family comparison under a change of base

Equality of the actual period points identifies the real period
isomorphisms and makes the literal map `(b, t) ↦ (f b, t)` commute with
the complex vector-cover projections.  Holomorphicity and local
biholomorphicity then descend through the genuine covering maps to the
named period-family atlases.  No comparison of families is assumed.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem

section LocalDiffeomorphismDescent

variable {E F F' H K K' M N R : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup F'] [NormedSpace ℂ F']
    [TopologicalSpace H] [TopologicalSpace K] [TopologicalSpace K']
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace K N]
    [TopologicalSpace R] [ChartedSpace K' R]
    (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ F K)
    (L : ModelWithCorners ℂ F' K')

/-- Cancelling a local analytic diffeomorphism on the source preserves
local analytic invertibility at the actual image point. -/
theorem isLocalDiffeomorphAt_of_comp_localDiffeomorph {f : M → N} {g : N → R} {x : M}
    (hf : IsLocalDiffeomorphAt I J ω f x)
    (hgf : IsLocalDiffeomorphAt I L ω (g ∘ f) x) :
    IsLocalDiffeomorphAt J L ω g (f x) := by
  obtain ⟨φ, hx, he⟩ := hgf
  have hinv : hf.localInverse (f x) = x :=
    hf.localInverse_left_inv hf.localInverse_mem_target
  refine ⟨hf.localInverse.trans φ, ⟨hf.localInverse_mem_source, ?_⟩, ?_⟩
  · change hf.localInverse (f x) ∈ φ.source
    rwa [hinv]
  · intro y hy
    change g y = φ (hf.localInverse y)
    exact (congrArg g (hf.localInverse_right_inv hy.1).symm).trans (he hy.2)

/-- Local analytic invertibility descends through a surjective local
analytic diffeomorphism, with the existing source and target atlases. -/
theorem isLocalDiffeomorph_of_comp_surjective {f : M → N} {g : N → R}
    (hf : IsLocalDiffeomorph I J ω f) (hsurj : Function.Surjective f)
    (hgf : IsLocalDiffeomorph I L ω (g ∘ f)) : IsLocalDiffeomorph J L ω g := by
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  exact isLocalDiffeomorphAt_of_comp_localDiffeomorph I J L (hf x) (hgf x)

end LocalDiffeomorphismDescent

namespace HolomorphicPeriodMap

section QuotientProjection

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B]
    [IsManifold (modelWithCornersSelf ℂ V) ω B]
    (P : HolomorphicPeriodMap V B)

local instance periodPullbackCoveringChartedSpace :
    ChartedSpace (V × ComplexPlane₂) (B × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd V ComplexPlane₂) (B × ComplexPlane₂))

local instance periodPullbackCoveringManifold :
    IsManifold (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (B × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := modelWithCornersSelf ℂ V)
    (I' := modelWithCornersSelf ℂ ComplexPlane₂) B ComplexPlane₂

/-- The actual vector-cover projection of any holomorphic period family
is locally biholomorphic for its named covering-quotient complex atlas. -/
theorem quotientMap_isLocalDiffeomorph :
    letI := P.totalChartedSpace
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω P.quotientMap := by
  let := P.coveringAction
  let := P.totalChartedSpace
  exact CoveringQuotient.project_isLocalDiffeomorph
    P.quotientCoveringMap P.coveringAction_holomorphic

end QuotientProjection

section BaseComparison

variable {B C : Type*} [TopologicalSpace B] [ChartedSpace ℂ B]
    [TopologicalSpace C] [ChartedSpace ℂ C]
    (P : HolomorphicPeriodMap ℂ B) (Q : HolomorphicPeriodMap ℂ C) (f : B → C)

/-- The literal base-change map of the actual topological total spaces. -/
def periodPullbackMap : P.TotalSpace → Q.TotalSpace :=
  fun x => (f x.1, x.2)

/-- The same base-change map on the actual complex vector covers. -/
def periodPullbackVectorMap : (B × ComplexPlane₂) → (C × ComplexPlane₂) :=
  fun x => (f x.1, x.2)

@[simp] theorem periodPullbackMap_apply (x : P.TotalSpace) :
    periodPullbackMap P Q f x = (f x.1, x.2) := rfl

omit [TopologicalSpace B] [ChartedSpace ℂ B] [TopologicalSpace C] [ChartedSpace ℂ C] in
@[simp] theorem periodPullbackVectorMap_apply (x : B × ComplexPlane₂) :
    periodPullbackVectorMap f x = (f x.1, x.2) := rfl

@[simp] theorem periodPullbackMap_projection (x : P.TotalSpace) :
    Q.projection (periodPullbackMap P Q f x) = f (P.projection x) := rfl

theorem periodPullbackMap_continuous (hf : Continuous f) :
    Continuous (periodPullbackMap P Q f) :=
  (hf.comp continuous_fst).prodMk continuous_snd

/-- Equal period points give equal actual real period isomorphisms. -/
theorem periodEquiv_pullback_eq (hpoint : ∀ b, Q.point (f b) = P.point b) (b : B) :
    Q.periodEquiv (f b) = P.periodEquiv b := by
  simp only [periodEquiv, hpoint b]

/-- The exact vector-cover diagram for the actual family comparison. -/
theorem periodPullbackMap_quotientMap (hpoint : ∀ b, Q.point (f b) = P.point b)
    (x : B × ComplexPlane₂) :
    periodPullbackMap P Q f (P.quotientMap x) = Q.quotientMap (periodPullbackVectorMap f x) := by
  change (f x.1, standardLattice.mkQ ((P.periodEquiv x.1).symm x.2)) =
    (f x.1, standardLattice.mkQ ((Q.periodEquiv (f x.1)).symm x.2))
  rw [periodEquiv_pullback_eq P Q f hpoint]

theorem periodPullbackMap_comp_quotientMap (hpoint : ∀ b, Q.point (f b) = P.point b) :
    periodPullbackMap P Q f ∘ P.quotientMap = Q.quotientMap ∘ periodPullbackVectorMap f :=
  funext (periodPullbackMap_quotientMap P Q f hpoint)

local instance periodPullbackSourceVectorChartedSpace :
    ChartedSpace (ℂ × ComplexPlane₂) (B × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (B × ComplexPlane₂))

local instance periodPullbackTargetVectorChartedSpace :
    ChartedSpace (ℂ × ComplexPlane₂) (C × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (C × ComplexPlane₂))

theorem periodPullbackVectorMap_holomorphic (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (periodPullbackVectorMap f) := by
  rw [modelWithCornersSelf_prod]
  exact (hf.comp contMDiff_fst).prodMk contMDiff_snd

/-- The proved actual local base charts extend with unchanged vector
coordinates to local analytic inverse charts on the vector covers. -/
theorem periodPullbackVectorMap_isLocalDiffeomorph (hf : IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω f) :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (periodPullbackVectorMap f) :=
  SpecialPeriods.EllipticFilling.productMap_isLocalDiffeomorph hf

variable [IsManifold 𝓘(ℂ) ω B] [IsManifold 𝓘(ℂ) ω C]

local instance periodPullbackSourceVectorManifold :
    IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (B × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℂ)) (I' := modelWithCornersSelf ℂ ComplexPlane₂) B ComplexPlane₂

local instance periodPullbackTargetVectorManifold :
    IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (C × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℂ)) (I' := modelWithCornersSelf ℂ ComplexPlane₂) C ComplexPlane₂

/-- Holomorphicity follows from the actual complex vector-cover
diagram, rather than from the real-coordinate product trivialization. -/
theorem periodPullbackMap_holomorphic (hpoint : ∀ b, Q.point (f b) = P.point b)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    letI := P.totalChartedSpace
    letI := Q.totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (periodPullbackMap P Q f) := by
  let := P.coveringAction
  let := P.totalChartedSpace
  let := Q.totalChartedSpace
  apply CoveringQuotient.contMDiff_of_comp (E := ℂ × ComplexPlane₂)
    P.quotientCoveringMap (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω
  rw [periodPullbackMap_comp_quotientMap P Q f hpoint]
  exact Q.quotientMap_holomorphic.comp (periodPullbackVectorMap_holomorphic f hf)

/-- An actual local biholomorphism of bases with equal period points
induces a local biholomorphism of the actual period-family total spaces.
This uses the existing covering-descent theorem for period families. -/
theorem periodPullbackMap_isLocalDiffeomorph (hpoint : ∀ b, Q.point (f b) = P.point b)
    (hf : IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω f) :
    letI := P.totalChartedSpace
    letI := Q.totalChartedSpace
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (periodPullbackMap P Q f) := by
  let := P.totalChartedSpace
  let := Q.totalChartedSpace
  exact SpecialPeriods.EllipticFilling.periodFamilyMap_isLocalDiffeomorph
    P Q f (fun b => (hpoint b).symm) hf

theorem periodPullbackMap_isLocalHomeomorph (hpoint : ∀ b, Q.point (f b) = P.point b)
    (hf : IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω f) :
    IsLocalHomeomorph (periodPullbackMap P Q f) := by
  let := P.totalChartedSpace
  let := Q.totalChartedSpace
  exact (periodPullbackMap_isLocalDiffeomorph P Q f hpoint hf).isLocalHomeomorph

theorem periodPullbackMap_isOpenMap (hpoint : ∀ b, Q.point (f b) = P.point b)
    (hf : IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω f) : IsOpenMap (periodPullbackMap P Q f) :=
  (periodPullbackMap_isLocalHomeomorph P Q f hpoint hf).isOpenMap

end BaseComparison

end HolomorphicPeriodMap

end Wikipedia.HopfProblem
