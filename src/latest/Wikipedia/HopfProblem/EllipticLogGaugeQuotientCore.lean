import Wikipedia.HopfProblem.EllipticFiniteQuotient
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Holomorphic conjugacies descend to the actual finite orbit quotients

An equivariant analytic diffeomorphism induces the equivalence of orbit
quotients given explicitly on representatives.  Both directions are proved
holomorphic in the covering-lift atlases of the actual quotients.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic.LogGauge

variable (G : Type*) [Group G] {M N : Type*} [MulAction G M] [MulAction G N]

def quotientEquiv (e : M ≃ N) (heq : ∀ (g : G) (x : M), e (g • x) = g • e x) :
    FiniteQuotient.Space G M ≃ FiniteQuotient.Space G N :=
  Quotient.congr e (by
    intro x y
    change (x ∈ MulAction.orbit G y) ↔ (e x ∈ MulAction.orbit G (e y))
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨g, (heq g y).symm.trans (congrArg e hg)⟩
    · rintro ⟨g, hg⟩
      exact ⟨g, e.injective ((heq g y).trans hg)⟩)

@[simp] theorem quotientEquiv_project (e : M ≃ N)
    (heq : ∀ (g : G) (x : M), e (g • x) = g • e x) (x : M) :
    quotientEquiv G e heq (FiniteQuotient.project G M x) =
      FiniteQuotient.project G N (e x) := rfl

@[simp] theorem quotientEquiv_symm_project (e : M ≃ N)
    (heq : ∀ (g : G) (x : M), e (g • x) = g • e x) (y : N) :
    (quotientEquiv G e heq).symm (FiniteQuotient.project G N y) =
      FiniteQuotient.project G M (e.symm y) := rfl

section ComplexStructure

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    [IsManifold (modelWithCornersSelf ℂ E) ω M]
    [IsManifold (modelWithCornersSelf ℂ F) ω N]
    [Finite G] [LocallyCompactSpace M] [T2Space M]
    [LocallyCompactSpace N] [T2Space N]
    [ContinuousConstSMul G M] [IsCancelSMul G M]
    [ContinuousConstSMul G N] [IsCancelSMul G N]
    (hM : ∀ g : G, ContMDiff (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E) ω (fun x : M => g • x))
    (hN : ∀ g : G, ContMDiff (modelWithCornersSelf ℂ F)
      (modelWithCornersSelf ℂ F) ω (fun y : N => g • y))
    (e : Diffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F) M N ω)
    (heq : ∀ (g : G) (x : M), e (g • x) = g • e x)

/-- The descended analytic diffeomorphism uses the genuine finite-orbit
quotients and their covering-lift atlases on both sides. -/
def quotientBiholomorph :
    letI := FiniteQuotient.chartedSpace (E := E) G M
    letI := FiniteQuotient.chartedSpace (E := F) G N
    Diffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F)
      (FiniteQuotient.Space G M) (FiniteQuotient.Space G N) ω := by
  let := FiniteQuotient.chartedSpace (E := E) G M
  let := FiniteQuotient.chartedSpace (E := F) G N
  refine
    { toEquiv := quotientEquiv G e.toEquiv heq
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · apply CoveringQuotient.contMDiff_of_comp
      (FiniteQuotient.project_isQuotientCoveringMap G M) (modelWithCornersSelf ℂ F) ω
    exact (FiniteQuotient.project_holomorphic G N hN).comp e.contMDiff
  · apply CoveringQuotient.contMDiff_of_comp
      (FiniteQuotient.project_isQuotientCoveringMap G N) (modelWithCornersSelf ℂ E) ω
    exact (FiniteQuotient.project_holomorphic G M hM).comp e.symm.contMDiff

@[simp] theorem quotientBiholomorph_project (x : M) :
    quotientBiholomorph G hM hN e heq (FiniteQuotient.project G M x) =
      FiniteQuotient.project G N (e x) := rfl

@[simp] theorem quotientBiholomorph_symm_project (y : N) :
    letI := FiniteQuotient.chartedSpace (E := E) G M
    letI := FiniteQuotient.chartedSpace (E := F) G N
    (quotientBiholomorph G hM hN e heq).symm (FiniteQuotient.project G N y) =
      FiniteQuotient.project G M (e.symm y) := by
  let := FiniteQuotient.chartedSpace (E := E) G M
  let := FiniteQuotient.chartedSpace (E := F) G N
  rfl

end ComplexStructure

end Wikipedia.HopfProblem.Elliptic.LogGauge
