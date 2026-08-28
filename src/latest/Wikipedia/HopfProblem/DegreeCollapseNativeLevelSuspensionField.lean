import Wikipedia.HopfProblem.DegreeCollapseNativeBaseSuspension
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Smooth native generator fields on a manifold-based level suspension

The vertical field on the genuine product manifold is a smooth section.
Push it through the actual suspension diffeomorphism using its tangent
map. This constructs the smooth native generator without identifying the
regular level with a Euclidean chart.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {Z N : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z] [TopologicalSpace N] [ChartedSpace Z N]
  [IsManifold 𝓘(ℝ, Z) ∞ N]

def nativeVerticalField (p : N × ℝ) : TangentSpace (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) p :=
  (show Z × ℝ from (0, 1))

theorem contMDiff_nativeVerticalField :
    ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun p : N × ℝ => (⟨p, nativeVerticalField p⟩ :
        TangentBundle (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ))) := by
  have hz : ContMDiff 𝓘(ℝ, Z) (𝓘(ℝ, Z).tangent) ∞
      (fun x : N => (⟨x, (0 : Z)⟩ : TangentBundle 𝓘(ℝ, Z) N)) :=
    Bundle.contMDiff_zeroSection ℝ (TangentSpace 𝓘(ℝ, Z) : N → Type _)
  have ho : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).tangent) ∞
      (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    have hpair : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).tangent) ∞
        (fun t : ℝ => (show ModelProd ℝ ℝ from (t, 1))) := by
      unfold ModelWithCorners.tangent
      rw [← modelWithCornersSelf_prod]
      exact (contDiff_id.prodMk contDiff_const).contMDiff
    exact (contMDiff_tangentBundleModelSpaceHomeomorph_symm
      (I := 𝓘(ℝ, ℝ)) (n := ∞)).comp hpair
  have hp := (contMDiff_equivTangentBundleProd_symm
    (I := 𝓘(ℝ, Z)) (I' := 𝓘(ℝ, ℝ)) (M := N) (M' := ℝ) (n := ∞)).comp
      ((hz.comp contMDiff_fst).prodMk (ho.comp contMDiff_snd))
  exact hp

def nativeSuspensionField
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ))
      (N × ℝ) (N × ℝ) ∞) (p : N × ℝ) :
    TangentSpace (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) p :=
  mfderiv (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) Ψ
    (Ψ.symm p) (nativeVerticalField (Ψ.symm p))

theorem contMDiff_nativeSuspensionField
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ))
      (N × ℝ) (N × ℝ) ∞) :
    ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun p : N × ℝ => (⟨p, nativeSuspensionField Ψ p⟩ :
        TangentBundle (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (N × ℝ))) := by
  have ht := (Ψ.contMDiff.contMDiff_tangentMap (m := ∞) (by simp)).comp
    (contMDiff_nativeVerticalField.comp Ψ.symm.contMDiff)
  convert! ht using 1
  funext p
  apply Bundle.TotalSpace.ext (Ψ.apply_symm_apply p).symm
  rfl

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
