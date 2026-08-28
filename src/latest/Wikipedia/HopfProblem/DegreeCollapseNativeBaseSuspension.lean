import Wikipedia.SmoothSixDPoincare.FiberwiseDiffeomorph
import Wikipedia.SmoothSixDPoincare.SupportedRelativeIsotopy
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Dynamics.Flow

/-!
# Suspending an isotopy of an actual native regular level

The base may be a genuine manifold, not a single Euclidean chart. Retain
time to obtain one native diffeomorphism and its smooth inverse, then
conjugate vertical translation to an actual complete smooth flow. This
allows an ambient attaching-sphere isotopy to be realized on the original
regular-level cylinder without assuming its support fits in one chart.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {Z N : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z] [TopologicalSpace N] [ChartedSpace Z N]
  [IsManifold 𝓘(ℝ, Z) ∞ N]

theorem exists_native_base_suspension
    (D : Diffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) N N ∞) {K S : Set N}
    (I : SupportedRelativeIsotopy D K S) :
    ∃ Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ))
        (N × ℝ) (N × ℝ) ∞,
      (∀ p, (Ψ p).2 = p.2) ∧
      (∀ p, p.2 ≤ 1 / 3 → Ψ p = p) ∧
      (∀ p, 2 / 3 ≤ p.2 → Ψ p = (D p.1, p.2)) ∧
      (∀ p, p.1 ∉ K → Ψ p = p) ∧
      ∀ p, p.1 ∈ S → Ψ p = p := by
  let τ : ℝ → ℝ := fun t => Real.smoothTransition (3 * t - 1)
  have hτ : ContDiff ℝ ∞ τ := Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hlow (t : ℝ) (ht : t ≤ 1 / 3) : τ t = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hhigh (t : ℝ) (ht : 2 / 3 ≤ t) : τ t = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  let A : N × ℝ → N := fun p => I.family (τ p.2, p.1)
  have hA : ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Z) ∞ A :=
    I.smooth.comp ((hτ.contMDiff.comp contMDiff_snd).prodMk contMDiff_fst)
  have hslice : ∀ t, ∃ d : Diffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) N N ∞,
      ∀ x, d x = A (x, t) := fun t => I.slices (τ t)
  let Ψ := FiberwiseDiffeomorph.diffeomorph hA hslice
  have hmap (p : N × ℝ) : Ψ p = (I.family (τ p.2, p.1), p.2) := rfl
  refine ⟨Ψ, fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [hmap, hlow p.2 hp, I.zero]
  · intro p hp
    rw [hmap, hhigh p.2 hp, I.one]
  · intro p hp
    rw [hmap, I.fixedOutside (τ p.2) p.1 hp]
  · intro p hp
    rw [hmap, I.fixedOn (τ p.2) p.1 hp]

def nativeSuspensionFlow
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ))
      (N × ℝ) (N × ℝ) ∞) : Flow ℝ (N × ℝ) where
  toFun t p := Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + t)
  cont' := Ψ.continuous.comp
    ((Ψ.symm.continuous.comp continuous_snd).fst.prodMk
      ((Ψ.symm.continuous.comp continuous_snd).snd.add continuous_fst))
  map_zero' p := by simp only [add_zero, Prod.mk.eta, Ψ.apply_symm_apply]
  map_add' s t p := by
    simp only [Ψ.symm_apply_apply]
    congr 1
    apply Prod.ext
    · rfl
    · ring

theorem nativeSuspensionFlow_chart
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ))
      (N × ℝ) (N × ℝ) ∞) (t : ℝ) (p : N × ℝ) :
    nativeSuspensionFlow Ψ t (Ψ p) = Ψ (p.1, p.2 + t) := by
  change Ψ ((Ψ.symm (Ψ p)).1, (Ψ.symm (Ψ p)).2 + t) = _
  rw [Ψ.symm_apply_apply]

theorem contMDiff_nativeSuspensionFlow
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ))
      (N × ℝ) (N × ℝ) ∞) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)))
      (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) ∞ (fun w : ℝ × (N × ℝ) => nativeSuspensionFlow Ψ w.1 w.2) :=
  Ψ.contMDiff.comp (((Ψ.symm.contMDiff.comp contMDiff_snd).fst).prodMk
    (((Ψ.symm.contMDiff.comp contMDiff_snd).snd).add contMDiff_fst))

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
