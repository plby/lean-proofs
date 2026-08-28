import Wikipedia.SmoothSixDPoincare.LocalInverseIntoManifold
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Smooth diffeomorphisms from small Lipschitz perturbations of the identity

Injectivity follows from the quantitative lower distance bound. Surjectivity
is proved by the contraction mapping theorem, and the derivative is invertible
everywhere. The smooth local inverse theorem then gives a genuine global
diffeomorphism, rather than only a smooth bijection.
-/

noncomputable section

open Function
open scoped ContDiff Manifold NNReal

namespace Wikipedia.SmoothSixDPoincare.SmallPerturbation

variable {E : Type*} [NormedAddCommGroup E]

/-- A Lipschitz perturbation smaller than the identity cannot identify distinct points. -/
theorem injective_id_add {u : E → E} {k : ℝ≥0} (hu : LipschitzWith k u) (hk : k < 1) :
    Injective (fun x => x + u x) :=
  (AntilipschitzWith.id.add_lipschitzWith hu (by simpa only [inv_one] using hk)).injective

variable [CompleteSpace E]

/-- Every target point is reached, by solving the actual contraction equation. -/
theorem surjective_id_add {u : E → E} {k : ℝ≥0} (hu : LipschitzWith k u) (hk : k < 1) :
    Surjective (fun x => x + u x) := by
  intro y
  have hlip : LipschitzWith k (fun x => y - u x) := by
    simpa only [zero_add] using (LipschitzWith.const y).sub hu
  have hc : ContractingWith k (fun x => y - u x) := ⟨hk, hlip⟩
  let x := ContractingWith.fixedPoint (fun x => y - u x) hc
  refine ⟨x, ?_⟩
  have hx : y - u x = x := hc.fixedPoint_isFixedPt.eq
  exact eq_sub_iff_add_eq.mp hx.symm

theorem bijective_id_add {u : E → E} {k : ℝ≥0} (hu : LipschitzWith k u) (hk : k < 1) :
    Bijective (fun x => x + u x) := ⟨injective_id_add hu hk, surjective_id_add hu hk⟩

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
/-- The actual derivative of the perturbation is invertible at every point. -/
theorem isInvertible_fderiv_id_add {u : E → E} {k : ℝ≥0}
    (hs : ContDiff ℝ ∞ u) (hu : LipschitzWith k u) (hk : k < 1) (x : E) :
    (fderiv ℝ (fun y => y + u y) x).IsInvertible := by
  have hn : ‖fderiv ℝ u x‖ < 1 :=
    (norm_fderiv_le_of_lipschitz ℝ hu).trans_lt (show (k : ℝ) < 1 from hk)
  have hnn : ‖fderiv ℝ u x‖₊ < 1 := hn
  have hi : Injective (ContinuousLinearMap.id ℝ E + fderiv ℝ u x) :=
    injective_id_add (fderiv ℝ u x).lipschitz hnn
  have hd : fderiv ℝ (fun y => y + u y) x = ContinuousLinearMap.id ℝ E + fderiv ℝ u x :=
    ((hasFDerivAt_id x).add (hs.contDiffAt.differentiableAt (by simp)).hasFDerivAt).fderiv
  rw [hd]
  let L := (LinearEquiv.ofInjectiveEndo
    (ContinuousLinearMap.id ℝ E + fderiv ℝ u x).toLinearMap hi).toContinuousLinearEquiv
  exact ⟨L, by ext v; rfl⟩

/-- The small smooth perturbation has a constructed global smooth inverse. -/
def diffeomorphIdAdd {u : E → E} {k : ℝ≥0}
    (hs : ContDiff ℝ ∞ u) (hu : LipschitzWith k u) (hk : k < 1) :
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ := by
  have hloc : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun x => x + u x) := by
    intro x
    apply isLocalDiffeomorphAt_of_contMDiffOn isOpen_univ (Set.mem_univ x)
      (contDiff_id.add hs).contMDiff.contMDiffOn
    rw [mfderiv_eq_fderiv]
    exact isInvertible_fderiv_id_add hs hu hk x
  exact hloc.diffeomorphOfBijective (bijective_id_add hu hk)

theorem diffeomorphIdAdd_apply {u : E → E} {k : ℝ≥0}
    (hs : ContDiff ℝ ∞ u) (hu : LipschitzWith k u) (hk : k < 1) (x : E) :
    diffeomorphIdAdd hs hu hk x = x + u x := rfl

end Wikipedia.SmoothSixDPoincare.SmallPerturbation
