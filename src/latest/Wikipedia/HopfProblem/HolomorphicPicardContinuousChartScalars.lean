import Wikipedia.HopfProblem.HolomorphicPicardContinuousCoreBasic
import Wikipedia.HopfProblem.HolomorphicCharacterBundleCoreSections

/-!
# Scalar coordinates of a continuous line-bundle trivialization

In every original bundle chart, a fibrewise linear trivialization is
multiplication by a continuous nonzero scalar. This records the actual
scalar, including at zeros of sections, so division by a vanishing
section is never used to define it.
-/

noncomputable section

open Set Topology Bundle

namespace Wikipedia.HopfProblem.HolomorphicPicard.ContinuousTrivialization

variable {M ι : Type*} [TopologicalSpace M]
  (A : HolomorphicCharacterBundle.TransitionData M ι)
  (T : ContinuousTrivialization A.core.Fiber)

def chartScalar (i : ι) (x : M) : ℂ :=
  T.fiberEquiv x (A.transition i (A.indexAt x) x : ℂ)

theorem chartScalar_ne_zero (i : ι) (x : M) : chartScalar A T i x ≠ 0 :=
  (T.fiberEquiv x).map_eq_zero_iff.not.mpr (A.transition_ne_zero i (A.indexAt x) x)

theorem chartScalar_continuousOn (i : ι) :
    ContinuousOn (chartScalar A T i) (A.baseSet i) := by
  have h := T.homeomorph.continuous.comp_continuousOn
    ((A.core.localTriv i).continuousOn_symm.comp
      (continuous_id.prodMk (continuous_const : Continuous (fun _ : M => (1 : ℂ)))).continuousOn
      (fun x hx => show (x, (1 : ℂ)) ∈ (A.core.localTriv i).target from ⟨hx, mem_univ _⟩))
  have hs := h.snd
  simp only [Function.comp_def, map_fiber, id_eq] at hs
  apply hs.congr
  intro x hx
  change chartScalar A T i x = T.fiberEquiv x ((A.core.localTriv i).symm x 1)
  rw [A.core_localTriv_fiber_symm i hx, mul_one]
  rfl

theorem sectionFromLocal_eq_mul_chartScalar (f : ι → M → ℂ) (hf : A.IsCompatible f)
    (i : ι) {x : M} (hx : x ∈ A.baseSet i) :
    T.fiberEquiv x (A.sectionFromLocal f x) = f i x * chartScalar A T i x := by
  have he := hf i (A.indexAt x) x ⟨hx, A.mem_baseSet_at x⟩
  change T.fiberEquiv x (f (A.indexAt x) x) = _
  rw [← he]
  have h := (show ℂ ≃ₗ[ℂ] ℂ from T.fiberEquiv x).map_smul (f i x)
    (A.transition i (A.indexAt x) x : ℂ)
  change T.fiberEquiv x (f i x * (A.transition i (A.indexAt x) x : ℂ)) =
    f i x * chartScalar A T i x at h
  exact (congrArg (T.fiberEquiv x)
    (mul_comm (A.transition i (A.indexAt x) x : ℂ) (f i x))).trans h

end Wikipedia.HopfProblem.HolomorphicPicard.ContinuousTrivialization
