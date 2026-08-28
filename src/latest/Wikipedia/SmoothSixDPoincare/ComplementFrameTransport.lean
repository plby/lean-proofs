import Wikipedia.SmoothSixDPoincare.SmoothComplementQuotient

/-!
# Transport a prescribed complement through an actual frame splitting

The change of frame carries the old first columns to the new first columns.
It therefore carries every complement of the old first columns to a complement
of the new ones, and is exactly the identity when the two splittings coincide.
-/

noncomputable section

open Function Set
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.FrameField

variable {D Z F : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem bijective_coprod_comm (W : D →L[ℝ] F) (H : Z →L[ℝ] F)
    (hi : Bijective (H.coprod W)) : Bijective (W.coprod H) := by
  have heq : W.coprod H = (H.coprod W).comp
      (ContinuousLinearEquiv.prodComm ℝ D Z).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro p
    change W p.1 + H p.2 = H p.2 + W p.1
    exact add_comm _ _
  rw [heq]
  exact hi.comp (ContinuousLinearEquiv.prodComm ℝ D Z).bijective

def transportComplement (W : D →L[ℝ] F) (B : Z →L[ℝ] F)
    (W₀ : D →L[ℝ] F) (B₀ H : Z →L[ℝ] F) : Z →L[ℝ] F :=
  (W.coprod B).comp ((W₀.coprod B₀).inverse.comp H)

theorem transportComplement_self (W : D →L[ℝ] F) (B H : Z →L[ℝ] F)
    (h : (W.coprod B).IsInvertible) : transportComplement W B W B H = H := by
  apply ContinuousLinearMap.ext
  intro z
  exact h.self_apply_inverse (H z)

/-- The entire transported frame is the actual change of splitting applied to the old frame. -/
theorem coprod_transportComplement (W : D →L[ℝ] F) (B : Z →L[ℝ] F)
    (W₀ : D →L[ℝ] F) (B₀ H : Z →L[ℝ] F) (h₀ : (W₀.coprod B₀).IsInvertible) :
    W.coprod (transportComplement W B W₀ B₀ H) =
      ((W.coprod B).comp (W₀.coprod B₀).inverse).comp (W₀.coprod H) := by
  have hfirst (u : D) : (W₀.coprod B₀).inverse (W₀ u) = (u, 0) := by
    simpa only [ContinuousLinearMap.coprod_apply, map_zero, add_zero] using
      h₀.inverse_apply_self (u, 0)
  apply ContinuousLinearMap.ext
  intro p
  simp only [transportComplement, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coprod_apply, map_add, hfirst, map_zero, add_zero]

theorem bijective_transportComplement (W : D →L[ℝ] F) (B : Z →L[ℝ] F)
    (W₀ : D →L[ℝ] F) (B₀ H : Z →L[ℝ] F)
    (h : (W.coprod B).IsInvertible) (h₀ : (W₀.coprod B₀).IsInvertible)
    (hH : Bijective (W₀.coprod H)) : Bijective (W.coprod (transportComplement W B W₀ B₀ H)) := by
  rw [coprod_transportComplement W B W₀ B₀ H h₀]
  exact (h.bijective.comp h₀.inverse.bijective).comp hH

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z]

theorem contDiffOn_transportComplement
    {W W₀ : X → (D →L[ℝ] F)} {B B₀ H : X → (Z →L[ℝ] F)} {U : Set X}
    (hU : IsOpen U) (hW : ContDiffOn ℝ ∞ W U) (hB : ContDiffOn ℝ ∞ B U)
    (hW₀ : ContDiffOn ℝ ∞ W₀ U) (hB₀ : ContDiffOn ℝ ∞ B₀ U)
    (hH : ContDiffOn ℝ ∞ H U) (hi : ∀ x ∈ U, ((W₀ x).coprod (B₀ x)).IsInvertible) :
    ContDiffOn ℝ ∞ (fun x => transportComplement (W x) (B x) (W₀ x) (B₀ x) (H x)) U := by
  have hT₀ := contDiffOn_coprod hW₀ hB₀
  have hInv : ContDiffOn ℝ ∞ (fun x => ((W₀ x).coprod (B₀ x)).inverse) U := by
    intro x hx
    exact ((hi x hx).contDiffAt_map_inverse.comp x
      (hT₀.contDiffAt (hU.mem_nhds hx))).contDiffWithinAt
  exact (contDiffOn_coprod hW hB).clm_comp (hInv.clm_comp hH)

end Wikipedia.SmoothSixDPoincare.FrameField
