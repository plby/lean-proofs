import Wikipedia.SmoothSixDPoincare.ComplementQuotient
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Smooth dependence of actual complementary-frame quotient coordinates

The total operator inverse is smooth on the actual open invertibility locus.
Consequently the quotient coordinates and exact coefficient correction vary
smoothly wherever the original splitting does.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.FrameField

variable {X D Z F : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiffOn_coprod {G : X → (D →L[ℝ] F)} {C : X → (Z →L[ℝ] F)} {U : Set X}
    (hG : ContDiffOn ℝ ∞ G U) (hC : ContDiffOn ℝ ∞ C U) :
    ContDiffOn ℝ ∞ (fun x => (G x).coprod (C x)) U :=
  (hG.clm_comp (contDiffOn_const (c := ContinuousLinearMap.fst ℝ D Z))).add
    (hC.clm_comp (contDiffOn_const (c := ContinuousLinearMap.snd ℝ D Z)))

variable [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z]

/-- In finite dimensions, the supplied actual bijective splitting has a continuous inverse. -/
theorem isInvertible_coprod_of_bijective (G : D →L[ℝ] F) (C : Z →L[ℝ] F)
    (h : Bijective (G.coprod C)) : (G.coprod C).IsInvertible := by
  let e := (LinearEquiv.ofBijective (G.coprod C).toLinearMap h).toContinuousLinearEquiv
  exact ⟨e, rfl⟩

/-- The actual quotient field is smooth on its genuine splitting neighborhood. -/
theorem contDiffOn_complementQuotient
    {G : X → (D →L[ℝ] F)} {C : X → (Z →L[ℝ] F)} {U : Set X}
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (hC : ContDiffOn ℝ ∞ C U)
    (hi : ∀ x ∈ U, ((G x).coprod (C x)).IsInvertible) :
    ContDiffOn ℝ ∞ (fun x => complementQuotient (G x) (C x)) U := by
  have hT := contDiffOn_coprod hG hC
  have hInv : ContDiffOn ℝ ∞ (fun x => ((G x).coprod (C x)).inverse) U := by
    intro x hx
    exact ((hi x hx).contDiffAt_map_inverse.comp x
      (hT.contDiffAt (hU.mem_nhds hx))).contDiffWithinAt
  exact contDiffOn_const.clm_comp hInv

/-- Changing the quotient coefficient by the explicit correction preserves smoothness. -/
theorem contDiffOn_correctedComplement
    {G : X → (D →L[ℝ] F)} {C L : X → (Z →L[ℝ] F)} {K : X → (Z →L[ℝ] Z)}
    {U : Set X} (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U)
    (hC : ContDiffOn ℝ ∞ C U) (hL : ContDiffOn ℝ ∞ L U) (hK : ContDiffOn ℝ ∞ K U)
    (hi : ∀ x ∈ U, ((G x).coprod (C x)).IsInvertible) :
    ContDiffOn ℝ ∞ (fun x => correctedComplement (G x) (C x) (L x) (K x)) U :=
  hL.add (hC.clm_comp (hK.sub ((contDiffOn_complementQuotient hU hG hC hi).clm_comp hL)))

end Wikipedia.SmoothSixDPoincare.FrameField
