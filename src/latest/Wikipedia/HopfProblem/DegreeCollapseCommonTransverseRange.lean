import Wikipedia.HopfProblem.DegreeCollapseTransverseCorrectionTransport
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

/-!
# A common actual label domain for both endpoint transitions

Restrict the two transverse charts to the source and target of their
relative chart. Their images are exactly the same open neighborhood.
This puts the entire supported correction inside one original cylinder
domain and ensures that every label there has both endpoint coordinates.
-/

noncomputable section

open Set Function Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms

variable {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

open Classical in
theorem exists_common_transverse_range
    (Q P : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Z) E Z ∞)
    (H : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    (h0 : (0 : E) ∈ H.source) (hQzero : Q 0 = 0)
    (hHs : H.source ⊆ Q.source) (hHt : H.target ⊆ P.source)
    (hdiagram : ∀ z ∈ H.source, P (H z) = Q z) :
    ∃ (Q' P' : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Z) E Z ∞) (U : Set Z),
      IsOpen U ∧ (0 : Z) ∈ U ∧
      Q'.source = H.source ∧ P'.source = H.target ∧
      Q'.target = U ∧ P'.target = U ∧
      U ⊆ Q.target ∩ P.target ∧ (∀ z, Q' z = Q z) ∧ (∀ z, P' z = P z) := by
  let Q' := PartialChart.restrictSource Q H.open_source
  let P' := PartialChart.restrictSource P H.open_target
  have hQs : Q'.source = H.source := inter_eq_right.mpr hHs
  have hPs : P'.source = H.target := inter_eq_right.mpr hHt
  have hsame : Q'.target = P'.target := by
    ext y
    constructor
    · intro hy
      have hz : Q'.symm y ∈ H.source := hQs ▸ Q'.map_target' hy
      have hw : H (Q'.symm y) ∈ P'.source := hPs.symm ▸ H.map_source' hz
      have heq : P' (H (Q'.symm y)) = y :=
        (hdiagram _ hz).trans (Q'.right_inv' hy)
      exact heq ▸ P'.map_source' hw
    · intro hy
      have hz : P'.symm y ∈ H.target := hPs ▸ P'.map_target' hy
      have hw : H.symm (P'.symm y) ∈ Q'.source := hQs.symm ▸ H.map_target' hz
      have heq : Q' (H.symm (P'.symm y)) = y := by
        have hh := hdiagram (H.symm (P'.symm y)) (H.map_target' hz)
        have hi : H (H.symm (P'.symm y)) = P'.symm y := H.right_inv' hz
        rw [hi] at hh
        exact hh.symm.trans (P'.right_inv' hy)
      exact heq ▸ Q'.map_source' hw
  have h0U : (0 : Z) ∈ Q'.target := by
    have hh := Q'.map_source' (hQs.symm ▸ h0)
    change Q 0 ∈ Q'.target at hh
    rwa [hQzero] at hh
  refine ⟨Q', P', Q'.target, Q'.open_target, h0U, hQs, hPs, rfl, hsame.symm,
    ?_, fun _ => rfl, fun _ => rfl⟩
  intro y hy
  have hyP : y ∈ P'.target := hsame ▸ hy
  exact ⟨hy.1, hyP.1⟩

end Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms
