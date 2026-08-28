import Wikipedia.HopfProblem.DegreeCollapseRelativeTransverseDomain
import Wikipedia.SmoothSixDPoincare.SignedSplitCoordinates

/-!
# The actual signed transverse planes in two-block coordinates

The original sign splitting identifies vanishing signed coordinates with
the two literal coordinate planes. Conjugating the genuine relative
transverse chart by that splitting retains its fixed origin and turns the
proved signed-plane uniqueness into the exact coordinate-plane criterion
used by the supported transverse correction theorem.
-/

noncomputable section

open Set Function Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms

variable {ι : Type*} [Fintype ι]

open Classical in
theorem splitCoordinates_negative_zero_iff (w : ι → ℝ) (z : ι → ℝ) :
    (MorseHandle.splitCoordinates w z).1 = 0 ↔ ∀ i, w i = -1 → z i = 0 := by
  constructor
  · intro h i hi
    have hh := congrArg (fun v : MorseHandle.NegativeSpace w => v ⟨i, hi⟩) h
    exact hh
  · intro h
    ext i
    exact h i.1 i.2

open Classical in
theorem splitCoordinates_positive_zero_iff (w : ι → ℝ)
    (hw : ∀ i, w i = -1 ∨ w i = 1) (z : ι → ℝ) :
    (MorseHandle.splitCoordinates w z).2 = 0 ↔ ∀ i, w i = 1 → z i = 0 := by
  constructor
  · intro h i hi
    have hn : w i ≠ -1 := by rw [hi]; norm_num
    have hh := congrArg (fun v : MorseHandle.PositiveSpace w => v ⟨i, hn⟩) h
    exact hh
  · intro h
    ext i
    exact h i.1 ((hw i.1).resolve_left i.2)

open Classical in
/-- Construct the actual two-block relative chart and its exact unique
coordinate-plane intersection criterion from the signed-coordinate version. -/
theorem exists_two_block_transverse_chart (w : ι → ℝ)
    (hw : ∀ i, w i = -1 ∨ w i = 1)
    (H : PartialDiffeomorph 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (ι → ℝ) (ι → ℝ) ∞)
    (h0 : (0 : ι → ℝ) ∈ H.source) (hfix : H 0 = 0)
    (hunique : ∀ z ∈ H.source, (∀ i, w i = 1 → z i = 0) →
      (∀ i, w i = -1 → H z i = 0) → z = 0) :
    ∃ G : PartialDiffeomorph
      𝓘(ℝ, MorseHandle.NegativeSpace w × MorseHandle.PositiveSpace w)
      𝓘(ℝ, MorseHandle.NegativeSpace w × MorseHandle.PositiveSpace w)
      (MorseHandle.NegativeSpace w × MorseHandle.PositiveSpace w)
      (MorseHandle.NegativeSpace w × MorseHandle.PositiveSpace w) ∞,
      (0 : MorseHandle.NegativeSpace w × MorseHandle.PositiveSpace w) ∈ G.source ∧
      G 0 = 0 ∧
      (∀ u, G u = MorseHandle.splitCoordinates w (H ((MorseHandle.splitCoordinates w).symm u))) ∧
      ∀ x : MorseHandle.NegativeSpace w, (x, (0 : MorseHandle.PositiveSpace w)) ∈ G.source →
        ((G (x, 0)).1 = 0 ↔ x = 0) := by
  let S := MorseHandle.splitCoordinates w
  let G := (S.symm.toDiffeomorph.toPartialDiffeomorph.trans H).trans
    S.toDiffeomorph.toPartialDiffeomorph
  have hG0 : (0 : MorseHandle.NegativeSpace w × MorseHandle.PositiveSpace w) ∈ G.source := by
    change ((0 : MorseHandle.NegativeSpace w × MorseHandle.PositiveSpace w) ∈ univ ∧
      S.symm 0 ∈ H.source) ∧ H (S.symm 0) ∈ univ
    rw [map_zero]
    exact ⟨⟨mem_univ _, h0⟩, mem_univ _⟩
  have hGfix : G 0 = 0 := by
    change S (H (S.symm 0)) = 0
    rw [map_zero, hfix, map_zero]
  refine ⟨G, hG0, hGfix, fun _ => rfl, ?_⟩
  intro x hx
  constructor
  · intro hfirst
    let z := S.symm (x, (0 : MorseHandle.PositiveSpace w))
    have hz : z ∈ H.source := hx.1.2
    have hpos : ∀ i, w i = 1 → z i = 0 :=
      (splitCoordinates_positive_zero_iff w hw z).mp (by
        change (S (S.symm (x, 0))).2 = 0
        rw [S.apply_symm_apply])
    have hneg : ∀ i, w i = -1 → H z i = 0 :=
      (splitCoordinates_negative_zero_iff w (H z)).mp hfirst
    have hz0 := hunique z hz hpos hneg
    have hh := congrArg S hz0
    change S (S.symm (x, 0)) = S 0 at hh
    rw [S.apply_symm_apply, map_zero] at hh
    exact congrArg Prod.fst hh
  · intro hx0
    subst x
    change (G 0).1 = 0
    rw [hGfix]
    rfl

end Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms
