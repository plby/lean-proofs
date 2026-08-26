import ErdosProblems.Erdos486.BiasedCandidateGeometry
import ErdosProblems.Erdos486.ColoringEnumeration
import ErdosProblems.Erdos486.FourColorTail
import ErdosProblems.Erdos486.FiniteAveraging

/- Ported to Lean/Mathlib 4.33.0; see README.md for source and modifications. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The bad-anchor tail for biased colourings

The anchor coordinates at a fixed residue are distinct.  Splitting a biased
colouring into its restriction to those coordinates and the complementary
coordinates therefore identifies the bad-anchor event with `fourColorTail`.
-/

namespace Erdos486

noncomputable section

/-- The anchor coordinates at any fixed scale and residue representative are
pairwise distinct. -/
theorem biasedAnchor_injective (j x : ℕ) :
    Function.Injective (biasedAnchor j x) := by
  intro i i' hii'
  simpa [biasedAnchor, endpointCoordinate] using congrArg Sigma.fst hii'

/-- The uniform rational average of the indicator that more than twice the
biased radius many anchor coordinates are black. -/
theorem biasedBadAnchorAverage_le (j : ℕ)
    (x : ZMod (biasedPeriod j)) :
    fintypeAverage
        (fun c : BiasedColoring j ↦
          if 2 * biasedRadius j <
              anchorBlackCount (biasedAnchor j x.val) c then
            (1 : ℚ)
          else 0) ≤
      ((125 : ℚ) / 128) ^ (2 * biasedRadius j) := by
  classical
  let anchor : Fin (biasedK j) ↪ BiasedCoordinate j :=
    ⟨biasedAnchor j x.val, biasedAnchor_injective j x.val⟩
  let split := oracleColoringEquiv anchor
  have hrestrict
      (c : FourColoring (Fin (biasedK j)) ×
        FourColoring (EmbeddingComplement anchor))
      (i : Fin (biasedK j)) :
      split c (biasedAnchor j x.val i) = c.1 i := by
    change split c (anchor i) = c.1 i
    simp [split]
  have hcount
      (c : FourColoring (Fin (biasedK j)) ×
        FourColoring (EmbeddingComplement anchor)) :
      anchorBlackCount (biasedAnchor j x.val) (split c) =
        blackCount c.1 := by
    unfold anchorBlackCount blackCount
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      hrestrict c i]
  calc
    fintypeAverage
        (fun c : BiasedColoring j ↦
          if 2 * biasedRadius j <
              anchorBlackCount (biasedAnchor j x.val) c then
            (1 : ℚ)
          else 0) =
        fintypeAverage
          (fun c : FourColoring (Fin (biasedK j)) ×
              FourColoring (EmbeddingComplement anchor) ↦
            if 2 * biasedRadius j <
                anchorBlackCount (biasedAnchor j x.val) (split c) then
              (1 : ℚ)
            else 0) := by
      exact (fintypeAverage_comp_equiv split _).symm
    _ = fintypeAverage
          (fun c : FourColoring (Fin (biasedK j)) ×
              FourColoring (EmbeddingComplement anchor) ↦
            if 2 * biasedRadius j < blackCount c.1 then
              (1 : ℚ)
            else 0) := by
      apply congrArg fintypeAverage
      funext c
      rw [hcount c]
    _ = fintypeAverage
          (fun c : FourColoring (Fin (biasedK j)) ↦
            if 2 * biasedRadius j < blackCount c then
              (1 : ℚ)
            else 0) := by
      exact fintypeAverage_prod_fst
        (α := FourColoring (Fin (biasedK j)))
        (β := FourColoring (EmbeddingComplement anchor))
        (fun c : FourColoring (Fin (biasedK j)) ↦
          if 2 * biasedRadius j < blackCount c then (1 : ℚ) else 0)
    _ = ((fourColorTail (ι := Fin (biasedK j)) (biasedRadius j)).card : ℚ) /
          Fintype.card (FourColoring (Fin (biasedK j))) := by
      have htail :
          (Finset.univ.filter fun c : FourColoring (Fin (biasedK j)) ↦
            2 * biasedRadius j < blackCount c) =
            fourColorTail (ι := Fin (biasedK j)) (biasedRadius j) := by
        ext c
        simp [fourColorTail]
      rw [fintypeAverage, Finset.sum_boole, htail]
    _ ≤ ((125 : ℚ) / 128) ^ (2 * biasedRadius j) := by
      have htail := fourColorTail_ratio_le_rat
        (ι := Fin (biasedK j)) (biasedRadius j) (by simp [biasedK])
      simpa only [Fintype.card_eq_nat_card] using htail

end

end Erdos486
