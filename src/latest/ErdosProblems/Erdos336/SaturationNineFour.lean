import ErdosProblems.Erdos336.DoubleSaturationDefect
import ErdosProblems.Erdos336.BalancedSaturationArithmetic

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Failure of full one-fibre growth under subgroup saturation automatically
produces a balanced saturation. Consequently strict `9/4` doubling survives,
and the saturated doubling defect cannot increase. -/
theorem nine_four_survives_failed_subgroup_growth
    (K : AddSubgroup G) (A : Finset G) (hA : A.Nonempty)
    (hfail : (A + addSubgroupFinset K).card <
      A.card + (addSubgroupFinset K).card)
    (hdoub : 4 * (A + A).card < 9 * A.card) :
    4 * ((A + A) + addSubgroupFinset K).card <
        9 * (A + addSubgroupFinset K).card ∧
      ((A + A) + addSubgroupFinset K).card -
          (A + addSubgroupFinset K).card ≤
        (A + A).card - A.card := by
  let H := addSubgroupFinset K
  have hzero : 0 ∈ H := by simp [H]
  have hAsub : A ⊆ A + H := by
    intro x hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, hzero, by simp⟩
  have h2sub : A + A ⊆ (A + A) + H := by
    intro x hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, hzero, by simp⟩
  have hdefect : (A + H).card - A.card < H.card := by
    have hAc := Finset.card_le_card hAsub
    have hfailH : (A + H).card < A.card + H.card := by
      simpa [H] using hfail
    omega
  have hbalance := double_saturation_defect_le K A hA (by simpa [H] using hdefect)
  have hres := nine_four_card_survives_balanced_saturation A (A + A) H
    hAsub h2sub hbalance hdoub
  simpa [H] using hres

end Erdos336
