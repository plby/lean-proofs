import ErdosProblems.Erdos336.CyclicQuotientCardinality
import ErdosProblems.Erdos336.SaturationNineFour
import ErdosProblems.Erdos336.HighPowerKneserReduction
import ErdosProblems.Erdos336.DensePowerSaturation

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {G Q : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
  [AddCommGroup Q] [Fintype Q] [DecidableEq Q]

lemma image_exactPowerFinset (f : G →+ Q) (C : Set G) (t : ℕ) :
    (exactPowerFinset C t).image f = exactPowerFinset (f '' C) t := by
  apply Finset.coe_injective
  rw [Finset.coe_image]
  simp only [coe_exactPowerFinset]
  exact image_exactPower f C t

lemma exactPowerFinset_add_self (C : Set G) (t : ℕ) :
    exactPowerFinset C t + exactPowerFinset C t =
      exactPowerFinset C (2 * t) := by
  apply Finset.coe_injective
  rw [Finset.coe_add]
  simp only [coe_exactPowerFinset]
  rw [exactPower_add]
  congr 2
  omega

lemma card_exactPower_image_mul_card_subgroup
    [IsAddCyclic G] (K : AddSubgroup G) (C : Set G) (t : ℕ) :
    (exactPowerFinset C t + addSubgroupFinset K).card =
      (ExactPower (cyclicQuotientHom K '' C) t).ncard *
        (addSubgroupFinset K).card := by
  let : NeZero (Nat.card (G ⧸ K)) :=
    ⟨Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩⟩
  rw [card_add_subgroup_eq_cyclicQuotient_image_mul]
  rw [image_exactPowerFinset]
  simp [card_exactPowerFinset]

/-- If a subgroup violates full one-fibre growth for a primitive high power,
then the strict `9/4` hypothesis and primitivity descend to the cyclic
quotient. Moreover the quotient doubling defect, multiplied by the fibre
size, is no larger than the original defect. -/
theorem failed_growth_cyclic_quotient_highPower_data
    [IsAddCyclic G] (K : AddSubgroup G) (C : Set G) (t : ℕ)
    (hzero : 0 ∈ C)
    (hprimitive : ∃ q : ℕ, ExactPower C q = Set.univ)
    (hfail : (exactPowerFinset C t + addSubgroupFinset K).card <
      (exactPowerFinset C t).card + (addSubgroupFinset K).card)
    (hdoub : 4 * (ExactPower C (2 * t)).ncard <
      9 * (ExactPower C t).ncard) :
    let m := Nat.card (G ⧸ K)
    let f := cyclicQuotientHom K
    0 < m ∧ Function.Surjective f ∧ 0 ∈ f '' C ∧
      (∃ q : ℕ, ExactPower (f '' C) q = Set.univ) ∧
      4 * (ExactPower (f '' C) (2 * t)).ncard <
        9 * (ExactPower (f '' C) t).ncard ∧
      ((ExactPower (f '' C) (2 * t)).ncard -
          (ExactPower (f '' C) t).ncard) *
          (addSubgroupFinset K).card ≤
        (ExactPower C (2 * t)).ncard - (ExactPower C t).ncard := by
  let m := Nat.card (G ⧸ K)
  let f := cyclicQuotientHom K
  have hm : 0 < m := Nat.card_pos
  let : NeZero m := ⟨hm.ne'⟩
  have hf : Function.Surjective f := cyclicQuotientHom_surjective K
  have hzS : (exactPowerFinset C t).Nonempty := by
    refine ⟨0, ?_⟩
    rw [mem_exactPowerFinset]
    refine ⟨List.replicate t 0, by simp, ?_, by simp⟩
    intro x hx
    rw [List.mem_replicate] at hx
    simpa [hx.2] using hzero
  have hdoubFin : 4 * (exactPowerFinset C t + exactPowerFinset C t).card <
      9 * (exactPowerFinset C t).card := by
    rw [exactPowerFinset_add_self]
    simpa [card_exactPowerFinset] using hdoub
  have hs := nine_four_survives_failed_subgroup_growth K
    (exactPowerFinset C t) hzS hfail hdoubFin
  have hcardT := card_exactPower_image_mul_card_subgroup K C t
  have hcard2T := card_exactPower_image_mul_card_subgroup K C (2 * t)
  have hsum : exactPowerFinset C t + exactPowerFinset C t =
      exactPowerFinset C (2 * t) := exactPowerFinset_add_self C t
  rw [hsum] at hs
  have hkpos : 0 < (addSubgroupFinset K).card := by
    rw [Finset.card_pos]
    exact ⟨0, by simp⟩
  have hquotDoub : 4 * (ExactPower (f '' C) (2 * t)).ncard <
      9 * (ExactPower (f '' C) t).ncard := by
    apply Nat.lt_of_mul_lt_mul_right (a := (addSubgroupFinset K).card)
    calc
      4 * (ExactPower (f '' C) (2 * t)).ncard *
          (addSubgroupFinset K).card =
          4 * (exactPowerFinset C (2 * t) + addSubgroupFinset K).card := by
            rw [hcard2T]
            ring
      _ < 9 * (exactPowerFinset C t + addSubgroupFinset K).card := hs.1
      _ = 9 * (ExactPower (f '' C) t).ncard *
          (addSubgroupFinset K).card := by
            rw [hcardT]
            ring
  have hdefect : ((ExactPower (f '' C) (2 * t)).ncard -
        (ExactPower (f '' C) t).ncard) *
        (addSubgroupFinset K).card ≤
      (ExactPower C (2 * t)).ncard - (ExactPower C t).ncard := by
    calc
      ((ExactPower (f '' C) (2 * t)).ncard -
          (ExactPower (f '' C) t).ncard) *
          (addSubgroupFinset K).card =
          (exactPowerFinset C (2 * t) + addSubgroupFinset K).card -
            (exactPowerFinset C t + addSubgroupFinset K).card := by
              rw [Nat.mul_sub_right_distrib, hcard2T, hcardT]
      _ ≤ (exactPowerFinset C (2 * t)).card -
          (exactPowerFinset C t).card := hs.2
      _ = (ExactPower C (2 * t)).ncard -
          (ExactPower C t).ncard := by simp [card_exactPowerFinset]
  refine ⟨hm, hf, ⟨0, hzero, f.map_zero⟩, ?_, hquotDoub, hdefect⟩
  exact exactPower_univ_image_of_surjective f hf hprimitive

end Erdos336
