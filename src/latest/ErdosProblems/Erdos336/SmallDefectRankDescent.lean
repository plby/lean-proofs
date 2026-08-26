import ErdosProblems.Erdos336.FinsetRankQuotientLift
import ErdosProblems.Erdos336.ModerateSaturationArithmetic

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {N : ℕ} [NeZero N]

/-- If subgroup saturation costs fewer than one fibre, then the child
quotient doubling defect, multiplied by the kernel size, is bounded by the
parent doubling defect. -/
theorem cyclicQuotient_defect_scales_of_small_saturation
    (K : AddSubgroup (ZMod N)) (A : Finset (ZMod N)) (hAne : A.Nonempty)
    (hdefect : (A + addSubgroupFinset K).card - A.card <
      (addSubgroupFinset K).card) :
    ((A.image (cyclicQuotientHom K) + A.image (cyclicQuotientHom K)).card -
        (A.image (cyclicQuotientHom K)).card) *
        (addSubgroupFinset K).card ≤
      (A + A).card - A.card := by
  let f := cyclicQuotientHom K
  let H := addSubgroupFinset K
  let k := H.card
  let X := (A.image f).card
  let Y := (A.image f + A.image f).card
  let a := A.card
  let d := (A + A).card
  let aSat := (A + H).card
  let dSat := ((A + A) + H).card
  have hbalance := double_saturation_defect_le K A hAne hdefect
  have hcardA := card_add_subgroup_eq_cyclicQuotient_image_mul K A
  have himageDouble : (A + A).image f = A.image f + A.image f := by
    simpa [f] using (Finset.image_add f (s := A) (t := A))
  have hcardD := card_add_subgroup_eq_cyclicQuotient_image_mul K (A + A)
  have hcardA' : aSat = X * k := by
    simpa [aSat, X, k, H, f] using hcardA
  have hcardD' : dSat = Y * k := by
    rw [himageDouble] at hcardD
    simpa [dSat, Y, k, H, f] using hcardD
  have hAle : a ≤ d := Finset.card_le_card_add_left hAne
  have hzeroH : 0 ∈ H := by simp [H]
  have haSat : a ≤ aSat := by
    dsimp [a, aSat]
    apply Finset.card_le_card
    intro x hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, hzeroH, by simp⟩
  have hdSat : d ≤ dSat := by
    dsimp [d, dSat]
    apply Finset.card_le_card
    intro x hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, hzeroH, by simp⟩
  have hImageNe : (A.image f).Nonempty := hAne.image f
  have hXleY : X ≤ Y := by
    dsimp [X, Y]
    exact Finset.card_le_card_add_left hImageNe
  have hSatLe : aSat ≤ dSat := by
    rw [hcardA', hcardD']
    exact Nat.mul_le_mul_right k hXleY
  have hbalance' : dSat - d ≤ aSat - a := by
    simpa [dSat, d, aSat, a, H] using hbalance
  have hdefParent : dSat - aSat ≤ d - a := by
    omega
  have hkpos : 0 < k := by
    dsimp [k, H]
    rw [Finset.card_pos]
    exact ⟨0, by simp⟩
  change (Y - X) * k ≤ d - a
  have hsubmul : (Y - X) * k = dSat - aSat := by
    rw [hcardA', hcardD', Nat.mul_sub_right_distrib]
  rw [hsubmul]
  exact hdefParent

/-- Consequently, every rank certificate proved in such a proper cyclic
quotient lifts to the original set. -/
theorem finsetRankCertificate_of_small_saturation_quotient
    (K : AddSubgroup (ZMod N)) [NeZero (Nat.card (ZMod N ⧸ K))]
    (A : Finset (ZMod N)) (hAne : A.Nonempty)
    (hdefect : (A + addSubgroupFinset K).card - A.card <
      (addSubgroupFinset K).card)
    (hchild : FinsetRankCertificate (A.image (cyclicQuotientHom K))) :
    FinsetRankCertificate A :=
  finsetRankCertificate_of_cyclicQuotient K A hAne hchild
    (cyclicQuotient_defect_scales_of_small_saturation K A hAne hdefect)

end Erdos336
