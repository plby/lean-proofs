import ErdosProblems.Erdos336.SmallDefectRankDescent

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {N : ℕ} [NeZero N]

/-- Quotient doubling defect scales under any subgroup saturation whose
double-set deficiency is no larger than the original-set deficiency. -/
theorem cyclicQuotient_defect_scales_of_balanced_saturation
    (K : AddSubgroup (ZMod N)) (A : Finset (ZMod N)) (hAne : A.Nonempty)
    (hbalance : ((A + A) + addSubgroupFinset K).card - (A + A).card ≤
      (A + addSubgroupFinset K).card - A.card) :
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
  have hcardA := card_add_subgroup_eq_cyclicQuotient_image_mul K A
  have himageDouble : (A + A).image f = A.image f + A.image f := by
    simpa [f] using (Finset.image_add f (s := A) (t := A))
  have hcardD := card_add_subgroup_eq_cyclicQuotient_image_mul K (A + A)
  rw [himageDouble] at hcardD
  have hcardA' : aSat = X * k := by
    simpa [aSat, X, k, H, f] using hcardA
  have hcardD' : dSat = Y * k := by
    simpa [dSat, Y, k, H, f] using hcardD
  have hAle : a ≤ d := Finset.card_le_card_add_left hAne
  have hzeroH : 0 ∈ H := by simp [H]
  have haSat : a ≤ aSat := by
    apply Finset.card_le_card
    intro x hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, hzeroH, by simp⟩
  have hdSat : d ≤ dSat := by
    apply Finset.card_le_card
    intro x hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, hzeroH, by simp⟩
  have hImageNe : (A.image f).Nonempty := hAne.image f
  have hXleY : X ≤ Y := Finset.card_le_card_add_left hImageNe
  have hSatLe : aSat ≤ dSat := by
    rw [hcardA', hcardD']
    exact Nat.mul_le_mul_right k hXleY
  have hdefParent : dSat - aSat ≤ d - a := by
    change dSat - d ≤ aSat - a at hbalance
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

/-- Thus a rank certificate in the quotient lifts under balanced saturation. -/
theorem finsetRankCertificate_of_balanced_saturation_quotient
    (K : AddSubgroup (ZMod N)) [NeZero (Nat.card (ZMod N ⧸ K))]
    (A : Finset (ZMod N)) (hAne : A.Nonempty)
    (hbalance : ((A + A) + addSubgroupFinset K).card - (A + A).card ≤
      (A + addSubgroupFinset K).card - A.card)
    (hchild : FinsetRankCertificate (A.image (cyclicQuotientHom K))) :
    FinsetRankCertificate A :=
  finsetRankCertificate_of_cyclicQuotient K A hAne hchild
    (cyclicQuotient_defect_scales_of_balanced_saturation K A hAne hbalance)

end Erdos336
