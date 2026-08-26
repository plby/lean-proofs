import ErdosProblems.Erdos336.StableHighPowerCertificateV2

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Wide-density quotient-stable certificate. The singleton branch supplies the
true base case; the density weight `|S|-1+(|2S|-|S|)` scales under every proper
failed-growth quotient and also handles saturated quotient powers. -/
def StableHighPowerCertificateV3 (C : Set G) (t : ℕ) : Prop :=
  let S := ExactPower C t
  Fintype.card G = 1 ∨
  Fintype.card G < (10000000 * Nat.factorial 36) * stableWeight S ∨
  RankExceptionalCertificate S

private theorem zero_mem_exactPower_of_zero_v3
    {C : Set G} (hzero : 0 ∈ C) (t : ℕ) : 0 ∈ ExactPower C t := by
  refine ⟨List.replicate t 0, by simp, ?_, by simp⟩
  intro y hy
  rw [List.mem_replicate] at hy
  simpa [hy.2] using hzero

private theorem ncard_le_double_of_zero_v3
    {S : Set G} (hz : 0 ∈ S) : S.ncard ≤ (ExactPower S 2).ncard := by
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  intro x hx
  rw [exactPower_eq_nsmul, two_nsmul]
  exact ⟨x, hx, 0, hz, by simp⟩

/-- The first quotient-stable certificate from F-087 implies V3 once the high
power has at least seven points. -/
theorem stableV3_of_stable
    {C : Set G} {t : ℕ} (hzero : 0 ∈ C)
    (hcard : 7 ≤ (ExactPower C t).ncard)
    (hdoub : 4 * (ExactPower C (2 * t)).ncard <
      9 * (ExactPower C t).ncard)
    (hstable : StableHighPowerCertificate C t) :
    StableHighPowerCertificateV3 C t := by
  let S := ExactPower C t
  have hzS : 0 ∈ S := zero_mem_exactPower_of_zero_v3 hzero t
  have hSle := ncard_le_double_of_zero_v3 hzS
  have hpower : ExactPower S 2 = ExactPower C (2 * t) := by
    simpa [S] using exactPower_exactPower C t 2
  have hdoubS : 4 * (ExactPower S 2).ncard < 9 * S.ncard := by
    rw [hpower]
    simpa [S] using hdoub
  change 7 ≤ S.ncard at hcard
  rcases hstable with hdense | hstruct
  · right; left
    change Fintype.card G < (10000000 * Nat.factorial 36) * stableWeight S
    change Fintype.card G < 20000 *
      ((ExactPower S 2).ncard - S.ncard) at hdense
    have hK : 20000 ≤ 10000000 * Nat.factorial 36 := by
      norm_num [Nat.factorial]
    have hdefle : (ExactPower S 2).ncard - S.ncard ≤ stableWeight S := by
      unfold stableWeight
      omega
    exact lt_of_lt_of_le hdense (Nat.mul_le_mul hK hdefle)
  · exact Or.inr (Or.inr hstruct)

section Lift

variable [IsAddCyclic G]

/-- V3 lifts through a proper failed-growth quotient. -/
theorem stableV3_of_failed_growth
    (K : AddSubgroup G) (hKtop : K ≠ ⊤)
    (C : Set G) (t : ℕ) (hzero : 0 ∈ C)
    (hcard : 7 ≤ (ExactPower C t).ncard)
    (hprimitive : ∃ q : ℕ, ExactPower C q = Set.univ)
    (hfail : (exactPowerFinset C t + addSubgroupFinset K).card <
      (exactPowerFinset C t).card + (addSubgroupFinset K).card)
    (hdoub : 4 * (ExactPower C (2 * t)).ncard <
      9 * (ExactPower C t).ncard)
    (hchild :
      let _ : NeZero (Nat.card (G ⧸ K)) :=
        ⟨Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩⟩
      StableHighPowerCertificateV3 (cyclicQuotientHom K '' C) t) :
    StableHighPowerCertificateV3 C t := by
  let m := Nat.card (G ⧸ K)
  let f := cyclicQuotientHom K
  let S := ExactPower C t
  let S' := ExactPower (f '' C) t
  let k := (addSubgroupFinset K).card
  have hm : 0 < m := Nat.card_pos
  letI : NeZero m := ⟨hm.ne'⟩
  have hdata := failed_growth_cyclic_quotient_highPower_data K C t
    hzero hprimitive hfail hdoub
  rcases hdata with ⟨_, hf, hz, hp, hd, hdefRaw⟩
  have himageS : f '' S = S' := by
    simpa [S, S'] using image_exactPower f C t
  have hcardSat : (exactPowerFinset C t + addSubgroupFinset K).card =
      S'.ncard * k := by
    simpa [S', f, k] using card_exactPower_image_mul_card_subgroup K C t
  have hdef : ((ExactPower S' 2).ncard - S'.ncard) * k ≤
      (ExactPower S 2).ncard - S.ncard := by
    simpa [S, S', f, k, exactPower_exactPower] using hdefRaw
  have hkpos : 0 < k := by
    dsimp [k]
    rw [Finset.card_pos]
    exact ⟨0, by simp⟩
  have hGcard : Fintype.card G = m * k := by
    letI : Fintype K := Fintype.ofFinite K
    rw [← Nat.card_eq_fintype_card,
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup]
    congr 1
    simpa [k, addSubgroupFinset] using
      (Nat.card_eq_fintype_card (α := K))
  change Fintype.card (ZMod m) = 1 ∨
      Fintype.card (ZMod m) < (10000000 * Nat.factorial 36) * stableWeight S' ∨
      RankExceptionalCertificate S' at hchild
  rcases hchild with hsingle | hdense | hstruct
  · have hm1 : m = 1 := by simpa using hsingle
    have hKG : Nat.card K = Nat.card G := by
      letI : Fintype K := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      have hkcard : Fintype.card K = k := by
        simpa [k, addSubgroupFinset]
      rw [hkcard, hGcard, hm1, one_mul]
    exact False.elim (hKtop (AddSubgroup.eq_top_of_card_eq K hKG))
  · right; left
    change Fintype.card G < (10000000 * Nat.factorial 36) * stableWeight S
    rw [ZMod.card] at hdense
    have hbase : (S'.ncard - 1) * k ≤ S.ncard - 1 := by
      rw [Nat.mul_sub_right_distrib]
      have hScard : (exactPowerFinset C t).card = S.ncard := by
        simp [S, card_exactPowerFinset]
      rw [hcardSat] at hfail
      rw [hScard] at hfail
      omega
    have hweight : stableWeight S' * k ≤ stableWeight S := by
      unfold stableWeight
      nlinarith
    rw [hGcard]
    calc
      m * k < ((10000000 * Nat.factorial 36) * stableWeight S') * k :=
        Nat.mul_lt_mul_of_pos_right hdense hkpos
      _ = (10000000 * Nat.factorial 36) * (stableWeight S' * k) := by ring
      _ ≤ (10000000 * Nat.factorial 36) * stableWeight S := Nat.mul_le_mul_left (10000000 * Nat.factorial 36) hweight
  · have holdChild : StableHighPowerCertificate (f '' C) t := Or.inr hstruct
    have holdParent := stableHighPowerCertificate_of_quotient K C t hzero
      holdChild hdef
    exact stableV3_of_stable hzero hcard hdoub holdParent

end Lift

end Erdos336
