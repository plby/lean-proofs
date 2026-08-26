import ErdosProblems.Erdos336.StableHighPowerCertificateV3
import ErdosProblems.Erdos336.KneserAlmostExpansion

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
  [IsAddCyclic G]

/-- Minimality for V3 gives full one-fibre growth under every nonzero proper
subgroup. -/
theorem proper_saturation_growth_of_smaller_stableV3
    (C : Set G) (t : ℕ) (ht : 6 ≤ t) (hzero : 0 ∈ C)
    (hcard : 7 ≤ (ExactPower C t).ncard)
    (hprimitive : ∃ q : ℕ, ExactPower C q = Set.univ)
    (hdoub : 4 * (ExactPower C (2 * t)).ncard <
      9 * (ExactPower C t).ncard)
    (hnot : ¬ StableHighPowerCertificateV3 C t)
    (hsmaller : ∀ (m : ℕ) (hm : 0 < m),
      let _ : NeZero m := ⟨hm.ne'⟩
      m < Fintype.card G →
        ∀ (D : Set (ZMod m)), 0 ∈ D →
          7 ≤ (ExactPower D t).ncard →
          (∃ q : ℕ, ExactPower D q = Set.univ) →
          4 * (ExactPower D (2 * t)).ncard <
            9 * (ExactPower D t).ncard →
          StableHighPowerCertificateV3 D t) :
    ∀ K : AddSubgroup G, K ≠ ⊥ → K ≠ ⊤ →
      (exactPowerFinset C t).card + (addSubgroupFinset K).card ≤
        (exactPowerFinset C t + addSubgroupFinset K).card := by
  intro K hKbot hKtop
  by_contra hfailNot
  have hfail : (exactPowerFinset C t + addSubgroupFinset K).card <
      (exactPowerFinset C t).card + (addSubgroupFinset K).card := by omega
  let m := Nat.card (G ⧸ K)
  have hm : 0 < m := Nat.card_pos
  letI : NeZero m := ⟨hm.ne'⟩
  have hdata := failed_growth_cyclic_quotient_highPower_data K C t
    hzero hprimitive hfail hdoub
  rcases hdata with ⟨_, hf, hz, hp, hd, hdef⟩
  have hGcard : Fintype.card G = m * (addSubgroupFinset K).card := by
    letI : Fintype K := Fintype.ofFinite K
    rw [← Nat.card_eq_fintype_card,
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup]
    congr 1
    simpa [addSubgroupFinset] using (Nat.card_eq_fintype_card (α := K))
  have hk2 : 2 ≤ (addSubgroupFinset K).card := by
    letI : Fintype K := Fintype.ofFinite K
    have hk := (AddSubgroup.one_lt_card_iff_ne_bot K).mpr hKbot
    have hk' : 1 < (addSubgroupFinset K).card := by
      simpa [addSubgroupFinset, Nat.card_eq_fintype_card] using hk
    omega
  have hmG : m < Fintype.card G := by
    rw [hGcard]
    nlinarith
  have hchild : StableHighPowerCertificateV3
      (cyclicQuotientHom K '' C) t := by
    by_cases hfull : ExactPower (cyclicQuotientHom K '' C) t = Set.univ
    · change Fintype.card (ZMod m) = 1 ∨
        Fintype.card (ZMod m) < (10000000 * Nat.factorial 36) *
          stableWeight (ExactPower (cyclicQuotientHom K '' C) t) ∨
        RankExceptionalCertificate (ExactPower (cyclicQuotientHom K '' C) t)
      by_cases hm1 : m = 1
      · left; simpa using hm1
      · right; left
        have huniv2 : ExactPower (Set.univ : Set (ZMod m)) 2 = Set.univ := by
          rw [exactPower_eq_nsmul, two_nsmul]
          simp
        rw [ZMod.card, hfull]
        unfold stableWeight
        rw [huniv2]
        have hcardZm : (Set.univ : Set (ZMod m)).ncard = m := by
          simp [Nat.card_eq_fintype_card]
        rw [hcardZm]
        simp only [Nat.sub_self, add_zero]
        have hm2 : 2 ≤ m := by omega
        have hK3 : 3 ≤ 10000000 * Nat.factorial 36 := by
          norm_num [Nat.factorial]
        have hmul := Nat.mul_le_mul_right (m - 1) hK3
        omega
    · have hlarge := add_one_le_ncard_exactPower_of_not_full hz hp t hfull
      have h7 : 7 ≤ (ExactPower (cyclicQuotientHom K '' C) t).ncard := by
        omega
      exact hsmaller m hm hmG (cyclicQuotientHom K '' C) hz h7 hp hd
  exact hnot (stableV3_of_failed_growth K hKtop C t hzero hcard
    hprimitive hfail hdoub hchild)

/-- A minimal V3 counterexample has almost-full expansion against every
nonempty subset of its high power. -/
theorem almost_expansion_of_smaller_stableV3
    (C : Set G) (t : ℕ) (ht : 6 ≤ t) (hzero : 0 ∈ C)
    (hcard : 7 ≤ (ExactPower C t).ncard)
    (hprimitive : ∃ q : ℕ, ExactPower C q = Set.univ)
    (hdoub : 4 * (ExactPower C (2 * t)).ncard <
      9 * (ExactPower C t).ncard)
    (hnot : ¬ StableHighPowerCertificateV3 C t)
    (hsmaller : ∀ (m : ℕ) (hm : 0 < m),
      let _ : NeZero m := ⟨hm.ne'⟩
      m < Fintype.card G →
        ∀ (D : Set (ZMod m)), 0 ∈ D →
          7 ≤ (ExactPower D t).ncard →
          (∃ q : ℕ, ExactPower D q = Set.univ) →
          4 * (ExactPower D (2 * t)).ncard <
            9 * (ExactPower D t).ncard →
          StableHighPowerCertificateV3 D t)
    {B : Finset G} (hB : B.Nonempty)
    (hBsub : B ⊆ exactPowerFinset C t) :
    (exactPowerFinset C t).card + B.card ≤
      (exactPowerFinset C t + B).card + 1 := by
  let A := exactPowerFinset C t
  let S := ExactPower C t
  have hA : A.Nonempty := by
    refine ⟨0, ?_⟩
    rw [mem_exactPowerFinset]
    refine ⟨List.replicate t 0, by simp, ?_, by simp⟩
    intro y hy
    rw [List.mem_replicate] at hy
    simpa [hy.2] using hzero
  have hsat := proper_saturation_growth_of_smaller_stableV3 C t ht hzero
    hcard hprimitive hdoub hnot hsmaller
  have hBcard : B.card ≤ A.card := Finset.card_le_card hBsub
  have hsize : A.card + B.card ≤ Fintype.card G + 1 := by
    by_contra hbad
    have htwice : Fintype.card G < 2 * A.card := by omega
    have hfull : A + A = Finset.univ := by
      have h := add_eq_vadd_of_coset_support_of_card_lt_add
        (⊤ : AddSubgroup G) (A := A) (B := A) (a := 0) (b := 0)
        (by simp [addSubgroupFinset]) (by simp [addSubgroupFinset])
        (by simpa [addSubgroupFinset, two_mul] using htwice)
      simpa [addSubgroupFinset] using h
    have h2 : ExactPower S 2 = Set.univ := by
      rw [exactPower_eq_nsmul, two_nsmul]
      have hc := congrArg (fun T : Finset G => (T : Set G)) hfull
      simpa [A, S, coe_exactPowerFinset] using hc
    have hstable : StableHighPowerCertificateV3 C t := by
      change Fintype.card G = 1 ∨
        Fintype.card G < (10000000 * Nat.factorial 36) * stableWeight S ∨
        RankExceptionalCertificate S
      by_cases hG1 : Fintype.card G = 1
      · exact Or.inl hG1
      · right; left
        have hGpos : 0 < Fintype.card G := Fintype.card_pos
        have hG2 : 2 ≤ Fintype.card G := by omega
        unfold stableWeight
        rw [h2]
        simp only [Set.ncard_univ]
        have hScard : S.ncard = A.card := by simp [A, S, card_exactPowerFinset]
        have hSpos : 0 < S.ncard := by
          rw [hScard]
          exact hA.card_pos
        have hSleG : S.ncard ≤ Fintype.card G := by
          calc
            S.ncard ≤ (Set.univ : Set G).ncard :=
              Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
            _ = Fintype.card G := by simp
        have hweightEq : (S.ncard - 1) + (Fintype.card G - S.ncard) =
            Fintype.card G - 1 := by omega
        rw [Nat.card_eq_fintype_card, hweightEq]
        have hK3 : 3 ≤ 10000000 * Nat.factorial 36 := by
          norm_num [Nat.factorial]
        have hmul := Nat.mul_le_mul_right (Fintype.card G - 1) hK3
        omega
    exact hnot hstable
  exact card_add_add_one_ge_of_proper_saturation_growth hA hB hsize
    (fun K hKbot hKtop => hsat K hKbot hKtop)

end Erdos336
