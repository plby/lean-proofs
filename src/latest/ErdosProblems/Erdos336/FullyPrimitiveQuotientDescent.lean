import ErdosProblems.Erdos336.RectifiableQuotientDescent
import ErdosProblems.Erdos336.BalancedRankDescent

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {N : ℕ} [NeZero N]

/-- The rectifiable threshold descends through a balanced subgroup saturation. -/
theorem three_minus_three_descends_balanced_cyclicQuotient
    {m : ℕ} [NeZero m]
    (K : AddSubgroup (ZMod N)) (π : ZMod N →+ ZMod m)
    (hK : K ≤ π.ker) (A : Finset (ZMod N)) (hAne : A.Nonempty)
    (hbalance : ((A + A) + addSubgroupFinset K).card - (A + A).card ≤
      (A + addSubgroupFinset K).card - A.card)
    (hsmall : (A.image π).card * (A + A).card <
      3 * ((A.image π).card - 1) * A.card) :
    let f := cyclicQuotientHom K
    let πbar := cyclicQuotientFactor K π hK
    ((A.image f).image πbar).card *
        (A.image f + A.image f).card <
      3 * (((A.image f).image πbar).card - 1) * (A.image f).card := by
  let f := cyclicQuotientHom K
  let πbar := cyclicQuotientFactor K π hK
  let s := (A.image π).card
  let X := (A.image f).card
  let Y := (A.image f + A.image f).card
  let k := (addSubgroupFinset K).card
  have hsmallS : s * (A + A).card < 3 * (s - 1) * A.card := by
    simpa [s] using hsmall
  have hs2 : 2 ≤ s := by
    have hs0 : s ≠ 0 := by
      intro hs
      rw [hs] at hsmallS
      simp at hsmallS
    have hs1 : s ≠ 1 := by
      intro hs
      rw [hs] at hsmallS
      simp at hsmallS
    omega
  let H := addSubgroupFinset K
  have hzeroH : 0 ∈ H := by simp [H]
  have hAsub : A ⊆ A + H := by
    intro x hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, hzeroH, by simp⟩
  have hDsub : A + A ⊆ (A + A) + H := by
    intro x hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, hzeroH, by simp⟩
  have hsat := three_minus_three_card_survives_balanced_saturation
    s hs2 A (A + A) H hAsub hDsub (by simpa [H] using hbalance)
      (by simpa [s] using hsmall)
  have hcardA := card_add_subgroup_eq_cyclicQuotient_image_mul K A
  have himageDouble : (A + A).image f = A.image f + A.image f := by
    simpa [f] using (Finset.image_add f (s := A) (t := A))
  have hcardD := card_add_subgroup_eq_cyclicQuotient_image_mul K (A + A)
  rw [himageDouble] at hcardD
  have hcardA' : (A + addSubgroupFinset K).card = X * k := by
    simpa [X, k, f] using hcardA
  have hcardD' : ((A + A) + addSubgroupFinset K).card = Y * k := by
    simpa [Y, k, f] using hcardD
  have hscaled : s * (Y * k) < 3 * (s - 1) * (X * k) := by
    rw [hcardA', hcardD'] at hsat
    exact hsat.1
  have hkpos : 0 < k := by
    dsimp [k]
    rw [Finset.card_pos]
    exact ⟨0, by simp⟩
  have hcancel : s * Y < 3 * (s - 1) * X := by
    apply (Nat.mul_lt_mul_right hkpos).mp
    simpa [mul_assoc] using hscaled
  have himage := image_cyclicQuotientFactor K π hK A
  change ((A.image f).image πbar).card * Y <
    3 * (((A.image f).image πbar).card - 1) * X
  rw [himage]
  simpa [s] using hcancel

/-- Fully primitive case: every nonzero kernel subgroup has both at least one
fibre of original saturation defect and strictly larger double-set defect. -/
def HasFullyPrimitiveRectifiableThreeMinusThree : Prop :=
  ∀ (N : ℕ) (hN : 0 < N),
    let _ : NeZero N := ⟨hN.ne'⟩
    ∀ (A : Finset (ZMod N)), A.Nonempty → FinsetAffineGenerates A →
      ∀ (m : ℕ) (hm : 0 < m),
        let _ : NeZero m := ⟨hm.ne'⟩
        ∀ (π : ZMod N →+ ZMod m), Function.Surjective π →
          ∀ α : ZMod m,
            (∀ x ∈ A, ∃ q : ℕ, 2 * q < m ∧ π x = α + (q : ZMod m)) →
            (A.image π).card * (A + A).card <
              3 * ((A.image π).card - 1) * A.card →
            (∀ K : AddSubgroup (ZMod N), K ≤ π.ker → K ≠ ⊥ →
              (addSubgroupFinset K).card ≤
                (A + addSubgroupFinset K).card - A.card ∧
              (A + addSubgroupFinset K).card - A.card <
                ((A + A) + addSubgroupFinset K).card - (A + A).card) →
            FinsetRankCertificate A

/-- Balanced-saturation descent plus small-defect descent reduce the full
rectifiable theorem to the fully primitive case. -/
theorem rectifiableThreeMinusThree_of_fullyPrimitive
    (hprimitive : HasFullyPrimitiveRectifiableThreeMinusThree) :
    HasRectifiableThreeMinusThree := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      intro hN
      let : NeZero N := ⟨hN.ne'⟩
      dsimp
      intro A hAne hAaff m hm
      let : NeZero m := ⟨hm.ne'⟩
      intro π hπ α houter hsmall
      by_cases hfull : ∀ K : AddSubgroup (ZMod N), K ≤ π.ker → K ≠ ⊥ →
          (addSubgroupFinset K).card ≤
              (A + addSubgroupFinset K).card - A.card ∧
            (A + addSubgroupFinset K).card - A.card <
              ((A + A) + addSubgroupFinset K).card - (A + A).card
      · exact hprimitive N hN A hAne hAaff m hm π hπ α houter hsmall hfull
      · push_neg at hfull
        obtain ⟨K, hKker, hKne, hfail⟩ := hfull
        let q := Nat.card (ZMod N ⧸ K)
        have hq : 0 < q := Nat.card_pos
        let : NeZero q := ⟨hq.ne'⟩
        let f := cyclicQuotientHom K
        let πbar := cyclicQuotientFactor K π hKker
        have hKcard2 : 2 ≤ (addSubgroupFinset K).card := by
          let : Fintype K := Fintype.ofFinite K
          have hk := (AddSubgroup.one_lt_card_iff_ne_bot K).mpr hKne
          have hk' : 1 < (addSubgroupFinset K).card := by
            simpa [addSubgroupFinset, Nat.card_eq_fintype_card] using hk
          omega
        let : Fintype K := Fintype.ofFinite K
        have hNcard : N = q * (addSubgroupFinset K).card := by
          have hc := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup K
          have hkcard : Nat.card K = (addSubgroupFinset K).card := by
            rw [Nat.card_eq_fintype_card]
            simp [addSubgroupFinset]
          calc
            N = Nat.card (ZMod N ⧸ K) * Nat.card K := by simpa using hc
            _ = q * (addSubgroupFinset K).card := by rw [hkcard]
        have hqN : q < N := by rw [hNcard]; nlinarith
        have hImageNe : (A.image f).Nonempty := hAne.image f
        have hImageAff : FinsetAffineGenerates (A.image f) :=
          hAaff.image f (cyclicQuotientHom_surjective K)
        have hπbar : Function.Surjective πbar :=
          cyclicQuotientFactor_surjective K π hKker hπ
        have houterChild : ∀ y ∈ A.image f,
            ∃ r : ℕ, 2 * r < m ∧ πbar y = α + (r : ZMod m) := by
          simpa [f, πbar] using
            half_interval_descends_cyclicQuotient K π hKker A α houter
        by_cases hbalance :
            ((A + A) + addSubgroupFinset K).card - (A + A).card ≤
              (A + addSubgroupFinset K).card - A.card
        · have hsmallChild : ((A.image f).image πbar).card *
                (A.image f + A.image f).card <
              3 * (((A.image f).image πbar).card - 1) *
                (A.image f).card := by
            simpa [f, πbar] using
              three_minus_three_descends_balanced_cyclicQuotient
                K π hKker A hAne hbalance hsmall
          have hchild : FinsetRankCertificate (A.image f) :=
            ih q hqN hq (A.image f) hImageNe hImageAff m hm πbar hπbar
              α houterChild hsmallChild
          exact finsetRankCertificate_of_balanced_saturation_quotient
            K A hAne hbalance (by simpa [f] using hchild)
        · have hstrict :
              (A + addSubgroupFinset K).card - A.card <
                ((A + A) + addSubgroupFinset K).card - (A + A).card := by
            omega
          have hKsmall : (A + addSubgroupFinset K).card - A.card <
              (addSubgroupFinset K).card := by
            by_contra hnot
            have hlarge : (addSubgroupFinset K).card ≤
                (A + addSubgroupFinset K).card - A.card := by omega
            exact (not_lt_of_ge (hfail hlarge)) hstrict
          have hsmallChild : ((A.image f).image πbar).card *
                (A.image f + A.image f).card <
              3 * (((A.image f).image πbar).card - 1) *
                (A.image f).card := by
            simpa [f, πbar] using
              three_minus_three_descends_cyclicQuotient
                K π hKker A hAne hKsmall hsmall
          have hchild : FinsetRankCertificate (A.image f) :=
            ih q hqN hq (A.image f) hImageNe hImageAff m hm πbar hπbar
              α houterChild hsmallChild
          exact finsetRankCertificate_of_small_saturation_quotient
            K A hAne hKsmall (by simpa [f] using hchild)

end Erdos336
