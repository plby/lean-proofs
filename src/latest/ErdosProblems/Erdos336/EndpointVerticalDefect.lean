import ErdosProblems.Erdos336.EndpointVerticalMissingClassification

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

set_option maxHeartbeats 1400000

open scoped Pointwise

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- The vertical-full branch has nonincreasing saturation defect.  This is the
corrected, fully counted form of Lev's final Claim 2 argument: the three
endpoint-pair fibres are charged jointly, rather than silently discarding the
top-top fibre. -/
theorem vertical_full_double_defect_le
    (T : Finset (ℤ × H)) (l : ℤ) (hlpos : 0 < l)
    (hzero : ((0 : ℤ), 0) ∈ T) (δ : ℤ × H)
    (hδ : δ ∈ integerFiber T l)
    (h0 : 0 ∈ T.image Prod.fst) (hl : l ∈ T.image Prod.fst)
    (hbounds : ∀ z ∈ T.image Prod.fst, 0 ≤ z ∧ z ≤ l)
    (hthreshold : (T.image Prod.fst).card * (T + T).card <
      3 * ((T.image Prod.fst).card - 1) * T.card)
    (hexpand : HasCoverExpansion T) :
    let Δ := AddSubgroup.zmultiples δ
    let q : (ℤ × H) →+ ((ℤ × H) ⧸ Δ) := QuotientAddGroup.mk' Δ
    let Bq := T.image q
    let Ffin := (Bq + Bq).addStab
    let Fsub : AddSubgroup ((ℤ × H) ⧸ Δ) :=
      AddAction.stabilizer ((ℤ × H) ⧸ Δ) (Bq + Bq : Set ((ℤ × H) ⧸ Δ))
    (∀ f ∈ Ffin, ∃ k : H, verticalEndpointHom δ k = f) →
    let K := endpointVerticalPart δ Fsub
    let V := verticalSubgroupFinset K
    ((T + T) + V).card - (T + T).card ≤ (T + V).card - T.card := by
  classical
  dsimp
  let Δ := AddSubgroup.zmultiples δ
  let q : (ℤ × H) →+ ((ℤ × H) ⧸ Δ) := QuotientAddGroup.mk' Δ
  let Bq := T.image q
  let Ffin := (Bq + Bq).addStab
  let Fsub : AddSubgroup ((ℤ × H) ⧸ Δ) :=
    AddAction.stabilizer ((ℤ × H) ⧸ Δ) (Bq + Bq : Set ((ℤ × H) ⧸ Δ))
  intro hfull
  let K := endpointVerticalPart δ Fsub
  let V := verticalSubgroupFinset K
  let A := integerFiber T 0
  let Al := integerFiber T l
  let B := -δ +ᵥ Al
  let E := (T + V) \ T
  let M := ((T + T) + V) \ (T + T)
  let I := strictInteriorPart E l
  let P0 := V \ (A + A)
  let P1 := V \ (A + B)
  let P2 := V \ (B + B)
  have hclassRaw := vertical_full_missing_classification
    T l hlpos hzero δ hδ h0 hl hbounds hthreshold hexpand hfull
  have hclass : ∀ m ∈ M,
      (A.card ≤ Al.card →
        m ∈ P0 ∨ -δ + m ∈ P1 ∨ -(δ + δ) + m ∈ P2 ∨ m ∈ I) ∧
      (Al.card ≤ A.card →
        m ∈ P0 ∨ -δ + m ∈ P1 ∨ -(δ + δ) + m ∈ P2 ∨ -δ + m ∈ I) := by
    simpa [M, P0, P1, P2, I, E, A, Al, B, V, K, Fsub, Ffin, Bq, q, Δ]
      using hclassRaw
  have hδfst : δ.1 = l := (mem_integerFiber.mp hδ).2
  have hfibers := endpoint_fibers_single_vertical_cosets T l hlpos hzero δ hδ
    h0 hl hbounds hthreshold hexpand hfull
  change A ⊆ V ∧ Al ⊆ δ +ᵥ V at hfibers
  have hzeroV : (0 : ℤ × H) ∈ V :=
    mem_verticalSubgroupFinset.mpr ⟨rfl, K.zero_mem⟩
  have hBsub : B ⊆ V := by
    intro b hb
    obtain ⟨t, htAl, htb⟩ := Finset.mem_vadd_finset.mp hb
    obtain ⟨w, hwV, hwt⟩ := Finset.mem_vadd_finset.mp (hfibers.2 htAl)
    have hbw : b = w := by
      simp only [vadd_eq_add] at htb hwt
      rw [← htb, ← hwt]
      abel
    simpa [hbw] using hwV
  have hzeroA : (0 : ℤ × H) ∈ A := mem_integerFiber.mpr ⟨hzero, rfl⟩
  have hzeroB : (0 : ℤ × H) ∈ B := by
    apply Finset.mem_vadd_finset.mpr
    refine ⟨δ, hδ, ?_⟩
    simp
  have hAA : A + A ⊆ V := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hz
    apply mem_verticalSubgroupFinset.mpr
    exact ⟨by simp [(mem_verticalSubgroupFinset.mp (hfibers.1 ha)).1,
        (mem_verticalSubgroupFinset.mp (hfibers.1 hb)).1],
      K.add_mem (mem_verticalSubgroupFinset.mp (hfibers.1 ha)).2
        (mem_verticalSubgroupFinset.mp (hfibers.1 hb)).2⟩
  have hAB : A + B ⊆ V := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hz
    apply mem_verticalSubgroupFinset.mpr
    exact ⟨by simp [(mem_verticalSubgroupFinset.mp (hfibers.1 ha)).1,
        (mem_verticalSubgroupFinset.mp (hBsub hb)).1],
      K.add_mem (mem_verticalSubgroupFinset.mp (hfibers.1 ha)).2
        (mem_verticalSubgroupFinset.mp (hBsub hb)).2⟩
  have hBB : B + B ⊆ V := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hz
    apply mem_verticalSubgroupFinset.mpr
    exact ⟨by simp [(mem_verticalSubgroupFinset.mp (hBsub ha)).1,
        (mem_verticalSubgroupFinset.mp (hBsub hb)).1],
      K.add_mem (mem_verticalSubgroupFinset.mp (hBsub ha)).2
        (mem_verticalSubgroupFinset.mp (hBsub hb)).2⟩
  have hcoverRaw := endpointBoundaryUnion_add_self_eq_vertical
    T l hlpos hzero δ hδ h0 hl hbounds hthreshold hexpand hfull
  have hboundary : endpointBoundaryUnion T l δ = A ∪ B := by
    rfl
  have hcover : (A ∪ B) + (A ∪ B) = V := by
    rw [← hboundary]
    simpa [V, K, Fsub, Ffin, Bq, q, Δ] using hcoverRaw
  have hendHoles := three_pair_sum_holes_le A B V hzeroA hzeroB
    hfibers.1 hBsub hAA hAB hBB hcover
  have hP0card : P0.card = V.card - (A + A).card := by
    exact Finset.card_sdiff_of_subset hAA
  have hP1card : P1.card = V.card - (A + B).card := by
    exact Finset.card_sdiff_of_subset hAB
  have hP2card : P2.card = V.card - (B + B).card := by
    exact Finset.card_sdiff_of_subset hBB
  have hendpoint : P0.card + P1.card + P2.card ≤
      (V.card - A.card) + (V.card - B.card) := by
    simpa [hP0card, hP1card, hP2card] using hendHoles
  have hcoverTop (hord : A.card ≤ Al.card) :
      M ⊆ ((P0 ∪ (δ +ᵥ P1)) ∪ ((δ + δ) +ᵥ P2)) ∪ I := by
    intro m hm
    rcases (hclass m hm).1 hord with hp0 | hp1 | hp2 | hi
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ hp0))
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_vadd_finset.mpr
      exact ⟨-δ + m, hp1, by simp only [vadd_eq_add]; abel⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_vadd_finset.mpr
      exact ⟨-(δ + δ) + m, hp2, by simp only [vadd_eq_add]; abel⟩
    · exact Finset.mem_union_right _ hi
  have hcoverBot (hord : Al.card ≤ A.card) :
      M ⊆ ((P0 ∪ (δ +ᵥ P1)) ∪ ((δ + δ) +ᵥ P2)) ∪ (δ +ᵥ I) := by
    intro m hm
    rcases (hclass m hm).2 hord with hp0 | hp1 | hp2 | hi
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ hp0))
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_vadd_finset.mpr
        ⟨-δ + m, hp1, by simp only [vadd_eq_add]; abel⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_vadd_finset.mpr
        ⟨-(δ + δ) + m, hp2, by simp only [vadd_eq_add]; abel⟩
    · apply Finset.mem_union_right
      exact Finset.mem_vadd_finset.mpr
        ⟨-δ + m, hi, by simp only [vadd_eq_add]; abel⟩
  have hMbound : M.card ≤ P0.card + P1.card + P2.card + I.card := by
    rcases le_total A.card Al.card with hord | hord
    · have hc := Finset.card_le_card (hcoverTop hord)
      calc
        M.card ≤ (((P0 ∪ (δ +ᵥ P1)) ∪ ((δ + δ) +ᵥ P2)) ∪ I).card := hc
        _ ≤ ((P0 ∪ (δ +ᵥ P1)) ∪ ((δ + δ) +ᵥ P2)).card + I.card :=
          Finset.card_union_le _ _
        _ ≤ (P0 ∪ (δ +ᵥ P1)).card + ((δ + δ) +ᵥ P2).card + I.card := by
          have hu := Finset.card_union_le (P0 ∪ (δ +ᵥ P1))
            ((δ + δ) +ᵥ P2)
          omega
        _ ≤ (P0.card + (δ +ᵥ P1).card) + ((δ + δ) +ᵥ P2).card + I.card := by
          have := Finset.card_union_le P0 (δ +ᵥ P1)
          omega
        _ = P0.card + P1.card + P2.card + I.card := by
          rw [Finset.card_vadd_finset, Finset.card_vadd_finset]
    · have hc := Finset.card_le_card (hcoverBot hord)
      calc
        M.card ≤ (((P0 ∪ (δ +ᵥ P1)) ∪ ((δ + δ) +ᵥ P2)) ∪
            (δ +ᵥ I)).card := hc
        _ ≤ ((P0 ∪ (δ +ᵥ P1)) ∪ ((δ + δ) +ᵥ P2)).card +
            (δ +ᵥ I).card := Finset.card_union_le _ _
        _ ≤ (P0 ∪ (δ +ᵥ P1)).card + ((δ + δ) +ᵥ P2).card +
            (δ +ᵥ I).card := by
          have hu := Finset.card_union_le (P0 ∪ (δ +ᵥ P1))
            ((δ + δ) +ᵥ P2)
          omega
        _ ≤ (P0.card + (δ +ᵥ P1).card) + ((δ + δ) +ᵥ P2).card +
            (δ +ᵥ I).card := by
          have := Finset.card_union_le P0 (δ +ᵥ P1)
          omega
        _ = P0.card + P1.card + P2.card + I.card := by
          rw [Finset.card_vadd_finset, Finset.card_vadd_finset,
            Finset.card_vadd_finset]
  let H0 := V \ A
  let H1 := δ +ᵥ (V \ B)
  have hH0sub : H0 ⊆ E := by
    intro z hz
    have hz' := Finset.mem_sdiff.mp hz
    apply Finset.mem_sdiff.mpr
    constructor
    · exact Finset.mem_add.mpr ⟨(0, 0), hzero, z, hz'.1, by simp⟩
    · intro hzT
      exact hz'.2 (mem_integerFiber.mpr
        ⟨hzT, (mem_verticalSubgroupFinset.mp hz'.1).1⟩)
  have hH1sub : H1 ⊆ E := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := Finset.mem_vadd_finset.mp hz
    have hw' := Finset.mem_sdiff.mp hw
    apply Finset.mem_sdiff.mpr
    constructor
    · exact Finset.mem_add.mpr ⟨δ, (mem_integerFiber.mp hδ).1,
        w, hw'.1, hwz⟩
    · intro hzT
      apply hw'.2
      apply Finset.mem_vadd_finset.mpr
      refine ⟨z, mem_integerFiber.mpr ⟨hzT, ?_⟩, ?_⟩
      · simp only [vadd_eq_add] at hwz
        rw [← hwz, Prod.fst_add,
          (mem_verticalSubgroupFinset.mp hw'.1).1, hδfst]
        simp
      · simp only [vadd_eq_add] at hwz ⊢
        rw [← hwz]
        abel
  have hIsub : I ⊆ E := by
    intro z hz
    exact (mem_strictInteriorPart.mp hz).1
  have hH0H1 : Disjoint H0 H1 := by
    rw [Finset.disjoint_left]
    intro z hz0 hz1
    have hzf0 := (mem_verticalSubgroupFinset.mp (Finset.mem_sdiff.mp hz0).1).1
    obtain ⟨w, hw, hwz⟩ := Finset.mem_vadd_finset.mp hz1
    have hwf0 := (mem_verticalSubgroupFinset.mp (Finset.mem_sdiff.mp hw).1).1
    simp only [vadd_eq_add] at hwz
    have hzfl : z.1 = l := by rw [← hwz, Prod.fst_add, hwf0, hδfst]; simp
    omega
  have hH01I : Disjoint (H0 ∪ H1) I := by
    rw [Finset.disjoint_left]
    intro z hzU hzI
    have hzI' := mem_strictInteriorPart.mp hzI
    rcases Finset.mem_union.mp hzU with hz0 | hz1
    · have hzf0 := (mem_verticalSubgroupFinset.mp (Finset.mem_sdiff.mp hz0).1).1
      omega
    · obtain ⟨w, hw, hwz⟩ := Finset.mem_vadd_finset.mp hz1
      have hwf0 := (mem_verticalSubgroupFinset.mp (Finset.mem_sdiff.mp hw).1).1
      simp only [vadd_eq_add] at hwz
      have hzfl : z.1 = l := by rw [← hwz, Prod.fst_add, hwf0, hδfst]; simp
      omega
  have hbudgetSub : (H0 ∪ H1) ∪ I ⊆ E :=
    Finset.union_subset (Finset.union_subset hH0sub hH1sub) hIsub
  have hbudgetCard := Finset.card_le_card hbudgetSub
  have hH0card : H0.card = V.card - A.card :=
    Finset.card_sdiff_of_subset hfibers.1
  have hH1card : H1.card = V.card - B.card := by
    rw [Finset.card_vadd_finset]
    exact Finset.card_sdiff_of_subset hBsub
  have hbudgetFinal : (V.card - A.card) + (V.card - B.card) + I.card ≤ E.card := by
    rw [Finset.card_union_of_disjoint hH01I,
      Finset.card_union_of_disjoint hH0H1, hH0card, hH1card] at hbudgetCard
    exact hbudgetCard
  have hME : M.card ≤ E.card := le_trans hMbound (le_trans
    (Nat.add_le_add_right hendpoint I.card) hbudgetFinal)
  have hTsub : T ⊆ T + V := by
    intro z hz
    exact Finset.mem_add.mpr ⟨z, hz, 0, hzeroV, by simp⟩
  have hTTsub : T + T ⊆ (T + T) + V := by
    intro z hz
    exact Finset.mem_add.mpr ⟨z, hz, 0, hzeroV, by simp⟩
  have hMcard : M.card = ((T + T) + V).card - (T + T).card :=
    Finset.card_sdiff_of_subset hTTsub
  have hEcard : E.card = (T + V).card - T.card :=
    Finset.card_sdiff_of_subset hTsub
  change ((T + T) + V).card - (T + T).card ≤
    (T + V).card - T.card
  rw [← hMcard, ← hEcard]
  exact hME

end Erdos336
