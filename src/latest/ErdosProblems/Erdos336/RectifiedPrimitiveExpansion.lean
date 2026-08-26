import ErdosProblems.Erdos336.VerticalStabilizer
import ErdosProblems.Erdos336.KneserConsequences

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {N m : ℕ} [NeZero N] [NeZero m]

/-- A vertical period of a sum of two nonempty subsets of a strict-half lift
is killed by the original rectifying homomorphism. -/
theorem verticalStabilizer_le_ker_of_rectified_subsets
    (A : Finset (ZMod N)) (π : ZMod N →+ ZMod m) (α : ZMod m)
    (houter : ∀ x ∈ A,
      ∃ q : ℕ, 2 * q < m ∧ π x = α + (q : ZMod m))
    (T₁ T₂ : Finset (ℤ × ZMod N))
    (hT₁ : T₁ ⊆ rectifiedLift A π α)
    (hT₂ : T₂ ⊆ rectifiedLift A π α)
    (hT₁ne : T₁.Nonempty) (hT₂ne : T₂.Nonempty) :
    verticalStabilizer (T₁ + T₂) ≤ π.ker := by
  intro k hk
  have hSne : (T₁ + T₂).Nonempty := hT₁ne.add hT₂ne
  obtain ⟨u, hu⟩ := hT₁ne
  obtain ⟨v, hv⟩ := hT₂ne
  have huv : u + v ∈ T₁ + T₂ :=
    Finset.mem_add.mpr ⟨u, hu, v, hv, rfl⟩
  have hkstab : (0, k) ∈ (T₁ + T₂).addStab :=
    (mem_verticalStabilizer hSne).mp hk
  have hshift : (0, k) + (u + v) ∈ T₁ + T₂ := by
    have := (Finset.mem_addStab' hSne).mp hkstab huv
    simpa [vadd_eq_add] using this
  obtain ⟨u', hu', v', hv', hu'v'⟩ := Finset.mem_add.mp hshift
  obtain ⟨a, ha, hua⟩ := mem_rectifiedLift.mp (hT₁ hu)
  obtain ⟨b, hb, hvb⟩ := mem_rectifiedLift.mp (hT₂ hv)
  obtain ⟨c, hc, hu'c⟩ := mem_rectifiedLift.mp (hT₁ hu')
  obtain ⟨d, hd, hv'd⟩ := mem_rectifiedLift.mp (hT₂ hv')
  have heq : (0, k) +
      ((Int.ofNat (halfIntervalLabel π α a), a) +
       (Int.ofNat (halfIntervalLabel π α b), b)) =
      (Int.ofNat (halfIntervalLabel π α c), c) +
       (Int.ofNat (halfIntervalLabel π α d), d) := by
    rw [← hua, ← hvb, ← hu'c, ← hv'd]
    exact hu'v'.symm
  have hlabelsInt := congrArg Prod.fst heq
  simp only [Prod.fst_add, Int.zero_add] at hlabelsInt
  have hlabels : halfIntervalLabel π α a + halfIntervalLabel π α b =
      halfIntervalLabel π α c + halfIntervalLabel π α d := by
    change Int.ofNat (halfIntervalLabel π α a + halfIntervalLabel π α b) =
      Int.ofNat (halfIntervalLabel π α c + halfIntervalLabel π α d) at hlabelsInt
    exact Int.ofNat.inj hlabelsInt
  have haS := halfIntervalLabel_spec π α a (houter a ha)
  have hbS := halfIntervalLabel_spec π α b (houter b hb)
  have hcS := halfIntervalLabel_spec π α c (houter c hc)
  have hdS := halfIntervalLabel_spec π α d (houter d hd)
  have hchars :
      (halfIntervalLabel π α a : ZMod m) +
          (halfIntervalLabel π α b : ZMod m) =
        (halfIntervalLabel π α c : ZMod m) +
          (halfIntervalLabel π α d : ZMod m) := by
    simpa only [Nat.cast_add] using
      congrArg (fun q : ℕ => (q : ZMod m)) hlabels
  have hpairs : π (a + b) = π (c + d) := by
    rw [map_add, map_add, haS.2, hbS.2, hcS.2, hdS.2]
    apply add_left_cancel (a := α + α)
    calc
      (α + α) + ((α + (halfIntervalLabel π α a : ZMod m)) +
          (α + (halfIntervalLabel π α b : ZMod m))) =
        ((α + α) + (α + α)) +
          ((halfIntervalLabel π α a : ZMod m) +
            (halfIntervalLabel π α b : ZMod m)) := by abel
      _ = ((α + α) + (α + α)) +
          ((halfIntervalLabel π α c : ZMod m) +
            (halfIntervalLabel π α d : ZMod m)) := by rw [hchars]
      _ = (α + α) + ((α + (halfIntervalLabel π α c : ZMod m)) +
          (α + (halfIntervalLabel π α d : ZMod m))) := by abel
  have hsecond := congrArg Prod.snd heq
  simp only [Prod.snd_add, Prod.snd_zero, zero_add] at hsecond
  change π k = 0
  have hmap := congrArg π hsecond
  rw [map_add, map_add, map_add] at hmap
  have hpairs' : π a + π b = π c + π d := by
    simpa [map_add] using hpairs
  apply add_right_cancel (b := π a + π b)
  simpa [hpairs'] using hmap

/-- Saturation defect is subadditive under unions. -/
theorem saturation_union_defect_le
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (X Y V : Finset G) (hzero : 0 ∈ V) :
    ((X ∪ Y) + V).card - (X ∪ Y).card ≤
      ((X + V).card - X.card) + ((Y + V).card - Y.card) := by
  have hXsub : X ⊆ X + V := by
    intro x hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, hzero, by simp⟩
  have hYsub : Y ⊆ Y + V := by
    intro y hy
    exact Finset.mem_add.mpr ⟨y, hy, 0, hzero, by simp⟩
  have hUsub : X ∪ Y ⊆ (X ∪ Y) + V := by
    intro x hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, hzero, by simp⟩
  have hdiff : ((X ∪ Y) + V) \ (X ∪ Y) ⊆
      ((X + V) \ X) ∪ ((Y + V) \ Y) := by
    intro z hz
    obtain ⟨hzsat, hznot⟩ := Finset.mem_sdiff.mp hz
    rw [Finset.union_add] at hzsat
    rcases Finset.mem_union.mp hzsat with hzX | hzY
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
        ⟨hzX, fun hzXin => hznot (Finset.mem_union_left _ hzXin)⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
        ⟨hzY, fun hzYin => hznot (Finset.mem_union_right _ hzYin)⟩)
  calc
    ((X ∪ Y) + V).card - (X ∪ Y).card =
        (((X ∪ Y) + V) \ (X ∪ Y)).card :=
      (Finset.card_sdiff_of_subset hUsub).symm
    _ ≤ (((X + V) \ X) ∪ ((Y + V) \ Y)).card :=
      Finset.card_le_card hdiff
    _ ≤ ((X + V) \ X).card + ((Y + V) \ Y).card :=
      Finset.card_union_le _ _
    _ = ((X + V).card - X.card) + ((Y + V).card - Y.card) := by
      rw [Finset.card_sdiff_of_subset hXsub,
        Finset.card_sdiff_of_subset hYsub]

/-- In the kernel-primitive case, every two nonempty subsets which
cover the rectified lift have the torsion-free lower sumset bound. -/
theorem rectified_subset_expansion_of_kernelPrimitive
    (A : Finset (ZMod N)) (π : ZMod N →+ ZMod m) (α : ZMod m)
    (houter : ∀ x ∈ A,
      ∃ q : ℕ, 2 * q < m ∧ π x = α + (q : ZMod m))
    (hsat : ∀ K : AddSubgroup (ZMod N), K ≤ π.ker → K ≠ ⊥ →
      (addSubgroupFinset K).card ≤
        (A + addSubgroupFinset K).card - A.card)
    (T₁ T₂ : Finset (ℤ × ZMod N))
    (hT₁ : T₁ ⊆ rectifiedLift A π α)
    (hT₂ : T₂ ⊆ rectifiedLift A π α)
    (hUnion : T₁ ∪ T₂ = rectifiedLift A π α)
    (hT₁ne : T₁.Nonempty) (hT₂ne : T₂.Nonempty) :
    T₁.card + T₂.card - 1 ≤ (T₁ + T₂).card := by
  by_contra hbad
  have hsmall : (T₁ + T₂).card ≤ T₁.card + T₂.card - 2 := by
    have h1 := hT₁ne.card_pos
    have h2 := hT₂ne.card_pos
    omega
  let S := T₁ + T₂
  have hSne : S.Nonempty := hT₁ne.add hT₂ne
  let K := verticalStabilizer S
  let V := verticalSubgroupFinset K
  have hKker : K ≤ π.ker := by
    exact verticalStabilizer_le_ker_of_rectified_subsets A π α houter
      T₁ T₂ hT₁ hT₂ hT₁ne hT₂ne
  have hkneser := add_kneser_eq_of_card_le hT₁ne hT₂ne (by
    have h1 := hT₁ne.card_pos
    have h2 := hT₂ne.card_pos
    omega : (T₁ + T₂).card ≤ T₁.card + T₂.card - 1)
  have hstab : S.addStab = V := by
    exact addStab_eq_verticalSubgroupFinset S hSne
  have hkEq : (T₁ + V).card + (T₂ + V).card = S.card + V.card := by
    simpa [S, hstab] using hkneser
  have hzero : 0 ∈ V := by
    apply mem_verticalSubgroupFinset.mpr
    exact ⟨rfl, K.zero_mem⟩
  have hT₁sub : T₁ ⊆ T₁ + V := by
    intro x hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, hzero, by simp⟩
  have hT₂sub : T₂ ⊆ T₂ + V := by
    intro x hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, hzero, by simp⟩
  have hT₁le := Finset.card_le_card hT₁sub
  have hT₂le := Finset.card_le_card hT₂sub
  have hV2 : 2 ≤ V.card := by
    dsimp [S] at hkEq
    omega
  have hKne : K ≠ ⊥ := by
    intro hbot
    have hVcard1 : V.card = 1 := by
      rw [card_verticalSubgroupFinset]
      rw [hbot]
      simp [addSubgroupFinset]
    omega
  have hpairDef :
      ((T₁ + V).card - T₁.card) + ((T₂ + V).card - T₂.card) ≤
        V.card - 2 := by
    dsimp [S] at hkEq
    omega
  have hunionDef := saturation_union_defect_le T₁ T₂ V hzero
  rw [hUnion] at hunionDef
  have hliftDef :
      (rectifiedLift A π α + V).card - (rectifiedLift A π α).card ≤
        V.card - 2 := le_trans hunionDef hpairDef
  have hVcard : V.card = (addSubgroupFinset K).card := by
    exact card_verticalSubgroupFinset K
  have hcycDef :
      (A + addSubgroupFinset K).card - A.card ≤
        (addSubgroupFinset K).card - 2 := by
    rw [← hVcard]
    rw [← card_rectifiedLift A π α,
      ← card_rectifiedLift_add_vertical A π α houter K hKker]
    exact hliftDef
  have hprim := hsat K hKker hKne
  have hKcard2 : 2 ≤ (addSubgroupFinset K).card := by
    rw [← hVcard]
    exact hV2
  omega

end Erdos336
