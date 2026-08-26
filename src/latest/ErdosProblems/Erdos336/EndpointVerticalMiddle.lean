import ErdosProblems.Erdos336.EndpointVerticalBoundaryCoset
import ErdosProblems.Erdos336.EndpointClassSumset
import ErdosProblems.Erdos336.DenseCosetAddition

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

noncomputable def endpointMiddlePart
    (T : Finset (ℤ × H)) (l : ℤ) : Finset (ℤ × H) :=
  T \ (integerFiber T 0 ∪ integerFiber T l)

/-- In the vertical-full branch, the original points over an interior
endpoint-quotient `F`-coset all lie in one vertical `K`-coset. -/
theorem endpointClassSlice_subset_vertical_of_interior
    (T : Finset (ℤ × H)) (l : ℤ) (hlpos : 0 < l)
    (δ : ℤ × H) (hδfst : δ.1 = l)
    (hbounds : ∀ x ∈ T, 0 ≤ x.1 ∧ x.1 ≤ l)
    (F : AddSubgroup ((ℤ × H) ⧸ AddSubgroup.zmultiples δ))
    (Ffin : Finset ((ℤ × H) ⧸ AddSubgroup.zmultiples δ))
    (hFfin : ∀ x, x ∈ Ffin ↔ x ∈ F)
    (hfull : ∀ f ∈ Ffin, ∃ k : H, verticalEndpointHom δ k = f)
    (a : ℤ × H) (haT : a ∈ T) (ha0 : 0 < a.1) (hal : a.1 < l) :
    endpointClassSlice T δ F
        ((QuotientAddGroup.mk' F)
          ((QuotientAddGroup.mk' (AddSubgroup.zmultiples δ)) a)) ⊆
      a +ᵥ verticalSubgroupFinset (endpointVerticalPart δ F) := by
  classical
  let q : (ℤ × H) →+
      ((ℤ × H) ⧸ AddSubgroup.zmultiples δ) :=
    QuotientAddGroup.mk' (AddSubgroup.zmultiples δ)
  let r := QuotientAddGroup.mk' F
  intro x hx
  have hx' := mem_endpointClassSlice.mp hx
  have hr : r (q x) = r (q a) := hx'.2
  have hdiffF : q x - q a ∈ F :=
    (QuotientAddGroup.eq_iff_sub_mem).mp hr
  obtain ⟨k, hk⟩ := hfull (q x - q a) ((hFfin _).mpr hdiffF)
  have hkK : k ∈ endpointVerticalPart δ F := by
    change verticalEndpointHom δ k ∈ F
    rw [hk]
    exact hdiffF
  have hzero : q ((x - a) - ((0 : ℤ), k)) = 0 := by
    rw [q.map_sub, q.map_sub]
    change (q x - q a) - verticalEndpointHom δ k = 0
    rw [hk, sub_self]
  have hmem : (x - a) - ((0 : ℤ), k) ∈ AddSubgroup.zmultiples δ :=
    (QuotientAddGroup.eq_zero_iff ((x - a) - ((0 : ℤ), k))).mp hzero
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  have hfirst := congrArg Prod.fst hn
  change n * δ.1 = (x.1 - a.1) - 0 at hfirst
  simp only [sub_zero] at hfirst
  rw [hδfst] at hfirst
  have hxbound := hbounds x hx'.1
  have hdifflo : -l < x.1 - a.1 := by nlinarith
  have hdiffhi : x.1 - a.1 < l := by nlinarith
  have hn0 : n = 0 := by
    rcases lt_trichotomy n 0 with hnneg | hnzero | hnpos
    · have hnle : n ≤ -1 := by omega
      have hmul : n * l ≤ (-1 : ℤ) * l :=
        (mul_le_mul_iff_of_pos_right hlpos).mpr hnle
      nlinarith
    · exact hnzero
    · have hnge : 1 ≤ n := by omega
      have hmul : (1 : ℤ) * l ≤ n * l :=
        (mul_le_mul_iff_of_pos_right hlpos).mpr hnge
      nlinarith
  rw [hn0, zero_zsmul] at hn
  have hxeq : x = a + ((0 : ℤ), k) := by
    have hz : (x - a) - ((0 : ℤ), k) = 0 := hn.symm
    have hz' : x - (a + ((0 : ℤ), k)) = 0 := by
      calc
        x - (a + ((0 : ℤ), k)) = (x - a) - ((0 : ℤ), k) := by abel
        _ = 0 := hz
    exact sub_eq_zero.mp hz'
  apply Finset.mem_vadd_finset.mpr
  refine ⟨((0 : ℤ), k), mem_verticalSubgroupFinset.mpr ⟨rfl, hkK⟩, ?_⟩
  simpa [vadd_eq_add] using hxeq.symm

/-- Dense subsets of two cosets of a finite vertical subgroup add to the
whole sum coset. -/
theorem add_eq_vadd_vertical_of_card_lt
    (K : AddSubgroup H) (A B : Finset (ℤ × H)) (a b : ℤ × H)
    (hA : A ⊆ a +ᵥ verticalSubgroupFinset K)
    (hB : B ⊆ b +ᵥ verticalSubgroupFinset K)
    (hcard : (verticalSubgroupFinset K).card < A.card + B.card) :
    A + B = (a + b) +ᵥ verticalSubgroupFinset K := by
  classical
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hx
    obtain ⟨ku, hku, huka⟩ := Finset.mem_vadd_finset.mp (hA hu)
    obtain ⟨kv, hkv, hvkb⟩ := Finset.mem_vadd_finset.mp (hB hv)
    apply Finset.mem_vadd_finset.mpr
    refine ⟨ku + kv, ?_, ?_⟩
    · exact mem_verticalSubgroupFinset.mpr
        ⟨by simp [(mem_verticalSubgroupFinset.mp hku).1,
          (mem_verticalSubgroupFinset.mp hkv).1],
         K.add_mem (mem_verticalSubgroupFinset.mp hku).2
           (mem_verticalSubgroupFinset.mp hkv).2⟩
    · simp only [vadd_eq_add] at huka hvkb ⊢
      rw [← huka, ← hvkb]
      abel
  · intro x hx
    obtain ⟨k, hk, hkx⟩ := Finset.mem_vadd_finset.mp hx
    let R : Finset (ℤ × H) := B.image (fun y => x - y)
    have hRcard : R.card = B.card := by
      dsimp [R]
      rw [Finset.card_image_of_injective]
      intro y z hyz
      exact sub_right_injective hyz
    have hRsub : R ⊆ a +ᵥ verticalSubgroupFinset K := by
      intro z hz
      obtain ⟨y, hyB, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨ky, hky, hyy⟩ := Finset.mem_vadd_finset.mp (hB hyB)
      apply Finset.mem_vadd_finset.mpr
      refine ⟨k - ky, ?_, ?_⟩
      · apply mem_verticalSubgroupFinset.mpr
        exact ⟨by
          rw [Prod.fst_sub, (mem_verticalSubgroupFinset.mp hk).1,
            (mem_verticalSubgroupFinset.mp hky).1, sub_zero],
          K.sub_mem (mem_verticalSubgroupFinset.mp hk).2
            (mem_verticalSubgroupFinset.mp hky).2⟩
      · simp only [vadd_eq_add] at hkx hyy ⊢
        rw [← hkx, ← hyy]
        abel
    have hcosetCard : (a +ᵥ verticalSubgroupFinset K).card =
        (verticalSubgroupFinset K).card := Finset.card_vadd_finset _ _
    have hinter : ¬ Disjoint A R := by
      apply not_disjoint_of_card_add_gt_of_subset hA hRsub
      rw [hcosetCard, hRcard]
      exact hcard
    rw [Finset.not_disjoint_iff] at hinter
    obtain ⟨z, hzA, hzR⟩ := hinter
    obtain ⟨y, hyB, hyz⟩ := Finset.mem_image.mp hzR
    exact Finset.mem_add.mpr ⟨z, hzA, y, hyB, by rw [← hyz]; abel⟩

/-- Two interior endpoint classes add to a complete vertical `K`-coset. -/
theorem add_endpointClassSlices_eq_vertical_coset
    (T : Finset (ℤ × H)) (l : ℤ) (hlpos : 0 < l)
    (δ : ℤ × H) (hδfst : δ.1 = l)
    (hbounds : ∀ x ∈ T, 0 ≤ x.1 ∧ x.1 ≤ l)
    (F : AddSubgroup ((ℤ × H) ⧸ AddSubgroup.zmultiples δ))
    (Ffin : Finset ((ℤ × H) ⧸ AddSubgroup.zmultiples δ))
    (hFfin : ∀ x, x ∈ Ffin ↔ x ∈ F)
    (hfull : ∀ f ∈ Ffin, ∃ k : H, verticalEndpointHom δ k = f)
    (hdef : 2 * ((T.image (QuotientAddGroup.mk'
      (AddSubgroup.zmultiples δ)) + Ffin).card -
      (T.image (QuotientAddGroup.mk' (AddSubgroup.zmultiples δ))).card) ≤
      Ffin.card - 2)
    (a b : ℤ × H) (haT : a ∈ T) (hbT : b ∈ T)
    (ha0 : 0 < a.1) (hal : a.1 < l)
    (hb0 : 0 < b.1) (hbl : b.1 < l) :
    let Fsub := endpointVerticalPart δ F
    endpointClassSlice T δ F
        ((QuotientAddGroup.mk' F)
          ((QuotientAddGroup.mk' (AddSubgroup.zmultiples δ)) a)) +
      endpointClassSlice T δ F
        ((QuotientAddGroup.mk' F)
          ((QuotientAddGroup.mk' (AddSubgroup.zmultiples δ)) b)) =
      (a + b) +ᵥ verticalSubgroupFinset Fsub := by
  classical
  dsimp
  let q : (ℤ × H) →+
      ((ℤ × H) ⧸ AddSubgroup.zmultiples δ) :=
    QuotientAddGroup.mk' (AddSubgroup.zmultiples δ)
  let r := QuotientAddGroup.mk' F
  let B := T.image q
  let K := endpointVerticalPart δ F
  let X := endpointClassSlice T δ F (r (q a))
  let Y := endpointClassSlice T δ F (r (q b))
  have hdefLocal : 2 * ((B + Ffin).card - B.card) ≤ Ffin.card - 2 := by
    simpa [B, q] using hdef
  have hKcard := card_endpointVerticalPart_eq_of_full δ (by rw [hδfst]; exact hlpos)
    F Ffin hFfin hfull
  have hXsub : X ⊆ a +ᵥ verticalSubgroupFinset K :=
    endpointClassSlice_subset_vertical_of_interior T l hlpos δ hδfst hbounds
      F Ffin hFfin hfull a haT ha0 hal
  have hYsub : Y ⊆ b +ᵥ verticalSubgroupFinset K :=
    endpointClassSlice_subset_vertical_of_interior T l hlpos δ hδfst hbounds
      F Ffin hFfin hfull b hbT hb0 hbl
  have hclassA : r (q a) ∈ B.image r :=
    Finset.mem_image.mpr ⟨q a, Finset.mem_image.mpr ⟨a, haT, rfl⟩, rfl⟩
  have hclassB : r (q b) ∈ B.image r :=
    Finset.mem_image.mpr ⟨q b, Finset.mem_image.mpr ⟨b, hbT, rfl⟩, rfl⟩
  have htotal := quotientDeficiency_eq_saturation_sub F Ffin hFfin B
  have hdefA : quotientFiberDeficiency F Ffin B (r (q a)) ≤
      (B + Ffin).card - B.card := by
    rw [← htotal]
    unfold quotientDeficiency
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by
      simpa [quotientImage, r] using hclassA)
  have hdefB : quotientFiberDeficiency F Ffin B (r (q b)) ≤
      (B + Ffin).card - B.card := by
    rw [← htotal]
    unfold quotientDeficiency
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by
      simpa [quotientImage, r] using hclassB)
  have hoccX := card_endpointClassInImage_le_slice T δ F (r (q a))
  have hoccY := card_endpointClassInImage_le_slice T δ F (r (q b))
  have heqX : endpointClassInImage T δ F (r (q a)) =
      quotientFiberFinset F B (r (q a)) := by
    ext x
    simp [endpointClassInImage, quotientFiberFinset, B, q, r]
  have heqY : endpointClassInImage T δ F (r (q b)) =
      quotientFiberFinset F B (r (q b)) := by
    ext x
    simp [endpointClassInImage, quotientFiberFinset, B, q, r]
  have hfibA := card_quotient_fiber_le_subgroup F Ffin hFfin B (r (q a))
  have hfibB := card_quotient_fiber_le_subgroup F Ffin hFfin B (r (q b))
  have hXlarge (hF2 : 2 ≤ Ffin.card) : Ffin.card + 2 ≤ 2 * X.card := by
    have hraw : (quotientFiberFinset F B (r (q a))).card ≤ X.card := by
      rw [← heqX]
      exact hoccX
    change Ffin.card - (quotientFiberFinset F B (r (q a))).card ≤
      (B + Ffin).card - B.card at hdefA
    have hdefA2 : 2 * (Ffin.card -
        (quotientFiberFinset F B (r (q a))).card) ≤ Ffin.card - 2 :=
      le_trans (Nat.mul_le_mul_left 2 hdefA) hdefLocal
    have hsplit := Nat.sub_add_cancel hfibA
    omega
  have hYlarge (hF2 : 2 ≤ Ffin.card) : Ffin.card + 2 ≤ 2 * Y.card := by
    have hraw : (quotientFiberFinset F B (r (q b))).card ≤ Y.card := by
      rw [← heqY]
      exact hoccY
    change Ffin.card - (quotientFiberFinset F B (r (q b))).card ≤
      (B + Ffin).card - B.card at hdefB
    have hdefB2 : 2 * (Ffin.card -
        (quotientFiberFinset F B (r (q b))).card) ≤ Ffin.card - 2 :=
      le_trans (Nat.mul_le_mul_left 2 hdefB) hdefLocal
    have hsplit := Nat.sub_add_cancel hfibB
    omega
  have hzeroF : 0 ∈ Ffin := (hFfin 0).mpr F.zero_mem
  have hFpos : 0 < Ffin.card := Finset.card_pos.mpr ⟨0, hzeroF⟩
  have hXne : X.Nonempty := by
    refine ⟨a, ?_⟩
    exact mem_endpointClassSlice.mpr ⟨haT, rfl⟩
  have hYne : Y.Nonempty := by
    refine ⟨b, ?_⟩
    exact mem_endpointClassSlice.mpr ⟨hbT, rfl⟩
  have hXYlarge : (verticalSubgroupFinset K).card < X.card + Y.card := by
    rw [card_verticalSubgroupFinset, hKcard]
    by_cases hF2 : 2 ≤ Ffin.card
    · have hx := hXlarge hF2
      have hy := hYlarge hF2
      omega
    · have hx := hXne.card_pos
      have hy := hYne.card_pos
      omega
  exact add_eq_vadd_vertical_of_card_lt K X Y a b hXsub hYsub hXYlarge

end Erdos336
