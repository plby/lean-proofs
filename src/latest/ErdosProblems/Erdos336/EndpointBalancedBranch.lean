import ErdosProblems.Erdos336.EndpointOutsideRoots
import ErdosProblems.Erdos336.EndpointClassSumset
import ErdosProblems.Erdos336.CriticalRepresentationDichotomy
import ErdosProblems.Erdos336.CosetDeficiencySum

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

set_option maxHeartbeats 1000000

open scoped Pointwise BigOperators

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- The balanced representation branch in Lev's endpoint argument, through
the point where only the size of the vertical intersection remains. -/
theorem endpoint_balanced_selector_count
    (T : Finset (ℤ × H)) (δ : ℤ × H)
    (hzero : ((0 : ℤ), 0) ∈ T) (hδT : δ ∈ T) (hδpos : 0 < δ.1) :
    let Δ := AddSubgroup.zmultiples δ
    let q : (ℤ × H) →+ ((ℤ × H) ⧸ Δ) := QuotientAddGroup.mk' Δ
    let B := T.image q
    let Ffin := (B + B).addStab
    let Fsub : AddSubgroup ((ℤ × H) ⧸ Δ) :=
      AddAction.stabilizer ((ℤ × H) ⧸ Δ) (B + B : Set ((ℤ × H) ⧸ Δ))
    let r : ((ℤ × H) ⧸ Δ) →+ (((ℤ × H) ⧸ Δ) ⧸ Fsub) :=
      QuotientAddGroup.mk' Fsub
    let C := B.image r
    let D := criticalNewSums C
    ∀ sel : CriticalSelector C,
      (∀ z ∈ C, selectorLoad sel z ≤ D.card) →
      (B + Ffin).card +
          D.card * (2 * Ffin.card -
            (addSubgroupFinset (endpointVerticalPart δ Fsub)).card) ≤
        ((T + T) \ T).card +
          D.card * ((B + Ffin).card - B.card) := by
  classical
  dsimp
  let Δ := AddSubgroup.zmultiples δ
  let q : (ℤ × H) →+ ((ℤ × H) ⧸ Δ) := QuotientAddGroup.mk' Δ
  let B := T.image q
  let Ffin := (B + B).addStab
  let Fsub : AddSubgroup ((ℤ × H) ⧸ Δ) :=
    AddAction.stabilizer ((ℤ × H) ⧸ Δ) (B + B : Set ((ℤ × H) ⧸ Δ))
  let r : ((ℤ × H) ⧸ Δ) →+ (((ℤ × H) ⧸ Δ) ⧸ Fsub) :=
    QuotientAddGroup.mk' Fsub
  let C := B.image r
  let D := criticalNewSums C
  intro sel hload
  change CriticalSelector C at sel
  change ∀ z ∈ C, selectorLoad sel z ≤ D.card at hload
  have hTne : T.Nonempty := ⟨(0, 0), hzero⟩
  have hBne : B.Nonempty := hTne.image q
  have hBBne : (B + B).Nonempty := hBne.add hBne
  have hzeroB : 0 ∈ B := Finset.mem_image.mpr ⟨(0, 0), hzero, q.map_zero⟩
  have hzeroFfin : 0 ∈ Ffin := Finset.zero_mem_addStab.mpr hBBne
  have hFmem (x : (ℤ × H) ⧸ Δ) : x ∈ Ffin ↔ x ∈ Fsub := by
    change x ∈ (B + B).addStab ↔ x ∈ Fsub
    rw [← SetLike.mem_coe, Finset.coe_addStab hBBne]
    simp [Fsub]
  have hclass_ne (z : (((ℤ × H) ⧸ Δ) ⧸ Fsub)) (hz : z ∈ C) :
      (endpointClassSlice T δ Fsub z).Nonempty := by
    obtain ⟨b, hbB, hbz⟩ := Finset.mem_image.mp hz
    obtain ⟨x, hxT, hxb⟩ := Finset.mem_image.mp hbB
    refine ⟨x, mem_endpointClassSlice.mpr ⟨hxT, ?_⟩⟩
    change r (q x) = z
    rw [hxb, hbz]
  have hsumclass (i : (((ℤ × H) ⧸ Δ) ⧸ Fsub)) (hi : i ∈ D)
      (x : ℤ × H)
      (hx : x ∈ endpointClassSlice T δ Fsub (sel.left i) +
        endpointClassSlice T δ Fsub (sel.right i)) : r (q x) = i := by
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hx
    rw [q.map_add, r.map_add,
      (mem_endpointClassSlice.mp ha).2,
      (mem_endpointClassSlice.mp hb).2]
    exact sel.add_eq i hi
  let piece : (((ℤ × H) ⧸ Δ) ⧸ Fsub) → Finset (ℤ × H) := fun i =>
    endpointClassSlice T δ Fsub (sel.left i) +
      endpointClassSlice T δ Fsub (sel.right i)
  let U : Finset (ℤ × H) := D.biUnion piece
  have hpieces_disjoint : (D : Set (((ℤ × H) ⧸ Δ) ⧸ Fsub)).PairwiseDisjoint piece := by
    intro i hi j hj hij
    change Disjoint (piece i) (piece j)
    rw [Finset.disjoint_left]
    intro x hxi hxj
    have hi' : i ∈ D := hi
    have hj' : j ∈ D := hj
    have hix : r (q x) = i := hsumclass i hi' x hxi
    have hjx : r (q x) = j := hsumclass j hj' x hxj
    exact hij (hix.symm.trans hjx)
  have hUcard : U.card = ∑ i ∈ D, (piece i).card := by
    exact Finset.card_biUnion hpieces_disjoint
  have hUsubDouble : U ⊆ T + T := by
    intro x hx
    obtain ⟨i, hiD, hxi⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hxi
    exact Finset.mem_add.mpr
      ⟨a, (mem_endpointClassSlice.mp ha).1,
       b, (mem_endpointClassSlice.mp hb).1, rfl⟩
  have hUoutside : U ⊆ (T + T) \ T := by
    intro x hxU
    apply Finset.mem_sdiff.mpr
    refine ⟨hUsubDouble hxU, ?_⟩
    intro hxT
    obtain ⟨i, hiD, hxi⟩ := Finset.mem_biUnion.mp hxU
    have hri : r (q x) = i := hsumclass i hiD x hxi
    have hrC : r (q x) ∈ C :=
      Finset.mem_image.mpr ⟨q x, Finset.mem_image.mpr ⟨x, hxT, rfl⟩, rfl⟩
    exact (Finset.mem_sdiff.mp hiD).2 (by simpa [← hri] using hrC)
  have hUsep : ∀ x ∈ U, q x ∉ B + Ffin := by
    intro x hxU hxBF
    obtain ⟨i, hiD, hxi⟩ := Finset.mem_biUnion.mp hxU
    have hri : r (q x) = i := hsumclass i hiD x hxi
    obtain ⟨b, hbB, f, hfF, hbf⟩ := Finset.mem_add.mp hxBF
    have hbfEq : r (b + f) = r b := by
      apply (QuotientAddGroup.eq_iff_sub_mem).mpr
      have hfsub : f ∈ Fsub := (hFmem f).mp hfF
      convert hfsub using 1 <;> abel
    have hrbC : r b ∈ C := Finset.mem_image.mpr ⟨b, hbB, rfl⟩
    have hriC : i ∈ C := by
      rw [← hri, ← hbf, hbfEq]
      exact hrbC
    exact (Finset.mem_sdiff.mp hiD).2 hriC
  let chooseB : (((ℤ × H) ⧸ Δ) ⧸ Fsub) → ((ℤ × H) ⧸ Δ) := fun z =>
    if hz : z ∈ C then (Finset.mem_image.mp hz).choose else 0
  have hchoose_mem (z : (((ℤ × H) ⧸ Δ) ⧸ Fsub)) (hz : z ∈ C) :
      chooseB z ∈ B := by
    dsimp [chooseB]
    split <;> rename_i h
    · exact (Finset.mem_image.mp h).choose_spec.1
    · exact (h hz).elim
  have hchoose_map (z : (((ℤ × H) ⧸ Δ) ⧸ Fsub)) (hz : z ∈ C) :
      r (chooseB z) = z := by
    dsimp [chooseB]
    split <;> rename_i h
    · exact (Finset.mem_image.mp h).choose_spec.2
    · exact (h hz).elim
  let leftB : (((ℤ × H) ⧸ Δ) ⧸ Fsub) → ((ℤ × H) ⧸ Δ) :=
    fun i => chooseB (sel.left i)
  let rightB : (((ℤ × H) ⧸ Δ) ⧸ Fsub) → ((ℤ × H) ⧸ Δ) :=
    fun i => chooseB (sel.right i)
  have hleft_mem (i : (((ℤ × H) ⧸ Δ) ⧸ Fsub)) (hi : i ∈ D) :
      leftB i ∈ B := hchoose_mem _ (sel.left_mem i hi)
  have hright_mem (i : (((ℤ × H) ⧸ Δ) ⧸ Fsub)) (hi : i ∈ D) :
      rightB i ∈ B := hchoose_mem _ (sel.right_mem i hi)
  have hleft_map (i : (((ℤ × H) ⧸ Δ) ⧸ Fsub)) (hi : i ∈ D) :
      r (leftB i) = sel.left i := hchoose_map _ (sel.left_mem i hi)
  have hright_map (i : (((ℤ × H) ⧸ Δ) ⧸ Fsub)) (hi : i ∈ D) :
      r (rightB i) = sel.right i := hchoose_map _ (sel.right_mem i hi)
  have hloadB : ∀ z ∈ quotientImage Fsub B,
      quotientEndpointLoad Fsub D leftB rightB z ≤ D.card := by
    intro z hz
    have hzC : z ∈ C := by simpa [quotientImage, C, r] using hz
    have hLf :
        D.filter (fun i => (QuotientAddGroup.mk' Fsub) (leftB i) = z) =
          D.filter (fun i => sel.left i = z) := by
      ext i
      rw [Finset.mem_filter, Finset.mem_filter]
      change (i ∈ D ∧ r (leftB i) = z) ↔
        (i ∈ D ∧ sel.left i = z)
      constructor
      · rintro ⟨hi, h⟩
        exact ⟨hi, (hleft_map i hi).symm.trans h⟩
      · rintro ⟨hi, h⟩
        exact ⟨hi, (hleft_map i hi).trans h⟩
    have hRf :
        D.filter (fun i => (QuotientAddGroup.mk' Fsub) (rightB i) = z) =
          D.filter (fun i => sel.right i = z) := by
      ext i
      rw [Finset.mem_filter, Finset.mem_filter]
      change (i ∈ D ∧ r (rightB i) = z) ↔
        (i ∈ D ∧ sel.right i = z)
      constructor
      · rintro ⟨hi, h⟩
        exact ⟨hi, (hright_map i hi).symm.trans h⟩
      · rintro ⟨hi, h⟩
        exact ⟨hi, (hright_map i hi).trans h⟩
    change (D.filter (fun i => r (leftB i) = z)).card +
      (D.filter (fun i => r (rightB i) = z)).card ≤ D.card
    rw [hLf, hRf]
    exact hload z hzC
  have hweighted := weighted_deficiency_le Fsub Ffin B D leftB rightB
    hleft_mem hright_mem D.card hloadB
  have hweighted' :
      (∑ i ∈ D,
        (quotientFiberDeficiency Fsub Ffin B (sel.left i) +
         quotientFiberDeficiency Fsub Ffin B (sel.right i))) ≤
      D.card * ((B + Ffin).card - B.card) := by
    rw [quotientDeficiency_eq_saturation_sub Fsub Ffin hFmem B] at hweighted
    have heq :
        (∑ i ∈ D,
          (quotientFiberDeficiency Fsub Ffin B
              ((QuotientAddGroup.mk' Fsub) (leftB i)) +
           quotientFiberDeficiency Fsub Ffin B
              ((QuotientAddGroup.mk' Fsub) (rightB i)))) =
        ∑ i ∈ D,
          (quotientFiberDeficiency Fsub Ffin B (sel.left i) +
           quotientFiberDeficiency Fsub Ffin B (sel.right i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hleft_map i hi, hright_map i hi]
    rw [heq] at hweighted
    exact hweighted
  have hpoint : ∀ i ∈ D,
      2 * Ffin.card -
          (addSubgroupFinset (endpointVerticalPart δ Fsub)).card ≤
        (piece i).card +
          quotientFiberDeficiency Fsub Ffin B (sel.left i) +
          quotientFiberDeficiency Fsub Ffin B (sel.right i) := by
    intro i hi
    have hLne := hclass_ne (sel.left i) (sel.left_mem i hi)
    have hRne := hclass_ne (sel.right i) (sel.right_mem i hi)
    have hsum := card_add_endpointClassSlices_ge T δ Fsub
      (sel.left i) (sel.right i) hLne hRne
    have hoccL := card_endpointClassInImage_le_slice T δ Fsub (sel.left i)
    have hoccR := card_endpointClassInImage_le_slice T δ Fsub (sel.right i)
    have hfiberL := card_quotient_fiber_le_subgroup
      Fsub Ffin hFmem B (sel.left i)
    have hfiberR := card_quotient_fiber_le_subgroup
      Fsub Ffin hFmem B (sel.right i)
    have hoccLraw :
        (quotientFiberFinset Fsub B (sel.left i)).card ≤
          (endpointClassSlice T δ Fsub (sel.left i)).card := by
      simpa [quotientFiberFinset, endpointClassInImage, B, q, r]
        using hoccL
    have hoccRraw :
        (quotientFiberFinset Fsub B (sel.right i)).card ≤
          (endpointClassSlice T δ Fsub (sel.right i)).card := by
      simpa [quotientFiberFinset, endpointClassInImage, B, q, r]
        using hoccR
    have hoccL' :
        Ffin.card - quotientFiberDeficiency Fsub Ffin B (sel.left i) ≤
          (endpointClassSlice T δ Fsub (sel.left i)).card := by
      change Ffin.card -
        (Ffin.card - (quotientFiberFinset Fsub B (sel.left i)).card) ≤ _
      rw [Nat.sub_sub_self hfiberL]
      exact hoccLraw
    have hoccR' :
        Ffin.card - quotientFiberDeficiency Fsub Ffin B (sel.right i) ≤
          (endpointClassSlice T δ Fsub (sel.right i)).card := by
      change Ffin.card -
        (Ffin.card - (quotientFiberFinset Fsub B (sel.right i)).card) ≤ _
      rw [Nat.sub_sub_self hfiberR]
      exact hoccRraw
    have hdL : quotientFiberDeficiency Fsub Ffin B (sel.left i) ≤ Ffin.card :=
      Nat.sub_le _ _
    have hdR : quotientFiberDeficiency Fsub Ffin B (sel.right i) ≤ Ffin.card :=
      Nat.sub_le _ _
    change 2 * Ffin.card -
        (addSubgroupFinset (endpointVerticalPart δ Fsub)).card ≤
      (endpointClassSlice T δ Fsub (sel.left i) +
       endpointClassSlice T δ Fsub (sel.right i)).card +
        quotientFiberDeficiency Fsub Ffin B (sel.left i) +
        quotientFiberDeficiency Fsub Ffin B (sel.right i)
    omega
  have hpointSum := Finset.sum_le_sum hpoint
  have hconstant :
      ∑ _i ∈ D,
        (2 * Ffin.card -
          (addSubgroupFinset (endpointVerticalPart δ Fsub)).card) =
      D.card * (2 * Ffin.card -
          (addSubgroupFinset (endpointVerticalPart δ Fsub)).card) := by
    simp
  have hrightSum :
      (∑ i ∈ D,
        ((piece i).card +
          quotientFiberDeficiency Fsub Ffin B (sel.left i) +
          quotientFiberDeficiency Fsub Ffin B (sel.right i))) =
      U.card +
        (∑ i ∈ D,
          (quotientFiberDeficiency Fsub Ffin B (sel.left i) +
           quotientFiberDeficiency Fsub Ffin B (sel.right i))) := by
    rw [hUcard]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    omega
  have hmain :
      D.card * (2 * Ffin.card -
          (addSubgroupFinset (endpointVerticalPart δ Fsub)).card) ≤
      U.card + D.card * ((B + Ffin).card - B.card) := by
    rw [← hconstant]
    calc
      (∑ _i ∈ D,
        (2 * Ffin.card -
          (addSubgroupFinset (endpointVerticalPart δ Fsub)).card)) ≤
        ∑ i ∈ D,
          ((piece i).card +
            quotientFiberDeficiency Fsub Ffin B (sel.left i) +
            quotientFiberDeficiency Fsub Ffin B (sel.right i)) := hpointSum
      _ = U.card +
          (∑ i ∈ D,
            (quotientFiberDeficiency Fsub Ffin B (sel.left i) +
             quotientFiberDeficiency Fsub Ffin B (sel.right i))) := hrightSum
      _ ≤ U.card + D.card * ((B + Ffin).card - B.card) :=
        Nat.add_le_add_left hweighted' _
  have hRsub : B + Ffin ⊆ (T + T).image q := by
    intro x hx
    obtain ⟨b, hbB, f, hfF, hbf⟩ := Finset.mem_add.mp hx
    have hbBB : b ∈ B + B :=
      Finset.mem_add.mpr ⟨b, hbB, 0, hzeroB, by simp⟩
    have hfb : f + b ∈ B + B := by
      have hact := (Finset.mem_addStab' hBBne).mp hfF hbBB
      simpa [vadd_eq_add] using hact
    have hxb : x ∈ B + B := by
      rw [← hbf]
      simpa [add_comm] using hfb
    rw [Finset.image_add]
    exact hxb
  have hroots := card_quotient_targets_add_separated_subset_le_double_sdiff
    T δ hδT hδpos (B + Ffin) hRsub U hUoutside hUsep
  change (B + Ffin).card +
      D.card * (2 * Ffin.card -
        (addSubgroupFinset (endpointVerticalPart δ Fsub)).card) ≤
    ((T + T) \ T).card + D.card * ((B + Ffin).card - B.card)
  omega

end Erdos336
