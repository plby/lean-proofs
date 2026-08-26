import ErdosProblems.Erdos336.EndpointVerticalEndpointMiddle

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

set_option maxHeartbeats 1600000

open scoped Pointwise

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

noncomputable def strictInteriorPart
    (S : Finset (ℤ × H)) (l : ℤ) : Finset (ℤ × H) :=
  S.filter fun x => 0 < x.1 ∧ x.1 < l

@[simp] theorem mem_strictInteriorPart
    {S : Finset (ℤ × H)} {l : ℤ} {x : ℤ × H} :
    x ∈ strictInteriorPart S l ↔ x ∈ S ∧ 0 < x.1 ∧ x.1 < l := by
  simp [strictInteriorPart]

/-- Every missing point after vertical saturation is either one of the three
aligned endpoint-pair holes, or a translate of an original interior hole.
Which translate occurs is determined by which endpoint fibre is larger. -/
theorem vertical_full_missing_classification
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
    let A := integerFiber T 0
    let B := -δ +ᵥ integerFiber T l
    let E := (T + V) \ T
    ∀ m ∈ ((T + T) + V) \ (T + T),
      ((A.card ≤ (integerFiber T l).card) →
        m ∈ V \ (A + A) ∨
        -δ + m ∈ V \ (A + B) ∨
        -(δ + δ) + m ∈ V \ (B + B) ∨
        m ∈ strictInteriorPart E l) ∧
      (((integerFiber T l).card ≤ A.card) →
        m ∈ V \ (A + A) ∨
        -δ + m ∈ V \ (A + B) ∨
        -(δ + δ) + m ∈ V \ (B + B) ∨
        -δ + m ∈ strictInteriorPart E l) := by
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
  intro m hm
  have hmSat := (Finset.mem_sdiff.mp hm).1
  have hmNot := (Finset.mem_sdiff.mp hm).2
  obtain ⟨s, hs, v, hv, hsv⟩ := Finset.mem_add.mp hmSat
  obtain ⟨x, hxT, y, hyT, hxy⟩ := Finset.mem_add.mp hs
  have hδfst : δ.1 = l := (mem_integerFiber.mp hδ).2
  have hboundsT : ∀ z ∈ T, 0 ≤ z.1 ∧ z.1 ≤ l := by
    intro z hz
    exact hbounds z.1 (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
  have hxbound := hboundsT x hxT
  have hybound := hboundsT y hyT
  have hxcase : x.1 = 0 ∨ x.1 = l ∨ (0 < x.1 ∧ x.1 < l) := by omega
  have hycase : y.1 = 0 ∨ y.1 = l ∨ (0 < y.1 ∧ y.1 < l) := by omega
  have hTne : T.Nonempty := ⟨(0, 0), hzero⟩
  have hBqne : Bq.Nonempty := hTne.image q
  have hBBne : (Bq + Bq).Nonempty := hBqne.add hBqne
  have hFmem (z : (ℤ × H) ⧸ Δ) : z ∈ Ffin ↔ z ∈ Fsub := by
    change z ∈ (Bq + Bq).addStab ↔ z ∈ Fsub
    rw [← SetLike.mem_coe, Finset.coe_addStab hBBne]
    simp [Fsub]
  have hdefRaw := endpointQuotient_nontrivial_stabilizer T l hlpos hzero δ hδ
    h0 hl hbounds hthreshold hexpand
  have hdef : 2 * ((Bq + Ffin).card - Bq.card) ≤ Ffin.card - 2 := by
    simpa [Bq, Ffin, q, Δ] using hdefRaw.2
  have hfibers := endpoint_fibers_single_vertical_cosets T l hlpos hzero δ hδ
    h0 hl hbounds hthreshold hexpand hfull
  change A ⊆ V ∧ Al ⊆ δ +ᵥ V at hfibers
  have hA0 (z : ℤ × H) (hzT : z ∈ T) (hz0 : z.1 = 0) : z ∈ A :=
    mem_integerFiber.mpr ⟨hzT, hz0⟩
  have hAl (z : ℤ × H) (hzT : z ∈ T) (hzl : z.1 = l) : z ∈ Al :=
    mem_integerFiber.mpr ⟨hzT, hzl⟩
  have hBshift (z : ℤ × H) (hzAl : z ∈ Al) : -δ + z ∈ B :=
    Finset.mem_vadd_finset.mpr ⟨z, hzAl, rfl⟩
  have hv0 : v.1 = 0 := (mem_verticalSubgroupFinset.mp hv).1
  have hmint : m.1 = x.1 + y.1 := by
    rw [← hsv, ← hxy, Prod.fst_add, Prod.fst_add, hv0, add_zero]
  have hsumEq : m = x + y + v := by rw [← hsv, ← hxy]
  have hfullInterior (hxI : 0 < x.1 ∧ x.1 < l)
      (hyI : 0 < y.1 ∧ y.1 < l) : m ∈ T + T := by
    have heq := add_endpointClassSlices_eq_vertical_coset
      T l hlpos δ hδfst hboundsT Fsub Ffin hFmem hfull hdef
        x y hxT hyT hxI.1 hxI.2 hyI.1 hyI.2
    let Xu := endpointClassSlice T δ Fsub
      ((QuotientAddGroup.mk' Fsub) (q x))
    let Xw := endpointClassSlice T δ Fsub
      ((QuotientAddGroup.mk' Fsub) (q y))
    change Xu + Xw = (x + y) +ᵥ V at heq
    have hmCoset : m ∈ (x + y) +ᵥ V := by
      apply Finset.mem_vadd_finset.mpr
      exact ⟨v, hv, by simpa [hsumEq]⟩
    have hmSlices : m ∈ Xu + Xw := by rw [heq]; exact hmCoset
    exact Finset.add_subset_add
      (fun z hz => (mem_endpointClassSlice.mp hz).1)
      (fun z hz => (mem_endpointClassSlice.mp hz).1) hmSlices
  have hfullLarger (u : ℤ × H) (huT : u ∈ T)
      (huI : 0 < u.1 ∧ u.1 < l) :=
    add_larger_endpoint_fiber_class_eq_vertical
      T l hlpos hzero δ hδ h0 hl hbounds hthreshold hexpand hfull
        u huT huI.1 huI.2
  have endpoint00 (hx0 : x.1 = 0) (hy0 : y.1 = 0) :
      m ∈ V \ (A + A) := by
    apply Finset.mem_sdiff.mpr
    constructor
    · have hxV := hfibers.1 (hA0 x hxT hx0)
      have hyV := hfibers.1 (hA0 y hyT hy0)
      apply mem_verticalSubgroupFinset.mpr
      have hxK := (mem_verticalSubgroupFinset.mp hxV).2
      have hyK := (mem_verticalSubgroupFinset.mp hyV).2
      have hvK := (mem_verticalSubgroupFinset.mp hv).2
      refine ⟨by rw [hmint, hx0, hy0]; simp,
        ?_⟩
      have hsnd := congrArg Prod.snd hsumEq
      simp only [Prod.snd_add] at hsnd
      rw [hsnd]
      exact K.add_mem (K.add_mem hxK hyK) hvK
    · intro hmAA
      exact hmNot (Finset.add_subset_add
        (fun _ hz => (mem_integerFiber.mp hz).1)
        (fun _ hz => (mem_integerFiber.mp hz).1) hmAA)
  have endpoint0l (b t : ℤ × H) (hbT : b ∈ T) (htT : t ∈ T)
      (hb0 : b.1 = 0) (htl : t.1 = l) (hbt : b + t = x + y) :
      -δ + m ∈ V \ (A + B) := by
    have hmEq : m = b + t + v := by rw [hsumEq, ← hbt]
    apply Finset.mem_sdiff.mpr
    constructor
    · have hbV := hfibers.1 (hA0 b hbT hb0)
      have htCos := hfibers.2 (hAl t htT htl)
      obtain ⟨wt, hwtV, hwtEq⟩ := Finset.mem_vadd_finset.mp htCos
      apply mem_verticalSubgroupFinset.mpr
      refine ⟨by rw [Prod.fst_add, Prod.fst_neg]; simp [hmEq, hb0, htl, hv0, hδfst],
        ?_⟩
      have hbK := (mem_verticalSubgroupFinset.mp hbV).2
      have hwtK := (mem_verticalSubgroupFinset.mp hwtV).2
      have hvK := (mem_verticalSubgroupFinset.mp hv).2
      simp only [vadd_eq_add] at hwtEq
      have hsnd := congrArg Prod.snd hmEq
      have hwtSnd := congrArg Prod.snd hwtEq
      simp only [Prod.snd_add, Prod.snd_neg] at hsnd hwtSnd ⊢
      rw [hsnd, ← hwtSnd]
      convert K.add_mem hbK (K.add_mem hwtK hvK) using 1 <;> abel
    · intro hz
      obtain ⟨a0, ha0, b0, hb0, hab⟩ := Finset.mem_add.mp hz
      obtain ⟨yt, hytAl, hytb⟩ := Finset.mem_vadd_finset.mp hb0
      apply hmNot
      apply Finset.mem_add.mpr
      refine ⟨a0, (mem_integerFiber.mp ha0).1, yt,
        (mem_integerFiber.mp hytAl).1, ?_⟩
      simp only [vadd_eq_add] at hytb
      calc
        a0 + yt = δ + (a0 + b0) := by rw [← hytb]; abel
        _ = δ + (-δ + m) := by rw [hab]
        _ = m := by abel
  have endpointll (hxl : x.1 = l) (hyl : y.1 = l) :
      -(δ + δ) + m ∈ V \ (B + B) := by
    apply Finset.mem_sdiff.mpr
    constructor
    · have hxCos := hfibers.2 (hAl x hxT hxl)
      have hyCos := hfibers.2 (hAl y hyT hyl)
      obtain ⟨wx, hwxV, hwxEq⟩ := Finset.mem_vadd_finset.mp hxCos
      obtain ⟨wy, hwyV, hwyEq⟩ := Finset.mem_vadd_finset.mp hyCos
      apply mem_verticalSubgroupFinset.mpr
      refine ⟨by rw [Prod.fst_add, Prod.fst_neg, Prod.fst_add,
        hmint, hxl, hyl, hδfst]; simp, ?_⟩
      have hwxK := (mem_verticalSubgroupFinset.mp hwxV).2
      have hwyK := (mem_verticalSubgroupFinset.mp hwyV).2
      have hvK := (mem_verticalSubgroupFinset.mp hv).2
      simp only [vadd_eq_add] at hwxEq hwyEq
      have hsnd := congrArg Prod.snd hsumEq
      have hwxSnd := congrArg Prod.snd hwxEq
      have hwySnd := congrArg Prod.snd hwyEq
      simp only [Prod.snd_add, Prod.snd_neg] at hsnd hwxSnd hwySnd ⊢
      rw [hsnd, ← hwxSnd, ← hwySnd]
      convert K.add_mem (K.add_mem hwxK hwyK) hvK using 1 <;> abel
    · intro hz
      obtain ⟨bx, hbx, by0, hby0, hbxy⟩ := Finset.mem_add.mp hz
      obtain ⟨xt, hxtAl, hxtbx⟩ := Finset.mem_vadd_finset.mp hbx
      obtain ⟨yt, hytAl, hytby⟩ := Finset.mem_vadd_finset.mp hby0
      apply hmNot
      apply Finset.mem_add.mpr
      refine ⟨xt, (mem_integerFiber.mp hxtAl).1,
        yt, (mem_integerFiber.mp hytAl).1, ?_⟩
      simp only [vadd_eq_add] at hxtbx hytby
      calc
        xt + yt = (δ + bx) + (δ + by0) := by rw [← hxtbx, ← hytby]; abel
        _ = (δ + δ) + (bx + by0) := by abel
        _ = (δ + δ) + (-(δ + δ) + m) := by rw [hbxy]
        _ = m := by abel
  have smaller0Interior (u b : ℤ × H) (huT : u ∈ T)
      (huI : 0 < u.1 ∧ u.1 < l) (hbT : b ∈ T) (hb0 : b.1 = 0)
      (hub : u + b = x + y) : m ∈ strictInteriorPart E l := by
    have hmEq : m = u + b + v := by rw [hsumEq, ← hub]
    have hmFst : m.1 = u.1 + b.1 := by
      rw [hmEq, Prod.fst_add, Prod.fst_add, hv0, add_zero]
    apply mem_strictInteriorPart.mpr
    refine ⟨Finset.mem_sdiff.mpr ⟨?_, ?_⟩, ?_, ?_⟩
    · apply Finset.mem_add.mpr
      let w := b + v
      have hwV : w ∈ V := by
        have hbV := hfibers.1 (hA0 b hbT hb0)
        apply mem_verticalSubgroupFinset.mpr
        exact ⟨by simp [w, (mem_verticalSubgroupFinset.mp hbV).1, hv0],
          K.add_mem (mem_verticalSubgroupFinset.mp hbV).2
            (mem_verticalSubgroupFinset.mp hv).2⟩
      refine ⟨u, huT, w, hwV, ?_⟩
      dsimp [w]
      rw [hmEq]
      abel
    · intro hmT
      exact hmNot (Finset.mem_add.mpr ⟨(0, 0), hzero, m, hmT, by simp⟩)
    · rw [hmFst, hb0]
      omega
    · rw [hmFst, hb0]
      omega
  have smallerLInterior (u t : ℤ × H) (huT : u ∈ T)
      (huI : 0 < u.1 ∧ u.1 < l) (htT : t ∈ T) (htl : t.1 = l)
      (hut : u + t = x + y) : -δ + m ∈ strictInteriorPart E l := by
    have hmEq : m = u + t + v := by rw [hsumEq, ← hut]
    have hmFst : m.1 = u.1 + t.1 := by
      rw [hmEq, Prod.fst_add, Prod.fst_add, hv0, add_zero]
    apply mem_strictInteriorPart.mpr
    refine ⟨Finset.mem_sdiff.mpr ⟨?_, ?_⟩, ?_, ?_⟩
    · have htCos := hfibers.2 (hAl t htT htl)
      obtain ⟨w, hwV, hwt⟩ := Finset.mem_vadd_finset.mp htCos
      apply Finset.mem_add.mpr
      refine ⟨u, huT, w + v, ?_, ?_⟩
      · apply mem_verticalSubgroupFinset.mpr
        exact ⟨by simp [(mem_verticalSubgroupFinset.mp hwV).1, hv0],
          K.add_mem (mem_verticalSubgroupFinset.mp hwV).2
            (mem_verticalSubgroupFinset.mp hv).2⟩
      · simp only [vadd_eq_add] at hwt
        rw [hmEq, ← hwt]
        abel
    · intro hzT
      apply hmNot
      exact Finset.mem_add.mpr ⟨δ, (mem_integerFiber.mp hδ).1,
        -δ + m, hzT, by abel⟩
    · rw [Prod.fst_add, Prod.fst_neg, hmFst, htl, hδfst]
      omega
    · rw [Prod.fst_add, Prod.fst_neg, hmFst, htl, hδfst]
      omega
  constructor
  · intro hord
    rcases hxcase with hx0 | hxl | hxI <;>
      rcases hycase with hy0 | hyl | hyI
    · exact Or.inl (endpoint00 hx0 hy0)
    · exact Or.inr (Or.inl (endpoint0l x y hxT hyT hx0 hyl rfl))
    · exact Or.inr (Or.inr (Or.inr
        (smaller0Interior y x hyT hyI hxT hx0 (add_comm y x))))
    · exact Or.inr (Or.inl
        (endpoint0l y x hyT hxT hy0 hxl (add_comm y x)))
    · exact Or.inr (Or.inr (Or.inl (endpointll hxl hyl)))
    · exfalso
      apply hmNot
      have hfill := (hfullLarger y hyT hyI).1 hord
      have hxAl := hAl x hxT hxl
      have hyX : y ∈ endpointClassSlice T δ Fsub
          ((QuotientAddGroup.mk' Fsub) (q y)) :=
        mem_endpointClassSlice.mpr ⟨hyT, rfl⟩
      have hmCos : m ∈ (δ + y) +ᵥ V := by
        obtain ⟨wx, hwx, hwxEq⟩ := Finset.mem_vadd_finset.mp (hfibers.2 hxAl)
        apply Finset.mem_vadd_finset.mpr
        refine ⟨wx + v, ?_, ?_⟩
        · apply mem_verticalSubgroupFinset.mpr
          exact ⟨by simp [(mem_verticalSubgroupFinset.mp hwx).1, hv0],
            K.add_mem (mem_verticalSubgroupFinset.mp hwx).2
              (mem_verticalSubgroupFinset.mp hv).2⟩
        · simp only [vadd_eq_add] at hwxEq ⊢
          rw [hsumEq, ← hwxEq]
          abel
      rw [← hfill] at hmCos
      exact Finset.add_subset_add
        (fun z hz => (mem_integerFiber.mp hz).1)
        (fun z hz => (mem_endpointClassSlice.mp hz).1) hmCos
    · exact Or.inr (Or.inr (Or.inr
        (smaller0Interior x y hxT hxI hyT hy0 rfl)))
    · exfalso
      apply hmNot
      have hfill := (hfullLarger x hxT hxI).1 hord
      have hyAl := hAl y hyT hyl
      have hmCos : m ∈ (δ + x) +ᵥ V := by
        obtain ⟨wy, hwy, hwyEq⟩ := Finset.mem_vadd_finset.mp (hfibers.2 hyAl)
        apply Finset.mem_vadd_finset.mpr
        refine ⟨wy + v, ?_, ?_⟩
        · apply mem_verticalSubgroupFinset.mpr
          exact ⟨by simp [(mem_verticalSubgroupFinset.mp hwy).1, hv0],
            K.add_mem (mem_verticalSubgroupFinset.mp hwy).2
              (mem_verticalSubgroupFinset.mp hv).2⟩
        · simp only [vadd_eq_add] at hwyEq ⊢
          rw [hsumEq, ← hwyEq]
          abel
      rw [← hfill] at hmCos
      exact Finset.add_subset_add
        (fun z hz => (mem_integerFiber.mp hz).1)
        (fun z hz => (mem_endpointClassSlice.mp hz).1) hmCos
    · exact (hmNot (hfullInterior hxI hyI)).elim
  · intro hord
    rcases hxcase with hx0 | hxl | hxI <;>
      rcases hycase with hy0 | hyl | hyI
    · exact Or.inl (endpoint00 hx0 hy0)
    · exact Or.inr (Or.inl (endpoint0l x y hxT hyT hx0 hyl rfl))
    · exfalso
      apply hmNot
      have hfill := (hfullLarger y hyT hyI).2 hord
      have hxA := hA0 x hxT hx0
      have hmCos : m ∈ y +ᵥ V := by
        apply Finset.mem_vadd_finset.mpr
        refine ⟨x + v, ?_, ?_⟩
        · apply mem_verticalSubgroupFinset.mpr
          have hxV := hfibers.1 hxA
          exact ⟨by simp [(mem_verticalSubgroupFinset.mp hxV).1, hv0],
            K.add_mem (mem_verticalSubgroupFinset.mp hxV).2
              (mem_verticalSubgroupFinset.mp hv).2⟩
        · simp only [vadd_eq_add]
          rw [hsumEq]
          abel
      rw [← hfill] at hmCos
      exact Finset.add_subset_add
        (fun z hz => (mem_integerFiber.mp hz).1)
        (fun z hz => (mem_endpointClassSlice.mp hz).1) hmCos
    · exact Or.inr (Or.inl
        (endpoint0l y x hyT hxT hy0 hxl (add_comm y x)))
    · exact Or.inr (Or.inr (Or.inl (endpointll hxl hyl)))
    · exact Or.inr (Or.inr (Or.inr
        (smallerLInterior y x hyT hyI hxT hxl (add_comm y x))))
    · exfalso
      apply hmNot
      have hfill := (hfullLarger x hxT hxI).2 hord
      have hyA := hA0 y hyT hy0
      have hmCos : m ∈ x +ᵥ V := by
        apply Finset.mem_vadd_finset.mpr
        refine ⟨y + v, ?_, ?_⟩
        · apply mem_verticalSubgroupFinset.mpr
          have hyV := hfibers.1 hyA
          exact ⟨by simp [(mem_verticalSubgroupFinset.mp hyV).1, hv0],
            K.add_mem (mem_verticalSubgroupFinset.mp hyV).2
              (mem_verticalSubgroupFinset.mp hv).2⟩
        · simp only [vadd_eq_add]
          rw [hsumEq]
          abel
      rw [← hfill] at hmCos
      exact Finset.add_subset_add
        (fun z hz => (mem_integerFiber.mp hz).1)
        (fun z hz => (mem_endpointClassSlice.mp hz).1) hmCos
    · exact Or.inr (Or.inr (Or.inr
        (smallerLInterior x y hxT hxI hyT hyl rfl)))
    · exact (hmNot (hfullInterior hxI hyI)).elim

end Erdos336
