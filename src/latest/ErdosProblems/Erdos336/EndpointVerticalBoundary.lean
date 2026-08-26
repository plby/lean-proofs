import ErdosProblems.Erdos336.EndpointVerticalFullBasics

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

noncomputable def verticalEndpointFinset (δ : ℤ × H) :
    Finset ((ℤ × H) ⧸ AddSubgroup.zmultiples δ) :=
  Finset.univ.image (verticalEndpointHom δ)

noncomputable def endpointBoundaryUnion
    (T : Finset (ℤ × H)) (l : ℤ) (δ : ℤ × H) : Finset (ℤ × H) :=
  integerFiber T 0 ∪ (-δ +ᵥ integerFiber T l)

/-- The vertical endpoint quotient points are exactly the image of the two
boundary fibres, with the top fibre shifted down by the endpoint displacement. -/
theorem image_endpointBoundaryUnion_eq_inter_vertical
    (T : Finset (ℤ × H)) (l : ℤ) (hlpos : 0 < l)
    (δ : ℤ × H) (hδfst : δ.1 = l)
    (hbounds : ∀ x ∈ T, 0 ≤ x.1 ∧ x.1 ≤ l) :
    let q : (ℤ × H) →+
        ((ℤ × H) ⧸ AddSubgroup.zmultiples δ) :=
      QuotientAddGroup.mk' (AddSubgroup.zmultiples δ)
    (endpointBoundaryUnion T l δ).image q =
      T.image q ∩ verticalEndpointFinset δ := by
  classical
  dsimp
  let q : (ℤ × H) →+
      ((ℤ × H) ⧸ AddSubgroup.zmultiples δ) :=
    QuotientAddGroup.mk' (AddSubgroup.zmultiples δ)
  ext b
  constructor
  · intro hb
    obtain ⟨y, hyU, hyb⟩ := Finset.mem_image.mp hb
    apply Finset.mem_inter.mpr
    refine ⟨?_, ?_⟩
    · rcases Finset.mem_union.mp hyU with hy0 | hyt
      · exact Finset.mem_image.mpr
          ⟨y, (mem_integerFiber.mp hy0).1, hyb⟩
      · obtain ⟨x, hxl, hxy⟩ := Finset.mem_vadd_finset.mp hyt
        apply Finset.mem_image.mpr
        refine ⟨x, (mem_integerFiber.mp hxl).1, ?_⟩
        rw [← hyb]
        simp only [vadd_eq_add] at hxy
        rw [← hxy]
        have hqδ : q δ = 0 := (QuotientAddGroup.eq_zero_iff δ).mpr
          (AddSubgroup.mem_zmultiples δ)
        change q x = q (-δ + x)
        rw [q.map_add, map_neg, hqδ, neg_zero, zero_add]
    · have hyfst : y.1 = 0 := by
        rcases Finset.mem_union.mp hyU with hy0 | hyt
        · exact (mem_integerFiber.mp hy0).2
        · obtain ⟨x, hxl, hxy⟩ := Finset.mem_vadd_finset.mp hyt
          simp only [vadd_eq_add] at hxy
          rw [← hxy, Prod.fst_add, Prod.fst_neg,
            (mem_integerFiber.mp hxl).2, hδfst]
          simp
      apply Finset.mem_image.mpr
      refine ⟨y.2, Finset.mem_univ _, ?_⟩
      rw [← hyb]
      apply congrArg q
      exact Prod.ext hyfst.symm rfl
  · intro hb
    obtain ⟨hbB, hbV⟩ := Finset.mem_inter.mp hb
    obtain ⟨x, hxT, hxb⟩ := Finset.mem_image.mp hbB
    obtain ⟨k, _hk, hvb⟩ := Finset.mem_image.mp hbV
    have hqeq : q x = q ((0, k) : ℤ × H) := by
      calc
        q x = b := hxb
        _ = verticalEndpointHom δ k := hvb.symm
        _ = q ((0, k) : ℤ × H) := rfl
    have hmem : (x - ((0, k) : ℤ × H)) ∈ AddSubgroup.zmultiples δ :=
      (QuotientAddGroup.eq_iff_sub_mem).mp hqeq
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
    have hfirst := congrArg Prod.fst hn
    change n * δ.1 = x.1 - 0 at hfirst
    simp only [sub_zero] at hfirst
    rw [hδfst] at hfirst
    have hxbound := hbounds x hxT
    have hncase : n = 0 ∨ n = 1 := by
      have hn0 : 0 ≤ n := by
        apply (mul_nonneg_iff_of_pos_right hlpos).mp
        rw [hfirst]
        exact hxbound.1
      have hn1 : n ≤ 1 := by
        apply (mul_le_mul_iff_of_pos_right hlpos).mp
        rw [hfirst, one_mul]
        exact hxbound.2
      omega
    apply Finset.mem_image.mpr
    rcases hncase with rfl | rfl
    · have hxeq : x = ((0, k) : ℤ × H) := by
        rw [zero_zsmul] at hn
        have := hn.symm
        exact sub_eq_zero.mp this
      refine ⟨x, ?_, hxb⟩
      apply Finset.mem_union_left
      exact mem_integerFiber.mpr ⟨hxT, by rw [hxeq]⟩
    · have hxfst : x.1 = l := by nlinarith
      let y := -δ + x
      refine ⟨y, ?_, ?_⟩
      · apply Finset.mem_union_right
        apply Finset.mem_vadd_finset.mpr
        exact ⟨x, mem_integerFiber.mpr ⟨hxT, hxfst⟩, rfl⟩
      · rw [← hxb]
        have hqδ : q δ = 0 := (QuotientAddGroup.eq_zero_iff δ).mpr
          (AddSubgroup.mem_zmultiples δ)
        simp [y, q.map_add, hqδ]

/-- Exact boundary cardinality. -/
theorem card_endpointBoundaryUnion
    (T : Finset (ℤ × H)) (l : ℤ) (δ : ℤ × H) :
    (endpointBoundaryUnion T l δ).card + (endpointOverlap T l δ).card =
      (integerFiber T 0).card + (integerFiber T l).card := by
  classical
  let A0 := integerFiber T 0
  let Al := integerFiber T l
  let V := -δ +ᵥ Al
  have hUnion := Finset.card_union_add_card_inter A0 V
  have hVcard : V.card = Al.card := Finset.card_vadd_finset _ _
  simpa [endpointBoundaryUnion, endpointOverlap, A0, Al, V, hVcard] using hUnion

/-- The endpoint quotient is injective on the shifted boundary union. -/
theorem endpointQuotient_injective_on_boundary
    (T : Finset (ℤ × H)) (l : ℤ) (δ : ℤ × H)
    (hδpos : 0 < δ.1) (hδfst : δ.1 = l) :
    Set.InjOn (QuotientAddGroup.mk' (AddSubgroup.zmultiples δ))
      (endpointBoundaryUnion T l δ : Set (ℤ × H)) := by
  intro x hx y hy hq
  have hxfst : x.1 = 0 := by
    rcases Finset.mem_union.mp hx with hx0 | hxt
    · exact (mem_integerFiber.mp hx0).2
    · obtain ⟨u, hu, hux⟩ := Finset.mem_vadd_finset.mp hxt
      simp only [vadd_eq_add] at hux
      rw [← hux, Prod.fst_add, Prod.fst_neg,
        (mem_integerFiber.mp hu).2]
      omega
  have hyfst : y.1 = 0 := by
    rcases Finset.mem_union.mp hy with hy0 | hyt
    · exact (mem_integerFiber.mp hy0).2
    · obtain ⟨u, hu, huy⟩ := Finset.mem_vadd_finset.mp hyt
      simp only [vadd_eq_add] at huy
      rw [← huy, Prod.fst_add, Prod.fst_neg,
        (mem_integerFiber.mp hu).2]
      omega
  have hmem : x - y ∈ AddSubgroup.zmultiples δ :=
    (QuotientAddGroup.eq_iff_sub_mem).mp hq
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  have hfirst := congrArg Prod.fst hn
  change n * δ.1 = x.1 - y.1 at hfirst
  rw [hxfst, hyfst] at hfirst
  have hn0 : n = 0 := by nlinarith
  rw [hn0, zero_zsmul] at hn
  exact sub_eq_zero.mp hn.symm

/-- Cardinal form of the boundary/vertical-intersection identity. -/
theorem card_inter_verticalEndpointFinset
    (T : Finset (ℤ × H)) (l : ℤ) (hlpos : 0 < l)
    (δ : ℤ × H) (hδfst : δ.1 = l)
    (hbounds : ∀ x ∈ T, 0 ≤ x.1 ∧ x.1 ≤ l) :
    ((T.image (QuotientAddGroup.mk' (AddSubgroup.zmultiples δ))) ∩
      verticalEndpointFinset δ).card + (endpointOverlap T l δ).card =
      (integerFiber T 0).card + (integerFiber T l).card := by
  classical
  let q := QuotientAddGroup.mk' (AddSubgroup.zmultiples δ)
  have himage := image_endpointBoundaryUnion_eq_inter_vertical
    T l hlpos δ hδfst hbounds
  have hinj := endpointQuotient_injective_on_boundary T l δ (by
    rw [hδfst]; exact hlpos) hδfst
  have hcardImage : ((endpointBoundaryUnion T l δ).image q).card =
      (endpointBoundaryUnion T l δ).card :=
    Finset.card_image_iff.mpr hinj
  rw [← himage, hcardImage]
  exact card_endpointBoundaryUnion T l δ

end Erdos336
