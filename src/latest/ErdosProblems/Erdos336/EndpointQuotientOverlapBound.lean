import ErdosProblems.Erdos336.EndpointCyclicQuotient

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {H : Type*} [AddCommGroup H] [DecidableEq H]

/-- In quotienting by a non-torsion displacement `δ`, every quotient fibre
contributes one maximal representative in addition to all adjacent
`δ`-overlaps. -/
theorem card_image_add_card_shift_overlap_le
    (S : Finset (ℤ × H)) (δ : ℤ × H) (hδpos : 0 < δ.1) :
    let Δ := AddSubgroup.zmultiples δ
    let q : (ℤ × H) →+ ((ℤ × H) ⧸ Δ) := QuotientAddGroup.mk' Δ
    (S.image q).card + (S ∩ (-δ +ᵥ S)).card ≤ S.card := by
  classical
  dsimp
  let Δ := AddSubgroup.zmultiples δ
  let q : (ℤ × H) →+ ((ℤ × H) ⧸ Δ) := QuotientAddGroup.mk' Δ
  let Q : Finset ((ℤ × H) ⧸ Δ) := S.image q
  let E : Finset (ℤ × H) := S ∩ (-δ +ᵥ S)
  let F : (z : ↥Q) → Finset (ℤ × H) := fun z => S.filter fun x => q x = z.1
  have hFne (z : ↥Q) : (F z).Nonempty := by
    obtain ⟨x, hxS, hxz⟩ := Finset.mem_image.mp z.2
    refine ⟨x, ?_⟩
    simpa [F, hxz]
  let root : ↥Q → ℤ × H := fun z =>
    (Finset.exists_max_image (F z) Prod.fst (hFne z)).choose
  have hrootmem (z : ↥Q) : root z ∈ F z := by
    exact (Finset.exists_max_image (F z) Prod.fst (hFne z)).choose_spec.1
  have hrootS (z : ↥Q) : root z ∈ S := by
    exact (Finset.mem_filter.mp (hrootmem z)).1
  have hrootq (z : ↥Q) : q (root z) = z.1 := by
    exact (Finset.mem_filter.mp (hrootmem z)).2
  have hrootmax (z : ↥Q) (x : ℤ × H) (hx : x ∈ F z) :
      x.1 ≤ (root z).1 := by
    exact (Finset.exists_max_image (F z) Prod.fst (hFne z)).choose_spec.2 x hx
  have hqδ : q δ = 0 := by
    exact (QuotientAddGroup.eq_zero_iff δ).mpr
      (AddSubgroup.mem_zmultiples δ)
  have hrootNotE (z : ↥Q) : root z ∉ E := by
    intro hzE
    obtain ⟨_hzS, hzshift⟩ := Finset.mem_inter.mp hzE
    obtain ⟨y, hyS, hyeq⟩ := Finset.mem_vadd_finset.mp hzshift
    have hyform : y = δ + root z := by
      simp only [vadd_eq_add] at hyeq
      rw [← hyeq]
      abel
    have hyq : q y = z.1 := by
      rw [hyform, map_add, hqδ, zero_add, hrootq]
    have hyF : y ∈ F z := Finset.mem_filter.mpr ⟨hyS, hyq⟩
    have hle := hrootmax z y hyF
    rw [hyform, Prod.fst_add] at hle
    omega
  let f : (↥Q ⊕ ↥E) → ↥S := fun u =>
    match u with
    | Sum.inl z => ⟨root z, hrootS z⟩
    | Sum.inr x => ⟨x.1, (Finset.mem_inter.mp x.2).1⟩
  have hf : Function.Injective f := by
    intro u v huv
    rcases u with z | x <;> rcases v with w | y
    · apply congrArg Sum.inl
      apply Subtype.ext
      rw [← hrootq z, ← hrootq w]
      exact congrArg (fun a : ↥S => q a.1) huv
    · exfalso
      have hval := congrArg (fun a : ↥S => a.1) huv
      change root z = y.1 at hval
      apply hrootNotE z
      rw [hval]
      exact y.2
    · exfalso
      have hval := congrArg (fun a : ↥S => a.1) huv
      change x.1 = root w at hval
      apply hrootNotE w
      rw [← hval]
      exact x.2
    · apply congrArg Sum.inr
      apply Subtype.ext
      exact congrArg (fun a : ↥S => a.1) huv
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_sum, Fintype.card_coe] at hc
  simpa [Q, E, q, Δ] using hc

/-- Aligned endpoint overlap produces distinct adjacent-`δ` pairs in the
double sumset. -/
theorem add_endpointOverlap_subset_double_shift_overlap
    (T : Finset (ℤ × H)) (l : ℤ) (δ : ℤ × H) :
    T + endpointOverlap T l δ ⊆
      (T + T) ∩ (-δ +ᵥ (T + T)) := by
  intro s hs
  obtain ⟨a, ha, e, he, hae⟩ := Finset.mem_add.mp hs
  obtain ⟨he0, heshift⟩ := Finset.mem_inter.mp he
  have heT := (mem_integerFiber.mp he0).1
  obtain ⟨u, huTop, hue⟩ := Finset.mem_vadd_finset.mp heshift
  have huT := (mem_integerFiber.mp huTop).1
  apply Finset.mem_inter.mpr
  refine ⟨Finset.mem_add.mpr ⟨a, ha, e, heT, hae⟩, ?_⟩
  apply Finset.mem_vadd_finset.mpr
  refine ⟨a + u, Finset.mem_add.mpr ⟨a, ha, u, huT, rfl⟩, ?_⟩
  simp only [vadd_eq_add] at hue ⊢
  rw [← hae, ← hue]
  abel

/-- The quotient double sumset plus the endpoint-generated overlap is bounded
by the original double sumset. -/
theorem card_image_double_add_card_add_endpointOverlap_le
    (T : Finset (ℤ × H)) (l : ℤ) (δ : ℤ × H) (hδpos : 0 < δ.1) :
    let Δ := AddSubgroup.zmultiples δ
    let q : (ℤ × H) →+ ((ℤ × H) ⧸ Δ) := QuotientAddGroup.mk' Δ
    ((T + T).image q).card + (T + endpointOverlap T l δ).card ≤
      (T + T).card := by
  dsimp
  let Δ := AddSubgroup.zmultiples δ
  let q : (ℤ × H) →+ ((ℤ × H) ⧸ Δ) := QuotientAddGroup.mk' Δ
  have hsub := add_endpointOverlap_subset_double_shift_overlap T l δ
  have hcard := Finset.card_le_card hsub
  have hbase := card_image_add_card_shift_overlap_le (T + T) δ hδpos
  change ((T + T).image q).card + (T + endpointOverlap T l δ).card ≤
    (T + T).card
  change ((T + T).image q).card +
      ((T + T) ∩ (-δ +ᵥ (T + T))).card ≤ (T + T).card at hbase
  omega

end Erdos336
