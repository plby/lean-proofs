import ErdosProblems.Erdos336.EndpointQuotientOverlapBound

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {H : Type*} [AddCommGroup H] [DecidableEq H]

/-- Maximal representatives over prescribed endpoint-quotient values lie
outside `T`; they can be counted together with any separated subset already
known to lie in `2T\T`. -/
theorem card_quotient_targets_add_separated_subset_le_double_sdiff
    (T : Finset (ℤ × H)) (δ : ℤ × H) (hδT : δ ∈ T) (hδpos : 0 < δ.1)
    (R : Finset ((ℤ × H) ⧸ AddSubgroup.zmultiples δ))
    (hR : R ⊆ (T + T).image (QuotientAddGroup.mk' (AddSubgroup.zmultiples δ)))
    (U : Finset (ℤ × H)) (hU : U ⊆ (T + T) \ T)
    (hsep : ∀ x ∈ U,
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples δ)) x ∉ R) :
    R.card + U.card ≤ ((T + T) \ T).card := by
  classical
  let Δ := AddSubgroup.zmultiples δ
  let q : (ℤ × H) →+ ((ℤ × H) ⧸ Δ) := QuotientAddGroup.mk' Δ
  let D := T + T
  let O := D \ T
  let fiber : (z : ↥R) → Finset (ℤ × H) := fun z =>
    D.filter fun x => q x = z.1
  have hfiberNe (z : ↥R) : (fiber z).Nonempty := by
    obtain ⟨x, hxD, hxq⟩ := Finset.mem_image.mp (hR z.2)
    refine ⟨x, Finset.mem_filter.mpr ⟨hxD, hxq⟩⟩
  let root : ↥R → ℤ × H := fun z =>
    (Finset.exists_max_image (fiber z) Prod.fst (hfiberNe z)).choose
  have hrootFiber (z : ↥R) : root z ∈ fiber z :=
    (Finset.exists_max_image (fiber z) Prod.fst (hfiberNe z)).choose_spec.1
  have hrootD (z : ↥R) : root z ∈ D := (Finset.mem_filter.mp (hrootFiber z)).1
  have hrootq (z : ↥R) : q (root z) = z.1 :=
    (Finset.mem_filter.mp (hrootFiber z)).2
  have hrootmax (z : ↥R) (x : ℤ × H) (hx : x ∈ fiber z) :
      x.1 ≤ (root z).1 :=
    (Finset.exists_max_image (fiber z) Prod.fst (hfiberNe z)).choose_spec.2 x hx
  have hqδ : q δ = 0 := (QuotientAddGroup.eq_zero_iff δ).mpr
    (AddSubgroup.mem_zmultiples δ)
  have hrootNotT (z : ↥R) : root z ∉ T := by
    intro hzT
    have hshiftD : δ + root z ∈ D :=
      Finset.mem_add.mpr ⟨δ, hδT, root z, hzT, rfl⟩
    have hshiftq : q (δ + root z) = z.1 := by
      rw [q.map_add, hqδ, zero_add, hrootq]
    have hshiftFiber : δ + root z ∈ fiber z :=
      Finset.mem_filter.mpr ⟨hshiftD, hshiftq⟩
    have hle := hrootmax z (δ + root z) hshiftFiber
    rw [Prod.fst_add] at hle
    omega
  have hrootO (z : ↥R) : root z ∈ O :=
    Finset.mem_sdiff.mpr ⟨hrootD z, hrootNotT z⟩
  let f : (↥R ⊕ ↥U) → ↥O := fun w =>
    match w with
    | Sum.inl z => ⟨root z, hrootO z⟩
    | Sum.inr x => ⟨x.1, hU x.2⟩
  have hf : Function.Injective f := by
    intro u v huv
    rcases u with z | x <;> rcases v with w | y
    · apply congrArg Sum.inl
      apply Subtype.ext
      rw [← hrootq z, ← hrootq w]
      exact congrArg (fun a : ↥O => q a.1) huv
    · exfalso
      have hval := congrArg (fun a : ↥O => a.1) huv
      change root z = y.1 at hval
      have hysep := hsep y.1 y.2
      apply hysep
      rw [← hval, hrootq]
      exact z.2
    · exfalso
      have hval := congrArg (fun a : ↥O => a.1) huv
      change x.1 = root w at hval
      have hxsep := hsep x.1 x.2
      apply hxsep
      rw [hval, hrootq]
      exact w.2
    · apply congrArg Sum.inr
      apply Subtype.ext
      exact congrArg (fun a : ↥O => a.1) huv
  have hc := Fintype.card_le_of_injective f hf
  change Fintype.card (↥R ⊕ ↥U) ≤ Fintype.card ↥O at hc
  rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe,
    Fintype.card_coe] at hc
  simpa [O] using hc

end Erdos336
