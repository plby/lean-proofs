import Mathlib
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
Portions of this file are adapted from Y. Paz, `PCF-Theory`,
licensed under Apache 2.0.  They have been updated for Mathlib v4.33.0.
-/

noncomputable section

universe u v w

open Set Order Cardinal

namespace Ordinal

instance : Nonempty (Iio omega0.{u}) := ⟨0, omega0_pos⟩

theorem coe_succ_Iio {α : Type*} [PartialOrder α] [SuccOrder α] {a : α} (h : IsSuccPrelimit a)
    {x : Iio a} : (succ x).1 = succ x.1 := by
  apply coe_succ_of_mem
  have := Subtype.mem x
  rw [mem_Iio] at this ⊢
  exact h.succ_lt this

theorem succ_Iio {α : Type*} [PartialOrder α] [SuccOrder α] {a : α} (h : IsSuccPrelimit a)
    {x : Iio a} : succ x = ⟨succ x.1, h.succ_lt x.2⟩ :=
  Subtype.val_inj.mp <| coe_succ_Iio h

-- #19189
/-- The order isomorphism between ℕ and the first ω ordinals. -/
@[simps! apply]
def relIso_nat_omega0 : ℕ ≃o Iio ω where
  toFun n := ⟨n, nat_lt_omega0 n⟩
  invFun n := Classical.choose (lt_omega0.1 n.2)
  left_inv n := by
    have h : ∃ m : ℕ, n = (m : Ordinal) := ⟨n, rfl⟩
    exact (Nat.cast_inj.1 (Classical.choose_spec h)).symm
  right_inv n := Subtype.eq (Classical.choose_spec (lt_omega0.1 n.2)).symm
  map_rel_iff' := by
    intro a b
    change (a : Ordinal) ≤ (b : Ordinal) ↔ a ≤ b
    exact_mod_cast Iff.rfl

@[simp]
theorem relIso_nat_omega0_coe_symm_apply (o : Iio ω) : relIso_nat_omega0.symm o = o.1 := by
  obtain ⟨o, h⟩ := o
  rcases lt_omega0.mp h with ⟨n, hn⟩
  simp_rw [hn]
  exact congrArg Nat.cast <| relIso_nat_omega0.symm_apply_apply n

theorem strictMono_of_succ_lt_omega0 {α : Type*} [Preorder α] (f : Iio ω → α)
    (hf : ∀ i, f i < f (succ i)) : StrictMono f := by
  have mono := strictMono_nat_of_lt_succ fun n ↦
    (succ_Iio isSuccLimit_omega0.isSuccPrelimit) ▸ hf ⟨n, natCast_lt_omega0 n⟩
  convert mono.comp relIso_nat_omega0.symm.strictMono
  ext
  simp

-- #14060
/-- The lift of a supremum is the supremum of the lifts. -/
theorem lift_sSup {s : Set Ordinal} (hs : BddAbove s) :
    lift.{u} (sSup s) = sSup (lift.{u} '' s) := by
  apply ((le_csSup_iff' (Ordinal.bddAbove_image.{_,u} hs _)).2 fun c hc => _).antisymm (csSup_le' _)
  · intro c hc
    by_contra h
    have := (not_le.1 h).le
    obtain ⟨d, rfl⟩ := mem_range_lift_of_le this
    simp_rw [lift_le] at h hc
    rw [csSup_le_iff' hs] at h
    exact h fun a ha => lift_le.1 <| hc (mem_image_of_mem _ ha)
  · rintro i ⟨j, hj, rfl⟩
    exact lift_le.2 (le_csSup hs hj)

/-- The lift of a supremum is the supremum of the lifts. -/
theorem lift_iSup {ι : Type v} {f : ι → Ordinal.{w}} (hf : BddAbove (range f)) :
    lift.{u} (iSup f) = ⨆ i, lift.{u} (f i) := by
  rw [iSup, iSup, lift_sSup hf, ← range_comp]
  simp [Function.comp_def]


@[elab_as_elim]
def boundedRec {l : Ordinal} {C : Iio l → Sort*}
    (H : (o : Iio l) → ((o' : Iio o) → C o') → C o) (o : Iio l) : C o :=
  lt_wf.fix (C := fun p ↦ (h : p < l) → C ⟨p, h⟩)
    (fun o h h' ↦ H ⟨o, h'⟩ fun o' ↦ h o'.1 o'.2 (o'.2.trans h')) o o.2

theorem boundedRec_eq {l} {C} (H o) :
    @boundedRec l C H o = H o (fun o' ↦ @boundedRec l C H o') := by
  rcases o with ⟨o, ho⟩
  unfold boundedRec
  rw [WellFounded.fix_eq]
  congr 1

/-- There doesn't exist a chain of subsets of `S` of length longer than `#S`. -/
theorem not_exists_ssubset_chain_lift {α : Type u} {S : Set α} {ℓ : Ordinal.{v}}
    (hℓ : IsSuccLimit ℓ)
    (h : Cardinal.lift.{v, u} #S < Cardinal.lift.{u, v} ℓ.card) :
    ¬ ∃ f : Iio ℓ → Set α, (∀ o, f o ⊆ S) ∧ (∀ o p, o < p → f p ⊂ f o) := by
  rintro ⟨f, hf⟩
  have hsub : ∀ (o p : ↑(Iio ℓ)), o ≤ p → f p ⊆ f o := by
    intro o p h
    rcases h.lt_or_eq with h' | h'
    · exact (hf.2 _ _ h').subset
    · rw [h']
  suffices g : Iio ℓ ↪ S by
    have hle := lift_mk_le'.mpr ⟨g⟩
    rw [mk_Iio_ordinal, Cardinal.lift_lift] at hle
    have aux1 : Cardinal.lift.{v + 1, u} #↑S =
        Cardinal.lift.{v + 1} (Cardinal.lift.{v, u} #↑S) :=
      (Cardinal.lift_lift _).symm
    have aux2 : Cardinal.lift.{max (v + 1) u, v} ℓ.card =
        Cardinal.lift.{v + 1} (Cardinal.lift.{u, v} ℓ.card) :=
      (Cardinal.lift_lift _).symm
    rw [aux1, aux2, Cardinal.lift_le] at hle
    exact (not_le_of_gt h) hle
  use fun i ↦ by
    have := trivial
    have := hf.2 i (succ i) (by
      change i.1 < (succ i).1
      rw [coe_succ_Iio hℓ.isSuccPrelimit]
      exact lt_succ _)
    let x := Classical.choose <| exists_of_ssubset this
    have xmemS : x ∈ S := hf.1 i (((exists_of_ssubset this).choose_spec).1)
    exact ⟨x, xmemS⟩
  intro i j
  simp only [Subtype.mk.injEq]
  intro h
  generalize_proofs _ pfi pfj at h
  have spec := Classical.choose_spec pfi
  have spec' := h ▸ Classical.choose_spec pfj
  set x := Classical.choose pfi
  refine ((lt_trichotomy i j).resolve_left ?_).resolve_right ?_
  · intro ho
    have : succ i ≤ j := succ_le_of_lt ho
    exact spec.2 <| hsub _ _ this spec'.1
  · intro ho
    have : succ j ≤ i := succ_le_of_lt ho
    exact spec'.2 <| hsub _ _ this spec.1

theorem mk_Iio_subtype {o : Ordinal} {p : Iio o} : #(Iio p) = #(Iio p.1) := by
  apply mk_congr
  let f : Iio p → Iio p.1 := fun ⟨x, h⟩ ↦ ⟨x, h⟩
  let g : Iio p.1 → Iio p := fun ⟨x, h⟩ ↦ ⟨⟨x,
    have : p.1 < o := p.2
    have := h.trans this
    this⟩, h⟩
  exact ⟨f, g, congrFun rfl, congrFun rfl⟩

theorem two_lt_aleph0 : 2 < ℵ₀ := nat_lt_aleph0 2

theorem succ_pred_of_finite {o : Ordinal} (h : 0 < o) (h' : o < ω) : succ o.pred = o := by
  rw [succ_pred_eq_iff_not_isSuccPrelimit]
  intro ho
  exact (not_le_of_gt h')
    (omega0_le_of_isSuccLimit ⟨fun hm ↦ h.ne' hm.eq_bot, ho⟩)

theorem type_Iio (α : Ordinal.{u}) : type (· < · : Iio α → Iio α → Prop) = lift.{u + 1} α := by
  exact type_lt_Iio α

theorem isLimit_iff' {o : Ordinal} : IsSuccLimit o ↔ o ≠ 0 ∧ ∀ x < o, succ x < o := by
  rw [isSuccLimit_iff, isSuccPrelimit_iff_succ_lt]
