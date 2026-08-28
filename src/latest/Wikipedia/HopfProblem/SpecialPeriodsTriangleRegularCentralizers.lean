import Wikipedia.HopfProblem.SpecialPeriodsTriangleRegularTorsionWords
import Mathlib.GroupTheory.Coprod.Basic

/-!
# Centralizers of factors in a free product

A conjugate of a nonidentity factor element can return to that same factor
only when the conjugating element belongs to the factor.  We prove this
malnormality statement from actual reduced words.  In particular, the
centralizer of a nonidentity factor element stays in the factor.
-/

noncomputable section

universe u

namespace Wikipedia.HopfProblem.SpecialPeriods.CoprodTorsion

open Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]

/-- A factor in an indexed free product is malnormal.  This formulation
states directly that a nonidentity factor element cannot be conjugated
back into its factor by an element outside that factor. -/
theorem coprodI_conjugate_factor {i : ι} (a b : G i) (ha : a ≠ 1)
    (g : Monoid.CoprodI G) (h : g⁻¹ * of a * g = of b) :
    ∃ c : G i, g = of c := by
  classical
  have hb : b ≠ 1 := by
    intro hb
    have he : (of a : Monoid.CoprodI G) = 1 := by
      have hh := congrArg (fun x : Monoid.CoprodI G => g * x * g⁻¹) h
      simpa only [hb, map_one, mul_one, one_mul, mul_assoc, mul_inv_cancel,
        inv_mul_cancel, mul_inv_cancel_left] using hh
    apply ha
    apply of_injective i
    simpa only [map_one] using he
  let p : Word.Pair G i := Word.equivPair i (Word.equiv g)
  have he : Word.rcons p = Word.equiv g :=
    (Word.equivPair i).symm_apply_apply (Word.equiv g)
  have hg : g = of p.head * p.tail.prod := by
    calc
      g = (Word.equiv g).prod := ((Word.equiv (M := G)).symm_apply_apply g).symm
      _ = (Word.rcons p).prod := congrArg Word.prod he.symm
      _ = of p.head * p.tail.prod := Word.prod_rcons p
  by_cases ht : p.tail = Word.empty
  · exact ⟨p.head, by simpa only [ht, Word.prod_empty, mul_one] using hg⟩
  · obtain ⟨j, k, w, hw⟩ := NeWord.of_word p.tail ht
    have hji : j ≠ i := by
      have hh := p.fstIdx_ne
      rw [← hw] at hh
      simpa only [Word.fstIdx, NeWord.toWord, NeWord.toList_head?,
        Option.map_some, ne_eq, Option.some.injEq] using hh
    let d : G i := p.head⁻¹ * a * p.head
    have hd : d ≠ 1 := by
      intro hd
      apply ha
      have hh := congrArg (fun x : G i => p.head * x * p.head⁻¹) hd
      simpa only [d, mul_assoc, mul_inv_cancel, inv_mul_cancel, mul_one,
        one_mul, mul_inv_cancel_left] using hh
    let v : NeWord G k k :=
      NeWord.append (NeWord.append w.inv hji (NeWord.singleton d hd)) hji.symm w
    have hgp : g = of p.head * w.prod := by
      simpa only [NeWord.prod, hw] using hg
    have hv : v.prod = of b := by
      rw [hgp] at h
      simpa only [v, NeWord.append_prod, NeWord.inv_prod, NeWord.prod_singleton,
        d, map_mul, map_inv, mul_inv_rev, mul_assoc] using h
    have hvw : v.toWord = (NeWord.singleton b hb).toWord := by
      apply word_prod_injective
      exact hv.trans (NeWord.prod_singleton b hb).symm
    have hlen := congrArg (fun t : Word G => t.toList.length) hvw
    simp only [v, NeWord.toWord, NeWord.toList, List.length_append,
      List.length_singleton] at hlen
    have hpos : 0 < w.toList.length := List.length_pos_iff.mpr w.toList_ne_nil
    omega

/-- The centralizer of a nonidentity factor element of an indexed free
product is contained in the same factor. -/
theorem coprodI_commute_of {i : ι} (a : G i) (ha : a ≠ 1)
    (g : Monoid.CoprodI G) (h : Commute (of a) g) :
    ∃ b : G i, g = of b := by
  apply coprodI_conjugate_factor a a ha g
  have hh := congrArg (fun x : Monoid.CoprodI G => g⁻¹ * x) h.eq
  simpa only [mul_assoc, inv_mul_cancel_left] using hh

/-- The centralizer of a nonidentity element of the left factor of a
binary free product lies in the left factor. -/
theorem coprod_commute_inl {A B : Type u} [Group A] [Group B]
    (a : A) (ha : a ≠ 1) (g : Monoid.Coprod A B)
    (h : Commute (Monoid.Coprod.inl a) g) :
    ∃ b : A, g = Monoid.Coprod.inl b := by
  let H : Bool → Type u := fun b => cond b B A
  let : ∀ b, Group (H b) :=
    Bool.rec (inferInstance : Group A) (inferInstance : Group B)
  let toI : Monoid.Coprod A B →* Monoid.CoprodI H :=
    Monoid.Coprod.lift (Monoid.CoprodI.of (M := H) (i := false))
      (Monoid.CoprodI.of (M := H) (i := true))
  let fromI : Monoid.CoprodI H →* Monoid.Coprod A B :=
    Monoid.CoprodI.lift fun b => match b with
      | false => Monoid.Coprod.inl
      | true => Monoid.Coprod.inr
  have hleft : fromI.comp toI = MonoidHom.id (Monoid.Coprod A B) := by
    apply Monoid.Coprod.hom_ext
    · ext b
      simp [toI, fromI]
    · ext b
      simp [toI, fromI]
  have hleft_apply (x : Monoid.Coprod A B) : fromI (toI x) = x :=
    DFunLike.congr_fun hleft x
  have hc : Commute (Monoid.CoprodI.of (i := false) a) (toI g) := by
    have hh := congrArg toI h.eq
    simpa only [commute_iff_eq, map_mul, toI, Monoid.Coprod.lift_apply_inl] using hh
  obtain ⟨b, hb⟩ := coprodI_commute_of (G := H) (i := false) a ha (toI g) hc
  refine ⟨b, ?_⟩
  have hh := congrArg fromI hb
  simpa only [hleft_apply, fromI, Monoid.CoprodI.lift_of] using hh

/-- The symmetric right-factor centralizer theorem. -/
theorem coprod_commute_inr {A B : Type u} [Group A] [Group B]
    (a : B) (ha : a ≠ 1) (g : Monoid.Coprod A B)
    (h : Commute (Monoid.Coprod.inr a) g) :
    ∃ b : B, g = Monoid.Coprod.inr b := by
  have hc : Commute (Monoid.Coprod.inl a) (Monoid.Coprod.swap A B g) := by
    have hh := congrArg (Monoid.Coprod.swap A B) h.eq
    simpa only [commute_iff_eq, map_mul, Monoid.Coprod.swap_inr] using hh
  obtain ⟨b, hb⟩ := coprod_commute_inl a ha (Monoid.Coprod.swap A B g) hc
  refine ⟨b, ?_⟩
  have hh := congrArg (Monoid.Coprod.swap B A) hb
  simpa only [Monoid.Coprod.swap_swap, Monoid.Coprod.swap_inl] using hh

end Wikipedia.HopfProblem.SpecialPeriods.CoprodTorsion
