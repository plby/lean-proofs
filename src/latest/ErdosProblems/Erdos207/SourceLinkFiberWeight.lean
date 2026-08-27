/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLinkMarkingWeight

/-! # Weighted transfer from marked link codes to their underlying families -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem sum_le_mul_sum_of_bounded_fibers
    {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (S : Finset X) (T : Finset Y) (f : X → Y) (u : X → ℝ≥0) (v : Y → ℝ≥0) (c : ℕ)
    (hmap : ∀ x ∈ S, f x ∈ T)
    (hcard : ∀ y ∈ T, (S.filter (fun x ↦ f x = y)).card ≤ c)
    (hweight : ∀ x ∈ S, u x ≤ v (f x)) :
    (∑ x ∈ S, u x) ≤ c * ∑ y ∈ T, v y := by
  calc
    _ = ∑ y ∈ T, ∑ x ∈ S with f x = y, u x := (sum_fiberwise_of_maps_to hmap u).symm
    _ ≤ ∑ y ∈ T, (c : ℝ≥0) * v y := by
      apply sum_le_sum
      intro y hy
      calc
        _ ≤ ∑ _x ∈ S with f _x = y, v y := by
          apply sum_le_sum
          intro x hx
          have hh := mem_filter.mp hx
          simpa only [hh.2] using hweight x hh.1
        _ = ((S.filter (fun x ↦ f x = y)).card : ℝ≥0) * v y := by simp
        _ ≤ _ := by gcongr; exact_mod_cast hcard y hy
    _ = _ := (mul_sum _ _ _).symm

theorem sourceLink_rooted_weight_transfer_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {A : TripleSystemOn V}
    (hpack : ∀ E ∈ F, IsPackingOn E) (hcard : ∀ E ∈ F, E.card = j - 2)
    (π : TripleOn V → ℝ≥0) (u : SourceLinkMarking V → ℝ≥0) (c : ℝ≥0)
    (H : Finset (SourceLinkCoordinate V))
    (hweight : ∀ x ∈ sourceLinkMarkings W F e A, H ⊆ x.coordinates e →
      u x ≤ c * setWeight π (x.system \ sourceLinkUnderlyingRoot H)) :
    (∑ x ∈ sourceLinkMarkings W F e A, if H ⊆ x.coordinates e then u x else 0) ≤
      (4 : ℝ≥0) ^ (j - 2) * c *
        ∑ E ∈ familyExtensions (sourceLinkUnderlyingFamily W F e H.toRight) (sourceLinkUnderlyingRoot H),
          setWeight π (E \ sourceLinkUnderlyingRoot H) := by
  classical
  rw [← sum_filter]
  let S := (sourceLinkMarkings W F e A).filter (fun x ↦ H ⊆ x.coordinates e)
  let T := familyExtensions (sourceLinkUnderlyingFamily W F e H.toRight) (sourceLinkUnderlyingRoot H)
  have hb := sum_le_mul_sum_of_bounded_fibers S T SourceLinkMarking.system u
    (fun E ↦ c * setWeight π (E \ sourceLinkUnderlyingRoot H)) (4 ^ (j - 2))
    (fun x hx ↦ sourceLinkMarking_rooted_system_mem
      ((mem_filter.mp (mem_filter.mp hx).1).2) (mem_filter.mp hx).2)
    (fun E hE ↦ by
      have hsub : S.filter (fun x ↦ x.system = E) ⊆
          (sourceLinkMarkings W F e A).filter (fun x ↦ x.system = E) := by
        intro x hx
        have hm := mem_filter.mp hx
        exact mem_filter.mpr ⟨(mem_filter.mp hm.1).1, hm.2⟩
      apply (card_le_card hsub).trans
      have hh := card_sourceLinkMarkings_system_fiber_le (W := W) (e := e) (A := A) hpack E
      rw [hcard E (sourceLinkUnderlyingFamily_data (mem_familyExtensions_iff.mp hE).1).1] at hh
      exact hh)
    (fun x hx ↦ hweight x (mem_filter.mp hx).1 (mem_filter.mp hx).2)
  simpa only [Nat.cast_pow, Nat.cast_ofNat, ← mul_sum, ← mul_assoc] using hb

theorem sourceLink_crude_extension_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {A : TripleSystemOn V}
    (hpack : ∀ E ∈ F, IsPackingOn E) (hcard : ∀ E ∈ F, E.card = j - 2)
    (f₀ f₁ f₂ π : TripleOn V → ℝ≥0) (fe : Sym2 V → ℝ≥0) (w : ℝ≥0)
    (h₀ : ∀ T, f₀ T ≤ w * π T) (h₁ : ∀ T, f₁ T ≤ w * π T)
    (h₂ : ∀ T ∈ A, f₂ T ≤ w * π T) (he : ∀ f, fe f ≤ 1)
    (H : Finset (SourceLinkCoordinate V)) :
    extensionWeight
      (fun x : sourceLinkMarkings W F e A ↦ x.1.coordinates e)
      (sourceLinkMixedWeight f₀ f₁ f₂ fe) H ≤
      (4 : ℝ≥0) ^ (j - 2) * w ^ (j - 2 - (sourceLinkUnderlyingRoot H).card) *
        ∑ E ∈ familyExtensions (sourceLinkUnderlyingFamily W F e H.toRight) (sourceLinkUnderlyingRoot H),
          setWeight π (E \ sourceLinkUnderlyingRoot H) := by
  classical
  unfold extensionWeight
  rw [← Finset.sum_subtype (sourceLinkMarkings W F e A)
    (p := fun x ↦ x ∈ sourceLinkMarkings W F e A) (fun _ ↦ Iff.rfl)
    (fun x ↦ if H ⊆ x.coordinates e then
      setWeight (sourceLinkMixedWeight f₀ f₁ f₂ fe) (x.coordinates e \ H) else 0)]
  apply sourceLink_rooted_weight_transfer_le hpack hcard π _ _ H
  intro x hx hH
  have hd : IsSourceLinkMarking W F e A x := (mem_filter.mp hx).2
  have hb := SourceLinkMarking.root_remainder_weight_le hd f₀ f₁ f₂ π fe w
    (fun T _ ↦ h₀ T) (fun T _ ↦ h₁ T) (fun T hT ↦ h₂ T (hd.2.2.2.2.2.2.1 hT)) he hH
  simpa only [hcard x.system (sourceLinkUnderlyingFamily_data hd.1).1] using hb

end

end Erdos207
