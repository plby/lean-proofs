/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SeededHammock

/-!
# Bounded maximal-up-to extensions of seeded hammocks

Every small hammock seed extends to a maximal-up-to-`kappa` hammock without
losing any seed member.  Start with an inclusion-maximal extension.  If it is
small, use it.  Otherwise retain the seed together with a `kappa`-sized
subfamily, while a separate `kappa⁺`-sized subfamily witnesses the large
branch of `MaximalUpTo`.

The final definition is total on arbitrary seeds.  Invalid or oversized
seeds select the empty family; valid small seeds select the bounded extension
proved above.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint

open DirectedPath Alternating

universe u

variable {V : Type u}

private theorem image_subtype_subset {X : Type u} {M : Set X}
    (s : Set M) : Subtype.val '' s ⊆ M := by
  rintro x ⟨y, _hy, rfl⟩
  exact y.2

private theorem mk_image_subtype_eq {X : Type u} {M : Set X}
    (s : Set M) : #(Subtype.val '' s : Set X) = #s :=
  Cardinal.mk_image_eq_of_injOn Subtype.val s Set.injOn_subtype_val

/-- A small hammock seed has a bounded maximal-up-to extension which still
contains every seed member. -/
theorem exists_hammockMaximalUpTo_superset
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (u : V) (e : AltEnd V)
    (kappa : Cardinal.{u}) (hkappa : aleph0 ≤ kappa)
    {K : Set (AltPath Gamma.graph)} (hK : Hammock Gamma Y u e K)
    (hKcard : #K ≤ kappa) :
    ∃ H : Set (AltPath Gamma.graph), K ⊆ H ∧
      HammockMaximalUpTo Gamma Y u e kappa H := by
  obtain ⟨M, hKM, hMmax⟩ :=
    exists_maximal_hammock_superset Gamma Y u e hK
  by_cases hMcard : #M ≤ kappa
  · exact ⟨M, hKM,
      maximalUpTo_of_maximal hMmax.1 hMmax hMcard⟩
  · have hkappaM : kappa ≤ #M := (lt_of_not_ge hMcard).le
    have hsuccM : succ kappa ≤ #M := succ_le_of_lt (lt_of_not_ge hMcard)
    obtain ⟨s, hs⟩ := Cardinal.le_mk_iff_exists_set.mp hkappaM
    obtain ⟨t, ht⟩ := Cardinal.le_mk_iff_exists_set.mp hsuccM
    let T : Set (AltPath Gamma.graph) := Subtype.val '' s
    let U : Set (AltPath Gamma.graph) := Subtype.val '' t
    let H : Set (AltPath Gamma.graph) := K ∪ T
    have hTM : T ⊆ M := image_subtype_subset s
    have hUM : U ⊆ M := image_subtype_subset t
    have hTcard : #T = kappa := (mk_image_subtype_eq s).trans hs
    have hUcard : #U = succ kappa := (mk_image_subtype_eq t).trans ht
    have hHM : H ⊆ M := Set.union_subset hKM hTM
    have hHgood : Hammock Gamma Y u e H := hMmax.1.subset hHM
    have hHcardUpper : #H ≤ kappa := by
      exact (Cardinal.mk_union_le K T).trans
        (Cardinal.add_le_of_le hkappa hKcard hTcard.le)
    have hHcardLower : kappa ≤ #H := by
      rw [← hTcard]
      exact Cardinal.mk_subtype_mono Set.subset_union_right
    have hHcard : #H = kappa := le_antisymm hHcardUpper hHcardLower
    have hUgood : Hammock Gamma Y u e U := hMmax.1.subset hUM
    exact ⟨H, Set.subset_union_left,
      maximalUpTo_of_large hHgood hHcard hUgood hUcard⟩

/-- The total selected extension.  It agrees with the preceding existence
theorem exactly for valid `kappa`-small hammock seeds and is empty otherwise.
-/
noncomputable def seededHammockExtension
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (kappa : Cardinal.{u})
    (u : V) (e : AltEnd V) (K : Set (AltPath Gamma.graph)) :
    Set (AltPath Gamma.graph) := by
  classical
  exact
    if h : aleph0 ≤ kappa ∧ Hammock Gamma Y u e K ∧ #K ≤ kappa then
      Classical.choose
        (exists_hammockMaximalUpTo_superset Gamma Y u e kappa
          h.1 h.2.1 h.2.2)
    else ∅

theorem seededHammockExtension_spec
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (kappa : Cardinal.{u})
    (u : V) (e : AltEnd V) (K : Set (AltPath Gamma.graph))
    (hkappa : aleph0 ≤ kappa) (hK : Hammock Gamma Y u e K)
    (hKcard : #K ≤ kappa) :
    K ⊆ seededHammockExtension Gamma Y kappa u e K ∧
      HammockMaximalUpTo Gamma Y u e kappa
        (seededHammockExtension Gamma Y kappa u e K) := by
  rw [seededHammockExtension, dif_pos ⟨hkappa, hK, hKcard⟩]
  exact Classical.choose_spec
    (exists_hammockMaximalUpTo_superset Gamma Y u e kappa
      hkappa hK hKcard)

/-- Under the sole cardinal assumption, the total selected extension is
always `kappa`-small, including on invalid seeds. -/
theorem seededHammockExtension_card_le
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (kappa : Cardinal.{u})
    (u : V) (e : AltEnd V) (K : Set (AltPath Gamma.graph))
    (hkappa : aleph0 ≤ kappa) :
    #(seededHammockExtension Gamma Y kappa u e K) ≤ kappa := by
  by_cases hvalid : Hammock Gamma Y u e K ∧ #K ≤ kappa
  · exact (seededHammockExtension_spec Gamma Y kappa u e K
      hkappa hvalid.1 hvalid.2).2.card_le
  · rw [seededHammockExtension, dif_neg]
    · simp
    · intro h
      exact hvalid h.2

#print axioms exists_hammockMaximalUpTo_superset
#print axioms seededHammockExtension_spec
#print axioms seededHammockExtension_card_le

end Blueprint
end Erdos599
