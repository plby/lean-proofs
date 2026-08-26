import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic

/-!
# Disjoint vertex pairs and the weighted independent-set bound
-/

namespace Erdos547

open Finset SimpleGraph

variable {U : Type*}

/-- A graph consisting of disjoint pairs, all of whose endpoints lie in `S`. -/
structure IsPairingOn (P : SimpleGraph U) (S : Finset U) : Prop where
  support : ∀ ⦃u v⦄, P.Adj u v → u ∈ S ∧ v ∈ S
  unique : ∀ ⦃u v w⦄, P.Adj u v → P.Adj u w → v = w

def addDisjointPair (P : SimpleGraph U) (u v : U) (huv : u ≠ v) : SimpleGraph U where
  Adj x y := P.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)
  symm.symm x y h := by
    rcases h with h | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨hy, hx⟩)
    · exact Or.inr (Or.inl ⟨hy, hx⟩)
  loopless.irrefl x h := by
    rcases h with h | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact P.loopless.irrefl x h
    · exact huv (hx.symm.trans hy)
    · exact huv (hy.symm.trans hx)

open scoped Classical in
theorem IsPairingOn.add_pair {P : SimpleGraph U} {S : Finset U}
    (hP : IsPairingOn P S) (u v : U) (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v) :
    IsPairingOn (addDisjointPair P u v huv) (insert u (insert v S)) := by
  classical
  constructor
  · intro x y h
    rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hP.support h).1),
        Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hP.support h).2)⟩
    · simp
    · simp
  · intro x y z hxy hxz
    rcases hxy with hxy | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hxz with hxz | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hP.unique hxy hxz
      · exact (hu (hP.support hxy).1).elim
      · exact (hv (hP.support hxy).1).elim
    · rcases hxz with hxz | ⟨_, rfl⟩ | ⟨h, _⟩
      · exact (hu (hP.support hxz).1).elim
      · rfl
      · exact (huv h).elim
    · rcases hxz with hxz | ⟨h, _⟩ | ⟨_, rfl⟩
      · exact (hv (hP.support hxz).1).elim
      · exact (huv h.symm).elim
      · rfl

open scoped Classical in
theorem sum_le_erase_pair_add (J : Finset U) (w : U → ℕ) (u v : U)
    (hweight : w v ≤ w u) (hnotboth : ¬ (u ∈ J ∧ v ∈ J)) :
    (∑ x ∈ J, w x) ≤ (∑ x ∈ (J.erase u).erase v, w x) + w u := by
  classical
  by_cases hu : u ∈ J
  · have hv : v ∉ J := fun h ↦ hnotboth ⟨hu, h⟩
    have hv' : v ∉ J.erase u := fun h ↦ hv (Finset.mem_of_mem_erase h)
    rw [Finset.erase_eq_of_notMem hv']
    exact (Finset.sum_erase_add J w hu).symm.le
  · rw [Finset.erase_eq_of_notMem hu]
    by_cases hv : v ∈ J
    · have hsum := Finset.sum_erase_add J w hv
      omega
    · rw [Finset.erase_eq_of_notMem hv]
      omega

open scoped Classical in
/-- Pair the vertices in descending order of weight. Any set containing at
most one endpoint of each pair has at most half the total weight plus half
the prescribed bound on one vertex's weight. -/
theorem exists_weighted_vertex_pairing (S : Finset U) (w : U → ℕ) (M : ℕ)
    (hbound : ∀ u ∈ S, w u ≤ M) :
    ∃ P : SimpleGraph U, IsPairingOn P S ∧
      ∀ J ⊆ S, (∀ u ∈ J, ∀ v ∈ J, ¬ P.Adj u v) →
        2 * (∑ u ∈ J, w u) ≤ (∑ u ∈ S, w u) + M := by
  classical
  induction S using Finset.strongInductionOn generalizing M with
  | _ S ih =>
    by_cases hS : S = ∅
    · subst S
      refine ⟨⊥, ⟨fun {_ _} h ↦ h.elim, fun {_ _ _} h ↦ h.elim⟩, ?_⟩
      intro J hJ _
      have hJempty := Finset.subset_empty.mp hJ
      simp [hJempty]
    obtain ⟨u, hu, humax⟩ := Finset.exists_max_image S w (Finset.nonempty_iff_ne_empty.mpr hS)
    by_cases hrest : S.erase u = ∅
    · refine ⟨⊥, ⟨fun {_ _} h ↦ h.elim, fun {_ _ _} h ↦ h.elim⟩, ?_⟩
      intro J hJ _
      have hsum := Finset.sum_erase_add S w hu
      rw [hrest] at hsum
      simp only [Finset.sum_empty, zero_add] at hsum
      have hle : (∑ x ∈ J, w x) ≤ ∑ x ∈ S, w x := Finset.sum_le_sum_of_subset hJ
      have hM := hbound u hu
      omega
    obtain ⟨v, hv, hvmax⟩ := Finset.exists_max_image (S.erase u) w
      (Finset.nonempty_iff_ne_empty.mpr hrest)
    let B := (S.erase u).erase v
    have hBS : B ⊆ S := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
    have hBlt : B ⊂ S := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨hBS, ?_⟩
      intro heq
      have huB : u ∈ B := heq.symm ▸ hu
      exact Finset.notMem_erase u S (Finset.mem_of_mem_erase huB)
    have hBbound : ∀ x ∈ B, w x ≤ w v := fun x hx ↦ hvmax x (Finset.mem_of_mem_erase hx)
    obtain ⟨P, hP, hPweight⟩ := ih B hBlt (w v) hBbound
    have huB : u ∉ B := fun h ↦ Finset.notMem_erase u S (Finset.mem_of_mem_erase h)
    have hvB : v ∉ B := Finset.notMem_erase _ _
    have huv : u ≠ v := (Finset.mem_erase.mp hv).1.symm
    have hfull : insert u (insert v B) = S := by
      dsimp [B]
      rw [Finset.insert_erase hv, Finset.insert_erase hu]
    let P' := addDisjointPair P u v huv
    have hP' : IsPairingOn P' S := by
      rw [← hfull]
      exact hP.add_pair u v huB hvB huv
    refine ⟨P', hP', ?_⟩
    intro J hJS hJind
    let J' := (J.erase u).erase v
    have hJ'B : J' ⊆ B := by
      intro x hx
      obtain ⟨hxv, hx⟩ := Finset.mem_erase.mp hx
      obtain ⟨hxu, hxJ⟩ := Finset.mem_erase.mp hx
      exact Finset.mem_erase.mpr ⟨hxv, Finset.mem_erase.mpr ⟨hxu, hJS hxJ⟩⟩
    have hJ'J : J' ⊆ J := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
    have hJ'ind : ∀ x ∈ J', ∀ y ∈ J', ¬ P.Adj x y := by
      intro x hx y hy hxy
      exact hJind x (hJ'J hx) y (hJ'J hy) (Or.inl hxy)
    have hnotboth : ¬ (u ∈ J ∧ v ∈ J) := by
      rintro ⟨huJ, hvJ⟩
      exact hJind u huJ v hvJ (Or.inr (Or.inl ⟨rfl, rfl⟩))
    have hwvu : w v ≤ w u := humax v (Finset.mem_of_mem_erase hv)
    have hJloss := sum_le_erase_pair_add J w u v hwvu hnotboth
    have hsmall := hPweight J' hJ'B hJ'ind
    have hsum₁ := Finset.sum_erase_add S w hu
    have hsum₂ := Finset.sum_erase_add (S.erase u) w hv
    change (∑ x ∈ B, w x) + w v = ∑ x ∈ S.erase u, w x at hsum₂
    change (∑ x ∈ J, w x) ≤ (∑ x ∈ J', w x) + w u at hJloss
    have hM := hbound u hu
    omega

end Erdos547

#print axioms Erdos547.exists_weighted_vertex_pairing
