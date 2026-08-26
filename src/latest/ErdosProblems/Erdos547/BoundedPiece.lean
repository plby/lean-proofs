import ErdosProblems.Erdos547.RootedPieces
import ErdosProblems.Erdos547.FiniteSelection

/-!
# A pendant piece of controlled order

Selecting branches of a smallest sufficiently large rooted piece avoids any
choice of a global rooting or a traversal order on the tree.
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph

variable {U : Type*} (T : SimpleGraph U)

open scoped Classical in
theorem exists_rooted_branch_family [Finite U] (hT : T.IsTree) (S : Finset U) (r : U)
    (hS : IsRootedPiece T (S : Set U) r) :
    ∃ F : Finset (Finset U), F.biUnion id = S.erase r ∧
      ∀ B ∈ F, r ∉ B ∧ (∃ p, IsRootedPiece T (B : Set U) p) ∧
        (∃ p ∈ B, T.Adj p r) ∧
        (∀ u ∈ B, ∀ v, T.Adj u v → v = r ∨ v ∈ B) := by
  classical
  let := Fintype.ofFinite U
  let outside (x : (↑(S.erase r) : Set U)) : ({r}ᶜ : Set U) :=
    ⟨x.val, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      (Finset.mem_erase.mp x.property).1⟩
  let component (x : (↑(S.erase r) : Set U)) :=
    (T.induce ({r}ᶜ : Set U)).connectedComponentMk (outside x)
  let branch (x : (↑(S.erase r) : Set U)) : Finset U :=
    (inducedComponentSet T ({r}ᶜ : Set U) (component x)).toFinset
  have hmem (x : (↑(S.erase r) : Set U)) : x.val ∈ branch x := by
    apply Set.mem_toFinset.mpr
    exact ⟨outside x, ConnectedComponent.connectedComponentMk_mem, rfl⟩
  have hbranch (x : (↑(S.erase r) : Set U)) :
      (branch x : Set U) = inducedComponentSet T ({r}ᶜ : Set U) (component x) :=
    Set.coe_toFinset _
  have hsub (x : (↑(S.erase r) : Set U)) : branch x ⊆ S.erase r := by
    intro v hv
    have hvB : v ∈ inducedComponentSet T ({r}ᶜ : Set U) (component x) := by
      rw [← hbranch x]; exact hv
    have hmeet : (inducedComponentSet T ({r}ᶜ : Set U) (component x) ∩
        (S : Set U)).Nonempty := by
      refine ⟨x.val, ?_, (Finset.mem_erase.mp x.property).2⟩
      rw [← hbranch x]; exact hmem x
    have hvS := branch_subset_of_meets T hS (component x) hmeet hvB
    have hvr := inducedComponentSet_subset T ({r}ᶜ : Set U) (component x) hvB
    exact Finset.mem_erase.mpr ⟨hvr, hvS⟩
  let F := (Finset.univ : Finset (↑(S.erase r) : Set U)).image branch
  refine ⟨F, ?_, ?_⟩
  · ext v
    constructor
    · intro hv
      obtain ⟨B, hBF, hvB⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hBF
      exact hsub x hvB
    · intro hv
      exact Finset.mem_biUnion.mpr ⟨branch ⟨v, hv⟩,
        Finset.mem_image.mpr ⟨⟨v, hv⟩, Finset.mem_univ _, rfl⟩, hmem ⟨v, hv⟩⟩
  · intro B hBF
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hBF
    refine ⟨fun h ↦ (Finset.mem_erase.mp (hsub x h)).1 rfl, ?_, ?_, ?_⟩
    · rw [hbranch x]
      exact branch_isRootedPiece T hT r (component x)
    · obtain ⟨p, hp, hpr⟩ := branch_attaches_root T hT.connected.preconnected r (component x)
      exact ⟨p, Set.mem_toFinset.mpr hp, hpr⟩
    · intro u hu v huv
      by_cases hvr : v = r
      · exact Or.inl hvr
      · right
        exact Set.mem_toFinset.mpr (inducedComponentSet_closed T ({r}ᶜ : Set U)
          (component x) (Set.mem_toFinset.mp hu) hvr huv)

open scoped Classical in
/-- A finite tree has a pendant rooted piece of every order scale: at least
`q` and at most `2*q-1` vertices. -/
theorem exists_bounded_rooted_piece [Fintype U] (hT : T.IsTree) (q : ℕ)
    (hqpos : 1 ≤ q) (hq : q ≤ Fintype.card U) :
    ∃ S : Finset U, ∃ r, q ≤ S.card ∧ S.card ≤ 2 * q - 1 ∧
      IsRootedPiece T (S : Set U) r := by
  classical
  obtain ⟨S, r, hsize, hpiece, hmin⟩ := exists_minimal_rooted_piece T hT q hq
  obtain ⟨F, hunion, hbranches⟩ := exists_rooted_branch_family T hT S r hpiece
  have hsub (B : Finset U) (hBF : B ∈ F) : B ⊆ S.erase r := by
    intro v hv
    rw [← hunion]
    exact Finset.mem_biUnion.mpr ⟨B, hBF, hv⟩
  have hsmall : ∀ B ∈ F, B.card ≤ q - 1 := by
    intro B hBF
    have hcard := Finset.card_le_card (hsub B hBF)
    have herase := Finset.card_erase_add_one hpiece.root_mem
    obtain ⟨p, hp⟩ := (hbranches B hBF).2.1
    by_contra h
    have hqB : q ≤ B.card := by omega
    have hminimal := hmin B p hqB hp
    omega
  have henough : q - 1 ≤ (F.biUnion id).card := by
    rw [hunion]
    have herase := Finset.card_erase_add_one hpiece.root_mem
    omega
  obtain ⟨C, hCF, hlow, hhigh⟩ := exists_bounded_subfamily F (q - 1) (q - 1)
    hsmall henough
  have hr : r ∉ C.biUnion id := by
    intro h
    obtain ⟨B, hBC, hrB⟩ := Finset.mem_biUnion.mp h
    exact (hbranches B (hCF hBC)).1 hrB
  have hcard : (insert r (C.biUnion id)).card = (C.biUnion id).card + 1 :=
    Finset.card_insert_of_notMem hr
  refine ⟨insert r (C.biUnion id), r, by omega, by omega, ?_⟩
  apply union_branches_isRootedPiece T C r
  · intro B hBC
    obtain ⟨p, hp⟩ := (hbranches B (hCF hBC)).2.1
    exact hp.connected
  · intro B hBC
    exact (hbranches B (hCF hBC)).2.2.1
  · intro B hBC
    exact (hbranches B (hCF hBC)).2.2.2

end Erdos547

#print axioms Erdos547.exists_bounded_rooted_piece
