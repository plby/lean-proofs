import Arxiv.Arxiv2411_18291.CliqueExtensionCount

/-!
# Clique extensions of an arbitrary root

Edges entirely inside the fixed root are exempted. All other edges must
be present. This includes punctured cliques, genuine cliques through a
host edge, and cliques through a smaller face. The next-vertex criterion
is the same common-neighborhood condition in every case.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {r a k : ℕ}

def IsRootedClique (G : Hypergraph V (r + 1)) (I U : Finset V) : Prop :=
  I ⊆ U ∧ ∀ e : Block V (r + 1), e.val ⊆ U → e ∈ G ∨ e.val ⊆ I

omit [Fintype V] [DecidableEq V] in
theorem isRootedClique_self (G : Hypergraph V (r + 1)) (I : Finset V) :
    IsRootedClique G I I := ⟨Subset.rfl, fun _ h => Or.inr h⟩

omit [Fintype V] [DecidableEq V] in
theorem IsRootedClique.mono {G : Hypergraph V (r + 1)} {I U W : Finset V}
    (hU : IsRootedClique G I U) (hWU : W ⊆ U) (hIW : I ⊆ W) : IsRootedClique G I W :=
  ⟨hIW, fun e he => hU.2 e (he.trans hWU)⟩

open Classical in
def rootedCliques (G : Hypergraph V (r + 1)) (I : Block V a) (k : ℕ) : Finset (Block V k) :=
  univ.filter fun U => IsRootedClique G I.val U.val

omit [DecidableEq V] in
theorem mem_rootedCliques (G : Hypergraph V (r + 1)) (I : Block V a) (U : Block V k) :
    U ∈ rootedCliques G I k ↔ IsRootedClique G I.val U.val := by
  simp [rootedCliques]

omit [DecidableEq V] in
theorem rootedCliques_base (G : Hypergraph V (r + 1)) (I : Block V a) :
    rootedCliques G I a = {I} := by
  ext U
  simp only [mem_rootedCliques, mem_singleton]
  constructor
  · intro hU
    exact Subtype.ext (eq_of_subset_of_card_le hU.1 (by rw [I.property, U.property])).symm
  · rintro rfl
    exact isRootedClique_self G _

def cliqueFamily (G : Hypergraph V r) (q : ℕ) : Finset (Block V q) :=
  univ.filter fun Q => cliqueEdges r Q ⊆ G

theorem rootedCliques_eq_filter_cliqueFamily (G : Hypergraph V (r + 1)) (I : Block V a)
    (hI : cliqueEdges (r + 1) I ⊆ G) :
    rootedCliques G I k = (cliqueFamily G k).filter fun Q => I.val ⊆ Q.val := by
  ext Q
  simp only [mem_rootedCliques, cliqueFamily, mem_filter, mem_univ, true_and]
  constructor
  · intro hQ
    refine ⟨?_, hQ.1⟩
    intro e he
    rcases hQ.2 e ((mem_cliqueEdges _ _).mp he) with hG | heI
    · exact hG
    · exact hI ((mem_cliqueEdges _ _).mpr heI)
  · rintro ⟨hQ, hIQ⟩
    exact ⟨hIQ, fun e he => Or.inl (hQ ((mem_cliqueEdges _ _).mpr he))⟩

theorem IsRootedClique.insert_iff {G : Hypergraph V (r + 1)} {I : Finset V}
    {U : Block V k} (hU : IsRootedClique G I U.val) {v : V} (hv : v ∉ U.val) :
    IsRootedClique G I (insert v U.val) ↔ v ∈ cliqueNextVertices G U := by
  rw [mem_cliqueNextVertices]
  constructor
  · intro hnew
    refine ⟨?_, hv⟩
    apply (mem_commonNeighbors _ _ _).mpr
    intro S hS
    have hSU := (mem_cliqueEdges S U).mp hS
    have hvS : v ∉ S.val := fun h => hv (hSU h)
    apply (mem_neighbors _ _ _).mpr
    refine ⟨hvS, ?_⟩
    rcases hnew.2 (extendBlock S v hvS) (insert_subset_insert v hSU) with hG | hI
    · exact hG
    · exact (hv (hU.1 (hI (mem_insert_self _ _)))).elim
  · rintro ⟨hcommon, _⟩
    refine ⟨hU.1.trans (subset_insert _ _), fun e he => ?_⟩
    by_cases hve : v ∈ e.val
    · let S : Block V r := ⟨e.val.erase v, by
        rw [card_erase_of_mem hve, e.property]
        omega⟩
      have hSU : S.val ⊆ U.val := by
        intro x hx
        obtain ⟨hxv, hxe⟩ := mem_erase.mp hx
        exact (mem_insert.mp (he hxe)).resolve_left hxv
      obtain ⟨hvS, hG⟩ := (mem_neighbors _ _ _).mp
        ((mem_commonNeighbors _ _ _).mp hcommon S ((mem_cliqueEdges S U).mpr hSU))
      have hSe : extendBlock S v hvS = e := Subtype.ext (insert_erase hve)
      exact Or.inl (hSe ▸ hG)
    · apply hU.2 e
      intro x hx
      rcases mem_insert.mp (he hx) with h | h
      · exact (hve (h ▸ hx)).elim
      · exact h

end Arxiv2411_18291
