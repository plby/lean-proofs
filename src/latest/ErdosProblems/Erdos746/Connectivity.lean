import ErdosProblems.Erdos746.Posa

/-!
# Expansion implies connectivity

This file isolates the elementary connectivity consequence needed in the
sprinkling argument for Erdős problem 746.  A graph on `n` vertices which
expands every set of at most `⌊n / 4⌋` vertices by a factor of two is
connected once `n ≥ 8`.
-/

open Finset

namespace SimpleGraph

noncomputable section

/-- A two-expander up to `⌊n / 4⌋` on `Fin n` is connected for `n ≥ 8`.

The proof takes two distinct connected components and chooses the smaller
one, say `C`.  Disjointness gives `2 * |C| ≤ n`.  If `|C| ≤ ⌊n / 4⌋`, then
expansion applied to all of `C` contradicts its empty external boundary.  If
`|C| > ⌊n / 4⌋`, choose `S ⊆ C` with `|S| = ⌊n / 4⌋`.  Its external
neighbourhood is contained in `C \ S`, hence expansion gives
`3 * ⌊n / 4⌋ ≤ |C|`.  Thus `6 * ⌊n / 4⌋ ≤ n`, contrary to `n ≥ 8`.
-/
theorem IsTwoExpanderUpTo.connected_fin_quarter {n : ℕ} (hn : 8 ≤ n)
    (G : SimpleGraph (Fin n)) (hG : G.IsTwoExpanderUpTo (n / 4)) : G.Connected := by
  classical
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  refine ⟨?_⟩
  intro u v
  by_contra huv
  have huvComp : G.connectedComponentMk u ≠ G.connectedComponentMk v := by
    intro h
    exact huv (ConnectedComponent.exact h)
  have component_contra (C D : G.ConnectedComponent) (hCD : C ≠ D)
      (hcard : C.supp.toFinset.card ≤ D.supp.toFinset.card) : False := by
    let Cfin : Finset (Fin n) := C.supp.toFinset
    let Dfin : Finset (Fin n) := D.supp.toFinset
    have hCnonempty : Cfin.Nonempty := by
      obtain ⟨x, hx⟩ := C.nonempty_supp
      exact ⟨x, by simpa [Cfin] using hx⟩
    have hCpos : 0 < Cfin.card := hCnonempty.card_pos
    have hdisj : Disjoint Cfin Dfin := by
      apply Set.disjoint_toFinset.mpr
      exact pairwise_disjoint_supp_connectedComponent G hCD
    have hunion : (Cfin ∪ Dfin).card ≤ n := by
      have h := Finset.card_le_card (Finset.subset_univ (Cfin ∪ Dfin))
      simpa using h
    have hsum : Cfin.card + Dfin.card ≤ n := by
      rw [Finset.card_union_of_disjoint hdisj] at hunion
      exact hunion
    have hCsmall : 2 * Cfin.card ≤ n := by
      have hcard' : Cfin.card ≤ Dfin.card := by simpa [Cfin, Dfin] using hcard
      omega
    have outer_subset (S : Finset (Fin n)) (hSC : S ⊆ Cfin) :
        G.outerNeighborFinset S ⊆ Cfin \ S := by
      intro x hx
      rw [mem_outerNeighborFinset] at hx
      obtain ⟨hxS, y, hyS, hyx⟩ := hx
      have hyC : y ∈ C.supp := by
        have : y ∈ Cfin := hSC hyS
        simpa [Cfin] using this
      have hxC : x ∈ C.supp := C.mem_supp_of_adj_mem_supp hyC hyx
      exact Finset.mem_sdiff.mpr ⟨by simpa [Cfin] using hxC, hxS⟩
    by_cases hCle : Cfin.card ≤ n / 4
    · have hout : (G.outerNeighborFinset Cfin).card = 0 := by
        have hle := Finset.card_le_card (outer_subset Cfin (Subset.rfl))
        simpa using hle
      have hexpand := hG Cfin hCle
      rw [hout] at hexpand
      exact (Nat.not_lt_zero Cfin.card) (by omega : Cfin.card < 0)
    · have hkC : n / 4 ≤ Cfin.card := by omega
      obtain ⟨S, hSC, hScard⟩ := Finset.exists_subset_card_eq hkC
      have hexpand := hG S (by omega)
      have houter := Finset.card_le_card (outer_subset S hSC)
      have hdiff : (Cfin \ S).card + S.card = Cfin.card :=
        Finset.card_sdiff_add_card_eq_card hSC
      have hthree : 3 * (n / 4) ≤ Cfin.card := by omega
      have hfloor : n < 6 * (n / 4) := by omega
      omega
  rcases le_total (G.connectedComponentMk u).supp.toFinset.card
      (G.connectedComponentMk v).supp.toFinset.card with hle | hle
  · exact component_contra _ _ huvComp hle
  · exact component_contra _ _ huvComp.symm hle

end

end SimpleGraph
