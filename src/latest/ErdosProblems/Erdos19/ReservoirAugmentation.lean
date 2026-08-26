import ErdosProblems.Erdos19.AdmissibleNeighbors
import ErdosProblems.Erdos19.LengthFiveAugmentation

/-! # Finding an alternating augmentation in a reservoir

The chosen six vertices avoid a prescribed forbidden set. New matching edges
belong to the reservoir and are supported on these six vertices.
-/

namespace Erdos19

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

theorem exists_reservoir_augmentation {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} (M : G.Subgraph) (hM : M.IsMatching)
    (R : _root_.SimpleGraph V) (hRG : R ≤ G) (hdis : Disjoint M.edgeSet R.edgeSet)
    (Z : Finset V) (u v : V) (hu : u ∉ M.verts) (hv : v ∉ M.verts)
    (huv : u ≠ v) (huZ : u ∉ Z) (hvZ : v ∉ Z) (q : ℕ)
    (hdu : 2 * q + 2 * Z.card + M.vertsᶜ.ncard ≤ R.degree u)
    (hdv : 2 * q + 2 * Z.card + M.vertsᶜ.ncard ≤ R.degree v)
    (hcut : ∀ A B : Finset V, Disjoint A B → A.card = q → B.card = q →
      ∃ x ∈ A, ∃ y ∈ B, R.Adj x y) :
    ∃ N : G.Subgraph, ∃ T : Finset V, N.IsMatching ∧
      N.verts = insert u (insert v M.verts) ∧ N.edgeSet.ncard = M.edgeSet.ncard + 1 ∧
      (T : Set V) ⊆ N.verts ∧ T.card = 6 ∧ Disjoint T Z ∧
      ∀ e ∈ N.edgeSet \ M.edgeSet, e ∈ R.edgeSet ∧ ∀ x ∈ e, x ∈ T := by
  classical
  obtain ⟨X, hXcard, hX⟩ := exists_matching_partner_neighbor_set M hM R u Z
  obtain ⟨Y, hYcard, hY⟩ := exists_matching_partner_neighbor_set M hM R v Z
  have hXlarge : 2 * q ≤ X.card := by omega
  have hYlarge : 2 * q ≤ Y.card := by omega
  obtain ⟨A, hAX, hAcard⟩ := exists_subset_card_eq (show q ≤ X.card by omega)
  have hYdiff : q ≤ (Y \ A).card := by
    have h := card_le_card_sdiff_add_card (s := Y) (t := A)
    omega
  obtain ⟨B, hBY, hBcard⟩ := exists_subset_card_eq hYdiff
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxB
    exact (mem_sdiff.mp (hBY hxB)).2 hxA
  obtain ⟨x, hxA, y, hyB, hxyR⟩ := hcut A B hAB hAcard hBcard
  obtain ⟨hxp, hux, hxZ, hpxZ⟩ := hX x (hAX hxA)
  obtain ⟨hyp, hvy, hyZ, hpyZ⟩ := hY y (mem_sdiff.mp (hBY hyB)).1
  let p := matchingPartner M hM
  have hxy : x ≠ y := fun h ↦ Finset.disjoint_left.mp hAB hxA (h ▸ hyB)
  have hnot : ¬M.Adj x y := by
    intro h
    exact Set.disjoint_left.mp hdis (Subgraph.mem_edgeSet.mpr h)
      (by simpa only [mem_edgeSet] using hxyR)
  have hpxx : p x ≠ x := hxp.ne.symm
  have hpyy : p y ≠ y := hyp.ne.symm
  have hpxpy : p x ≠ p y := p.injective.ne hxy
  have hpxy : p x ≠ y := fun h ↦ hnot (h ▸ hxp)
  have hxpy : x ≠ p y := by
    intro h
    apply hnot
    rw [h]
    exact hyp.symm
  have huxne : u ≠ x := fun h ↦ hu (h.symm ▸ hxp.fst_mem)
  have huypne : u ≠ p y := fun h ↦ hu (h.symm ▸ hyp.snd_mem)
  have huyne : u ≠ y := fun h ↦ hu (h.symm ▸ hyp.fst_mem)
  have hupne : u ≠ p x := fun h ↦ hu (h.symm ▸ hxp.snd_mem)
  have hvxne : v ≠ x := fun h ↦ hv (h.symm ▸ hxp.fst_mem)
  have hvypne : v ≠ p y := fun h ↦ hv (h.symm ▸ hyp.snd_mem)
  have hvyne : v ≠ y := fun h ↦ hv (h.symm ▸ hyp.fst_mem)
  have hvpne : v ≠ p x := fun h ↦ hv (h.symm ▸ hxp.snd_mem)
  let path : Fin 6 → V := ![u, p x, x, y, p y, v]
  have hpath : Function.Injective path := by
    have hlist : ([u, p x, x, y, p y, v] : List V).Nodup := by
      simp [hupne, huxne, huyne, huypne, huv, hpxx, hpxy, hpxpy,
        hvpne.symm, hxy, hxpy, hvxne.symm, hpyy.symm, hvyne.symm, hvypne.symm]
    have heq : path = ([u, p x, x, y, p y, v] : List V).get := by
      funext i
      fin_cases i <;> rfl
    rw [heq]
    exact hlist.injective_get
  obtain ⟨N, hN, hNv, hNc, hNe⟩ := exists_matching_augment_five M hM path hpath
    hu hv hxp.symm hyp (hRG hux) (hRG hxyR) (hRG hvy.symm)
  let T := univ.image path
  have hTcard : T.card = 6 := by
    rw [card_image_of_injective _ hpath]
    simp
  have hTdis : Disjoint T Z := by
    apply Finset.disjoint_left.mpr
    intro z hz hzZ
    obtain ⟨i, _, rfl⟩ := mem_image.mp hz
    fin_cases i <;> simp only [path, Matrix.cons_val_zero, Matrix.cons_val_succ] at hzZ
    · exact huZ hzZ
    · exact hpxZ hzZ
    · exact hxZ hzZ
    · exact hyZ hzZ
    · exact hpyZ hzZ
    · exact hvZ hzZ
  have hTN : (T : Set V) ⊆ N.verts := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := mem_image.mp hz
    rw [hNv]
    change path i ∈ insert u (insert v M.verts)
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inr hxp.snd_mem)
    · exact Or.inr (Or.inr hxp.fst_mem)
    · exact Or.inr (Or.inr hyp.fst_mem)
    · exact Or.inr (Or.inr hyp.snd_mem)
    · exact Or.inr (Or.inl rfl)
  refine ⟨N, T, hN, hNv, hNc, hTN, hTcard, hTdis, ?_⟩
  intro e he
  have heNew := (hNe he.1).resolve_left he.2
  have hpair : ∀ i j : Fin 6, R.Adj (path i) (path j) →
      s(path i, path j) ∈ R.edgeSet ∧ ∀ z ∈ s(path i, path j), z ∈ T := by
    intro i j hij
    refine ⟨by simpa only [mem_edgeSet] using hij, ?_⟩
    intro z hz
    rcases Sym2.mem_iff.mp hz with rfl | rfl
    · exact mem_image.mpr ⟨i, mem_univ _, rfl⟩
    · exact mem_image.mpr ⟨j, mem_univ _, rfl⟩
  rcases heNew with rfl | rfl | rfl
  · exact hpair 0 1 hux
  · exact hpair 2 3 hxyR
  · exact hpair 4 5 hvy.symm

#print axioms exists_reservoir_augmentation

end Erdos19
