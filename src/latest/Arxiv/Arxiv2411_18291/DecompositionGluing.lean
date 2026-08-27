import Arxiv.Arxiv2411_18291.Partite

/-!
# Gluing decompositions along a common clique

The algebraic gluing operation from Section 3, proved for actual clique
families. The geometric embeddings that make two hosts meet in precisely
the chosen clique are a separate step.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem boundary_indicator_singleton (Q : Block V q) :
    boundary r (indicator {Q}) = indicator (cliqueEdges r Q) := by
  funext e
  rw [boundary, sum_eq_single Q]
  · by_cases he : e.val ⊆ Q.val <;> simp [indicator, he]
  · intro P _ hPQ
    simp [indicator, hPQ]
  · intro hQ
    exact (hQ (mem_univ Q)).elim

theorem IsDecomposition.erase {G : Hypergraph V r} {D : Finset (Block V q)}
    (hD : IsDecomposition G D) {Q : Block V q} (hQ : Q ∈ D) :
    IsDecomposition (G \ cliqueEdges r Q) (D.erase Q) := by
  unfold IsDecomposition
  rw [← sdiff_singleton_eq_erase, indicator_sdiff (singleton_subset_iff.mpr hQ),
    boundary_sub, hD, boundary_indicator_singleton, indicator_sdiff (hD.clique_subset hQ)]

theorem IsDecomposition.families_disjoint (hqr : r ≤ q)
    {G H : Hypergraph V r} {D E : Finset (Block V q)}
    (hD : IsDecomposition G D) (hE : IsDecomposition H E) (hGH : Disjoint G H) :
    Disjoint D E := by
  apply Finset.disjoint_left.mpr
  intro Q hQD hQE
  obtain ⟨e, he⟩ := cliqueEdges_nonempty hqr Q
  exact Finset.disjoint_left.mp hGH (hD.clique_subset hQD he) (hE.clique_subset hQE he)

/-- The union of the actual families decomposes the union of disjoint hosts. -/
theorem IsDecomposition.union (hqr : r ≤ q) {G H : Hypergraph V r}
    {D E : Finset (Block V q)} (hD : IsDecomposition G D)
    (hE : IsDecomposition H E) (hGH : Disjoint G H) :
    IsDecomposition (G ∪ H) (D ∪ E) := by
  unfold IsDecomposition
  rw [indicator_union (hD.families_disjoint hqr hE hGH), boundary_add,
    hD, hE, indicator_union hGH]

/-- Remove the duplicate copy of the common clique from the second family. -/
theorem IsDecomposition.glue (hqr : r ≤ q) {G H : Hypergraph V r}
    {D E : Finset (Block V q)} (hD : IsDecomposition G D)
    (hE : IsDecomposition H E) (Q : Block V q) (hQ : Q ∈ E)
    (hGH : G ∩ H = cliqueEdges r Q) :
    IsDecomposition (G ∪ H) (D ∪ E.erase Q) := by
  have hdis : Disjoint G (H \ cliqueEdges r Q) := by
    apply Finset.disjoint_left.mpr
    intro e heG heH
    obtain ⟨heH, heQ⟩ := mem_sdiff.mp heH
    apply heQ
    rw [← hGH]
    exact mem_inter.mpr ⟨heG, heH⟩
  have hQG : cliqueEdges r Q ⊆ G := by rw [← hGH]; exact inter_subset_left
  have hunion : G ∪ (H \ cliqueEdges r Q) = G ∪ H := by
    ext e
    simp only [mem_union, mem_sdiff]
    constructor
    · rintro (heG | ⟨heH, _⟩)
      · exact Or.inl heG
      · exact Or.inr heH
    · rintro (heG | heH)
      · exact Or.inl heG
      · by_cases heG : e ∈ G
        · exact Or.inl heG
        · exact Or.inr ⟨heH, fun heQ => heG (hQG heQ)⟩
  simpa only [hunion] using hD.union hqr (hE.erase hQ) hdis

/-- The two orientations of the shared-clique gluing operation. -/
theorem glue_two_decompositions (hqr : r ≤ q) {G H : Hypergraph V r}
    {Dp Dn Ep En : Finset (Block V q)}
    (hDp : IsDecomposition G Dp) (hDn : IsDecomposition G Dn)
    (hEp : IsDecomposition H Ep) (hEn : IsDecomposition H En)
    (Q : Block V q) (hQn : Q ∈ Dn) (hQp : Q ∈ Ep)
    (hGH : G ∩ H = cliqueEdges r Q) :
    IsDecomposition (G ∪ H) (Dp ∪ Ep.erase Q) ∧
      IsDecomposition (G ∪ H) (En ∪ Dn.erase Q) := by
  refine ⟨hDp.glue hqr hEp Q hQp hGH, ?_⟩
  have hHG : H ∩ G = cliqueEdges r Q := by rw [inter_comm, hGH]
  simpa only [union_comm H G] using hEn.glue hqr hDn Q hQn hHG

/-- For positive uniformity, inclusion of all clique edges forces inclusion
of the underlying vertex sets. -/
theorem clique_vertices_subset (hr : 0 < r) (hqr : r ≤ q) (P Q : Block V q)
    (h : cliqueEdges r P ⊆ cliqueEdges r Q) : P.val ⊆ Q.val := by
  intro v hv
  obtain ⟨s, hvs, hsP, hsr⟩ := exists_subsuperset_card_eq
    (s := {v}) (t := P.val) (n := r) (singleton_subset_iff.mpr hv)
    (by simpa only [card_singleton] using Nat.succ_le_of_lt hr)
    (by simpa only [P.property] using hqr)
  have hsQ : s ⊆ Q.val :=
    (mem_cliqueEdges (⟨s, hsr⟩ : Block V r) Q).mp
      (h ((mem_cliqueEdges _ P).mpr hsP))
  exact hsQ (hvs (mem_singleton_self v))

/-- A clique belonging to decompositions of both hosts must be their shared
gluing clique. -/
theorem IsDecomposition.common_clique_eq (hr : 0 < r) (hqr : r ≤ q)
    {G H : Hypergraph V r} {D E : Finset (Block V q)}
    (hD : IsDecomposition G D) (hE : IsDecomposition H E)
    (Q : Block V q) (hGH : G ∩ H = cliqueEdges r Q)
    {P : Block V q} (hPD : P ∈ D) (hPE : P ∈ E) : P = Q := by
  have hsub : cliqueEdges r P ⊆ cliqueEdges r Q := by
    rw [← hGH]
    exact subset_inter (hD.clique_subset hPD) (hE.clique_subset hPE)
  apply Subtype.ext
  exact eq_of_subset_of_card_le (clique_vertices_subset hr hqr P Q hsub)
    (by rw [Q.property, P.property])

/-- If the original positive and negative families are disjoint, the two
families obtained by gluing remain disjoint. -/
theorem glue_families_disjoint (hr : 0 < r) (hqr : r ≤ q)
    {G H : Hypergraph V r} {Dp Dn Ep En : Finset (Block V q)}
    (hDp : IsDecomposition G Dp) (hDn : IsDecomposition G Dn)
    (hEp : IsDecomposition H Ep) (hEn : IsDecomposition H En)
    (hD : Disjoint Dp Dn) (hE : Disjoint Ep En)
    (Q : Block V q) (hQn : Q ∈ Dn)
    (hGH : G ∩ H = cliqueEdges r Q) :
    Disjoint (Dp ∪ Ep.erase Q) (En ∪ Dn.erase Q) := by
  apply Finset.disjoint_left.mpr
  intro P hPp hPn
  rcases mem_union.mp hPp with hPD | hPE
  · rcases mem_union.mp hPn with hPEn | hPDn
    · have hPQ := hDp.common_clique_eq hr hqr hEn Q hGH hPD hPEn
      subst P
      exact Finset.disjoint_left.mp hD hPD hQn
    · exact Finset.disjoint_left.mp hD hPD (mem_erase.mp hPDn).2
  · rcases mem_union.mp hPn with hPEn | hPDn
    · exact Finset.disjoint_left.mp hE (mem_erase.mp hPE).2 hPEn
    · have hPQ := hDn.common_clique_eq hr hqr hEp Q hGH
        (mem_erase.mp hPDn).2 (mem_erase.mp hPE).2
      exact (mem_erase.mp hPE).1 hPQ

end Arxiv2411_18291
