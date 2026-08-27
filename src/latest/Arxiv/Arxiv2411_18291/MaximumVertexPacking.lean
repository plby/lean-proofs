import Arxiv.Arxiv2411_18291.FinalNegativeFamily
import Mathlib.Data.Finset.Max

/-! # Maximum families of vertex-disjoint blocks -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [DecidableEq V] {q : ℕ}

def vertexSupport (D : Finset (Block V q)) : Finset V := D.biUnion Subtype.val

def IsVertexPacking (D : Finset (Block V q)) : Prop :=
  (D : Set (Block V q)).PairwiseDisjoint Subtype.val

structure IsMaximumVertexPacking (H D : Finset (Block V q)) : Prop where
  subset : D ⊆ H
  packing : IsVertexPacking D
  maximum : ∀ E : Finset (Block V q), E ⊆ H → IsVertexPacking E → E.card ≤ D.card

omit [DecidableEq V] in
theorem exists_maximum_vertex_packing (H : Finset (Block V q)) :
    ∃ D, IsMaximumVertexPacking H D := by
  classical
  let F := H.powerset.filter IsVertexPacking
  have hF : F.Nonempty := ⟨∅, mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _),
    by simp [IsVertexPacking]⟩⟩
  obtain ⟨D, hD, hmax⟩ := F.exists_max_image Finset.card hF
  obtain ⟨hsub, hpack⟩ := mem_filter.mp hD
  exact ⟨D, ⟨mem_powerset.mp hsub, hpack,
    fun E hE hpackE => hmax E (mem_filter.mpr ⟨mem_powerset.mpr hE, hpackE⟩)⟩⟩

theorem subset_vertexSupport {D : Finset (Block V q)} {Q : Block V q} (hQ : Q ∈ D) :
    Q.val ⊆ vertexSupport D := by
  intro v hv
  exact mem_biUnion.mpr ⟨Q, hQ, hv⟩

theorem IsVertexPacking.card_vertexSupport {D : Finset (Block V q)}
    (hD : IsVertexPacking D) : (vertexSupport D).card = D.card * q := by
  rw [vertexSupport, card_biUnion hD]
  calc
    ∑ Q ∈ D, Q.val.card = ∑ _Q ∈ D, q := sum_congr rfl fun Q _ => Q.property
    _ = _ := by simp

omit [DecidableEq V] in
theorem IsVertexPacking.mono {D E : Finset (Block V q)}
    (hD : IsVertexPacking D) (hED : E ⊆ D) : IsVertexPacking E := by
  intro P hP Q hQ hPQ
  exact hD (hED hP) (hED hQ) hPQ

theorem IsVertexPacking.insert {D : Finset (Block V q)} (hD : IsVertexPacking D)
    {Q : Block V q} (hQ : Disjoint Q.val (vertexSupport D)) : IsVertexPacking (insert Q D) := by
  rw [IsVertexPacking, coe_insert, Set.pairwiseDisjoint_insert]
  exact ⟨hD, fun P hP _ => hQ.mono_right (subset_vertexSupport hP)⟩

theorem notMem_of_disjoint_vertexSupport {D : Finset (Block V q)} {Q : Block V q}
    (hq : 0 < q) (hQ : Disjoint Q.val (vertexSupport D)) : Q ∉ D := by
  intro hmem
  have hz := disjoint_self.mp (hQ.mono_right (subset_vertexSupport hmem))
  change Q.val = ∅ at hz
  have hcard : q = 0 := by rw [← Q.property, hz]; rfl
  omega

theorem IsMaximumVertexPacking.not_disjoint {H D : Finset (Block V q)}
    (hD : IsMaximumVertexPacking H D) (hq : 0 < q) {Q : Block V q} (hQ : Q ∈ H) :
    ¬Disjoint Q.val (vertexSupport D) := by
  intro hdis
  have hmax := hD.maximum (insert Q D) (insert_subset hQ hD.subset) (hD.packing.insert hdis)
  rw [card_insert_of_notMem (notMem_of_disjoint_vertexSupport hq hdis)] at hmax
  omega

theorem IsVertexPacking.isDecomposition_rankOne [Fintype V] {D : Finset (Block V q)}
    (hD : IsVertexPacking D) : IsDecomposition (cliqueSupport 1 D) D := by
  apply isDecomposition_cliqueSupport_of_pairwise
  intro Q hQ P hP hQP
  apply disjoint_left.mpr
  intro e heQ heP
  obtain ⟨v, hv⟩ := card_eq_one.mp e.property
  have hve : v ∈ e.val := by rw [hv]; exact mem_singleton_self _
  exact disjoint_left.mp (hD hQ hP hQP)
    ((mem_cliqueEdges _ _).mp heQ hve) ((mem_cliqueEdges _ _).mp heP hve)

end Arxiv2411_18291
