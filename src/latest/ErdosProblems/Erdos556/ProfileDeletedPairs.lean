import ErdosProblems.Erdos556.DecompositionEdgeCounts
import ErdosProblems.Erdos556.ProfileMassCounts
import ErdosProblems.Erdos556.CompletePairCounts
import ErdosProblems.Erdos556.CubeRetainedGeometry

/-! Incompatible profile pairs consist entirely of deleted edges. -/

namespace Erdos556

open SimpleGraph Finset

theorem ThreeColourDecomposition.missing_of_singleton_profile_intersection {V : Type*}
    [DecidableEq V] {c : ThreeColouring V} {E D : ℝ} (h : ThreeColourDecomposition c E D)
    (u v : V) (huv : u ≠ v)
    (hinter : (profileVertices (h.profile u) ∩ profileVertices (h.profile v)).card = 1) :
    h.missing.Adj u v := by
  rw [missing, compl_adj]
  refine ⟨huv, ?_⟩
  intro hret
  obtain ⟨i, hi⟩ := iSup_adj.mp hret
  rcases hi with hB | hF
  · have hdis := profileOppositeAt_disjoint _ _ i (h.bipartite_profiles_opposite i u v hB)
    have he : profileVertices (h.profile u) ∩ profileVertices (h.profile v) = ∅ :=
      Finset.disjoint_iff_inter_eq_empty.mp hdis
    rw [he, card_empty] at hinter
    omega
  · exact singleton_profile_intersection_no_common_free _ _ i hinter
      (h.sparse_profiles_free i u v hF)

theorem ThreeColourDecomposition.incompatible_profile_product_bound {V : Type*}
    [Fintype V] [DecidableEq V] {c : ThreeColouring V} {E D : ℝ}
    (h : ThreeColourDecomposition c E D) (p q : CubeProfile)
    (hpq : (profileVertices p ∩ profileVertices q).card = 1) :
    ((h.profileClass p).card : ℝ) * (h.profileClass q).card ≤ 6 * E + Fintype.card V := by
  classical
  have hpair : ∀ u ∈ h.profileClass p, ∀ v ∈ h.profileClass q, u ≠ v → h.missing.Adj u v := by
    intro u hu v hv huv
    apply h.missing_of_singleton_profile_intersection u v huv
    rw [(h.mem_profileClass_iff p u).mp hu, (h.mem_profileClass_iff q v).mp hv]
    exact hpq
  have hc := complete_pair_card_product_bound h.missing (h.profileClass p) (h.profileClass q) hpair
  have hcR : ((h.profileClass p).card : ℝ) * (h.profileClass q).card ≤
      2 * (Nat.card h.missing.edgeSet : ℝ) + Fintype.card V := by exact_mod_cast hc
  have hm := h.missing_edge_count_le
  linarith

theorem ThreeColourDecomposition.vertex_profile_square_bound {V : Type*}
    [Fintype V] [DecidableEq V] {c : ThreeColouring V} {E D : ℝ}
    (h : ThreeColourDecomposition c E D) (p : CubeProfile) (hp : profileDimension p = 0) :
    ((h.profileClass p).card : ℝ) ^ 2 ≤ 6 * E + Fintype.card V := by
  have hpq : (profileVertices p ∩ profileVertices p).card = 1 := by
    rw [inter_self, profileVertices_card, hp]
    rfl
  simpa only [pow_two] using h.incompatible_profile_product_bound p p hpq

theorem ThreeColourDecomposition.wrong_colour_in_edge_profile_missing {V : Type*}
    [Fintype V] [DecidableEq V] {c : ThreeColouring V} {E D : ℝ}
    (h : ThreeColourDecomposition c E D) (p : CubeProfile) (i : Fin 3)
    (hfree : ∀ j, p j = none → j = i)
    (u v : V) (hu : u ∈ h.profileClass p) (hv : v ∈ h.profileClass p)
    (hwrong : (c.graph i)ᶜ.Adj u v) : h.missing.Adj u v := by
  rw [missing, compl_adj]
  refine ⟨hwrong.1, ?_⟩
  intro hret
  obtain ⟨j, hj⟩ := iSup_adj.mp hret
  have hup := (h.mem_profileClass_iff p u).mp hu
  have hvp := (h.mem_profileClass_iff p v).mp hv
  rcases hj with hB | hF
  · have hopp := h.bipartite_profiles_opposite j u v hB
    rw [hup, hvp] at hopp
    rcases hopp with ⟨h0, h1⟩ | ⟨h1, h0⟩ <;>
      have he : (some false : Option Bool) = some true := h0.symm.trans h1 <;> cases he
  · have hpf := (h.sparse_profiles_free j u v hF).1
    rw [hup] at hpf
    have hji := hfree j hpf
    subst j
    exact hwrong.2 (h.sparse_le i hF)

#print axioms ThreeColourDecomposition.incompatible_profile_product_bound

end Erdos556
