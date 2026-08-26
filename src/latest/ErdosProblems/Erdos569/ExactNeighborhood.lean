/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos569.Regions
import ErdosProblems.Erdos569.Completion
import ErdosProblems.Erdos569.Coloring
import ErdosProblems.Erdos569.Partition

/-! # Counting the vertices outside the blue clique -/

open scoped SimpleGraph

namespace Erdos569

open Erdos79 Erdos570

/-- The common graph-theoretic part of the final counting argument. -/
theorem blue_of_clique_region_exact
    {H : GraphCode} {k N t : ℕ} {budget : ℕ → ℕ} (hk : 5 ≤ k)
    (hn : 3 ≤ H.vertexCount) (hm : 0 < H.edgeCount)
    (C : SimpleGraph (Fin N)) [DecidableRel C.Adj]
    (hN : N = budget H.edgeCount)
    (c : H.graph.Coloring (Fin t))
    (hcycle : ¬ (cycleCode k).graph ⊑ C)
    (hIH : ∀ Q : GraphCode, NoIsolated Q → Q.edgeCount < H.edgeCount →
      RamseyAt (cycleCode k) Q (budget Q.edgeCount))
    (v : Fin N) (U₁ : Finset (Fin N))
    (ha : U₁.card = H.vertexCount / 2 + 1)
    (hU₁ : U₁ ⊆ C.neighborFinset v)
    (hclique : Cᶜ.IsClique (U₁ : Set (Fin N)))
    (hroom : ∀ b g e : ℕ,
      g + 1 ≤ H.vertexCount + (k - 1) * (t - 1) →
      1 + U₁.card + b + g = budget H.edgeCount →
      4 * e < H.edgeCount →
      e * (H.vertexCount * (H.vertexCount - 1)) ≤
        H.edgeCount * ((H.vertexCount - (H.vertexCount / 2 + 1)) *
          (H.vertexCount - (H.vertexCount / 2 + 1) - 1)) →
      budget e ≤ b ∧ H.vertexCount - U₁.card ≤ b) :
    H.graph ⊑ Cᶜ := by
  classical
  by_contra hblue
  let P := (externalNeighbors C v (U₁ : Set (Fin N))).toFinset
  have hPS : (P : Set (Fin N)) = externalNeighbors C v (U₁ : Set (Fin N)) := by
    simp [P]
  have hPmem (x : Fin N) : x ∈ P ↔ x ∈ externalNeighbors C v (U₁ : Set (Fin N)) := by
    change x ∈ (P : Set (Fin N)) ↔ _
    rw [hPS]
  have hS : (U₁ : Set (Fin N)) ⊆ C.neighborSet v := by
    intro x hx
    exact (C.mem_neighborFinset v x).mp (hU₁ hx)
  have hpath : ¬ SimpleGraph.pathGraph (k + 1) ⊑ C.induce (P : Set (Fin N)) := by
    rw [hPS]
    exact externalNeighbors_path_free hk v _ hS hcycle
  have hg : P.card + 1 ≤ H.vertexCount + (k - 1) * (t - 1) := by
    by_contra h
    have hsize : H.vertexCount + ((k + 1) - 2) * (t - 1) ≤ P.card := by
      have he : k + 1 - 2 = k - 1 := by omega
      rw [he]
      omega
    rcases Erdos570.RamseyAt.on_finset
        (ramseyAt_path_coloring H (by omega : 2 ≤ k + 1) c) C P hsize with hr | hb
    · exact hpath hr
    · exact hblue (hb.trans (SimpleGraph.Embedding.induce _).isContained)
  have hvU : v ∉ U₁ := by
    intro h
    exact ((C.mem_neighborFinset v v).mp (hU₁ h)).ne rfl
  have hvP : v ∉ P := by
    intro h
    exact ((hPmem v).mp h).1 rfl
  have hUP : Disjoint U₁ P := by
    rw [Finset.disjoint_left]
    intro x hxU hxP
    have hx := (hPmem x).mp hxP
    exact hx.2.1 hxU
  let removed := insert v (U₁ ∪ P)
  let U₂ := removedᶜ
  have hremoved : removed.card = 1 + U₁.card + P.card := by
    simp [removed, Finset.card_insert_of_notMem (show v ∉ U₁ ∪ P by simp [hvU, hvP]),
      Finset.card_union_of_disjoint hUP, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  have hcounts : 1 + U₁.card + U₂.card + P.card = budget H.edgeCount := by
    have ht := Finset.card_add_card_compl removed
    simp only [Fintype.card_fin] at ht
    change removed.card + U₂.card = N at ht
    rw [hremoved] at ht
    omega
  have hdisj : Disjoint U₁ U₂ := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    have hx := Finset.mem_compl.mp hx₂
    exact hx (by simp [removed, hx₁])
  have hcross : ∀ x ∈ U₁, ∀ y ∈ U₂, Cᶜ.Adj x y := by
    intro x hx y hy
    have hynot : y ∉ removed := Finset.mem_compl.mp hy
    have hyv : y ≠ v := by intro h; exact hynot (by simp [removed, h])
    have hyU : y ∉ U₁ := by intro h; exact hynot (by simp [removed, h])
    refine ⟨fun h ↦ hyU (h ▸ hx), ?_⟩
    intro hxy
    have hyP : y ∈ P := by
      apply (hPmem y).mpr
      exact ⟨hyv, hyU, x, hx, hxy⟩
    exact hynot (by simp [removed, hyP])
  obtain ⟨S, hSsize, hSedge, havg⟩ := exists_sparse_half_exact H hn hm
  obtain ⟨hbudget, hcard₂⟩ :=
    hroom U₂.card P.card (inducedCode H S).edgeCount hg hcounts hSedge havg
  apply hblue
  apply partition_forces_blue C hcycle hIH S (by omega) U₁ U₂ hdisj hclique hcross
  · rw [hSsize, ha]
    omega
  · rw [hSsize, ← ha]
    exact hcard₂
  · exact hbudget

end Erdos569
