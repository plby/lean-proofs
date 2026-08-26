/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos569.PathRamsey
import ErdosProblems.Erdos569.SecondNeighborhood
import ErdosProblems.Erdos570.RamseyRegion

/-!
# The first and second vertex regions in the cycle Ramsey argument

The root restriction retains every edge away from the chosen root. In
particular it retains the path edges in the external neighborhood; this
makes the application of Lemma 7 explicit.
-/

open scoped SimpleGraph

namespace Erdos569

open Erdos79 Erdos570

theorem ramseyAt_path_coloring (H : GraphCode) {k t : ℕ} (hk : 2 ≤ k)
    (c : H.graph.Coloring (Fin t)) :
    RamseyAt (pathCode k) H (H.vertexCount + (k - 2) * (t - 1)) := by
  intro C
  exact pathGraph_isContained_or_compl_of_coloring hk H.graph c C (by simp)

/-- Corollary 6, including the empty target. -/
theorem ramseyAt_path_order (H : GraphCode) {k : ℕ} (hk : 2 ≤ k) :
    RamseyAt (pathCode k) H ((k - 1) * (H.vertexCount - 1) + 1) := by
  classical
  intro C
  by_cases hn : H.vertexCount = 0
  · right
    let : IsEmpty (Fin H.vertexCount) := by rw [hn]; infer_instance
    exact SimpleGraph.IsContained.of_isEmpty
  let c : H.graph.Coloring (Fin H.vertexCount) :=
    SimpleGraph.Coloring.mk id (fun h ↦ h.ne)
  apply pathGraph_isContained_or_compl_of_coloring hk H.graph c C
  simp only [Fintype.card_fin]
  have hn1 : 1 ≤ H.vertexCount := by omega
  have hk1 : k - 1 = k - 2 + 1 := by omega
  rw [hk1, Nat.add_mul, one_mul]
  omega

/-- Delete just the root edges whose other endpoints are outside `S`. -/
def restrictRoot {V : Type*} (G : SimpleGraph V) (v : V) (S : Set V) :
    SimpleGraph V where
  Adj x y := G.Adj x y ∧ (x = v → y ∈ S) ∧ (y = v → x ∈ S)
  symm := ⟨by
    intro x y h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨by intro x h; exact h.1.ne rfl⟩

theorem restrictRoot_le {V : Type*} (G : SimpleGraph V) (v : V) (S : Set V) :
    restrictRoot G v S ≤ G := fun _ _ h ↦ h.1

/-- Vertices outside the root and `S` with a neighbor in `S`. -/
def externalNeighbors {V : Type*} (G : SimpleGraph V) (v : V) (S : Set V) : Set V :=
  {z | z ≠ v ∧ z ∉ S ∧ ∃ s ∈ S, G.Adj s z}

/-- The external-neighborhood path bound, with no assumption about edges
from the root directly to that region in the original graph. -/
theorem externalNeighbors_path_free
    {V : Type*} {G : SimpleGraph V} {k : ℕ} (hk : 5 ≤ k) (v : V) (S : Set V)
    (hS : S ⊆ G.neighborSet v) (hcycle : ¬ SimpleGraph.cycleGraph k ⊑ G) :
    ¬ SimpleGraph.pathGraph (k + 1) ⊑ G.induce (externalNeighbors G v S) := by
  intro hpath
  let R := restrictRoot G v S
  have hsub (z : externalNeighbors G v S) : z.1 ∈ secondNeighborSet R v := by
    obtain ⟨hzv, hzS, s, hsS, hsz⟩ := z.2
    have hvs : G.Adj v s := hS hsS
    refine ⟨hzv, ?_, s, ?_, ?_⟩
    · intro hvz
      exact hzS (hvz.2.1 rfl)
    · exact ⟨hvs, fun _ ↦ hsS, fun h ↦ (hvs.ne h.symm).elim⟩
    · exact ⟨hsz, fun h ↦ (hvs.ne h.symm).elim, fun h ↦ (hzv h).elim⟩
  let f : G.induce (externalNeighbors G v S) →g
      R.induce (secondNeighborSet R v) :=
    { toFun := fun z ↦ ⟨z.1, hsub z⟩
      map_rel' := by
        intro a b hab
        exact ⟨hab, fun h ↦ (a.2.1 h).elim, fun h ↦ (b.2.1 h).elim⟩ }
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun z : secondNeighborSet R v ↦ z.1) hab)
  have hpathR := hpath.trans (show G.induce (externalNeighbors G v S) ⊑
      R.induce (secondNeighborSet R v) from ⟨f.toCopy hf⟩)
  exact hcycle ((cycleGraph_isContained_of_pathGraph_secondNeighbor_ge_five hk v hpathR).trans
    (SimpleGraph.IsContained.of_le (restrictRoot_le G v S)))

/-- A sufficiently large red neighborhood contains the required blue clique. -/
theorem exists_blue_clique_in_neighborhood
    {V : Type*} [Fintype V] {k a : ℕ} (hk : 3 ≤ k)
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hcycle : ¬ SimpleGraph.cycleGraph k ⊑ G)
    (hdeg : (k - 2) * (a - 1) + 1 ≤ G.degree v) :
    ∃ S : Finset V, S.card = a ∧ S ⊆ G.neighborFinset v ∧ Gᶜ.IsClique (S : Set V) := by
  classical
  let T := G.neighborFinset v
  have hset : (T : Set V) = G.neighborSet v := by ext x; simp [T]
  have hpath : ¬ SimpleGraph.pathGraph (k - 1) ⊑ G.induce (T : Set V) := by
    rw [hset]
    apply pathGraph_not_isContained_neighbor_of_cycleGraph_not_isContained (by omega) v
    rw [show k - 1 + 1 = k by omega]
    exact hcycle
  have hroom : ((k - 1) - 1) * ((completeCode a).vertexCount - 1) + 1 ≤ T.card := by
    change ((k - 1) - 1) * (a - 1) + 1 ≤ T.card
    have hk' : k - 1 - 1 = k - 2 := by omega
    simpa only [hk', T, SimpleGraph.card_neighborFinset_eq_degree] using hdeg
  rcases Erdos570.RamseyAt.on_finset
      (ramseyAt_path_order (completeCode a) (by omega : 2 ≤ k - 1)) G T hroom
      with hred | hblue
  · exact (hpath hred).elim
  obtain ⟨copy⟩ := hblue
  let f : Fin a → V := fun i ↦ (copy i).1
  have hf : Function.Injective f := by
    intro i j hij
    exact copy.injective (Subtype.ext hij)
  let S := Finset.univ.image f
  refine ⟨S, ?_, ?_, ?_⟩
  · simp [S, Finset.card_image_of_injective _ hf]
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact (copy i).2
  · intro x hx y hy hxy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    apply copy.toHom.map_adj
    exact (SimpleGraph.top_adj _ _).mpr (fun hij ↦ hxy (congrArg f hij))

end Erdos569
