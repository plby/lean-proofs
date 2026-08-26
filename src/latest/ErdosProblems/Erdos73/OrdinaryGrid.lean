/- An ordinary grid-minor bound from the checked bramble and linkage chain. -/
import ErdosProblems.Erdos73.ProperLinkage
import ErdosProblems.Erdos73.SimultaneousRouting
import ErdosProblems.Erdos73.PathBlocks
import ErdosProblems.Erdos73.GroupedRootedModels
import ErdosProblems.Erdos73.BranchRouting

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Erdos73Infrastructure.SimpleGraph

def ordinaryGridBrambleBound (g h : ℕ) : ℕ :=
  2 * (2 * h * simultaneousRoutingBound g h (h * h))

/-- A large bramble forces an ordinary grid or complete bipartite minor.
This theorem does not assert control of the resulting minor by a tangle. -/
theorem bramble_grid_or_completeBipartite
    {V : Type*} [Fintype V] {G : SimpleGraph V} {β : Finset (Finset V)}
    (hβ : IsFiniteBramble G β) (g h : ℕ) (hh : 0 < h)
    (horder : BrambleOrderAtLeast (ordinaryGridBrambleBound g h) β) :
    IsMinor (squareGrid g) G ∨ IsMinor (completeBipartiteGraph (Fin h) (Fin h)) G := by
  by_cases hg : IsMinor (squareGrid g) G
  · exact Or.inl hg
  by_cases hb : IsMinor (completeBipartiteGraph (Fin h) (Fin h)) G
  · exact Or.inr hb
  let I := Fin h ⊕ Fin h
  let E := Fin h × Fin h
  let s := simultaneousRoutingBound g h (h * h)
  have hs : 0 < s := simultaneousRoutingBound_pos g h _
  have hI : Fintype.card I = 2 * h := by simp [I, two_mul]
  have hE : Fintype.card E = h * h := by simp [E]
  have hpos : 0 < Fintype.card I * s := by rw [hI]; exact Nat.mul_pos (by omega) hs
  have hq : 2 * Fintype.card (Fin (Fintype.card I * s)) ≤ ordinaryGridBrambleBound g h := by
    simp only [Fintype.card_fin, hI, ordinaryGridBrambleBound, s, le_refl]
  obtain ⟨A, B, hAB, _, ⟨M⟩, _, _, hlinked⟩ := exists_treeSeparation_properLinked
    (SimpleGraph.pathGraph (Fintype.card I * s)) (pathGraph_isTree _ hpos) hβ horder hq
  let blocks (i : I) := pathBlock (s := s) ((Fintype.equivFin I) i)
  let X (i : I) := M.groupBranch (blocks i)
  let Z (i : I) := M.groupRoots (blocks i)
  have hXne (i : I) : (X i).Nonempty :=
    M.groupBranch_nonempty _ (pathBlock_nonempty hs _)
  have hXconn (i : I) : (G.induce (X i : Set V)).Connected :=
    M.groupBranch_connected _ (pathBlock_connected hs _)
  have hXdis : Pairwise fun i j => Disjoint (X i) (X j) := by
    intro i j hij
    exact M.groupBranch_disjoint (pathBlock_disjoint ((Fintype.equivFin I).injective.ne hij))
  have hZsub (i : I) : Z i ⊆ A ∩ B := M.groupRoots_subset_separator _
  have hZbranch (i : I) : Z i ⊆ X i := M.groupRoots_subset_branch _
  have hZcard (i : I) : (Z i).card = s := by
    rw [LeftRootedModel.groupRoots_card, pathBlock_card]
  let left (e : E) : I := Sum.inl e.1
  let right (e : E) : I := Sum.inr e.2
  have hp (e : E) := hlinked (Z (left e)) (Z (right e)) (hZsub _) (hZsub _)
    ((hZcard _).trans (hZcard _).symm)
  choose P hPcard hPprop using hp
  have hPproper (e : E) : (P e).toPathPacking.IsBoundaryProper (A ∩ B) := by
    intro r
    exact ⟨hZsub _ ((P e).endpoint_clean r).source_mem,
      hZsub _ ((P e).endpoint_clean r).target_mem, (hPprop e r).2.1, (hPprop e r).2.2⟩
  have hPsize (e : E) : simultaneousRoutingBound g h (Fintype.card E) ≤ (P e).toPathPacking.card := by
    rw [hE, EndpointCleanPathPacking.toPathPacking_card, hPcard, hZcard]
  obtain ⟨R, hR, hRd⟩ := exists_boundaryProper_disjoint_paths_staysIn
    (fun e => Z (left e)) (fun e => Z (right e)) (A ∩ B) B
    (fun e => (P e).toPathPacking) hPproper (fun e => hZsub _) (fun e => hZsub _)
    Finset.inter_subset_right (fun e r => (hPprop e r).1) g h hh hPsize hg hb
  let R' (e : E) := (R e).orient (hR e).1
  have hR'verts (e : E) : (R' e).vertexSet = (R e).vertexSet :=
    GraphPath.orient_vertexSet _ _
  let model : BranchRouting (completeBipartiteGraph (Fin h) (Fin h)) G E := {
    base := X
    nonempty := hXne
    connected := hXconn
    disjoint := hXdis
    source := left
    target := right
    source_ne_target := fun e => Sum.inl_ne_inr
    path := R'
    starts := fun e => hZbranch _ (GraphPath.orient_source_mem _ _)
    ends := fun e => hZbranch _ (GraphPath.orient_target_mem _ _)
    meets_base := by
      intro e i v hv hvX
      have hvB : v ∈ B := (hR e).2.2 ((hR'verts e) ▸ hv)
      have hvA : v ∈ A := M.groupBranch_subset_left _ hvX
      exact ((hR e).2.1.orient (hR e).1).internal_disjoint hv (Finset.mem_inter.mpr ⟨hvA, hvB⟩)
    paths_disjoint := by
      intro e f hef
      rw [hR'verts e, hR'verts f]
      exact hRd hef
    realizes := by
      intro i j hij
      cases i with
      | inl i =>
        cases j with
        | inl j => simp [completeBipartiteGraph] at hij
        | inr j => exact ⟨(i, j), Or.inl ⟨rfl, rfl⟩⟩
      | inr i =>
        cases j with
        | inl j => exact ⟨(j, i), Or.inr ⟨rfl, rfl⟩⟩
        | inr j => simp [completeBipartiteGraph] at hij }
  exact Or.inr ⟨model.toMinorModel⟩

/-- Parity of the coordinate sum embeds the square grid into a complete
bipartite graph with more than its total number of vertices on each side. -/
def squareGridCopyCompleteBipartite (g : ℕ) :
    (squareGrid g).Copy (completeBipartiteGraph (Fin (g * g + 1)) (Fin (g * g + 1))) := by
  let index (x : Fin g × Fin g) : Fin (g * g + 1) := (finProdFinEquiv x).castSucc
  let f (x : Fin g × Fin g) : Fin (g * g + 1) ⊕ Fin (g * g + 1) :=
    if (x.1.val + x.2.val) % 2 = 0 then Sum.inl (index x) else Sum.inr (index x)
  have hinj : Function.Injective index := fun x y h =>
    finProdFinEquiv.injective (Fin.castSucc_injective _ h)
  refine { toHom := { toFun := f, map_rel' := ?_ }, injective' := ?_ }
  · intro x y hxy
    have hstep : (x.1.val + x.2.val) + 1 = y.1.val + y.2.val ∨
        (y.1.val + y.2.val) + 1 = x.1.val + x.2.val := by
      rcases hxy with ⟨h, heq⟩ | ⟨h, heq⟩
      · have h' := SimpleGraph.pathGraph_adj.mp h
        have he := congrArg Fin.val heq
        omega
      · have h' := SimpleGraph.pathGraph_adj.mp h
        have he := congrArg Fin.val heq
        omega
    by_cases hx : (x.1.val + x.2.val) % 2 = 0 <;>
      by_cases hy : (y.1.val + y.2.val) % 2 = 0
    · omega
    · simp only [f, if_pos hx, if_neg hy, completeBipartiteGraph_adj]
      exact Or.inl ⟨rfl, rfl⟩
    · simp only [f, if_neg hx, if_pos hy, completeBipartiteGraph_adj]
      exact Or.inr ⟨rfl, rfl⟩
    · omega
  · intro x y hxy
    apply hinj
    change f x = f y at hxy
    have he := congrArg (Sum.elim id id) hxy
    simpa only [f, apply_ite, Sum.elim_inl, Sum.elim_inr, id_eq, ite_self] using he

def ordinarySquareGridBound (g : ℕ) : ℕ := ordinaryGridBrambleBound g (g * g + 1)

/-- Every finite graph with a bramble of this explicit order contains an
ordinary square-grid minor. No tangle orientation claim is included. -/
theorem squareGrid_minor_of_bramble
    {V : Type*} [Fintype V] {G : SimpleGraph V} {β : Finset (Finset V)}
    (hβ : IsFiniteBramble G β) (g : ℕ)
    (horder : BrambleOrderAtLeast (ordinarySquareGridBound g) β) :
    IsMinor (squareGrid g) G := by
  rcases bramble_grid_or_completeBipartite hβ g (g * g + 1) (Nat.succ_pos _) horder with h | h
  · exact h
  · exact (show IsMinor (squareGrid g)
      (completeBipartiteGraph (Fin (g * g + 1)) (Fin (g * g + 1))) from
      ⟨MinorModel.of_copy (squareGridCopyCompleteBipartite g)⟩).trans h

end
end Erdos73
