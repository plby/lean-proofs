/- A grid minor whose row orientation is controlled by the original haven. -/
import ErdosProblems.Erdos73.ControlledRouting

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Erdos73Infrastructure.SimpleGraph

def controlledGridBlockSize (g : ℕ) : ℕ :=
  max (2 * g) (controlledRoutingBound g ((g * g + 1) * (g * g + 1)))

def controlledGridBrambleBound (g : ℕ) : ℕ :=
  2 * (2 * (g * g + 1) * controlledGridBlockSize g + g + 1)

/-- The grid is controlled by this specific haven, not merely contained
as an ordinary minor in a graph of large bramble order. -/
theorem BrambleHaven.exists_grid_with_row_control
    {V : Type*} [Fintype V] {G : SimpleGraph V} {β : Finset (Finset V)} {q : ℕ}
    (haven : BrambleHaven G β q) (g : ℕ) (horder : controlledGridBrambleBound g ≤ q) :
    ∃ M : MinorModel (squareGrid g) G, NoGridRowInHavenSmallSide haven M := by
  by_contra hno
  let h := g * g + 1
  let I := Fin h ⊕ Fin h
  let E := Fin h × Fin h
  let s := controlledGridBlockSize g
  have hs : 0 < s := (controlledRoutingBound_pos g _).trans_le (Nat.le_max_right _ _)
  have hsg : 2 * g ≤ s := Nat.le_max_left _ _
  have hI : Fintype.card I = 2 * h := by simp [I, two_mul]
  have hE : Fintype.card E = h * h := by simp [E]
  have hpos : 0 < Fintype.card I * s := by
    rw [hI]
    exact Nat.mul_pos (by dsimp only [h]; omega) hs
  have hbound : 2 * (Fintype.card I * s + g + 1) ≤ q := by
    simpa only [hI, h, s, controlledGridBrambleBound] using horder
  obtain ⟨A, B, hAB, hcard, hpoint, hsat, ⟨M⟩⟩ := haven.exists_saturated_treeModel
    (SimpleGraph.pathGraph (Fintype.card I * s)) (pathGraph_isTree _ hpos)
    (by rw [Fintype.card_fin]; omega)
  have hmin := haven.forwardSaturated_minimal hsat
  have hrootcard : (A ∩ B).card = Fintype.card I * s := by
    simpa only [Fintype.card_fin] using hcard
  have hnoRooted : NoRootedColumnRichGrid G (A ∩ B) g :=
    noRootedColumnRichGrid_of_no_controlledGrid haven hAB hpoint hmin
      (by rw [hrootcard]; omega) hno
  have hlinked : BoundaryProperLinked G B (A ∩ B) := by
    intro X Y hX hY hXY
    exact haven.exists_boundaryProperLinkage hAB hpoint hmin hX hY hXY
      (by rw [hrootcard]; omega)
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
  have hPsize (e : E) : controlledRoutingBound g (Fintype.card E) ≤ (P e).toPathPacking.card := by
    rw [hE, EndpointCleanPathPacking.toPathPacking_card, hPcard, hZcard]
    exact Nat.le_max_right _ _
  obtain ⟨R, hR, hRd⟩ := exists_controlled_boundaryProper_disjoint_paths_staysIn
    (fun e => Z (left e)) (fun e => Z (right e)) (A ∩ B) B
    (fun e => (P e).toPathPacking) hPproper (fun e => hZsub _) (fun e => hZsub _)
    Finset.inter_subset_right (fun e r => (hPprop e r).1) g hPsize hnoRooted
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
  let Q (j : Fin (Fintype.card I * s)) : Finset V := {M.root j}
  have hQconn (j : Fin (Fintype.card I * s)) :
      (G.induce (Q j : Set V)).Connected := (MinorModel.refl G).branch_connected (M.root j)
  have hQdis : Pairwise fun i j => Disjoint (Q i) (Q j) :=
    fun _ _ hij => Finset.disjoint_singleton.mpr (M.root_injective.ne hij)
  have hQroot (j : Fin (Fintype.card I * s)) : ∃ v ∈ Q j, v ∈ A ∩ B :=
    ⟨M.root j, Finset.mem_singleton_self _, M.root_mem_separator j⟩
  apply hnoRooted _ Q hQconn hQdis hQroot
  apply ColumnRichBipartite.toGrid
  refine ⟨model.toMinorModel, fun r => ?_⟩
  refine ⟨blocks (Sum.inl r), ?_, fun j hj => ?_⟩
  · change 2 * g ≤ (pathBlock ((Fintype.equivFin I) (Sum.inl r))).card
    rw [pathBlock_card]
    exact hsg
  · refine ⟨M.root j, Finset.mem_singleton_self _, ?_⟩
    apply model.base_subset_augmented (Sum.inl r)
    exact (M.mem_groupBranch _ _).mpr ⟨j, hj, M.root_mem j⟩

/-- A sufficiently high-order finite bramble admits a haven and a grid
model agreeing with that haven on all separations of order below the grid size. -/
theorem exists_haven_and_grid_with_row_control
    {V : Type*} [Fintype V] {G : SimpleGraph V} {β : Finset (Finset V)}
    (hβ : IsFiniteBramble G β) (g : ℕ)
    (horder : BrambleOrderAtLeast (controlledGridBrambleBound g) β) :
    ∃ haven : BrambleHaven G β (controlledGridBrambleBound g),
      ∃ M : MinorModel (squareGrid g) G, NoGridRowInHavenSmallSide haven M := by
  obtain ⟨haven⟩ := exists_brambleHaven hβ horder
  exact ⟨haven, haven.exists_grid_with_row_control g le_rfl⟩

end
end Erdos73

