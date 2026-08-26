import ErdosProblems.Erdos593.TripleSystem.Embedding
import ErdosProblems.Erdos593.TripleSystem.Expansion
import ErdosProblems.Erdos593.TripleSystem.PairCodegree
import ErdosProblems.Erdos593.Graph.CompleteBipartiteEdges
import ErdosProblems.Erdos593.Graph.RainbowBipartite

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos593

universe u v

namespace TripleSystem

structure WitnessedBipartiteMatrix {W : Type u} {D : Type v}
    (H : TripleSystem W D) (q t : Nat) where
  left : Fin q ↪ W
  right : Fin q ↪ W
  apex : Fin q → Fin q → W
  edge : Fin q → Fin q → D
  core_disjoint : ∀ i j, left i ≠ right j
  apex_ne_left : ∀ i j k, apex i j ≠ left k
  apex_ne_right : ∀ i j k, apex i j ≠ right k
  edgeSet_eq : ∀ i j,
    H.edgeSet (edge i j) = {left i, right j, apex i j}
  locallyBounded : RainbowBipartite.LocallyBounded t apex

/-- Package independently selected cell witnesses into the matrix consumed by
the finite rainbow extraction. The global core-avoidance and local-bound
conditions remain explicit hypotheses: pair codegree alone does not supply
them. -/
def WitnessedBipartiteMatrix.ofThirdVertexWitnesses
    {W : Type u} {D : Type v} {H : TripleSystem W D} {q t : Nat}
    (left right : Fin q ↪ W) (apex : Fin q → Fin q → W)
    (cell : ∀ i j, ThirdVertexWitness H (left i) (right j) (apex i j))
    (core_disjoint : ∀ i j, left i ≠ right j)
    (apex_ne_left : ∀ i j k, apex i j ≠ left k)
    (apex_ne_right : ∀ i j k, apex i j ≠ right k)
    (locallyBounded : RainbowBipartite.LocallyBounded t apex) :
    WitnessedBipartiteMatrix H q t where
  left := left
  right := right
  apex := apex
  edge := fun i j => (cell i j).edge
  core_disjoint := core_disjoint
  apex_ne_left := apex_ne_left
  apex_ne_right := apex_ne_right
  edgeSet_eq := fun i j => (cell i j).edgeSet_eq
  locallyBounded := locallyBounded

noncomputable def WitnessedBipartiteMatrix.rainbowEmbedding
    {W : Type u} {D : Type v} {H : TripleSystem W D} {n q t : Nat}
    (M : WitnessedBipartiteMatrix H q t)
    (row column : Fin n ↪ Fin q)
    (hrainbow : RainbowBipartite.IsRainbow M.apex row column) :
    (privateVertexExpansion (completeBipartiteNN.{u} n)).Embedding H := by
  let G := completeBipartiteNN.{u} n
  let vertexMap : PrivateVertexExpansion.Point G → W
    | .inl (.inl a) => M.left (row a.down)
    | .inl (.inr b) => M.right (column b.down)
    | .inr e => M.apex (row (CompleteBipartiteEdges.coords n e).1.down)
        (column (CompleteBipartiteEdges.coords n e).2.down)
  let edgeMap : G.edgeSet → D := fun e =>
    M.edge (row (CompleteBipartiteEdges.coords n e).1.down)
      (column (CompleteBipartiteEdges.coords n e).2.down)
  have hvertexMap : Function.Injective vertexMap := by
    intro p q hpq
    rcases p with p | e <;> rcases q with q | f
    · rcases p with a | b <;> rcases q with c | d
      · have h : row a.down = row c.down := M.left.injective (by
          simpa [vertexMap] using! hpq)
        have hac : a.down = c.down := row.injective h
        have hac' : a = c := ULift.ext a c hac
        exact congrArg (fun z => Sum.inl (Sum.inl z)) hac'
      · exfalso
        exact M.core_disjoint (row a.down) (column d.down) (by
          simpa [vertexMap] using! hpq)
      · exfalso
        exact (M.core_disjoint (row c.down) (column b.down)).symm (by
          simpa [vertexMap] using! hpq)
      · have h : column b.down = column d.down := M.right.injective (by
          simpa [vertexMap] using! hpq)
        have hbd : b.down = d.down := column.injective h
        have hbd' : b = d := ULift.ext b d hbd
        exact congrArg (fun z => Sum.inl (Sum.inr z)) hbd'
    · rcases p with a | b
      · exfalso
        exact M.apex_ne_left
          (row (CompleteBipartiteEdges.coords n f).1.down)
          (column (CompleteBipartiteEdges.coords n f).2.down)
          (row a.down) (by simpa [vertexMap] using! hpq.symm)
      · exfalso
        exact M.apex_ne_right
          (row (CompleteBipartiteEdges.coords n f).1.down)
          (column (CompleteBipartiteEdges.coords n f).2.down)
          (column b.down) (by simpa [vertexMap] using! hpq.symm)
    · rcases q with a | b
      · exfalso
        exact M.apex_ne_left
          (row (CompleteBipartiteEdges.coords n e).1.down)
          (column (CompleteBipartiteEdges.coords n e).2.down)
          (row a.down) (by simpa [vertexMap] using! hpq)
      · exfalso
        exact M.apex_ne_right
          (row (CompleteBipartiteEdges.coords n e).1.down)
          (column (CompleteBipartiteEdges.coords n e).2.down)
          (column b.down) (by simpa [vertexMap] using! hpq)
    · have hcoord :
          ((CompleteBipartiteEdges.coords n e).1.down,
            (CompleteBipartiteEdges.coords n e).2.down) =
          ((CompleteBipartiteEdges.coords n f).1.down,
            (CompleteBipartiteEdges.coords n f).2.down) :=
        hrainbow (by simpa [vertexMap] using! hpq)
      have hcoords : CompleteBipartiteEdges.coords n e =
          CompleteBipartiteEdges.coords n f := by
        apply Prod.ext
        · apply ULift.ext
          exact congrArg Prod.fst hcoord
        · apply ULift.ext
          exact congrArg Prod.snd hcoord
      exact congrArg Sum.inr (CompleteBipartiteEdges.coords_injective n hcoords)
  let vertexEmbedding : PrivateVertexExpansion.Point G ↪ W :=
    { toFun := vertexMap
      inj' := hvertexMap }
  exact
    { vertex := vertexEmbedding
      edge := edgeMap
      map_edge := by
        intro e
        change vertexMap '' {p | PrivateVertexExpansion.Inc G p e} =
          H.edgeSet (edgeMap e)
        rw [← CompleteBipartiteEdges.edge_coords n e]
        have hInc :
            {p | PrivateVertexExpansion.Inc G p
              (CompleteBipartiteEdges.edge n
                (CompleteBipartiteEdges.coords n e).1
                (CompleteBipartiteEdges.coords n e).2)} =
              {PrivateVertexExpansion.core G
                (Sum.inl (CompleteBipartiteEdges.coords n e).1),
               PrivateVertexExpansion.core G
                (Sum.inr (CompleteBipartiteEdges.coords n e).2),
               PrivateVertexExpansion.privateVertex G
                (CompleteBipartiteEdges.edge n
                  (CompleteBipartiteEdges.coords n e).1
                  (CompleteBipartiteEdges.coords n e).2)} := by
          change {p | PrivateVertexExpansion.Inc G p
            (⟨s(Sum.inl (CompleteBipartiteEdges.coords n e).1,
                Sum.inr (CompleteBipartiteEdges.coords n e).2), by
                simp [G, completeBipartiteNN]⟩ : G.edgeSet)} = _
          exact PrivateVertexExpansion.incidenceSet_eq G (by
            simp [G, completeBipartiteNN])
        rw [hInc]
        rw [M.edgeSet_eq]
        ext z
        simp [vertexMap, PrivateVertexExpansion.core,
          PrivateVertexExpansion.privateVertex,
          CompleteBipartiteEdges.coords_edge, eq_comm] }

theorem exists_rainbowEmbedding_of_witnessedMatrices
    {W : Type u} {D : Type v} (H : TripleSystem W D) (n t : Nat)
    (hn : 0 < n) (ht : 0 < t)
    (hmat : ∀ q : Nat, Nonempty (WitnessedBipartiteMatrix H q t)) :
    Nonempty ((privateVertexExpansion (completeBipartiteNN.{u} n)).Embedding H) := by
  obtain ⟨q, hq⟩ :=
    RainbowBipartite.exists_rainbow_bipartite_submatrix n t hn ht
  obtain ⟨M⟩ := hmat q
  obtain ⟨row, column, hrainbow⟩ := hq W M.apex M.locallyBounded
  exact ⟨M.rainbowEmbedding row column hrainbow⟩

end TripleSystem
end Erdos593
