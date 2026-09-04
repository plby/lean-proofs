/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.Connectivity

/-!
# The structural core for Erdős Problem 916

This file isolates the connectivity bookkeeping in the Thomassen--Toft
minimum-degree reduction.  The reduction naturally has a slightly stronger
form: one distinguished vertex is allowed to have small degree, and the
`K₂,₃` certificate avoids that vertex.  This strengthening is what makes an
induction through an end piece at a cut vertex possible.
-/

attribute [local instance] Classical.propDecidable

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace K23Reduction

/-- A reduction certificate avoids a distinguished vertex. -/
def Avoids (R : K23Reduction G) (x₀ : V) : Prop :=
  x₀ ∉ Set.range R.copy

theorem avoids_iff (R : K23Reduction G) (x₀ : V) :
    R.Avoids x₀ ↔ ∀ z : Fin 2 ⊕ Fin 3, R.copy z ≠ x₀ := by
  simp [Avoids]

/-- Lift a reduction in an induced subgraph once the four required ambient
degree equalities have been supplied. -/
def liftInduce (S : Set V) (R : K23Reduction (G.induce S))
    (hleft : ∀ i : Fin 2, G.degree (R.copy (.inl i)).1 = 3)
    (hright : ∀ j : Fin 2,
      G.degree (R.copy (.inr (firstTwo j))).1 = 3) : K23Reduction G where
  copy := R.copy.trans (SimpleGraph.Embedding.induce S)
  degree_left := hleft
  degree_right := hright

@[simp] theorem liftInduce_copy (S : Set V) (R : K23Reduction (G.induce S))
    (hleft : ∀ i : Fin 2, G.degree (R.copy (.inl i)).1 = 3)
    (hright : ∀ j : Fin 2,
      G.degree (R.copy (.inr (firstTwo j))).1 = 3)
    (z : Fin 2 ⊕ Fin 3) :
    (R.liftInduce S hleft hright).copy z = (R.copy z).1 := rfl

end K23Reduction

/-- Minimum degree three away from one distinguished vertex. -/
def MinDegreeThreeExcept (G : SimpleGraph V) [DecidableRel G.Adj] (x₀ : V) : Prop :=
  ∀ v : V, v ≠ x₀ → 3 ≤ G.degree v

/-- The strengthened output used in the cut-vertex induction. -/
def StructuralAlternative (G : SimpleGraph V) [DecidableRel G.Adj] (x₀ : V) : Prop :=
  HasWheelWitness G ∨ ∃ R : K23Reduction G, R.Avoids x₀

/-- The dependency-minimized statement of the genuinely two-connected part
of Thomassen--Toft's structural theorem. -/
def VertexTwoConnectedCorePrinciple : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (x₀ : W),
      2 ≤ Fintype.card W →
      (H.Connected ∧ ∀ c : W, (H.induce (fun w : W => w ≠ c)).Connected) →
      MinDegreeThreeExcept H x₀ →
      StructuralAlternative H x₀

namespace ComponentEndBlock

variable {c x₀ : V} (K : (deleteVertex G c).ConnectedComponent)

private theorem mem_side_of_mem_verts_ne_cut {v : V}
    (hv : v ∈ verts c K) (hvc : v ≠ c) : v ∈ side c K := by
  simpa [verts, hvc] using hv

/-- A reduction in a component end piece which avoids its cut vertex lifts
to a reduction in the ambient graph.  Avoiding the cut vertex is essential:
all other end-piece vertices retain their ambient degree. -/
def liftReduction
    (R : K23Reduction (G.induce (verts c K)))
    (havoid : R.Avoids ⟨c, by simp [verts]⟩) : K23Reduction G := by
  have hne (z : Fin 2 ⊕ Fin 3) : (R.copy z).1 ≠ c := by
    intro hz
    apply (R.avoids_iff ⟨c, by simp [verts]⟩).mp havoid z
    apply Subtype.ext
    exact hz
  have hside (z : Fin 2 ⊕ Fin 3) : (R.copy z).1 ∈ side c K :=
    mem_side_of_mem_verts_ne_cut K (R.copy z).property (hne z)
  apply R.liftInduce (verts c K)
  · intro i
    rw [← degree_induce_verts (G := G) K (hside (.inl i))]
    exact R.degree_left i
  · intro j
    rw [← degree_induce_verts (G := G) K (hside (.inr (firstTwo j)))]
    exact R.degree_right j

@[simp] theorem liftReduction_copy
    (R : K23Reduction (G.induce (verts c K)))
    (havoid : R.Avoids ⟨c, by simp [verts]⟩)
    (z : Fin 2 ⊕ Fin 3) :
    (liftReduction K R havoid).copy z = (R.copy z).1 := rfl

/-- If the chosen component side avoids `x₀`, then a lifted certificate
which avoids the cut vertex also avoids `x₀`. -/
theorem liftReduction_avoids
    (hsideAvoid : x₀ = c ∨ x₀ ∉ side c K)
    (R : K23Reduction (G.induce (verts c K)))
    (havoid : R.Avoids ⟨c, by simp [verts]⟩) :
    (liftReduction K R havoid).Avoids x₀ := by
  rw [K23Reduction.avoids_iff]
  intro z hz
  have hzcut : (R.copy z).1 ≠ c := by
    intro h
    apply (K23Reduction.avoids_iff R ⟨c, by simp [verts]⟩).mp havoid z
    apply Subtype.ext
    exact h
  have hzside : (R.copy z).1 ∈ side c K :=
    mem_side_of_mem_verts_ne_cut K (R.copy z).property hzcut
  rcases hsideAvoid with rfl | hx
  · exact hzcut hz
  · exact hx (hz ▸ hzside)

end ComponentEndBlock

/-! ## Reduction from connected graphs to the two-connected core -/

/-- Assuming the two-connected Thomassen--Toft core, the strengthened
structural alternative holds for every connected graph.  This is the N1
endblock induction, formalized with an explicit exceptional vertex. -/
theorem connected_structural_of_vertexTwoConnectedCore
    (hcore : VertexTwoConnectedCorePrinciple.{u})
    {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (x₀ : W) (hcard : 2 ≤ Fintype.card W)
    (hconn : H.Connected) (hdeg : MinDegreeThreeExcept H x₀) :
    StructuralAlternative H x₀ := by
  classical
  induction hn : Fintype.card W using Nat.strong_induction_on generalizing W with
  | h n ih =>
      by_cases hcut : ∃ c : W, IsCutVertex H c
      · obtain ⟨c, hc⟩ := hcut
        obtain ⟨K, havoidSide, hproper, hpieceConn, -⟩ :=
          ComponentEndBlock.endblock_reduction_N1 hconn c x₀ hc
        let S : Set W := ComponentEndBlock.verts c K
        let J : SimpleGraph S := H.induce S
        let c' : S := ⟨c, by simp [S, ComponentEndBlock.verts]⟩
        have hcardJ : 2 ≤ Fintype.card S := by
          obtain ⟨v, hv⟩ := ComponentEndBlock.side_nonempty (G := H) c K
          have hvc : v ≠ c := by
            intro h
            subst v
            exact ComponentEndBlock.cut_not_mem_side (G := H) c K hv
          have hne : (⟨v, by simp [S, ComponentEndBlock.verts, hv]⟩ : S) ≠ c' := by
            intro heq
            exact hvc (congrArg Subtype.val heq)
          rw [show (2 : ℕ) = 1 + 1 by omega]
          exact Fintype.one_lt_card_iff.mpr ⟨_, _, hne⟩
        have hcard_lt : Fintype.card S < n := by
          rw [← hn]
          exact ComponentEndBlock.card_verts_lt (G := H) K hproper
        have hdegJ : MinDegreeThreeExcept J c' := by
          intro v hvcut
          have hvne : v.1 ≠ c := by
            intro heq
            apply hvcut
            apply Subtype.ext
            exact heq
          have hvside : v.1 ∈ ComponentEndBlock.side c K := by
            have hvverts : v.1 ∈ ComponentEndBlock.verts c K := by
              simpa [S] using v.2
            simpa [ComponentEndBlock.verts, hvne] using hvverts
          have hvx₀ : v.1 ≠ x₀ := by
            rcases havoidSide with rfl | hx₀side
            · exact hvne
            · intro hvx
              exact hx₀side (hvx ▸ hvside)
          rw [show J.degree v = H.degree v.1 by
            simpa [J, S] using
              ComponentEndBlock.degree_induce_verts (G := H) K hvside]
          exact hdeg v.1 hvx₀
        have hrec : StructuralAlternative J c' :=
          ih (Fintype.card S) hcard_lt J c' hcardJ (by simpa [J, S] using hpieceConn)
            hdegJ rfl
        rcases hrec with hW | ⟨R, hRavoid⟩
        · exact Or.inl (HasWheelWitness.induce S hW)
        · exact Or.inr ⟨ComponentEndBlock.liftReduction K R hRavoid,
            ComponentEndBlock.liftReduction_avoids K havoidSide R hRavoid⟩
      · have hncut : ∀ c : W, ¬IsCutVertex H c := by
          simpa only [not_exists] using hcut
        have htwo : H.Connected ∧
            ∀ c : W, (H.induce (fun w : W => w ≠ c)).Connected := by
          refine ⟨hconn, ?_⟩
          intro c
          have hnonempty : Nonempty {w : W // w ≠ c} := by
            obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card W)
            by_cases hac : a ≠ c
            · exact ⟨⟨a, hac⟩⟩
            · have hbc : b ≠ c := by
                intro hbc
                apply hab
                exact (not_ne_iff.mp hac).trans hbc.symm
              exact ⟨⟨b, hbc⟩⟩
          change (deleteVertex H c).Connected
          let : Nonempty {w : W // w ≠ c} := hnonempty
          exact SimpleGraph.Connected.mk (not_not.mp (hncut c))
        exact @hcore W _ _ H _ x₀ hcard htwo hdeg

/-! ## Reduction of arbitrary nonempty graphs to a connected component -/

namespace ConnectedComponent

noncomputable local instance componentFintype
    (C : G.ConnectedComponent) : Fintype C := Fintype.ofFinite C

noncomputable local instance componentAdjDecidable
    (C : G.ConnectedComponent) : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _

/-- Passing to a connected component preserves every vertex degree. -/
theorem degree_toSimpleGraph (C : G.ConnectedComponent) (v : C) :
    C.toSimpleGraph.degree v = G.degree v.1 := by
  exact degree_connectedComponent G C v

/-- A component of a graph of minimum degree at least three has at least four
vertices. -/
theorem four_le_card (C : G.ConnectedComponent)
    (hdeg : ∀ v : V, 3 ≤ G.degree v) : 4 ≤ Fintype.card C := by
  obtain ⟨v, hv⟩ := C.nonempty_supp
  let v' : C := ⟨v, hv⟩
  have hthree : 3 ≤ C.toSimpleGraph.degree v' := by
    rw [degree_toSimpleGraph C v']
    exact hdeg v
  have hle : C.toSimpleGraph.degree v' < Fintype.card C :=
    C.toSimpleGraph.degree_lt_card_verts v'
  omega

end ConnectedComponent

/-- The full minimum-degree structural reduction, modulo only the
two-connected core.  A nonemptiness assumption is mathematically necessary:
on the empty vertex type the degree hypothesis is vacuous. -/
theorem structural_of_vertexTwoConnectedCore
    (hcore : VertexTwoConnectedCorePrinciple.{u})
    {W : Type u} [Fintype W] [DecidableEq W] [Nonempty W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hdeg : ∀ w : W, 3 ≤ H.degree w) :
    HasWheelWitness H ∨ Nonempty (K23Reduction H) := by
  classical
  let C : H.ConnectedComponent := H.connectedComponentMk (Classical.choice inferInstance)
  let : Fintype C := Fintype.ofFinite C
  let : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  obtain ⟨x, hx⟩ := C.nonempty_supp
  let x₀ : C := ⟨x, hx⟩
  have hcardC : 2 ≤ Fintype.card C :=
    (ConnectedComponent.four_le_card C hdeg).trans' (by omega)
  have hdegC : MinDegreeThreeExcept (V := C) C.toSimpleGraph x₀ :=
    fun v _ => by
      rw [ConnectedComponent.degree_toSimpleGraph C v]
      exact hdeg v.1
  have hC := connected_structural_of_vertexTwoConnectedCore hcore
    C.toSimpleGraph x₀ hcardC C.connected_toSimpleGraph hdegC
  rcases hC with hW | ⟨R, -⟩
  · let f : C.toSimpleGraph ↪g H :=
      { toFun := fun v => v.1
        inj' := Subtype.val_injective
        map_rel_iff' := Iff.rfl }
    exact Or.inl (HasWheelWitness.mapEmbedding f hW)
  · let f : C.toSimpleGraph ↪g H :=
      { toFun := fun v => v.1
        inj' := Subtype.val_injective
        map_rel_iff' := Iff.rfl }
    refine Or.inr ⟨{
      copy := R.copy.trans f
      degree_left := ?_
      degree_right := ?_ }⟩
    · intro i
      change H.degree (R.copy (.inl i)).1 = 3
      rw [← ConnectedComponent.degree_toSimpleGraph C (R.copy (.inl i))]
      exact R.degree_left i
    · intro j
      change H.degree (R.copy (.inr (firstTwo j))).1 = 3
      rw [← ConnectedComponent.degree_toSimpleGraph C
        (R.copy (.inr (firstTwo j)))]
      exact R.degree_right j

/-- Cardinal form of `structural_of_vertexTwoConnectedCore`, convenient for
the density induction. -/
theorem structural_of_vertexTwoConnectedCore_of_card
    (hcore : VertexTwoConnectedCorePrinciple.{u})
    {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hcard : 1 ≤ Fintype.card W)
    (hdeg : ∀ w : W, 3 ≤ H.degree w) :
    HasWheelWitness H ∨ Nonempty (K23Reduction H) := by
  let : Nonempty W := Fintype.card_pos_iff.mp hcard
  exact structural_of_vertexTwoConnectedCore hcore H hdeg

end Erdos916
