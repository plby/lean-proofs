/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.LeafExtension
import ErdosProblems.Erdos570.SparseColoring
import ErdosProblems.Erdos570.Neighborhood
import ErdosProblems.Erdos570.RamseyRegion

/-!
# Repeated leaf obstructions inside a fixed neighborhood

Once one obstruction supplies a set `S` in a red neighborhood, a red
`P_(k-1)` cannot occur inside `S`.  A path-versus-core Ramsey bound can
therefore be applied repeatedly after deleting the previously selected
parents.  Each resulting core copy either extends to the target or supplies
a new parent with a large unused red neighborhood.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

/-- The data accumulated after `t` repetitions of the leaf obstruction. -/
structure LeafObstructionFamily
    {W : Type*} [Fintype W] [DecidableEq W]
    (C : SimpleGraph W) (S T : Finset W)
    (leafCount globalLower t : ℕ) where
  parent : Fin t → W
  unused : Fin t → Finset W
  parent_injective : Function.Injective parent
  parent_mem : ∀ i, parent i ∈ S
  red_neighborhood : ∀ i, ∀ x ∈ unused i, C.Adj (parent i) x
  global_large : ∀ i, globalLower ≤ (unused i).card
  outside_large : ∀ i,
    T.card - (leafCount - 1) ≤ ((unused i) ∩ T).card

/-- The empty obstruction family. -/
def LeafObstructionFamily.empty
    {W : Type*} [Fintype W] [DecidableEq W]
    (C : SimpleGraph W) (S T : Finset W)
    (leafCount globalLower : ℕ) :
    LeafObstructionFamily C S T leafCount globalLower 0 where
  parent := Fin.elim0
  unused := Fin.elim0
  parent_injective := fun i ↦ Fin.elim0 i
  parent_mem := fun i ↦ Fin.elim0 i
  red_neighborhood := fun i ↦ Fin.elim0 i
  global_large := fun i ↦ Fin.elim0 i
  outside_large := fun i ↦ Fin.elim0 i

/-- A path copy in a finite region contained in a vertex neighborhood closes
to a cycle with the center vertex. -/
theorem no_path_induce_of_subset_neighbor
    {W : Type*} [Fintype W] [DecidableEq W]
    {C : SimpleGraph W} {k : ℕ} (hk : 3 ≤ k)
    (hcycle : ¬SimpleGraph.cycleGraph k ⊑ C)
    (z : W) (R : Finset W)
    (hR : ∀ x ∈ R, C.Adj z x) :
    ¬SimpleGraph.pathGraph (k - 1) ⊑ C.induce (R : Set W) := by
  have hkn : 2 ≤ k - 1 := by omega
  have hcycle' : ¬SimpleGraph.cycleGraph ((k - 1) + 1) ⊑ C := by
    rw [show (k - 1) + 1 = k by omega]
    exact hcycle
  have hnone :=
    pathGraph_not_isContained_neighbor_of_cycleGraph_not_isContained
      hkn z hcycle'
  intro hpath
  apply hnone
  let e : C.induce (R : Set W) →g C.induce (C.neighborSet z) :=
    { toFun := fun x ↦ ⟨x.1, hR x.1 x.2⟩
      map_rel' := by
        intro x y hxy
        exact hxy }
  have he : Function.Injective e := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun q : ↥(C.neighborSet z) ↦ q.1) hxy
  exact hpath.trans ⟨e.toCopy he⟩

/-- Repeatedly find distinct leaf obstructions in `S`.  The only numerical
cost per repetition is one removed parent; the chosen leaf set pays for all
those removals in addition to the path Ramsey overhead. -/
theorem exists_leafObstructionFamily
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (hconn : H.graph.Connected) (hn : 3 ≤ H.vertexCount)
    (L : Finset (Fin H.vertexCount))
    (hL : ∀ v ∈ L, H.graph.degree v = 1)
    (C : SimpleGraph W) (S T : Finset W) (z : W)
    {k t : ℕ} (hk : 3 ≤ k)
    (hScard : S.card = H.vertexCount)
    (hTS : T = Sᶜ)
    (hremain : 2 ≤ H.vertexCount - L.card)
    (hzS : ∀ x ∈ S, C.Adj z x)
    (hnoCycle : ¬SimpleGraph.cycleGraph k ⊑ C)
    (hnoH : ¬H.graph ⊑ Cᶜ)
    (hroom : t + (k - 1) *
      (1 + 2 * (H.edgeCount + 1 - H.vertexCount)) ≤ L.card) :
    Nonempty (LeafObstructionFamily C S T L.card
      (Fintype.card W - (H.vertexCount - 1)) t) := by
  classical
  let Q := deleteLeavesCode H L
  have hLcard : L.card ≤ H.vertexCount := by
    simpa using Finset.card_le_card (Finset.subset_univ L)
  have hQconn : Q.graph.Connected :=
    deleteLeavesCode_connected H hconn L hL (by omega)
  have hQexcess : Q.edgeCount + 1 - Q.vertexCount ≤
      H.edgeCount + 1 - H.vertexCount :=
    deleteLeavesCode_sparseExcess_le H hconn hn L hL
  induction t with
  | zero => exact ⟨LeafObstructionFamily.empty C S T L.card
      (Fintype.card W - (H.vertexCount - 1))⟩
  | succ t ih =>
      have hroomPrev : t + (k - 1) *
          (1 + 2 * (H.edgeCount + 1 - H.vertexCount)) ≤ L.card := by
        omega
      obtain ⟨F⟩ := ih hroomPrev
      let usedParents : Finset W := Finset.univ.image F.parent
      let R : Finset W := S \ usedParents
      have hparentRangeCard : usedParents.card = t := by
        dsimp only [usedParents]
        rw [Finset.card_image_of_injective _ F.parent_injective]
        simp
      have hparentRangeS : usedParents ⊆ S := by
        intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨i, _, rfl⟩ := hx
        exact F.parent_mem i
      have hRcard : R.card = H.vertexCount - t := by
        dsimp only [R]
        rw [Finset.card_sdiff_of_subset hparentRangeS,
          hparentRangeCard, hScard]
      have hpathSize : Q.vertexCount + (k - 1) *
          (1 + 2 * (Q.edgeCount + 1 - Q.vertexCount)) ≤ R.card := by
        have hcost : (k - 1) *
            (1 + 2 * (Q.edgeCount + 1 - Q.vertexCount)) ≤
            (k - 1) *
              (1 + 2 * (H.edgeCount + 1 - H.vertexCount)) :=
          Nat.mul_le_mul_left (k - 1)
          (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hQexcess) 1)
        have hqv : Q.vertexCount = H.vertexCount - L.card := by
          simp [Q]
        rw [hqv] at hcost
        have htotal : Q.vertexCount + (k - 1) *
              (1 + 2 * (Q.edgeCount + 1 - Q.vertexCount)) + t ≤
            H.vertexCount := by
          calc
            Q.vertexCount + (k - 1) *
                (1 + 2 * (Q.edgeCount + 1 - Q.vertexCount)) + t ≤
                (H.vertexCount - L.card) + (k - 1) *
                  (1 + 2 * (H.edgeCount + 1 - H.vertexCount)) + t := by
              rw [hqv]
              exact Nat.add_le_add_right
                (Nat.add_le_add_left hcost (H.vertexCount - L.card)) t
            _ = (H.vertexCount - L.card) +
                ((k - 1) *
                  (1 + 2 * (H.edgeCount + 1 - H.vertexCount)) + t) := by
              omega
            _ ≤ (H.vertexCount - L.card) + L.card := by
              apply Nat.add_le_add_left
              omega
            _ = H.vertexCount := Nat.sub_add_cancel hLcard
        rw [hRcard]
        exact Nat.le_sub_of_add_le (by omega)
      have hRam : RamseyAt (pathCode (k - 1)) Q
          (Q.vertexCount + (k - 1) *
            (1 + 2 * (Q.edgeCount + 1 - Q.vertexCount))) :=
        ramseyAt_path_connected_excess Q hQconn (by omega) le_rfl
      rcases Erdos570.RamseyAt.on_finset hRam C R hpathSize with
        hred | hblue
      · have hnoPath := no_path_induce_of_subset_neighbor hk hnoCycle z R
          (fun x hx ↦ hzS x (Finset.mem_sdiff.mp hx).1)
        exact (hnoPath (by simpa [pathCode] using hred)).elim
      · let e := inducedCodeIso H (Finset.univ \ L)
        let copy : SimpleGraph.Copy
            (H.graph.induce
              ((Finset.univ \ L : Finset (Fin H.vertexCount)) : Set _)) Cᶜ :=
          (SimpleGraph.Embedding.induce (G := Cᶜ) (R : Set W)).toCopy.comp
            (hblue.some.comp e.toCopy)
        rcases isContained_or_leaf_obstruction H hconn hn L Cᶜ hL copy with
          hHcopy | ⟨d, U, hUglobal, hUneighbor, hUoutside⟩
        · exact (hnoH hHcopy).elim
        · have hcopyR : ∀ e, copy e ∈ R := by
            intro v
            exact (hblue.some (e v)).2
          have hcopyS : copy d ∈ S :=
            (Finset.mem_sdiff.mp (hcopyR d)).1
          have hcopyNotRange : copy d ∉ Set.range F.parent := by
            rintro ⟨i, hi⟩
            have hmemUsed : F.parent i ∈ usedParents := by
              apply Finset.mem_image.mpr
              exact ⟨i, Finset.mem_univ _, rfl⟩
            exact (Finset.mem_sdiff.mp (hcopyR d)).2 (hi ▸ hmemUsed)
          let parent' : Fin (t + 1) → W := Fin.snoc F.parent (copy d)
          let unused' : Fin (t + 1) → Finset W := Fin.snoc F.unused U
          refine ⟨
            { parent := parent'
              unused := unused'
              parent_injective := Fin.snoc_injective_of_injective
                F.parent_injective hcopyNotRange
              parent_mem := ?_
              red_neighborhood := ?_
              global_large := ?_
              outside_large := ?_ }⟩
          · intro i
            induction i using Fin.lastCases with
            | last => simpa [parent'] using hcopyS
            | cast i => simpa [parent'] using F.parent_mem i
          · intro i x hx
            induction i using Fin.lastCases with
            | last =>
                have h := hUneighbor x (by simpa [unused'] using hx)
                simpa [parent'] using h
            | cast i =>
                simpa [parent'] using
                  F.red_neighborhood i x (by simpa [unused'] using hx)
          · intro i
            induction i using Fin.lastCases with
            | last => simpa [unused'] using hUglobal
            | cast i => simpa [unused'] using F.global_large i
          · intro i
            induction i using Fin.lastCases with
            | last =>
                have hu := hUoutside S (fun v ↦
                  (Finset.mem_sdiff.mp (hcopyR v)).1)
                simpa [unused', hTS] using hu
            | cast i => simpa [unused'] using F.outside_large i

end Erdos570
