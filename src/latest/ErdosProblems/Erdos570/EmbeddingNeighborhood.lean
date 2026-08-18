/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.Support
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! # A large host neighborhood from a one-vertex target deletion -/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

/-- If `H-v` already occurs in the complement of `C`, but `H` does not,
then some image of a neighbor of `v` has a large red neighborhood.  The
inequality is the division-free pigeonhole statement used in the CFMPP
induction. -/
theorem exists_large_degree_of_delete_vertex_copy
    {W V : Type*} [Fintype W] [Fintype V]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (C : SimpleGraph V) [DecidableRel C.Adj]
    (v : W) (hdeg : 0 < H.degree v)
    (hcopy : H.induce ({v} : Set W)ᶜ ⊑ Cᶜ)
    (hno : ¬ H ⊑ Cᶜ) :
    ∃ u : V,
      Fintype.card V - (Fintype.card W - 1) ≤ H.degree v * C.degree u := by
  classical
  obtain ⟨copy⟩ := hcopy
  let D := {w : W // w ≠ v}
  let fD : D → V := fun w ↦ copy ⟨w.1, by
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using w.2⟩
  have hfD : Function.Injective fD := by
    intro x y hxy
    have hsub := copy.injective hxy
    exact Subtype.ext (congrArg Subtype.val hsub)
  let occupied : Finset V := Finset.univ.image fD
  have hoccupied : occupied.card = Fintype.card W - 1 := by
    calc
      occupied.card = Fintype.card D := by
        change (Finset.univ.image fD).card = Fintype.card D
        rw [Finset.card_image_of_injective _ hfD]
        simp
      _ = Fintype.card W - 1 := by
        change Fintype.card {w : W // ¬w = v} = _
        rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  let spare : Finset V := Finset.univ \ occupied
  have hspare : spare.card = Fintype.card V - (Fintype.card W - 1) := by
    change (Finset.univ \ occupied).card = _
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ occupied),
      Finset.card_univ, hoccupied]
  let neighborLift : H.neighborFinset v → D := fun w ↦
    ⟨w.1, (H.ne_of_adj ((H.mem_neighborFinset v w.1).mp w.2)).symm⟩
  have hneighborLift : Function.Injective neighborLift := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : D ↦ z.1) hxy
  let neighborImage : H.neighborFinset v → V := fD ∘ neighborLift
  have hneighborImage : Function.Injective neighborImage :=
    hfD.comp hneighborLift
  let U : Finset V := Finset.univ.image neighborImage
  have hUcard : U.card = H.degree v := by
    calc
      U.card = (Finset.univ : Finset (↑(H.neighborFinset v))).card := by
        change (Finset.univ.image neighborImage).card = _
        rw [Finset.card_image_of_injective _ hneighborImage]
      _ = (H.neighborFinset v).card := by simp
      _ = H.degree v := rfl
  have hUne : U.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hU
    have : U.card = 0 := by simp [hU]
    omega
  obtain ⟨u, huU, huMax⟩ := U.exists_max_image (fun y ↦ C.degree y) hUne
  refine ⟨u, ?_⟩
  rw [← hspare, ← hUcard]
  let covered : Finset V := U.biUnion fun y ↦ C.neighborFinset y
  have hcover : spare ⊆ covered := by
    intro x hxSpare
    have hxNotOccupied : x ∉ occupied := (Finset.mem_sdiff.mp hxSpare).2
    by_contra hxCovered
    have hredFree : ∀ y ∈ U, ¬ C.Adj x y := by
      intro y hyU hxy
      apply hxCovered
      change x ∈ U.biUnion fun y ↦ C.neighborFinset y
      rw [Finset.mem_biUnion]
      exact ⟨y, hyU, (C.mem_neighborFinset y x).mpr hxy.symm⟩
    have hblueNeighbor (w : H.neighborFinset v) :
        Cᶜ.Adj x (neighborImage w) := by
      rw [SimpleGraph.compl_adj]
      have hwU : neighborImage w ∈ U := by
        change neighborImage w ∈ Finset.univ.image neighborImage
        rw [Finset.mem_image]
        exact ⟨w, Finset.mem_univ _, rfl⟩
      refine ⟨?_, hredFree _ hwU⟩
      intro hxw
      apply hxNotOccupied
      change x ∈ Finset.univ.image fD
      rw [Finset.mem_image]
      exact ⟨neighborLift w, Finset.mem_univ _, hxw.symm⟩
    let f : W → V := fun w ↦
      if hw : w = v then x else fD ⟨w, hw⟩
    have hf : Function.Injective f := by
      intro a b hab
      by_cases ha : a = v <;> by_cases hb : b = v
      · exact ha.trans hb.symm
      · dsimp only [f] at hab
        rw [dif_pos ha, dif_neg hb] at hab
        exfalso
        apply hxNotOccupied
        change x ∈ Finset.univ.image fD
        rw [Finset.mem_image]
        exact ⟨⟨b, hb⟩, Finset.mem_univ _, hab.symm⟩
      · dsimp only [f] at hab
        rw [dif_neg ha, dif_pos hb] at hab
        exfalso
        apply hxNotOccupied
        change x ∈ Finset.univ.image fD
        rw [Finset.mem_image]
        exact ⟨⟨a, ha⟩, Finset.mem_univ _, hab⟩
      · dsimp only [f] at hab
        rw [dif_neg ha, dif_neg hb] at hab
        exact congrArg Subtype.val (hfD hab)
    let hom : H →g Cᶜ :=
      { toFun := f
        map_rel' := by
          intro a b hab
          by_cases ha : a = v <;> by_cases hb : b = v
          · subst a
            subst b
            exact (hab.ne rfl).elim
          · subst a
            dsimp only [f]
            rw [dif_pos rfl, dif_neg hb]
            let w : H.neighborFinset v :=
              ⟨b, (H.mem_neighborFinset v b).mpr hab⟩
            exact hblueNeighbor w
          · subst b
            dsimp only [f]
            rw [dif_neg ha, dif_pos rfl]
            let w : H.neighborFinset v :=
              ⟨a, (H.mem_neighborFinset v a).mpr hab.symm⟩
            exact (hblueNeighbor w).symm
          · dsimp only [f]
            rw [dif_neg ha, dif_neg hb]
            apply copy.toHom.map_adj
            exact hab }
    exact hno ⟨hom.toCopy hf⟩
  calc
    spare.card ≤ covered.card := Finset.card_le_card hcover
    _ ≤ ∑ y ∈ U, (C.neighborFinset y).card := Finset.card_biUnion_le
    _ = ∑ y ∈ U, C.degree y := by simp
    _ ≤ ∑ _y ∈ U, C.degree u := by
      exact Finset.sum_le_sum fun y hy ↦ huMax y hy
    _ = U.card * C.degree u := by simp

/-- Coded Ramsey specialization: an inductively forced copy of the supported
one-vertex deletion supplies the deletion copy required above. -/
theorem exists_large_degree_of_ramseyAt_supported_delete
    {F H : GraphCode} {N : ℕ} (C : SimpleGraph (Fin N))
    [DecidableRel C.Adj] (v : Fin H.vertexCount)
    [DecidableRel H.graph.Adj] (hdeg : 0 < H.graph.degree v)
    (hroom : H.vertexCount - 1 ≤ N)
    (hRamsey : RamseyAt F (supportCode (deleteVertexCode H v)) N)
    (hnoF : ¬ F.graph ⊑ C) (hnoH : ¬ H.graph ⊑ Cᶜ) :
    ∃ u : Fin N,
      N - (H.vertexCount - 1) ≤ H.graph.degree v * C.degree u := by
  rcases hRamsey C with hF | hcore
  · exact (hnoF hF).elim
  · let intoUniv : SimpleGraph.Copy Cᶜ
        (Cᶜ.induce ((Finset.univ : Finset (Fin N)) : Set (Fin N))) :=
      { toHom :=
          { toFun := fun x ↦ ⟨x, by simp⟩
            map_rel' := by
              intro x y hxy
              exact hxy }
        injective' := by
          intro x y hxy
          exact congrArg Subtype.val hxy }
    have hcore' : (supportCode (deleteVertexCode H v)).graph ⊑
        Cᶜ.induce ((Finset.univ : Finset (Fin N)) : Set (Fin N)) :=
      hcore.trans ⟨intoUniv⟩
    have hdeleteRegion : (deleteVertexCode H v).graph ⊑
        Cᶜ.induce ((Finset.univ : Finset (Fin N)) : Set (Fin N)) :=
      isContained_induce_of_supportCode_isContained
        (H := deleteVertexCode H v) Cᶜ Finset.univ hcore' (by
          simpa only [deleteVertexCode_vertexCount, Finset.card_univ,
            Fintype.card_fin] using hroom)
    have hdeleteCode : (deleteVertexCode H v).graph ⊑ Cᶜ :=
      hdeleteRegion.trans
        (SimpleGraph.Embedding.induce
          ((Finset.univ : Finset (Fin N)) : Set (Fin N))).isContained
    have hdelete : H.graph.induce ({v} : Set (Fin H.vertexCount))ᶜ ⊑ Cᶜ :=
      deleteVertexGraph_isContained_of_code_isContained v hdeleteCode
    simpa using
      exists_large_degree_of_delete_vertex_copy H.graph C v hdeg hdelete hnoH

end Erdos570
