/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InternalEdgeIntermediateState
import ErdosProblems.Erdos207.InternalEdgeScheduledStarBound

/-!
# Localized link loss after the internal stage

The preliminary family covers only outside--outside pairs.  Consequently it
does not remove any neighbor in the next vortex set from an outside center.
The only such losses come from genuinely new internal-stage triangles, and
their number is bounded by the scheduled-edge incidence at the center.
-/

namespace Erdos207

open Finset

noncomputable section

/-- A scheduled internal triangle has a unique vertex in `U`: its scheduled
edge has both endpoints outside `U`, while its third vertex lies in `U`. -/
lemma newScheduledTriangle_inner_vertex_unique
    {V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} {E : Finset (Sym2 V)}
    {P0 Q : TripleSystemOn V}
    (houter : ∀ e ∈ E, e.out.1 ∉ U ∧ e.out.2 ∉ U)
    (huse : NewTrianglesUseScheduledOuterEdges U E P0 Q)
    {T : TripleOn V} (hT : T ∈ Q \ P0)
    {x y : V} (hxT : x ∈ T.1) (hxU : x ∈ U)
    (hyT : y ∈ T.1) (hyU : y ∈ U) : x = y := by
  obtain ⟨e, heE, hne, w, hwU, rfl⟩ := huse T hT
  have heOuter := houter e heE
  simp only [internalEdgeTriangle, thirdVertexTriple, tripleOfThree,
    mem_insert, mem_singleton] at hxT hyT
  rcases hxT with rfl | rfl | rfl
  · exact (heOuter.1 hxU).elim
  · exact (heOuter.2 hxU).elim
  · rcases hyT with rfl | rfl | rfl
    · exact (heOuter.1 hyU).elim
    · exact (heOuter.2 hyU).elim
    · rfl

/-- The neighbors in `U` covered by the stage family at an outside center
inject into the new internal triangles through that center. -/
theorem card_coveredNeighborsIn_internalStageFamily_le_newStar
    {V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} {E : Finset (Sym2 V)}
    {I D Mstar P0 Q : TripleSystemOn V}
    (hP0 : P0 = I ∪ (D ∪ Mstar))
    (hstarDisjoint : ∀ T ∈ Mstar, Disjoint T.1 U)
    (hP0Q : P0 ⊆ Q)
    (hpacking : IsPackingOn Q)
    (houter : ∀ e ∈ E, e.out.1 ∉ U ∧ e.out.2 ∉ U)
    (huse : NewTrianglesUseScheduledOuterEdges U E P0 Q)
    {v : V} (hv : v ∉ U) :
    ((coveredGraph (internalStageFamily I D Mstar Q)).neighborFinset v ∩ U).card ≤
      (triplesThrough (Q \ P0) v).card := by
  classical
  let S : Finset V :=
    (coveredGraph (internalStageFamily I D Mstar Q)).neighborFinset v ∩ U
  have hwitness : ∀ y ∈ S,
      ∃ T : TripleOn V, T ∈ Q \ P0 ∧ v ∈ T.1 ∧ y ∈ T.1 := by
    intro y hy
    have hyData := mem_inter.mp hy
    have hvy : (coveredGraph (internalStageFamily I D Mstar Q)).Adj v y := by
      simpa only [SimpleGraph.mem_neighborFinset] using hyData.1
    obtain ⟨T, hTR, hvT, hyT, _hvy⟩ := coveredGraph_adj.mp hvy
    have hnotStar : T ∉ Mstar := by
      intro hTstar
      exact Finset.disjoint_left.mp (hstarDisjoint T hTstar) hyT hyData.2
    have hTnew : T ∈ Q \ P0 := by
      have hTR' : T ∈ Mstar ∪ (Q \ (I ∪ (D ∪ Mstar))) := by
        simpa only [internalStageFamily] using hTR
      have hdiff := (mem_union.mp hTR').resolve_left hnotStar
      simpa only [hP0] using hdiff
    exact ⟨T, hTnew, hvT, hyT⟩
  let f : {y // y ∈ S} → {T // T ∈ triplesThrough (Q \ P0) v} :=
    fun y ↦ ⟨Classical.choose (hwitness y.1 y.2), by
      have hs := Classical.choose_spec (hwitness y.1 y.2)
      exact mem_filter.mpr ⟨hs.1, hs.2.1⟩⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hx := Classical.choose_spec (hwitness x.1 x.2)
    have hy := Classical.choose_spec (hwitness y.1 y.2)
    have hT : Classical.choose (hwitness x.1 x.2) =
        Classical.choose (hwitness y.1 y.2) := congrArg Subtype.val hxy
    have hyIn : y.1 ∈ (Classical.choose (hwitness x.1 x.2)).1 := by
      rw [hT]
      exact hy.2.2
    have hxU : x.1 ∈ U := by
      exact (mem_inter.mp (by simpa only [S] using x.2)).2
    have hyU : y.1 ∈ U := by
      exact (mem_inter.mp (by simpa only [S] using y.2)).2
    exact newScheduledTriangle_inner_vertex_unique houter huse hx.1
      hx.2.2 hxU hyIn hyU
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, S] using hcard

/-- A uniform scheduled-incidence cap is therefore the exact localized loss
budget used by residual-link typicality. -/
theorem card_coveredNeighborsIn_internalStageFamily_le_scheduledIncidence
    {V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} {E : Finset (Sym2 V)}
    {I D Mstar P0 Q : TripleSystemOn V} {d : ℕ}
    (hP0 : P0 = I ∪ (D ∪ Mstar))
    (hstarDisjoint : ∀ T ∈ Mstar, Disjoint T.1 U)
    (hP0Q : P0 ⊆ Q)
    (hpacking : IsPackingOn Q)
    (houter : ∀ e ∈ E, e.out.1 ∉ U ∧ e.out.2 ∉ U)
    (huse : NewTrianglesUseScheduledOuterEdges U E P0 Q)
    (hincidence : ∀ v : V, (scheduledEdgesAt E v).card ≤ d)
    {v : V} (hv : v ∉ U) :
    ((coveredGraph (internalStageFamily I D Mstar Q)).neighborFinset v ∩ U).card ≤ d := by
  exact (card_coveredNeighborsIn_internalStageFamily_le_newStar hP0
    hstarDisjoint hP0Q hpacking houter huse hv).trans
      ((card_triplesThrough_sdiff_le_scheduledEdgesAt hpacking houter huse hv).trans
        (hincidence v))

/-- The genuinely new internal difference has the same localized incidence
bound, without any hypothesis on the geometry of an earlier preliminary
family. -/
theorem card_coveredNeighborsIn_newInternalAdded_le_scheduledIncidence
    {V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} {E : Finset (Sym2 V)}
    {P₀ Q : TripleSystemOn V} {d : ℕ}
    (hP₀Q : P₀ ⊆ Q)
    (hpacking : IsPackingOn Q)
    (houter : ∀ e ∈ E, e.out.1 ∉ U ∧ e.out.2 ∉ U)
    (huse : NewTrianglesUseScheduledOuterEdges U E P₀ Q)
    (hincidence : ∀ v : V, (scheduledEdgesAt E v).card ≤ d)
    {v : V} (hv : v ∉ U) :
    ((coveredGraph (Q \ P₀)).neighborFinset v ∩ U).card ≤ d := by
  have hfamily : internalStageFamily P₀ ∅ ∅ Q = Q \ P₀ := by
    ext T
    simp [internalStageFamily]
  rw [← hfamily]
  exact card_coveredNeighborsIn_internalStageFamily_le_scheduledIncidence
    (I := P₀) (D := ∅) (Mstar := ∅) (P0 := P₀) (Q := Q)
    (U := U) (E := E) (d := d) (by simp) (by simp) hP₀Q hpacking
    houter huse hincidence hv

end

end Erdos207
