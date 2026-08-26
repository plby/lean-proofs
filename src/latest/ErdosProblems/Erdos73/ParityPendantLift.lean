import ErdosProblems.Erdos73.ParityPendantAttachment
import ErdosProblems.Erdos73.ParityColoring
import ErdosProblems.Erdos73.OddTerminalSegments

/-! Lift parity-breaking paths by attaching their colour-one endpoint leaves. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {T : Finset V} {c : V → Bool}

theorem exists_oddPendantPath_of_parityBreakingPath (P : GraphPath G)
    (hP : IsParityBreakingPath c T P) :
    ∃ D : GraphPath (parityPendantGraph G T c),
      IsOddTerminalPath (parityPendantTerminals T c) D ∧
      D.vertexSet.image pendantProjection ⊆ P.vertexSet := by
  let B := P.mapCopy (parityPendantCopy G T c)
  have hnoLeaf (v : V) : Sum.inr v ∉ B.vertexSet := by
    intro hv
    obtain ⟨w, _, hw⟩ := (P.mem_mapCopy_vertexSet _ _).mp hv
    exact Sum.inl_ne_inr hw
  have hBimage : B.vertexSet.image pendantProjection ⊆ P.vertexSet := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hv
    obtain ⟨w, hw, rfl⟩ := (P.mem_mapCopy_vertexSet _ x).mp hx
    exact hw
  obtain ⟨Q, hQs, hQt, hQlen, hQsub, hQimage⟩ :=
    attach_pendant_source B P.source hP.source_mem rfl (hnoLeaf P.source)
  have hQfresh : Sum.inr P.target ∉ Q.reverse.vertexSet := by
    intro hv
    have hvQ : Sum.inr P.target ∈ Q.vertexSet := by simpa only [GraphPath.reverse_vertexSet] using hv
    rcases mem_union.mp (hQsub hvQ) with hvB | he
    · exact hnoLeaf P.target hvB
    · have heq : P.target = P.source := Sum.inr.inj (mem_singleton.mp he)
      exact hP.breaking.source_ne_target heq.symm
  have hQtarget : Q.reverse.source = Sum.inl P.target := hQt
  obtain ⟨L, hLs, hLt, hLlen, _, hLimage⟩ :=
    attach_pendant_source Q.reverse P.target hP.target_mem hQtarget hQfresh
  let R := L.reverse
  have hRs : R.source = pendantTerminal c P.source := hLt.trans hQs
  have hRt : R.target = pendantTerminal c P.target := hLs
  have hRlen : R.walk.length = P.walk.length + (c P.source).toNat + (c P.target).toNat := by
    have hBlen : B.walk.length = P.walk.length := by
      simp only [B, GraphPath.mapCopy, Walk.length_map]
    simpa only [R, GraphPath.reverse, Walk.length_reverse, hQlen, hBlen] using hLlen
  have hRimage : R.vertexSet.image pendantProjection ⊆ P.vertexSet := by
    have hh : Q.reverse.vertexSet.image pendantProjection ⊆ B.vertexSet.image pendantProjection := by
      simpa only [GraphPath.reverse_vertexSet] using hQimage
    simpa only [R, GraphPath.reverse_vertexSet] using hLimage.trans (hh.trans hBimage)
  have hsT : R.source ∈ parityPendantTerminals T c :=
    hRs ▸ mem_image.mpr ⟨P.source, hP.source_mem, rfl⟩
  have htT : R.target ∈ parityPendantTerminals T c :=
    hRt ▸ mem_image.mpr ⟨P.target, hP.target_mem, rfl⟩
  have ho : Odd R.walk.length := by rw [hRlen]; exact hP.breaking
  obtain ⟨D, hD, hDR⟩ := exists_oddTerminalSegment (parityPendantTerminals T c) R hsT htT ho
  exact ⟨D, hD, (image_subset_image hDR).trans hRimage⟩

end
end Erdos73
