import ErdosProblems.Erdos73.ParityPendantTrimming
import ErdosProblems.Erdos73.ParityPendantProjection

/-! Odd paths between pendant terminals project to parity-breaking terminal paths. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {T : Finset V} {c : V → Bool}

theorem exists_parityBreaking_path_of_oddPendantPath
    (P : GraphPath (parityPendantGraph G T c))
    (hP : IsOddTerminalPath (parityPendantTerminals T c) P) :
    ∃ B : GraphPath G, IsParityBreakingPath c T B ∧
      B.vertexSet ⊆ P.vertexSet.image pendantProjection := by
  have hnil : ¬ P.walk.Nil := by
    intro hn
    have hz := hn.length_eq_zero
    have ho := hP.odd_length
    rw [Nat.odd_iff, hz] at ho
    contradiction
  obtain ⟨Q, hQs, hQt, hQsub, hQlen⟩ := trim_pendant_source P hP.source_mem (fun _ _ => hnil)
  have hQtmem : Q.reverse.source ∈ parityPendantTerminals T c := by
    simpa only [GraphPath.reverse_source, hQt] using hP.target_mem
  have hQnon : ∀ v, Q.reverse.source = Sum.inr v → ¬ Q.reverse.walk.Nil := by
    intro v hv hn
    have he : Sum.inr v = Sum.inl (pendantProjection P.source) :=
      hv.symm.trans (hn.eq.trans hQs)
    exact Sum.inr_ne_inl he
  obtain ⟨L, hLs, hLt, hLsub, hLlen⟩ := trim_pendant_source Q.reverse hQtmem hQnon
  let R := L.reverse
  have hRs : R.source = Sum.inl (pendantProjection P.source) := hLt.trans hQs
  have hRt : R.target = Sum.inl (pendantProjection P.target) :=
    hLs.trans (congrArg (fun v => Sum.inl (pendantProjection v)) hQt)
  have hRsub : R.vertexSet ⊆ P.vertexSet := by
    simpa only [R, GraphPath.reverse_vertexSet] using hLsub.trans
      (show Q.reverse.vertexSet ⊆ P.vertexSet from (by simpa using hQsub))
  have hRorig : ∀ x ∈ R.vertexSet, x = Sum.inl (pendantProjection x) := by
    intro x hx
    cases x with
    | inl v => rfl
    | inr v =>
      rcases parityPendant_leaf_endpoint R hx with he | he
      · exact (Sum.inr_ne_inl (he.trans hRs)).elim
      · exact (Sum.inr_ne_inl (he.trans hRt)).elim
  obtain ⟨B, hBs, hBt, hBlen, hBsub⟩ := project_original_pendant_path R hRorig
  have hlength : B.walk.length + (c (pendantProjection P.source)).toNat +
      (c (pendantProjection P.target)).toNat = P.walk.length := by
    have hLlen' : L.walk.length + (c (pendantProjection P.target)).toNat = Q.walk.length := by
      simpa only [GraphPath.reverse_source, GraphPath.reverse, Walk.length_reverse, hQt] using hLlen
    have hBR : B.walk.length = L.walk.length := by
      simpa only [R, GraphPath.reverse, Walk.length_reverse] using hBlen
    omega
  have hBs' : B.source = pendantProjection P.source := by
    simpa only [hRs, pendantProjection, Sum.elim_inl, id_eq] using hBs
  have hBt' : B.target = pendantProjection P.target := by
    simpa only [hRt, pendantProjection, Sum.elim_inl, id_eq] using hBt
  have hbreak : ParityBreaking c B := by
    change Odd (B.walk.length + (c B.source).toNat + (c B.target).toNat)
    simpa only [hBs', hBt', hlength] using hP.odd_length
  have hsT := ((mem_parityPendantTerminals T c P.source).mp hP.source_mem).1
  have htT := ((mem_parityPendantTerminals T c P.target).mp hP.target_mem).1
  obtain ⟨D, hD, hDsub⟩ := exists_parityBreaking_segment c T B
    (hBs' ▸ hsT) (hBt' ▸ htT) hbreak
  exact ⟨D, hD, hDsub.trans (hBsub.trans (image_subset_image hRsub))⟩

end
end Erdos73
