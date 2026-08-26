import ErdosProblems.Erdos73.OddPathLiftSequence
import ErdosProblems.Erdos73.FiniteSequencePath
import ErdosProblems.Erdos73.MatchingAugmenting

/-! Every odd terminal path lifts to an augmenting path without new projected vertices. -/

namespace Erdos73

open SimpleGraph Finset Erdos556 OddPathVertex
open Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A : Finset V}

theorem exists_augmentingPath_of_oddTerminalPath {Q : GraphPath G}
    (hQ : IsOddTerminalPath A Q) :
    ∃ P : GraphPath (oddPathAuxiliary G A),
      IsMatchingAugmentingPath (oddPathBaseMatching A) P ∧
        ∀ x ∈ P.vertexSet, projection x ∈ Q.vertexSet := by
  obtain ⟨t, hlen⟩ := hQ.odd_length
  obtain ⟨f, hf, hproj, hlayer, hadj⟩ := exists_oddPathLiftSequence hQ hlen
  let P := GraphPath.ofSequence (n := 4 * t + 1) f hf hadj
  have hsrc : P.source = f 0 := GraphPath.ofSequence_source f hf hadj
  have htgt : P.target = f (Fin.last (4 * t + 1)) := GraphPath.ofSequence_target f hf hadj
  have hsrcproj : projection P.source = Q.source := by
    rw [hsrc, hproj]
    simp only [Fin.val_zero, Nat.zero_add, Nat.reduceDiv, Walk.getVert_zero]
  have htgtproj : projection P.target = Q.target := by
    rw [htgt, hproj]
    have he : ((Fin.last (4 * t + 1)).val + 1) / 2 = Q.walk.length := by
      simp only [Fin.val_last]
      omega
    rw [he, Walk.getVert_length]
  have hedge (i : ℕ) (hi : i < 4 * t + 1) :
      s(f ⟨i, by omega⟩, f ⟨i + 1, by omega⟩) ∈ P.edgeSet :=
    GraphPath.ofSequence_edge f hf hadj i hi
  have hmatch (i : ℕ) (hi : i < 4 * t + 1) (hp : i % 2 = 1) :
      s(f ⟨i, by omega⟩, f ⟨i + 1, by omega⟩) ∈ oddPathBaseMatching A := by
    apply (oddPathAuxiliary_matching_iff_same_projection (hadj i (by omega))).mpr
    rw [hproj, hproj]
    congr 1
    change (i + 1) / 2 = (i + 1 + 1) / 2
    omega
  refine ⟨P, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro he
    rw [hsrc, htgt] at he
    have hi := congrArg Fin.val (hf he)
    simp only [Fin.val_zero, Fin.val_last] at hi
    omega
  · intro hs
    have hn := (mem_oddPathBaseMatching_support A P.source).mp hs
    exact hn (hsrcproj ▸ hQ.source_mem)
  · intro ht
    have hn := (mem_oddPathBaseMatching_support A P.target).mp ht
    exact hn (htgtproj ▸ hQ.target_mem)
  · intro x hx hs ht
    obtain ⟨r, rfl⟩ := (GraphPath.mem_ofSequence_vertexSet f hf hadj x).mp hx
    have hr0 : 0 < r.val := by
      by_contra hn
      have he : r = 0 := Fin.ext (by change r.val = 0; omega)
      exact hs (he ▸ hsrc.symm)
    have hrend : r.val < 4 * t + 1 := by
      have hr := r.isLt
      by_contra hn
      have he : r = Fin.last (4 * t + 1) := Fin.ext (by simpa only [Fin.val_last] using
        (show r.val = 4 * t + 1 by omega))
      exact ht (he ▸ htgt.symm)
    by_cases hp : r.val % 2 = 1
    · refine ⟨f ⟨r.val + 1, by omega⟩, ?_, ?_⟩
      · exact hmatch r.val hrend hp
      · exact hedge r.val hrend
    · have hprev : r.val - 1 < 4 * t + 1 := by omega
      have hprevodd : (r.val - 1) % 2 = 1 := by omega
      have hm := hmatch (r.val - 1) hprev hprevodd
      have he := hedge (r.val - 1) hprev
      have hidx : r.val - 1 + 1 = r.val := by omega
      refine ⟨f ⟨r.val - 1, by omega⟩, ?_, ?_⟩
      · rw [Sym2.eq_swap]
        simpa only [hidx] using hm
      · rw [Sym2.eq_swap]
        simpa only [hidx] using he
  · intro x hx
    obtain ⟨r, rfl⟩ := (GraphPath.mem_ofSequence_vertexSet f hf hadj x).mp hx
    rw [hproj]
    exact List.mem_toFinset.mpr (Q.walk.getVert_mem_support _)

end Erdos73
