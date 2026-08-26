/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos76.PentagonTransversal

/-!
# Extending a pentagon blow-up by one vertex

This is the graph-level form of Proposition 7.10's zero-bad-configuration
case.  The old graph is a pentagon blow-up on `Fin n`, the new graph is an
initial extension on `Fin (n+1)`, and all five old fibres are nonempty.  If
every old transversal has a bad-free adjacency pattern to the last vertex,
the finite rigidity theorem supplies one label for that vertex and the
enlarged graph is again a pentagon blow-up.
-/

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Extend a five-valued labelling across the final vertex. -/
def extendPentagonBlob {n : ℕ} (blob : Fin n → Fin 5) (s : Fin 5) :
    Fin (n + 1) → Fin 5 :=
  Fin.lastCases s blob

@[simp] theorem extendPentagonBlob_last {n : ℕ}
    (blob : Fin n → Fin 5) (s : Fin 5) :
    extendPentagonBlob blob s (Fin.last n) = s := by
  simp [extendPentagonBlob]

@[simp] theorem extendPentagonBlob_castSucc {n : ℕ}
    (blob : Fin n → Fin 5) (s : Fin 5) (i : Fin n) :
    extendPentagonBlob blob s i.castSucc = blob i := by
  simp [extendPentagonBlob]

/-- A choice of one old vertex carrying each of the five blob labels. -/
def PentagonOldTransversal {n : ℕ} (blob : Fin n → Fin 5) : Type :=
  ∀ i : Fin 5, {x : Fin n // blob x = i}

/-- If no old transversal forms a bad configuration with the last vertex,
the initial extension is itself a pentagon blow-up. -/
theorem isPentagonBlowup_of_no_badPatterns
    {n : ℕ} {H : SimpleGraph (Fin n)}
    {G : SimpleGraph (Fin (n + 1))} {blob : Fin n → Fin 5}
    (hHG : IsInitialVertexExtension H G)
    (hH : IsPentagonBlowup H blob)
    (hnobad : ∀ v : PentagonOldTransversal blob,
      pentagonBadPattern
        (pentagonAdjacencyPattern G (Fin.last n)
          (fun i ↦ (v i).1.castSucc)) = false) :
    ∃ blob' : Fin (n + 1) → Fin 5,
      IsPentagonBlowup G blob' := by
  let β : Fin 5 → Type := fun i ↦ {x : Fin n // blob x = i}
  letI : ∀ i, Nonempty (β i) := fun i ↦ by
    obtain ⟨x, hx⟩ := hH.1 i
    exact ⟨⟨x, hx⟩⟩
  have hnew := no_badPatterns_indexed_extend_one_blob
    (β := β) (G := G) (u := Fin.last n)
    (fun _ x ↦ x.1.castSucc) hnobad
  obtain ⟨s, hs⟩ := hnew
  refine ⟨extendPentagonBlob blob s, ?_⟩
  constructor
  · intro j
    obtain ⟨x, hx⟩ := hH.1 j
    exact ⟨x.castSucc, by simp [hx]⟩
  · intro a b hab
    induction a using Fin.lastCases with
    | last =>
        induction b using Fin.lastCases with
        | last => exact (hab rfl).elim
        | cast b =>
            have hbs : blob b ≠ s := by
              simpa [ne_comm] using hab
            simpa using hs (blob b) hbs (⟨b, rfl⟩ : β (blob b))
    | cast a =>
        induction b using Fin.lastCases with
        | last =>
            have has : blob a ≠ s := by
              simpa using hab
            rw [G.adj_comm, (SimpleGraph.cycleGraph 5).adj_comm]
            simpa using hs (blob a) has (⟨a, rfl⟩ : β (blob a))
        | cast b =>
            have hablob : blob a ≠ blob b := by
              simpa using hab
            rw [← hHG a b]
            simpa [extendPentagonBlob] using hH.2 hablob

/-- Graph-level form of the Section 7 pattern dichotomy.  When one vertex is
adjoined to a pentagon blow-up, either all old transversals are compatible
with one common blob label for the new vertex, or one transversal supplies
an actual two-element monochromatic packing through that vertex. -/
theorem pentagonBlowup_initialExtension_dichotomy
    {n : ℕ} {H : SimpleGraph (Fin n)}
    {G : SimpleGraph (Fin (n + 1))} {blob : Fin n → Fin 5}
    (hHG : IsInitialVertexExtension H G)
    (hH : IsPentagonBlowup H blob) :
    (∃ blob' : Fin (n + 1) → Fin 5, IsPentagonBlowup G blob') ∨
      ∃ v : PentagonOldTransversal blob,
        pentagonBadPattern
          (pentagonAdjacencyPattern G (Fin.last n)
            (fun i ↦ (v i).1.castSucc)) = true ∧
        ∃ P : Finset (Finset (Fin (n + 1))),
          IsMonochromaticPacking G P ∧ P.card = 2 ∧
            ∀ t ∈ P, Fin.last n ∈ t := by
  classical
  by_cases hnobad : ∀ v : PentagonOldTransversal blob,
      pentagonBadPattern
        (pentagonAdjacencyPattern G (Fin.last n)
          (fun i ↦ (v i).1.castSucc)) = false
  · exact Or.inl (isPentagonBlowup_of_no_badPatterns hHG hH hnobad)
  · right
    obtain ⟨v, hv⟩ := not_forall.mp hnobad
    have hvbad : pentagonBadPattern
        (pentagonAdjacencyPattern G (Fin.last n)
          (fun i ↦ (v i).1.castSucc)) = true := by
      cases hpat : pentagonBadPattern
          (pentagonAdjacencyPattern G (Fin.last n)
            (fun i ↦ (v i).1.castSucc)) <;> simp_all
    have hvInjective : Function.Injective
        (fun i ↦ (v i).1.castSucc) := by
      intro i j hij
      have hijOld : (v i).1 = (v j).1 :=
        Fin.castSucc_injective n hij
      calc
        i = blob (v i).1 := (v i).2.symm
        _ = blob (v j).1 := congrArg blob hijOld
        _ = j := (v j).2
    have hlast : ∀ i, Fin.last n ≠ (v i).1.castSucc := by
      intro i hi
      exact Fin.castSucc_ne_last (v i).1 hi.symm
    have hcross : ∀ i j, i ≠ j →
        (G.Adj (v i).1.castSucc (v j).1.castSucc ↔
          (SimpleGraph.cycleGraph 5).Adj i j) := by
      intro i j hij
      rw [← hHG]
      have hlabels : blob (v i).1 ≠ blob (v j).1 := by
        simpa only [(v i).2, (v j).2] using hij
      simpa only [(v i).2, (v j).2] using hH.2 hlabels
    obtain ⟨P, hP, hcard, hthrough⟩ :=
      badPattern_exists_two_monochromaticPacking
        hvInjective hlast hcross hvbad
    exact ⟨v, hvbad, P, hP, hcard, hthrough⟩

end

end Erdos76
