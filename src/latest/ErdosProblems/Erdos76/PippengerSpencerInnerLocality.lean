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
import ErdosProblems.Erdos76.PippengerSpencerInner

/-!
# Locality of the fixed-length inner matching generator

This small downstream file packages the radius invariant proved for
`innerState` as an `EventDependsOn` statement on flattened Bernoulli
coordinates.
-/

open Finset

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

namespace FiniteHypergraph

variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Pointwise form of locality for the fixed-length inner acceptance event. -/
lemma innerAcceptedEvent_iff_of_agreesOn
    (H : FiniteHypergraph V E) (L : ℕ) (e : E)
    {Z T : Finset (Fin L × E)}
    (hZT : FiniteNibble.AgreesOn (H.innerEdgeInfluenceSupport L e) Z T) :
    H.innerAcceptedEvent L e Z ↔ H.innerAcceptedEvent L e T := by
  change e ∈ H.innerState (fun i ↦ batchAt Z i) L ↔
    e ∈ H.innerState (fun i ↦ batchAt T i) L
  apply H.innerState_mem_iff_of_sample_agreement
    (X := fun i ↦ batchAt Z i) (Y := fun i ↦ batchAt T i)
    (e := e) (le_refl L)
  intro i f hf
  simp only [mem_batchAt]
  have hif : (i, f) ∈ H.innerEdgeInfluenceSupport L e :=
    (H.mem_innerEdgeInfluenceSupport L e (i, f)).2 hf
  unfold FiniteNibble.AgreesOn at hZT
  have hmem := congrArg
    (fun S : Finset (Fin L × E) ↦ (i, f) ∈ S) hZT
  have hmem' : ((i, f) ∈ Z) = ((i, f) ∈ T) := by
    simpa only [mem_inter, hif, and_true] using hmem
  exact eq_iff_iff.mp hmem'

/-- Fixed-length inner acceptance depends only on its explicit
radius-`2L+1` coordinate support. -/
lemma innerAcceptedEvent_eventDependsOn
    (H : FiniteHypergraph V E) (L : ℕ) (e : E) :
    FiniteNibble.EventDependsOn (H.innerEdgeInfluenceSupport L e)
      (fun Z : Finset (Fin L × E) ↦ H.innerAcceptedEvent L e Z) := by
  intro Z T hZT
  exact H.innerAcceptedEvent_iff_of_agreesOn L e hZT

/-- A dependency neighbourhood containing every edge whose inner influence
support can overlap that of `e`. -/
def innerEdgeDependency (H : FiniteHypergraph V E) (L : ℕ) (e : E) :
    Finset E :=
  (H.conflictBall (4 * L + 2) e).erase e

@[simp] lemma mem_innerEdgeDependency
    (H : FiniteHypergraph V E) (L : ℕ) (e f : E) :
    f ∈ H.innerEdgeDependency L e ↔
      f ≠ e ∧ f ∈ H.conflictBall (4 * L + 2) e := by
  simp [innerEdgeDependency]

/-- The inner dependency neighbourhood contains every overlap of explicit
coordinate supports. -/
lemma innerEdgeInfluence_contains_overlaps
    (H : FiniteHypergraph V E) (L : ℕ) :
    FiniteNibble.ContainsSupportOverlaps
      (H.innerEdgeInfluenceSupport L) (H.innerEdgeDependency L) := by
  intro e f hef hoverlap
  obtain ⟨z, hze, hzf⟩ := not_disjoint_iff.mp hoverlap
  have hge : z.2 ∈ H.conflictBall (2 * L + 1) e :=
    (H.mem_innerEdgeInfluenceSupport L e z).mp hze
  have hgf : z.2 ∈ H.conflictBall (2 * L + 1) f :=
    (H.mem_innerEdgeInfluenceSupport L f z).mp hzf
  have hfg : f ∈ H.conflictBall (2 * L + 1) z.2 :=
    (H.mem_conflictBall_comm (2 * L + 1) f z.2).mp hgf
  have hball : f ∈
      H.conflictBall ((2 * L + 1) + (2 * L + 1)) e :=
    H.conflictBall_comp hge (2 * L + 1) hfg
  rw [H.mem_innerEdgeDependency]
  refine ⟨hef.symm, ?_⟩
  have harith : (2 * L + 1) + (2 * L + 1) = 4 * L + 2 := by omega
  rwa [← harith]

lemma innerEdgeDependency_card_le
    {H : FiniteHypergraph V E} {k D L : ℕ}
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) (e : E) :
    (H.innerEdgeDependency L e).card ≤ (k * D + 1) ^ (4 * L + 2) := by
  calc
    (H.innerEdgeDependency L e).card ≤
        (H.conflictBall (4 * L + 2) e).card := card_erase_le
    _ ≤ (k * D + 1) ^ (4 * L + 2) :=
      H.conflictBall_card_le hunif hdeg (4 * L + 2) e

end FiniteHypergraph

end


end Erdos76
