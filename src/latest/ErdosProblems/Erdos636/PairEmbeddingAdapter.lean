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
import ErdosProblems.Erdos636.Pairing
import ErdosProblems.Erdos636.External.Erdos88.Fourier

/-!
# From unordered matchings to Fourier pair embeddings

The matching lemma used for Erdős problem 636 naturally returns a finite set
of unordered pairs.  The slice Fourier argument instead takes an embedding of
an indexed family of oriented pairs.  This file supplies the lossless adapter:
the index type is the subtype of edges belonging to the matching, and
`Sym2.out` gives each edge an arbitrary but fixed orientation.
-/

open Finset Set

namespace Erdos636.PairEmbeddingAdapter

open Erdos88.Fourier

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {I : Type u} [Fintype I] [DecidableEq I]

/-- The canonical finite index type attached to a finite set of unordered
pairs. -/
abbrev MatchingIndex (M : Finset (Sym2 I)) := {e : Sym2 I // e ∈ M}

/-- The endpoint selected by a Boolean orientation bit. -/
def matchingEndpoint (e : Sym2 I) (b : Bool) : I :=
  if b then e.out.2 else e.out.1

@[simp] lemma matchingEndpoint_false (e : Sym2 I) :
    matchingEndpoint e false = e.out.1 := rfl

@[simp] lemma matchingEndpoint_true (e : Sym2 I) :
    matchingEndpoint e true = e.out.2 := rfl

lemma matchingEndpoint_mem (e : Sym2 I) (b : Bool) :
    matchingEndpoint e b ∈ (e : Set I) := by
  cases b
  · exact Sym2.out_fst_mem e
  · exact Sym2.out_snd_mem e

private lemma out_fst_ne_out_snd_of_not_isDiag (e : Sym2 I)
    (he : ¬ e.IsDiag) : e.out.1 ≠ e.out.2 := by
  intro hout
  apply he
  have hrepr : s(e.out.1, e.out.2) = e := by
    rw [Sym2.mk, e.out_eq]
  rw [← hrepr, Sym2.mk_isDiag_iff]
  exact hout

/-- Pairwise-disjoint, non-diagonal unordered pairs form a Fourier
`PairEmbedding`.  No edge is discarded, so the resulting index type has
exactly `M.card` elements. -/
noncomputable def pairEmbeddingOfDisjointPairs
    (M : Finset (Sym2 I))
    (hpair : (M : Set (Sym2 I)).Pairwise fun e f ↦
      Disjoint (e : Set I) (f : Set I))
    (hnondiag : ∀ e ∈ M, ¬ e.IsDiag) :
    PairEmbedding (MatchingIndex M) I where
  toFun z := matchingEndpoint z.1.1 z.2
  inj' := by
    rintro ⟨⟨e, heM⟩, b⟩ ⟨⟨f, hfM⟩, c⟩ heq
    change matchingEndpoint e b = matchingEndpoint f c at heq
    have hef : e = f := by
      by_contra hne
      have hd := hpair heM hfM hne
      apply Set.disjoint_left.mp hd (matchingEndpoint_mem e b)
      rw [heq]
      exact matchingEndpoint_mem f c
    subst f
    have hends : e.out.1 ≠ e.out.2 :=
      out_fst_ne_out_snd_of_not_isDiag e (hnondiag e heM)
    cases b <;> cases c <;> simp_all

@[simp] lemma pairEmbeddingOfDisjointPairs_apply
    (M : Finset (Sym2 I))
    (hpair : (M : Set (Sym2 I)).Pairwise fun e f ↦
      Disjoint (e : Set I) (f : Set I))
    (hnondiag : ∀ e ∈ M, ¬ e.IsDiag)
    (k : MatchingIndex M) (b : Bool) :
    pairEmbeddingOfDisjointPairs M hpair hnondiag (k, b) =
      matchingEndpoint k.1 b := rfl

@[simp] lemma card_matchingIndex (M : Finset (Sym2 I)) :
    Fintype.card (MatchingIndex M) = M.card := by
  exact Fintype.card_coe M

/-- Specialization of `pairEmbeddingOfDisjointPairs` to an `EdgeMatching`.
Membership in a simple graph's edge finset supplies non-diagonality. -/
noncomputable def pairEmbeddingOfEdgeMatching
    (G : SimpleGraph I) [DecidableRel G.Adj]
    (M : Finset (Sym2 I)) (hM : Pairing.EdgeMatching G M) :
    PairEmbedding (MatchingIndex M) I :=
  pairEmbeddingOfDisjointPairs M hM.2 fun e he ↦
    G.not_isDiag_of_mem_edgeFinset (hM.1 he)

@[simp] lemma pairEmbeddingOfEdgeMatching_apply
    (G : SimpleGraph I) [DecidableRel G.Adj]
    (M : Finset (Sym2 I)) (hM : Pairing.EdgeMatching G M)
    (k : MatchingIndex M) (b : Bool) :
    pairEmbeddingOfEdgeMatching G M hM (k, b) =
      matchingEndpoint k.1 b := rfl

/-- Any endpoint-wise property of the unordered matching transports to the
two endpoints of its Fourier pair embedding. -/
theorem endpoint_property_of_edgeMatching
    (G : SimpleGraph I) [DecidableRel G.Adj]
    (M : Finset (Sym2 I)) (hM : Pairing.EdgeMatching G M)
    (P : I → I → Prop)
    (hP : ∀ e ∈ M, ∀ i ∈ (e : Set I), ∀ j ∈ (e : Set I), i ≠ j → P i j) :
    ∀ k : MatchingIndex M,
      P (pairEmbeddingOfEdgeMatching G M hM (k, false))
        (pairEmbeddingOfEdgeMatching G M hM (k, true)) := by
  intro k
  apply hP k.1 k.2
  · exact matchingEndpoint_mem k.1 false
  · exact matchingEndpoint_mem k.1 true
  · exact (pairEmbeddingOfEdgeMatching G M hM).injective.ne (by simp)

/-- In particular, lower and upper bounds for the absolute coefficient gap
on every unordered matching edge hold on every oriented Fourier pair. -/
theorem coefficient_gap_of_edgeMatching
    (G : SimpleGraph I) [DecidableRel G.Adj]
    (M : Finset (Sym2 I)) (hM : Pairing.EdgeMatching G M)
    (a : I → ℤ) (L U : ℤ)
    (hgap : ∀ e ∈ M, ∀ i ∈ (e : Set I), ∀ j ∈ (e : Set I), i ≠ j →
      L ≤ |a i - a j| ∧ |a i - a j| ≤ U) :
    ∀ k : MatchingIndex M,
      L ≤ |a (pairEmbeddingOfEdgeMatching G M hM (k, false)) -
        a (pairEmbeddingOfEdgeMatching G M hM (k, true))| ∧
      |a (pairEmbeddingOfEdgeMatching G M hM (k, false)) -
        a (pairEmbeddingOfEdgeMatching G M hM (k, true))| ≤ U := by
  exact endpoint_property_of_edgeMatching G M hM
    (fun i j ↦ L ≤ |a i - a j| ∧ |a i - a j| ≤ U) hgap

/-- Real-cast form of `coefficient_gap_of_edgeMatching`, matching the
coefficient type used by the Fourier anti-concentration lemmas. -/
theorem coefficient_gap_real_of_edgeMatching
    (G : SimpleGraph I) [DecidableRel G.Adj]
    (M : Finset (Sym2 I)) (hM : Pairing.EdgeMatching G M)
    (a : I → ℤ) (L U : ℤ)
    (hgap : ∀ e ∈ M, ∀ i ∈ (e : Set I), ∀ j ∈ (e : Set I), i ≠ j →
      L ≤ |a i - a j| ∧ |a i - a j| ≤ U) :
    ∀ k : MatchingIndex M,
      (L : ℝ) ≤
        |(a (pairEmbeddingOfEdgeMatching G M hM (k, false)) : ℝ) -
          (a (pairEmbeddingOfEdgeMatching G M hM (k, true)) : ℝ)| ∧
      |(a (pairEmbeddingOfEdgeMatching G M hM (k, false)) : ℝ) -
          (a (pairEmbeddingOfEdgeMatching G M hM (k, true)) : ℝ)| ≤ (U : ℝ) := by
  intro k
  have hk := coefficient_gap_of_edgeMatching G M hM a L U hgap k
  constructor
  · exact_mod_cast hk.1
  · exact_mod_cast hk.2

end

end Erdos636.PairEmbeddingAdapter
