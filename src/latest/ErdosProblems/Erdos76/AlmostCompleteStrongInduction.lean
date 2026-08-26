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
import ErdosProblems.Erdos76.AlmostCompleteDownward
import ErdosProblems.Erdos76.AlmostCompleteHamiltonian
import ErdosProblems.Erdos76.InducedTransport
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Strong induction for almost-complete fractional decompositions

This file formalizes the structural induction in Section 5 of Gruslys--Letzter.
The first section makes the induction hypothesis available on arbitrary finite
vertex types, rather than only `Fin n`; subsequent sections implement the four
cases of the exact-missing-edge induction.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

variable {A B : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B]

lemma missingEdgeCount_eq_compl_edgeSet_ncard (G : SimpleGraph A) :
    missingEdgeCount G = Gᶜ.edgeSet.ncard := by
  classical
  let hs : Gᶜ.edgeSet.Finite := Set.toFinite _
  unfold missingEdgeCount
  rw [Set.ncard_eq_toFinset_card _ hs]
  congr 1
  ext e
  simp [SimpleGraph.mem_edgeFinset]

lemma missingEdgeCount_map_equiv (G : SimpleGraph A) (e : A ≃ B) :
    missingEdgeCount (G.map e.toEmbedding) = missingEdgeCount G := by
  have hcompl : (G.map e.toEmbedding)ᶜ = Gᶜ.map e.toEmbedding :=
    compl_map_equiv G e
  calc
    missingEdgeCount (G.map e.toEmbedding) =
        (G.map e.toEmbedding)ᶜ.edgeSet.ncard :=
      missingEdgeCount_eq_compl_edgeSet_ncard _
    _ = (Gᶜ.map e.toEmbedding).edgeSet.ncard :=
      congrArg (fun H : SimpleGraph B ↦ H.edgeSet.ncard) hcompl
    _ = Gᶜ.edgeSet.ncard :=
      (Nat.card_congr (SimpleGraph.Iso.map e Gᶜ).mapEdgeSet).symm
    _ = missingEdgeCount G := (missingEdgeCount_eq_compl_edgeSet_ncard G).symm

attribute [local instance] Classical.propDecidable

private lemma edgeLoad_extendInducedWeight_eq_zero_of_not_mem_AC
    (G : SimpleGraph A) (S : Finset A) (w : Finset S → ℝ)
    (a b : A) (ha : a ∉ S) :
    fractionalEdgeLoad G (extendInducedWeight S w) s(a, b) = 0 := by
  classical
  unfold fractionalEdgeLoad
  apply Finset.sum_eq_zero
  intro t ht
  simp only [Finset.mem_filter] at ht
  rw [extendInducedWeight, dif_neg]
  intro hsub
  exact ha (hsub (Finset.mk_mem_sym2_iff.mp ht.2).1)

private lemma card_edgeFinset_filter_triangle_strong {G : SimpleGraph A}
    (t : Finset A) (ht : G.IsNClique 3 t) :
    ((G.edgeFinset).filter fun e ↦ e ∈ t.sym2).card = 3 := by
  classical
  rw [show (G.edgeFinset.filter fun e ↦ e ∈ t.sym2) =
      {e ∈ G.edgeFinset | e.toFinset ⊆ t} by
    ext e
    simp [Finset.mem_sym2_iff, subset_iff]]
  rw [G.card_filter_edgeFinset_toFinset_subset t]
  have htop : G.induce (↑t : Set A) = ⊤ := G.induce_eq_top.mpr ht.isClique
  calc
    #(G.induce (↑t : Set A)).edgeFinset =
        Nat.card (G.induce (↑t : Set A)).edgeSet := by
          rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
    _ = Nat.card (⊤ : SimpleGraph t).edgeSet :=
      congrArg (fun H : SimpleGraph t ↦ Nat.card H.edgeSet) htop
    _ = #((⊤ : SimpleGraph t).edgeFinset) := by
      rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
    _ = (Fintype.card t).choose 2 :=
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two
    _ = 3 := by simp [ht.card_eq]

private lemma sum_fractionalEdgeLoad_eq_three_mul_fractionalSize_strong
    (G : SimpleGraph A) (w : Finset A → ℝ) :
    ∑ e ∈ G.edgeFinset, fractionalEdgeLoad G w e =
      3 * fractionalSize G w := by
  rw [fractionalSize]
  simp_rw [fractionalEdgeLoad, Finset.sum_filter]
  rw [Finset.sum_comm, mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [show (∑ e ∈ G.edgeFinset, if e ∈ t.sym2 then w t else 0) =
      ∑ e ∈ (G.edgeFinset.filter fun e ↦ e ∈ t.sym2), w t by
    rw [Finset.sum_filter]]
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [card_edgeFinset_filter_triangle_strong t
    (SimpleGraph.mem_cliqueFinset_iff.mp ht)]
  norm_num

lemma fractionalUncoveredWeight_eq_card_sub_general
    (G : SimpleGraph A) (w : Finset A → ℝ) :
    fractionalUncoveredWeight G w =
      (Nat.card G.edgeSet : ℝ) - 3 * fractionalSize G w := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  rw [fractionalUncoveredWeight, Finset.sum_sub_distrib,
    sum_fractionalEdgeLoad_eq_three_mul_fractionalSize_strong]
  simp only [Finset.sum_const, nsmul_one]
  congr
  rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]

lemma fractionalUncoveredWeight_relabel_general
    (G : SimpleGraph A) (e : A ≃ B) (w : Finset A → ℝ) :
    fractionalUncoveredWeight (G.map e.toEmbedding) (relabelWeight e w) =
      fractionalUncoveredWeight G w := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  letI : DecidableRel (G.map e.toEmbedding).Adj := Classical.decRel _
  have hcard : Nat.card (G.map e.toEmbedding).edgeSet = Nat.card G.edgeSet :=
    (Nat.card_congr (SimpleGraph.Iso.map e G).mapEdgeSet).symm
  rw [fractionalUncoveredWeight_eq_card_sub_general,
    fractionalUncoveredWeight_eq_card_sub_general, fractionalSize_relabel, hcard]

lemma IsHalfBounded.relabel {G : SimpleGraph A} {w : Finset A → ℝ}
    (hw : IsHalfBounded G w) (e : A ≃ B) :
    IsHalfBounded (G.map e.toEmbedding) (relabelWeight e w) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  letI : DecidableRel (G.map e.toEmbedding).Adj := Classical.decRel _
  intro t ht
  have ht' := SimpleGraph.mem_cliqueFinset_iff.mp ht
  obtain ⟨s, hs, rfl⟩ :=
    (SimpleGraph.isNClique_map_iff (G := G) (f := e.toEmbedding) (by omega)).mp ht'
  simpa using hw s (SimpleGraph.mem_cliqueFinset_iff.mpr hs)

lemma HasStrongFractionalPacking.relabel {G : SimpleGraph A}
    (e : A ≃ B) {a : ℝ} (hG : HasStrongFractionalPacking G a) :
    HasStrongFractionalPacking (G.map e.toEmbedding) a := by
  classical
  obtain ⟨w, hw, hunc, hhalf⟩ := hG
  refine ⟨relabelWeight e w, hw.relabel e, ?_, hhalf.relabel e⟩
  rwa [fractionalUncoveredWeight_relabel_general]

/-- The strong conclusion at a fixed cardinality, quantified over arbitrary
finite vertex types.  This is the form stable under vertex deletion. -/
def AlmostCompleteStrongAt (n : ℕ) : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A], Fintype.card A = n →
    ∀ a : ℕ, a ≤ 4 → ∀ G : SimpleGraph A,
      missingEdgeCount G ≤ n - 4 + a →
        HasStrongFractionalPacking G (a : ℝ)

/-- A theorem on `Fin n` transports to every finite vertex type of cardinality
`n`. -/
theorem almostCompleteStrongAt_of_fin {n : ℕ}
    (hfin : ∀ a : ℕ, a ≤ 4 → ∀ G : SimpleGraph (Fin n),
      missingEdgeCount G ≤ n - 4 + a →
        HasStrongFractionalPacking G (a : ℝ)) :
    AlmostCompleteStrongAt n := by
  classical
  intro A _ _ hcard a ha G hmissing
  let e : A ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let H : SimpleGraph (Fin n) := G.map e.toEmbedding
  have hmissingH : missingEdgeCount H ≤ n - 4 + a := by
    simpa only [H, missingEdgeCount_map_equiv] using hmissing
  have hH := hfin a ha H hmissingH
  have hback : H.map e.symm.toEmbedding = G := by
    dsimp only [H]
    rw [SimpleGraph.map_map]
    simpa using G.map_id
  simpa only [hback] using hH.relabel e.symm

/-- Extract a generic-cardinality strong base from the finite certificate
family. -/
theorem certificateBases_strongAt
    (hbases : AlmostCompleteCertificateBases) {n : ℕ}
    (hn11 : 11 ≤ n) (hn13 : n ≤ 13) : AlmostCompleteStrongAt n := by
  classical
  apply almostCompleteStrongAt_of_fin
  intro a ha G hmissing
  have hexact : ∀ H : SimpleGraph (Fin n),
      missingEdgeCount H = n - 4 + a →
        HasStrongFractionalPacking H (a : ℝ) :=
    hbases.1 n a hn11 hn13 ha
  by_cases hlow : missingEdgeCount G ≤ n - 4
  · have hexactZero : ∀ H : SimpleGraph (Fin n),
        missingEdgeCount H = n - 4 →
          ∃ w : Finset (Fin n) → ℝ,
            IsFractionalDecomposition H w ∧ IsHalfBounded H w := by
      intro H hH
      obtain ⟨w, hw, hunc, hhalf⟩ :=
        hbases.1 n 0 hn11 hn13 (by omega) H (by simpa using hH)
      have hunc0 : fractionalUncoveredWeight H w = 0 :=
        le_antisymm (by simpa using hunc)
          (fractionalUncoveredWeight_nonneg hw)
      exact ⟨w, (isFractionalDecomposition_iff hw).2 hunc0, hhalf⟩
    obtain ⟨w, hw, hhalf⟩ := halfBoundedDecomposition_of_exact_missing
      (A := Fin n) (by simpa using (show 7 ≤ n by omega))
      (m := n - 4) (by simp) hexactZero G hlow
    refine ⟨w, hw.isPacking, ?_, hhalf⟩
    rw [fractionalUncoveredWeight_eq_zero hw]
    positivity
  · let b := missingEdgeCount G - (n - 4)
    have hb : b ≤ a := by
      dsimp only [b]
      omega
    have hb4 : b ≤ 4 := hb.trans ha
    have hGb : missingEdgeCount G = n - 4 + b := by
      dsimp only [b]
      omega
    obtain ⟨w, hw, hunc, hhalf⟩ := hbases.1 n b hn11 hn13 hb4 G hGb
    refine ⟨w, hw, hunc.trans ?_, hhalf⟩
    exact_mod_cast hb

/-! ## The strong-induction spine

The four structural cases in Section 5 only call the induction hypothesis at
orders `n - 1` and `n - 2`.  The following proposition isolates precisely that
local step.  It is useful while the individual cases are developed: the
well-founded induction itself is then a separate, completely arithmetic
argument, and the checked orders `11`, `12`, and `13` are consumed in exactly
one place.
-/

/-- The local two-order induction step proved by cases D5--D8 in the paper. -/
def AlmostCompleteStructuralStep : Prop :=
  ∀ n : ℕ, 14 ≤ n → AlmostCompleteStrongAt (n - 1) →
    AlmostCompleteStrongAt (n - 2) → AlmostCompleteStrongAt n

/-- Checked bases at orders `11`, `12`, and `13`, together with the structural
two-order step, imply the generic-cardinality strong theorem at every order at
least `11`.  This is the well-founded-induction spine of Theorem 2.1. -/
theorem strongAt_of_certificateBases_and_structuralStep
    (hbases : AlmostCompleteCertificateBases)
    (hstep : AlmostCompleteStructuralStep) {n : ℕ} (hn : 11 ≤ n) :
    AlmostCompleteStrongAt n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn13 : n ≤ 13
      · exact certificateBases_strongAt hbases hn hn13
      · have hn14 : 14 ≤ n := by omega
        apply hstep n hn14
        · exact ih (n - 1) (by omega) (by omega)
        · exact ih (n - 2) (by omega) (by omega)

/-- Finite-type specialization of the abstract induction spine. -/
theorem almostCompleteStrong_of_certificateBases_and_structuralStep
    (hbases : AlmostCompleteCertificateBases)
    (hstep : AlmostCompleteStructuralStep) : AlmostCompleteStrong := by
  intro n a hn ha G hmissing
  exact strongAt_of_certificateBases_and_structuralStep hbases hstep hn
    (Fin n) (by simp) a ha G hmissing

/-! ## Vertex deletion bookkeeping

The first structural case deletes one vertex.  These identities put the
order and the number of missing edges of the induced graph into the precise
form required by `AlmostCompleteStrongAt` and `weightedReduction`.
-/

/-- The subtype obtained by deleting one vertex has the expected order. -/
lemma card_univ_erase (u : A) : Fintype.card (↑((Finset.univ : Finset A).erase u)) =
    Fintype.card A - 1 := by
  rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ u),
    Finset.card_univ]

/-- Deleting a vertex removes exactly its nonedges from the missing-edge
count. -/
lemma missingEdgeCount_induce_univ_erase (G : SimpleGraph A) (u : A) :
    missingEdgeCount (G.induce
      (↑((Finset.univ : Finset A).erase u) : Set A)) =
      missingEdgeCount G - Gᶜ.degree u := by
  classical
  let S : Finset A := Finset.univ.erase u
  have hset : (↑S : Set A) = ({u} : Set A)ᶜ := by
    ext x
    simp [S]
  have hcard := SimpleGraph.card_edgeFinset_induce_compl_singleton Gᶜ u
  have hinc : (Gᶜ.incidenceFinset u).card = Gᶜ.degree u := by
    rw [← SimpleGraph.card_incidenceSet_eq_degree]
    exact Set.toFinset_card _
  have hdelete : (Gᶜ.deleteIncidenceSet u).edgeFinset.card =
      Gᶜ.edgeFinset.card - Gᶜ.degree u := by
    rw [SimpleGraph.edgeFinset_deleteIncidenceSet_eq_sdiff,
      Finset.card_sdiff_of_subset]
    · rw [hinc]
    · intro e he
      rw [SimpleGraph.mem_incidenceFinset] at he
      exact SimpleGraph.mem_edgeFinset.mpr he.1
  have hcardSet : Nat.card (Gᶜ.induce ({u} : Set A)ᶜ).edgeSet =
      Nat.card (Gᶜ.deleteIncidenceSet u).edgeSet := by
    simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet] using hcard
  have hdeleteSet : Nat.card (Gᶜ.deleteIncidenceSet u).edgeSet =
      Nat.card Gᶜ.edgeSet - Gᶜ.degree u := by
    simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet] using hdelete
  calc
    missingEdgeCount (G.induce (↑((Finset.univ : Finset A).erase u) : Set A)) =
        Nat.card (G.induce
          (↑((Finset.univ : Finset A).erase u) : Set A))ᶜ.edgeSet :=
      missingEdgeCount_eq_compl_edgeSet_ncard _
    _ = Nat.card (Gᶜ.induce
          (↑((Finset.univ : Finset A).erase u) : Set A)).edgeSet := by
      rw [compl_induce]
    _ = Nat.card (Gᶜ.induce ({u} : Set A)ᶜ).edgeSet := by
      rw [hset]
    _ = Nat.card (Gᶜ.deleteIncidenceSet u).edgeSet := hcardSet
    _ = Nat.card Gᶜ.edgeSet - Gᶜ.degree u := hdeleteSet
    _ = missingEdgeCount G - Gᶜ.degree u := by
      rw [Nat.card_coe_set_eq, missingEdgeCount_eq_compl_edgeSet_ncard]

/-- Restricting to a smaller induced vertex set cannot create more missing
edges.  The proof maps complement edges along the subtype inclusion. -/
lemma missingEdgeCount_induce_finset_mono (G : SimpleGraph A)
    {S T : Finset A} (hST : S ⊆ T) :
    missingEdgeCount (G.induce (↑S : Set A)) ≤
      missingEdgeCount (G.induce (↑T : Set A)) := by
  classical
  let ι : S ↪ T :=
    ⟨fun x ↦ ⟨x, hST x.property⟩,
      fun x y h ↦ Subtype.ext
        (show (x : A) = (y : A) from
          congrArg (fun z : T ↦ (z : A)) h)⟩
  let φ : Gᶜ.induce (↑S : Set A) →g Gᶜ.induce (↑T : Set A) :=
    ⟨fun x ↦ ι x, fun {_ _} h ↦ h⟩
  rw [missingEdgeCount_eq_compl_edgeSet_ncard,
    missingEdgeCount_eq_compl_edgeSet_ncard]
  rw [← compl_induce G S, ← compl_induce G T]
  exact Nat.card_le_card_of_injective φ.mapEdgeSet
    (SimpleGraph.Hom.mapEdgeSet.injective φ ι.injective)

/-- Incidence in a finite set of unordered pairs is preserved when every
pair is mapped along an embedding. -/
lemma filter_map_sym2_incidence_card {X Y : Type*}
    [DecidableEq X] [DecidableEq Y] (e : X ↪ Y)
    (C : Finset (Sym2 X)) (x : X) :
    ((C.map e.sym2Map).filter fun p ↦ e x ∈ p).card =
      (C.filter fun p ↦ x ∈ p).card := by
  classical
  rw [Finset.filter_map, Finset.card_map]
  congr 1
  apply Finset.filter_congr
  intro p hp
  change e x ∈ Sym2.map e p ↔ x ∈ p
  rw [Sym2.mem_map]
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact e.injective hxy.symm ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- A finite matching of size at least two can be reindexed to avoid every
edge of another matching.  This is the small derangement step used after the
two D6 target sets have been chosen. -/
theorem exists_reindex_avoiding_injective {X Y : Type*}
    [Fintype X] [DecidableEq X] [DecidableEq Y]
    (hX : 2 ≤ Fintype.card X) (f g : X → Y)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ σ : X ≃ X, ∀ x, g (σ x) ≠ f x := by
  classical
  let allowed : X → Finset X := fun x ↦
    Finset.univ.filter fun y ↦ g y ≠ f x
  have hHall : ∀ s : Finset X, s.card ≤ (s.biUnion allowed).card := by
    intro s
    by_cases hs0 : s = ∅
    · subst s
      simp
    by_cases hs1 : s.card = 1
    · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hs1
      rw [Finset.card_singleton, Finset.singleton_biUnion]
      by_cases hex : ∃ y, g y = f x
      · obtain ⟨y, hy⟩ := hex
        have hallowed : allowed x = Finset.univ.erase y := by
          ext z
          simp only [allowed, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_erase]
          constructor
          · intro hz
            exact ⟨fun hzy ↦ hz (hzy ▸ hy), trivial⟩
          · rintro ⟨hzy, _⟩ hgf
            exact hzy (hg (hgf.trans hy.symm))
        rw [hallowed, Finset.card_erase_of_mem (Finset.mem_univ y),
          Finset.card_univ]
        omega
      · have hallowed : allowed x = Finset.univ := by
          ext z
          simp only [allowed, Finset.mem_filter, Finset.mem_univ, true_and,
            iff_true]
          exact fun h ↦ hex ⟨z, h⟩
        rw [hallowed, Finset.card_univ]
        omega
    · have hspos : 0 < s.card := Finset.card_pos.mpr
        (Finset.nonempty_of_ne_empty hs0)
      have hs2 : 2 ≤ s.card := by omega
      have hUnion : s.biUnion allowed = Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro y
        rw [Finset.mem_biUnion]
        by_contra hnone
        push Not at hnone
        obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty hs0
        have hsub : s ⊆ {x} := by
          intro z hz
          rw [Finset.mem_singleton]
          apply hf
          have hyx : g y = f x := by
            by_contra hne
            exact hnone x hx (by simp [allowed, hne])
          have hyz : g y = f z := by
            by_contra hne
            exact hnone z hz (by simp [allowed, hne])
          exact hyz.symm.trans hyx
        have := Finset.card_le_card hsub
        simp at this
        omega
      rw [hUnion, Finset.card_univ]
      exact s.card_le_univ
  obtain ⟨σ, hσinj, hσmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' allowed).mp hHall
  have hσbij : Function.Bijective σ :=
    (Fintype.bijective_iff_injective_and_card σ).2 ⟨hσinj, rfl⟩
  let e : X ≃ X := Equiv.ofBijective σ hσbij
  refine ⟨e, ?_⟩
  intro x
  have hm := hσmem x
  simpa only [allowed, Finset.mem_filter, Finset.mem_univ, true_and, e,
    Equiv.ofBijective_apply] using hm

/-- Capacity assignment behind the two D6 target matchings.  A vertex of
`K` supplies one slot to each matching, while a vertex of `L` supplies one
slot globally. -/
theorem exists_d6_slot_assignment {X K L : Type*}
    [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K]
    [Fintype L] [DecidableEq L]
    (hm : Fintype.card X ≤ 3)
    (hcapacity : Fintype.card X + 3 ≤
      2 * Fintype.card K + Fintype.card L) :
    ∃ F : Fin 2 × X → (Fin 2 × K) ⊕ L,
      Function.Injective F ∧
      ∀ i x, match F (i, x) with
        | Sum.inl p => p.1 = i
        | Sum.inr _ => True := by
  classical
  let embK (i : Fin 2) : K ↪ (Fin 2 × K) ⊕ L :=
    ⟨fun k ↦ Sum.inl (i, k), fun x y h ↦ by simpa using h⟩
  let embL : L ↪ (Fin 2 × K) ⊕ L :=
    ⟨Sum.inr, Sum.inr_injective⟩
  let allowed : Fin 2 × X → Finset ((Fin 2 × K) ⊕ L) := fun p ↦
    (Finset.univ.map (embK p.1)) ∪ Finset.univ.map embL
  have hcardAllowed (p : Fin 2 × X) :
      (allowed p).card = Fintype.card K + Fintype.card L := by
    have hdisj : Disjoint (Finset.univ.map (embK p.1))
        (Finset.univ.map embL) := by
      rw [Finset.disjoint_left]
      intro z hzK hzL
      obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hzK
      obtain ⟨l, _, hbad⟩ := Finset.mem_map.mp hzL
      exact Sum.inr_ne_inl hbad
    change ((Finset.univ.map (embK p.1)) ∪
      Finset.univ.map embL).card = _
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_map, Finset.card_map, Finset.card_univ, Finset.card_univ]
  have hHall : ∀ s : Finset (Fin 2 × X),
      s.card ≤ (s.biUnion allowed).card := by
    intro s
    by_cases hs0 : s = ∅
    · subst s
      simp
    let I : Finset (Fin 2) := s.image Prod.fst
    have hSsub : s ⊆ I ×ˢ (Finset.univ : Finset X) := by
      intro p hp
      exact Finset.mem_product.mpr
        ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩, Finset.mem_univ p.2⟩
    have hSbound : s.card ≤ I.card * Fintype.card X := by
      calc
        s.card ≤ (I ×ˢ (Finset.univ : Finset X)).card :=
          Finset.card_le_card hSsub
        _ = I.card * Fintype.card X := by
          rw [Finset.card_product, Finset.card_univ]
    have hIpos : 0 < I.card := by
      apply Finset.card_pos.mpr
      obtain ⟨p, hp⟩ := Finset.nonempty_of_ne_empty hs0
      exact ⟨p.1, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
    have hIle : I.card ≤ 2 := by
      calc
        I.card ≤ (Finset.univ : Finset (Fin 2)).card :=
          Finset.card_le_card (Finset.subset_univ I)
        _ = 2 := by simp
    have hIc : I.card = 1 ∨ I.card = 2 := by omega
    rcases hIc with hIc | hIc
    · obtain ⟨p, hp⟩ := Finset.nonempty_of_ne_empty hs0
      have hsub : allowed p ⊆ s.biUnion allowed := by
        intro z hz
        exact Finset.mem_biUnion.mpr ⟨p, hp, hz⟩
      have htarget : Fintype.card X ≤
          Fintype.card K + Fintype.card L := by omega
      calc
        s.card ≤ Fintype.card X := by simpa [hIc] using hSbound
        _ ≤ Fintype.card K + Fintype.card L := htarget
        _ = (allowed p).card := (hcardAllowed p).symm
        _ ≤ (s.biUnion allowed).card := Finset.card_le_card hsub
    · have hIuniv : I = Finset.univ := by
        apply Finset.eq_of_subset_of_card_le (Finset.subset_univ I)
        simpa [hIc]
      have hUnion : s.biUnion allowed = Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro z
        rw [Finset.mem_biUnion]
        rcases z with z | z
        · obtain ⟨i, k⟩ := z
          have hiI : i ∈ I := by rw [hIuniv]; simp
          obtain ⟨p, hp, hpi⟩ := Finset.mem_image.mp hiI
          refine ⟨p, hp, ?_⟩
          have hi : p.1 = i := by simpa using hpi
          subst i
          apply Finset.mem_union_left
          exact Finset.mem_map.mpr ⟨k, Finset.mem_univ k, rfl⟩
        · obtain ⟨p, hp⟩ := Finset.nonempty_of_ne_empty hs0
          refine ⟨p, hp, ?_⟩
          apply Finset.mem_union_right
          exact Finset.mem_map.mpr ⟨z, Finset.mem_univ z, rfl⟩
      have hs2m : s.card ≤ 2 * Fintype.card X := by
        simpa only [hIc] using hSbound
      calc
        s.card ≤ 2 * Fintype.card X := hs2m
        _ ≤ Fintype.card X + 3 := by omega
        _ ≤ 2 * Fintype.card K + Fintype.card L := hcapacity
        _ = Fintype.card ((Fin 2 × K) ⊕ L) := by simp
        _ = (s.biUnion allowed).card := by rw [hUnion, Finset.card_univ]
  obtain ⟨F, hFinj, hFmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' allowed).mp hHall
  refine ⟨F, hFinj, ?_⟩
  intro i x
  have hmF := hFmem (i, x)
  rcases hFx : F (i, x) with p | l
  · obtain ⟨j, k⟩ := p
    simp only [hFx] at hmF ⊢
    simp only [allowed, Finset.mem_union, Finset.mem_map, Finset.mem_univ,
      true_and] at hmF
    rcases hmF with ⟨k', hk'⟩ | ⟨l', hl'⟩
    · change Sum.inl (i, k') = Sum.inl (j, k) at hk'
      exact (congrArg Prod.fst (Sum.inl.inj hk')).symm
    · change Sum.inr l' = Sum.inl (j, k) at hl'
      exact (Sum.inr_ne_inl hl').elim
  · trivial

/-! ## The half-capacity used in case D5 -/

/-- Capacity one on the edges of `H`, except for a selected set `C` of
edges which receive capacity one half; all nonedges of `H` have capacity
zero.  In case D5, `C` is the Hamilton cycle in the neighborhood of the
deleted vertex. -/
def halfEdgeCapacity (H : SimpleGraph A) (C : Finset (Sym2 A)) :
    Sym2 A → ℝ :=
  fun e ↦ if e ∈ H.edgeSet then if e ∈ C then 1 / 2 else 1 else 0

/-- The genuine edges of an augmented cycle: edges added only to obtain the
cycle are discarded before assigning triangle weights. -/
def presentCycleEdges (H : SimpleGraph A) (C : Finset (Sym2 A)) :
    Finset (Sym2 A) := C.filter (· ∈ H.edgeSet)

lemma presentCycleEdges_subset (H : SimpleGraph A) (C : Finset (Sym2 A)) :
    presentCycleEdges H C ⊆ C := Finset.filter_subset _ _

lemma presentCycleEdges_mem_edgeSet (H : SimpleGraph A)
    (C : Finset (Sym2 A)) :
    ∀ e ∈ presentCycleEdges H C, e ∈ H.edgeSet := by
  intro e he
  exact (Finset.mem_filter.mp he).2

/-- If an augmented cycle has `d` edges and exactly `α` of them are absent
from the graph, its genuine edge set has size `d - α`. -/
lemma card_presentCycleEdges {H : SimpleGraph A} {C : Finset (Sym2 A)}
    {d α : ℕ} (hcard : C.card = d)
    (habsent : (C.filter fun e ↦ e ∉ H.edgeSet).card = α) :
    (presentCycleEdges H C).card = d - α := by
  classical
  let P := C.filter fun e ↦ e ∈ H.edgeSet
  let N := C.filter fun e ↦ e ∉ H.edgeSet
  have hdisj : Disjoint P N := by
    rw [Finset.disjoint_left]
    intro e heP heN
    exact (Finset.mem_filter.mp heN).2 (Finset.mem_filter.mp heP).2
  have hunion : P ∪ N = C := by
    ext e
    simp only [P, N, Finset.mem_union, Finset.mem_filter]
    tauto
  have hpartition : P.card + N.card = C.card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  change P.card = d - α
  have hN : N.card = α := by simpa only [N] using habsent
  rw [hN, hcard] at hpartition
  omega

lemma halfEdgeCapacity_isEdgeCapacity_top (H : SimpleGraph A)
    (C : Finset (Sym2 A)) :
    IsEdgeCapacity (⊤ : SimpleGraph A) (halfEdgeCapacity H C) := by
  classical
  constructor
  · intro e he
    by_cases hH : e ∈ H.edgeSet <;> by_cases hC : e ∈ C <;>
      simp [halfEdgeCapacity, hH, hC] <;> norm_num
  · intro e he
    have hdiag : e.IsDiag := by
      simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
    have hnH : e ∉ H.edgeSet := fun hH ↦
      (H.not_isDiag_of_mem_edgeSet hH) hdiag
    simp [halfEdgeCapacity, hnH]

private lemma sum_indicator_mem_eq_card_mul {X : Type*} [DecidableEq X]
    (S T : Finset X) (hTS : T ⊆ S) (r : ℝ) :
    ∑ x ∈ S, (if x ∈ T then r else 0) = (T.card : ℝ) * r := by
  rw [← Finset.sum_filter]
  have hfilter : S.filter (· ∈ T) = T := by
    ext x
    simp [hTS]
  rw [hfilter, Finset.sum_const, nsmul_eq_mul]

lemma capacityMissingWeight_halfEdgeCapacity
    (H : SimpleGraph A) (C : Finset (Sym2 A))
    (hCH : ∀ e ∈ C, e ∈ H.edgeSet) :
    capacityMissingWeight (halfEdgeCapacity H C) =
      (missingEdgeCount H : ℝ) + (C.card : ℝ) / 2 := by
  classical
  let topEdges : Finset (Sym2 A) := (⊤ : SimpleGraph A).edgeFinset
  have hCtop : C ⊆ topEdges := by
    intro e he
    have hH := hCH e he
    exact SimpleGraph.mem_edgeFinset.mpr
      (SimpleGraph.edgeSet_mono le_top hH)
  have hcomptop : Hᶜ.edgeFinset ⊆ topEdges := by
    intro e he
    exact SimpleGraph.mem_edgeFinset.mpr
      (SimpleGraph.edgeSet_mono le_top (SimpleGraph.mem_edgeFinset.mp he))
  have hpoint : ∀ e ∈ topEdges,
      1 - halfEdgeCapacity H C e =
        (if e ∈ Hᶜ.edgeFinset then 1 else 0) +
          (if e ∈ C then (1 / 2 : ℝ) else 0) := by
    intro e he
    have hne : ¬ e.IsDiag := SimpleGraph.not_isDiag_of_mem_edgeFinset he
    induction e using Sym2.inductionOn with
    | hf x y =>
        simp only [Sym2.mk_isDiag_iff] at hne
        by_cases hH : H.Adj x y
        · have hHset : s(x, y) ∈ H.edgeSet := by
            simpa [SimpleGraph.mem_edgeSet] using hH
          have hncomp : s(x, y) ∉ Hᶜ.edgeFinset := by
            simp [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
              SimpleGraph.compl_adj, hH]
          by_cases hC : s(x, y) ∈ C <;>
            simp [halfEdgeCapacity, hHset, hC, hncomp] <;> norm_num
        · have hnHset : s(x, y) ∉ H.edgeSet := by
            simpa [SimpleGraph.mem_edgeSet] using hH
          have hcomp : s(x, y) ∈ Hᶜ.edgeFinset := by
            simp [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
              SimpleGraph.compl_adj, hne, hH]
          have hnC : s(x, y) ∉ C := fun hC ↦ hnHset (hCH s(x, y) hC)
          simp [halfEdgeCapacity, hnHset, hnC, hcomp]
  unfold capacityMissingWeight
  change (∑ e ∈ topEdges, (1 - halfEdgeCapacity H C e)) = _
  rw [Finset.sum_congr rfl (fun e he ↦ hpoint e he)]
  rw [Finset.sum_add_distrib]
  rw [sum_indicator_mem_eq_card_mul topEdges Hᶜ.edgeFinset hcomptop,
    sum_indicator_mem_eq_card_mul topEdges C hCtop]
  unfold missingEdgeCount
  norm_num [div_eq_mul_inv]

/-- The numerical estimate in case D5 after deleting the high-nondegree
vertex.  `M - q` is the number of missing edges left after the deletion and
`d - α` is the number of genuine graph edges on the augmented Hamilton
cycle. -/
lemma d5_capacity_bound {n a α M q d : ℕ}
    (hn : 5 ≤ n) (hαa : α ≤ a) (hαd : α ≤ d) (hqM : q ≤ M)
    (hM : M ≤ n - 4 + a) (hdegree : d + q = n - 1)
    (hlarge : n + α + 1 ≤ 3 * q) :
    ((M - q : ℕ) : ℝ) + ((d - α : ℕ) : ℝ) / 2 ≤
      ((((n - 1) - 4) + (a - α) : ℕ) : ℝ) := by
  have hn4 : 4 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hn14 : 4 ≤ n - 1 := by omega
  have hM' : (M : ℝ) ≤ ((n - 4 + a : ℕ) : ℝ) := by exact_mod_cast hM
  have hdegree' : (d : ℝ) + q = ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast hdegree
  have hlarge' : ((n + α + 1 : ℕ) : ℝ) ≤ (3 * q : ℕ) := by
    exact_mod_cast hlarge
  rw [Nat.cast_add, Nat.cast_sub hn4] at hM'
  rw [Nat.cast_sub hn1] at hdegree'
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_mul,
    Nat.cast_ofNat] at hlarge'
  rw [Nat.cast_add, Nat.cast_sub hqM, Nat.cast_sub hαd,
    Nat.cast_sub hn14, Nat.cast_sub hn1, Nat.cast_sub hαa]
  norm_num only [Nat.cast_ofNat] at hM' hdegree' ⊢
  have hd' : (d : ℝ) = (n : ℝ) - 1 - q := by linarith
  calc
    (M : ℝ) - q + ((d : ℝ) - α) / 2 ≤
        ((n : ℝ) - 4 + a) - q + ((d : ℝ) - α) / 2 := by
      linarith
    _ = ((n : ℝ) - 4 + a) - q +
        (((n : ℝ) - 1 - q) - α) / 2 := by rw [hd']
    _ ≤ (n : ℝ) - 1 - 4 + (a - α) := by linarith

/-- `AlmostCompleteStrongAt` is exactly the graph hypothesis needed by the
weighted reduction at the same order and defect parameter. -/
theorem weightedPacking_of_strongAt {n a : ℕ}
    (hstrong : AlmostCompleteStrongAt n) (hcard : Fintype.card A = n)
    (ha : a ≤ 4) (c : Sym2 A → ℝ)
    (hc : IsEdgeCapacity (⊤ : SimpleGraph A) c)
    (hmissing : capacityMissingWeight c ≤ (n - 4 + a : ℕ)) :
    ∃ w : Finset A → ℝ,
      IsCapacityPacking (⊤ : SimpleGraph A) c w ∧
        capacityUncoveredWeight (⊤ : SimpleGraph A) c w ≤ (a : ℝ) ∧
          IsHalfBounded (⊤ : SimpleGraph A) w := by
  apply weightedReduction (m := n - 4 + a) c hc hmissing (a : ℝ)
  intro H hH
  exact hstrong A hcard a ha H hH

/-- Weighted-reduction output in the nontrivial branch of case D5.  The
selected set `C` is the set of genuine edges of the Hamilton cycle after at
most `α` nonedges have been added.  Thus it has `degree u - α` edges. -/
theorem d5_weightedPacking_on_vertexComplement {n a α : ℕ}
    (hcard : Fintype.card A = n) (hn : 5 ≤ n) (ha : a ≤ 4)
    (G : SimpleGraph A) (u : A)
    (hαa : α ≤ a) (hαd : α ≤ G.degree u)
    (hstrong : AlmostCompleteStrongAt (n - 1))
    (hmissing : missingEdgeCount G ≤ n - 4 + a)
    (hlarge : n + α + 1 ≤ 3 * Gᶜ.degree u)
    (C : Finset (Sym2 (↑((Finset.univ : Finset A).erase u))))
    (hCH : ∀ e ∈ C, e ∈ (G.induce
      (↑((Finset.univ : Finset A).erase u) : Set A)).edgeSet)
    (hcardC : C.card = G.degree u - α) :
    ∃ w : Finset (↑((Finset.univ : Finset A).erase u)) → ℝ,
      IsCapacityPacking (⊤ : SimpleGraph
        (↑((Finset.univ : Finset A).erase u)))
        (halfEdgeCapacity (G.induce
          (↑((Finset.univ : Finset A).erase u) : Set A)) C) w ∧
      capacityUncoveredWeight (⊤ : SimpleGraph
        (↑((Finset.univ : Finset A).erase u)))
          (halfEdgeCapacity (G.induce
            (↑((Finset.univ : Finset A).erase u) : Set A)) C) w ≤
        ((a - α : ℕ) : ℝ) ∧
      IsHalfBounded (⊤ : SimpleGraph
        (↑((Finset.univ : Finset A).erase u))) w := by
  classical
  let S : Finset A := Finset.univ.erase u
  have horder : Fintype.card S = n - 1 := by
    rw [card_univ_erase, hcard]
  have hqM : Gᶜ.degree u ≤ missingEdgeCount G := by
    simpa only [missingEdgeCount] using
      (Gᶜ.degree_le_card_edgeFinset (v := u))
  have hdegree : G.degree u + Gᶜ.degree u = n - 1 := by
    have hdlt := G.degree_lt_card_verts u
    have hcomp := G.degree_compl (v := u)
    rw [hcard] at hdlt hcomp
    omega
  have hcapMissing : capacityMissingWeight (halfEdgeCapacity
      (G.induce (↑((Finset.univ : Finset A).erase u) : Set A)) C) ≤
      (((n - 1) - 4) + (a - α) : ℕ) := by
    rw [capacityMissingWeight_halfEdgeCapacity
      (G.induce (↑((Finset.univ : Finset A).erase u) : Set A)) C hCH]
    · rw [show missingEdgeCount (G.induce
            (↑((Finset.univ : Finset A).erase u) : Set A)) =
            missingEdgeCount G - Gᶜ.degree u by
          simpa only using missingEdgeCount_induce_univ_erase G u,
        hcardC]
      exact d5_capacity_bound hn hαa hαd hqM hmissing hdegree hlarge
  simpa only [S] using weightedPacking_of_strongAt hstrong horder
    (show a - α ≤ 4 by omega)
    (halfEdgeCapacity
      (G.induce (↑((Finset.univ : Finset A).erase u) : Set A)) C)
    (halfEdgeCapacity_isEdgeCapacity_top
      (G.induce (↑((Finset.univ : Finset A).erase u) : Set A)) C)
    hcapMissing

/-- The D5 weighted reduction in the form delivered by the augmented
Hamilton-cycle argument.  The cycle may use missing edges; filtering it to the
edges present in the induced graph produces precisely the half-capacity set. -/
theorem d5_weightedPacking_of_augmentedCycle {n a α : ℕ}
    (hcard : Fintype.card A = n) (hn : 5 ≤ n) (ha : a ≤ 4)
    (G : SimpleGraph A) (u : A)
    (hαa : α ≤ a) (hαd : α ≤ G.degree u)
    (hstrong : AlmostCompleteStrongAt (n - 1))
    (hmissing : missingEdgeCount G ≤ n - 4 + a)
    (hlarge : n + α + 1 ≤ 3 * Gᶜ.degree u)
    (C : Finset (Sym2 (↑((Finset.univ : Finset A).erase u))))
    (hcardC : C.card = G.degree u)
    (habsent : (C.filter fun e ↦ e ∉ (G.induce
      (↑((Finset.univ : Finset A).erase u) : Set A)).edgeSet).card = α) :
    ∃ w : Finset (↑((Finset.univ : Finset A).erase u)) → ℝ,
      IsCapacityPacking (⊤ : SimpleGraph
        (↑((Finset.univ : Finset A).erase u)))
        (halfEdgeCapacity (G.induce
          (↑((Finset.univ : Finset A).erase u) : Set A))
          (presentCycleEdges (G.induce
            (↑((Finset.univ : Finset A).erase u) : Set A)) C)) w ∧
      capacityUncoveredWeight (⊤ : SimpleGraph
        (↑((Finset.univ : Finset A).erase u)))
          (halfEdgeCapacity (G.induce
            (↑((Finset.univ : Finset A).erase u) : Set A))
            (presentCycleEdges (G.induce
              (↑((Finset.univ : Finset A).erase u) : Set A)) C)) w ≤
        ((a - α : ℕ) : ℝ) ∧
      IsHalfBounded (⊤ : SimpleGraph
        (↑((Finset.univ : Finset A).erase u))) w := by
  let H := G.induce (↑((Finset.univ : Finset A).erase u) : Set A)
  apply d5_weightedPacking_on_vertexComplement hcard hn ha G u hαa hαd
    hstrong hmissing hlarge (presentCycleEdges H C)
  · exact presentCycleEdges_mem_edgeSet H C
  · exact card_presentCycleEdges hcardC habsent

/-! ## Arithmetic closures for cases D6--D8

The remaining cases repeatedly reduce a finite-sum estimate to one of a small
number of integer contradictions.  Keeping these closures separate prevents
the graph/matching part of the proof from carrying divisions by three.
-/

/-- Arithmetic endpoint of Claim 5.1.  The first displayed inequality is the
degree-sum upper bound after multiplying by three; `2*k + ell ≤ m + 2` is
the negation of the claim. -/
lemma d6_claim51_arithmetic {n a m k ell : ℕ}
    (hn : 14 ≤ n) (ha : a ≤ 4) (hm : m ≤ 3)
    (hsmall : 2 * k + ell ≤ m + 2)
    (hdegree : 6 * (n - 4 + a) + 3 * m + 3 * k ≤
      k * (n + a) + 3 * ell + 3 * n) : False := by
  have hn4 : 4 ≤ n := by omega
  have hk : k ≤ 2 := by omega
  rw [Nat.mul_add] at hdegree
  interval_cases k <;> norm_num at hdegree ⊢ <;> omega

/-- Arithmetic endpoint of Claim 5.2.  In the unsaturated branch the first
aggregate inequality holds; in the unique-saturated-vertex branch the second
one holds.  Either contradicts `n ≥ 14` and `m ≤ 3` if the total residual
allowance is below `2a`. -/
lemma d6_claim52_arithmetic {n a m R : ℕ}
    (hn : 14 ≤ n) (hm : m ≤ 3) (hR : R < 2 * a)
    (haggregate : n + 2 * a ≤ R + 8 + m ∨
      2 * n + 8 * a ≤ 3 * R + 21 + 3 * m) : False := by
  rcases haggregate with haggregate | haggregate <;> omega

/-- Arithmetic endpoint shared by Claim 5.3 and the first assertion of Claim
5.7.  `k` counts the vertices whose residual contribution has saturated at
`a`; the degree-sum argument forces the displayed aggregate lower bound. -/
lemma d7_claim53_arithmetic {n a m k R : ℕ}
    (hn : 14 ≤ n) (hm : 4 ≤ m) (hk : k ≤ 1) (hR : R < 2 * a)
    (haggregate : (3 - k) * n + (6 + 2 * k) * a + 3 * m ≤
      3 * R + 24 - 3 * k) : False := by
  interval_cases k <;> norm_num at haggregate ⊢ <;> omega

/-- Strengthened arithmetic endpoint in Claim 5.7.  When `a = 4` and
`3m ≥ n - 7`, at most three vertices can saturate the residual allowance;
the degree-sum estimate rules out total residual at most `2a+5`. -/
lemma d8_claim57_strong_arithmetic {n a k R : ℕ}
    (hn : 14 ≤ n) (ha : a = 4) (hk : k ≤ 3) (hR : R ≤ 2 * a + 5)
    (haggregate : 2 * k * a + (4 - k) * n + 3 * k + 6 * a ≤
      3 * R + 31) : False := by
  subst a
  interval_cases k <;> norm_num at haggregate ⊢ <;> omega

/-- The high-defect-vertex count used in the rho-equals-six branch of
Claim 5.8.  The printed prose says "at most eight", but the displayed
degree-sum calculation actually rules out a set of eight and hence proves
the seven-vertex bound needed for the subsequent fourteen-unit allocation. -/
lemma d8_highDefectSet_card_le_seven
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (d : ι → ℕ) (S : Finset ι)
    (hn : 14 ≤ n) (htotal : ∑ u, d u = 2 * n)
    (hhigh : ∀ u ∈ S, n - 2 ≤ 3 * d u) :
    S.card ≤ 7 := by
  by_contra hcard
  have hcard8 : 8 ≤ S.card := by omega
  have hlocal : S.card * (n - 2) ≤ 3 * ∑ u ∈ S, d u := by
    calc
      S.card * (n - 2) = ∑ _u ∈ S, (n - 2) := by simp
      _ ≤ ∑ u ∈ S, 3 * d u :=
        Finset.sum_le_sum fun u hu ↦ hhigh u hu
      _ = 3 * ∑ u ∈ S, d u := by
        rw [Finset.mul_sum]
  have hsub : (∑ u ∈ S, d u) ≤ ∑ u, d u :=
    Finset.sum_le_univ_sum_of_nonneg fun u ↦ Nat.zero_le (d u)
  have hbound : 8 * (n - 2) ≤ 6 * n := by
    calc
      8 * (n - 2) ≤ S.card * (n - 2) :=
        Nat.mul_le_mul_right (n - 2) hcard8
      _ ≤ 3 * ∑ u ∈ S, d u := hlocal
      _ ≤ 3 * ∑ u, d u := Nat.mul_le_mul_left 3 hsub
      _ = 6 * n := by rw [htotal]; omega
  omega

/-- A finite family of natural capacities can realize every total up to its
sum.  This elementary allocation lemma is used to impose the lower bounds on
the distinguished vertices in Claim 5.8. -/
private lemma exists_boundedAssignment_on_finset
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (r : ι → ℕ) {t : ℕ}
    (ht : t ≤ ∑ u ∈ s, r u) :
    ∃ sigma : ι → ℕ,
      (∀ u ∈ s, sigma u ≤ r u) ∧
      ∑ u ∈ s, sigma u = t := by
  induction s using Finset.induction_on generalizing t with
  | empty =>
      have ht0 : t = 0 := by simpa using ht
      refine ⟨fun _ ↦ 0, ?_, ?_⟩
      · simp
      · simp [ht0]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha] at ht
      let x := min (r a) t
      have hxCapacity : x ≤ r a := min_le_left _ _
      have hremaining : t - x ≤ ∑ u ∈ s, r u := by
        dsimp only [x]
        by_cases htr : t ≤ r a
        · rw [min_eq_right htr]
          simp
        · rw [min_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge htr))]
          omega
      obtain ⟨sigma, hsigma, hsum⟩ :=
        ih (t := t - x) hremaining
      let tau : ι → ℕ := fun u ↦ if u = a then x else sigma u
      refine ⟨tau, ?_, ?_⟩
      · intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu
        · simpa [tau] using hxCapacity
        · have hua : u ≠ a := by
            intro hua
            subst u
            exact ha hu
          simpa [tau, hua] using hsigma u hu
      · rw [Finset.sum_insert ha]
        have hsumTau :
            (∑ u ∈ s, tau u) = ∑ u ∈ s, sigma u := by
          apply Finset.sum_congr rfl
          intro u hu
          have hua : u ≠ a := by
            intro hua
            subst u
            exact ha hu
          simp [tau, hua]
        rw [hsumTau, hsum]
        simp only [tau, if_pos]
        omega

/-- The exact fourteen-unit assignment used in the rho-equals-six branch of
Claim 5.8: every high-defect vertex receives at least two units, no vertex
exceeds its allowance, and the total is fourteen. -/
lemma exists_d8_sigma_assignment
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι → ℕ) (S : Finset ι)
    (hcard : S.card ≤ 7)
    (hhigh : ∀ u ∈ S, 2 ≤ r u)
    (htotal : 14 ≤ ∑ u, r u) :
    ∃ sigma : ι → ℕ,
      (∀ u, sigma u ≤ r u) ∧
      (∀ u ∈ S, 2 ≤ sigma u) ∧
      ∑ u, sigma u = 14 := by
  let base : ι → ℕ := fun u ↦ if u ∈ S then 2 else 0
  have hbase : ∀ u, base u ≤ r u := by
    intro u
    by_cases hu : u ∈ S
    · simpa [base, hu] using hhigh u hu
    · simp [base, hu]
  have hbaseSum : (∑ u, base u) = S.card * 2 := by
    simp [base]
  have hbaseTotal : (∑ u, base u) ≤ 14 := by
    rw [hbaseSum]
    omega
  let capacity : ι → ℕ := fun u ↦ r u - base u
  have hsumSplit :
      (∑ u, capacity u) + ∑ u, base u = ∑ u, r u := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    exact Nat.sub_add_cancel (hbase u)
  have hremaining :
      14 - ∑ u, base u ≤ ∑ u, capacity u := by
    omega
  obtain ⟨delta, hdelta, hdeltaSum⟩ :=
    exists_boundedAssignment_on_finset
      (Finset.univ : Finset ι) capacity hremaining
  let sigma : ι → ℕ := fun u ↦ base u + delta u
  refine ⟨sigma, ?_, ?_, ?_⟩
  · intro u
    have hdu := hdelta u (Finset.mem_univ u)
    have hbu := hbase u
    dsimp only [capacity] at hdu
    dsimp only [sigma]
    omega
  · intro u hu
    have hbu : base u = 2 := by simp [base, hu]
    dsimp only [sigma]
    omega
  · have hdeltaSum' : (∑ u, delta u) =
        14 - ∑ u, base u := by
      simpa using hdeltaSum
    dsimp only [sigma]
    rw [Finset.sum_add_distrib, hdeltaSum']
    omega

/-- Whole-set Hall arithmetic in the small-universal-set branch of Claim
5.8, where rho is zero. -/
lemma d8_claim58_whole_zero_arithmetic {n m : ℕ}
    (hsmall : 3 * m ≤ n - 8) :
    4 * m ≤ n + m - 8 := by
  omega

/-- The quadratic comparison used in the rho-equals-six whole-set Hall
branch.  It is the precise monotonicity calculation hidden in the paper's
sentence that the relevant quadratic is maximized at beta equal to two. -/
lemma d8_claim58_beta_quadratic
    {n m : ℕ} {beta : ℝ}
    (hn : 14 ≤ n) (hbeta₀ : 0 ≤ beta) (hbeta₂ : beta ≤ 2)
    (hfail : 3 * (m : ℝ) < (n : ℝ) + 4 - 3 * beta) :
    3 * (m : ℝ) * beta < 2 * ((n : ℝ) - 2) := by
  have hnR : (14 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases hbeta : beta = 0
  · subst beta
    norm_num
    nlinarith
  · have hbetaPos : 0 < beta := lt_of_le_of_ne hbeta₀ (Ne.symm hbeta)
    have hmul := mul_lt_mul_of_pos_right hfail hbetaPos
    have hfactor :
        0 ≤ (2 - beta) * ((n : ℝ) - 3 * beta - 2) :=
      mul_nonneg (by linarith) (by nlinarith)
    have hquad :
        beta * ((n : ℝ) + 4 - 3 * beta) ≤
          2 * ((n : ℝ) - 2) := by
      nlinarith
    nlinarith

/-- Singleton Hall arithmetic for rho equal to zero. -/
lemma d8_claim58_singleton_zero_arithmetic {n : ℕ} (hn : 14 ≤ n) :
    0 ≤ (2 * (n : ℝ) - 25) / 3 := by
  have hnR : (14 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_nonneg (by linarith) (by norm_num)

/-- Singleton Hall arithmetic for rho equal to six after assigning two
units to each high-defect vertex. -/
lemma d8_claim58_singleton_six_arithmetic {n : ℕ} (hn : 14 ≤ n) :
    0 ≤ (2 * (n : ℝ) - 28) / 3 := by
  have hnR : (14 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_nonneg (by linarith) (by norm_num)

/-! ## Universal-vertex bookkeeping -/

/-- Vertices incident with no missing edge. -/
def universalVertices (G : SimpleGraph A) : Finset A :=
  Finset.univ.filter fun u ↦ Gᶜ.degree u = 0

/-- Vertices incident with at least one missing edge. -/
def nonUniversalVertices (G : SimpleGraph A) : Finset A :=
  Finset.univ.filter fun u ↦ 0 < Gᶜ.degree u

@[simp] lemma mem_universalVertices {G : SimpleGraph A} {u : A} :
    u ∈ universalVertices G ↔ Gᶜ.degree u = 0 := by
  simp [universalVertices]

@[simp] lemma mem_nonUniversalVertices {G : SimpleGraph A} {u : A} :
    u ∈ nonUniversalVertices G ↔ 0 < Gᶜ.degree u := by
  simp [nonUniversalVertices]

/-- Universal and nonuniversal vertices partition the vertex set. -/
lemma card_nonUniversalVertices_add_card_universalVertices (G : SimpleGraph A) :
    (nonUniversalVertices G).card + (universalVertices G).card =
      Fintype.card A := by
  classical
  have hdisj : Disjoint (nonUniversalVertices G) (universalVertices G) := by
    rw [Finset.disjoint_left]
    intro u hu hn
    rw [mem_nonUniversalVertices] at hu
    rw [mem_universalVertices] at hn
    omega
  have hunion : nonUniversalVertices G ∪ universalVertices G = Finset.univ := by
    ext u
    simp only [Finset.mem_union, mem_nonUniversalVertices,
      mem_universalVertices, Finset.mem_univ, iff_true]
    omega
  calc
    (nonUniversalVertices G).card + (universalVertices G).card =
        (nonUniversalVertices G ∪ universalVertices G).card :=
      (Finset.card_union_of_disjoint hdisj).symm
    _ = Fintype.card A := by rw [hunion, Finset.card_univ]

/-- The complement-degree sum may be restricted to nonuniversal vertices,
and is twice the number of missing edges. -/
lemma sum_nonUniversalVertices_compl_degree (G : SimpleGraph A) :
    ∑ u ∈ nonUniversalVertices G, Gᶜ.degree u =
      2 * missingEdgeCount G := by
  classical
  have hsum : (∑ u ∈ nonUniversalVertices G, Gᶜ.degree u) =
      ∑ u : A, Gᶜ.degree u := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro u _ hu
    have hzero : Gᶜ.degree u = 0 := by
      by_contra hne
      exact hu (mem_nonUniversalVertices.mpr (Nat.pos_of_ne_zero hne))
    simp [hzero]
  rw [hsum, SimpleGraph.sum_degrees_eq_twice_card_edges]
  unfold missingEdgeCount
  rfl

/-- The residual allowance used in the large-universal-set branch D7. -/
def d7ResidualAllowance (G : SimpleGraph A) (a : ℕ) (u : A) : ℕ :=
  min a (Gᶜ.degree u - 1)

/-- Vertices at which the D7 residual allowance saturates at `a`. -/
def d7SaturatedVertices (G : SimpleGraph A) (a : ℕ) : Finset A :=
  (nonUniversalVertices G).filter fun u ↦ a + 1 ≤ Gᶜ.degree u

/-- Claim 5.3 in graph form.  In D7 the capped residual allowances over the
nonuniversal vertices have total at least `2a`. -/
theorem d7_claim53 {n a : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n) (ha : a < 4)
    (G : SimpleGraph A)
    (hexact : missingEdgeCount G = n - 4 + a)
    (hm : 4 ≤ (universalVertices G).card)
    (hnoD5 : ∀ u : A, 3 * Gᶜ.degree u ≤ n + a) :
    2 * a ≤ ∑ u ∈ nonUniversalVertices G,
      d7ResidualAllowance G a u := by
  classical
  let U := nonUniversalVertices G
  let m := (universalVertices G).card
  let K := d7SaturatedVertices G a
  let k := K.card
  let R := ∑ u ∈ U, d7ResidualAllowance G a u
  let c := n - 2 * a - 3
  have hc : 2 * a + 3 ≤ n := by omega
  have hclass : ∀ u ∈ U,
      3 * Gᶜ.degree u ≤
        3 * d7ResidualAllowance G a u + 3 +
          (if u ∈ K then c else 0) := by
    intro u hu
    by_cases hs : a + 1 ≤ Gᶜ.degree u
    · have huK : u ∈ K := by
        exact Finset.mem_filter.mpr ⟨by simpa only [U] using hu, hs⟩
      have hr : d7ResidualAllowance G a u = a := by
        unfold d7ResidualAllowance
        rw [Nat.min_eq_left]
        omega
      rw [if_pos huK, hr]
      have hdu := hnoD5 u
      dsimp only [c]
      omega
    · have huK : u ∉ K := by
        intro h
        exact hs (Finset.mem_filter.mp h).2
      have hduPos : 0 < Gᶜ.degree u := by
        simpa only [U, mem_nonUniversalVertices] using hu
      have hr : d7ResidualAllowance G a u = Gᶜ.degree u - 1 := by
        unfold d7ResidualAllowance
        rw [Nat.min_eq_right]
        omega
      rw [if_neg huK, hr]
      omega
  have hindicator :
      (∑ u ∈ U, if u ∈ K then c else 0) = k * c := by
    have hfilter : U.filter (fun u ↦ u ∈ K) = K := by
      ext u
      simp [U, K, d7SaturatedVertices]
    rw [← Finset.sum_filter]
    rw [hfilter]
    simp only [k, Finset.sum_const, Nat.nsmul_eq_mul]
  have hsumUpper :
      (∑ u ∈ U, 3 * Gᶜ.degree u) ≤
        3 * R + 3 * U.card + k * c := by
    calc
      (∑ u ∈ U, 3 * Gᶜ.degree u) ≤
          ∑ u ∈ U, (3 * d7ResidualAllowance G a u + 3 +
            (if u ∈ K then c else 0)) :=
        Finset.sum_le_sum fun u hu ↦ hclass u hu
      _ = 3 * R + 3 * U.card + k * c := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_const, Nat.nsmul_eq_mul, R, hindicator]
        omega
  have hsumDegrees :
      6 * (n - 4 + a) ≤ 3 * R + 3 * U.card + k * c := by
    have heq : (∑ u ∈ U, 3 * Gᶜ.degree u) =
        6 * (n - 4 + a) := by
      rw [← Finset.mul_sum]
      simp only [U, sum_nonUniversalVertices_compl_degree, hexact]
      omega
    rw [← heq]
    exact hsumUpper
  by_contra hres
  have hR : R < 2 * a := by
    simpa only [R, U] using Nat.lt_of_not_ge hres
  have hKa : k * a ≤ R := by
    calc
      k * a = ∑ _u ∈ K, a := by simp [k]
      _ = ∑ u ∈ K, d7ResidualAllowance G a u := by
        apply Finset.sum_congr rfl
        intro u hu
        unfold d7ResidualAllowance
        rw [Nat.min_eq_left]
        have hs := (Finset.mem_filter.mp hu).2
        omega
      _ ≤ ∑ u ∈ U, d7ResidualAllowance G a u := by
        apply Finset.sum_le_sum_of_subset
        exact (Finset.filter_subset _ _)
      _ = R := rfl
  have hk : k ≤ 1 := by
    by_cases ha0 : a = 0
    · subst a
      simp at hR
    · interval_cases a <;> omega
  have hpart : U.card + m = n := by
    simpa only [U, m, hcard] using
      card_nonUniversalVertices_add_card_universalVertices G
  have haggregate :
      (3 - k) * n + (6 + 2 * k) * a + 3 * m ≤
        3 * R + 24 - 3 * k := by
    have hsumDegrees' :
        6 * (n - 4 + a) ≤
          3 * R + 3 * U.card + k * (n - 2 * a - 3) := by
      simpa only [c] using hsumDegrees
    interval_cases k <;> simp_all only [Nat.zero_mul, Nat.mul_zero,
      Nat.add_zero, Nat.sub_zero, Nat.one_mul, Nat.mul_one]
    all_goals omega
  exact d7_claim53_arithmetic hn hm hk hR haggregate

/-- The allocation form of Claim 5.3: choose exactly `2a` units of residual
mass, respecting every vertexwise D7 allowance and using only nonuniversal
vertices. -/
theorem exists_d7ResidualAllocation {n a : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n) (ha : a < 4)
    (G : SimpleGraph A)
    (hexact : missingEdgeCount G = n - 4 + a)
    (hm : 4 ≤ (universalVertices G).card)
    (hnoD5 : ∀ u : A, 3 * Gᶜ.degree u ≤ n + a) :
    ∃ sigma : A → ℕ,
      (∀ u, sigma u ≤ d7ResidualAllowance G a u) ∧
      (∀ u ∉ nonUniversalVertices G, sigma u = 0) ∧
      ∑ u ∈ nonUniversalVertices G, sigma u = 2 * a := by
  classical
  let U := nonUniversalVertices G
  have htotal : 2 * a ≤ ∑ u ∈ U, d7ResidualAllowance G a u := by
    simpa only [U] using d7_claim53 hcard hn ha G hexact hm hnoD5
  obtain ⟨tau, htau, hsum⟩ :=
    exists_boundedAssignment_on_finset U (d7ResidualAllowance G a) htotal
  let sigma : A → ℕ := fun u ↦ if u ∈ U then tau u else 0
  refine ⟨sigma, ?_, ?_, ?_⟩
  · intro u
    by_cases hu : u ∈ U
    · simpa only [sigma, if_pos hu] using htau u hu
    · simp only [sigma, if_neg hu, Nat.zero_le]
  · intro u hu
    simp only [sigma, U, if_neg hu]
  · calc
      ∑ u ∈ nonUniversalVertices G, sigma u = ∑ u ∈ U, tau u := by
        apply Finset.sum_congr (by rfl)
        intro u hu
        simp only [sigma, if_pos hu]
      _ = 2 * a := hsum

/-- Nonuniversal vertices incident with at least three missing edges. -/
def highMissingVertices (G : SimpleGraph A) : Finset A :=
  Finset.univ.filter fun u ↦ 3 ≤ Gᶜ.degree u

/-- Vertices incident with exactly two missing edges. -/
def twoMissingVertices (G : SimpleGraph A) : Finset A :=
  Finset.univ.filter fun u ↦ Gᶜ.degree u = 2

/-- Vertices incident with exactly one missing edge. -/
def oneMissingVertices (G : SimpleGraph A) : Finset A :=
  Finset.univ.filter fun u ↦ Gᶜ.degree u = 1

@[simp] lemma mem_highMissingVertices {G : SimpleGraph A} {u : A} :
    u ∈ highMissingVertices G ↔ 3 ≤ Gᶜ.degree u := by
  simp [highMissingVertices]

@[simp] lemma mem_twoMissingVertices {G : SimpleGraph A} {u : A} :
    u ∈ twoMissingVertices G ↔ Gᶜ.degree u = 2 := by
  simp [twoMissingVertices]

@[simp] lemma mem_oneMissingVertices {G : SimpleGraph A} {u : A} :
    u ∈ oneMissingVertices G ↔ Gᶜ.degree u = 1 := by
  simp [oneMissingVertices]

/-- Claim 5.1 in graph form.  Once D5 has failed, the degree-sum formula
forces enough vertices of complement-degree at least three or exactly two
to supply the two matchings used in D6. -/
theorem d6_claim51 {n a : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n) (ha : a ≤ 4)
    (G : SimpleGraph A)
    (hexact : missingEdgeCount G = n - 4 + a)
    (hm : (universalVertices G).card ≤ 3)
    (hnoD5 : ∀ u : A, 3 * Gᶜ.degree u ≤ n + a) :
    (universalVertices G).card + 3 ≤
      2 * (highMissingVertices G).card + (twoMissingVertices G).card := by
  classical
  let m := (universalVertices G).card
  let k := (highMissingVertices G).card
  let ell := (twoMissingVertices G).card
  let r := (oneMissingVertices G).card
  have hclass (u : A) :
      3 * Gᶜ.degree u ≤
        (if 3 ≤ Gᶜ.degree u then n + a else 0) +
        (if Gᶜ.degree u = 2 then 6 else 0) +
        (if Gᶜ.degree u = 1 then 3 else 0) := by
    by_cases hhigh : 3 ≤ Gᶜ.degree u
    · have hne2 : Gᶜ.degree u ≠ 2 := by omega
      have hne1 : Gᶜ.degree u ≠ 1 := by omega
      simpa [hhigh, hne2, hne1] using hnoD5 u
    · have hle : Gᶜ.degree u ≤ 2 := by omega
      interval_cases hdu : Gᶜ.degree u <;> simp [hdu]
  have hsumUpper :
      ∑ u : A, 3 * Gᶜ.degree u ≤
        k * (n + a) + 6 * ell + 3 * r := by
    calc
      ∑ u : A, 3 * Gᶜ.degree u ≤
          ∑ u : A,
            ((if 3 ≤ Gᶜ.degree u then n + a else 0) +
            (if Gᶜ.degree u = 2 then 6 else 0) +
            (if Gᶜ.degree u = 1 then 3 else 0)) := by
        exact Finset.sum_le_sum fun u _ ↦ hclass u
      _ = k * (n + a) + 6 * ell + 3 * r := by
        simp only [Finset.sum_add_distrib]
        have hK : (∑ u : A, if 3 ≤ Gᶜ.degree u then n + a else 0) =
            k * (n + a) := by
          rw [← Finset.sum_filter]
          simp [k, highMissingVertices, mul_comm]
        have hL : (∑ u : A, if Gᶜ.degree u = 2 then 6 else 0) =
            6 * ell := by
          rw [← Finset.sum_filter]
          simp [ell, twoMissingVertices, mul_comm]
        have hR : (∑ u : A, if Gᶜ.degree u = 1 then 3 else 0) =
            3 * r := by
          rw [← Finset.sum_filter]
          simp [r, oneMissingVertices, mul_comm]
        rw [hK, hL, hR]
  have hpartition : m + r + ell + k = n := by
    have hpoint (u : A) :
        (if Gᶜ.degree u = 0 then 1 else 0) +
          (if Gᶜ.degree u = 1 then 1 else 0) +
          (if Gᶜ.degree u = 2 then 1 else 0) +
          (if 3 ≤ Gᶜ.degree u then 1 else 0) = 1 := by
      by_cases h0 : Gᶜ.degree u = 0
      · simp [h0]
      by_cases h1 : Gᶜ.degree u = 1
      · simp [h0, h1]
      by_cases h2 : Gᶜ.degree u = 2
      · simp [h0, h1, h2]
      have h3 : 3 ≤ Gᶜ.degree u := by omega
      simp [h0, h1, h2, h3]
    have hsumPoint :
        (∑ u : A,
          ((if Gᶜ.degree u = 0 then 1 else 0) +
          (if Gᶜ.degree u = 1 then 1 else 0) +
          (if Gᶜ.degree u = 2 then 1 else 0) +
          (if 3 ≤ Gᶜ.degree u then 1 else 0))) =
          ∑ _u : A, 1 := by
      exact Finset.sum_congr rfl
        (fun u (_ : u ∈ (Finset.univ : Finset A)) ↦ hpoint u)
    have h0sum : (∑ u : A, if Gᶜ.degree u = 0 then 1 else 0) = m := by
      rw [Finset.sum_boole]
      rfl
    have h1sum : (∑ u : A, if Gᶜ.degree u = 1 then 1 else 0) = r := by
      rw [Finset.sum_boole]
      rfl
    have h2sum : (∑ u : A, if Gᶜ.degree u = 2 then 1 else 0) = ell := by
      rw [Finset.sum_boole]
      rfl
    have h3sum : (∑ u : A, if 3 ≤ Gᶜ.degree u then 1 else 0) = k := by
      rw [Finset.sum_boole]
      rfl
    simpa only [Finset.sum_add_distrib, h0sum, h1sum, h2sum, h3sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard,
      Nat.cast_id]
      using hsumPoint
  have hdegree :
      6 * (n - 4 + a) + 3 * m + 3 * k ≤
        k * (n + a) + 3 * ell + 3 * n := by
    have hhandshake := Gᶜ.sum_degrees_eq_twice_card_edges
    have hmissingCard : Gᶜ.edgeFinset.card = missingEdgeCount G := by
      rfl
    have hsumEq : ∑ u : A, 3 * Gᶜ.degree u =
        6 * (n - 4 + a) := by
      calc
        ∑ u : A, 3 * Gᶜ.degree u =
            3 * ∑ u : A, Gᶜ.degree u := by rw [Finset.mul_sum]
        _ = 3 * (2 * Gᶜ.edgeFinset.card) := by rw [hhandshake]
        _ = 6 * (n - 4 + a) := by rw [hmissingCard, hexact]; omega
    rw [hsumEq] at hsumUpper
    omega
  by_contra hclaim
  have hsmall : 2 * k + ell ≤ m + 2 := by omega
  exact d6_claim51_arithmetic hn ha hm hsmall hdegree

private lemma d6_claim52_saturated_aggregate {n a m R B bv E : ℕ}
    (hn : 14 ≤ n) (hm : m ≤ 3)
    (hB : B = n - 8 + 2 * a - m) (hBsplit : B = bv + E)
    (hRsplit : R = a + E) (hbv : 3 * bv + 3 ≤ n + a) :
    2 * n + 8 * a ≤ 3 * R + 21 + 3 * m := by
  omega

/-- Claim 5.2 abstracted to the residual allowances produced by the two D6
matchings.  The identity for their total is the only place the matching
degrees enter the proof. -/
theorem d6_claim52_of_residuals {n a m : ℕ}
    (hn : 14 ≤ n) (hm : m ≤ 3) (G : SimpleGraph A)
    (hcard : Fintype.card A = n)
    (hmcard : (universalVertices G).card = m)
    (hnoD5 : ∀ u : A, 3 * Gᶜ.degree u ≤ n + a)
    (b : A → ℕ)
    (hbSum : ∑ u ∈ nonUniversalVertices G, b u = n - 8 + 2 * a - m)
    (hbDegree : ∀ u ∈ nonUniversalVertices G, b u + 1 ≤ Gᶜ.degree u) :
    2 * a ≤ ∑ u ∈ nonUniversalVertices G, min a (b u) := by
  classical
  let U := nonUniversalVertices G
  let R := ∑ u ∈ U, min a (b u)
  by_contra hR
  have hRlt : R < 2 * a := by
    have := Nat.lt_of_not_ge hR
    simpa only [R, U] using this
  by_cases hall : ∀ u ∈ U, b u ≤ a
  · have hReq : R = ∑ u ∈ U, b u := by
      dsimp only [R]
      apply Finset.sum_congr rfl
      intro u hu
      rw [min_eq_right (hall u hu)]
    have haggregate : n + 2 * a ≤ R + 8 + m := by
      have hbSum' : ∑ u ∈ U, b u = n - 8 + 2 * a - m := by
        simpa only [U] using hbSum
      omega
    exact d6_claim52_arithmetic hn hm hRlt (Or.inl haggregate)
  · push_neg at hall
    obtain ⟨v, hvU, hva⟩ := hall
    have hother : ∀ u ∈ U, u ≠ v → b u ≤ a := by
      intro u hu huv
      by_contra hua
      have hav : min a (b v) = a := min_eq_left (by omega)
      have hau : min a (b u) = a := min_eq_left (by omega)
      have hpair : min a (b v) + min a (b u) ≤ R := by
        have hsub : ({v, u} : Finset A) ⊆ U := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hvU
          · exact hu
        calc
          min a (b v) + min a (b u) =
              ∑ x ∈ ({v, u} : Finset A), min a (b x) := by
            simp [huv, huv.symm, add_comm]
          _ ≤ ∑ x ∈ U, min a (b x) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun _ _ _ ↦ Nat.zero_le _)
          _ = R := rfl
      rw [hav, hau] at hpair
      omega
    have hvMin : min a (b v) = a := min_eq_left (by omega)
    have hRsplit : R = a + ∑ u ∈ U.erase v, b u := by
      have hsumErase :
          ∑ u ∈ U.erase v, min a (b u) =
            ∑ u ∈ U.erase v, b u := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [min_eq_right]
        exact hother u (Finset.mem_of_mem_erase hu) (Finset.ne_of_mem_erase hu)
      dsimp only [R]
      rw [← Finset.sum_erase_add _ _ hvU, hvMin, hsumErase]
      exact Nat.add_comm _ _
    have hbSplit :
        ∑ u ∈ U, b u = b v + ∑ u ∈ U.erase v, b u := by
      simpa only [Nat.add_comm] using
        (Finset.sum_erase_add (s := U) (f := b) hvU).symm
    have hbSum' : ∑ u ∈ U, b u = n - 8 + 2 * a - m := by
      simpa only [U] using hbSum
    have hbvDegree : b v + 1 ≤ Gᶜ.degree v := by
      exact hbDegree v (by simpa only [U] using hvU)
    have hbvBound : 3 * b v + 3 ≤ n + a := by
      have := (Nat.mul_le_mul_left 3 hbvDegree).trans (hnoD5 v)
      omega
    have haggregate : 2 * n + 8 * a ≤ 3 * R + 21 + 3 * m := by
      exact d6_claim52_saturated_aggregate hn hm hbSum' hbSplit hRsplit hbvBound
    exact d6_claim52_arithmetic hn hm hRlt (Or.inr haggregate)

/-- The residual identity used to feed Claim 5.2.  Here `d₁,d₂` are
the degrees in the two D6 matchings and `b` is the uncapped residual
`d̄(u)-1-d₁(u)-d₂(u)`. -/
theorem d6_residual_identity_of_matching_degrees {n a m : ℕ}
    (hn : 14 ≤ n) (hm : m ≤ 3) (G : SimpleGraph A)
    (hcard : Fintype.card A = n)
    (hexact : missingEdgeCount G = n - 4 + a)
    (hmcard : (universalVertices G).card = m)
    (d₁ d₂ b : A → ℕ)
    (hdegree : ∀ u ∈ nonUniversalVertices G,
      Gᶜ.degree u = 1 + d₁ u + d₂ u + b u)
    (hmatchingSum : ∑ u ∈ nonUniversalVertices G, (d₁ u + d₂ u) = 2 * m) :
    (∑ u ∈ nonUniversalVertices G, b u = n - 8 + 2 * a - m) ∧
      ∀ u ∈ nonUniversalVertices G, b u + 1 ≤ Gᶜ.degree u := by
  classical
  let U := nonUniversalVertices G
  have hcardU : U.card + m = n := by
    have hpart := card_nonUniversalVertices_add_card_universalVertices G
    simpa only [U, hmcard, hcard] using hpart
  have hsumDegree : ∑ u ∈ U, Gᶜ.degree u = 2 * (n - 4 + a) := by
    simpa only [U, hexact] using sum_nonUniversalVertices_compl_degree G
  have hsumDecomp :
      ∑ u ∈ U, Gᶜ.degree u =
        U.card + ∑ u ∈ U, (d₁ u + d₂ u) + ∑ u ∈ U, b u := by
    calc
      ∑ u ∈ U, Gᶜ.degree u =
          ∑ u ∈ U, (1 + d₁ u + d₂ u + b u) := by
        apply Finset.sum_congr rfl
        intro u hu
        exact hdegree u (by simpa only [U] using hu)
      _ = U.card + ∑ u ∈ U, (d₁ u + d₂ u) +
          ∑ u ∈ U, b u := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
          mul_one, Nat.cast_id]
        omega
  have hsumMatch : ∑ u ∈ U, (d₁ u + d₂ u) = 2 * m := by
    simpa only [U] using hmatchingSum
  constructor
  · change (∑ u ∈ U, b u) = n - 8 + 2 * a - m
    rw [hsumDegree, hsumMatch] at hsumDecomp
    omega
  · intro u hu
    have huDegree := hdegree u hu
    omega

/-- For `|Z|≥2`, Claim 5.1 and the slot assignment produce the two
edge-disjoint target matchings used in D6.  High-missing vertices may occur
once in each matching; degree-two vertices occur at most once globally. -/
theorem exists_d6_target_maps_of_two_le (G : SimpleGraph A)
    (hm : (universalVertices G).card ≤ 3)
    (hZ2 : 2 ≤ (universalVertices G).card)
    (hclaim : (universalVertices G).card + 3 ≤
      2 * (highMissingVertices G).card + (twoMissingVertices G).card) :
    ∃ f₁ f₂ : (↑(universalVertices G)) → A,
      Function.Injective f₁ ∧ Function.Injective f₂ ∧
      (∀ z, f₁ z ∈ highMissingVertices G ∨
        f₁ z ∈ twoMissingVertices G) ∧
      (∀ z, f₂ z ∈ highMissingVertices G ∨
        f₂ z ∈ twoMissingVertices G) ∧
      (∀ z, f₁ z ≠ f₂ z) ∧
      ∀ z₁ z₂, f₁ z₁ ∈ twoMissingVertices G →
        f₂ z₂ ∈ twoMissingVertices G → f₁ z₁ ≠ f₂ z₂ := by
  classical
  let Z := ↑(universalVertices G)
  let K := ↑(highMissingVertices G)
  let L := ↑(twoMissingVertices G)
  obtain ⟨F, hFinj, hFcolor⟩ := exists_d6_slot_assignment
    (X := Z) (K := K) (L := L)
    (by simpa only [Z, Fintype.card_coe] using hm)
    (by simpa only [Z, K, L, Fintype.card_coe] using hclaim)
  let val : ((Fin 2 × K) ⊕ L) → A
    | Sum.inl p => p.2
    | Sum.inr l => l
  let f : Fin 2 → Z → A := fun i z ↦ val (F (i, z))
  have hKnotL (k : K) : (k : A) ∉ twoMissingVertices G := by
    intro hkL
    have hkHigh : 3 ≤ Gᶜ.degree (k : A) := by
      simpa only [K, mem_highMissingVertices] using k.property
    have hkTwo : Gᶜ.degree (k : A) = 2 := by
      simpa only [mem_twoMissingVertices] using hkL
    omega
  have hinj : ∀ i, Function.Injective (f i) := by
    intro i x y hxy
    have hxColor := hFcolor i x
    have hyColor := hFcolor i y
    rcases hx : F (i, x) with ⟨jx, kx⟩ | lx <;>
      rcases hy : F (i, y) with ⟨jy, ky⟩ | ly
    · simp only [hx, hy] at hxColor hyColor
      have hval : (kx : A) = (ky : A) := by
        simpa only [f, val, hx, hy] using hxy
      have hk : kx = ky := Subtype.ext hval
      have hslot : F (i, x) = F (i, y) := by
        rw [hx, hy, hxColor, hyColor, hk]
      exact congrArg Prod.snd (hFinj hslot)
    · have hval : (kx : A) = (ly : A) := by
        simpa only [f, val, hx, hy] using hxy
      have : (kx : A) ∈ twoMissingVertices G := by
        rw [hval]
        simpa only [L] using ly.property
      exact (hKnotL kx this).elim
    · have hval : (lx : A) = (ky : A) := by
        simpa only [f, val, hx, hy] using hxy
      have : (ky : A) ∈ twoMissingVertices G := by
        rw [← hval]
        simpa only [L] using lx.property
      exact (hKnotL ky this).elim
    · have hl : lx = ly := Subtype.ext (by
        simpa only [f, val, hx, hy] using hxy)
      have hslot : F (i, x) = F (i, y) := by rw [hx, hy, hl]
      exact congrArg Prod.snd (hFinj hslot)
  have hrange : ∀ i z, f i z ∈ highMissingVertices G ∨
      f i z ∈ twoMissingVertices G := by
    intro i z
    rcases hz : F (i, z) with ⟨j, k⟩ | l
    · left
      simpa only [f, val, hz, K] using k.property
    · right
      simpa only [f, val, hz, L] using l.property
  have hLcross : ∀ x y, f 0 x ∈ twoMissingVertices G →
      f 1 y ∈ twoMissingVertices G → f 0 x ≠ f 1 y := by
    intro x y hxL hyL hxy
    rcases hx : F (0, x) with ⟨jx, kx⟩ | lx
    · have hkL : (kx : A) ∈ twoMissingVertices G := by
        simpa only [f, val, hx] using hxL
      exact hKnotL kx hkL
    · rcases hy : F (1, y) with ⟨jy, ky⟩ | ly
      · have hkL : (ky : A) ∈ twoMissingVertices G := by
          simpa only [f, val, hy] using hyL
        exact hKnotL ky hkL
      · have hl : lx = ly := Subtype.ext (by
          simpa only [f, val, hx, hy] using hxy)
        have hslot : F (0, x) = F (1, y) := by rw [hx, hy, hl]
        have hp := congrArg Prod.fst (hFinj hslot)
        norm_num at hp
  obtain ⟨σ, hσ⟩ := exists_reindex_avoiding_injective
    (X := Z) (Y := A)
    (by simpa only [Z, Fintype.card_coe] using hZ2)
    (f 0) (f 1) (hinj 0) (hinj 1)
  let f₁ : Z → A := f 0
  let f₂ : Z → A := fun z ↦ f 1 (σ z)
  refine ⟨f₁, f₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hinj 0
  · exact (hinj 1).comp σ.injective
  · exact hrange 0
  · intro z
    exact hrange 1 (σ z)
  · intro z hEq
    exact hσ z hEq.symm
  · intro z₁ z₂ hz₁ hz₂
    exact hLcross z₁ (σ z₂) hz₁ hz₂

/-- Claim 5.1 supplies the two D6 target matchings for every possible
number `m ≤ 3` of universal vertices.  The preceding slot construction
handles `m = 2,3`.  For `m = 1`, its numerical conclusion says that the
union of the high-missing and degree-two classes contains two distinct
vertices; for `m = 0` the two maps have empty domain. -/
theorem exists_d6_target_maps (G : SimpleGraph A)
    (hm : (universalVertices G).card ≤ 3)
    (hclaim : (universalVertices G).card + 3 ≤
      2 * (highMissingVertices G).card + (twoMissingVertices G).card) :
    ∃ f₁ f₂ : (↑(universalVertices G)) → A,
      Function.Injective f₁ ∧ Function.Injective f₂ ∧
      (∀ z, f₁ z ∈ highMissingVertices G ∨
        f₁ z ∈ twoMissingVertices G) ∧
      (∀ z, f₂ z ∈ highMissingVertices G ∨
        f₂ z ∈ twoMissingVertices G) ∧
      (∀ z, f₁ z ≠ f₂ z) ∧
      ∀ z₁ z₂, f₁ z₁ ∈ twoMissingVertices G →
        f₂ z₂ ∈ twoMissingVertices G → f₁ z₁ ≠ f₂ z₂ := by
  classical
  by_cases hZ2 : 2 ≤ (universalVertices G).card
  · exact exists_d6_target_maps_of_two_le G hm hZ2 hclaim
  by_cases hZ0 : (universalVertices G).card = 0
  · have hZempty : universalVertices G = ∅ := Finset.card_eq_zero.mp hZ0
    let absurdVertex : ↑(universalVertices G) → False := fun z ↦ by
      have hz : (z : A) ∈ (∅ : Finset A) := by
        rw [← hZempty]
        exact z.property
      simpa using hz
    let f : ↑(universalVertices G) → A := fun z ↦ (absurdVertex z).elim
    refine ⟨f, f, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro z
      exact (absurdVertex z).elim
    · intro z
      exact (absurdVertex z).elim
    · intro z
      exact (absurdVertex z).elim
    · intro z
      exact (absurdVertex z).elim
    · intro z
      exact (absurdVertex z).elim
    · intro z
      exact (absurdVertex z).elim
  · have hZone : (universalVertices G).card = 1 := by omega
    have hdisj : Disjoint (highMissingVertices G) (twoMissingVertices G) := by
      rw [Finset.disjoint_left]
      intro x hxK hxL
      rw [mem_highMissingVertices] at hxK
      rw [mem_twoMissingVertices] at hxL
      omega
    have hUnionCard :
        (highMissingVertices G ∪ twoMissingVertices G).card =
          (highMissingVertices G).card + (twoMissingVertices G).card :=
      Finset.card_union_of_disjoint hdisj
    have hUnionTwo : 1 <
        (highMissingVertices G ∪ twoMissingVertices G).card := by
      rw [hUnionCard]
      omega
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hUnionTwo
    let f₁ : ↑(universalVertices G) → A := fun _ ↦ x
    let f₂ : ↑(universalVertices G) → A := fun _ ↦ y
    have hsubsingleton : Subsingleton (↑(universalVertices G)) :=
      Finset.card_le_one_iff_subsingleton_coe.mp (by omega)
    refine ⟨f₁, f₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro z w _
      exact hsubsingleton.elim z w
    · intro z w _
      exact hsubsingleton.elim z w
    · intro z
      simpa only [f₁, Finset.mem_union] using hx
    · intro z
      simpa only [f₂, Finset.mem_union] using hy
    · intro z
      simpa only [f₁, f₂] using hxy
    · intro z₁ z₂ _ _
      simpa only [f₁, f₂] using hxy

/-- The number of vertices of a finite source which a target map sends to a
given ambient vertex.  For the D6 maps this is the degree of that vertex in
the corresponding matching. -/
def d6TargetMultiplicity {X : Type*} [Fintype X]
    (f : X → A) (u : A) : ℕ :=
  (Finset.univ.filter fun x ↦ f x = u).card

lemma d6TargetMultiplicity_le_one {X : Type*} [Fintype X]
    {f : X → A} (hf : Function.Injective f) (u : A) :
    d6TargetMultiplicity f u ≤ 1 := by
  classical
  rw [d6TargetMultiplicity, Finset.card_le_one]
  intro x hx y hy
  exact hf ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)

lemma d6TargetMultiplicity_pos_iff {X : Type*} [Fintype X]
    (f : X → A) (u : A) :
    0 < d6TargetMultiplicity f u ↔ ∃ x, f x = u := by
  classical
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Finset.card_pos.mp h
    exact ⟨x, (Finset.mem_filter.mp hx).2⟩
  · rintro ⟨x, hx⟩
    apply Finset.card_pos.mpr
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩

/-- Summing target multiplicities over any finset containing the entire
range counts the source exactly once. -/
lemma sum_d6TargetMultiplicity {X : Type*} [Fintype X]
    (f : X → A) (S : Finset A) (hrange : ∀ x, f x ∈ S) :
    ∑ u ∈ S, d6TargetMultiplicity f u = Fintype.card X := by
  classical
  simp only [d6TargetMultiplicity, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  rw [Finset.sum_comm]
  calc
    (∑ x : X, ∑ u ∈ S, if f x = u then 1 else 0) =
        ∑ _x : X, 1 := by
      apply Finset.sum_congr rfl
      intro x _
      calc
        (∑ u ∈ S, if f x = u then 1 else 0) =
            (if f x = f x then 1 else 0) := by
          apply Finset.sum_eq_single (f x)
          · intro y hy hyne
            rw [if_neg]
            exact fun h ↦ hyne h.symm
          · exact fun h ↦ (h (hrange x)).elim
        _ = 1 := by simp
    _ = Fintype.card X := by simp

/-- The two target maps from Claim 5.1 have precisely the degree and total
incidence properties used in Claim 5.2.  The remaining value `b(u)` is the
nonnegative degree left after reserving one missing edge and the two matching
incidences. -/
theorem exists_d6_matching_degrees (G : SimpleGraph A)
    (hm : (universalVertices G).card ≤ 3)
    (hclaim : (universalVertices G).card + 3 ≤
      2 * (highMissingVertices G).card + (twoMissingVertices G).card) :
    ∃ d₁ d₂ b : A → ℕ,
      (∀ u ∈ nonUniversalVertices G,
        Gᶜ.degree u = 1 + d₁ u + d₂ u + b u) ∧
      (∑ u ∈ nonUniversalVertices G, (d₁ u + d₂ u) =
        2 * (universalVertices G).card) := by
  classical
  obtain ⟨f₁, f₂, hf₁, hf₂, hrange₁, hrange₂, hdistinct, hLcross⟩ :=
    exists_d6_target_maps G hm hclaim
  let d₁ : A → ℕ := d6TargetMultiplicity f₁
  let d₂ : A → ℕ := d6TargetMultiplicity f₂
  let b : A → ℕ := fun u ↦ Gᶜ.degree u - (1 + d₁ u + d₂ u)
  have hrangeU₁ : ∀ z, f₁ z ∈ nonUniversalVertices G := by
    intro z
    rcases hrange₁ z with hz | hz
    · exact mem_nonUniversalVertices.mpr
        (by have := mem_highMissingVertices.mp hz; omega)
    · exact mem_nonUniversalVertices.mpr
        (by have := mem_twoMissingVertices.mp hz; omega)
  have hrangeU₂ : ∀ z, f₂ z ∈ nonUniversalVertices G := by
    intro z
    rcases hrange₂ z with hz | hz
    · exact mem_nonUniversalVertices.mpr
        (by have := mem_highMissingVertices.mp hz; omega)
    · exact mem_nonUniversalVertices.mpr
        (by have := mem_twoMissingVertices.mp hz; omega)
  have hbound : ∀ u ∈ nonUniversalVertices G,
      1 + d₁ u + d₂ u ≤ Gᶜ.degree u := by
    intro u hu
    have hd₁ : d₁ u ≤ 1 := by
      simpa only [d₁] using d6TargetMultiplicity_le_one hf₁ u
    have hd₂ : d₂ u ≤ 1 := by
      simpa only [d₂] using d6TargetMultiplicity_le_one hf₂ u
    by_cases huK : u ∈ highMissingVertices G
    · have huDegree := mem_highMissingVertices.mp huK
      omega
    by_cases huL : u ∈ twoMissingVertices G
    · have huDegree := mem_twoMissingVertices.mp huL
      have hnotBoth : d₁ u = 0 ∨ d₂ u = 0 := by
        by_contra hne
        push Not at hne
        have hd₁pos : 0 < d₁ u := Nat.pos_of_ne_zero hne.1
        have hd₂pos : 0 < d₂ u := Nat.pos_of_ne_zero hne.2
        obtain ⟨z₁, hz₁⟩ := (d6TargetMultiplicity_pos_iff f₁ u).mp
          (by simpa only [d₁] using hd₁pos)
        obtain ⟨z₂, hz₂⟩ := (d6TargetMultiplicity_pos_iff f₂ u).mp
          (by simpa only [d₂] using hd₂pos)
        exact hLcross z₁ z₂ (hz₁.symm ▸ huL) (hz₂.symm ▸ huL)
          (hz₁.trans hz₂.symm)
      rcases hnotBoth with hd₁zero | hd₂zero <;> omega
    · have hd₁zero : d₁ u = 0 := by
        by_contra hne
        obtain ⟨z, hz⟩ := (d6TargetMultiplicity_pos_iff f₁ u).mp
          (by simpa only [d₁] using Nat.pos_of_ne_zero hne)
        rcases hrange₁ z with hzK | hzL
        · exact huK (hz.symm ▸ hzK)
        · exact huL (hz.symm ▸ hzL)
      have hd₂zero : d₂ u = 0 := by
        by_contra hne
        obtain ⟨z, hz⟩ := (d6TargetMultiplicity_pos_iff f₂ u).mp
          (by simpa only [d₂] using Nat.pos_of_ne_zero hne)
        rcases hrange₂ z with hzK | hzL
        · exact huK (hz.symm ▸ hzK)
        · exact huL (hz.symm ▸ hzL)
      have huDegree := mem_nonUniversalVertices.mp hu
      omega
  refine ⟨d₁, d₂, b, ?_, ?_⟩
  · intro u hu
    dsimp only [b]
    exact (Nat.add_sub_of_le (hbound u hu)).symm
  · rw [Finset.sum_add_distrib]
    have hsum₁ := sum_d6TargetMultiplicity f₁
      (nonUniversalVertices G) hrangeU₁
    have hsum₂ := sum_d6TargetMultiplicity f₂
      (nonUniversalVertices G) hrangeU₂
    change (∑ u ∈ nonUniversalVertices G, d6TargetMultiplicity f₁ u) +
      (∑ u ∈ nonUniversalVertices G, d6TargetMultiplicity f₂ u) =
        2 * (universalVertices G).card
    rw [hsum₁, hsum₂, Fintype.card_coe]
    omega

/-- Concrete graph-level closure of Claims 5.1 and 5.2.  If D5 fails and
there are at most three universal vertices, the two matchings can be chosen
so that the capped residual allowances have total at least `2a`.  This is
the numerical input consumed by the family of induced graphs in D6. -/
theorem exists_d6_matching_residuals {n a : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n) (ha : a ≤ 4)
    (G : SimpleGraph A)
    (hexact : missingEdgeCount G = n - 4 + a)
    (hm : (universalVertices G).card ≤ 3)
    (hnoD5 : ∀ u : A, 3 * Gᶜ.degree u ≤ n + a) :
    ∃ d₁ d₂ b : A → ℕ,
      (∀ u ∈ nonUniversalVertices G,
        Gᶜ.degree u = 1 + d₁ u + d₂ u + b u) ∧
      (∑ u ∈ nonUniversalVertices G, (d₁ u + d₂ u) =
        2 * (universalVertices G).card) ∧
      (∑ u ∈ nonUniversalVertices G, b u =
        n - 8 + 2 * a - (universalVertices G).card) ∧
      (∀ u ∈ nonUniversalVertices G, b u + 1 ≤ Gᶜ.degree u) ∧
      2 * a ≤ ∑ u ∈ nonUniversalVertices G, min a (b u) := by
  classical
  have hclaim := d6_claim51 hcard hn ha G hexact hm hnoD5
  obtain ⟨d₁, d₂, b, hdegree, hmatchingSum⟩ :=
    exists_d6_matching_degrees G hm hclaim
  obtain ⟨hbSum, hbDegree⟩ := d6_residual_identity_of_matching_degrees
    hn hm G hcard hexact rfl d₁ d₂ b hdegree hmatchingSum
  have hresidual := d6_claim52_of_residuals hn hm G hcard rfl hnoD5 b
    hbSum hbDegree
  exact ⟨d₁, d₂, b, hdegree, hmatchingSum, hbSum, hbDegree, hresidual⟩

/-- Map-preserving form of the D6 matching and residual construction.  The
previous numerical interface records only the two degree functions; the
auxiliary graphs below need the actual target maps which realize them. -/
theorem exists_d6_target_maps_with_residuals {n a : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n) (ha : a ≤ 4)
    (G : SimpleGraph A)
    (hexact : missingEdgeCount G = n - 4 + a)
    (hm : (universalVertices G).card ≤ 3)
    (hnoD5 : ∀ u : A, 3 * Gᶜ.degree u ≤ n + a) :
    ∃ f₁ f₂ : (↑(universalVertices G)) → A, ∃ b : A → ℕ,
      Function.Injective f₁ ∧ Function.Injective f₂ ∧
      (∀ z, f₁ z ∈ nonUniversalVertices G) ∧
      (∀ z, f₂ z ∈ nonUniversalVertices G) ∧
      (∀ z, f₁ z ≠ f₂ z) ∧
      (∀ u ∈ nonUniversalVertices G,
        Gᶜ.degree u = 1 + d6TargetMultiplicity f₁ u +
          d6TargetMultiplicity f₂ u + b u) ∧
      2 * a ≤ ∑ u ∈ nonUniversalVertices G, min a (b u) := by
  classical
  have hclaim := d6_claim51 hcard hn ha G hexact hm hnoD5
  obtain ⟨f₁, f₂, hf₁, hf₂, hrange₁, hrange₂, hdistinct, hLcross⟩ :=
    exists_d6_target_maps G hm hclaim
  let d₁ : A → ℕ := d6TargetMultiplicity f₁
  let d₂ : A → ℕ := d6TargetMultiplicity f₂
  have hrangeU₁ : ∀ z, f₁ z ∈ nonUniversalVertices G := by
    intro z
    rcases hrange₁ z with hz | hz
    · exact mem_nonUniversalVertices.mpr
        (by have := mem_highMissingVertices.mp hz; omega)
    · exact mem_nonUniversalVertices.mpr
        (by have := mem_twoMissingVertices.mp hz; omega)
  have hrangeU₂ : ∀ z, f₂ z ∈ nonUniversalVertices G := by
    intro z
    rcases hrange₂ z with hz | hz
    · exact mem_nonUniversalVertices.mpr
        (by have := mem_highMissingVertices.mp hz; omega)
    · exact mem_nonUniversalVertices.mpr
        (by have := mem_twoMissingVertices.mp hz; omega)
  have hbound : ∀ u ∈ nonUniversalVertices G,
      1 + d₁ u + d₂ u ≤ Gᶜ.degree u := by
    intro u hu
    have hd₁ : d₁ u ≤ 1 := by
      simpa only [d₁] using d6TargetMultiplicity_le_one hf₁ u
    have hd₂ : d₂ u ≤ 1 := by
      simpa only [d₂] using d6TargetMultiplicity_le_one hf₂ u
    by_cases huK : u ∈ highMissingVertices G
    · have huDegree := mem_highMissingVertices.mp huK
      omega
    by_cases huL : u ∈ twoMissingVertices G
    · have huDegree := mem_twoMissingVertices.mp huL
      have hnotBoth : d₁ u = 0 ∨ d₂ u = 0 := by
        by_contra hne
        push Not at hne
        obtain ⟨z₁, hz₁⟩ := (d6TargetMultiplicity_pos_iff f₁ u).mp
          (by simpa only [d₁] using Nat.pos_of_ne_zero hne.1)
        obtain ⟨z₂, hz₂⟩ := (d6TargetMultiplicity_pos_iff f₂ u).mp
          (by simpa only [d₂] using Nat.pos_of_ne_zero hne.2)
        exact hLcross z₁ z₂ (hz₁.symm ▸ huL) (hz₂.symm ▸ huL)
          (hz₁.trans hz₂.symm)
      rcases hnotBoth with hd₁zero | hd₂zero <;> omega
    · have hd₁zero : d₁ u = 0 := by
        by_contra hne
        obtain ⟨z, hz⟩ := (d6TargetMultiplicity_pos_iff f₁ u).mp
          (by simpa only [d₁] using Nat.pos_of_ne_zero hne)
        rcases hrange₁ z with hzK | hzL
        · exact huK (hz.symm ▸ hzK)
        · exact huL (hz.symm ▸ hzL)
      have hd₂zero : d₂ u = 0 := by
        by_contra hne
        obtain ⟨z, hz⟩ := (d6TargetMultiplicity_pos_iff f₂ u).mp
          (by simpa only [d₂] using Nat.pos_of_ne_zero hne)
        rcases hrange₂ z with hzK | hzL
        · exact huK (hz.symm ▸ hzK)
        · exact huL (hz.symm ▸ hzL)
      have huDegree := mem_nonUniversalVertices.mp hu
      omega
  let b : A → ℕ := fun u ↦ Gᶜ.degree u - (1 + d₁ u + d₂ u)
  have hdegree : ∀ u ∈ nonUniversalVertices G,
      Gᶜ.degree u = 1 + d₁ u + d₂ u + b u := by
    intro u hu
    dsimp only [b]
    exact (Nat.add_sub_of_le (hbound u hu)).symm
  have hmatchingSum :
      ∑ u ∈ nonUniversalVertices G, (d₁ u + d₂ u) =
        2 * (universalVertices G).card := by
    rw [Finset.sum_add_distrib]
    have hsum₁ := sum_d6TargetMultiplicity f₁
      (nonUniversalVertices G) hrangeU₁
    have hsum₂ := sum_d6TargetMultiplicity f₂
      (nonUniversalVertices G) hrangeU₂
    change (∑ u ∈ nonUniversalVertices G, d6TargetMultiplicity f₁ u) +
      (∑ u ∈ nonUniversalVertices G, d6TargetMultiplicity f₂ u) =
        2 * (universalVertices G).card
    rw [hsum₁, hsum₂, Fintype.card_coe]
    omega
  obtain ⟨hbSum, hbDegree⟩ := d6_residual_identity_of_matching_degrees
    hn hm G hcard hexact rfl d₁ d₂ b hdegree hmatchingSum
  have hresidual := d6_claim52_of_residuals
    hn hm G hcard rfl hnoD5 b hbSum hbDegree
  refine ⟨f₁, f₂, b, hf₁, hf₂, hrangeU₁, hrangeU₂,
    hdistinct, ?_, hresidual⟩
  intro u hu
  simpa only [d₁, d₂] using hdegree u hu

/-! ## The corrected D6 deletion family

The sentence defining `G_u` on page 10 of the published PDF says to delete
the edge `uz` when `uz ∈ M₂`, immediately after deleting the vertex `u`.
Taken literally that edge deletion is redundant.  It also cannot produce the
displayed `+ d₂(u)` missing-edge term, and the claimed uniform edge
multiplicity `|U|-2` is then false.  The construction forced by both ensuing
calculations is the following: if `M₂` matches `z` to `u`, delete the `M₁`
edge incident with `z`.  Edge-disjointness ensures that this edge survives the
vertex deletions.  The definitions below encode this uniquely consistent
correction and the subsequent lemmas verify both calculations exactly.
-/

/-- Universal vertices deleted from `G_u` through their `M₁` edge. -/
def d6M1RemovedUniversals (G : SimpleGraph A)
    (f₁ : (↑(universalVertices G)) → A) (u : A) : Finset A :=
  (Finset.univ.filter fun z ↦ f₁ z = u).map (Function.Embedding.subtype _)

/-- The full vertex set removed from the corrected auxiliary graph `G_u`. -/
def d6RemovedVertices (G : SimpleGraph A)
    (f₁ : (↑(universalVertices G)) → A) (u : A) : Finset A :=
  insert u (d6M1RemovedUniversals G f₁ u)

/-- If `M₂` matches `z` to `u`, the corrected construction deletes the
`M₁` edge `z f₁(z)`. -/
def d6CorrectedDeletedEdges (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A) (u : A) :
    Finset (Sym2 A) :=
  (Finset.univ.filter fun z ↦ f₂ z = u).image
    (fun z : ↑(universalVertices G) ↦ s((z : A), f₁ z))

/-- Vertices retained by the corrected auxiliary graph. -/
def d6KeptVertices (G : SimpleGraph A)
    (f₁ : (↑(universalVertices G)) → A) (u : A) : Finset A :=
  Finset.univ \ d6RemovedVertices G f₁ u

/-- The actual finite graph to which induction is applied in D6. -/
def d6AuxGraph (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A) (u : A) :
    SimpleGraph (↑(d6KeptVertices G f₁ u)) :=
  (G.deleteEdges (d6CorrectedDeletedEdges G f₁ f₂ u :
    Set (Sym2 A))).induce (↑(d6KeptVertices G f₁ u) : Set A)

@[simp] lemma card_d6M1RemovedUniversals (G : SimpleGraph A)
    (f₁ : (↑(universalVertices G)) → A) (u : A) :
    (d6M1RemovedUniversals G f₁ u).card = d6TargetMultiplicity f₁ u := by
  classical
  rw [d6M1RemovedUniversals, Finset.card_map]
  rfl

/-- The auxiliary graph loses `1+d₁(u)` vertices. -/
lemma card_d6KeptVertices {n : ℕ} (hcard : Fintype.card A = n)
    (G : SimpleGraph A) (f₁ : (↑(universalVertices G)) → A) (u : A)
    (hu : u ∈ nonUniversalVertices G) :
    Fintype.card (↑(d6KeptVertices G f₁ u)) =
      n - 1 - d6TargetMultiplicity f₁ u := by
  classical
  have huNotRemoved : u ∉ d6M1RemovedUniversals G f₁ u := by
    intro hmem
    have huUniversal : u ∈ universalVertices G :=
      Finset.property_of_mem_map_subtype _ hmem
    have hpos := mem_nonUniversalVertices.mp hu
    have hzero := mem_universalVertices.mp huUniversal
    omega
  have hremovedCard : (d6RemovedVertices G f₁ u).card =
      1 + d6TargetMultiplicity f₁ u := by
    rw [d6RemovedVertices, Finset.card_insert_of_notMem huNotRemoved,
      card_d6M1RemovedUniversals]
    omega
  rw [Fintype.card_coe, d6KeptVertices,
    Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    hcard, hremovedCard]
  omega

private lemma d6M1EdgeMap_injective (G : SimpleGraph A)
    (f₁ : (↑(universalVertices G)) → A)
    (hrange₁ : ∀ z, f₁ z ∈ nonUniversalVertices G) :
    Function.Injective (fun z : ↑(universalVertices G) ↦
      s((z : A), f₁ z)) := by
  intro z w hzw
  rw [Sym2.eq_iff] at hzw
  rcases hzw with hstraight | hcross
  · exact Subtype.ext hstraight.1
  · have hzZero := mem_universalVertices.mp z.property
    have hwPos := mem_nonUniversalVertices.mp (hrange₁ w)
    have : (z : A) = f₁ w := hcross.1
    rw [this] at hzZero
    omega

/-- The corrected extra-edge set has cardinality exactly `d₂(u)`. -/
lemma card_d6CorrectedDeletedEdges (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A)
    (hrange₁ : ∀ z, f₁ z ∈ nonUniversalVertices G) (u : A) :
    (d6CorrectedDeletedEdges G f₁ f₂ u).card =
      d6TargetMultiplicity f₂ u := by
  classical
  rw [d6CorrectedDeletedEdges,
    Finset.card_image_of_injective _ (d6M1EdgeMap_injective G f₁ hrange₁)]
  rfl

private lemma complEdge_endpoint_not_universal (G : SimpleGraph A)
    {e : Sym2 A} (he : e ∈ Gᶜ.edgeSet) {x : A} (hx : x ∈ e) :
    x ∉ universalVertices G := by
  induction e using Sym2.inductionOn with
  | _ p q =>
      have hpq : Gᶜ.Adj p q := by
        simpa only [SimpleGraph.mem_edgeSet] using he
      simp only [Sym2.mem_iff] at hx
      intro hxUniversal
      have hxZero := mem_universalVertices.mp hxUniversal
      rcases hx with rfl | rfl
      · have hpos := hpq.degree_pos_left
        omega
      · have hpos := hpq.degree_pos_right
        omega

private lemma edgeSet_ncard_eq_edgeFinset_card_AC (G : SimpleGraph A) :
    G.edgeSet.ncard = G.edgeFinset.card := by
  classical
  let hs : G.edgeSet.Finite := Set.toFinite _
  rw [Set.ncard_eq_toFinset_card _ hs]
  congr 1
  ext e
  simp [SimpleGraph.mem_edgeFinset]

/-- Removing the `M₁`-matched universal vertex creates no new missing
edge; the only original missing edges lost from `G` are those incident with
the index vertex `u`. -/
lemma missingEdgeCount_induce_d6KeptVertices (G : SimpleGraph A)
    (f₁ : (↑(universalVertices G)) → A) (u : A) :
    missingEdgeCount (G.induce (↑(d6KeptVertices G f₁ u) : Set A)) =
      missingEdgeCount G - Gᶜ.degree u := by
  classical
  let S : Finset A := d6KeptVertices G f₁ u
  let T : Finset A := Finset.univ.erase u
  have hfilter :
      (Gᶜ.edgeFinset.filter fun e ↦ e.toFinset ⊆ S) =
        (Gᶜ.edgeFinset.filter fun e ↦ e.toFinset ⊆ T) := by
    ext e
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨he, hsub⟩
      refine ⟨he, ?_⟩
      intro x hx
      have hxS := hsub hx
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_univ x⟩
      intro hxu
      subst x
      exact (Finset.mem_sdiff.mp hxS).2
        (by simp [d6RemovedVertices])
    · rintro ⟨he, hsub⟩
      refine ⟨he, ?_⟩
      intro x hx
      have hxT := hsub hx
      have hxu : x ≠ u := (Finset.mem_erase.mp hxT).1
      have hxNotM1 : x ∉ d6M1RemovedUniversals G f₁ u := by
        intro hxM1
        have hxUniversal : x ∈ universalVertices G :=
          Finset.property_of_mem_map_subtype _ hxM1
        exact (complEdge_endpoint_not_universal G
          (SimpleGraph.mem_edgeFinset.mp he) (Sym2.mem_toFinset.mp hx)) hxUniversal
      simp only [S, d6KeptVertices, d6RemovedVertices,
        Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        not_or]
      exact ⟨hxu, hxNotM1⟩
  have hcardEdges :
      (Gᶜ.induce (↑S : Set A)).edgeFinset.card =
        (Gᶜ.induce (↑T : Set A)).edgeFinset.card := by
    calc
      (Gᶜ.induce (↑S : Set A)).edgeFinset.card =
          (Gᶜ.edgeFinset.filter fun e ↦ e.toFinset ⊆ S).card :=
        (Gᶜ.card_filter_edgeFinset_toFinset_subset S).symm
      _ = (Gᶜ.edgeFinset.filter fun e ↦ e.toFinset ⊆ T).card := by
        rw [hfilter]
      _ = (Gᶜ.induce (↑T : Set A)).edgeFinset.card :=
        Gᶜ.card_filter_edgeFinset_toFinset_subset T
  have hcardSet :
      Nat.card (Gᶜ.induce (↑S : Set A)).edgeSet =
        Nat.card (Gᶜ.induce (↑T : Set A)).edgeSet := by
    simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet] using
      hcardEdges
  have hmain :
      missingEdgeCount (G.induce (↑S : Set A)) =
        missingEdgeCount (G.induce (↑T : Set A)) := by
    calc
      missingEdgeCount (G.induce (↑S : Set A)) =
          Nat.card (G.induce (↑S : Set A))ᶜ.edgeSet :=
        missingEdgeCount_eq_compl_edgeSet_ncard _
      _ = Nat.card (Gᶜ.induce (↑S : Set A)).edgeSet := by
        rw [compl_induce]
      _ = Nat.card (Gᶜ.induce (↑T : Set A)).edgeSet := hcardSet
      _ = Nat.card (G.induce (↑T : Set A))ᶜ.edgeSet := by
        rw [compl_induce]
      _ = missingEdgeCount (G.induce (↑T : Set A)) :=
        (missingEdgeCount_eq_compl_edgeSet_ncard _).symm
  calc
    missingEdgeCount (G.induce (↑(d6KeptVertices G f₁ u) : Set A)) =
        missingEdgeCount (G.induce (↑T : Set A)) := by
      simpa only [S] using hmain
    _ = missingEdgeCount G - Gᶜ.degree u := by
      simpa only [T] using missingEdgeCount_induce_univ_erase G u

/-- Deleting a finite family `D` of surviving edges after restricting to a
vertex set adds exactly `|D|` missing edges. -/
lemma missingEdgeCount_deleteEdges_induce_add
    (G : SimpleGraph A) (S : Finset A) (D : Finset (Sym2 A))
    (hDG : D ⊆ G.edgeFinset) (hDS : ∀ e ∈ D, e.toFinset ⊆ S) :
    missingEdgeCount ((G.deleteEdges (D : Set (Sym2 A))).induce
      (↑S : Set A)) = missingEdgeCount (G.induce (↑S : Set A)) + D.card := by
  classical
  let H₀ : SimpleGraph S := G.induce (↑S : Set A)
  let H : SimpleGraph S := (G.deleteEdges (D : Set (Sym2 A))).induce
    (↑S : Set A)
  have hfilter :
      ((G.deleteEdges (D : Set (Sym2 A))).edgeFinset.filter
        fun e ↦ e.toFinset ⊆ S) =
      (G.edgeFinset.filter fun e ↦ e.toFinset ⊆ S) \ D := by
    ext e
    simp only [SimpleGraph.edgeFinset_deleteEdges, Finset.mem_filter,
      Finset.mem_sdiff]
    tauto
  have hDsub : D ⊆ G.edgeFinset.filter fun e ↦ e.toFinset ⊆ S := by
    intro e he
    exact Finset.mem_filter.mpr ⟨hDG he, hDS e he⟩
  have hcardEdges : H.edgeFinset.card + D.card = H₀.edgeFinset.card := by
    have hH := (G.deleteEdges (D : Set (Sym2 A))).card_filter_edgeFinset_toFinset_subset S
    have hH₀ := G.card_filter_edgeFinset_toFinset_subset S
    dsimp only [H, H₀]
    rw [← hH, hfilter, Finset.card_sdiff_of_subset hDsub, ← hH₀]
    exact Nat.sub_add_cancel (Finset.card_le_card hDsub)
  have hsum₀ := card_edges_add_missing H₀
  have hsum := card_edges_add_missing H
  rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
    SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hcardEdges
  dsimp only [H₀, H] at hcardEdges hsum₀ hsum
  omega

lemma d6CorrectedDeletedEdges_subset_edgeFinset (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A)
    (hrange₁ : ∀ z, f₁ z ∈ nonUniversalVertices G) (u : A) :
    d6CorrectedDeletedEdges G f₁ f₂ u ⊆ G.edgeFinset := by
  classical
  intro e he
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp he
  have hzUniversal : Gᶜ.degree (z : A) = 0 :=
    mem_universalVertices.mp z.property
  have hf₁Positive : 0 < Gᶜ.degree (f₁ z) :=
    mem_nonUniversalVertices.mp (hrange₁ z)
  have hne : (z : A) ≠ f₁ z := by
    intro h
    rw [← h] at hf₁Positive
    omega
  apply SimpleGraph.mem_edgeFinset.mpr
  change G.Adj (z : A) (f₁ z)
  by_contra hnot
  have hcomp : Gᶜ.Adj (z : A) (f₁ z) := ⟨hne, hnot⟩
  have hpos := hcomp.degree_pos_left
  omega

lemma d6CorrectedDeletedEdges_endpoints_kept (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A)
    (hrange₁ : ∀ z, f₁ z ∈ nonUniversalVertices G)
    (hrange₂ : ∀ z, f₂ z ∈ nonUniversalVertices G)
    (hdistinct : ∀ z, f₁ z ≠ f₂ z) (u : A) :
    ∀ e ∈ d6CorrectedDeletedEdges G f₁ f₂ u,
      e.toFinset ⊆ d6KeptVertices G f₁ u := by
  classical
  intro e he
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp he
  have hf₂u : f₂ z = u := (Finset.mem_filter.mp hz).2
  intro x hx
  have hxEnds : x = (z : A) ∨ x = f₁ z := by
    simpa only [Sym2.toFinset_mk_eq, Finset.mem_insert,
      Finset.mem_singleton] using hx
  rw [d6KeptVertices, Finset.mem_sdiff]
  refine ⟨Finset.mem_univ x, ?_⟩
  rw [d6RemovedVertices, Finset.mem_insert]
  push Not
  rcases hxEnds with hzx | hxf
  · subst x
    refine ⟨?_, ?_⟩
    · intro hzu
      have hzZero := mem_universalVertices.mp z.property
      have huPos := mem_nonUniversalVertices.mp (hrange₂ z)
      rw [hf₂u, ← hzu] at huPos
      omega
    · intro hzRemoved
      rw [d6M1RemovedUniversals, Finset.mem_map] at hzRemoved
      obtain ⟨w, hw, hwz⟩ := hzRemoved
      have hwTarget : f₁ w = u := (Finset.mem_filter.mp hw).2
      have hwEq : w = z := Subtype.ext hwz
      subst w
      exact hdistinct z (hwTarget.trans hf₂u.symm)
  · subst x
    refine ⟨?_, ?_⟩
    · intro hf₁u
      exact hdistinct z (hf₁u.trans hf₂u.symm)
    · intro hf₁Removed
      have hf₁Universal : f₁ z ∈ universalVertices G :=
        Finset.property_of_mem_map_subtype _ hf₁Removed
      have hzero := mem_universalVertices.mp hf₁Universal
      have hpos := mem_nonUniversalVertices.mp (hrange₁ z)
      omega

/-- Exact missing-edge formula for the corrected D6 auxiliary graph.  This
is the paper's displayed `n-4+a-d̄(u)+d₂(u)` identity before substituting
the exact missing count. -/
theorem missingEdgeCount_d6AuxGraph (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A)
    (hrange₁ : ∀ z, f₁ z ∈ nonUniversalVertices G)
    (hrange₂ : ∀ z, f₂ z ∈ nonUniversalVertices G)
    (hdistinct : ∀ z, f₁ z ≠ f₂ z) (u : A) :
    missingEdgeCount (d6AuxGraph G f₁ f₂ u) =
      missingEdgeCount G - Gᶜ.degree u + d6TargetMultiplicity f₂ u := by
  classical
  rw [d6AuxGraph,
    missingEdgeCount_deleteEdges_induce_add G
      (d6KeptVertices G f₁ u) (d6CorrectedDeletedEdges G f₁ f₂ u)
      (d6CorrectedDeletedEdges_subset_edgeFinset G f₁ f₂ hrange₁ u)
      (d6CorrectedDeletedEdges_endpoints_kept G f₁ f₂ hrange₁
        hrange₂ hdistinct u),
    missingEdgeCount_induce_d6KeptVertices,
    card_d6CorrectedDeletedEdges G f₁ f₂ hrange₁]

/-- After substituting the exact D6 degree decomposition, the corrected
auxiliary graph has precisely the missing-edge budget required by the
induction hypothesis. -/
theorem missingEdgeCount_d6AuxGraph_le_strongBudget {n a : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n) (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A) (b : A → ℕ)
    (hrange₁ : ∀ z, f₁ z ∈ nonUniversalVertices G)
    (hrange₂ : ∀ z, f₂ z ∈ nonUniversalVertices G)
    (hdistinct : ∀ z, f₁ z ≠ f₂ z)
    (hexact : missingEdgeCount G = n - 4 + a)
    (hdegree : ∀ u ∈ nonUniversalVertices G,
      Gᶜ.degree u = 1 + d6TargetMultiplicity f₁ u +
        d6TargetMultiplicity f₂ u + b u)
    (u : A) (hu : u ∈ nonUniversalVertices G) :
    missingEdgeCount (d6AuxGraph G f₁ f₂ u) ≤
      Fintype.card (↑(d6KeptVertices G f₁ u)) - 4 +
        (a - min a (b u)) := by
  have hdegreeLe : Gᶜ.degree u ≤ missingEdgeCount G := by
    simpa only [missingEdgeCount] using
      (Gᶜ.degree_le_card_edgeFinset (v := u))
  rw [hexact, hdegree u hu] at hdegreeLe
  rw [missingEdgeCount_d6AuxGraph G f₁ f₂ hrange₁ hrange₂
      hdistinct u,
    card_d6KeptVertices hcard G f₁ u hu, hexact, hdegree u hu]
  omega

/-- Each corrected D6 auxiliary graph is covered by one of the two local
induction hypotheses.  Injectivity of `f₁` makes its target multiplicity
either zero or one, so its order is respectively `n-1` or `n-2`. -/
theorem d6AuxGraph_hasStrongFractionalPacking {n a : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n) (ha : a ≤ 4)
    (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A) (b : A → ℕ)
    (hf₁ : Function.Injective f₁)
    (hrange₁ : ∀ z, f₁ z ∈ nonUniversalVertices G)
    (hrange₂ : ∀ z, f₂ z ∈ nonUniversalVertices G)
    (hdistinct : ∀ z, f₁ z ≠ f₂ z)
    (hexact : missingEdgeCount G = n - 4 + a)
    (hdegree : ∀ u ∈ nonUniversalVertices G,
      Gᶜ.degree u = 1 + d6TargetMultiplicity f₁ u +
        d6TargetMultiplicity f₂ u + b u)
    (hstrong₁ : AlmostCompleteStrongAt (n - 1))
    (hstrong₂ : AlmostCompleteStrongAt (n - 2))
    (u : A) (hu : u ∈ nonUniversalVertices G) :
    HasStrongFractionalPacking (d6AuxGraph G f₁ f₂ u)
      ((a - min a (b u) : ℕ) : ℝ) := by
  let d := a - min a (b u)
  have hd4 : d ≤ 4 := by
    dsimp only [d]
    omega
  have hmissing : missingEdgeCount (d6AuxGraph G f₁ f₂ u) ≤
      Fintype.card (↑(d6KeptVertices G f₁ u)) - 4 + d := by
    simpa only [d] using
      missingEdgeCount_d6AuxGraph_le_strongBudget hcard hn G f₁ f₂ b
        hrange₁ hrange₂ hdistinct hexact hdegree u hu
  have hd₁le : d6TargetMultiplicity f₁ u ≤ 1 :=
    d6TargetMultiplicity_le_one hf₁ u
  by_cases hd₁ : d6TargetMultiplicity f₁ u = 0
  · have horder : Fintype.card (↑(d6KeptVertices G f₁ u)) = n - 1 := by
      rw [card_d6KeptVertices hcard G f₁ u hu, hd₁]
      omega
    exact hstrong₁ _ horder d hd4 (d6AuxGraph G f₁ f₂ u)
      (by simpa only [horder] using hmissing)
  · have hd₁one : d6TargetMultiplicity f₁ u = 1 := by omega
    have horder : Fintype.card (↑(d6KeptVertices G f₁ u)) = n - 2 := by
      rw [card_d6KeptVertices hcard G f₁ u hu, hd₁one]
      omega
    exact hstrong₂ _ horder d hd4 (d6AuxGraph G f₁ f₂ u)
      (by simpa only [horder] using hmissing)

/-- Extending a packing by zero from a spanning subgraph to a supergraph
preserves feasibility. -/
lemma IsFractionalPacking.zeroExtendMono {H K : SimpleGraph A}
    (hHK : H ≤ K) {w : Finset A → ℝ} (hw : IsFractionalPacking H w) :
    IsFractionalPacking K (zeroExtendTriangleWeight H w) := by
  constructor
  · exact zeroExtendTriangleWeight_nonneg hHK hw
  · intro e he
    rw [fractionalEdgeLoad_zeroExtend hHK]
    by_cases heH : e ∈ H.edgeFinset
    · exact hw.edgeLoad_le_one heH
    · have heND : ¬ e.IsDiag := K.not_isDiag_of_mem_edgeFinset he
      rw [fractionalEdgeLoad_eq_zero_of_not_edge H w heND heH]
      norm_num

/-- Zero extension from a subgraph preserves total triangle weight. -/
lemma fractionalSize_zeroExtendTriangleWeight {H K : SimpleGraph A}
    (hHK : H ≤ K) (w : Finset A → ℝ) :
    fractionalSize K (zeroExtendTriangleWeight H w) =
      fractionalSize H w := by
  let sH := H.cliqueFinset 3
  let sK := K.cliqueFinset 3
  have hsub : sH ⊆ sK := by
    intro t ht
    exact SimpleGraph.cliqueFinset_mono K hHK ht
  unfold fractionalSize
  change (∑ t ∈ sK, zeroExtendTriangleWeight H w t) = ∑ t ∈ sH, w t
  calc
    (∑ t ∈ sK, zeroExtendTriangleWeight H w t) =
        ∑ t ∈ sH, zeroExtendTriangleWeight H w t := by
      symm
      apply sum_subset hsub
      intro t htK htH
      exact zeroExtendTriangleWeight_of_not_mem htH
    _ = ∑ t ∈ sH, w t := by
      apply sum_congr rfl
      intro t ht
      exact zeroExtendTriangleWeight_of_mem ht

/-- The corrected auxiliary graph is a subgraph of the graph induced on its
retained vertices. -/
lemma d6AuxGraph_le_induce (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A) (u : A) :
    d6AuxGraph G f₁ f₂ u ≤
      G.induce (↑(d6KeptVertices G f₁ u) : Set A) := by
  intro x y hxy
  exact hxy.1

/-- The corrected auxiliary graph, embedded back into the ambient vertex
set.  This is the support graph of the corresponding lifted weighting. -/
def d6AmbientAuxGraph (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A) (u : A) : SimpleGraph A :=
  (d6AuxGraph G f₁ f₂ u).map
    (inducedEmbedding (d6KeptVertices G f₁ u))

/-- Lift a corrected D6 auxiliary weighting to the ambient vertex set,
assigning zero to triples outside the auxiliary graph. -/
def d6LiftedWeight (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A) (u : A)
    (w : Finset (↑(d6KeptVertices G f₁ u)) → ℝ) : Finset A → ℝ :=
  extendInducedWeight (d6KeptVertices G f₁ u)
    (zeroExtendTriangleWeight (d6AuxGraph G f₁ f₂ u) w)

/-- A lifted D6 weighting vanishes on every triple outside its mapped
auxiliary graph. -/
lemma d6LiftedWeight_eq_zero_of_not_mem_ambient (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A) (u : A)
    (w : Finset (↑(d6KeptVertices G f₁ u)) → ℝ) (t : Finset A)
    (ht : t ∉ (d6AmbientAuxGraph G f₁ f₂ u).cliqueFinset 3) :
    d6LiftedWeight G f₁ f₂ u w t = 0 := by
  classical
  let S := d6KeptVertices G f₁ u
  by_cases hsub : t ⊆ S
  · let q : Finset S := restrictToInduced S t hsub
    have hmap : q.map (inducedEmbedding S) = t := by
      simpa only [q, restrictToInduced, inducedEmbedding] using
        (Finset.subtype_map_of_mem hsub)
    by_cases hq : q ∈ (d6AuxGraph G f₁ f₂ u).cliqueFinset 3
    · exfalso
      apply ht
      apply SimpleGraph.mem_cliqueFinset_iff.mpr
      rw [← hmap]
      exact (SimpleGraph.mem_cliqueFinset_iff.mp hq).map
    · unfold d6LiftedWeight
      rw [extendInducedWeight, dif_pos hsub]
      change zeroExtendTriangleWeight (d6AuxGraph G f₁ f₂ u) w q = 0
      exact zeroExtendTriangleWeight_of_not_mem hq
  · exact extendInducedWeight_eq_zero hsub

/-- Zero-extension from the mapped support graph leaves a lifted weighting
unchanged. -/
lemma zeroExtendTriangleWeight_d6AmbientAuxGraph (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A) (u : A)
    (w : Finset (↑(d6KeptVertices G f₁ u)) → ℝ) :
    zeroExtendTriangleWeight (d6AmbientAuxGraph G f₁ f₂ u)
        (d6LiftedWeight G f₁ f₂ u w) =
      d6LiftedWeight G f₁ f₂ u w := by
  funext t
  by_cases ht : t ∈ (d6AmbientAuxGraph G f₁ f₂ u).cliqueFinset 3
  · exact zeroExtendTriangleWeight_of_mem ht
  · rw [zeroExtendTriangleWeight_of_not_mem ht,
      d6LiftedWeight_eq_zero_of_not_mem_ambient G f₁ f₂ u w t ht]

lemma d6LiftedWeight_isFractionalPacking (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A) (u : A)
    {w : Finset (↑(d6KeptVertices G f₁ u)) → ℝ}
    (hw : IsFractionalPacking (d6AuxGraph G f₁ f₂ u) w) :
    IsFractionalPacking G (d6LiftedWeight G f₁ f₂ u w) := by
  unfold d6LiftedWeight
  apply IsFractionalPacking.extendInduced
  exact hw.zeroExtendMono (d6AuxGraph_le_induce G f₁ f₂ u)

lemma d6LiftedWeight_halfBounded (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A) (u : A)
    {w : Finset (↑(d6KeptVertices G f₁ u)) → ℝ}
    (hw : IsHalfBounded (d6AuxGraph G f₁ f₂ u) w) :
    IsHalfBounded G (d6LiftedWeight G f₁ f₂ u w) := by
  classical
  let S := d6KeptVertices G f₁ u
  have htop : IsHalfBounded
      (⊤ : SimpleGraph (↑(d6KeptVertices G f₁ u)))
      (zeroExtendTriangleWeight (d6AuxGraph G f₁ f₂ u) w) :=
    zeroExtendTriangleWeight_le_half le_top hw
  intro t ht
  have htNC : (⊤ : SimpleGraph A).IsNClique 3 t :=
    SimpleGraph.mem_cliqueFinset_iff.mp
      (SimpleGraph.cliqueFinset_mono (⊤ : SimpleGraph A) le_top ht)
  by_cases hsub : t ⊆ S
  · let q : Finset S := restrictToInduced S t hsub
    have hmap : q.map (inducedEmbedding S) = t := by
      simpa only [q, restrictToInduced, inducedEmbedding] using
        (Finset.subtype_map_of_mem hsub)
    have hcard : q.card = 3 := by
      have htcard : t.card = 3 := htNC.card_eq
      rw [← Finset.card_map (inducedEmbedding S), hmap]
      exact htcard
    have hqNC : (⊤ : SimpleGraph S).IsNClique 3 q := by
      refine ⟨?_, hcard⟩
      intro x hx y hy hxy
      simp only [SimpleGraph.top_adj]
      exact hxy
    unfold d6LiftedWeight
    rw [extendInducedWeight, dif_pos hsub]
    apply htop q
    simpa only [S, SimpleGraph.mem_cliqueFinset_iff] using hqNC
  · unfold d6LiftedWeight
    rw [extendInducedWeight_eq_zero hsub]
    norm_num

lemma fractionalSize_d6LiftedWeight (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A) (u : A)
    (w : Finset (↑(d6KeptVertices G f₁ u)) → ℝ) :
    fractionalSize G (d6LiftedWeight G f₁ f₂ u w) =
      fractionalSize (d6AuxGraph G f₁ f₂ u) w := by
  rw [d6LiftedWeight, fractionalSize_extendInducedWeight,
    fractionalSize_zeroExtendTriangleWeight
      (d6AuxGraph_le_induce G f₁ f₂ u)]

/-- An ambient edge survives in the corrected D6 auxiliary graph indexed by
`u` precisely when both endpoints survive the vertex deletion and it is not
the one corrected extra deletion.  Keeping this predicate on `Sym2 A` avoids
dependent subtype bookkeeping in the subsequent multiplicity count. -/
def d6EdgePresentAt (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A)
    (u : A) (e : Sym2 A) : Prop :=
  e.toFinset ⊆ d6KeptVertices G f₁ u ∧
    e ∉ d6CorrectedDeletedEdges G f₁ f₂ u

/-- On an original edge, membership in the mapped auxiliary graph is
exactly the explicit D6 survival predicate. -/
lemma d6AmbientAuxGraph_adj_iff (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A) (u x y : A)
    (hxy : G.Adj x y) :
    (d6AmbientAuxGraph G f₁ f₂ u).Adj x y ↔
      d6EdgePresentAt G f₁ f₂ u s(x, y) := by
  simp [d6AmbientAuxGraph, d6AuxGraph, d6EdgePresentAt,
    SimpleGraph.map_adj, Sym2.toFinset_mk_eq,
    Finset.insert_subset_iff, Finset.singleton_subset_iff, hxy,
    and_left_comm, and_comm, and_assoc]

/-- Every mapped auxiliary edge is an original edge. -/
lemma d6AmbientAuxGraph_le (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A) (u : A) :
    d6AmbientAuxGraph G f₁ f₂ u ≤ G := by
  intro x y hxy
  unfold d6AmbientAuxGraph at hxy
  rw [SimpleGraph.map_adj] at hxy
  obtain ⟨x', y', hxy', rfl, rfl⟩ := hxy
  exact SimpleGraph.induce_adj.mp
    (d6AuxGraph_le_induce G f₁ f₂ u hxy')

/-- The edge set of the mapped auxiliary graph is the explicit survival
filter on the original edge set. -/
lemma edgeFinset_d6AmbientAuxGraph (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A) (u : A) :
    (d6AmbientAuxGraph G f₁ f₂ u).edgeFinset =
      G.edgeFinset.filter fun e ↦ d6EdgePresentAt G f₁ f₂ u e := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      constructor
      · intro heA
        have heG : s(x, y) ∈ G.edgeFinset :=
          SimpleGraph.edgeFinset_mono (d6AmbientAuxGraph_le G f₁ f₂ u) heA
        have hxyG : G.Adj x y := by simpa using heG
        have hxyA : (d6AmbientAuxGraph G f₁ f₂ u).Adj x y := by
          simpa using heA
        exact Finset.mem_filter.mpr ⟨heG,
          (d6AmbientAuxGraph_adj_iff G f₁ f₂ u x y hxyG).mp hxyA⟩
      · intro he
        obtain ⟨heG, hp⟩ := Finset.mem_filter.mp he
        have hxyG : G.Adj x y := by simpa using heG
        have hxyA :=
          (d6AmbientAuxGraph_adj_iff G f₁ f₂ u x y hxyG).mpr hp
        simpa using hxyA

/-- Cardinal form of the preceding support identity, on the original
auxiliary vertex type. -/
lemma card_edgeFinset_d6AuxGraph (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A) (u : A) :
    (d6AuxGraph G f₁ f₂ u).edgeFinset.card =
      (G.edgeFinset.filter fun e ↦ d6EdgePresentAt G f₁ f₂ u e).card := by
  calc
    (d6AuxGraph G f₁ f₂ u).edgeFinset.card =
        (d6AmbientAuxGraph G f₁ f₂ u).edgeFinset.card := by
      rw [← edgeSet_ncard_eq_edgeFinset_card_AC,
        ← edgeSet_ncard_eq_edgeFinset_card_AC, d6AmbientAuxGraph,
        SimpleGraph.edgeSet_map,
        Set.ncard_image_of_injective _
          (inducedEmbedding (d6KeptVertices G f₁ u)).sym2Map.injective]
    _ = (G.edgeFinset.filter fun e ↦
        d6EdgePresentAt G f₁ f₂ u e).card := by
      rw [edgeFinset_d6AmbientAuxGraph]

/-- If an original edge is absent from an auxiliary graph, the lifted
weighting places no load on it. -/
lemma fractionalEdgeLoad_d6LiftedWeight_eq_zero_of_not_present
    (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A) (u : A)
    (w : Finset (↑(d6KeptVertices G f₁ u)) → ℝ)
    (e : Sym2 A) (heG : e ∈ G.edgeFinset)
    (he : ¬ d6EdgePresentAt G f₁ f₂ u e) :
    fractionalEdgeLoad G (d6LiftedWeight G f₁ f₂ u w) e = 0 := by
  have heND : ¬ e.IsDiag := G.not_isDiag_of_mem_edgeFinset heG
  rw [← zeroExtendTriangleWeight_d6AmbientAuxGraph,
    fractionalEdgeLoad_zeroExtend (d6AmbientAuxGraph_le G f₁ f₂ u)]
  apply fractionalEdgeLoad_eq_zero_of_not_edge _ _ heND
  intro heA
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxyG : G.Adj x y := by simpa using heG
      have hxyA : (d6AmbientAuxGraph G f₁ f₂ u).Adj x y := by
        simpa using heA
      exact he ((d6AmbientAuxGraph_adj_iff G f₁ f₂ u x y hxyG).mp hxyA)

/-- A lifted auxiliary packing contributes at most the indicator that the
given original edge survives in that auxiliary graph. -/
lemma fractionalEdgeLoad_d6LiftedWeight_le_indicator (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A) (u : A)
    {w : Finset (↑(d6KeptVertices G f₁ u)) → ℝ}
    (hw : IsFractionalPacking (d6AuxGraph G f₁ f₂ u) w)
    (e : Sym2 A) (heG : e ∈ G.edgeFinset) :
    fractionalEdgeLoad G (d6LiftedWeight G f₁ f₂ u w) e ≤
      if d6EdgePresentAt G f₁ f₂ u e then 1 else 0 := by
  by_cases he : d6EdgePresentAt G f₁ f₂ u e
  · rw [if_pos he]
    exact (d6LiftedWeight_isFractionalPacking G f₁ f₂ u hw).2 e heG
  · rw [if_neg he,
      fractionalEdgeLoad_d6LiftedWeight_eq_zero_of_not_present
        G f₁ f₂ u w e heG he]

lemma mem_d6KeptVertices_iff (G : SimpleGraph A)
    (f₁ : (↑(universalVertices G)) → A) (u x : A) :
    x ∈ d6KeptVertices G f₁ u ↔
      x ≠ u ∧ ∀ z : ↑(universalVertices G), f₁ z = u → (z : A) ≠ x := by
  classical
  rw [d6KeptVertices, Finset.mem_sdiff, d6RemovedVertices,
    Finset.mem_insert]
  simp only [Finset.mem_univ, true_and, not_or]
  constructor
  · rintro ⟨hxu, hxM⟩
    refine ⟨hxu, ?_⟩
    intro z hf₁ hzx
    apply hxM
    rw [d6M1RemovedUniversals, Finset.mem_map]
    exact ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ z, hf₁⟩, hzx⟩
  · rintro ⟨hxu, hx⟩
    refine ⟨hxu, ?_⟩
    intro hxM
    rw [d6M1RemovedUniversals, Finset.mem_map] at hxM
    obtain ⟨z, hz, hzx⟩ := hxM
    exact hx z (Finset.mem_filter.mp hz).2 hzx

lemma mem_d6CorrectedDeletedEdges_iff (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A)
    (u : A) (e : Sym2 A) :
    e ∈ d6CorrectedDeletedEdges G f₁ f₂ u ↔
      ∃ z : ↑(universalVertices G), f₂ z = u ∧ e = s((z : A), f₁ z) := by
  classical
  rw [d6CorrectedDeletedEdges, Finset.mem_image]
  constructor
  · rintro ⟨z, hz, hze⟩
    exact ⟨z, (Finset.mem_filter.mp hz).2, hze.symm⟩
  · rintro ⟨z, hf₂, rfl⟩
    exact ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ z, hf₂⟩, rfl⟩

private lemma nonUniversal_not_universal (G : SimpleGraph A) {x : A}
    (hx : x ∈ nonUniversalVertices G) : x ∉ universalVertices G := by
  intro hx0
  have hpos := mem_nonUniversalVertices.mp hx
  have hzero := mem_universalVertices.mp hx0
  omega

private lemma card_filter_ne_pair (S : Finset A) (x y : A)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    (S.filter fun u ↦ u ≠ x ∧ u ≠ y).card = S.card - 2 := by
  classical
  have hpair : ({x, y} : Finset A) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  rw [show S.filter (fun u ↦ u ≠ x ∧ u ≠ y) = S \ {x, y} by
    ext u
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton, not_or],
    Finset.card_sdiff_of_subset hpair]
  simp [hxy]

private lemma card_filter_of_iff_ne_pair (S : Finset A) (p : A → Prop)
    (x y : A) (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y)
    (hp : ∀ u ∈ S, p u ↔ u ≠ x ∧ u ≠ y) :
    (S.filter p).card = S.card - 2 := by
  classical
  rw [show S.filter p = S.filter (fun u ↦ u ≠ x ∧ u ≠ y) by
    apply Finset.filter_congr
    exact hp]
  exact card_filter_ne_pair S x y hx hy hxy

private lemma nonUniversal_mem_d6KeptVertices_iff (G : SimpleGraph A)
    (f₁ : (↑(universalVertices G)) → A) (u : A) {x : A}
    (hx : x ∈ nonUniversalVertices G) :
    x ∈ d6KeptVertices G f₁ u ↔ x ≠ u := by
  rw [mem_d6KeptVertices_iff]
  constructor
  · exact fun h ↦ h.1
  · intro hxu
    refine ⟨hxu, ?_⟩
    intro z _ hzx
    exact (nonUniversal_not_universal G hx) (hzx.symm ▸ z.property)

private lemma universal_mem_d6KeptVertices_iff (G : SimpleGraph A)
    (f₁ : (↑(universalVertices G)) → A) (u : A)
    (hu : u ∈ nonUniversalVertices G) (z : ↑(universalVertices G)) :
    (z : A) ∈ d6KeptVertices G f₁ u ↔ f₁ z ≠ u := by
  rw [mem_d6KeptVertices_iff]
  constructor
  · intro hz hf₁
    exact hz.2 z hf₁ rfl
  · intro hf₁
    refine ⟨?_, ?_⟩
    · intro hzu
      exact (nonUniversal_not_universal G hu) (hzu.symm ▸ z.property)
    · intro w hfw hwz
      apply hf₁
      rw [← hfw]
      exact (congrArg f₁ (Subtype.ext hwz)).symm

private lemma universal_nonUniversal_deleted_iff (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A)
    (hrange₁ : ∀ z, f₁ z ∈ nonUniversalVertices G)
    (z : ↑(universalVertices G)) {y u : A}
    (hy : y ∈ nonUniversalVertices G) :
    s((z : A), y) ∈ d6CorrectedDeletedEdges G f₁ f₂ u ↔
      y = f₁ z ∧ f₂ z = u := by
  constructor
  · intro hdel
    obtain ⟨w, hfw, heq⟩ := (mem_d6CorrectedDeletedEdges_iff
      G f₁ f₂ u s((z : A), y)).mp hdel
    rw [Sym2.eq_iff] at heq
    rcases heq with hstraight | hcross
    · have hwz : w = z := Subtype.ext hstraight.1.symm
      subst w
      exact ⟨hstraight.2, hfw⟩
    · have hzNonUniversal : (z : A) ∈ nonUniversalVertices G := by
        have hwRange := hrange₁ w
        rw [← hcross.1] at hwRange
        exact hwRange
      exact (nonUniversal_not_universal G hzNonUniversal z.property).elim
  · rintro ⟨rfl, hf₂⟩
    exact (mem_d6CorrectedDeletedEdges_iff
      G f₁ f₂ u s((z : A), f₁ z)).mpr ⟨z, hf₂, rfl⟩

private lemma universal_universal_not_deleted (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A)
    (hrange₁ : ∀ z, f₁ z ∈ nonUniversalVertices G)
    (z w : ↑(universalVertices G)) (u : A) :
    s((z : A), (w : A)) ∉ d6CorrectedDeletedEdges G f₁ f₂ u := by
  intro hdel
  obtain ⟨v, _, heq⟩ := (mem_d6CorrectedDeletedEdges_iff
    G f₁ f₂ u s((z : A), (w : A))).mp hdel
  rw [Sym2.eq_iff] at heq
  rcases heq with hstraight | hcross
  · have hwNonUniversal : (w : A) ∈ nonUniversalVertices G := by
      have hvRange := hrange₁ v
      rw [← hstraight.2] at hvRange
      exact hvRange
    exact nonUniversal_not_universal G hwNonUniversal w.property
  · have hzNonUniversal : (z : A) ∈ nonUniversalVertices G := by
      have hvRange := hrange₁ v
      rw [← hcross.1] at hvRange
      exact hvRange
    exact nonUniversal_not_universal G hzNonUniversal z.property

/-- If both endpoints are nonuniversal, the edge is absent precisely from
the two auxiliary graphs indexed by its endpoints. -/
lemma d6EdgePresentAt_nonUniversal_nonUniversal (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A)
    (hrange₁ : ∀ z, f₁ z ∈ nonUniversalVertices G)
    {x y u : A} (hx : x ∈ nonUniversalVertices G)
    (hy : y ∈ nonUniversalVertices G) :
    d6EdgePresentAt G f₁ f₂ u s(x, y) ↔ u ≠ x ∧ u ≠ y := by
  classical
  have hxKeep := nonUniversal_mem_d6KeptVertices_iff G f₁ u hx
  have hyKeep := nonUniversal_mem_d6KeptVertices_iff G f₁ u hy
  have hnotDeleted :
      s(x, y) ∉ d6CorrectedDeletedEdges G f₁ f₂ u := by
    intro hdel
    obtain ⟨z, _, heq⟩ := (mem_d6CorrectedDeletedEdges_iff
      G f₁ f₂ u s(x, y)).mp hdel
    rw [Sym2.eq_iff] at heq
    rcases heq with hstraight | hcross
    · have hxUniversal : x ∈ universalVertices G := by
        rw [hstraight.1]
        exact z.property
      exact (nonUniversal_not_universal G hx) hxUniversal
    · have hyUniversal : y ∈ universalVertices G := by
        rw [hcross.2]
        exact z.property
      exact (nonUniversal_not_universal G hy) hyUniversal
  simp only [d6EdgePresentAt, Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
    Finset.singleton_subset_iff, hxKeep, hyKeep, hnotDeleted, not_false_eq_true,
    and_true]
  tauto

/-- For a universal--nonuniversal edge which is not in `M₁`, the two
missing auxiliaries are indexed by the nonuniversal endpoint and by the
`M₁`-target of the universal endpoint. -/
lemma d6EdgePresentAt_universal_nonUniversal_ne (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A)
    (hrange₁ : ∀ z, f₁ z ∈ nonUniversalVertices G)
    (z : ↑(universalVertices G)) {y u : A}
    (hy : y ∈ nonUniversalVertices G) (hu : u ∈ nonUniversalVertices G)
    (hyf₁ : y ≠ f₁ z) :
    d6EdgePresentAt G f₁ f₂ u s((z : A), y) ↔
      u ≠ f₁ z ∧ u ≠ y := by
  classical
  have hzKeep := universal_mem_d6KeptVertices_iff G f₁ u hu z
  have hyKeep := nonUniversal_mem_d6KeptVertices_iff G f₁ u hy
  have hnotDeleted :
      s((z : A), y) ∉ d6CorrectedDeletedEdges G f₁ f₂ u := by
    rw [universal_nonUniversal_deleted_iff G f₁ f₂ hrange₁ z hy]
    exact fun h ↦ hyf₁ h.1
  simp only [d6EdgePresentAt, Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
    Finset.singleton_subset_iff, hzKeep, hyKeep, hnotDeleted,
    not_false_eq_true, and_true]
  tauto

/-- On an `M₁` edge, the correction adds the `M₂` target as the second
bad index; this is the exact point at which the published literal definition
would fail to have uniform multiplicity. -/
lemma d6EdgePresentAt_universal_M1 (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A)
    (hrange₁ : ∀ z, f₁ z ∈ nonUniversalVertices G)
    (z : ↑(universalVertices G)) {u : A}
    (hu : u ∈ nonUniversalVertices G) :
    d6EdgePresentAt G f₁ f₂ u s((z : A), f₁ z) ↔
      u ≠ f₁ z ∧ u ≠ f₂ z := by
  classical
  have hzKeep := universal_mem_d6KeptVertices_iff G f₁ u hu z
  have hf₁Keep := nonUniversal_mem_d6KeptVertices_iff G f₁ u (hrange₁ z)
  have hdeleted :
      (s((z : A), f₁ z) ∈ d6CorrectedDeletedEdges G f₁ f₂ u ↔
        f₂ z = u) := by
    rw [universal_nonUniversal_deleted_iff G f₁ f₂ hrange₁ z
      (hrange₁ z)]
    simp
  simp only [d6EdgePresentAt, Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
    Finset.singleton_subset_iff, hzKeep, hf₁Keep, hdeleted]
  tauto

/-- An edge with two universal endpoints is absent at the two corresponding
`M₁` targets. -/
lemma d6EdgePresentAt_universal_universal (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A)
    (hrange₁ : ∀ z, f₁ z ∈ nonUniversalVertices G)
    (z w : ↑(universalVertices G)) {u : A}
    (hu : u ∈ nonUniversalVertices G) :
    d6EdgePresentAt G f₁ f₂ u s((z : A), (w : A)) ↔
      u ≠ f₁ z ∧ u ≠ f₁ w := by
  classical
  have hzKeep := universal_mem_d6KeptVertices_iff G f₁ u hu z
  have hwKeep := universal_mem_d6KeptVertices_iff G f₁ u hu w
  have hnotDeleted := universal_universal_not_deleted
    G f₁ f₂ hrange₁ z w u
  simp only [d6EdgePresentAt, Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
    Finset.singleton_subset_iff, hzKeep, hwKeep, hnotDeleted,
    not_false_eq_true, and_true]
  tauto

/-- The corrected D6 family has the uniform edge multiplicity claimed in
Section 5: every original edge occurs in exactly `|U|-2` auxiliaries, where
`U` is the set of nonuniversal vertices indexing the family. -/
theorem card_filter_d6EdgePresentAt (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A)
    (hf₁ : Function.Injective f₁)
    (hrange₁ : ∀ z, f₁ z ∈ nonUniversalVertices G)
    (hrange₂ : ∀ z, f₂ z ∈ nonUniversalVertices G)
    (hdistinct : ∀ z, f₁ z ≠ f₂ z)
    (e : Sym2 A) (he : e ∈ G.edgeFinset) :
    ((nonUniversalVertices G).filter fun u ↦
      d6EdgePresentAt G f₁ f₂ u e).card =
        (nonUniversalVertices G).card - 2 := by
  classical
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy : x ≠ y := by
        have hnd := G.not_isDiag_of_mem_edgeFinset he
        simpa only [Sym2.mk_isDiag_iff] using hnd
      have nonUniversal_of_not_universal : ∀ {v : A},
          v ∉ universalVertices G → v ∈ nonUniversalVertices G := by
        intro v hv
        apply mem_nonUniversalVertices.mpr
        have hvne : Gᶜ.degree v ≠ 0 := by
          intro hz
          exact hv (mem_universalVertices.mpr hz)
        exact Nat.pos_of_ne_zero hvne
      by_cases hxZ : x ∈ universalVertices G
      · let z : ↑(universalVertices G) := ⟨x, hxZ⟩
        by_cases hyZ : y ∈ universalVertices G
        · let w : ↑(universalVertices G) := ⟨y, hyZ⟩
          have hzw : z ≠ w := by
            intro h
            exact hxy (congrArg Subtype.val h)
          have htargets : f₁ z ≠ f₁ w := fun h ↦ hzw (hf₁ h)
          apply card_filter_of_iff_ne_pair (nonUniversalVertices G)
            (fun u ↦ d6EdgePresentAt G f₁ f₂ u s((z : A), (w : A)))
            (f₁ z) (f₁ w)
            (hrange₁ z) (hrange₁ w) htargets
          intro u hu
          exact d6EdgePresentAt_universal_universal G f₁ f₂ hrange₁
            z w hu
        · have hyU := nonUniversal_of_not_universal hyZ
          by_cases hyM : y = f₁ z
          · subst y
            apply card_filter_of_iff_ne_pair (nonUniversalVertices G)
              (fun u ↦ d6EdgePresentAt G f₁ f₂ u s((z : A), f₁ z))
              (f₁ z) (f₂ z)
              (hrange₁ z) (hrange₂ z) (hdistinct z)
            intro u hu
            exact d6EdgePresentAt_universal_M1 G f₁ f₂ hrange₁ z hu
          · apply card_filter_of_iff_ne_pair (nonUniversalVertices G)
              (fun u ↦ d6EdgePresentAt G f₁ f₂ u s((z : A), y))
              (f₁ z) y
              (hrange₁ z) hyU (Ne.symm hyM)
            intro u hu
            exact d6EdgePresentAt_universal_nonUniversal_ne G f₁ f₂
              hrange₁ z hyU hu hyM
      · have hxU := nonUniversal_of_not_universal hxZ
        by_cases hyZ : y ∈ universalVertices G
        · let w : ↑(universalVertices G) := ⟨y, hyZ⟩
          rw [show s(x, y) = s((w : A), x) from
            Sym2.sound (Sym2.Rel.swap x y)]
          by_cases hxM : x = f₁ w
          · subst x
            apply card_filter_of_iff_ne_pair (nonUniversalVertices G)
              (fun u ↦ d6EdgePresentAt G f₁ f₂ u s((w : A), f₁ w))
              (f₁ w) (f₂ w)
              (hrange₁ w) (hrange₂ w) (hdistinct w)
            intro u hu
            exact d6EdgePresentAt_universal_M1 G f₁ f₂ hrange₁ w hu
          · apply card_filter_of_iff_ne_pair (nonUniversalVertices G)
              (fun u ↦ d6EdgePresentAt G f₁ f₂ u s((w : A), x))
              (f₁ w) x
              (hrange₁ w) hxU (Ne.symm hxM)
            intro u hu
            exact d6EdgePresentAt_universal_nonUniversal_ne G f₁ f₂
              hrange₁ w hxU hu hxM
        · have hyU := nonUniversal_of_not_universal hyZ
          apply card_filter_of_iff_ne_pair (nonUniversalVertices G)
            (fun u ↦ d6EdgePresentAt G f₁ f₂ u s(x, y)) x y
            hxU hyU hxy
          intro u _
          exact d6EdgePresentAt_nonUniversal_nonUniversal G f₁ f₂
            hrange₁ hxU hyU

private lemma sum_subtype_indicator_nat_eq_filter_card (U : Finset A)
    (P : A → Prop) [DecidablePred P] :
    (∑ u : ↑U, if P u then 1 else 0) = (U.filter P).card := by
  rw [Finset.card_filter]
  simpa only [Finset.univ_eq_attach] using
    Finset.sum_attach U (fun u ↦ if P u then 1 else 0)

/-- Double-counting the mapped auxiliary edges: every original edge occurs
in exactly `|U|-2` members of the corrected D6 family. -/
lemma sum_card_edgeFinset_d6AuxGraph (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A)
    (hf₁ : Function.Injective f₁)
    (hrange₁ : ∀ z, f₁ z ∈ nonUniversalVertices G)
    (hrange₂ : ∀ z, f₂ z ∈ nonUniversalVertices G)
    (hdistinct : ∀ z, f₁ z ≠ f₂ z) :
    (∑ u : ↑(nonUniversalVertices G),
        (d6AuxGraph G f₁ f₂ (u : A)).edgeFinset.card) =
      ((nonUniversalVertices G).card - 2) * G.edgeFinset.card := by
  classical
  calc
    (∑ u : ↑(nonUniversalVertices G),
        (d6AuxGraph G f₁ f₂ (u : A)).edgeFinset.card) =
      ∑ u : ↑(nonUniversalVertices G),
        (G.edgeFinset.filter fun e ↦
          d6EdgePresentAt G f₁ f₂ (u : A) e).card := by
        apply Finset.sum_congr rfl
        intro u _
        exact card_edgeFinset_d6AuxGraph G f₁ f₂ (u : A)
    _ = ∑ u : ↑(nonUniversalVertices G), ∑ e ∈ G.edgeFinset,
        if d6EdgePresentAt G f₁ f₂ (u : A) e then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      exact Finset.card_filter _ _
    _ = ∑ e ∈ G.edgeFinset, ∑ u : ↑(nonUniversalVertices G),
        if d6EdgePresentAt G f₁ f₂ (u : A) e then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ e ∈ G.edgeFinset,
        ((nonUniversalVertices G).filter fun u ↦
          d6EdgePresentAt G f₁ f₂ u e).card := by
      apply Finset.sum_congr rfl
      intro e _
      exact sum_subtype_indicator_nat_eq_filter_card (nonUniversalVertices G)
        (fun u ↦ d6EdgePresentAt G f₁ f₂ u e)
    _ = ∑ _e ∈ G.edgeFinset, ((nonUniversalVertices G).card - 2) := by
      apply Finset.sum_congr rfl
      intro e he
      exact card_filter_d6EdgePresentAt G f₁ f₂ hf₁ hrange₁
        hrange₂ hdistinct e he
    _ = ((nonUniversalVertices G).card - 2) * G.edgeFinset.card := by
      simp [Nat.mul_comm]

/-- The corrected D6 average, normalized by the exact common edge
multiplicity `|U|-2`. -/
def d6AveragedWeight (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d6KeptVertices G f₁ (u : A))) → ℝ) : Finset A → ℝ :=
  fun t ↦ (((nonUniversalVertices G).card - 2 : ℕ) : ℝ)⁻¹ *
    ∑ u : ↑(nonUniversalVertices G),
      d6LiftedWeight G f₁ f₂ (u : A) (w u) t

lemma fractionalEdgeLoad_d6AveragedWeight (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d6KeptVertices G f₁ (u : A))) → ℝ) (e : Sym2 A) :
    fractionalEdgeLoad G (d6AveragedWeight G f₁ f₂ w) e =
      (((nonUniversalVertices G).card - 2 : ℕ) : ℝ)⁻¹ *
        ∑ u : ↑(nonUniversalVertices G),
          fractionalEdgeLoad G
            (d6LiftedWeight G f₁ f₂ (u : A) (w u)) e := by
  unfold d6AveragedWeight
  rw [fractionalEdgeLoad_smul, fractionalEdgeLoad_sum]

lemma fractionalSize_d6AveragedWeight (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d6KeptVertices G f₁ (u : A))) → ℝ) :
    fractionalSize G (d6AveragedWeight G f₁ f₂ w) =
      (((nonUniversalVertices G).card - 2 : ℕ) : ℝ)⁻¹ *
        ∑ u : ↑(nonUniversalVertices G),
          fractionalSize (d6AuxGraph G f₁ f₂ (u : A)) (w u) := by
  unfold fractionalSize d6AveragedWeight
  rw [← Finset.mul_sum]
  apply congrArg
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  exact fractionalSize_d6LiftedWeight G f₁ f₂ (u : A) (w u)

private lemma sum_subtype_indicator_eq_filter_card (U : Finset A)
    (P : A → Prop) [DecidablePred P] :
    (∑ u : ↑U, if P u then (1 : ℝ) else 0) = ((U.filter P).card : ℝ) := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.univ_eq_attach, Finset.filter_attach, Finset.card_map,
    Finset.card_attach]

private lemma sum_subtype_ite_eq_filter_card_mul (U : Finset A)
    (P : A → Prop) [DecidablePred P] (b : ℝ) :
    (∑ u : ↑U, if P u then b else 0) = ((U.filter P).card : ℝ) * b := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.univ_eq_attach, Finset.filter_attach, Finset.card_map,
    Finset.card_attach]

/-- Feasibility of the normalized corrected D6 average. -/
lemma d6AveragedWeight_isFractionalPacking (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A)
    (hf₁ : Function.Injective f₁)
    (hrange₁ : ∀ z, f₁ z ∈ nonUniversalVertices G)
    (hrange₂ : ∀ z, f₂ z ∈ nonUniversalVertices G)
    (hdistinct : ∀ z, f₁ z ≠ f₂ z)
    (hU : 2 < (nonUniversalVertices G).card)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d6KeptVertices G f₁ (u : A))) → ℝ)
    (hw : ∀ u : ↑(nonUniversalVertices G), IsFractionalPacking
      (d6AuxGraph G f₁ f₂ (u : A)) (w u)) :
    IsFractionalPacking G (d6AveragedWeight G f₁ f₂ w) := by
  classical
  constructor
  · intro t ht
    unfold d6AveragedWeight
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun u _ ↦
        (d6LiftedWeight_isFractionalPacking G f₁ f₂ (u : A) (hw u)).1 t ht)
  · intro e he
    rw [fractionalEdgeLoad_d6AveragedWeight]
    have hsum :
        (∑ u : ↑(nonUniversalVertices G),
          fractionalEdgeLoad G
            (d6LiftedWeight G f₁ f₂ (u : A) (w u)) e) ≤
          (((nonUniversalVertices G).card - 2 : ℕ) : ℝ) := by
      calc
        (∑ u : ↑(nonUniversalVertices G),
            fractionalEdgeLoad G
              (d6LiftedWeight G f₁ f₂ (u : A) (w u)) e) ≤
            ∑ u : ↑(nonUniversalVertices G),
              if d6EdgePresentAt G f₁ f₂ (u : A) e then 1 else 0 := by
                apply Finset.sum_le_sum
                intro u _
                exact fractionalEdgeLoad_d6LiftedWeight_le_indicator
                  G f₁ f₂ (u : A) (hw u) e he
        _ = (((nonUniversalVertices G).filter fun u ↦
              d6EdgePresentAt G f₁ f₂ u e).card : ℝ) :=
          sum_subtype_indicator_eq_filter_card (nonUniversalVertices G)
            (fun u ↦ d6EdgePresentAt G f₁ f₂ u e)
        _ = (((nonUniversalVertices G).card - 2 : ℕ) : ℝ) := by
          rw [card_filter_d6EdgePresentAt G f₁ f₂ hf₁ hrange₁
            hrange₂ hdistinct e he]
    have hden : (0 : ℝ) < ((nonUniversalVertices G).card - 2 : ℕ) := by
      exact_mod_cast (Nat.sub_pos_of_lt hU)
    calc
      (((nonUniversalVertices G).card - 2 : ℕ) : ℝ)⁻¹ *
          ∑ u : ↑(nonUniversalVertices G),
            fractionalEdgeLoad G
              (d6LiftedWeight G f₁ f₂ (u : A) (w u)) e ≤
          (((nonUniversalVertices G).card - 2 : ℕ) : ℝ)⁻¹ *
            (((nonUniversalVertices G).card - 2 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hden.le)
      _ = 1 := by field_simp

/-- The same exact edge-multiplicity normalization preserves the pointwise
one-half bound on triangle weights. -/
lemma d6AveragedWeight_halfBounded (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A)
    (hf₁ : Function.Injective f₁)
    (hrange₁ : ∀ z, f₁ z ∈ nonUniversalVertices G)
    (hrange₂ : ∀ z, f₂ z ∈ nonUniversalVertices G)
    (hdistinct : ∀ z, f₁ z ≠ f₂ z)
    (hU : 2 < (nonUniversalVertices G).card)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d6KeptVertices G f₁ (u : A))) → ℝ)
    (hw : ∀ u : ↑(nonUniversalVertices G), IsHalfBounded
      (d6AuxGraph G f₁ f₂ (u : A)) (w u)) :
    IsHalfBounded G (d6AveragedWeight G f₁ f₂ w) := by
  classical
  intro t ht
  have htNC : G.IsNClique 3 t := SimpleGraph.mem_cliqueFinset_iff.mp ht
  have htwo : 1 < t.card := by rw [htNC.card_eq]; omega
  obtain ⟨x, y, hx, hy, hxy⟩ := Finset.one_lt_card_iff.mp htwo
  let e : Sym2 A := s(x, y)
  have hxyG : G.Adj x y := htNC.isClique hx hy hxy
  have heG : e ∈ G.edgeFinset := by
    simpa only [e, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hxyG
  have hterm : ∀ u : ↑(nonUniversalVertices G),
      d6LiftedWeight G f₁ f₂ (u : A) (w u) t ≤
        if d6EdgePresentAt G f₁ f₂ (u : A) e then 1 / 2 else 0 := by
    intro u
    by_cases hp : d6EdgePresentAt G f₁ f₂ (u : A) e
    · rw [if_pos hp]
      exact d6LiftedWeight_halfBounded G f₁ f₂ (u : A) (hw u) t ht
    · rw [if_neg hp,
        d6LiftedWeight_eq_zero_of_not_mem_ambient G f₁ f₂ (u : A)
          (w u) t]
      intro htA
      have hxyA : (d6AmbientAuxGraph G f₁ f₂ (u : A)).Adj x y :=
        (SimpleGraph.mem_cliqueFinset_iff.mp htA).isClique hx hy hxy
      exact hp ((d6AmbientAuxGraph_adj_iff G f₁ f₂ (u : A)
        x y hxyG).mp hxyA)
  have hden : (0 : ℝ) < ((nonUniversalVertices G).card - 2 : ℕ) := by
    exact_mod_cast (Nat.sub_pos_of_lt hU)
  unfold d6AveragedWeight
  calc
    (((nonUniversalVertices G).card - 2 : ℕ) : ℝ)⁻¹ *
        ∑ u : ↑(nonUniversalVertices G),
          d6LiftedWeight G f₁ f₂ (u : A) (w u) t ≤
      (((nonUniversalVertices G).card - 2 : ℕ) : ℝ)⁻¹ *
        ∑ u : ↑(nonUniversalVertices G),
          if d6EdgePresentAt G f₁ f₂ (u : A) e then 1 / 2 else 0 :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun u _ ↦ hterm u) (inv_nonneg.mpr hden.le)
    _ = (((nonUniversalVertices G).card - 2 : ℕ) : ℝ)⁻¹ *
        ((((nonUniversalVertices G).filter fun u ↦
          d6EdgePresentAt G f₁ f₂ u e).card : ℝ) * (1 / 2)) :=
      congrArg (fun z : ℝ ↦
        (((nonUniversalVertices G).card - 2 : ℕ) : ℝ)⁻¹ * z)
        (sum_subtype_ite_eq_filter_card_mul (nonUniversalVertices G)
          (fun u ↦ d6EdgePresentAt G f₁ f₂ u e) (1 / 2))
    _ = (((nonUniversalVertices G).card - 2 : ℕ) : ℝ)⁻¹ *
        ((((nonUniversalVertices G).card - 2 : ℕ) : ℝ) * (1 / 2)) := by
      rw [card_filter_d6EdgePresentAt G f₁ f₂ hf₁ hrange₁
        hrange₂ hdistinct e heG]
    _ = 1 / 2 := by field_simp

/-- The residual allowances from Claim 5.2 give the required uncovered-edge
bound for the normalized D6 average. -/
lemma fractionalUncoveredWeight_d6AveragedWeight_le {a : ℕ}
    (G : SimpleGraph A)
    (f₁ f₂ : (↑(universalVertices G)) → A)
    (b : A → ℕ)
    (hf₁ : Function.Injective f₁)
    (hrange₁ : ∀ z, f₁ z ∈ nonUniversalVertices G)
    (hrange₂ : ∀ z, f₂ z ∈ nonUniversalVertices G)
    (hdistinct : ∀ z, f₁ z ≠ f₂ z)
    (hU : 2 < (nonUniversalVertices G).card)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d6KeptVertices G f₁ (u : A))) → ℝ)
    (hunc : ∀ u : ↑(nonUniversalVertices G),
      fractionalUncoveredWeight (d6AuxGraph G f₁ f₂ (u : A)) (w u) ≤
        ((a - min a (b u) : ℕ) : ℝ))
    (hresidual : 2 * a ≤
      ∑ u ∈ nonUniversalVertices G, min a (b u)) :
    fractionalUncoveredWeight G (d6AveragedWeight G f₁ f₂ w) ≤ a := by
  classical
  let U := nonUniversalVertices G
  let d := U.card - 2
  have hdenNat : 0 < d := by dsimp only [d, U]; omega
  have hden : (0 : ℝ) < d := by exact_mod_cast hdenNat
  have hresidual' : 2 * a ≤ ∑ u : ↑U, min a (b u) := by
    calc
      2 * a ≤ ∑ u ∈ U, min a (b u) := by simpa only [U] using hresidual
      _ = ∑ u : ↑U, min a (b u) := by
        symm
        simpa only [Finset.univ_eq_attach] using
          Finset.sum_attach U (fun u ↦ min a (b u))
  have hdefectIdentity :
      (∑ u : ↑U, (a - min a (b u))) +
          (∑ u : ↑U, min a (b u)) = U.card * a := by
    rw [← Finset.sum_add_distrib]
    simp [Nat.sub_add_cancel (Nat.min_le_left _ _)]
  have hdefectNat :
      (∑ u : ↑U, (a - min a (b u))) ≤ d * a := by
    have hU' : 2 < U.card := by simpa only [U] using hU
    have hmul : d * a + 2 * a = U.card * a := by
      rw [← Nat.add_mul]
      congr 1
      dsimp only [d]
      omega
    omega
  have hdefectReal :
      (∑ u : ↑U, ((a - min a (b u) : ℕ) : ℝ)) ≤
        (d : ℝ) * (a : ℝ) := by
    exact_mod_cast hdefectNat
  have hsumCardNat := sum_card_edgeFinset_d6AuxGraph
    G f₁ f₂ hf₁ hrange₁ hrange₂ hdistinct
  have hsumCardReal :
      (∑ u : ↑U,
        ((d6AuxGraph G f₁ f₂ (u : A)).edgeFinset.card : ℝ)) =
        (d : ℝ) * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast hsumCardNat
  have hsumUncovered :
      (∑ u : ↑U,
        (((d6AuxGraph G f₁ f₂ (u : A)).edgeFinset.card : ℝ) -
          3 * fractionalSize (d6AuxGraph G f₁ f₂ (u : A)) (w u))) ≤
        ∑ u : ↑U, ((a - min a (b u) : ℕ) : ℝ) := by
    apply Finset.sum_le_sum
    intro u _
    have hu := hunc u
    rw [fractionalUncoveredWeight_eq_card_sub_general,
      Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet] at hu
    exact hu
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsumUncovered
  rw [fractionalUncoveredWeight_eq_card_sub_general,
    Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet,
    fractionalSize_d6AveragedWeight]
  have hcore :
      (d : ℝ) * (G.edgeFinset.card : ℝ) -
          3 * ∑ u : ↑U,
            fractionalSize (d6AuxGraph G f₁ f₂ (u : A)) (w u) ≤
        (d : ℝ) * (a : ℝ) := by
    rw [← hsumCardReal]
    exact hsumUncovered.trans hdefectReal
  change (G.edgeFinset.card : ℝ) -
      3 * ((d : ℝ)⁻¹ * ∑ u : ↑U,
        fractionalSize (d6AuxGraph G f₁ f₂ (u : A)) (w u)) ≤ (a : ℝ)
  refine le_of_mul_le_mul_left (a := (d : ℝ)) ?_ hden
  calc
    (d : ℝ) * ((G.edgeFinset.card : ℝ) -
        3 * ((d : ℝ)⁻¹ * ∑ u : ↑U,
          fractionalSize (d6AuxGraph G f₁ f₂ (u : A)) (w u))) =
      (d : ℝ) * (G.edgeFinset.card : ℝ) -
        3 * ∑ u : ↑U,
          fractionalSize (d6AuxGraph G f₁ f₂ (u : A)) (w u) := by
      field_simp [ne_of_gt hden]
    _ ≤ (d : ℝ) * (a : ℝ) := hcore

/-- Complete D6 case of the almost-complete strong induction.  The two
corrected matching deletion families are packed by the `n-1` and `n-2`
induction hypotheses and averaged with exact multiplicity `|U|-2`. -/
theorem d6_case {n a : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n) (ha : a ≤ 4)
    (G : SimpleGraph A)
    (hexact : missingEdgeCount G = n - 4 + a)
    (hm : (universalVertices G).card ≤ 3)
    (hnoD5 : ∀ u : A, 3 * Gᶜ.degree u ≤ n + a)
    (hstrong₁ : AlmostCompleteStrongAt (n - 1))
    (hstrong₂ : AlmostCompleteStrongAt (n - 2)) :
    HasStrongFractionalPacking G (a : ℝ) := by
  classical
  obtain ⟨f₁, f₂, b, hf₁, hf₂, hrange₁, hrange₂, hdistinct,
    hdegree, hresidual⟩ :=
    exists_d6_target_maps_with_residuals hcard hn ha G hexact hm hnoD5
  have hU : 2 < (nonUniversalVertices G).card := by
    have hpart := card_nonUniversalVertices_add_card_universalVertices G
    rw [hcard] at hpart
    omega
  have haux : ∀ u : ↑(nonUniversalVertices G),
      HasStrongFractionalPacking (d6AuxGraph G f₁ f₂ (u : A))
        ((a - min a (b u) : ℕ) : ℝ) := by
    intro u
    exact d6AuxGraph_hasStrongFractionalPacking hcard hn ha G f₁ f₂ b
      hf₁ hrange₁ hrange₂ hdistinct hexact hdegree hstrong₁ hstrong₂
      (u : A) u.property
  choose w hw using haux
  refine ⟨d6AveragedWeight G f₁ f₂ w, ?_, ?_, ?_⟩
  · exact d6AveragedWeight_isFractionalPacking G f₁ f₂ hf₁ hrange₁
      hrange₂ hdistinct hU w (fun u ↦ (hw u).1)
  · exact fractionalUncoveredWeight_d6AveragedWeight_le G f₁ f₂ b hf₁
      hrange₁ hrange₂ hdistinct hU w (fun u ↦ (hw u).2.1) hresidual
  · exact d6AveragedWeight_halfBounded G f₁ f₂ hf₁ hrange₁ hrange₂
      hdistinct hU w (fun u ↦ (hw u).2.2)

/-! ## The common corrected vertex-deletion average for D7 and D8 -/

/-- The retained vertices after deleting a single vertex. -/
def d7DeletedFinset (u : A) : Finset A :=
  Finset.univ.erase u

/-- The graph obtained by deleting one vertex, on its natural subtype. -/
def d7DeletedGraph (G : SimpleGraph A) (u : A) :
    SimpleGraph (↑(d7DeletedFinset u)) :=
  G.induce (↑(d7DeletedFinset u) : Set A)

/-- Lift a weighting on a one-vertex deletion back to the ambient type. -/
def d7LiftedWeight (u : A)
    (w : Finset (↑(d7DeletedFinset u)) → ℝ) : Finset A → ℝ :=
  extendInducedWeight (d7DeletedFinset u) w

/-- The local defect used in D7.  A nonuniversal deletion spends its chosen
residual allocation; deleting a universal vertex costs one extra unit. -/
def d7LocalDefect (G : SimpleGraph A) (a : ℕ) (sigma : A → ℕ)
    (u : A) : ℕ :=
  if u ∈ nonUniversalVertices G then a - sigma u else a + 1

/-- Every one-vertex deletion needed in D7 is covered by the `n-1`
induction hypothesis with the local defect prescribed above. -/
theorem d7DeletedGraph_hasStrongFractionalPacking {n a : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n) (ha : a < 4)
    (G : SimpleGraph A)
    (hexact : missingEdgeCount G = n - 4 + a)
    (sigma : A → ℕ)
    (hsigma : ∀ u, sigma u ≤ d7ResidualAllowance G a u)
    (hstrong : AlmostCompleteStrongAt (n - 1)) (u : A) :
    HasStrongFractionalPacking (d7DeletedGraph G u)
      (d7LocalDefect G a sigma u : ℝ) := by
  classical
  have horder : Fintype.card (↑(d7DeletedFinset u)) = n - 1 := by
    unfold d7DeletedFinset
    rw [card_univ_erase, hcard]
  have hmissingExact : missingEdgeCount (d7DeletedGraph G u) =
      missingEdgeCount G - Gᶜ.degree u := by
    change missingEdgeCount
      (G.induce (↑((Finset.univ : Finset A).erase u) : Set A)) = _
    exact missingEdgeCount_induce_univ_erase G u
  by_cases hu : u ∈ nonUniversalVertices G
  · have hdegreePos : 0 < Gᶜ.degree u := mem_nonUniversalVertices.mp hu
    have hsigmaLe : sigma u ≤ a :=
      (hsigma u).trans (Nat.min_le_left _ _)
    have hsigmaDegree : sigma u + 1 ≤ Gᶜ.degree u := by
      have h := (hsigma u).trans (Nat.min_le_right _ _)
      omega
    have hdefect4 : a - sigma u ≤ 4 := by omega
    have hmissing : missingEdgeCount (d7DeletedGraph G u) ≤
        n - 1 - 4 + (a - sigma u) := by
      rw [hmissingExact, hexact]
      omega
    simpa only [d7LocalDefect, if_pos hu] using
      hstrong _ horder (a - sigma u) hdefect4 (d7DeletedGraph G u) hmissing
  · have hdegreeZero : Gᶜ.degree u = 0 := by
      apply Nat.eq_zero_of_not_pos
      simpa only [mem_nonUniversalVertices] using hu
    have hdefect4 : a + 1 ≤ 4 := by omega
    have hmissing : missingEdgeCount (d7DeletedGraph G u) ≤
        n - 1 - 4 + (a + 1) := by
      rw [hmissingExact, hexact, hdegreeZero]
      omega
    simpa only [d7LocalDefect, if_neg hu] using
      hstrong _ horder (a + 1) hdefect4 (d7DeletedGraph G u) hmissing

/-- The normalized vertex-deletion sum with one additional explicit
correction.  In D7 the correction contains the `UUZ`, `UZZ`, and `ZZZ`
triangles from the paper. -/
def d7CorrectedAverageWeight (G : SimpleGraph A)
    (w : ∀ u : A, Finset (↑(d7DeletedFinset u)) → ℝ)
    (correction : Finset A → ℝ) : Finset A → ℝ :=
  fun t ↦ (((Fintype.card A - 2 : ℕ) : ℝ)⁻¹) *
    ((∑ u : A, d7LiftedWeight u (w u) t) + correction t)

lemma fractionalEdgeLoad_d7CorrectedAverageWeight (G : SimpleGraph A)
    (w : ∀ u : A, Finset (↑(d7DeletedFinset u)) → ℝ)
    (correction : Finset A → ℝ) (e : Sym2 A) :
    fractionalEdgeLoad G (d7CorrectedAverageWeight G w correction) e =
      (((Fintype.card A - 2 : ℕ) : ℝ)⁻¹) *
        ((∑ u : A,
          fractionalEdgeLoad G (d7LiftedWeight u (w u)) e) +
          fractionalEdgeLoad G correction e) := by
  unfold d7CorrectedAverageWeight
  rw [fractionalEdgeLoad_smul, fractionalEdgeLoad_add,
    fractionalEdgeLoad_sum]

lemma fractionalSize_d7CorrectedAverageWeight (G : SimpleGraph A)
    (w : ∀ u : A, Finset (↑(d7DeletedFinset u)) → ℝ)
    (correction : Finset A → ℝ) :
    fractionalSize G (d7CorrectedAverageWeight G w correction) =
      (((Fintype.card A - 2 : ℕ) : ℝ)⁻¹) *
        ((∑ u : A, fractionalSize (d7DeletedGraph G u) (w u)) +
          fractionalSize G correction) := by
  have hmain :
      (∑ t ∈ G.cliqueFinset 3, ∑ u : A, d7LiftedWeight u (w u) t) =
        ∑ u : A, fractionalSize (d7DeletedGraph G u) (w u) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    exact fractionalSize_extendInducedWeight G (d7DeletedFinset u) (w u)
  unfold fractionalSize d7CorrectedAverageWeight
  rw [← Finset.mul_sum, Finset.sum_add_distrib, hmain]
  rfl

/-- Shared D7/D8 assembly lemma.  It isolates all normalization algebra:
aggregate load at most `n-2`, aggregate triangle weight at most
`(n-2)/2`, and the displayed residual budget imply that the corrected
average is a strong fractional packing. -/
theorem hasStrongFractionalPacking_of_d7CorrectedData {a : ℕ}
    (G : SimpleGraph A)
    (hcard : 2 < Fintype.card A)
    (w : ∀ u : A, Finset (↑(d7DeletedFinset u)) → ℝ)
    (correction : Finset A → ℝ)
    (hwPacking : ∀ u : A, IsFractionalPacking (d7DeletedGraph G u) (w u))
    (hcorrectionNonneg : ∀ t ∈ G.cliqueFinset 3, 0 ≤ correction t)
    (hload : ∀ e ∈ G.edgeFinset,
      (∑ u : A, fractionalEdgeLoad G (d7LiftedWeight u (w u)) e) +
        fractionalEdgeLoad G correction e ≤
          ((Fintype.card A - 2 : ℕ) : ℝ))
    (hhalf : ∀ t ∈ G.cliqueFinset 3,
      (∑ u : A, d7LiftedWeight u (w u) t) + correction t ≤
        ((Fintype.card A - 2 : ℕ) : ℝ) / 2)
    (hbudget :
      ((Fintype.card A - 2 : ℕ) : ℝ) *
          (G.edgeFinset.card : ℝ) -
        3 * ((∑ u : A, fractionalSize (d7DeletedGraph G u) (w u)) +
          fractionalSize G correction) ≤
        ((Fintype.card A - 2 : ℕ) : ℝ) * (a : ℝ)) :
    HasStrongFractionalPacking G (a : ℝ) := by
  classical
  let d : ℝ := ((Fintype.card A - 2 : ℕ) : ℝ)
  have hd : 0 < d := by
    dsimp only [d]
    exact_mod_cast (Nat.sub_pos_of_lt hcard)
  refine ⟨d7CorrectedAverageWeight G w correction, ?_, ?_, ?_⟩
  · constructor
    · intro t ht
      unfold d7CorrectedAverageWeight
      apply mul_nonneg (inv_nonneg.mpr hd.le)
      apply add_nonneg
      · apply Finset.sum_nonneg
        intro u _
        exact (hwPacking u).extendInduced.nonneg_on ht
      · exact hcorrectionNonneg t ht
    · intro e he
      rw [fractionalEdgeLoad_d7CorrectedAverageWeight]
      calc
        d⁻¹ * ((∑ u : A,
            fractionalEdgeLoad G (d7LiftedWeight u (w u)) e) +
            fractionalEdgeLoad G correction e) ≤ d⁻¹ * d :=
          mul_le_mul_of_nonneg_left (by simpa only [d] using hload e he)
            (inv_nonneg.mpr hd.le)
        _ = 1 := by field_simp
  · rw [fractionalUncoveredWeight_eq_card_sub_general,
      Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet,
      fractionalSize_d7CorrectedAverageWeight]
    change (G.edgeFinset.card : ℝ) -
      3 * (d⁻¹ * ((∑ u : A,
        fractionalSize (d7DeletedGraph G u) (w u)) +
        fractionalSize G correction)) ≤ (a : ℝ)
    refine le_of_mul_le_mul_left (a := d) ?_ hd
    calc
      d * ((G.edgeFinset.card : ℝ) -
          3 * (d⁻¹ * ((∑ u : A,
            fractionalSize (d7DeletedGraph G u) (w u)) +
            fractionalSize G correction))) =
        d * (G.edgeFinset.card : ℝ) -
          3 * ((∑ u : A,
            fractionalSize (d7DeletedGraph G u) (w u)) +
            fractionalSize G correction) := by
              field_simp [ne_of_gt hd]
      _ ≤ d * (a : ℝ) := by simpa only [d] using hbudget
  · intro t ht
    unfold d7CorrectedAverageWeight
    calc
      d⁻¹ * ((∑ u : A, d7LiftedWeight u (w u) t) + correction t) ≤
          d⁻¹ * (d / 2) :=
        mul_le_mul_of_nonneg_left (by simpa only [d] using hhalf t ht)
          (inv_nonneg.mpr hd.le)
      _ = 1 / 2 := by field_simp

/-! ## Attaching the deleted vertex to a cycle edge -/

/-- The ambient triangle obtained by adjoining `u` to the two endpoints of
an edge in the induced subtype `S`. -/
def attachedEdgeTriangle (S : Finset A) (u : A) (e : Sym2 S) : Finset A :=
  insert u (e.toFinset.map (inducedEmbedding S))

lemma card_attachedEdgeTriangle {S : Finset A} {u : A} {e : Sym2 S}
    (hu : u ∉ S) (he : ¬e.IsDiag) : (attachedEdgeTriangle S u e).card = 3 := by
  have hnot : u ∉ e.toFinset.map (inducedEmbedding S) := by
    intro hmem
    obtain ⟨x, _, hxu⟩ := Finset.mem_map.mp hmem
    apply hu
    change (x : A) = u at hxu
    rw [← hxu]
    exact x.property
  rw [attachedEdgeTriangle, Finset.card_insert_of_notMem hnot,
    Finset.card_map, Sym2.card_toFinset_of_not_isDiag e he]

private lemma sym2_eq_of_toFinset_eq_of_not_isDiag {X : Type*}
    [DecidableEq X] {e f : Sym2 X} (he : ¬e.IsDiag) (hf : ¬f.IsDiag)
    (h : e.toFinset = f.toFinset) : e = f := by
  induction e using Sym2.inductionOn with
  | hf x y =>
      induction f using Sym2.inductionOn with
      | hf z w =>
          simp only [Sym2.mk_isDiag_iff] at he hf
          simp only [Sym2.toFinset_mk_eq] at h
          rw [Sym2.eq_iff]
          have hx : x = z ∨ x = w := by
            have hxmem : x ∈ ({z, w} : Finset X) := by
              rw [← h]
              simp
            simpa using hxmem
          have hy : y = z ∨ y = w := by
            have hymem : y ∈ ({z, w} : Finset X) := by
              rw [← h]
              simp
            simpa using hymem
          rcases hx with hx | hx
          · left
            refine ⟨hx, ?_⟩
            rcases hy with hy | hy
            · exact (he (hx.trans hy.symm)).elim
            · exact hy
          · right
            refine ⟨hx, ?_⟩
            rcases hy with hy | hy
            · exact hy
            · exact (he (hx.trans hy.symm)).elim

/-- Distinct non-diagonal induced edges give distinct attached triangles. -/
lemma attachedEdgeTriangle_injective {S : Finset A} {u : A} (hu : u ∉ S)
    {e f : Sym2 S} (he : ¬e.IsDiag) (hf : ¬f.IsDiag)
    (h : attachedEdgeTriangle S u e = attachedEdgeTriangle S u f) : e = f := by
  have hnotE : u ∉ e.toFinset.map (inducedEmbedding S) := by
    intro hmem
    obtain ⟨x, _, hxu⟩ := Finset.mem_map.mp hmem
    apply hu
    change (x : A) = u at hxu
    rw [← hxu]
    exact x.property
  have hnotF : u ∉ f.toFinset.map (inducedEmbedding S) := by
    intro hmem
    obtain ⟨x, _, hxu⟩ := Finset.mem_map.mp hmem
    apply hu
    change (x : A) = u at hxu
    rw [← hxu]
    exact x.property
  have hmap := congrArg (fun t : Finset A ↦ t.erase u) h
  dsimp only [attachedEdgeTriangle] at hmap
  rw [Finset.erase_insert hnotE, Finset.erase_insert hnotF] at hmap
  exact sym2_eq_of_toFinset_eq_of_not_isDiag he hf
    (Finset.map_injective (inducedEmbedding S) hmap)

/-- If the two endpoints form an edge in the induced graph and the attachment
vertex is adjacent to all vertices of `S`, the attached set is a triangle of
the ambient graph. -/
lemma attachedEdgeTriangle_isNClique {G : SimpleGraph A} {S : Finset A}
    {u : A} {e : Sym2 S}
    (he : e ∈ (G.induce (S : Set A)).edgeSet)
    (hstar : ∀ x : S, x ∈ e → G.Adj u x) :
    G.IsNClique 3 (attachedEdgeTriangle S u e) := by
  induction e using Sym2.inductionOn with
  | hf x y =>
      have hxy : G.Adj (x : A) y := by
        simpa [SimpleGraph.mem_edgeSet] using he
      simpa [attachedEdgeTriangle, Sym2.toFinset_mk_eq] using
        (SimpleGraph.is3Clique_triple_iff.mpr
          ⟨hstar x (by simp), hstar y (by simp), hxy⟩)

/-- Put the same weight `r` on every triangle obtained by adjoining `u` to an
edge in `C`.  The sum presentation is convenient for edge-load calculations;
injectivity of `attachedEdgeTriangle` ensures that at most one summand is
nonzero. -/
def attachedEdgeWeight (S : Finset A) (u : A) (C : Finset (Sym2 S))
    (r : ℝ) (t : Finset A) : ℝ :=
  ∑ e ∈ C, if t = attachedEdgeTriangle S u e then r else 0

lemma attachedEdgeWeight_apply {G : SimpleGraph A} {S : Finset A} {u : A}
    {C : Finset (Sym2 S)} {r : ℝ} (hu : u ∉ S)
    (hCG : ∀ e ∈ C, e ∈ (G.induce (S : Set A)).edgeSet)
    {e : Sym2 S} (heC : e ∈ C) :
    attachedEdgeWeight S u C r (attachedEdgeTriangle S u e) = r := by
  classical
  have hnonDiag : ∀ f ∈ C, ¬f.IsDiag := by
    intro f hfC
    exact (G.induce (S : Set A)).not_isDiag_of_mem_edgeSet (hCG f hfC)
  unfold attachedEdgeWeight
  calc
    (∑ f ∈ C,
        if attachedEdgeTriangle S u e = attachedEdgeTriangle S u f then r else 0) =
        (if attachedEdgeTriangle S u e = attachedEdgeTriangle S u e then r else 0) := by
      apply Finset.sum_eq_single e
      · intro f hfC hfe
        rw [if_neg]
        intro htri
        exact hfe (attachedEdgeTriangle_injective hu (hnonDiag f hfC)
          (hnonDiag e heC) htri.symm)
      · exact fun h ↦ (h heC).elim
    _ = r := by simp

lemma attachedEdgeWeight_eq_zero_of_not_exists
    {S : Finset A} {u : A} {C : Finset (Sym2 S)} {r : ℝ} {t : Finset A}
    (ht : ¬ ∃ e ∈ C, t = attachedEdgeTriangle S u e) :
    attachedEdgeWeight S u C r t = 0 := by
  unfold attachedEdgeWeight
  apply Finset.sum_eq_zero
  intro e he
  rw [if_neg]
  exact fun h ↦ ht ⟨e, he, h⟩

/-- The half-cycle attachment has no heavy triangle. -/
lemma attachedEdgeWeight_halfBounded {G : SimpleGraph A} {S : Finset A}
    {u : A} {C : Finset (Sym2 S)} (hu : u ∉ S)
    (hCG : ∀ e ∈ C, e ∈ (G.induce (S : Set A)).edgeSet) :
    IsHalfBounded G (attachedEdgeWeight S u C (1 / 2)) := by
  classical
  intro t ht
  by_cases hex : ∃ e ∈ C, t = attachedEdgeTriangle S u e
  · obtain ⟨e, heC, rfl⟩ := hex
    rw [attachedEdgeWeight_apply hu hCG heC]
  · rw [attachedEdgeWeight_eq_zero_of_not_exists hex]
    norm_num

/-- Under the same hypotheses, all half-cycle attachment weights are
nonnegative on ambient triangles. -/
lemma attachedEdgeWeight_half_nonneg {G : SimpleGraph A} {S : Finset A}
    {u : A} {C : Finset (Sym2 S)} :
    ∀ t ∈ G.cliqueFinset 3, 0 ≤ attachedEdgeWeight S u C (1 / 2) t := by
  intro t _ht
  unfold attachedEdgeWeight
  apply Finset.sum_nonneg
  intro e he
  split <;> norm_num

/-- Edge load of an attached-edge weighting is the weighted incidence count
of the queried edge among the attached triangles. -/
lemma fractionalEdgeLoad_attachedEdgeWeight {G : SimpleGraph A}
    {S : Finset A} {u : A} {C : Finset (Sym2 S)} {r : ℝ}
    (hCG : ∀ e ∈ C, e ∈ (G.induce (S : Set A)).edgeSet)
    (hstar : ∀ e ∈ C, ∀ x : S, x ∈ e → G.Adj u x)
    (p : Sym2 A) :
    fractionalEdgeLoad G (attachedEdgeWeight S u C r) p =
      ∑ e ∈ C,
        if p ∈ (attachedEdgeTriangle S u e).sym2 then r else 0 := by
  classical
  unfold fractionalEdgeLoad attachedEdgeWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e heC
  have htri : attachedEdgeTriangle S u e ∈ G.cliqueFinset 3 :=
    SimpleGraph.mem_cliqueFinset_iff.mpr
      (attachedEdgeTriangle_isNClique (hCG e heC) (hstar e heC))
  by_cases hp : p ∈ (attachedEdgeTriangle S u e).sym2
  · rw [if_pos hp]
    calc
      (∑ t ∈ (G.cliqueFinset 3).filter (fun t ↦ p ∈ t.sym2),
          if t = attachedEdgeTriangle S u e then r else 0) =
          (if attachedEdgeTriangle S u e = attachedEdgeTriangle S u e
            then r else 0) := by
        apply Finset.sum_eq_single (attachedEdgeTriangle S u e)
        · intro t ht hne
          rw [if_neg hne]
        · exact fun h ↦ (h (Finset.mem_filter.mpr ⟨htri, hp⟩)).elim
      _ = r := by simp
  · rw [if_neg hp]
    apply Finset.sum_eq_zero
    intro t ht
    rw [if_neg]
    intro hte
    subst t
    exact hp (Finset.mem_filter.mp ht).2

/-- There is one attached triangle of weight `r` for every selected edge. -/
lemma fractionalSize_attachedEdgeWeight {G : SimpleGraph A}
    {S : Finset A} {u : A} {C : Finset (Sym2 S)} {r : ℝ}
    (hu : u ∉ S)
    (hCG : ∀ e ∈ C, e ∈ (G.induce (S : Set A)).edgeSet)
    (hstar : ∀ e ∈ C, ∀ x : S, x ∈ e → G.Adj u x) :
    fractionalSize G (attachedEdgeWeight S u C r) = (C.card : ℝ) * r := by
  classical
  unfold fractionalSize attachedEdgeWeight
  rw [Finset.sum_comm]
  calc
    (∑ e ∈ C, ∑ t ∈ G.cliqueFinset 3,
        if t = attachedEdgeTriangle S u e then r else 0) =
        ∑ _e ∈ C, r := by
      apply Finset.sum_congr rfl
      intro e heC
      have htri : attachedEdgeTriangle S u e ∈ G.cliqueFinset 3 :=
        SimpleGraph.mem_cliqueFinset_iff.mpr
          (attachedEdgeTriangle_isNClique (hCG e heC) (hstar e heC))
      calc
        (∑ t ∈ G.cliqueFinset 3,
            if t = attachedEdgeTriangle S u e then r else 0) =
            (if attachedEdgeTriangle S u e = attachedEdgeTriangle S u e
              then r else 0) := by
          apply Finset.sum_eq_single (attachedEdgeTriangle S u e)
          · intro t ht hne
            rw [if_neg hne]
          · exact fun h ↦ (h htri).elim
        _ = r := by simp
    _ = (C.card : ℝ) * r := by
      rw [Finset.sum_const, nsmul_eq_mul]

private lemma inducedEdge_mem_attachedEdgeTriangle_sym2_iff
    {S : Finset A} {u : A} {p f : Sym2 S} (hu : u ∉ S)
    (hp : ¬p.IsDiag) (hf : ¬f.IsDiag) :
    (inducedEmbedding S).sym2Map p ∈ (attachedEdgeTriangle S u f).sym2 ↔
      p = f := by
  induction p using Sym2.inductionOn with
  | hf a b =>
      induction f using Sym2.inductionOn with
      | hf x y =>
          simp only [Sym2.mk_isDiag_iff] at hp hf
          have hau : (a : A) ≠ u := by
            intro h
            apply hu
            rw [← h]
            exact a.property
          have hbu : (b : A) ≠ u := by
            intro h
            apply hu
            rw [← h]
            exact b.property
          simp only [attachedEdgeTriangle, Sym2.map_mk,
            Sym2.toFinset_mk_eq, Finset.map_insert, Finset.map_singleton,
            Finset.mk_mem_sym2_iff, Finset.mem_insert, Finset.mem_singleton,
            Sym2.eq_iff]
          aesop

/-- On an edge internal to `S`, the attachment contributes `r` precisely
when that edge was selected in `C`. -/
lemma fractionalEdgeLoad_attachedEdgeWeight_induced {G : SimpleGraph A}
    {S : Finset A} {u : A} {C : Finset (Sym2 S)} {r : ℝ}
    (hu : u ∉ S)
    (hCG : ∀ e ∈ C, e ∈ (G.induce (S : Set A)).edgeSet)
    (hstar : ∀ e ∈ C, ∀ x : S, x ∈ e → G.Adj u x)
    {p : Sym2 S} (hp : ¬p.IsDiag) :
    fractionalEdgeLoad G (attachedEdgeWeight S u C r)
        ((inducedEmbedding S).sym2Map p) =
      if p ∈ C then r else 0 := by
  classical
  rw [fractionalEdgeLoad_attachedEdgeWeight hCG hstar]
  have hnonDiag : ∀ f ∈ C, ¬f.IsDiag := by
    intro f hfC
    exact (G.induce (S : Set A)).not_isDiag_of_mem_edgeSet (hCG f hfC)
  by_cases hpC : p ∈ C
  · rw [if_pos hpC]
    calc
      (∑ f ∈ C,
          if (inducedEmbedding S).sym2Map p ∈
            (attachedEdgeTriangle S u f).sym2 then r else 0) =
          (if (inducedEmbedding S).sym2Map p ∈
            (attachedEdgeTriangle S u p).sym2 then r else 0) := by
        apply Finset.sum_eq_single p
        · intro f hfC hfp
          rw [if_neg]
          intro hmem
          exact hfp ((inducedEdge_mem_attachedEdgeTriangle_sym2_iff
            hu hp (hnonDiag f hfC)).mp hmem).symm
        · exact fun h ↦ (h hpC).elim
      _ = r := by rw [if_pos ((inducedEdge_mem_attachedEdgeTriangle_sym2_iff
        hu hp (hnonDiag p hpC)).mpr rfl)]
  · rw [if_neg hpC]
    apply Finset.sum_eq_zero
    intro f hfC
    rw [if_neg]
    intro hmem
    exact hpC ((inducedEdge_mem_attachedEdgeTriangle_sym2_iff
      hu hp (hnonDiag f hfC)).mp hmem ▸ hfC)

private lemma starEdge_mem_attachedEdgeTriangle_sym2_iff
    {S : Finset A} {u : A} (hu : u ∉ S) (x : S) (f : Sym2 S) :
    s(u, (x : A)) ∈ (attachedEdgeTriangle S u f).sym2 ↔ x ∈ f := by
  induction f using Sym2.inductionOn with
  | hf a b =>
      have hxu : (x : A) ≠ u := by
        intro h
        apply hu
        rw [← h]
        exact x.property
      simp only [attachedEdgeTriangle, Sym2.toFinset_mk_eq,
        Finset.map_insert, Finset.map_singleton, Finset.mk_mem_sym2_iff,
        Finset.mem_insert, Finset.mem_singleton, Sym2.mem_iff]
      aesop

/-- On a star edge `ux`, the attachment load is `r` times the number of
selected edges of `C` incident with `x`. -/
lemma fractionalEdgeLoad_attachedEdgeWeight_star {G : SimpleGraph A}
    {S : Finset A} {u : A} {C : Finset (Sym2 S)} {r : ℝ}
    (hu : u ∉ S)
    (hCG : ∀ e ∈ C, e ∈ (G.induce (S : Set A)).edgeSet)
    (hstar : ∀ e ∈ C, ∀ y : S, y ∈ e → G.Adj u y) (x : S) :
    fractionalEdgeLoad G (attachedEdgeWeight S u C r) s(u, (x : A)) =
      (((C.filter fun e ↦ x ∈ e).card : ℕ) : ℝ) * r := by
  classical
  rw [fractionalEdgeLoad_attachedEdgeWeight hCG hstar]
  simp_rw [starEdge_mem_attachedEdgeTriangle_sym2_iff hu x]
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]

lemma fractionalEdgeLoad_attachedEdgeWeight_eq_card {G : SimpleGraph A}
    {S : Finset A} {u : A} {C : Finset (Sym2 S)} {r : ℝ}
    (hCG : ∀ e ∈ C, e ∈ (G.induce (S : Set A)).edgeSet)
    (hstar : ∀ e ∈ C, ∀ x : S, x ∈ e → G.Adj u x)
    (p : Sym2 A) :
    fractionalEdgeLoad G (attachedEdgeWeight S u C r) p =
      (((C.filter fun e ↦ p ∈ (attachedEdgeTriangle S u e).sym2).card : ℕ) : ℝ) * r := by
  rw [fractionalEdgeLoad_attachedEdgeWeight hCG hstar]
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]

/-- The half-weight attachment is itself a fractional packing whenever each
ambient edge occurs in at most two selected attached triangles.  A Hamilton
cycle supplies exactly this incidence bound. -/
lemma attachedEdgeWeight_isFractionalPacking_half {G : SimpleGraph A}
    {S : Finset A} {u : A} {C : Finset (Sym2 S)}
    (hCG : ∀ e ∈ C, e ∈ (G.induce (S : Set A)).edgeSet)
    (hstar : ∀ e ∈ C, ∀ x : S, x ∈ e → G.Adj u x)
    (hinc : ∀ p ∈ G.edgeFinset,
      (C.filter fun e ↦ p ∈ (attachedEdgeTriangle S u e).sym2).card ≤ 2) :
    IsFractionalPacking G (attachedEdgeWeight S u C (1 / 2)) := by
  constructor
  · exact attachedEdgeWeight_half_nonneg
  · intro p hp
    rw [fractionalEdgeLoad_attachedEdgeWeight_eq_card hCG hstar]
    have hinc' :
        (((C.filter fun e ↦ p ∈ (attachedEdgeTriangle S u e).sym2).card : ℕ) : ℝ) ≤ 2 := by
      exact_mod_cast hinc p hp
    calc
      (((C.filter fun e ↦ p ∈ (attachedEdgeTriangle S u e).sym2).card : ℕ) : ℝ) *
          (1 / 2 : ℝ) ≤ 2 * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hinc' (by norm_num)
      _ = 1 := by norm_num

/-- Adding a nonnegative triangle weighting to a capacity packing is feasible
provided the capacity plus the added edge load stays below one. -/
lemma IsCapacityPacking.add_of_capacity_add_load_le
    {G : SimpleGraph A} {c : Sym2 A → ℝ} {w v : Finset A → ℝ}
    (hw : IsCapacityPacking G c w)
    (hv : ∀ t ∈ G.cliqueFinset 3, 0 ≤ v t)
    (hedge : ∀ e ∈ G.edgeFinset,
      c e + fractionalEdgeLoad G v e ≤ 1) :
    IsFractionalPacking G (fun t ↦ w t + v t) := by
  constructor
  · intro t ht
    exact add_nonneg (hw.1 t ht) (hv t ht)
  · intro e he
    rw [fractionalEdgeLoad_add]
    exact (add_le_add (hw.2 e he) le_rfl).trans (hedge e he)

/-- Pointwise-disjoint half-bounded packings remain half-bounded after
addition.  In D5 the old triangles avoid `u`, while every attached triangle
contains `u`, so the disjointness premise is automatic. -/
lemma IsHalfBounded.add_of_pointwise_disjoint {G : SimpleGraph A}
    {w v : Finset A → ℝ} (hw : IsHalfBounded G w) (hv : IsHalfBounded G v)
    (hdisj : ∀ t ∈ G.cliqueFinset 3, w t = 0 ∨ v t = 0) :
    IsHalfBounded G (fun t ↦ w t + v t) := by
  intro t ht
  rcases hdisj t ht with hzero | hzero
  · dsimp
    rw [hzero, zero_add]
    exact hv t ht
  · dsimp
    rw [hzero, add_zero]
    exact hw t ht

/-! ## Removing triangles outside the support graph -/

/-- In a nonnegative capacity packing of the complete graph, a triangle which
is not a triangle of the capacity support graph has weight zero.  Indeed, it
contains a support nonedge; that edge has capacity and hence load zero. -/
lemma IsCapacityPacking.eq_zero_of_not_support_triangle
    {U : Type*} [Fintype U] [DecidableEq U]
    {H : SimpleGraph U} {c : Sym2 U → ℝ} {w : Finset U → ℝ}
    (hw : IsCapacityPacking (⊤ : SimpleGraph U) c w)
    (hcSupport : ∀ e, e ∉ H.edgeSet → c e = 0)
    {t : Finset U} (htTop : (⊤ : SimpleGraph U).IsNClique 3 t)
    (htH : ¬H.IsNClique 3 t) : w t = 0 := by
  classical
  letI : DecidableRel (⊤ : SimpleGraph U).Adj := Classical.decRel _
  letI : DecidableRel H.Adj := Classical.decRel _
  have htTopMem : t ∈ (⊤ : SimpleGraph U).cliqueFinset 3 :=
    SimpleGraph.mem_cliqueFinset_iff.mpr htTop
  have hnotClique : ¬H.IsClique (t : Set U) := by
    intro hclique
    apply htH
    exact ⟨hclique, htTop.card_eq⟩
  obtain ⟨x, y, hxy, hnxy⟩ := H.not_isClique_iff.mp hnotClique
  let p : Sym2 U := s((x : U), (y : U))
  have hpTop : p ∈ (⊤ : SimpleGraph U).edgeFinset := by
    simp [p, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, hxy]
  have hpNotH : p ∉ H.edgeSet := by
    intro hp
    apply hnxy
    simpa [p, SimpleGraph.mem_edgeSet] using hp
  have hpCap : c p = 0 := hcSupport p hpNotH
  have hloadUpper : fractionalEdgeLoad (⊤ : SimpleGraph U) w p ≤ 0 := by
    simpa only [hpCap] using hw.2 p hpTop
  have htFilter : t ∈ ((⊤ : SimpleGraph U).cliqueFinset 3).filter
      (fun q ↦ p ∈ q.sym2) := by
    apply Finset.mem_filter.mpr
    refine ⟨htTopMem, ?_⟩
    exact Finset.mk_mem_sym2_iff.mpr ⟨x.property, y.property⟩
  have hweightLoad : w t ≤ fractionalEdgeLoad (⊤ : SimpleGraph U) w p := by
    unfold fractionalEdgeLoad
    apply Finset.single_le_sum
    · intro q hq
      exact hw.1 q (Finset.mem_filter.mp hq).1
    · exact htFilter
  have hnonneg : 0 ≤ w t := hw.1 t htTopMem
  linarith

/-- Consequently zero-extension to the support graph does not change a
capacity packing pointwise on complete-graph triangles. -/
lemma zeroExtendTriangleWeight_eq_of_capacity_support
    {U : Type*} [Fintype U] [DecidableEq U]
    {H : SimpleGraph U} {c : Sym2 U → ℝ} {w : Finset U → ℝ}
    (hw : IsCapacityPacking (⊤ : SimpleGraph U) c w)
    (hcSupport : ∀ e, e ∉ H.edgeSet → c e = 0)
    {t : Finset U} (htTop : (⊤ : SimpleGraph U).IsNClique 3 t) :
    zeroExtendTriangleWeight H w t = w t := by
  classical
  letI : DecidableRel H.Adj := Classical.decRel _
  by_cases htH : H.IsNClique 3 t
  · exact zeroExtendTriangleWeight_of_mem
      (SimpleGraph.mem_cliqueFinset_iff.mpr htH)
  · rw [zeroExtendTriangleWeight_of_not_mem
        (fun h ↦ htH (SimpleGraph.mem_cliqueFinset_iff.mp h)),
      hw.eq_zero_of_not_support_triangle hcSupport htTop htH]

lemma fractionalEdgeLoad_zeroExtend_eq_of_capacity_support
    {U : Type*} [Fintype U] [DecidableEq U]
    {H : SimpleGraph U} {c : Sym2 U → ℝ} {w : Finset U → ℝ}
    (hw : IsCapacityPacking (⊤ : SimpleGraph U) c w)
    (hcSupport : ∀ e, e ∉ H.edgeSet → c e = 0) (p : Sym2 U) :
    fractionalEdgeLoad (⊤ : SimpleGraph U) (zeroExtendTriangleWeight H w) p =
      fractionalEdgeLoad (⊤ : SimpleGraph U) w p := by
  letI : DecidableRel (⊤ : SimpleGraph U).Adj :=
    Classical.decRel _
  unfold fractionalEdgeLoad
  apply Finset.sum_congr rfl
  intro t ht
  apply zeroExtendTriangleWeight_eq_of_capacity_support hw hcSupport
  exact SimpleGraph.mem_cliqueFinset_iff.mp (Finset.mem_filter.mp ht).1

lemma capacityUncoveredWeight_zeroExtend_eq_of_capacity_support
    {U : Type*} [Fintype U] [DecidableEq U]
    {H : SimpleGraph U} {c : Sym2 U → ℝ} {w : Finset U → ℝ}
    (hw : IsCapacityPacking (⊤ : SimpleGraph U) c w)
    (hcSupport : ∀ e, e ∉ H.edgeSet → c e = 0) :
    capacityUncoveredWeight (⊤ : SimpleGraph U) c
        (zeroExtendTriangleWeight H w) =
      capacityUncoveredWeight (⊤ : SimpleGraph U) c w := by
  unfold capacityUncoveredWeight
  apply Finset.sum_congr rfl
  intro e he
  rw [fractionalEdgeLoad_zeroExtend_eq_of_capacity_support hw hcSupport]

/-- Restricting a complete-graph capacity packing to its support graph
preserves feasibility. -/
lemma IsCapacityPacking.zeroExtend_support
    {U : Type*} [Fintype U] [DecidableEq U]
    {H : SimpleGraph U} {c : Sym2 U → ℝ} {w : Finset U → ℝ}
    (hw : IsCapacityPacking (⊤ : SimpleGraph U) c w)
    (hcSupport : ∀ e, e ∉ H.edgeSet → c e = 0) :
    IsCapacityPacking H c (zeroExtendTriangleWeight H w) := by
  classical
  letI : DecidableRel (⊤ : SimpleGraph U).Adj := Classical.decRel _
  letI : DecidableRel H.Adj := Classical.decRel _
  constructor
  · intro t htH
    rw [zeroExtendTriangleWeight_of_mem htH]
    apply hw.1 t
    exact SimpleGraph.cliqueFinset_mono (⊤ : SimpleGraph U) le_top htH
  · intro e heH
    have heTop : e ∈ (⊤ : SimpleGraph U).edgeFinset := by
      exact SimpleGraph.mem_edgeFinset.mpr
        (SimpleGraph.edgeSet_mono le_top (SimpleGraph.mem_edgeFinset.mp heH))
    calc
      fractionalEdgeLoad H (zeroExtendTriangleWeight H w) e =
          fractionalEdgeLoad H w e :=
        fractionalEdgeLoad_zeroExtend le_rfl w e
      _ = fractionalEdgeLoad (⊤ : SimpleGraph U)
          (zeroExtendTriangleWeight H w) e :=
        (fractionalEdgeLoad_zeroExtend le_top w e).symm
      _ = fractionalEdgeLoad (⊤ : SimpleGraph U) w e :=
        fractionalEdgeLoad_zeroExtend_eq_of_capacity_support hw hcSupport e
      _ ≤ c e := hw.2 e heTop

@[simp] lemma halfEdgeCapacity_eq_zero_of_not_edgeSet
    (H : SimpleGraph A) (C : Finset (Sym2 A)) {e : Sym2 A}
    (he : e ∉ H.edgeSet) : halfEdgeCapacity H C e = 0 := by
  simp [halfEdgeCapacity, he]

/-- The output of the weighted reduction for `halfEdgeCapacity` can be
chosen to be supported on the underlying graph `H`, without changing its
uncovered capacity or its half-bound. -/
lemma supportedPacking_of_halfEdgeCapacity
    (H : SimpleGraph A) (C : Finset (Sym2 A)) {w : Finset A → ℝ} {a : ℝ}
    (hw : IsCapacityPacking (⊤ : SimpleGraph A)
      (halfEdgeCapacity H C) w)
    (hunc : capacityUncoveredWeight (⊤ : SimpleGraph A)
      (halfEdgeCapacity H C) w ≤ a)
    (hhalf : IsHalfBounded (⊤ : SimpleGraph A) w) :
    ∃ v : Finset A → ℝ,
      IsCapacityPacking H (halfEdgeCapacity H C) v ∧
      capacityUncoveredWeight (⊤ : SimpleGraph A)
        (halfEdgeCapacity H C) v ≤ a ∧
      IsHalfBounded (⊤ : SimpleGraph A) v := by
  classical
  letI : DecidableRel (⊤ : SimpleGraph A).Adj := Classical.decRel _
  let v := zeroExtendTriangleWeight H w
  have hsupport : ∀ e, e ∉ H.edgeSet → halfEdgeCapacity H C e = 0 :=
    fun e he ↦ halfEdgeCapacity_eq_zero_of_not_edgeSet H C he
  refine ⟨v, hw.zeroExtend_support hsupport, ?_, ?_⟩
  · rw [show capacityUncoveredWeight (⊤ : SimpleGraph A)
        (halfEdgeCapacity H C) v =
        capacityUncoveredWeight (⊤ : SimpleGraph A)
          (halfEdgeCapacity H C) w by
      exact capacityUncoveredWeight_zeroExtend_eq_of_capacity_support
        hw hsupport]
    exact hunc
  · intro t htTop
    dsimp only [v]
    rw [zeroExtendTriangleWeight_eq_of_capacity_support hw hsupport
      (SimpleGraph.mem_cliqueFinset_iff.mp htTop)]
    exact hhalf t htTop

/-- The weighted output in D5 may be chosen to live on the deleted-vertex
graph itself.  This is the support-respecting form needed before extending
the weighting back to the ambient graph and adjoining the half-cycle
triangles through `u`. -/
theorem d5_supportedWeightedPacking_of_augmentedCycle {n a α : ℕ}
    (hcard : Fintype.card A = n) (hn : 5 ≤ n) (ha : a ≤ 4)
    (G : SimpleGraph A) (u : A)
    (hαa : α ≤ a) (hαd : α ≤ G.degree u)
    (hstrong : AlmostCompleteStrongAt (n - 1))
    (hmissing : missingEdgeCount G ≤ n - 4 + a)
    (hlarge : n + α + 1 ≤ 3 * Gᶜ.degree u)
    (C : Finset (Sym2 (↑((Finset.univ : Finset A).erase u))))
    (hcardC : C.card = G.degree u)
    (habsent : (C.filter fun e ↦ e ∉ (G.induce
      (↑((Finset.univ : Finset A).erase u) : Set A)).edgeSet).card = α) :
    ∃ w : Finset (↑((Finset.univ : Finset A).erase u)) → ℝ,
      IsCapacityPacking (G.induce
        (↑((Finset.univ : Finset A).erase u) : Set A))
        (halfEdgeCapacity (G.induce
          (↑((Finset.univ : Finset A).erase u) : Set A))
          (presentCycleEdges (G.induce
            (↑((Finset.univ : Finset A).erase u) : Set A)) C)) w ∧
      capacityUncoveredWeight (⊤ : SimpleGraph
        (↑((Finset.univ : Finset A).erase u)))
          (halfEdgeCapacity (G.induce
            (↑((Finset.univ : Finset A).erase u) : Set A))
            (presentCycleEdges (G.induce
              (↑((Finset.univ : Finset A).erase u) : Set A)) C)) w ≤
        ((a - α : ℕ) : ℝ) ∧
      IsHalfBounded (⊤ : SimpleGraph
        (↑((Finset.univ : Finset A).erase u))) w := by
  let S : Finset A := Finset.univ.erase u
  let H : SimpleGraph S := G.induce (S : Set A)
  let P : Finset (Sym2 S) := presentCycleEdges H C
  obtain ⟨w, hw, hunc, hhalf⟩ :=
    d5_weightedPacking_of_augmentedCycle hcard hn ha G u hαa hαd
      hstrong hmissing hlarge C hcardC habsent
  exact supportedPacking_of_halfEdgeCapacity H P hw hunc hhalf

/-! ## Extending and adjoining the D5 attachment -/

/-- A half-bound on the complete graph of an induced subtype is preserved by
extension by zero to the ambient complete graph. -/
lemma IsHalfBounded.extendInduced {S : Finset A} {w : Finset S → ℝ}
    (hw : IsHalfBounded (⊤ : SimpleGraph S) w) :
    IsHalfBounded (⊤ : SimpleGraph A) (extendInducedWeight S w) := by
  intro t ht
  have htNC : (⊤ : SimpleGraph A).IsNClique 3 t := by
    simpa only [SimpleGraph.cliqueFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] using ht
  by_cases hsub : t ⊆ S
  · let q : Finset S := restrictToInduced S t hsub
    have hmap : q.map (inducedEmbedding S) = t := by
      simpa only [q, restrictToInduced, inducedEmbedding] using
        (Finset.subtype_map_of_mem hsub)
    have hcard : q.card = 3 := by
      have htcard : t.card = 3 := htNC.card_eq
      rw [← Finset.card_map (inducedEmbedding S), hmap]
      exact htcard
    have hqNC : (⊤ : SimpleGraph S).IsNClique 3 q := by
      refine ⟨?_, hcard⟩
      intro x hx y hy hxy
      simp only [SimpleGraph.top_adj]
      exact hxy
    rw [extendInducedWeight, dif_pos hsub]
    apply hw q
    simpa only [SimpleGraph.cliqueFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] using hqNC
  · rw [extendInducedWeight_eq_zero hsub]
    norm_num

/-- Old induced triangles and newly attached triangles have disjoint support:
the former avoid `u`, while the latter contain it. -/
lemma extendInducedWeight_or_attachedEdgeWeight_eq_zero
    {S : Finset A} {u : A} (hu : u ∉ S) (w : Finset S → ℝ)
    (C : Finset (Sym2 S)) (r : ℝ) (t : Finset A) :
    extendInducedWeight S w t = 0 ∨ attachedEdgeWeight S u C r t = 0 := by
  classical
  by_cases hut : u ∈ t
  · left
    apply extendInducedWeight_eq_zero
    intro hsub
    exact hu (hsub hut)
  · right
    apply attachedEdgeWeight_eq_zero_of_not_exists
    rintro ⟨e, heC, rfl⟩
    apply hut
    simp [attachedEdgeTriangle]

/-- On the support graph, replacing capacity one by capacity one half on
`C` decreases total uncovered capacity by exactly `|C|/2`. -/
lemma fractionalUncoveredWeight_eq_capacityUncoveredWeight_halfEdgeCapacity
    (H : SimpleGraph A) (C : Finset (Sym2 A)) (w : Finset A → ℝ)
    (hCH : ∀ e ∈ C, e ∈ H.edgeSet) :
    fractionalUncoveredWeight H w =
      capacityUncoveredWeight H (halfEdgeCapacity H C) w +
        (C.card : ℝ) / 2 := by
  classical
  have hCedges : C ⊆ H.edgeFinset := by
    intro e he
    exact SimpleGraph.mem_edgeFinset.mpr (hCH e he)
  unfold fractionalUncoveredWeight capacityUncoveredWeight
  calc
    (∑ e ∈ H.edgeFinset, (1 - fractionalEdgeLoad H w e)) =
        ∑ e ∈ H.edgeFinset,
          ((halfEdgeCapacity H C e - fractionalEdgeLoad H w e) +
            if e ∈ C then (1 / 2 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro e he
      have heSet : e ∈ H.edgeSet := SimpleGraph.mem_edgeFinset.mp he
      by_cases heC : e ∈ C <;>
        simp [halfEdgeCapacity, heSet, heC] <;> ring
    _ = (∑ e ∈ H.edgeFinset,
          (halfEdgeCapacity H C e - fractionalEdgeLoad H w e)) +
        ∑ e ∈ H.edgeFinset,
          (if e ∈ C then (1 / 2 : ℝ) else 0) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ e ∈ H.edgeFinset,
          (halfEdgeCapacity H C e - fractionalEdgeLoad H w e)) +
        (C.card : ℝ) / 2 := by
      rw [sum_indicator_mem_eq_card_mul H.edgeFinset C hCedges]
      ring

/-- Zero extension converts the complete-graph half-capacity sum into the
same half-capacity sum over its support graph. -/
lemma capacityUncoveredWeight_halfEdgeCapacity_zeroExtend
    (H : SimpleGraph A) (C : Finset (Sym2 A)) (w : Finset A → ℝ) :
    capacityUncoveredWeight (⊤ : SimpleGraph A) (halfEdgeCapacity H C)
        (zeroExtendTriangleWeight H w) =
      capacityUncoveredWeight H (halfEdgeCapacity H C) w := by
  classical
  unfold capacityUncoveredWeight
  simp_rw [fractionalEdgeLoad_zeroExtend le_top]
  have hsub : H.edgeFinset ⊆
      @SimpleGraph.edgeFinset A (⊤ : SimpleGraph A)
        (@SimpleGraph.fintypeEdgeSet A (⊤ : SimpleGraph A) Sym2.instFintype
          (fun a b ↦ Classical.propDecidable ((⊤ : SimpleGraph A).Adj a b))) := by
    intro e he
    have heND : ¬ e.IsDiag := H.not_isDiag_of_mem_edgeFinset he
    induction e using Sym2.inductionOn with
    | hf x y =>
        simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using heND
  symm
  apply Finset.sum_subset hsub
  intro e heTop heH
  have heND : ¬ e.IsDiag :=
    @SimpleGraph.not_isDiag_of_mem_edgeFinset A (⊤ : SimpleGraph A) e
      (@SimpleGraph.fintypeEdgeSet A (⊤ : SimpleGraph A) Sym2.instFintype
        (fun a b ↦ Classical.propDecidable ((⊤ : SimpleGraph A).Adj a b))) heTop
  have heHSet : e ∉ H.edgeSet := fun he ↦
    heH (SimpleGraph.mem_edgeFinset.mpr he)
  rw [halfEdgeCapacity_eq_zero_of_not_edgeSet H C heHSet,
    fractionalEdgeLoad_eq_zero_of_not_edge H w heND heH]
  norm_num

/-- Extending a triangle weighting by zero from a graph to that same graph
does not change any of its edge loads, and hence does not change its total
uncovered capacity. -/
lemma capacityUncoveredWeight_zeroExtend_sameGraph
    (H : SimpleGraph A) (c : Sym2 A → ℝ) (w : Finset A → ℝ) :
    capacityUncoveredWeight H c (zeroExtendTriangleWeight H w) =
      capacityUncoveredWeight H c w := by
  classical
  unfold capacityUncoveredWeight
  apply Finset.sum_congr rfl
  intro e he
  rw [fractionalEdgeLoad_zeroExtend le_rfl]

/-- The half-edge capacity is also a genuine capacity on its support graph,
not merely on the ambient complete graph. -/
lemma halfEdgeCapacity_isEdgeCapacity_support (H : SimpleGraph A)
    (C : Finset (Sym2 A)) : IsEdgeCapacity H (halfEdgeCapacity H C) := by
  classical
  constructor
  · intro e he
    have heSet : e ∈ H.edgeSet := SimpleGraph.mem_edgeFinset.mp he
    by_cases heC : e ∈ C <;>
      simp [halfEdgeCapacity, heSet, heC] <;> norm_num
  · intro e he
    have heSet : e ∉ H.edgeSet := fun h ↦
      he (SimpleGraph.mem_edgeFinset.mpr h)
    exact halfEdgeCapacity_eq_zero_of_not_edgeSet H C heSet

/-- Algebraic core of the D5 construction.  A packing of the deleted-vertex
graph with half-capacity on selected cycle edges is extended by zero, then a
triangle of weight `1/2` is attached through `u` to every selected edge.
The endpoint and incidence hypotheses are precisely the two elementary
properties supplied by a (possibly augmented and then filtered) cycle. -/
theorem d5_combinedWeight_isFractionalPacking
    (G : SimpleGraph A) (u : A)
    (C : Finset (Sym2 (↑((Finset.univ : Finset A).erase u))))
    (hCG : ∀ e ∈ C, e ∈ (G.induce
      (↑((Finset.univ : Finset A).erase u) : Set A)).edgeSet)
    (hstar : ∀ e ∈ C,
      ∀ x : ↑((Finset.univ : Finset A).erase u), x ∈ e → G.Adj u x)
    (hinc : ∀ p ∈ G.edgeFinset,
      (C.filter fun e ↦ p ∈ (attachedEdgeTriangle
        (Finset.univ.erase u) u e).sym2).card ≤ 2)
    {w : Finset (↑((Finset.univ : Finset A).erase u)) → ℝ}
    (hw : IsCapacityPacking (G.induce
      (↑((Finset.univ : Finset A).erase u) : Set A))
      (halfEdgeCapacity (G.induce
        (↑((Finset.univ : Finset A).erase u) : Set A)) C) w)
    (hhalf : IsHalfBounded (⊤ : SimpleGraph
      (↑((Finset.univ : Finset A).erase u))) w) :
    let S : Finset A := Finset.univ.erase u
    let W : Finset A → ℝ := fun t ↦
      extendInducedWeight S w t + attachedEdgeWeight S u C (1 / 2) t
    IsFractionalPacking G W ∧ IsHalfBounded G W := by
  classical
  let S : Finset A := Finset.univ.erase u
  let H : SimpleGraph S := G.induce (S : Set A)
  let old : Finset A → ℝ := extendInducedWeight S w
  let add : Finset A → ℝ := attachedEdgeWeight S u C (1 / 2)
  have hu : u ∉ S := by simp [S]
  have hAttach : IsFractionalPacking G add := by
    dsimp only [add]
    exact attachedEdgeWeight_isFractionalPacking_half hCG hstar hinc
  have hOld : IsFractionalPacking G old := by
    dsimp only [old]
    apply IsFractionalPacking.extendInduced
    exact hw.toFractionalPacking (halfEdgeCapacity_isEdgeCapacity_support H C)
  have hpacking : IsFractionalPacking G (fun t ↦ old t + add t) := by
    constructor
    · intro t ht
      exact add_nonneg (hOld.1 t ht) (hAttach.1 t ht)
    · intro p hp
      rw [fractionalEdgeLoad_add]
      induction p using Sym2.inductionOn with
      | hf x y =>
          by_cases hx : x ∈ S
          · by_cases hy : y ∈ S
            · let xS : S := ⟨x, hx⟩
              let yS : S := ⟨y, hy⟩
              let q : Sym2 S := s(xS, yS)
              have hmap : (inducedEmbedding S).sym2Map q = s(x, y) := rfl
              have hxy : G.Adj x y := by
                simpa only [SimpleGraph.mem_edgeFinset,
                  SimpleGraph.mem_edgeSet] using hp
              have hqSet : q ∈ H.edgeSet := by
                dsimp only [q]
                change H.Adj xS yS
                change G.Adj x y
                exact hxy
              have hq : q ∈ H.edgeFinset :=
                SimpleGraph.mem_edgeFinset.mpr hqSet
              have hqND : ¬q.IsDiag := H.not_isDiag_of_mem_edgeFinset hq
              have hOldLoad : fractionalEdgeLoad G old s(x, y) =
                  fractionalEdgeLoad H w q := by
                dsimp only [old]
                rw [← hmap, fractionalEdgeLoad_extendInducedWeight]
              have hAddLoad : fractionalEdgeLoad G add s(x, y) =
                  if q ∈ C then (1 / 2 : ℝ) else 0 := by
                dsimp only [add]
                rw [← hmap]
                exact fractionalEdgeLoad_attachedEdgeWeight_induced
                  hu hCG hstar hqND
              have hcap : fractionalEdgeLoad H w q ≤
                  halfEdgeCapacity H C q := by
                simpa only [H, S] using hw.2 q hq
              rw [hOldLoad, hAddLoad]
              by_cases hqC : q ∈ C <;>
                simp [halfEdgeCapacity, hqSet, hqC] at hcap ⊢ <;> linarith
            · have hyu : y = u := by simpa [S] using hy
              subst y
              have hp' : s(u, x) ∈ G.edgeFinset := by
                rw [show s(u, x) = s(x, u) from
                  Sym2.sound (Sym2.Rel.swap u x)]
                exact hp
              rw [show s(x, u) = s(u, x) from
                Sym2.sound (Sym2.Rel.swap x u)]
              have hzero : fractionalEdgeLoad G old s(u, x) = 0 := by
                dsimp only [old]
                exact edgeLoad_extendInducedWeight_eq_zero_of_not_mem_AC
                  G S w u x hu
              rw [hzero, zero_add]
              exact hAttach.2 s(u, x) hp'
          · have hxu : x = u := by simpa [S] using hx
            subst x
            have hzero : fractionalEdgeLoad G old s(u, y) = 0 := by
              dsimp only [old]
              exact edgeLoad_extendInducedWeight_eq_zero_of_not_mem_AC
                G S w u y hu
            rw [hzero, zero_add]
            exact hAttach.2 s(u, y) hp
  have hhalfOld : IsHalfBounded G old := by
    dsimp only [old]
    have htop := IsHalfBounded.extendInduced hhalf
    intro t ht
    apply htop t
    have htNC : G.IsNClique 3 t := by
      simpa only [SimpleGraph.cliqueFinset, Finset.mem_filter,
        Finset.mem_univ, true_and] using ht
    have htopNC : (⊤ : SimpleGraph A).IsNClique 3 t := htNC.mono le_top
    simpa only [SimpleGraph.cliqueFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] using htopNC
  have hhalfAdd : IsHalfBounded G add := by
    dsimp only [add]
    exact attachedEdgeWeight_halfBounded hu hCG
  have hhalfW : IsHalfBounded G (fun t ↦ old t + add t) :=
    hhalfOld.add_of_pointwise_disjoint hhalfAdd fun t _ ↦ by
      dsimp only [old, add]
      exact extendInducedWeight_or_attachedEdgeWeight_eq_zero hu w C (1 / 2) t
  simpa only [S, old, add] using And.intro hpacking hhalfW

/-- Splitting off one vertex partitions the ambient edge set into the edges
of the induced complement and the edges incident with that vertex. -/
lemma card_edgeSet_induce_univ_erase_add_degree (G : SimpleGraph A) (u : A) :
    Nat.card G.edgeSet =
      Nat.card (G.induce
        (↑((Finset.univ : Finset A).erase u) : Set A)).edgeSet +
        G.degree u := by
  classical
  let S : Finset A := Finset.univ.erase u
  have hset : (↑S : Set A) = ({u} : Set A)ᶜ := by
    ext x
    simp [S]
  have hbij : Set.BijOn (id : A → A) (↑S : Set A) ({u} : Set A)ᶜ := by
    rw [← hset]
    exact Set.bijOn_id _
  let φ : G.induce (↑S : Set A) ≃g G.induce ({u} : Set A)ᶜ :=
    (SimpleGraph.Iso.refl : G ≃g G).induce hbij
  have hind : (G.induce (↑S : Set A)).edgeFinset.card =
      G.edgeFinset.card - G.degree u := by
    calc
      (G.induce (↑S : Set A)).edgeFinset.card =
          (G.induce ({u} : Set A)ᶜ).edgeFinset.card := φ.card_edgeFinset_eq
      _ = (G.deleteIncidenceSet u).edgeFinset.card :=
        G.card_edgeFinset_induce_compl_singleton u
      _ = G.edgeFinset.card - G.degree u :=
        G.card_edgeFinset_deleteIncidenceSet u
  have hdeg : G.degree u ≤ G.edgeFinset.card :=
    G.degree_le_card_edgeFinset u
  have hcard : G.edgeFinset.card =
      (G.induce (↑S : Set A)).edgeFinset.card + G.degree u := by
    rw [hind, Nat.sub_add_cancel hdeg]
  simpa only [S, Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet] using hcard

/-- Exact uncovered-weight identity for the D5 combined weighting.  The
deleted graph contributes its half-capacity deficit; the new star contributes
one unit for each neighbor, while each selected edge creates a triangle that
covers three half-edges in total. -/
lemma fractionalUncoveredWeight_d5_combined
    (G : SimpleGraph A) (u : A)
    (C : Finset (Sym2 (↑((Finset.univ : Finset A).erase u))))
    (w : Finset (↑((Finset.univ : Finset A).erase u)) → ℝ)
    (hCG : ∀ e ∈ C, e ∈ (G.induce
      (↑((Finset.univ : Finset A).erase u) : Set A)).edgeSet)
    (hstar : ∀ e ∈ C,
      ∀ x : ↑((Finset.univ : Finset A).erase u), x ∈ e → G.Adj u x) :
    let S : Finset A := Finset.univ.erase u
    let H : SimpleGraph S := G.induce (S : Set A)
    fractionalUncoveredWeight G (fun t ↦
      extendInducedWeight S w t + attachedEdgeWeight S u C (1 / 2) t) =
      capacityUncoveredWeight H (halfEdgeCapacity H C) w +
        (G.degree u : ℝ) - (C.card : ℝ) := by
  classical
  dsimp only
  let S : Finset A := Finset.univ.erase u
  have hu : u ∉ S := by simp [S]
  have hcardReal : (Nat.card G.edgeSet : ℝ) =
      (Nat.card (G.induce
        (↑((Finset.univ : Finset A).erase u) : Set A)).edgeSet : ℝ) +
        (G.degree u : ℝ) := by
    exact_mod_cast card_edgeSet_induce_univ_erase_add_degree G u
  have hsupport : fractionalUncoveredWeight (G.induce
      (↑((Finset.univ : Finset A).erase u) : Set A)) w =
      capacityUncoveredWeight (G.induce
        (↑((Finset.univ : Finset A).erase u) : Set A))
        (halfEdgeCapacity (G.induce
          (↑((Finset.univ : Finset A).erase u) : Set A)) C) w +
        (C.card : ℝ) / 2 :=
    fractionalUncoveredWeight_eq_capacityUncoveredWeight_halfEdgeCapacity
      (G.induce (↑((Finset.univ : Finset A).erase u) : Set A)) C w hCG
  rw [fractionalUncoveredWeight_eq_card_sub_general] at hsupport
  have hsizeAdd : fractionalSize G (fun t ↦
      extendInducedWeight (Finset.univ.erase u) w t +
        attachedEdgeWeight (Finset.univ.erase u) u C (1 / 2) t) =
      fractionalSize G (extendInducedWeight (Finset.univ.erase u) w) +
        fractionalSize G
          (attachedEdgeWeight (Finset.univ.erase u) u C (1 / 2)) := by
    unfold fractionalSize
    rw [Finset.sum_add_distrib]
  rw [fractionalUncoveredWeight_eq_card_sub_general,
    hsizeAdd,
    fractionalSize_extendInducedWeight,
    fractionalSize_attachedEdgeWeight hu hCG hstar,
    hcardReal]
  linarith

/-- Core D5 conclusion from the set of genuine selected cycle edges.  The
weighted-reduction packing supplies the old triangles, and each selected
edge is adjoined to `u` with weight `1/2`.  This formulation also covers the
paper's exceptional two-neighbor case, in which the same edge is viewed as
one present and one missing edge of a length-two cycle. -/
theorem d5_case_of_selectedEdges {n a α : ℕ}
    (hcard : Fintype.card A = n) (hn : 5 ≤ n) (ha : a ≤ 4)
    (G : SimpleGraph A) (u : A)
    (hαa : α ≤ a) (hαd : α ≤ G.degree u)
    (hstrong : AlmostCompleteStrongAt (n - 1))
    (hmissing : missingEdgeCount G ≤ n - 4 + a)
    (hlarge : n + α + 1 ≤ 3 * Gᶜ.degree u)
    (P : Finset (Sym2 (↑((Finset.univ : Finset A).erase u))))
    (hPH : ∀ e ∈ P, e ∈ (G.induce
      (↑((Finset.univ : Finset A).erase u) : Set A)).edgeSet)
    (hcardP : P.card = G.degree u - α)
    (hstar : ∀ e ∈ P,
      ∀ x : ↑((Finset.univ : Finset A).erase u), x ∈ e → G.Adj u x)
    (hinc : ∀ p ∈ G.edgeFinset,
      (P.filter fun e ↦
        p ∈ (attachedEdgeTriangle (Finset.univ.erase u) u e).sym2).card ≤ 2) :
    HasStrongFractionalPacking G (a : ℝ) := by
  classical
  letI : DecidableRel (⊤ : SimpleGraph
      (↑((Finset.univ : Finset A).erase u))).Adj := Classical.decRel _
  let S : Finset A := Finset.univ.erase u
  let H : SimpleGraph S := G.induce (S : Set A)
  obtain ⟨w, hw, hunc, hhalf⟩ :=
    d5_weightedPacking_on_vertexComplement hcard hn ha G u hαa hαd
      hstrong hmissing hlarge P hPH hcardP
  let v : Finset S → ℝ := zeroExtendTriangleWeight H w
  let W : Finset A → ℝ := fun t ↦
    extendInducedWeight S v t + attachedEdgeWeight S u P (1 / 2) t
  have hsupport : ∀ e, e ∉ H.edgeSet → halfEdgeCapacity H P e = 0 :=
    fun e he ↦ halfEdgeCapacity_eq_zero_of_not_edgeSet H P he
  have hvPacking : IsCapacityPacking H (halfEdgeCapacity H P) v := by
    dsimp only [v]
    exact hw.zeroExtend_support hsupport
  have hvHalfRaw : IsHalfBounded (⊤ : SimpleGraph
      (↑((Finset.univ : Finset A).erase u)))
      (zeroExtendTriangleWeight (G.induce
        (↑((Finset.univ : Finset A).erase u) : Set A)) w) := by
    intro t htTop
    rw [zeroExtendTriangleWeight_eq_of_capacity_support hw hsupport
      (SimpleGraph.mem_cliqueFinset_iff.mp htTop)]
    exact hhalf t htTop
  have hvHalf : IsHalfBounded (⊤ : SimpleGraph S) v := by
    simpa only [S, H, v] using hvHalfRaw
  have hcombined : IsFractionalPacking G W ∧ IsHalfBounded G W := by
    simpa only [S, H, W] using
      (d5_combinedWeight_isFractionalPacking G u P hPH hstar hinc
        hvPacking hvHalf)
  have hvUncovered :
      capacityUncoveredWeight H (halfEdgeCapacity H P) v ≤
        ((a - α : ℕ) : ℝ) := by
    calc
      capacityUncoveredWeight H (halfEdgeCapacity H P) v =
          capacityUncoveredWeight H (halfEdgeCapacity H P) w := by
        dsimp only [v]
        exact capacityUncoveredWeight_zeroExtend_sameGraph H
          (halfEdgeCapacity H P) w
      _ = capacityUncoveredWeight (⊤ : SimpleGraph S)
          (halfEdgeCapacity H P) v := by
        dsimp only [v]
        exact (capacityUncoveredWeight_halfEdgeCapacity_zeroExtend H P w).symm
      _ = capacityUncoveredWeight (⊤ : SimpleGraph S)
          (halfEdgeCapacity H P) w := by
        dsimp only [v]
        exact capacityUncoveredWeight_zeroExtend_eq_of_capacity_support
          hw hsupport
      _ ≤ ((a - α : ℕ) : ℝ) := by
        simpa only [S, H] using hunc
  refine ⟨W, hcombined.1, ?_, hcombined.2⟩
  have hid : fractionalUncoveredWeight G W =
      capacityUncoveredWeight H (halfEdgeCapacity H P) v +
        (G.degree u : ℝ) - (P.card : ℝ) := by
    simpa only [S, H, W] using
      (fractionalUncoveredWeight_d5_combined G u P v hPH hstar)
  rw [hid, hcardP]
  rw [Nat.cast_sub hαa] at hvUncovered
  rw [Nat.cast_sub hαd]
  linarith

/-- Complete D5 conclusion once the augmented Hamilton-cycle data have been
constructed.  Filtering the augmented cycle to its genuine graph edges
produces the selected-edge input of `d5_case_of_selectedEdges`. -/
theorem d5_case_of_augmentedCycle {n a α : ℕ}
    (hcard : Fintype.card A = n) (hn : 5 ≤ n) (ha : a ≤ 4)
    (G : SimpleGraph A) (u : A)
    (hαa : α ≤ a) (hαd : α ≤ G.degree u)
    (hstrong : AlmostCompleteStrongAt (n - 1))
    (hmissing : missingEdgeCount G ≤ n - 4 + a)
    (hlarge : n + α + 1 ≤ 3 * Gᶜ.degree u)
    (C : Finset (Sym2 (↑((Finset.univ : Finset A).erase u))))
    (hcardC : C.card = G.degree u)
    (habsent : (C.filter fun e ↦ e ∉ (G.induce
      (↑((Finset.univ : Finset A).erase u) : Set A)).edgeSet).card = α)
    (hstar : ∀ e ∈ presentCycleEdges (G.induce
        (↑((Finset.univ : Finset A).erase u) : Set A)) C,
      ∀ x : ↑((Finset.univ : Finset A).erase u), x ∈ e → G.Adj u x)
    (hinc : ∀ p ∈ G.edgeFinset,
      ((presentCycleEdges (G.induce
          (↑((Finset.univ : Finset A).erase u) : Set A)) C).filter fun e ↦
        p ∈ (attachedEdgeTriangle (Finset.univ.erase u) u e).sym2).card ≤ 2) :
    HasStrongFractionalPacking G (a : ℝ) := by
  apply d5_case_of_selectedEdges hcard hn ha G u hαa hαd hstrong
    hmissing hlarge
    (presentCycleEdges (G.induce
      (↑((Finset.univ : Finset A).erase u) : Set A)) C)
    (presentCycleEdges_mem_edgeSet _ _)
  · exact card_presentCycleEdges hcardC habsent
  · exact hstar
  · exact hinc

/-- The elementary low-degree part of D5.  A zero-uncovered induction
packing on `G - u` extends to `G`; its only additional uncovered edges are
the `degree u` edges incident with `u`.  The hypotheses `degree u ≤ 2` and
`a ≤ 4` ensure that the deleted graph lies in the zero-defect induction
range. -/
theorem d5_lowDegree_case {n a : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n) (ha : a ≤ 4)
    (G : SimpleGraph A) (u : A)
    (hdegreeSmall : G.degree u ≤ 2) (hdegreeBudget : G.degree u ≤ a)
    (hstrong : AlmostCompleteStrongAt (n - 1))
    (hmissing : missingEdgeCount G ≤ n - 4 + a) :
    HasStrongFractionalPacking G (a : ℝ) := by
  classical
  letI : DecidableRel (⊤ : SimpleGraph A).Adj := Classical.decRel _
  let S : Finset A := Finset.univ.erase u
  let H : SimpleGraph S := G.induce (S : Set A)
  have horder : Fintype.card S = n - 1 := by
    simpa only [S] using (card_univ_erase u).trans (congrArg (· - 1) hcard)
  have hdegree : G.degree u + Gᶜ.degree u = n - 1 := by
    have hcomp := G.degree_compl (v := u)
    rw [hcard] at hcomp
    omega
  have hmissingH : missingEdgeCount H ≤ (n - 1) - 4 + 0 := by
    rw [show missingEdgeCount H = missingEdgeCount G - Gᶜ.degree u by
      simpa only [S, H] using missingEdgeCount_induce_univ_erase G u]
    omega
  obtain ⟨w, hw, hunc, hhalf⟩ :=
    hstrong S horder 0 (by omega) H hmissingH
  let W : Finset A → ℝ := extendInducedWeight S w
  have hcardReal : (Nat.card G.edgeSet : ℝ) =
      (Nat.card H.edgeSet : ℝ) + (G.degree u : ℝ) := by
    exact_mod_cast card_edgeSet_induce_univ_erase_add_degree G u
  have hid : fractionalUncoveredWeight G W =
      fractionalUncoveredWeight H w + (G.degree u : ℝ) := by
    rw [fractionalUncoveredWeight_eq_card_sub_general,
      fractionalUncoveredWeight_eq_card_sub_general]
    dsimp only [W]
    rw [fractionalSize_extendInducedWeight, hcardReal]
    ring
  have hhalfW : IsHalfBounded G W := by
    intro t htG
    have htNC : G.IsNClique 3 t :=
      SimpleGraph.mem_cliqueFinset_iff.mp htG
    by_cases hsub : t ⊆ S
    · let q : Finset S := restrictToInduced S t hsub
      have hmap : q.map (inducedEmbedding S) = t := by
        simpa only [q, restrictToInduced, inducedEmbedding] using
          (Finset.subtype_map_of_mem hsub)
      have hqNC : H.IsNClique 3 q := by
        dsimp only [H]
        rw [SimpleGraph.isNClique_induce_iff]
        rw [← inducedEmbedding_eq_setEmbedding S]
        simpa only [hmap] using htNC
      dsimp only [W]
      rw [extendInducedWeight, dif_pos hsub]
      exact hhalf q (SimpleGraph.mem_cliqueFinset_iff.mpr hqNC)
    · dsimp only [W]
      rw [extendInducedWeight_eq_zero hsub]
      norm_num
  refine ⟨W, ?_, ?_, hhalfW⟩
  · dsimp only [W]
    exact hw.extendInduced
  · rw [hid]
    have hunc0 : fractionalUncoveredWeight H w ≤ 0 := by
      simpa using hunc
    have hdegreeBudgetReal : (G.degree u : ℝ) ≤ (a : ℝ) := by
      exact_mod_cast hdegreeBudget
    linarith

/-- The sole low-degree exception not covered by `d5_lowDegree_case`:
`degree u = 2` and `a = 1`.  All missing edges are then incident with `u`,
so its two neighbors are adjacent.  Their single edge is the one genuine
edge of the paper's formal length-two cycle; the other cycle edge accounts
for `α = 1`. -/
theorem d5_degree_two_budget_one_case {n : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n)
    (G : SimpleGraph A) (u : A) (hdegreeTwo : G.degree u = 2)
    (hstrong : AlmostCompleteStrongAt (n - 1))
    (hmissing : missingEdgeCount G ≤ n - 3) :
    HasStrongFractionalPacking G (1 : ℝ) := by
  classical
  let S : Finset A := Finset.univ.erase u
  let H : SimpleGraph S := G.induce (S : Set A)
  have hdegreeComp : Gᶜ.degree u = n - 3 := by
    have hcomp := G.degree_compl (v := u)
    rw [hcard, hdegreeTwo] at hcomp
    omega
  have hqM : Gᶜ.degree u ≤ missingEdgeCount G := by
    simpa only [missingEdgeCount] using
      (Gᶜ.degree_le_card_edgeFinset (v := u))
  have hmissingEq : missingEdgeCount G = n - 3 := by omega
  have hmissingH : missingEdgeCount H = 0 := by
    rw [show missingEdgeCount H = missingEdgeCount G - Gᶜ.degree u by
      simpa only [S, H] using missingEdgeCount_induce_univ_erase G u,
      hmissingEq, hdegreeComp]
    omega
  have hHtop : H = ⊤ := by
    have hcardSet : Hᶜ.edgeSet.ncard = 0 := by
      rw [← missingEdgeCount_eq_compl_edgeSet_ncard H]
      exact hmissingH
    have hempty : Hᶜ.edgeSet = ∅ :=
      (Set.ncard_eq_zero (Set.toFinite Hᶜ.edgeSet)).mp hcardSet
    have hbot : Hᶜ = ⊥ := SimpleGraph.edgeSet_eq_empty.mp hempty
    have := congrArg (fun K : SimpleGraph S ↦ Kᶜ) hbot
    simpa using this
  have hcardN : (G.neighborFinset u).card = 2 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hdegreeTwo]
  obtain ⟨x, y, hxy, hneighbors⟩ := Finset.card_eq_two.mp hcardN
  have hux : G.Adj u x := by
    have : x ∈ G.neighborFinset u := by simp [hneighbors]
    simpa only [SimpleGraph.mem_neighborFinset] using this
  have huy : G.Adj u y := by
    have : y ∈ G.neighborFinset u := by simp [hneighbors]
    simpa only [SimpleGraph.mem_neighborFinset] using this
  let xS : S := ⟨x, by simp [S, hux.ne.symm]⟩
  let yS : S := ⟨y, by simp [S, huy.ne.symm]⟩
  let e : Sym2 S := s(xS, yS)
  let P : Finset (Sym2 S) := {e}
  have hePH : e ∈ H.edgeSet := by
    change H.Adj xS yS
    rw [hHtop]
    simpa only [SimpleGraph.top_adj, ne_eq, xS, yS, Subtype.mk.injEq]
  have hPH : ∀ f ∈ P, f ∈ H.edgeSet := by
    intro f hf
    have hfe : f = e := by simpa only [P, Finset.mem_singleton] using hf
    subst f
    exact hePH
  have hcardP : P.card = G.degree u - 1 := by
    simp [P, hdegreeTwo]
  have hstar : ∀ f ∈ P, ∀ z : S, z ∈ f → G.Adj u z := by
    intro f hf z hz
    have hfe : f = e := by simpa only [P, Finset.mem_singleton] using hf
    subst f
    change z ∈ s(xS, yS) at hz
    simp only [Sym2.mem_iff] at hz
    rcases hz with hz | hz
    · simpa only [xS, Subtype.ext_iff] using hz ▸ hux
    · simpa only [yS, Subtype.ext_iff] using hz ▸ huy
  have hinc : ∀ p ∈ G.edgeFinset,
      (P.filter fun f ↦
        p ∈ (attachedEdgeTriangle (Finset.univ.erase u) u f).sym2).card ≤ 2 := by
    intro p hp
    calc
      (P.filter fun f ↦
          p ∈ (attachedEdgeTriangle (Finset.univ.erase u) u f).sym2).card ≤
          P.card := Finset.card_filter_le _ _
      _ = 1 := by simp [P]
      _ ≤ 2 := by omega
  have hlarge : n + 1 + 1 ≤ 3 * Gᶜ.degree u := by
    rw [hdegreeComp]
    omega
  simpa only [Nat.cast_one] using
    (d5_case_of_selectedEdges (n := n) (a := 1) (α := 1)
      hcard (by omega) (by omega) G u
      (by omega) (by omega) hstrong (by omega) hlarge P hPH
      hcardP hstar hinc)

/-- The complete low-degree branch of D5.  The general zero-extension argument
applies whenever `degree u ≤ a`.  The missing-edge inequality forces this
budget condition for `degree u ≤ 2`, except in the unique case
`degree u = 2, a = 1`, which is discharged by the one-edge augmented cycle
above. -/
theorem d5_case_of_degree_le_two {n a : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n) (ha : a ≤ 4)
    (G : SimpleGraph A) (u : A) (hdegreeSmall : G.degree u ≤ 2)
    (hstrong : AlmostCompleteStrongAt (n - 1))
    (hmissing : missingEdgeCount G ≤ n - 4 + a) :
    HasStrongFractionalPacking G (a : ℝ) := by
  have hqM : Gᶜ.degree u ≤ missingEdgeCount G := by
    simpa only [missingEdgeCount] using
      (Gᶜ.degree_le_card_edgeFinset (v := u))
  have hdegreeSum : G.degree u + Gᶜ.degree u = n - 1 := by
    have hcomp := G.degree_compl (v := u)
    rw [hcard] at hcomp
    omega
  by_cases hdegreeBudget : G.degree u ≤ a
  · exact d5_lowDegree_case hcard hn ha G u hdegreeSmall hdegreeBudget
      hstrong hmissing
  · have hdegreeTwo : G.degree u = 2 := by omega
    have haOne : a = 1 := by omega
    subst a
    simpa only [Nat.cast_one] using
      (d5_degree_two_budget_one_case hcard hn G u hdegreeTwo hstrong
        (by omega))

/-- The augmented-cycle data required by D5 when the deleted vertex has at
least three neighbors.  Corollary 2.5 is applied to the graph induced by the
neighborhood and the resulting cycle is embedded into `V(G) \ {u}`. -/
theorem exists_d5_augmentedCycle_of_degree_ge_three {n a : ℕ}
    (hcard : Fintype.card A = n) (G : SimpleGraph A) (u : A)
    (hdegree : 3 ≤ G.degree u)
    (hmissing : missingEdgeCount G ≤ n - 4 + a) :
    ∃ α : ℕ,
      ∃ C : Finset (Sym2 (↑((Finset.univ : Finset A).erase u))),
        α ≤ a ∧
        α ≤ G.degree u ∧
        C.card = G.degree u ∧
        (C.filter fun e ↦ e ∉ (G.induce
          (↑((Finset.univ : Finset A).erase u) : Set A)).edgeSet).card = α ∧
        (∀ e ∈ C,
          ∀ x : ↑((Finset.univ : Finset A).erase u), x ∈ e → G.Adj u x) ∧
        ∀ x : ↑((Finset.univ : Finset A).erase u),
          (C.filter fun e ↦ x ∈ e).card ≤ 2 := by
  classical
  let S : Finset A := Finset.univ.erase u
  let N : Finset A := G.neighborFinset u
  let H : SimpleGraph S := G.induce (S : Set A)
  let HN : SimpleGraph N := G.induce (N : Set A)
  have hNS : N ⊆ S := by
    intro x hx
    have hux : G.Adj u x := by
      simpa only [N, SimpleGraph.mem_neighborFinset] using hx
    simp [S, hux.ne.symm]
  have horderN : Fintype.card N = G.degree u := by
    simpa only [N, Fintype.card_coe] using
      (SimpleGraph.card_neighborFinset_eq_degree G u)
  have hdegreeN : 3 ≤ Fintype.card N := by omega
  have hdegreeLt : G.degree u < n := by
    have hlt := G.degree_lt_card_verts u
    simpa only [hcard] using hlt
  have hdegreeSum : G.degree u + Gᶜ.degree u = n - 1 := by
    have hcomp := G.degree_compl (v := u)
    rw [hcard] at hcomp
    omega
  have hmissingHN : missingEdgeCount HN ≤ Fintype.card N - 3 + a := by
    calc
      missingEdgeCount HN ≤ missingEdgeCount H := by
        simpa only [HN, H] using
          missingEdgeCount_induce_finset_mono G hNS
      _ = missingEdgeCount G - Gᶜ.degree u := by
        simpa only [H, S] using missingEdgeCount_induce_univ_erase G u
      _ ≤ Fintype.card N - 3 + a := by omega
  obtain ⟨CN, hcardCN, habsentCN, hincCN⟩ :=
    exists_approximateHamiltonianCycle_edges HN a hdegreeN hmissingHN
  let ι : N ↪ S :=
    ⟨fun x ↦ ⟨x, hNS x.property⟩,
      fun x y h ↦ Subtype.ext
        (show (x : A) = (y : A) from
          congrArg (fun z : S ↦ (z : A)) h)⟩
  let C : Finset (Sym2 S) := CN.map ι.sym2Map
  let α : ℕ := (CN.filter fun e ↦ e ∉ HN.edgeSet).card
  have hedge (p : Sym2 N) :
      ι.sym2Map p ∈ H.edgeSet ↔ p ∈ HN.edgeSet := by
    induction p using Sym2.inductionOn with
    | _ x y => rfl
  have habsent :
      (C.filter fun e ↦ e ∉ H.edgeSet).card = α := by
    dsimp only [C, α]
    rw [Finset.filter_map, Finset.card_map]
    congr 1
    apply Finset.filter_congr
    intro p hp
    exact not_congr (hedge p)
  have hstar : ∀ e ∈ C, ∀ x : S, x ∈ e → G.Adj u x := by
    intro e he x hx
    rw [show C = CN.map ι.sym2Map by rfl, Finset.mem_map] at he
    obtain ⟨p, hp, rfl⟩ := he
    change x ∈ Sym2.map ι p at hx
    rw [Sym2.mem_map] at hx
    obtain ⟨y, hy, hiy⟩ := hx
    have huy : G.Adj u (y : A) := by
      simpa only [N, SimpleGraph.mem_neighborFinset] using y.property
    have hval : (y : A) = (x : A) :=
      congrArg (fun z : S ↦ (z : A)) hiy
    exact hval ▸ huy
  have hinc : ∀ x : S, (C.filter fun e ↦ x ∈ e).card ≤ 2 := by
    intro x
    by_cases hux : G.Adj u x
    · let y : N := ⟨x, by
          simpa only [N, SimpleGraph.mem_neighborFinset] using hux⟩
      have hiy : ι y = x := by
        apply Subtype.ext
        rfl
      calc
        (C.filter fun e ↦ x ∈ e).card =
            (C.filter fun e ↦ ι y ∈ e).card := by rw [hiy]
        _ = (CN.filter fun e ↦ y ∈ e).card := by
          exact filter_map_sym2_incidence_card ι CN y
        _ = 2 := hincCN y
        _ ≤ 2 := le_rfl
    · have hempty : (C.filter fun e ↦ x ∈ e) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro e he
        exact fun hxe ↦ hux (hstar e he x hxe)
      rw [hempty]
      simp
  refine ⟨α, C, ?_, ?_, ?_, ?_, hstar, hinc⟩
  · exact habsentCN
  · calc
      α ≤ CN.card := Finset.card_filter_le _ _
      _ = Fintype.card N := hcardCN
      _ = G.degree u := horderN
  · calc
      C.card = CN.card := Finset.card_map _
      _ = Fintype.card N := hcardCN
      _ = G.degree u := horderN
  · change (C.filter fun e ↦ e ∉ H.edgeSet).card = α
    exact habsent

/-- If every vertex is incident with at most two selected edges, then every
ambient edge occurs in at most two of the triangles obtained by adjoining
`u` to those edges.  Internal edges occur in at most one such triangle;
star edges inherit the stated vertex-incidence bound. -/
theorem attachedEdgeTriangle_incidence_le_two
    (G : SimpleGraph A) (u : A)
    (P : Finset (Sym2 (↑((Finset.univ : Finset A).erase u))))
    (hPH : ∀ e ∈ P, e ∈ (G.induce
      (↑((Finset.univ : Finset A).erase u) : Set A)).edgeSet)
    (hvertex : ∀ x : ↑((Finset.univ : Finset A).erase u),
      (P.filter fun e ↦ x ∈ e).card ≤ 2) :
    ∀ p ∈ G.edgeFinset,
      (P.filter fun e ↦
        p ∈ (attachedEdgeTriangle (Finset.univ.erase u) u e).sym2).card ≤ 2 := by
  classical
  let S : Finset A := Finset.univ.erase u
  let H : SimpleGraph S := G.induce (S : Set A)
  have hu : u ∉ S := by simp [S]
  intro p hp
  induction p using Sym2.inductionOn with
  | _ x y =>
      have hxy : G.Adj x y := by
        simpa only [SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet] using hp
      by_cases hx : x ∈ S
      · by_cases hy : y ∈ S
        · let xS : S := ⟨x, hx⟩
          let yS : S := ⟨y, hy⟩
          let q : Sym2 S := s(xS, yS)
          have hqSet : q ∈ H.edgeSet := by
            change G.Adj x y
            exact hxy
          have hqND : ¬q.IsDiag := by
            exact H.not_isDiag_of_mem_edgeFinset
              (SimpleGraph.mem_edgeFinset.mpr hqSet)
          have hsub :
              (P.filter fun e ↦
                s(x, y) ∈ (attachedEdgeTriangle S u e).sym2) ⊆ {q} := by
            intro e he
            have heP := (Finset.mem_filter.mp he).1
            have heND : ¬e.IsDiag :=
              (G.induce
                (↑((Finset.univ : Finset A).erase u) : Set A)).not_isDiag_of_mem_edgeSet
                  (hPH e heP)
            rw [Finset.mem_singleton]
            have heMem := (Finset.mem_filter.mp he).2
            change (inducedEmbedding S).sym2Map q ∈
              (attachedEdgeTriangle S u e).sym2 at heMem
            exact ((inducedEdge_mem_attachedEdgeTriangle_sym2_iff
              hu hqND heND).mp heMem).symm
          calc
            (P.filter fun e ↦ s(x, y) ∈
                (attachedEdgeTriangle (Finset.univ.erase u) u e).sym2).card ≤
                ({q} : Finset (Sym2 S)).card := by
              simpa only [S] using Finset.card_le_card hsub
            _ = 1 := Finset.card_singleton q
            _ ≤ 2 := by omega
        · have hyu : y = u := by simpa [S] using hy
          subst y
          let xS : S := ⟨x, hx⟩
          have hsub :
              (P.filter fun e ↦
                s(x, u) ∈ (attachedEdgeTriangle S u e).sym2) ⊆
                P.filter fun e ↦ xS ∈ e := by
            intro e he
            have heP := (Finset.mem_filter.mp he).1
            apply Finset.mem_filter.mpr
            refine ⟨heP, ?_⟩
            apply (starEdge_mem_attachedEdgeTriangle_sym2_iff
              hu xS e).mp
            rw [show s(u, (xS : A)) = s(x, u) from
              Sym2.sound (Sym2.Rel.swap u x)]
            exact (Finset.mem_filter.mp he).2
          calc
            (P.filter fun e ↦ s(x, u) ∈
                (attachedEdgeTriangle (Finset.univ.erase u) u e).sym2).card ≤
                (P.filter fun e ↦ xS ∈ e).card := by
              simpa only [S] using Finset.card_le_card hsub
            _ ≤ 2 := hvertex xS
      · have hxu : x = u := by simpa [S] using hx
        subst x
        have hy : y ∈ S := by simp [S, hxy.ne.symm]
        let yS : S := ⟨y, hy⟩
        have hsub :
            (P.filter fun e ↦
              s(u, y) ∈ (attachedEdgeTriangle S u e).sym2) ⊆
              P.filter fun e ↦ yS ∈ e := by
          intro e he
          have heP := (Finset.mem_filter.mp he).1
          apply Finset.mem_filter.mpr
          refine ⟨heP, ?_⟩
          exact (starEdge_mem_attachedEdgeTriangle_sym2_iff
            hu yS e).mp (Finset.mem_filter.mp he).2
        calc
          (P.filter fun e ↦ s(u, y) ∈
              (attachedEdgeTriangle (Finset.univ.erase u) u e).sym2).card ≤
              (P.filter fun e ↦ yS ∈ e).card := by
            simpa only [S] using Finset.card_le_card hsub
          _ ≤ 2 := hvertex yS

/-- Complete high-degree D5 branch.  The sparse-complement Hamilton theorem
constructs the augmented cycle; filtering out its absent edges and applying
the preceding incidence lemma supplies exactly the hypotheses of the D5
weighted-reduction assembly. -/
theorem d5_case_of_degree_ge_three {n a : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n) (ha : a ≤ 4)
    (G : SimpleGraph A) (u : A) (hdegree : 3 ≤ G.degree u)
    (hstrong : AlmostCompleteStrongAt (n - 1))
    (hmissing : missingEdgeCount G ≤ n - 4 + a)
    (hlarge : n + a + 1 ≤ 3 * Gᶜ.degree u) :
    HasStrongFractionalPacking G (a : ℝ) := by
  classical
  obtain ⟨α, C, hαa, hαd, hcardC, habsent, hstarC, hvertexC⟩ :=
    exists_d5_augmentedCycle_of_degree_ge_three hcard G u hdegree hmissing
  have hvertexP : ∀ x : ↑((Finset.univ : Finset A).erase u),
      ((presentCycleEdges (G.induce
        (↑((Finset.univ : Finset A).erase u) : Set A)) C).filter
          fun e ↦ x ∈ e).card ≤ 2 := by
    intro x
    calc
      ((presentCycleEdges (G.induce
          (↑((Finset.univ : Finset A).erase u) : Set A)) C).filter
          fun e ↦ x ∈ e).card ≤
          (C.filter fun e ↦ x ∈ e).card := by
        apply Finset.card_le_card
        intro e he
        exact Finset.mem_filter.mpr
          ⟨presentCycleEdges_subset _ C (Finset.mem_filter.mp he).1,
            (Finset.mem_filter.mp he).2⟩
      _ ≤ 2 := hvertexC x
  have hinc : ∀ p ∈ G.edgeFinset,
      ((presentCycleEdges (G.induce
        (↑((Finset.univ : Finset A).erase u) : Set A)) C).filter fun e ↦
        p ∈ (attachedEdgeTriangle (Finset.univ.erase u) u e).sym2).card ≤ 2 := by
    exact attachedEdgeTriangle_incidence_le_two G u
      (presentCycleEdges (G.induce
        (↑((Finset.univ : Finset A).erase u) : Set A)) C)
      (presentCycleEdges_mem_edgeSet _ C) hvertexP
  have hlargeα : n + α + 1 ≤ 3 * Gᶜ.degree u := by omega
  apply d5_case_of_augmentedCycle hcard (by omega) ha G u hαa hαd
    hstrong hmissing hlargeα C hcardC habsent
  · intro e he x hx
    exact hstarC e (presentCycleEdges_subset _ C he) x hx
  · exact hinc

/-- All degree subcases of D5, with the paper's defining complement-degree
inequality as the sole case hypothesis. -/
theorem d5_case {n a : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n) (ha : a ≤ 4)
    (G : SimpleGraph A) (u : A)
    (hstrong : AlmostCompleteStrongAt (n - 1))
    (hmissing : missingEdgeCount G ≤ n - 4 + a)
    (hlarge : n + a + 1 ≤ 3 * Gᶜ.degree u) :
    HasStrongFractionalPacking G (a : ℝ) := by
  by_cases hdegree : G.degree u ≤ 2
  · exact d5_case_of_degree_le_two hcard hn ha G u hdegree hstrong hmissing
  · exact d5_case_of_degree_ge_three hcard hn ha G u (by omega)
      hstrong hmissing hlarge

end

end Erdos76
