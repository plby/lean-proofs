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
import ErdosProblems.Erdos76.CertificateBridge
import ErdosProblems.Erdos76.CertificateExhaustion
import ErdosProblems.Erdos76.Certificates.ExactN7
import ErdosProblems.Erdos76.Certificates.ExactN8
import ErdosProblems.Erdos76.Certificates.ExactN9
import ErdosProblems.Erdos76.Certificates.ExactN10
import ErdosProblems.Erdos76.Certificates.ExhaustionN7
import ErdosProblems.Erdos76.Certificates.ExhaustionN8
import ErdosProblems.Erdos76.Certificates.ExhaustionN9
import ErdosProblems.Erdos76.Certificates.ExhaustionN10
import ErdosProblems.Erdos76.FractionalTransport

/-!
# From finite exhaustion certificates to almost-complete graph bases

An exhaustion certificate classifies the *missing-edge graph*.  The packing
certificates are attached to the complements of its final representatives.
This module joins those two independently checked facts, and transports the
resulting exact or strong fractional packing across the certified vertex
permutation.

The generic statements only mention semantic graph predicates and Boolean
checks on canonical bit graphs.  In particular, no `DecidableRel` instance
occurs in their public types.
-/

open Finset
open scoped BigOperators

namespace Erdos76
namespace CertificateExhaustion

open CertificateChecker
open CertificateChecker.PackingCert

noncomputable section

/-! ## Isomorphism transport -/

/-- Isomorphisms commute with taking graph complements.  This is deliberately
named outside `SimpleGraph.Iso`, whose abbreviation to `RelIso` otherwise
causes dot notation to select relation complementation. -/
noncomputable def complIso {n : ℕ}
    {G H : SimpleGraph (Fin n)} (f : G ≃g H) : Gᶜ ≃g Hᶜ where
  __ := f.toEquiv
  map_rel_iff' := by
    intro x y
    simp [SimpleGraph.compl_adj, f.map_rel_iff]

/-- Relabel an exact fractional decomposition by a vertex equivalence. -/
theorem IsFractionalDecomposition.relabelEquiv {n : ℕ}
    {G : SimpleGraph (Fin n)} {w : Finset (Fin n) → ℝ}
    (hw : IsFractionalDecomposition G w) (e : Equiv.Perm (Fin n)) :
    IsFractionalDecomposition (G.map e.toEmbedding) (relabelWeight e w) := by
  classical
  let : DecidableRel G.Adj := Classical.decRel _
  let : DecidableRel (G.map e.toEmbedding).Adj := Classical.decRel _
  refine ⟨hw.isPacking.relabel e, ?_⟩
  intro p hp
  have hp' := SimpleGraph.mem_edgeFinset.mp hp
  rw [SimpleGraph.edgeSet_map e.toEmbedding G] at hp'
  obtain ⟨q, hq, rfl⟩ := hp'
  rw [fractionalEdgeLoad_relabel]
  exact hw.edgeLoad_eq_one (SimpleGraph.mem_edgeFinset.mpr hq)

/-- The half-bound condition is invariant under vertex relabelling. -/
theorem IsHalfBounded.relabelEquiv {n : ℕ}
    {G : SimpleGraph (Fin n)} {w : Finset (Fin n) → ℝ}
    (hw : IsHalfBounded G w) (e : Equiv.Perm (Fin n)) :
    IsHalfBounded (G.map e.toEmbedding) (relabelWeight e w) := by
  classical
  let : DecidableRel G.Adj := Classical.decRel _
  let : DecidableRel (G.map e.toEmbedding).Adj := Classical.decRel _
  intro t ht
  have ht' := SimpleGraph.mem_cliqueFinset_iff.mp ht
  obtain ⟨s, hs, rfl⟩ :=
    (SimpleGraph.isNClique_map_iff (G := G) (f := e.toEmbedding) (by omega)).mp ht'
  simpa using hw s (SimpleGraph.mem_cliqueFinset_iff.mpr hs)

/-- Rewrite uncovered weight as the number of edges minus total edge load. -/
lemma fractionalUncoveredWeight_eq_card_sub {n : ℕ}
    (G : SimpleGraph (Fin n)) (w : Finset (Fin n) → ℝ) :
    fractionalUncoveredWeight G w =
      (Nat.card G.edgeSet : ℝ) - 3 * fractionalSize G w := by
  classical
  let : DecidableRel G.Adj := Classical.decRel _
  rw [fractionalUncoveredWeight, Finset.sum_sub_distrib,
    sum_fractionalEdgeLoad_eq_three_mul_fractionalSize]
  simp only [Finset.sum_const, nsmul_one]
  congr
  rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]

/-- Uncovered weight is invariant under vertex relabelling. -/
theorem fractionalUncoveredWeight_relabelEquiv {n : ℕ}
    (G : SimpleGraph (Fin n)) (e : Equiv.Perm (Fin n))
    (w : Finset (Fin n) → ℝ) :
    fractionalUncoveredWeight (G.map e.toEmbedding) (relabelWeight e w) =
      fractionalUncoveredWeight G w := by
  classical
  let : DecidableRel G.Adj := Classical.decRel _
  let : DecidableRel (G.map e.toEmbedding).Adj := Classical.decRel _
  have hcard : Nat.card (G.map e.toEmbedding).edgeSet = Nat.card G.edgeSet :=
    (Nat.card_congr (SimpleGraph.Iso.map e G).mapEdgeSet).symm
  rw [fractionalUncoveredWeight_eq_card_sub,
    fractionalUncoveredWeight_eq_card_sub, fractionalSize_relabel, hcard]

/-- Pull an exact decomposition backwards across a graph isomorphism. -/
theorem IsFractionalDecomposition.transportIso {n : ℕ}
    {G H : SimpleGraph (Fin n)} {w : Finset (Fin n) → ℝ}
    (hw : IsFractionalDecomposition H w) (f : G ≃g H) :
    ∃ u : Finset (Fin n) → ℝ, IsFractionalDecomposition G u := by
  let e : Equiv.Perm (Fin n) := f.symm.toEquiv
  have hmap : H.map e.toEmbedding = G := by
    rw [← SimpleGraph.comap_symm H e]
    ext x y
    simp only [SimpleGraph.comap_adj]
    change H.Adj (f x) (f y) ↔ G.Adj x y
    exact f.map_rel_iff
  refine ⟨relabelWeight e w, ?_⟩
  simpa only [hmap] using IsFractionalDecomposition.relabelEquiv hw e

/-- Pull a strong fractional packing backwards across a graph isomorphism. -/
theorem HasStrongFractionalPacking.transportIso {n : ℕ}
    {G H : SimpleGraph (Fin n)} {a : ℝ}
    (hw : HasStrongFractionalPacking H a) (f : G ≃g H) :
    HasStrongFractionalPacking G a := by
  obtain ⟨w, hpacking, huncovered, hhalf⟩ := hw
  let e : Equiv.Perm (Fin n) := f.symm.toEquiv
  let u : Finset (Fin n) → ℝ := relabelWeight e w
  have hmap : H.map e.toEmbedding = G := by
    rw [← SimpleGraph.comap_symm H e]
    ext x y
    simp only [SimpleGraph.comap_adj]
    change H.Adj (f x) (f y) ↔ G.Adj x y
    exact f.map_rel_iff
  refine ⟨u, ?_, ?_, ?_⟩
  · simpa only [u, hmap] using hpacking.relabel e
  · calc
      fractionalUncoveredWeight G u = fractionalUncoveredWeight H w := by
        rw [← hmap]
        simpa only [u] using fractionalUncoveredWeight_relabelEquiv H e w
      _ ≤ a := huncovered
  · simpa only [u, hmap] using IsHalfBounded.relabelEquiv hhalf e

/-! ## Generic joins between exhaustions and packing certificates -/

/-- Executable bitwise condition saying that `dense` encodes the complement
of `missing`.  The diagonal is irrelevant because `graphOfBits` is loopless. -/
def ComplementMasks {n : ℕ} (dense missing : BitVec (edgeCount n)) : Prop :=
  ∀ i j : Fin n, i ≠ j →
    (dense.getLsbD (edgeIndex i.1 j.1) = true ↔
      ¬ missing.getLsbD (edgeIndex i.1 j.1) = true)

instance {n : ℕ} (dense missing : BitVec (edgeCount n)) :
    Decidable (ComplementMasks dense missing) := by
  unfold ComplementMasks
  infer_instance

lemma ComplementMasks.graphOfBits_eq_compl {n : ℕ}
    {dense missing : BitVec (edgeCount n)}
    (h : ComplementMasks dense missing) :
    graphOfBits dense = (graphOfBits missing)ᶜ := by
  ext i j
  by_cases hij : i = j
  · simp [hij]
  · simpa [hij, SimpleGraph.compl_adj] using h i j hij

/-- The dense graph mask in every entry is the complement of some final
missing-edge representative.  Extra entries are harmless. -/
def MasksCover {n : ℕ} (reps : Array (BitVec (edgeCount n)))
    (entries : List (BitVec (edgeCount n) × PackingCert n)) : Prop :=
  ∀ k : Fin reps.size, ∃ entry ∈ entries,
    ComplementMasks entry.1 reps[k]

instance {n : ℕ} (reps : Array (BitVec (edgeCount n)))
    (entries : List (BitVec (edgeCount n) × PackingCert n)) :
    Decidable (MasksCover reps entries) := by
  unfold MasksCover
  infer_instance

/-- Semantic exact-decomposition join. -/
theorem checkExactEntries_sound {n : ℕ} [NeZero n]
    {d : ExhaustionData n}
    {entries : List (BitVec (edgeCount n) × PackingCert n)}
    (hd : d.check = true)
    (hcover : MasksCover (d.level d.steps.size) entries)
    (hchecks : entries.all
      (fun entry ↦ entry.2.checkExact (graphOfBits entry.1)) = true)
    (G : SimpleGraph (Fin n))
    (hcard : Gᶜ.edgeSet.ncard = d.steps.size) :
    ∃ w : Finset (Fin n) → ℝ, IsFractionalDecomposition G w := by
  have hall : ∀ entry ∈ entries,
      entry.2.checkExact (graphOfBits entry.1) = true := by
    simpa only [List.all_eq_true] using hchecks
  have hfinal : ∀ k : Fin (d.level d.steps.size).size,
      ∃ w : Finset (Fin n) → ℝ,
        IsFractionalDecomposition ((graphOfBits (d.level d.steps.size)[k])ᶜ) w := by
    intro k
    obtain ⟨entry, hmem, hmasks⟩ := hcover k
    have hgraph := hmasks.graphOfBits_eq_compl
    have hw := checkExact_sound_isFractionalDecomposition entry.2 (hall entry hmem)
    exact ⟨entry.2.weight, by simpa only [hgraph] using hw⟩
  have hmissing := d.check_transport_atTarget hd
    (fun H ↦ ∃ w : Finset (Fin n) → ℝ, IsFractionalDecomposition Hᶜ w)
    hfinal (by
      intro A B ⟨f⟩ hB
      obtain ⟨w, hw⟩ := hB
      exact IsFractionalDecomposition.transportIso hw (complIso f))
    Gᶜ hcard
  simpa using hmissing

/-- Semantic strong-packing join. -/
theorem checkStrongEntries_sound {n : ℕ} [NeZero n]
    {d : ExhaustionData n} {a : ℕ}
    {entries : List (BitVec (edgeCount n) × PackingCert n)}
    (hd : d.check = true)
    (hcover : MasksCover (d.level d.steps.size) entries)
    (hchecks : entries.all
      (fun entry ↦ entry.2.checkStrong (graphOfBits entry.1) a) = true)
    (G : SimpleGraph (Fin n))
    (hcard : Gᶜ.edgeSet.ncard = d.steps.size) :
    HasStrongFractionalPacking G (a : ℝ) := by
  have hall : ∀ entry ∈ entries,
      entry.2.checkStrong (graphOfBits entry.1) a = true := by
    simpa only [List.all_eq_true] using hchecks
  have hfinal : ∀ k : Fin (d.level d.steps.size).size,
      HasStrongFractionalPacking
        ((graphOfBits (d.level d.steps.size)[k])ᶜ) (a : ℝ) := by
    intro k
    obtain ⟨entry, hmem, hmasks⟩ := hcover k
    have hgraph := hmasks.graphOfBits_eq_compl
    have hw := checkStrong_sound_hasStrongFractionalPacking a entry.2 (hall entry hmem)
    simpa only [hgraph] using hw
  have hmissing := d.check_transport_atTarget hd
    (fun H ↦ HasStrongFractionalPacking Hᶜ (a : ℝ)) hfinal (by
      intro A B ⟨f⟩ hB
      exact HasStrongFractionalPacking.transportIso hB (complIso f))
    Gᶜ hcard
  simpa using hmissing

/-! ## Exact bases at orders seven through ten -/

private lemma compl_edgeSet_ncard_eq_missingEdgeCount {n : ℕ}
    (G : SimpleGraph (Fin n)) :
    Gᶜ.edgeSet.ncard = missingEdgeCount G := by
  classical
  exact Set.ncard_eq_toFinset_card' Gᶜ.edgeSet

namespace Certificates.ExactExhaustionN7

open CertificateChecker.Certificates
open CertificateExhaustion.Certificates

/-- The five exact certificates align with the complements of the five final
three-missing-edge representatives. -/
theorem masksCover : MasksCover
    (ExhaustionN7.data.level ExhaustionN7.data.steps.size) ExactN7.entries := by
  decide

/-- Unconditional `n = 7`, three-missing-edge clause of the exact base family
in `AlmostCompleteCertificateBases`. -/
theorem exactBase (G : SimpleGraph (Fin 7))
    (hmissing : missingEdgeCount G = 3) :
    ∃ w : Finset (Fin 7) → ℝ, IsFractionalDecomposition G w := by
  classical
  have hncard : Gᶜ.edgeSet.ncard = ExhaustionN7.data.steps.size := by
    calc
      Gᶜ.edgeSet.ncard = missingEdgeCount G :=
        compl_edgeSet_ncard_eq_missingEdgeCount G
      _ = 3 := hmissing
      _ = ExhaustionN7.data.steps.size := by rfl
  exact checkExactEntries_sound ExhaustionN7.checks masksCover ExactN7.checks G hncard

end Certificates.ExactExhaustionN7

namespace Certificates.ExactExhaustionN8

open CertificateChecker.Certificates
open CertificateExhaustion.Certificates

/-- The exact certificates cover the complements of all four-missing-edge
representatives on eight vertices. -/
theorem masksCover : MasksCover
    (ExhaustionN8.data.level ExhaustionN8.data.steps.size) ExactN8.entries := by
  decide

/-- Unconditional `n = 8`, four-missing-edge exact base. -/
theorem exactBase (G : SimpleGraph (Fin 8))
    (hmissing : missingEdgeCount G = 4) :
    ∃ w : Finset (Fin 8) → ℝ, IsFractionalDecomposition G w := by
  classical
  have hncard : Gᶜ.edgeSet.ncard = ExhaustionN8.data.steps.size := by
    calc
      Gᶜ.edgeSet.ncard = missingEdgeCount G :=
        compl_edgeSet_ncard_eq_missingEdgeCount G
      _ = 4 := hmissing
      _ = ExhaustionN8.data.steps.size := by rfl
  exact checkExactEntries_sound ExhaustionN8.checks masksCover ExactN8.checks G hncard

end Certificates.ExactExhaustionN8

namespace Certificates.ExactExhaustionN9

open CertificateChecker.Certificates
open CertificateExhaustion.Certificates

/-- The exact certificates cover the complements of all five-missing-edge
representatives on nine vertices. -/
theorem masksCover : MasksCover
    (ExhaustionN9.data.level ExhaustionN9.data.steps.size) ExactN9.entries := by
  decide

/-- Unconditional `n = 9`, five-missing-edge exact base. -/
theorem exactBase (G : SimpleGraph (Fin 9))
    (hmissing : missingEdgeCount G = 5) :
    ∃ w : Finset (Fin 9) → ℝ, IsFractionalDecomposition G w := by
  classical
  have hncard : Gᶜ.edgeSet.ncard = ExhaustionN9.data.steps.size := by
    calc
      Gᶜ.edgeSet.ncard = missingEdgeCount G :=
        compl_edgeSet_ncard_eq_missingEdgeCount G
      _ = 5 := hmissing
      _ = ExhaustionN9.data.steps.size := by rfl
  exact checkExactEntries_sound ExhaustionN9.checks masksCover ExactN9.checks G hncard

end Certificates.ExactExhaustionN9

namespace Certificates.ExactExhaustionN10

open CertificateChecker.Certificates
open CertificateExhaustion.Certificates

/-- The exact certificates cover the complements of all six-missing-edge
representatives on ten vertices. -/
theorem masksCover : MasksCover
    (ExhaustionN10.data.level ExhaustionN10.data.steps.size) ExactN10.entries := by
  decide

/-- Unconditional `n = 10`, six-missing-edge exact base. -/
theorem exactBase (G : SimpleGraph (Fin 10))
    (hmissing : missingEdgeCount G = 6) :
    ∃ w : Finset (Fin 10) → ℝ, IsFractionalDecomposition G w := by
  classical
  have hncard : Gᶜ.edgeSet.ncard = ExhaustionN10.data.steps.size := by
    calc
      Gᶜ.edgeSet.ncard = missingEdgeCount G :=
        compl_edgeSet_ncard_eq_missingEdgeCount G
      _ = 6 := hmissing
      _ = ExhaustionN10.data.steps.size := by rfl
  exact checkExactEntries_sound ExhaustionN10.checks masksCover ExactN10.checks G hncard

end Certificates.ExactExhaustionN10

/-- The exact half of `AlmostCompleteCertificateBases`, discharged entirely
by the four checked finite exhaustion-and-packing certificate families. -/
theorem exactCertificateBases :
    ∀ n : ℕ, 7 ≤ n → n ≤ 10 →
      ∀ G : SimpleGraph (Fin n), missingEdgeCount G = n - 4 →
        ∃ w : Finset (Fin n) → ℝ, IsFractionalDecomposition G w := by
  intro n hnlo hnhi
  interval_cases n <;> intro G hmissing
  · exact Certificates.ExactExhaustionN7.exactBase G (by omega)
  · exact Certificates.ExactExhaustionN8.exactBase G (by omega)
  · exact Certificates.ExactExhaustionN9.exactBase G (by omega)
  · exact Certificates.ExactExhaustionN10.exactBase G (by omega)

end

end CertificateExhaustion
end Erdos76
