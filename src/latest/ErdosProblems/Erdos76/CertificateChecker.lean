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
import ErdosProblems.Erdos76.Fractional
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.BitVec

/-!
# Verified finite certificates for Erdős Problem 76

This module contains the small reusable checker core.  It intentionally does
not contain any of the large computer-search certificates.

A graph on `Fin n` is represented by one bit for every unordered vertex pair.
A fractional packing certificate stores a common natural-number denominator
and a sparse list of triangle numerators.  Repeated triangle entries are
allowed: their numerators are added.  The executable checker verifies only
finite, decidable conditions.  Its soundness theorem turns an accepted
certificate into the real-valued `IsFractionalPacking` used by the main proof.
-/

open Finset
open scoped BigOperators

namespace Erdos76
namespace CertificateChecker

/-! ## Bit-encoded graphs -/

/-- Number of unordered pairs of distinct elements of `Fin n`. -/
def edgeCount (n : ℕ) : ℕ := n * (n - 1) / 2

/-- Index of an unordered pair.  For `i < j`, this is
`j * (j - 1) / 2 + i`. -/
def edgeIndex (i j : ℕ) : ℕ :=
  max i j * (max i j - 1) / 2 + min i j

lemma edgeIndex_comm (i j : ℕ) : edgeIndex i j = edgeIndex j i := by
  simp [edgeIndex, max_comm, min_comm]

/-- Decode an edge bit-vector as a simple graph. -/
def graphOfBits {n : ℕ} (bits : BitVec (edgeCount n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j ↦ bits.getLsbD (edgeIndex i.1 j.1) = true

instance {n : ℕ} (bits : BitVec (edgeCount n)) :
    DecidableRel (graphOfBits bits).Adj := by
  dsimp only [graphOfBits]
  infer_instance

@[simp] lemma graphOfBits_adj {n : ℕ} (bits : BitVec (edgeCount n)) (i j : Fin n) :
    (graphOfBits bits).Adj i j ↔
      i ≠ j ∧ bits.getLsbD (edgeIndex i.1 j.1) = true := by
  simp only [graphOfBits, SimpleGraph.fromRel_adj]
  rw [edgeIndex_comm j.1 i.1]
  simp

/-! ## Sparse common-denominator packing certificates -/

/-- One sparse triangle numerator. -/
structure PackingTerm (n : ℕ) where
  i : Fin n
  j : Fin n
  k : Fin n
  numerator : ℕ
  deriving DecidableEq

namespace PackingTerm

/-- The unordered vertex set represented by a packing term. -/
def triangle {n : ℕ} (q : PackingTerm n) : Finset (Fin n) :=
  {q.i, q.j, q.k}

end PackingTerm

/-- A sparse rational packing with one positive common denominator. -/
structure PackingCert (n : ℕ) where
  denominator : ℕ
  terms : List (PackingTerm n)
  deriving DecidableEq

namespace PackingCert

variable {n : ℕ}

/-- The numerator assigned to a vertex set.  Repeated entries are added. -/
def triangleNumerator (c : PackingCert n) (t : Finset (Fin n)) : ℕ :=
  (c.terms.map fun q ↦ if q.triangle = t then q.numerator else 0).sum

/-- Total numerator of all sparse entries. -/
def totalNumerator (c : PackingCert n) : ℕ :=
  (c.terms.map PackingTerm.numerator).sum

/-- Numerator placed on one edge by the sparse entries containing it. -/
def edgeNumerator (c : PackingCert n) (e : Sym2 (Fin n)) : ℕ :=
  (c.terms.map fun q ↦ if e ∈ q.triangle.sym2 then q.numerator else 0).sum

/-- The real-valued weight decoded from a common-denominator certificate. -/
noncomputable def weight (c : PackingCert n) (t : Finset (Fin n)) : ℝ :=
  (c.triangleNumerator t : ℝ) / c.denominator

/-- Proposition checked by `check`.  It contains only bounded finite
quantifiers and natural-number inequalities. -/
def Valid (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : PackingCert n) : Prop :=
  0 < c.denominator ∧
    (∀ q ∈ c.terms, G.IsNClique 3 q.triangle) ∧
      ∀ i ∈ List.finRange n, ∀ j ∈ List.finRange n,
        G.Adj i j → c.edgeNumerator s(i, j) ≤ c.denominator

/-- Executable Boolean verifier for a common-denominator fractional packing. -/
def check (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : PackingCert n) : Bool :=
  decide (0 < c.denominator) &&
    c.terms.all (fun q ↦ decide (G.IsNClique 3 q.triangle)) &&
      (List.finRange n).all fun i ↦
        (List.finRange n).all fun j ↦
          decide (G.Adj i j → c.edgeNumerator s(i, j) ≤ c.denominator)

@[simp] theorem check_eq_true_iff (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : PackingCert n) : c.check G = true ↔ c.Valid G := by
  simp [check, Valid, List.all_eq_true, and_assoc, imp_iff_not_or]

/-! ## Strengthened finite predicates -/

/-- A packing certificate which covers every present edge exactly once. -/
def ExactValid (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : PackingCert n) : Prop :=
  0 < c.denominator ∧
    (∀ q ∈ c.terms, G.IsNClique 3 q.triangle) ∧
      ∀ i ∈ List.finRange n, ∀ j ∈ List.finRange n,
        G.Adj i j → c.edgeNumerator s(i, j) = c.denominator

/-- Executable exact-decomposition verifier. -/
def checkExact (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : PackingCert n) : Bool :=
  decide (0 < c.denominator) &&
    c.terms.all (fun q ↦ decide (G.IsNClique 3 q.triangle)) &&
      (List.finRange n).all fun i ↦
        (List.finRange n).all fun j ↦
          decide (G.Adj i j → c.edgeNumerator s(i, j) = c.denominator)

@[simp] theorem checkExact_eq_true_iff
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (c : PackingCert n) :
    c.checkExact G = true ↔ c.ExactValid G := by
  simp [checkExact, ExactValid, List.all_eq_true, and_assoc, imp_iff_not_or]

/-- The all-natural-number statement checked for a strong base certificate.

The triangle keys must be distinct because the sparse representation otherwise
adds repeated entries.  This makes the per-term half bound a genuine bound on
the decoded triangle weight. -/
def StrongValid (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : ℕ) (c : PackingCert n) : Prop :=
  c.Valid G ∧
    (c.terms.map PackingTerm.triangle).Nodup ∧
      (∀ q ∈ c.terms, 2 * q.numerator ≤ c.denominator) ∧
        c.denominator * (G.edgeFinset.card - a) ≤ 3 * c.totalNumerator

/-- Executable strong-base verifier.  All arithmetic is in `Nat`; no rational
normalization or graph canonicalization is performed by the checker. -/
def checkStrong (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : ℕ) (c : PackingCert n) : Bool :=
  c.check G &&
    decide (c.terms.map PackingTerm.triangle).Nodup &&
      c.terms.all (fun q ↦ decide (2 * q.numerator ≤ c.denominator)) &&
        decide (c.denominator * (G.edgeFinset.card - a) ≤ 3 * c.totalNumerator)

@[simp] theorem checkStrong_eq_true_iff
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : ℕ) (c : PackingCert n) :
    c.checkStrong G a = true ↔ c.StrongValid G a := by
  simp [checkStrong, StrongValid, List.all_eq_true, and_assoc]

section Semantic

/- The semantic definitions in `Fractional` deliberately use the classical
decision procedure.  Pin the same instance here so the checker instance never
leaks into a `cliqueFinset` occurring in a semantic theorem type. -/
attribute [local instance] Classical.propDecidable

private lemma sum_sparse_numerators (S : Finset (Finset (Fin n)))
    (l : List (PackingTerm n)) :
    ∑ t ∈ S, (l.map fun q ↦ if q.triangle = t then q.numerator else 0).sum =
      (l.map fun q ↦ if q.triangle ∈ S then q.numerator else 0).sum := by
  induction l with
  | nil => simp
  | cons q l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Finset.sum_add_distrib, ih]
      simp

lemma sum_triangleNumerator (c : PackingCert n) (S : Finset (Finset (Fin n))) :
    ∑ t ∈ S, c.triangleNumerator t =
      (c.terms.map fun q ↦ if q.triangle ∈ S then q.numerator else 0).sum := by
  exact sum_sparse_numerators S c.terms

/-- With distinct sparse triangle keys, looking up the key of a stored term
returns exactly that term's numerator. -/
lemma triangleNumerator_eq_term (c : PackingCert n)
    (hkeys : (c.terms.map PackingTerm.triangle).Nodup)
    (q : PackingTerm n) (hq : q ∈ c.terms) :
    c.triangleNumerator q.triangle = q.numerator := by
  classical
  unfold triangleNumerator
  rw [← List.sum_toFinset _ (hkeys.of_map PackingTerm.triangle)]
  calc
    ∑ r ∈ c.terms.toFinset,
        (if r.triangle = q.triangle then r.numerator else 0) =
        (if q.triangle = q.triangle then q.numerator else 0) := by
      apply Finset.sum_eq_single q
      · intro r hr hrq
        rw [if_neg]
        intro htri
        apply hrq
        exact List.inj_on_of_nodup_map hkeys (List.mem_toFinset.mp hr) hq htri
      · simp [hq]
    _ = q.numerator := if_pos rfl

lemma sum_triangleNumerator_cliques {G : SimpleGraph (Fin n)}
    (c : PackingCert n) (hterms : ∀ q ∈ c.terms, G.IsNClique 3 q.triangle) :
    ∑ t ∈ G.cliqueFinset 3, c.triangleNumerator t = c.totalNumerator := by
  classical
  rw [sum_triangleNumerator]
  unfold totalNumerator
  congr 1
  apply List.map_congr_left
  intro q hq
  simp [SimpleGraph.mem_cliqueFinset_iff, hterms q hq]

lemma sum_triangleNumerator_edge {G : SimpleGraph (Fin n)}
    (c : PackingCert n) (hterms : ∀ q ∈ c.terms, G.IsNClique 3 q.triangle)
    (e : Sym2 (Fin n)) :
    ∑ t ∈ (G.cliqueFinset 3).filter (fun t ↦ e ∈ t.sym2), c.triangleNumerator t =
      c.edgeNumerator e := by
  classical
  rw [sum_triangleNumerator]
  unfold edgeNumerator
  congr 1
  apply List.map_congr_left
  intro q hq
  simp [SimpleGraph.mem_cliqueFinset_iff, hterms q hq]

/-- Exact total-size interpretation of a certificate whose sparse entries are
genuine triangles of `G`. -/
lemma fractionalSize_weight {G : SimpleGraph (Fin n)}
    (c : PackingCert n) (hterms : ∀ q ∈ c.terms, G.IsNClique 3 q.triangle) :
    fractionalSize G c.weight = (c.totalNumerator : ℝ) / c.denominator := by
  classical
  rw [fractionalSize]
  simp only [weight]
  calc
    ∑ t ∈ G.cliqueFinset 3, (c.triangleNumerator t : ℝ) / c.denominator =
        (∑ t ∈ G.cliqueFinset 3, (c.triangleNumerator t : ℝ)) /
          c.denominator := (Finset.sum_div _ _ _).symm
    _ = (c.totalNumerator : ℝ) / c.denominator := by
      congr 1
      exact_mod_cast sum_triangleNumerator_cliques (G := G) c hterms

/-- Exact edge-load interpretation of a certificate whose sparse entries are
genuine triangles of `G`. -/
lemma fractionalEdgeLoad_weight {G : SimpleGraph (Fin n)}
    (c : PackingCert n) (hterms : ∀ q ∈ c.terms, G.IsNClique 3 q.triangle)
    (e : Sym2 (Fin n)) :
    fractionalEdgeLoad G c.weight e = (c.edgeNumerator e : ℝ) / c.denominator := by
  classical
  rw [fractionalEdgeLoad]
  simp only [weight]
  calc
    ∑ t ∈ (G.cliqueFinset 3).filter (fun t ↦ e ∈ t.sym2),
        (c.triangleNumerator t : ℝ) / c.denominator =
        (∑ t ∈ (G.cliqueFinset 3).filter (fun t ↦ e ∈ t.sym2),
          (c.triangleNumerator t : ℝ)) / c.denominator :=
      (Finset.sum_div _ _ _).symm
    _ = (c.edgeNumerator e : ℝ) / c.denominator := by
      congr 1
      exact_mod_cast sum_triangleNumerator_edge (G := G) c hterms e

/-- A triangle has exactly three present graph edges.  The `Nat.card`
intermediate avoids making the proof depend on a particular decidable
adjacency instance for the induced complete graph. -/
lemma card_edgeFinset_filter_triangle {G : SimpleGraph (Fin n)}
    (t : Finset (Fin n)) (ht : G.IsNClique 3 t) :
    ((G.edgeFinset).filter fun e ↦ e ∈ t.sym2).card = 3 := by
  classical
  rw [show (G.edgeFinset.filter fun e ↦ e ∈ t.sym2) =
      {e ∈ G.edgeFinset | e.toFinset ⊆ t} by
    ext e
    simp [Finset.mem_sym2_iff, subset_iff]]
  rw [G.card_filter_edgeFinset_toFinset_subset t]
  have htop : G.induce (↑t : Set (Fin n)) = ⊤ := G.induce_eq_top.mpr ht.isClique
  calc
    #(G.induce (↑t : Set (Fin n))).edgeFinset =
        Nat.card (G.induce (↑t : Set (Fin n))).edgeSet := by
          rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
    _ = Nat.card (⊤ : SimpleGraph t).edgeSet :=
      congrArg (fun H : SimpleGraph t ↦ Nat.card H.edgeSet) htop
    _ = #((⊤ : SimpleGraph t).edgeFinset) := by
      rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
    _ = (Fintype.card t).choose 2 :=
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two
    _ = 3 := by simp [ht.card_eq]

/-- Double-counting triangle--edge incidences: total edge load is three times
total triangle weight. -/
lemma sum_fractionalEdgeLoad_eq_three_mul_fractionalSize
    (G : SimpleGraph (Fin n)) (w : Finset (Fin n) → ℝ) :
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
  rw [card_edgeFinset_filter_triangle t
    (SimpleGraph.mem_cliqueFinset_iff.mp ht)]
  norm_num

/-- Semantic soundness of the proposition checked by `check`. -/
theorem Valid.isFractionalPacking {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (c : PackingCert n) (hc : c.Valid G) : IsFractionalPacking G c.weight := by
  constructor
  · intro t ht
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro e he
    have hedge : c.edgeNumerator e ≤ c.denominator := by
      induction e using Sym2.inductionOn with
      | _ i j =>
          apply hc.2.2 i (List.mem_finRange i) j (List.mem_finRange j)
          simpa [SimpleGraph.mem_edgeFinset] using he
    rw [fractionalEdgeLoad_weight c hc.2.1 e]
    apply (div_le_one (by exact_mod_cast hc.1)).2
    exact_mod_cast hedge

/-- An accepted Boolean certificate gives a fractional packing. -/
theorem check_sound {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (c : PackingCert n) (hc : c.check G = true) :
    IsFractionalPacking G c.weight :=
  (check_eq_true_iff G c).mp hc |>.isFractionalPacking c

/-- Combined form used by finite Gruslys--Letzter certificates: acceptance
gives both feasibility and the exact total weight represented by the sparse
natural numerators. -/
theorem check_sound_with_size {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (c : PackingCert n) (hc : c.check G = true) :
    IsFractionalPacking G c.weight ∧
      fractionalSize G c.weight = (c.totalNumerator : ℝ) / c.denominator := by
  have hv := (check_eq_true_iff G c).mp hc
  exact ⟨hv.isFractionalPacking c, fractionalSize_weight c hv.2.1⟩

/-! ## Soundness of strengthened predicates -/

/-- Exact coverage is in particular feasible coverage. -/
theorem ExactValid.valid {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (c : PackingCert n) (hc : c.ExactValid G) : c.Valid G := by
  refine ⟨hc.1, hc.2.1, ?_⟩
  intro i hi j hj hij
  exact (hc.2.2 i hi j hj hij).le

/-- Raw natural-numerator consequence of exact acceptance, for an arbitrary
unordered present edge. -/
theorem ExactValid.edgeNumerator_eq {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (c : PackingCert n) (hc : c.ExactValid G) (e : Sym2 (Fin n))
    (he : e ∈ G.edgeFinset) : c.edgeNumerator e = c.denominator := by
  induction e using Sym2.inductionOn with
  | _ i j =>
      apply hc.2.2 i (List.mem_finRange i) j (List.mem_finRange j)
      simpa [SimpleGraph.mem_edgeFinset] using he

/-- Exact natural coverage decodes to real edge load one. -/
theorem ExactValid.edgeLoad_eq_one {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (c : PackingCert n) (hc : c.ExactValid G) (e : Sym2 (Fin n))
    (he : e ∈ G.edgeFinset) : fractionalEdgeLoad G c.weight e = 1 := by
  rw [fractionalEdgeLoad_weight c hc.2.1 e, hc.edgeNumerator_eq c e he]
  exact div_self (by exact_mod_cast hc.1.ne')

/-- Kernel-checked semantic result of the exact Boolean verifier. -/
theorem checkExact_sound {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (c : PackingCert n) (hc : c.checkExact G = true) :
    IsFractionalPacking G c.weight ∧
      ∀ e ∈ G.edgeFinset, fractionalEdgeLoad G c.weight e = 1 := by
  have hv := (checkExact_eq_true_iff G c).mp hc
  exact ⟨hv.valid c |>.isFractionalPacking c, hv.edgeLoad_eq_one c⟩

/-- The ordinary feasibility part of a strong certificate. -/
theorem StrongValid.isFractionalPacking {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (a : ℕ) (c : PackingCert n) (hc : c.StrongValid G a) :
    IsFractionalPacking G c.weight :=
  hc.1.isFractionalPacking c

/-- Raw per-term half bound extracted from a strong certificate. -/
theorem StrongValid.termNumerator_le_half {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (a : ℕ) (c : PackingCert n) (hc : c.StrongValid G a)
    (q : PackingTerm n) (hq : q ∈ c.terms) :
    2 * q.numerator ≤ c.denominator :=
  hc.2.2.1 q hq

/-- The distinct-key condition upgrades all stored per-term bounds to a bound
on every aggregate triangle numerator, including absent triangles. -/
theorem StrongValid.triangleNumerator_le_half {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (a : ℕ) (c : PackingCert n) (hc : c.StrongValid G a)
    (t : Finset (Fin n)) : 2 * c.triangleNumerator t ≤ c.denominator := by
  by_cases ht : t ∈ c.terms.map PackingTerm.triangle
  · obtain ⟨q, hq, hqt⟩ := List.mem_map.mp ht
    rw [← hqt, triangleNumerator_eq_term c hc.2.1 q hq]
    exact hc.termNumerator_le_half a c q hq
  · have hzero : c.triangleNumerator t = 0 := by
      unfold triangleNumerator
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
      rw [if_neg]
      intro hqt
      exact ht (List.mem_map.mpr ⟨q, hq, hqt⟩)
    simp [hzero]

/-- Semantic half bound on the decoded real triangle weights.  This conclusion
is stated without importing `AlmostComplete`, so the checker core stays
independent of the later bridge definition. -/
theorem StrongValid.weight_le_half {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (a : ℕ) (c : PackingCert n) (hc : c.StrongValid G a)
    (t : Finset (Fin n)) : c.weight t ≤ (1 : ℝ) / 2 := by
  unfold weight
  have hd : (0 : ℝ) < c.denominator := by exact_mod_cast hc.1.1
  apply (div_le_div_iff₀ hd (by norm_num)).2
  have hhalf : (2 : ℝ) * c.triangleNumerator t ≤ c.denominator := by
    exact_mod_cast hc.triangleNumerator_le_half a c t
  simpa [mul_comm] using hhalf

/-- Raw natural objective inequality extracted from a strong certificate. -/
theorem StrongValid.objective {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (a : ℕ) (c : PackingCert n) (hc : c.StrongValid G a) :
    c.denominator * (G.edgeFinset.card - a) ≤ 3 * c.totalNumerator :=
  hc.2.2.2

/-- The natural strong objective becomes the exact lower bound on decoded
fractional size needed by finite Gruslys--Letzter certificates. -/
theorem StrongValid.fractionalSize_lower_bound
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (a : ℕ) (c : PackingCert n) (hc : c.StrongValid G a) :
    ((G.edgeFinset.card - a : ℕ) : ℝ) ≤ 3 * fractionalSize G c.weight := by
  rw [fractionalSize_weight c hc.1.2.1]
  have hd : (0 : ℝ) < c.denominator := by exact_mod_cast hc.1.1
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hd).2
  have hobjective :
      (c.denominator : ℝ) * ((G.edgeFinset.card - a : ℕ) : ℝ) ≤
        3 * (c.totalNumerator : ℝ) := by
    exact_mod_cast hc.objective a c
  simpa [mul_comm] using hobjective

/-- Kernel-checked feasibility and objective result of the strong Boolean
verifier. -/
theorem checkStrong_sound {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (a : ℕ) (c : PackingCert n) (hc : c.checkStrong G a = true) :
    IsFractionalPacking G c.weight ∧
      ((G.edgeFinset.card - a : ℕ) : ℝ) ≤
        3 * fractionalSize G c.weight := by
  have hv := (checkStrong_eq_true_iff G a c).mp hc
  exact ⟨hv.isFractionalPacking a c, hv.fractionalSize_lower_bound a c⟩

end Semantic

end PackingCert

end CertificateChecker
end Erdos76
