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
import ErdosProblems.Erdos76.FastCertificateChecker

/-!
# Flat linear verifier for strong certificates

The verified matrix checker is already linear, but nine persistent-array
updates per triangle make its kernel reduction term too deep for the stock
recursion limit on a full certificate.  This production checker uses the
canonical unordered `edgeIndex` and performs exactly three updates per term.

Soundness is parameterized by the finite proposition `PairIndexValid n`.
That proposition says that `edgeIndex` is in range and injective on non-loop
unordered pairs.  The only orders needed by the finite bases (`11`, `12`, and
`13`) are checked once in small order-specific data modules by ordinary
kernel `decide`; the check is not repeated for every packing certificate.
-/

namespace Erdos76
namespace CertificateChecker
namespace PackingCert

variable {n : ℕ}

/-- `edgeIndex` is a valid array index and classifies unordered non-loop
pairs on `Fin n`. -/
def PairIndexValid (n : ℕ) : Prop :=
  (∀ i j : Fin n, i ≠ j → edgeIndex i j < edgeCount n) ∧
  (∀ i j k l : Fin n, i ≠ j → k ≠ l →
    (edgeIndex i j = edgeIndex k l ↔ s(i, j) = s(k, l)))

instance (n : ℕ) : Decidable (PairIndexValid n) := by
  unfold PairIndexValid
  infer_instance

/-- One independently decidable row of `PairIndexValid`.  Keeping the first
vertex fixed makes the stock-kernel checks for orders `11`--`13` small enough
to run without changing any reduction limit. -/
def PairIndexRowValid (n : ℕ) (i : Fin n) : Prop :=
  (∀ j : Fin n, i ≠ j → edgeIndex i j < edgeCount n) ∧
  (∀ j k l : Fin n, i ≠ j → k ≠ l →
    (edgeIndex i j = edgeIndex k l ↔ s(i, j) = s(k, l)))

instance (n : ℕ) (i : Fin n) : Decidable (PairIndexRowValid n i) := by
  unfold PairIndexRowValid
  infer_instance

/-- Assemble the global pair-index property from independently checked
first-vertex rows. -/
theorem pairIndexValid_of_rows (n : ℕ)
    (h : ∀ i : Fin n, PairIndexRowValid n i) : PairIndexValid n := by
  constructor
  · intro i j hij
    exact (h i).1 j hij
  · intro i j k l hij hkl
    exact (h i).2 j k l hij hkl

/-- Add one numerator to a flat edge-load array. -/
def edgeLoadAdd (loads : Array ℕ) (index value : ℕ) : Array ℕ :=
  loads.setIfInBounds index (loads.getD index 0 + value)

@[simp] lemma edgeLoadAdd_size (loads : Array ℕ) (index value : ℕ) :
    (edgeLoadAdd loads index value).size = loads.size := by
  exact Array.size_setIfInBounds

/-- Three unordered edge updates for one triangle. -/
def addTermEdgeLoads (loads : Array ℕ) (q : PackingTerm n) : Array ℕ :=
  edgeLoadAdd
    (edgeLoadAdd
      (edgeLoadAdd loads (edgeIndex q.i q.j) q.numerator)
      (edgeIndex q.i q.k) q.numerator)
    (edgeIndex q.j q.k) q.numerator

/-- Flat accumulated load of every unordered-pair index. -/
def edgeLoads (c : PackingCert n) : Array ℕ :=
  c.terms.foldl addTermEdgeLoads (Array.replicate (edgeCount n) 0)

/-- Contribution of one sparse term at one unordered-pair index. -/
def termEdgeEntry (q : PackingTerm n) (index : ℕ) : ℕ :=
  (if edgeIndex q.i q.j = index then q.numerator else 0) +
  (if edgeIndex q.i q.k = index then q.numerator else 0) +
  (if edgeIndex q.j q.k = index then q.numerator else 0)

/-- Total numerator carried by one unordered-pair index. -/
def termEdgeSum (terms : List (PackingTerm n)) (index : ℕ) : ℕ :=
  (terms.map fun q ↦ termEdgeEntry q index).sum

/-- Production linear verifier. -/
def checkStrongLinear (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : ℕ) (c : PackingCert n) : Bool :=
  decide (0 < c.denominator) &&
    c.terms.all (fun q ↦ decide (G.IsNClique 3 q.triangle)) &&
      decide (c.terms.map PackingTerm.triangle).Nodup &&
        c.terms.all (fun q ↦ decide (2 * q.numerator ≤ c.denominator)) &&
          (List.range (edgeCount n)).all (fun index ↦
            decide (termEdgeSum c.terms index ≤ c.denominator)) &&
            decide (c.denominator * (G.edgeFinset.card - a) ≤
              3 * c.totalNumerator)

/-- Proposition reflected by `checkStrongLinear`. -/
def LinearValid (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : ℕ) (c : PackingCert n) : Prop :=
  0 < c.denominator ∧
    (∀ q ∈ c.terms, G.IsNClique 3 q.triangle) ∧
      (c.terms.map PackingTerm.triangle).Nodup ∧
        (∀ q ∈ c.terms, 2 * q.numerator ≤ c.denominator) ∧
          (∀ index < edgeCount n,
            termEdgeSum c.terms index ≤ c.denominator) ∧
            c.denominator * (G.edgeFinset.card - a) ≤
              3 * c.totalNumerator

@[simp] theorem checkStrongLinear_eq_true_iff
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : ℕ) (c : PackingCert n) :
    c.checkStrongLinear G a = true ↔ c.LinearValid G a := by
  simp [checkStrongLinear, LinearValid, List.all_eq_true,
    and_assoc]

/-! ## Flat accumulator correctness -/

lemma edgeLoadAdd_getD (loads : Array ℕ) {added index : ℕ}
    (hadded : added < loads.size) (hindex : index < loads.size) (value : ℕ) :
    (edgeLoadAdd loads added value).getD index 0 =
      loads.getD index 0 + if added = index then value else 0 := by
  by_cases h : added = index
  · subst index
    simp [edgeLoadAdd, Array.getD_eq_getD_getElem?, hadded]
  · simp [edgeLoadAdd, Array.getD_eq_getD_getElem?, hadded, hindex, h]

lemma addTermEdgeLoads_size (loads : Array ℕ) (q : PackingTerm n) :
    (addTermEdgeLoads loads q).size = loads.size := by
  simp [addTermEdgeLoads]

lemma addTermEdgeLoads_getD (hpairs : PairIndexValid n)
    (loads : Array ℕ) (hsize : loads.size = edgeCount n)
    (q : PackingTerm n) (hq : q.i ≠ q.j ∧ q.i ≠ q.k ∧ q.j ≠ q.k)
    (index : ℕ) (hindex : index < loads.size) :
    (addTermEdgeLoads loads q).getD index 0 =
      loads.getD index 0 + termEdgeEntry q index := by
  have hij : edgeIndex q.i q.j < loads.size := by
    rw [hsize]
    exact hpairs.1 q.i q.j hq.1
  have hik : edgeIndex q.i q.k < loads.size := by
    rw [hsize]
    exact hpairs.1 q.i q.k hq.2.1
  have hjk : edgeIndex q.j q.k < loads.size := by
    rw [hsize]
    exact hpairs.1 q.j q.k hq.2.2
  unfold addTermEdgeLoads termEdgeEntry
  rw [edgeLoadAdd_getD
      (loads := edgeLoadAdd (edgeLoadAdd loads (edgeIndex q.i q.j) q.numerator)
        (edgeIndex q.i q.k) q.numerator)
      (added := edgeIndex q.j q.k) (index := index)
      (by simpa using hjk) (by simpa using hindex),
    edgeLoadAdd_getD
      (loads := edgeLoadAdd loads (edgeIndex q.i q.j) q.numerator)
      (added := edgeIndex q.i q.k) (index := index)
      (by simpa using hik) (by simpa using hindex),
    edgeLoadAdd_getD (loads := loads) (added := edgeIndex q.i q.j)
      (index := index) hij hindex]
  omega

lemma foldl_addTermEdgeLoads_size (loads : Array ℕ)
    (terms : List (PackingTerm n)) :
    (terms.foldl addTermEdgeLoads loads).size = loads.size := by
  induction terms generalizing loads with
  | nil => rfl
  | cons q terms ih =>
      rw [List.foldl_cons, ih, addTermEdgeLoads_size]

lemma foldl_addTermEdgeLoads_getD (hpairs : PairIndexValid n)
    {G : SimpleGraph (Fin n)} (loads : Array ℕ)
    (hsize : loads.size = edgeCount n) (terms : List (PackingTerm n))
    (hterms : ∀ q ∈ terms, G.IsNClique 3 q.triangle)
    (index : ℕ) (hindex : index < loads.size) :
    (terms.foldl addTermEdgeLoads loads).getD index 0 =
      loads.getD index 0 + termEdgeSum terms index := by
  induction terms generalizing loads with
  | nil => simp [termEdgeSum]
  | cons q terms ih =>
      have hq := PackingTerm.pairwise_ne_of_isNClique q
        (hterms q (by simp))
      rw [List.foldl_cons, ih (loads := addTermEdgeLoads loads q)
        (by simpa [addTermEdgeLoads_size] using hsize)
        (fun r hr ↦ hterms r (by simp [hr]))
        (by simpa [addTermEdgeLoads_size] using hindex),
        addTermEdgeLoads_getD hpairs loads hsize q hq index hindex]
      simp only [termEdgeSum, List.map_cons, List.sum_cons]
      omega

lemma edgeLoads_size (c : PackingCert n) : c.edgeLoads.size = edgeCount n := by
  rw [edgeLoads, foldl_addTermEdgeLoads_size]
  simp

lemma edgeLoads_getD (hpairs : PairIndexValid n)
    {G : SimpleGraph (Fin n)} (c : PackingCert n)
    (hterms : ∀ q ∈ c.terms, G.IsNClique 3 q.triangle)
    (index : ℕ) (hindex : index < edgeCount n) :
    c.edgeLoads.getD index 0 = termEdgeSum c.terms index := by
  have hi : index < (Array.replicate (edgeCount n) 0).size := by
    simpa only [Array.size_replicate] using hindex
  rw [edgeLoads, foldl_addTermEdgeLoads_getD hpairs _ (by simp) c.terms
    hterms index hi]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
  simp

/-! ## Agreement with unordered edge loads -/

lemma termEdgeEntry_eq_indicator (hpairs : PairIndexValid n)
    {G : SimpleGraph (Fin n)} (q : PackingTerm n)
    (hq : G.IsNClique 3 q.triangle) (i j : Fin n) (hij : i ≠ j) :
    termEdgeEntry q (edgeIndex i j) =
      if s(i, j) ∈ q.triangle.sym2 then q.numerator else 0 := by
  obtain ⟨hqij, hqik, hqjk⟩ :=
    PackingTerm.pairwise_ne_of_isNClique q hq
  have h₁ := hpairs.2 q.i q.j i j hqij hij
  have h₂ := hpairs.2 q.i q.k i j hqik hij
  have h₃ := hpairs.2 q.j q.k i j hqjk hij
  have hp₁₂ : s(q.i, q.j) ≠ s(q.i, q.k) := by
    simp [Sym2.eq_iff, hqij, hqik, hqjk]
  have hp₁₃ : s(q.i, q.j) ≠ s(q.j, q.k) := by
    simp [Sym2.eq_iff, hqij, hqik, hqjk]
  have hp₂₃ : s(q.i, q.k) ≠ s(q.j, q.k) := by
    simp [Sym2.eq_iff, hqij, hqik, hqjk]
  unfold termEdgeEntry
  simp only [h₁, h₂, h₃]
  by_cases h₁ : s(q.i, q.j) = s(i, j) <;>
    by_cases h₂ : s(q.i, q.k) = s(i, j) <;>
    by_cases h₃ : s(q.j, q.k) = s(i, j) <;>
    simp_all [PackingTerm.triangle, Finset.mk_mem_sym2_iff, Sym2.eq_iff] <;>
    aesop

lemma termEdgeSum_eq_edgeNumerator (hpairs : PairIndexValid n)
    {G : SimpleGraph (Fin n)} (c : PackingCert n)
    (hterms : ∀ q ∈ c.terms, G.IsNClique 3 q.triangle)
    (i j : Fin n) (hij : i ≠ j) :
    termEdgeSum c.terms (edgeIndex i j) = c.edgeNumerator s(i, j) := by
  unfold termEdgeSum edgeNumerator
  congr 1
  apply List.map_congr_left
  intro q hq
  exact termEdgeEntry_eq_indicator hpairs q (hterms q hq) i j hij

/-- Linear validity implies the original strong specification. -/
theorem LinearValid.strongValid (hpairs : PairIndexValid n)
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (a : ℕ) (c : PackingCert n) (hc : c.LinearValid G a) :
    c.StrongValid G a := by
  rcases hc with ⟨hden, hterms, hkeys, hhalf, hloads, hobjective⟩
  refine ⟨⟨hden, hterms, ?_⟩, hkeys, hhalf, hobjective⟩
  intro i hi j hj hadj
  have hij : i ≠ j := by
    intro hij
    subst j
    exact G.loopless.irrefl i hadj
  have hindex : edgeIndex i j < edgeCount n := hpairs.1 i j hij
  rw [← termEdgeSum_eq_edgeNumerator hpairs c hterms i j hij]
  exact hloads (edgeIndex i j) hindex

/-- Semantic soundness of the production linear verifier. -/
theorem checkStrongLinear_sound (hpairs : PairIndexValid n)
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (a : ℕ) (c : PackingCert n) (hc : c.checkStrongLinear G a = true) :
    HasStrongFractionalPacking G (a : ℝ) := by
  apply PackingCert.checkStrong_sound_hasStrongFractionalPacking a c
  exact (checkStrong_eq_true_iff G a c).mpr
    ((checkStrongLinear_eq_true_iff G a c).mp hc |>.strongValid hpairs a c)

end PackingCert
end CertificateChecker
end Erdos76
