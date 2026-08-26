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

/-!
# Linear executable checker for strong packing certificates

`PackingCert.checkStrong` is a deliberately simple specification checker: for
each graph edge it scans the complete sparse term list.  That is convenient
for small certificates but unnecessarily expensive for the large finite
bases at orders 11--13.

This module provides a linear-in-the-number-of-terms data path.  It accumulates
the load matrix while traversing the terms, then scans the fixed `n × n`
matrix once.  Both orientations and diagonal cells are accumulated.  The
diagonal is ignored semantically, while storing it makes the executable update
and its correctness proof independent of an unordered-pair ranking theorem.
-/

namespace Erdos76
namespace CertificateChecker
namespace PackingCert

variable {n : ℕ}

/-- Add one value to a cell of a rectangular natural-number matrix. -/
def matrixAdd (loads : Array (Array ℕ)) (i j value : ℕ) : Array (Array ℕ) :=
  let row := loads.getD i #[]
  loads.setIfInBounds i (row.setIfInBounds j (row.getD j 0 + value))

@[simp] lemma matrixAdd_size (loads : Array (Array ℕ)) (i j value : ℕ) :
    (matrixAdd loads i j value).size = loads.size := by
  dsimp only [matrixAdd]
  exact Array.size_setIfInBounds

/-- Add one term row, for a fixed first vertex, to the three term vertices. -/
def addTermRow (loads : Array (Array ℕ)) (x : Fin n) (q : PackingTerm n) :
    Array (Array ℕ) :=
  matrixAdd (matrixAdd (matrixAdd loads x q.i q.numerator)
    x q.j q.numerator) x q.k q.numerator

/-- Add a term's numerator to all nine ordered pairs of its three vertices.
For a genuine three-vertex clique, each non-diagonal pair is updated exactly
once. -/
def addTermMatrix (loads : Array (Array ℕ)) (q : PackingTerm n) :
    Array (Array ℕ) :=
  addTermRow (addTermRow (addTermRow loads q.i q) q.j q) q.k q

/-- Matrix of all ordered-pair loads. -/
def loadMatrix (c : PackingCert n) : Array (Array ℕ) :=
  c.terms.foldl addTermMatrix (Array.replicate n (Array.replicate n 0))

/-- Linear executable verifier for the same strong natural-number
conditions as `checkStrong`. -/
def checkStrongFast (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : ℕ) (c : PackingCert n) : Bool :=
  decide (0 < c.denominator) &&
    c.terms.all (fun q ↦ decide (G.IsNClique 3 q.triangle)) &&
      decide (c.terms.map PackingTerm.triangle).Nodup &&
        c.terms.all (fun q ↦ decide (2 * q.numerator ≤ c.denominator)) &&
          (c.loadMatrix.all fun row ↦
            row.all fun load ↦ decide (load ≤ c.denominator)) &&
            decide (c.denominator * (G.edgeFinset.card - a) ≤
              3 * c.totalNumerator)

/-- Proposition computed by `checkStrongFast`. -/
def FastValid (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : ℕ) (c : PackingCert n) : Prop :=
  0 < c.denominator ∧
    (∀ q ∈ c.terms, G.IsNClique 3 q.triangle) ∧
      (c.terms.map PackingTerm.triangle).Nodup ∧
        (∀ q ∈ c.terms, 2 * q.numerator ≤ c.denominator) ∧
          (∀ i (hi : i < c.loadMatrix.size),
            ∀ j (hj : j < c.loadMatrix[i].size),
              c.loadMatrix[i][j] ≤ c.denominator) ∧
            c.denominator * (G.edgeFinset.card - a) ≤
              3 * c.totalNumerator

@[simp] theorem checkStrongFast_eq_true_iff
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : ℕ) (c : PackingCert n) :
    c.checkStrongFast G a = true ↔ c.FastValid G a := by
  simp [checkStrongFast, FastValid, List.all_eq_true,
    Array.all_eq_true, and_assoc]

/-! ## Correctness of matrix accumulation -/

/-- The shape invariant of an `n × n` load matrix. -/
def IsLoadMatrix (n : ℕ) (loads : Array (Array ℕ)) : Prop :=
  loads.size = n ∧ ∀ i < n, (loads.getD i #[]).size = n

lemma isLoadMatrix_replicate (n : ℕ) :
    IsLoadMatrix n (Array.replicate n (Array.replicate n 0)) := by
  constructor
  · simp
  · intro i hi
    simp [Array.getD_eq_getD_getElem?, hi]

lemma IsLoadMatrix.matrixAdd {loads : Array (Array ℕ)}
    (hloads : IsLoadMatrix n loads) (i j : Fin n) (value : ℕ) :
    IsLoadMatrix n (matrixAdd loads i j value) := by
  rw [IsLoadMatrix] at hloads ⊢
  constructor
  · rw [matrixAdd_size, hloads.1]
  · intro k hk
    have hi' : i.1 < loads.size := by simpa [hloads.1] using i.isLt
    have hrowi : loads[i.1].size = n := by
      simpa [Array.getD_eq_getD_getElem?, hi'] using hloads.2 i.1 i.isLt
    by_cases hki : k = i.1
    · subst k
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by
        rw [matrixAdd_size]
        exact hi'), Option.getD_some]
      unfold PackingCert.matrixAdd
      rw [Array.getElem_setIfInBounds_self, Array.size_setIfInBounds]
      exact hloads.2 i.1 i.isLt
    · have hk' : k < loads.size := by simpa [hloads.1] using hk
      have hrowk : loads[k].size = n := by
        simpa [Array.getD_eq_getD_getElem?, hk'] using hloads.2 k hk
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by
        rw [matrixAdd_size]
        exact hk'), Option.getD_some]
      unfold PackingCert.matrixAdd
      rw [Array.getElem_setIfInBounds_ne]
      · exact hrowk
      · exact Ne.symm hki

/-- Read one load-matrix cell, defaulting only for malformed matrices. -/
def matrixEntry (loads : Array (Array ℕ)) (i j : ℕ) : ℕ :=
  (loads.getD i #[]).getD j 0

lemma matrixEntry_matrixAdd {loads : Array (Array ℕ)}
    (hloads : IsLoadMatrix n loads) (x y i j : Fin n) (value : ℕ) :
    matrixEntry (matrixAdd loads x y value) i j =
      matrixEntry loads i j + if x = i ∧ y = j then value else 0 := by
  rw [IsLoadMatrix] at hloads
  have hx : x.1 < loads.size := by simpa [hloads.1] using x.isLt
  have hi : i.1 < loads.size := by simpa [hloads.1] using i.isLt
  have hrowx : (loads.getD x.1 #[]).size = n := hloads.2 x.1 x.isLt
  have hrowi : (loads.getD i.1 #[]).size = n := hloads.2 i.1 i.isLt
  have hrowx' : loads[x.1].size = n := by
    simpa [Array.getD_eq_getD_getElem?, hx] using hrowx
  have hrowi' : loads[i.1].size = n := by
    simpa [Array.getD_eq_getD_getElem?, hi] using hrowi
  by_cases hxi : x = i
  · subst i
    by_cases hyj : y = j
    · subst j
      simp [matrixEntry, matrixAdd, hx, hrowx, hrowx', x.isLt, y.isLt]
    · have hyjv : y.1 ≠ j.1 := fun h ↦ hyj (Fin.ext h)
      simp [matrixEntry, matrixAdd, hx, hrowx, hrowx', x.isLt, y.isLt,
        j.isLt, hyj, hyjv]
  · have hxiv : x.1 ≠ i.1 := fun h ↦ hxi (Fin.ext h)
    simp [matrixEntry, matrixAdd, hx, hi, hrowx, hrowi, hrowx', hrowi', x.isLt, y.isLt,
      i.isLt, j.isLt, hxi, hxiv]

/-- Contribution of one term to an ordered matrix cell. -/
def termMatrixEntry (q : PackingTerm n) (i j : Fin n) : ℕ :=
  (if q.i = i ∧ q.i = j then q.numerator else 0) +
  (if q.i = i ∧ q.j = j then q.numerator else 0) +
  (if q.i = i ∧ q.k = j then q.numerator else 0) +
  (if q.j = i ∧ q.i = j then q.numerator else 0) +
  (if q.j = i ∧ q.j = j then q.numerator else 0) +
  (if q.j = i ∧ q.k = j then q.numerator else 0) +
  (if q.k = i ∧ q.i = j then q.numerator else 0) +
  (if q.k = i ∧ q.j = j then q.numerator else 0) +
  (if q.k = i ∧ q.k = j then q.numerator else 0)

/-- Contribution of a fixed first-vertex row of a term. -/
def termRowEntry (x : Fin n) (q : PackingTerm n) (i j : Fin n) : ℕ :=
  (if x = i ∧ q.i = j then q.numerator else 0) +
  (if x = i ∧ q.j = j then q.numerator else 0) +
  (if x = i ∧ q.k = j then q.numerator else 0)

lemma IsLoadMatrix.addTermRow {loads : Array (Array ℕ)}
    (hloads : IsLoadMatrix n loads) (x : Fin n) (q : PackingTerm n) :
    IsLoadMatrix n (addTermRow loads x q) := by
  unfold PackingCert.addTermRow
  exact ((hloads.matrixAdd x q.i q.numerator).matrixAdd
    x q.j q.numerator).matrixAdd x q.k q.numerator

lemma matrixEntry_addTermRow {loads : Array (Array ℕ)}
    (hloads : IsLoadMatrix n loads) (x : Fin n) (q : PackingTerm n)
    (i j : Fin n) :
    matrixEntry (addTermRow loads x q) i j =
      matrixEntry loads i j + termRowEntry x q i j := by
  unfold addTermRow termRowEntry
  rw [matrixEntry_matrixAdd
      ((hloads.matrixAdd x q.i q.numerator).matrixAdd x q.j q.numerator),
    matrixEntry_matrixAdd (hloads.matrixAdd x q.i q.numerator),
    matrixEntry_matrixAdd hloads]
  omega

lemma IsLoadMatrix.addTermMatrix {loads : Array (Array ℕ)}
    (hloads : IsLoadMatrix n loads) (q : PackingTerm n) :
    IsLoadMatrix n (addTermMatrix loads q) := by
  unfold PackingCert.addTermMatrix
  exact ((hloads.addTermRow q.i q).addTermRow q.j q).addTermRow q.k q

lemma matrixEntry_addTermMatrix {loads : Array (Array ℕ)}
    (hloads : IsLoadMatrix n loads) (q : PackingTerm n) (i j : Fin n) :
    matrixEntry (addTermMatrix loads q) i j =
      matrixEntry loads i j + termMatrixEntry q i j := by
  unfold PackingCert.addTermMatrix termMatrixEntry
  rw [matrixEntry_addTermRow
      ((hloads.addTermRow q.i q).addTermRow q.j q),
    matrixEntry_addTermRow (hloads.addTermRow q.i q),
    matrixEntry_addTermRow hloads]
  unfold termRowEntry
  omega

/-- Sum of the contributions of a term list to one ordered cell. -/
def termMatrixSum (terms : List (PackingTerm n)) (i j : Fin n) : ℕ :=
  (terms.map fun q ↦ termMatrixEntry q i j).sum

lemma IsLoadMatrix.foldl_addTermMatrix {loads : Array (Array ℕ)}
    (hloads : IsLoadMatrix n loads) (terms : List (PackingTerm n)) :
    IsLoadMatrix n (terms.foldl PackingCert.addTermMatrix loads) := by
  induction terms generalizing loads with
  | nil => exact hloads
  | cons q terms ih =>
      apply ih
      exact IsLoadMatrix.addTermMatrix hloads q

lemma loadMatrix_isLoadMatrix (c : PackingCert n) :
    IsLoadMatrix n c.loadMatrix := by
  exact (isLoadMatrix_replicate n).foldl_addTermMatrix c.terms

lemma matrixEntry_foldl_addTermMatrix {loads : Array (Array ℕ)}
    (hloads : IsLoadMatrix n loads) (terms : List (PackingTerm n))
    (i j : Fin n) :
    matrixEntry (terms.foldl PackingCert.addTermMatrix loads) i j =
      matrixEntry loads i j + termMatrixSum terms i j := by
  induction terms generalizing loads with
  | nil => simp [termMatrixSum]
  | cons q terms ih =>
      rw [List.foldl_cons, ih (IsLoadMatrix.addTermMatrix hloads q),
        matrixEntry_addTermMatrix hloads]
      simp only [termMatrixSum, List.map_cons, List.sum_cons]
      omega

lemma matrixEntry_loadMatrix (c : PackingCert n) (i j : Fin n) :
    matrixEntry c.loadMatrix i j = termMatrixSum c.terms i j := by
  rw [loadMatrix, matrixEntry_foldl_addTermMatrix (isLoadMatrix_replicate n)]
  simp [matrixEntry]

lemma PackingTerm.pairwise_ne_of_isNClique {G : SimpleGraph (Fin n)}
    (q : PackingTerm n) (hq : G.IsNClique 3 q.triangle) :
    q.i ≠ q.j ∧ q.i ≠ q.k ∧ q.j ≠ q.k := by
  have hcard := hq.card_eq
  constructor
  · intro hij
    have hle : q.triangle.card ≤ 2 := by
      rw [PackingTerm.triangle, hij]
      simpa [PackingTerm.triangle, hij] using
        (Finset.card_le_two (a := q.j) (b := q.k))
    omega
  constructor
  · intro hik
    have hle : q.triangle.card ≤ 2 := by
      rw [PackingTerm.triangle, hik]
      simpa [PackingTerm.triangle, hik, Finset.pair_comm] using
        (Finset.card_le_two (a := q.k) (b := q.j))
    omega
  · intro hjk
    have hle : q.triangle.card ≤ 2 := by
      rw [PackingTerm.triangle, hjk]
      simpa [PackingTerm.triangle, hjk] using
        (Finset.card_le_two (a := q.i) (b := q.k))
    omega

lemma termMatrixEntry_eq_indicator {G : SimpleGraph (Fin n)}
    (q : PackingTerm n) (hq : G.IsNClique 3 q.triangle)
    (i j : Fin n) (hij : i ≠ j) :
    termMatrixEntry q i j =
      if s(i, j) ∈ q.triangle.sym2 then q.numerator else 0 := by
  obtain ⟨hqij, hqik, hqjk⟩ :=
    PackingTerm.pairwise_ne_of_isNClique q hq
  by_cases hii : q.i = i <;> by_cases hji : q.j = i <;>
    by_cases hki : q.k = i <;> by_cases hij : q.i = j <;>
    by_cases hjj : q.j = j <;> by_cases hkj : q.k = j <;>
    simp_all [termMatrixEntry, PackingTerm.triangle, Finset.mk_mem_sym2_iff] <;>
    aesop

lemma termMatrixSum_eq_edgeNumerator {G : SimpleGraph (Fin n)}
    (c : PackingCert n)
    (hterms : ∀ q ∈ c.terms, G.IsNClique 3 q.triangle)
    (i j : Fin n) (hij : i ≠ j) :
    termMatrixSum c.terms i j = c.edgeNumerator s(i, j) := by
  unfold termMatrixSum edgeNumerator
  congr 1
  apply List.map_congr_left
  intro q hq
  exact termMatrixEntry_eq_indicator q (hterms q hq) i j hij

lemma matrixEntry_eq_getElem (loads : Array (Array ℕ)) {i j : ℕ}
    (hi : i < loads.size) (hj : j < loads[i].size) :
    matrixEntry loads i j = loads[i][j] := by
  simp [matrixEntry, Array.getD_eq_getD_getElem?, hi, hj]

/-- The linear matrix checker implies the original `StrongValid`
specification. -/
theorem FastValid.strongValid {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (a : ℕ) (c : PackingCert n) (hc : c.FastValid G a) :
    c.StrongValid G a := by
  rcases hc with ⟨hden, hterms, hkeys, hhalf, hloads, hobjective⟩
  refine ⟨⟨hden, hterms, ?_⟩, hkeys, hhalf, hobjective⟩
  intro i hi j hj hadj
  have hij : i ≠ j := by
    intro hij
    subst j
    exact G.loopless.irrefl i hadj
  have hmatrix := loadMatrix_isLoadMatrix c
  have hiMatrix : i.1 < c.loadMatrix.size := by
    rw [hmatrix.1]
    exact i.isLt
  have hrowSize : c.loadMatrix[i.1].size = n := by
    rw [IsLoadMatrix] at hmatrix
    have hrowD := hmatrix.2 i.1 i.isLt
    simpa [Array.getD_eq_getD_getElem?, hiMatrix] using hrowD
  have hjMatrix : j.1 < c.loadMatrix[i.1].size := by
    rw [hrowSize]
    exact j.isLt
  have hbound : c.loadMatrix[i.1][j.1] ≤ c.denominator :=
    hloads i.1 hiMatrix j.1 hjMatrix
  rw [← termMatrixSum_eq_edgeNumerator c hterms i j hij,
    ← matrixEntry_loadMatrix, matrixEntry_eq_getElem c.loadMatrix hiMatrix hjMatrix]
  exact hbound

/-- Kernel-checked semantic soundness of the linear verifier. -/
theorem checkStrongFast_sound {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (a : ℕ) (c : PackingCert n) (hc : c.checkStrongFast G a = true) :
    HasStrongFractionalPacking G (a : ℝ) := by
  apply PackingCert.checkStrong_sound_hasStrongFractionalPacking a c
  exact (checkStrong_eq_true_iff G a c).mpr
    ((checkStrongFast_eq_true_iff G a c).mp hc |>.strongValid a c)

end PackingCert
end CertificateChecker
end Erdos76
