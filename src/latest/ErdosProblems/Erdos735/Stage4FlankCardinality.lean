/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos735.FlankExtraction
import ErdosProblems.Erdos735.ConcretePolarABKPRData
import ErdosProblems.Erdos735.LeviSignVector

/-!
# The cyclic two-flank bound

The two possible flanks of an evil triangle are the successor and the
predecessor of its bad dart on the adjacent quadrangle.  This file proves
the corresponding cardinality bound directly from the cyclic boundary and
injectivity of supporting-line labels on a face.
-/

open Classical
noncomputable section

namespace Erdos735
namespace ABKPR

theorem cyclicSucc_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (cyclicSucc hn) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simp only [cyclicSucc] at hval
  by_cases hi : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hi] at hval
    by_cases hj : j.val + 1 < n
    · rw [Nat.mod_eq_of_lt hj] at hval
      omega
    · have hjlast : j.val + 1 = n := by omega
      rw [hjlast, Nat.mod_self] at hval
      omega
  · have hilast : i.val + 1 = n := by omega
    rw [hilast, Nat.mod_self] at hval
    by_cases hj : j.val + 1 < n
    · rw [Nat.mod_eq_of_lt hj] at hval
      omega
    · omega

theorem faceSucc_injective
    {Vertex Edge Face : Type*}
    [Fintype Vertex] [Fintype Edge] [Fintype Face]
    [DecidableEq Vertex] [DecidableEq Edge] [DecidableEq Face]
    (C : BlueCellulation Vertex Edge Face) (f : Face) :
    Function.Injective (faceSucc C f) :=
  cyclicSucc_injective (faceDegree_pos C f)

namespace Data

universe uV uEd uF uL

variable {Vertex : Type uV} {Edge : Type uEd} {Face : Type uF}
variable [Fintype Vertex] [Fintype Edge] [Fintype Face]
variable [DecidableEq Vertex] [DecidableEq Edge] [DecidableEq Face]
variable {C : BlueCellulation Vertex Edge Face}
variable {A : ABKPR.Data C}
variable {Line : Type uL} [Fintype Line] [DecidableEq Line]

private noncomputable def geometricFlankAdjacentIndex
    (edgeLine : Edge → Line) (e : A.EvilFace)
    (h : {h : A.HelpingPair // A.IsGeometricFlank edgeLine e h}) :
    Fin (C.faceDegree (A.across (A.evilDart e)).1) :=
  Classical.choose h.2.1

private theorem geometricFlankAdjacentIndex_spec
    (edgeLine : Edge → Line) (e : A.EvilFace)
    (h : {h : A.HelpingPair // A.IsGeometricFlank edgeLine e h}) :
    CyclicAdjacentIndex (C := C) (A.across (A.evilDart e)).2
        (A.geometricFlankAdjacentIndex edgeLine e h) ∧
      (A.across ⟨(A.across (A.evilDart e)).1,
        A.geometricFlankAdjacentIndex edgeLine e h⟩).1 = h.1.face :=
  Classical.choose_spec h.2.1

private noncomputable def geometricFlankSide
    (edgeLine : Edge → Line) (e : A.EvilFace)
    (h : {h : A.HelpingPair // A.IsGeometricFlank edgeLine e h}) : Bool :=
  decide (faceSucc C (A.across (A.evilDart e)).1
    (A.across (A.evilDart e)).2 =
      A.geometricFlankAdjacentIndex edgeLine e h)

/-- Supporting-line injectivity on each face makes the two cyclic flank
slots injectively enumerate all geometric flanks of a fixed evil face. -/
theorem geometricFlanks_card_le_two_of_boundaryLine_injective
    (edgeLine : Edge → Line)
    (hinj : ∀ f, Function.Injective
      (fun i ↦ edgeLine (A.boundaryEdge f i)))
    (e : A.EvilFace) :
    (A.geometricFlanks edgeLine e).card ≤ 2 := by
  rw [← Fintype.card_coe]
  let φ : {h : A.HelpingPair // h ∈ A.geometricFlanks edgeLine e} → Bool :=
    fun h ↦ A.geometricFlankSide edgeLine e
      ⟨h.1, (Finset.mem_filter.mp h.2).2⟩
  have hφ : Function.Injective φ := by
    intro h k hside
    let h' : {h : A.HelpingPair // A.IsGeometricFlank edgeLine e h} :=
      ⟨h.1, (Finset.mem_filter.mp h.2).2⟩
    let k' : {h : A.HelpingPair // A.IsGeometricFlank edgeLine e h} :=
      ⟨k.1, (Finset.mem_filter.mp k.2).2⟩
    let q := A.across (A.evilDart e)
    let jh := A.geometricFlankAdjacentIndex edgeLine e h'
    let jk := A.geometricFlankAdjacentIndex edgeLine e k'
    have hh := A.geometricFlankAdjacentIndex_spec edgeLine e h'
    have hk := A.geometricFlankAdjacentIndex_spec edgeLine e k'
    change A.geometricFlankSide edgeLine e h' =
      A.geometricFlankSide edgeLine e k' at hside
    have hj : jh = jk := by
      by_cases hs : faceSucc C q.1 q.2 = jh
      · have hst : A.geometricFlankSide edgeLine e h' = true := by
          change decide (faceSucc C (A.across (A.evilDart e)).1
            (A.across (A.evilDart e)).2 =
              A.geometricFlankAdjacentIndex edgeLine e h') = true
          exact decide_eq_true (by simpa [q, jh] using hs)
        have hkt : A.geometricFlankSide edgeLine e k' = true := by
          exact hside.symm.trans hst
        have hsk : faceSucc C q.1 q.2 = jk := by
          change decide (faceSucc C (A.across (A.evilDart e)).1
            (A.across (A.evilDart e)).2 =
              A.geometricFlankAdjacentIndex edgeLine e k') = true at hkt
          simpa [q, jk] using of_decide_eq_true hkt
        exact hs.symm.trans hsk
      · have hs' : faceSucc C (A.across (A.evilDart e)).1
            (A.across (A.evilDart e)).2 ≠ jh := by
          simpa [q] using hs
        have hjh : faceSucc C q.1 jh = q.2 := by
          simpa [q, jh] using hh.1.resolve_left hs'
        have hsf : A.geometricFlankSide edgeLine e h' = false := by
          change decide (faceSucc C (A.across (A.evilDart e)).1
            (A.across (A.evilDart e)).2 =
              A.geometricFlankAdjacentIndex edgeLine e h') = false
          exact decide_eq_false (by simpa [q, jh] using hs)
        have hkf : A.geometricFlankSide edgeLine e k' = false := by
          exact hside.symm.trans hsf
        have hsk : faceSucc C q.1 q.2 ≠ jk := by
          change decide (faceSucc C (A.across (A.evilDart e)).1
            (A.across (A.evilDart e)).2 =
              A.geometricFlankAdjacentIndex edgeLine e k') = false at hkf
          simpa [q, jk] using of_decide_eq_false hkf
        have hsk' : faceSucc C (A.across (A.evilDart e)).1
            (A.across (A.evilDart e)).2 ≠ jk := by
          simpa [q] using hsk
        have hjk : faceSucc C q.1 jk = q.2 := by
          simpa [q, jk] using hk.1.resolve_left hsk'
        exact (faceSucc_injective C q.1) (hjh.trans hjk.symm)
    apply Subtype.ext
    rcases h with ⟨⟨hf, hi⟩, hhmem⟩
    rcases k with ⟨⟨kf, ki⟩, hkmem⟩
    have hface : hf = kf := by
      change h'.1.1 = k'.1.1
      calc
        h'.1.1 = (A.across ⟨(A.across (A.evilDart e)).1, jh⟩).1 := by
          change h'.1.face = _
          simpa [jh] using hh.2.symm
        _ = (A.across ⟨(A.across (A.evilDart e)).1, jk⟩).1 := by
          exact congrArg (fun j ↦ (A.across
            ⟨(A.across (A.evilDart e)).1, j⟩).1) hj
        _ = k'.1.1 := by
          have hkr := hk.2
          change _ = k'.1.face at hkr
          simpa only [jk, HelpingPair.face] using hkr
    subst kf
    change (⟨hf, hi⟩ : A.HelpingPair) = ⟨hf, ki⟩
    congr 1
    apply Subtype.ext
    apply hinj hf
    exact h'.2.2.trans k'.2.2.symm
  have hc := Fintype.card_le_of_injective φ hφ
  simpa using hc

end Data
end ABKPR

namespace ConcreteStage4Flanks

open ProjectiveArrangement ProjectiveBoundaryExtraction SignVector
open SignVectorArrangement
open ConcretePolarABKPRData
open ConcretePolarOrientedVertex

abbrev Point := ProjectiveArrangement.Point

variable {P : Finset Point} {w : Point → ℝ} {c : ℝ}
variable (hred : IsReducedMagic P w c)
variable {a b d : Point}
variable (ha : a ∈ nonordinaryPoints P) (hb : b ∈ nonordinaryPoints P)
variable (hd : d ∈ nonordinaryPoints P)
variable (hncol : ¬ ProjectiveDuality.Collinear3 a b d)
variable [Nonempty (ProjectiveBoundaryExtraction.Line (nonordinaryPoints P))]

abbrev C := ConcretePolarCellulation.blueCellulation
  (nonordinaryPoints P) ha hb hd hncol

abbrev D := ConcretePolarABKPRData.concreteData hred ha hb hd hncol

/-- On a concrete polar face, the supporting arrangement-line label is
injective along the boundary. -/
theorem boundaryOwner_injective
    (f : StrictFace (normals (nonordinaryPoints P))) :
    Function.Injective (fun i ↦
      strictEdgeOwner ((D hred ha hb hd hncol).boundaryEdge f i)) := by
  intro i j hij
  apply (D hred ha hb hd hncol).boundaryEdge_injective f
  apply strictEdgeOwner_injOn_faceEdges (normals (nonordinaryPoints P)) f
  · rw [← SignVector.PolarBoundaryAcross.faceBoundary_toFinset
      (normals (nonordinaryPoints P)) normal_cross
      (ConcretePolarABKPRData.hspan ha hb hd hncol) f]
    exact List.mem_toFinset.mpr ((D hred ha hb hd hncol).boundaryEdge_mem f i)
  · rw [← SignVector.PolarBoundaryAcross.faceBoundary_toFinset
      (normals (nonordinaryPoints P)) normal_cross
      (ConcretePolarABKPRData.hspan ha hb hd hncol) f]
    exact List.mem_toFinset.mpr ((D hred ha hb hd hncol).boundaryEdge_mem f j)
  · exact hij

/-- The concrete polar arrangement has at most the two literal cyclic
flanks of an evil face. -/
theorem geometricFlanks_card_le_two (e : (D hred ha hb hd hncol).EvilFace) :
    ((D hred ha hb hd hncol).geometricFlanks strictEdgeOwner e).card ≤ 2 :=
  ABKPR.Data.geometricFlanks_card_le_two_of_boundaryLine_injective
    strictEdgeOwner
    (boundaryOwner_injective hred ha hb hd hncol) e

end ConcreteStage4Flanks
end Erdos735
