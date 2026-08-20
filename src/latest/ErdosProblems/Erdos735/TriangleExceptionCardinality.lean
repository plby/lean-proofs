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

import ErdosProblems.Erdos735.ConcreteStage3Local
import ErdosProblems.Erdos735.ConcreteStrictEdgeCyclic
import ErdosProblems.Erdos735.ConcretePolarRecognition

/-!
# The two-bad-neighbours triangle exception

This file proves the local cardinality statement behind ABKPR's
one-bad-quadrangle-per-triangle lemma.  Two consecutive bad quadrangles at a
literal polar triangle determine three consecutive intervals on the third
boundary owner.  Hence that projective blue line has exactly three vertices;
the two triangle endpoints are double, and failed-Fano recognition applies.
-/

open Classical
noncomputable section
open scoped LinearAlgebra.Projectivization Matrix

namespace Erdos735.TriangleExceptionCardinality

open ProjectiveArrangement ProjectiveBoundaryExtraction SignVector ChartOrder
open SignVector.RedChordSector
open SignVector.ProjectiveEdgeEndpointEquiv
open ConcretePolarOrientedVertex ConcretePolarEdgeVertices
open SignVector.PolarBoundaryAcross

abbrev Point := ProjectiveArrangement.Point
private abbrev PBLine (B : Finset Point) :=
  ProjectiveBoundaryExtraction.Line B
private abbrev PBVertex (B : Finset Point) :=
  ProjectiveBoundaryExtraction.Vertex B

private lemma fin_four_other_neighbor
    (b a x : Fin 4)
    (hba : a = ABKPR.cyclicSucc (by decide) b ∨
      b = ABKPR.cyclicSucc (by decide) a)
    (hxb : x ≠ b)
    (hxnext : x ≠ ABKPR.cyclicSucc (by decide) b)
    (hnextx : b ≠ ABKPR.cyclicSucc (by decide) x) :
    x = ABKPR.cyclicSucc (by decide) a ∨
      a = ABKPR.cyclicSucc (by decide) x := by
  fin_cases b <;> fin_cases a <;> fin_cases x <;>
    simp [ABKPR.cyclicSucc] at hba hxb hxnext hnextx ⊢

private lemma cyclic_succ_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (ABKPR.cyclicSucc hn) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simp only [ABKPR.cyclicSucc] at hval
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

private lemma fin_three_distinct_are_cyclic_neighbors
    {m : ℕ} (hm : m = 3) (i j : Fin m) (hij : i ≠ j) :
    j = ABKPR.cyclicSucc (by omega) i ∨
      i = ABKPR.cyclicSucc (by omega) j := by
  simp only [Fin.ext_iff, ABKPR.cyclicSucc] at hij ⊢
  simp only [hm] at hij ⊢
  omega

private lemma other_neighbor_of_degree_four
    {m : ℕ} (hm : m = 4) (b a x : Fin m)
    (hba : a = ABKPR.cyclicSucc (by omega) b ∨
      b = ABKPR.cyclicSucc (by omega) a)
    (hxb : x ≠ b)
    (hxnext : x ≠ ABKPR.cyclicSucc (by omega) b)
    (hnextx : b ≠ ABKPR.cyclicSucc (by omega) x) :
    x = ABKPR.cyclicSucc (by omega) a ∨
      a = ABKPR.cyclicSucc (by omega) x := by
  let cast : Fin m → Fin 4 := Fin.cast hm
  have cast_inj : Function.Injective cast := Fin.cast_injective hm
  have cast_succ (q : Fin m) :
      cast (ABKPR.cyclicSucc (by omega) q) =
        ABKPR.cyclicSucc (by decide) (cast q) := by
    apply Fin.ext
    simp [cast, ABKPR.cyclicSucc, hm]
  have hba' : cast a = ABKPR.cyclicSucc (by decide) (cast b) ∨
      cast b = ABKPR.cyclicSucc (by decide) (cast a) := by
    rcases hba with h | h
    · exact Or.inl (congrArg cast h |>.trans (cast_succ b))
    · exact Or.inr (congrArg cast h |>.trans (cast_succ a))
  have hxb' : cast x ≠ cast b := fun h ↦ hxb (cast_inj h)
  have hxnext' : cast x ≠ ABKPR.cyclicSucc (by decide) (cast b) := by
    rw [← cast_succ]
    exact fun h ↦ hxnext (cast_inj h)
  have hnextx' : cast b ≠ ABKPR.cyclicSucc (by decide) (cast x) := by
    rw [← cast_succ]
    exact fun h ↦ hnextx (cast_inj h)
  rcases fin_four_other_neighbor (cast b) (cast a) (cast x)
      hba' hxb' hxnext' hnextx' with h | h
  · left
    apply cast_inj
    rw [cast_succ]
    exact h
  · right
    apply cast_inj
    rw [cast_succ]
    exact h

private lemma line_eq_of_multiplicity_two
    {B : Finset Point} (v : PBVertex B) (l₀ l₁ l : PBLine B)
    (hmult : lineMultiplicity (OnLine B) v = 2)
    (hl₀ : OnLine B v l₀) (hl₁ : OnLine B v l₁) (hl : OnLine B v l)
    (h₀₁ : l₀ ≠ l₁) (hl₀ne : l ≠ l₀) : l = l₁ := by
  let S := Finset.univ.filter fun q : PBLine B ↦ OnLine B v q
  have hpair : ({l₀, l₁} : Finset (PBLine B)) ⊆ S := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> simp [S, hl₀, hl₁]
  have hcard : S.card = 2 := hmult
  have hpCard : ({l₀, l₁} : Finset (PBLine B)).card = 2 :=
    Finset.card_pair h₀₁
  have heq : S = {l₀, l₁} := by
    exact Finset.Subset.antisymm
      (Finset.eq_of_subset_of_card_le hpair (by omega) |>.symm.subset) hpair
  have hlmem : l ∈ S := by simp [S, hl]
  rw [heq] at hlmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hlmem
  exact hlmem.resolve_left hl₀ne

private abbrev B {P : Finset Point} := nonordinaryPoints P
private abbrev C {P : Finset Point} {a b d : Point}
    (ha : a ∈ B (P := P)) (hb : b ∈ B (P := P)) (hd : d ∈ B (P := P))
    (hncol : ¬ ProjectiveDuality.Collinear3 a b d) :=
  ConcretePolarCellulation.blueCellulation (B (P := P)) ha hb hd hncol
private abbrev D {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c) {a b d : Point}
    (ha : a ∈ B (P := P)) (hb : b ∈ B (P := P)) (hd : d ∈ B (P := P))
    (hncol : ¬ ProjectiveDuality.Collinear3 a b d) :=
  ConcretePolarABKPRData.concreteData hred ha hb hd hncol
private abbrev hs {P : Finset Point} {a b d : Point}
    (ha : a ∈ B (P := P)) (hb : b ∈ B (P := P)) (hd : d ∈ B (P := P))
    (hncol : ¬ ProjectiveDuality.Collinear3 a b d) :
    Submodule.span ℝ (Set.range (normals (B (P := P)))) = ⊤ :=
  ConcretePolarABKPRData.hspan ha hb hd hncol

section Concrete

variable {P : Finset Point} {w : Point → ℝ} {c : ℝ}
variable (hred : IsReducedMagic P w c)
variable {a b d : Point}
variable (ha : a ∈ B (P := P)) (hb : b ∈ B (P := P))
variable (hd : d ∈ B (P := P))
variable (hncol : ¬ ProjectiveDuality.Collinear3 a b d)
variable [Nonempty (PBLine (B (P := P)))]

private noncomputable def pick : OtherLineChoice (PBLine (B (P := P))) :=
  otherLineChoiceOfPair ⟨a, ha⟩ ⟨b, hb⟩ (by
    intro hab
    apply hncol
    have : a = b := congrArg Subtype.val hab
    subst b
    simp [ProjectiveDuality.Collinear3, ProjectiveDuality.orientationDet])

private theorem boundaryVertex_projective_injective
    (f : StrictFace (normals (B (P := P))))
    {i j : Fin ((C ha hb hd hncol).faceDegree f)}
    (h : ((D hred ha hb hd hncol).boundaryVertex f i).1 =
      ((D hred ha hb hd hncol).boundaryVertex f j).1) : i = j := by
  apply (ConcretePolarABKPRData.indexEquiv
    (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
      (B (P := P)) ha hb hd hncol) ha hb hd hncol f).injective
  have hp := congrArg Subtype.val h
  change PolarBoundaryOrder.boundaryProjectiveVertex f
      (faceWitness_realizes (normals (B (P := P))) f) normal_cross
      (hs ha hb hd hncol)
        ((finRotate _).symm (ConcretePolarABKPRData.indexEquiv
          (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
            (B (P := P)) ha hb hd hncol) ha hb hd hncol f i)) =
    PolarBoundaryOrder.boundaryProjectiveVertex f
      (faceWitness_realizes (normals (B (P := P))) f) normal_cross
      (hs ha hb hd hncol)
        ((finRotate _).symm (ConcretePolarABKPRData.indexEquiv
          (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
            (B (P := P)) ha hb hd hncol) ha hb hd hncol f j)) at hp
  exact (finRotate _).symm.injective
    (PolarBoundaryOrder.boundaryProjectiveVertex_injective f
      (faceWitness_realizes (normals (B (P := P))) f) normal_cross
      (hs ha hb hd hncol) hp)

private structure Continuation
    (t : StrictFace (normals (B (P := P))))
    (third : Fin ((C ha hb hd hncol).faceDegree t))
    (shared : ℙ ℝ SignVector.Vec3) (outer : PBVertex (B (P := P))) where
  red : Point
  red_mem : red ∈ ordinaryPoints P
  x : PBVertex (B (P := P))
  shared_incident : Incident shared red
  x_incident : Incident x.1 red
  x_ne_outer : x ≠ outer
  edge : StrictEdge (normals (B (P := P)))
  edge_line : edge.1.1 =
    ⟨((D hred ha hb hd hncol).boundaryEdge t third).1.1.1,
      ((D hred ha hb hd hncol).boundaryEdge t third).1.1.2⟩
  edge_vertices :
    (concreteEdgeVertices (hs ha hb hd hncol) edge).image Prod.fst = {outer, x}

private noncomputable def bad_side_continuation
    (t : StrictFace (normals (B (P := P))))
    (side outer shared third : Fin ((C ha hb hd hncol).faceDegree t))
    (houter_ne_shared : outer ≠ shared)
    (hsideThird : side ≠ third)
    (houterSide : outer = side ∨
      outer = ABKPR.faceSucc (C ha hb hd hncol) t side)
    (hsharedSide : shared = side ∨
      shared = ABKPR.faceSucc (C ha hb hd hncol) t side)
    (houterThird : outer = third ∨
      outer = ABKPR.faceSucc (C ha hb hd hncol) t third)
    (hbad : (D hred ha hb hd hncol).IsBadTwoQuadrangle
      ((D hred ha hb hd hncol).across ⟨t, side⟩).1)
    (hmult : lineMultiplicity (OnLine (B (P := P)))
      ((D hred ha hb hd hncol).boundaryVertex t outer).1 = 2) :
    Continuation hred ha hb hd hncol t third
      ((D hred ha hb hd hncol).boundaryVertex t shared).1.1
      ((D hred ha hb hd hncol).boundaryVertex t outer).1 := by
  let DD := D hred ha hb hd hncol
  let CC := C ha hb hd hncol
  let dart : ABKPR.FaceDart CC := ⟨t, side⟩
  let g := (DD.across dart).1
  let j := (DD.across dart).2
  have hgdeg : CC.faceDegree g = 4 := hbad.1.1
  have hedge : DD.boundaryEdge t side = DD.boundaryEdge g j :=
    DD.across_sameEdge dart
  have hverts := congrArg CC.edgeVertices hedge
  rw [DD.boundaryEdge_vertices t side, DD.boundaryEdge_vertices g j] at hverts
  have outer_mem : DD.boundaryVertex t outer ∈
      ({DD.boundaryVertex t side,
        DD.boundaryVertex t (ABKPR.faceSucc CC t side)} :
          Finset (OrientedVertex (B (P := P)))) := by
    rcases houterSide with h | h
    · simpa [h]
    · simpa [h, CC]
  have shared_mem : DD.boundaryVertex t shared ∈
      ({DD.boundaryVertex t side,
        DD.boundaryVertex t (ABKPR.faceSucc CC t side)} :
          Finset (OrientedVertex (B (P := P)))) := by
    rcases hsharedSide with h | h
    · simpa [h]
    · simpa [h, CC]
  have outer_mem_g : DD.boundaryVertex t outer ∈
      ({DD.boundaryVertex g j,
        DD.boundaryVertex g (ABKPR.faceSucc CC g j)} :
          Finset (OrientedVertex (B (P := P)))) := by
    rw [← hverts]
    exact outer_mem
  have shared_mem_g : DD.boundaryVertex t shared ∈
      ({DD.boundaryVertex g j,
        DD.boundaryVertex g (ABKPR.faceSucc CC g j)} :
          Finset (OrientedVertex (B (P := P)))) := by
    rw [← hverts]
    exact shared_mem
  have hkoExists : ∃ ko : Fin (CC.faceDegree g),
      DD.boundaryVertex g ko = DD.boundaryVertex t outer ∧
        (ko = j ∨ ko = ABKPR.faceSucc CC g j) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at outer_mem_g
    rcases outer_mem_g with h | h
    · exact ⟨j, h.symm, Or.inl rfl⟩
    · exact ⟨ABKPR.faceSucc CC g j, h.symm, Or.inr rfl⟩
  let ko := Classical.choose hkoExists
  have hko : DD.boundaryVertex g ko = DD.boundaryVertex t outer :=
    (Classical.choose_spec hkoExists).1
  have hkoj : ko = j ∨ ko = ABKPR.faceSucc CC g j :=
    (Classical.choose_spec hkoExists).2
  have hksExists : ∃ ks : Fin (CC.faceDegree g),
      DD.boundaryVertex g ks = DD.boundaryVertex t shared ∧
        (ks = j ∨ ks = ABKPR.faceSucc CC g j) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at shared_mem_g
    rcases shared_mem_g with h | h
    · exact ⟨j, h.symm, Or.inl rfl⟩
    · exact ⟨ABKPR.faceSucc CC g j, h.symm, Or.inr rfl⟩
  let ks := Classical.choose hksExists
  have hks : DD.boundaryVertex g ks = DD.boundaryVertex t shared :=
    (Classical.choose_spec hksExists).1
  have hksj : ks = j ∨ ks = ABKPR.faceSucc CC g j :=
    (Classical.choose_spec hksExists).2
  have hkone : ko ≠ ks := by
    intro h
    apply houter_ne_shared
    apply DD.boundaryVertex_injective t
    rw [← hko, ← hks, h]
  have hkadj : ko = ABKPR.faceSucc CC g ks ∨
      ks = ABKPR.faceSucc CC g ko := by
    rcases hkoj with hko0 | hko1 <;> rcases hksj with hks0 | hks1
    · exact False.elim (hkone (hko0.trans hks0.symm))
    · exact Or.inr (hks1.trans (congrArg (ABKPR.faceSucc CC g) hko0.symm))
    · exact Or.inl (hko1.trans (congrArg (ABKPR.faceSucc CC g) hks0.symm))
    · exact False.elim (hkone (hko1.trans hks1.symm))
  have hksred : ks ∈ DD.redEndpoints g := by
    rw [DD.redEndpoints_eq_univ_of_twoDiagonal hbad.1]
    simp
  have hpExists := (DD.redEndpoint_iff g ks).mp hksred
  let p := Classical.choose hpExists
  have hp : p ∈ DD.redChords g := (Classical.choose_spec hpExists).1
  have hksp : ks = p.1 ∨ ks = p.2 := (Classical.choose_spec hpExists).2
  have hpConcrete : p ∈ ConcretePolarABKPRData.redChords hred
      (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
        (B (P := P)) ha hb hd hncol) ha hb hd hncol g := by
    exact hp
  have hrExists := (ConcretePolarABKPRData.mem_redChords_iff hred
    (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
      (B (P := P)) ha hb hd hncol) ha hb hd hncol g p).mp hpConcrete
  let r := Classical.choose hrExists
  have hrp := Classical.choose_spec hrExists
  let kx : Fin (CC.faceDegree g) := if ks = p.1 then p.2 else p.1
  have hkxp : kx = p.1 ∨ kx = p.2 := by
    dsimp [kx]
    split_ifs with h
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hks_coord : ks = p.1 ∨ ks = p.2 := hksp
  have hkxne : kx ≠ ks := by
    have hpne := DD.redChord_distinct g p hp
    rcases hks_coord with h | h
    · have hkx : kx = p.2 := by simp [kx, h]
      rw [hkx, h]
      exact hpne.symm
    · have hne : ks ≠ p.1 := by simpa [h] using hpne.symm
      have hkx : kx = p.1 := by simp [kx, hne]
      rw [hkx, h]
      exact hpne
  have hnon := DD.redChord_nonadjacent g p hp
  have hkx_not_succ : kx ≠ ABKPR.faceSucc CC g ks := by
    rcases hks_coord with h | h
    · have hkx : kx = p.2 := by simp [kx, h]
      simpa [h, hkx] using hnon.1
    · have hne : ks ≠ p.1 := by
        simpa [h] using (DD.redChord_distinct g p hp).symm
      have hkx : kx = p.1 := by simp [kx, hne]
      simpa [h, hkx] using hnon.2
  have hks_not_succ : ks ≠ ABKPR.faceSucc CC g kx := by
    rcases hks_coord with h | h
    · have hkx : kx = p.2 := by simp [kx, h]
      simpa [h, hkx] using hnon.2
    · have hne : ks ≠ p.1 := by
        simpa [h] using (DD.redChord_distinct g p hp).symm
      have hkx : kx = p.1 := by simp [kx, hne]
      simpa [h, hkx] using hnon.1
  have hkxadj : kx = ABKPR.faceSucc CC g ko ∨
      ko = ABKPR.faceSucc CC g kx := by
    exact other_neighbor_of_degree_four hgdeg ks ko kx hkadj hkxne
      hkx_not_succ hks_not_succ
  have hkxneko : kx ≠ ko := by
    intro hEq
    rcases hkadj with h | h
    · exact hkx_not_succ (hEq.trans h)
    · exact hks_not_succ (h.trans (congrArg (ABKPR.faceSucc CC g) hEq.symm))
  let ell : Fin (CC.faceDegree g) :=
    if kx = ABKPR.faceSucc CC g ko then ko else kx
  have hellpair :
      ({ell, ABKPR.faceSucc CC g ell} : Finset (Fin (CC.faceDegree g))) =
        {ko, kx} := by
    rcases hkxadj with h | h
    · simp [ell, h]
    · have hn : ¬ kx = ABKPR.faceSucc CC g ko := by
        intro hx
        apply hkxneko
        apply Fin.ext
        have hval := congrArg Fin.val h
        have hxval := congrArg Fin.val hx
        simp only [ABKPR.faceSucc, ABKPR.cyclicSucc] at hval hxval
        simp only [hgdeg] at hval hxval
        omega
      simp only [ell, if_neg hn]
      rw [← h]
      exact Finset.pair_comm _ _
  have hkx_mem_endpoint : kx ∈
      ConcretePolarABKPRData.chordEndpoints
        (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
          (B (P := P)) ha hb hd hncol) ha hb hd hncol p := by
    change kx ∈ ({p.1, p.2} : Finset (Fin (CC.faceDegree g)))
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hkxp
  have hks_mem_endpoint : ks ∈
      ConcretePolarABKPRData.chordEndpoints
        (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
          (B (P := P)) ha hb hd hncol) ha hb hd hncol p := by
    change ks ∈ ({p.1, p.2} : Finset (Fin (CC.faceDegree g)))
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hks_coord
  have hkxPolar := (ConcretePolarABKPRData.chordEndpoint_mem_iff hred
    (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
      (B (P := P)) ha hb hd hncol) ha hb hd hncol g r kx).mp (by
        rw [hrp]
        exact hkx_mem_endpoint)
  have hksPolar := (ConcretePolarABKPRData.chordEndpoint_mem_iff hred
    (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
      (B (P := P)) ha hb hd hncol) ha hb hd hncol g r ks).mp (by
        rw [hrp]
        exact hks_mem_endpoint)
  have hxinc : Incident (DD.boundaryVertex g kx).1.1 r.1.1 := by
    exact (Finset.mem_filter.mp hkxPolar).2
  have hsinc : Incident (DD.boundaryVertex g ks).1.1 r.1.1 := by
    exact (Finset.mem_filter.mp hksPolar).2
  have hellne : ell ≠ j := by
    intro heq
    have hksmem : ks ∈
        ({ell, ABKPR.faceSucc CC g ell} : Finset (Fin (CC.faceDegree g))) := by
      rw [heq]
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hksj
    have hksPair : ks ∈ ({ko, kx} : Finset (Fin (CC.faceDegree g))) := by
      rw [← hellpair]
      exact hksmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hksPair
    have hkskx : ks = kx := hksPair.resolve_left (fun h ↦ hkone h.symm)
    exact hkxne hkskx.symm
  let eNew := DD.boundaryEdge g ell
  let eSide := DD.boundaryEdge t side
  let eThird := DD.boundaryEdge t third
  let lNew : PBLine (B (P := P)) := ⟨eNew.1.1.1, eNew.1.1.2⟩
  let lSide : PBLine (B (P := P)) := ⟨eSide.1.1.1, eSide.1.1.2⟩
  let lThird : PBLine (B (P := P)) := ⟨eThird.1.1.1, eThird.1.1.2⟩
  have houterNew : DD.boundaryVertex t outer ∈
      concreteEdgeVertices (hs ha hb hd hncol) eNew := by
    change DD.boundaryVertex t outer ∈ CC.edgeVertices eNew
    rw [DD.boundaryEdge_vertices]
    have hkomem : ko ∈ ({ell, ABKPR.faceSucc CC g ell} :
        Finset (Fin (CC.faceDegree g))) := by rw [hellpair]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hkomem ⊢
    rcases hkomem with h | h
    · left; rw [← h, hko]
    · right; rw [← h, hko]
  have houterSideMem : DD.boundaryVertex t outer ∈
      concreteEdgeVertices (hs ha hb hd hncol) eSide := by
    change DD.boundaryVertex t outer ∈ CC.edgeVertices eSide
    rw [DD.boundaryEdge_vertices]
    rcases houterSide with rfl | rfl <;> simp
  have houterThirdMem : DD.boundaryVertex t outer ∈
      concreteEdgeVertices (hs ha hb hd hncol) eThird := by
    change DD.boundaryVertex t outer ∈ CC.edgeVertices eThird
    rw [DD.boundaryEdge_vertices]
    rcases houterThird with rfl | rfl <;> simp
  have hlNew : OnLine (B (P := P)) (DD.boundaryVertex t outer).1 lNew :=
    concreteEdgeVertex_on_support (hs ha hb hd hncol) eNew _ houterNew
  have hlSide : OnLine (B (P := P)) (DD.boundaryVertex t outer).1 lSide :=
    concreteEdgeVertex_on_support (hs ha hb hd hncol) eSide _ houterSideMem
  have hlThird : OnLine (B (P := P)) (DD.boundaryVertex t outer).1 lThird :=
    concreteEdgeVertex_on_support (hs ha hb hd hncol) eThird _ houterThirdMem
  have hSideThird : lSide ≠ lThird := by
    intro h
    apply hsideThird
    apply (ConcretePolarABKPRData.indexEquiv
      (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
        (B (P := P)) ha hb hd hncol) ha hb hd hncol t).injective
    apply (SignVector.PolarBoundaryOrder.boundaryOwnerEquiv t
      (faceWitness_realizes (normals (B (P := P))) t) normal_cross
      (hs ha hb hd hncol)).injective
    apply Subtype.ext
    exact h
  have hNewSide : lNew ≠ lSide := by
    intro h
    apply hellne
    apply (ConcretePolarABKPRData.indexEquiv
      (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
        (B (P := P)) ha hb hd hncol) ha hb hd hncol g).injective
    apply (SignVector.PolarBoundaryOrder.boundaryOwnerEquiv g
      (faceWitness_realizes (normals (B (P := P))) g) normal_cross
      (hs ha hb hd hncol)).injective
    apply Subtype.ext
    calc
      _ = lSide := h
      _ = _ := by
        apply Subtype.ext
        exact congrArg
          (fun e : StrictEdge (normals (B (P := P))) ↦ e.1.1.1) hedge
  have hline : lNew = lThird :=
    line_eq_of_multiplicity_two (DD.boundaryVertex t outer).1
      lSide lThird lNew hmult hlSide hlThird hlNew hSideThird hNewSide
  refine
    { red := r.1.1
      red_mem := r.1.2
      x := (DD.boundaryVertex g kx).1
      shared_incident := by simpa [hks] using hsinc
      x_incident := hxinc
      x_ne_outer := by
        intro h
        apply hkxneko
        apply boundaryVertex_projective_injective hred ha hb hd hncol g
        rw [hko]
        exact h
      edge := eNew
      edge_line := hline
      edge_vertices := ?_ }
  change (CC.edgeVertices eNew).image Prod.fst = _
  rw [DD.boundaryEdge_vertices]
  simp only [Finset.image_insert, Finset.image_singleton]
  have hpairVertices :
      ({(DD.boundaryVertex g ell).1,
        (DD.boundaryVertex g (ABKPR.faceSucc CC g ell)).1} :
          Finset (PBVertex (B (P := P)))) =
        {(DD.boundaryVertex g ko).1, (DD.boundaryVertex g kx).1} := by
    apply congrArg (fun s : Finset (Fin (CC.faceDegree g)) ↦
      s.image (fun q ↦ (DD.boundaryVertex g q).1)) at hellpair
    simpa using hellpair
  rw [hpairVertices, hko]

private theorem continuation_x_on_third
    (t : StrictFace (normals (B (P := P))))
    (third : Fin ((C ha hb hd hncol).faceDegree t))
    (shared : ℙ ℝ SignVector.Vec3) (outer : PBVertex (B (P := P)))
    (q : Continuation hred ha hb hd hncol t third shared outer) :
    OnLine (B (P := P)) q.x
      ⟨((D hred ha hb hd hncol).boundaryEdge t third).1.1.1,
        ((D hred ha hb hd hncol).boundaryEdge t third).1.1.2⟩ := by
  have hxmem : q.x ∈
      (concreteEdgeVertices (hs ha hb hd hncol) q.edge).image Prod.fst := by
    rw [q.edge_vertices]
    simp
  obtain ⟨v, hv, hvx⟩ := Finset.mem_image.mp hxmem
  have hon := concreteEdgeVertex_on_support (hs ha hb hd hncol) q.edge v hv
  rw [← q.edge_line]
  simpa only [OnLine, hvx] using hon

/-- Two bad neighbours of a literal polar triangle force the failed-Fano
configuration.  This is the concrete recognition theorem for the
`Stage3LocalObstruction.triangleTwoBad` constructor. -/
theorem isFailedFano_of_triangleTwoBad
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (t : StrictFace (normals (B (P := P))))
    (ht : (C ha hb hd hncol).faceDegree t = 3)
    (i j : Fin ((C ha hb hd hncol).faceDegree t)) (hij : i ≠ j)
    (hi : i ∈ (D hred ha hb hd hncol).badNeighborIndices t)
    (hj : j ∈ (D hred ha hb hd hncol).badNeighborIndices t) :
    IsFailedFano P := by
  let CC := C ha hb hd hncol
  let DD := D hred ha hb hd hncol
  have hadj : j = ABKPR.faceSucc CC t i ∨
      i = ABKPR.faceSucc CC t j := by
    simpa only [ABKPR.faceSucc] using
      fin_three_distinct_are_cyclic_neighbors ht i j hij
  have canonical : ∀ i : Fin (CC.faceDegree t),
      i ∈ DD.badNeighborIndices t →
      ABKPR.faceSucc CC t i ∈ DD.badNeighborIndices t →
      IsFailedFano P := by
    intro i hi hj
    let s : Fin (CC.faceDegree t) := ABKPR.faceSucc CC t i
    let k : Fin (CC.faceDegree t) := ABKPR.faceSucc CC t s
    have his : i ≠ s := by
      intro h
      have hval := congrArg Fin.val h
      simp only [s, ABKPR.faceSucc, ABKPR.cyclicSucc] at hval
      simp only [CC, ht] at hval
      omega
    have hsk : s ≠ k := by
      intro h
      have hval := congrArg Fin.val h
      simp only [s, k, ABKPR.faceSucc, ABKPR.cyclicSucc] at hval
      simp only [CC, ht] at hval
      omega
    have hik : i ≠ k := by
      intro h
      have hval := congrArg Fin.val h
      simp only [s, k, ABKPR.faceSucc, ABKPR.cyclicSucc] at hval
      simp only [CC, ht] at hval
      omega
    have hcycle : ABKPR.faceSucc CC t k = i := by
      apply Fin.ext
      simp only [s, k, ABKPR.faceSucc, ABKPR.cyclicSucc, Fin.ext_iff]
      simp only [CC, ht]
      omega
    have hbadI : DD.IsBadTwoQuadrangle (DD.across ⟨t, i⟩).1 :=
      (Finset.mem_filter.mp hi).2
    have hbadS : DD.IsBadTwoQuadrangle (DD.across ⟨t, s⟩).1 := by
      exact (Finset.mem_filter.mp hj).2
    have hmultI := ConcreteStage3Local.triangle_boundary_lineMultiplicity_eq_two
      hred ha hb hd hncol t ht i s his hi hj i
    have hmultK := ConcreteStage3Local.triangle_boundary_lineMultiplicity_eq_two
      hred ha hb hd hncol t ht i s his hi hj k
    let qI := bad_side_continuation hred ha hb hd hncol t i i s k
      his hik (Or.inl rfl) (Or.inr rfl) (Or.inr hcycle.symm) hbadI hmultI
    let qK := bad_side_continuation hred ha hb hd hncol t s k s k
      hsk.symm hsk (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) hbadS hmultK
    have hredEq : qI.red = qK.red := by
      by_contra hne
      exact RedChordIncidence.no_common_blueVertex_of_distinct_red hred
        qI.red_mem qK.red_mem hne (DD.boundaryVertex t s).1
        qI.shared_incident qK.shared_incident
    have hxI := continuation_x_on_third hred ha hb hd hncol t k
      (DD.boundaryVertex t s).1.1 (DD.boundaryVertex t i).1 qI
    have hxK := continuation_x_on_third hred ha hb hd hncol t k
      (DD.boundaryVertex t s).1.1 (DD.boundaryVertex t k).1 qK
    have hredBlue : qI.red ≠ (DD.boundaryEdge t k).1.1.1 :=
      RedChordIncidence.red_ne_blue qI.red_mem (DD.boundaryEdge t k).1.1.2
    have hxEqVal : qI.x.1 = qK.x.1 := by
      apply ProjectiveArrangement.eq_of_two_common_lines hredBlue
      · exact qI.x_incident
      · exact hxI
      · rw [hredEq]
        exact qK.x_incident
      · exact hxK
    have hxEq : qI.x = qK.x := Subtype.ext hxEqVal
    let vI : PBVertex (B (P := P)) := (DD.boundaryVertex t i).1
    let vK : PBVertex (B (P := P)) := (DD.boundaryVertex t k).1
    have hvIvK : vI ≠ vK := by
      intro h
      apply hik
      exact boundaryVertex_projective_injective hred ha hb hd hncol t h
    have hvIx : vI ≠ qI.x := fun h ↦ qI.x_ne_outer h.symm
    have hvKx : vK ≠ qI.x := by
      intro h
      apply qK.x_ne_outer
      rw [← hxEq]
      exact h.symm
    let eIK := DD.boundaryEdge t k
    let owner : PBLine (B (P := P)) := ⟨eIK.1.1.1, eIK.1.1.2⟩
    have hpairIK :
        (concreteEdgeVertices (hs ha hb hd hncol) eIK).image Prod.fst =
          {vI, vK} := by
      change (CC.edgeVertices eIK).image Prod.fst = _
      rw [DD.boundaryEdge_vertices]
      simp only [Finset.image_insert, Finset.image_singleton]
      rw [hcycle]
      exact Finset.pair_comm _ _
    have hpairKx :
        (concreteEdgeVertices (hs ha hb hd hncol) qK.edge).image Prod.fst =
          {vK, qI.x} := by
      rw [qK.edge_vertices, hxEq]
    have hpairxI :
        (concreteEdgeVertices (hs ha hb hd hncol) qI.edge).image Prod.fst =
          {qI.x, vI} := by
      rw [qI.edge_vertices]
      exact Finset.pair_comm _ _
    exact ConcretePolarRecognition.isFailedFano_of_three_literal_edges_two_double
      hred hAcard ha hb hd hncol (pick ha hb hncol)
      owner vI vK qI.x hvIvK hvIx hvKx eIK qK.edge qI.edge
      rfl qK.edge_line qI.edge_line hpairIK hpairKx hpairxI hmultI hmultK
  rcases hadj with hji | hij'
  · apply canonical i hi
    simpa only [hji] using hj
  · apply canonical j hj
    simpa only [hij'] using hi

end Concrete

end Erdos735.TriangleExceptionCardinality
