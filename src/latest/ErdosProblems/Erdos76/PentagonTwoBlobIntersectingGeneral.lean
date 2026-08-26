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
import ErdosProblems.Erdos76.PentagonTwoBlobIntersectingCanonical
import ErdosProblems.Erdos76.PentagonTwoBlobExceptionalGeneral

/-!
# The arbitrary-blob form of Proposition 7.2(c)

We label the common endpoint and the two opposite endpoints of the missing
cross edges, transport one of the four checked finite certificates, and
extend the resulting packing from the induced two-blob graph to the ambient
graph.
-/

open Finset

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {alpha : Type*} [Fintype alpha] [DecidableEq alpha]

/-- A labeling of two blobs which sends the common missing-edge endpoint and
the two opposite endpoints to three prescribed canonical vertices. -/
structure Proposition72cLabeling
    (A B : Finset alpha) (x : A) (y z : B)
    (nA nB : Nat) (a0 : Fin nA) (b0 b1 : Fin nB) where
  leftEquiv : A ≃ Fin nA
  rightEquiv : B ≃ Fin nB
  left_apply : leftEquiv x = a0
  right_first : rightEquiv y = b0
  right_second : rightEquiv z = b1

theorem exists_proposition72cLabeling
    {A B : Finset alpha} {x : A} {y z : B} {nA nB : Nat}
    {a0 : Fin nA} {b0 b1 : Fin nB}
    (hAcard : A.card = nA) (hBcard : B.card = nB)
    (hyz : y ≠ z) (hb : b0 ≠ b1) :
    Nonempty (Proposition72cLabeling A B x y z nA nB a0 b0 b1) := by
  classical
  let eA0 : A ≃ Fin nA := Fintype.equivFinOfCardEq (by simpa using hAcard)
  let eB0 : B ≃ Fin nB := Fintype.equivFinOfCardEq (by simpa using hBcard)
  let sourceA : Unit → Fin nA := fun _ ↦ eA0 x
  let targetA : Unit → Fin nA := fun _ ↦ a0
  have hsourceA : Function.Injective sourceA := by
    intro i j _
    cases i
    cases j
    rfl
  have htargetA : Function.Injective targetA := by
    intro i j _
    cases i
    cases j
    rfl
  obtain ⟨sigmaA, hsigmaA⟩ := Equiv.Perm.exists_extending_pair
    sourceA targetA hsourceA htargetA
  let sourceB : Bool → Fin nB := fun i ↦ if i then eB0 z else eB0 y
  let targetB : Bool → Fin nB := fun i ↦ if i then b1 else b0
  have hsourceB : Function.Injective sourceB := by
    intro i j
    cases i <;> cases j <;> simp [sourceB, hyz, hyz.symm]
  have htargetB : Function.Injective targetB := by
    intro i j
    cases i <;> cases j <;> simp [targetB, hb, hb.symm]
  obtain ⟨sigmaB, hsigmaB⟩ := Equiv.Perm.exists_extending_pair
    sourceB targetB hsourceB htargetB
  let eA : A ≃ Fin nA := eA0.trans sigmaA
  let eB : B ≃ Fin nB := eB0.trans sigmaB
  refine ⟨⟨eA, eB, ?_, ?_, ?_⟩⟩
  · exact hsigmaA ()
  · exact hsigmaB false
  · exact hsigmaB true

/-- The standard first block in `Fin (nA+nB)`. -/
def proposition72cCanonicalSide (nA nB : Nat) : Finset (Fin (nA + nB)) :=
  univ.map (Fin.castAddEmb nB)

/-- The two canonical missing cross edges with a common first-block
endpoint. -/
def proposition72cCanonicalMissing
    {nA nB : Nat} (a0 : Fin nA) (b0 b1 : Fin nB) :
    Finset (Sym2 (Fin (nA + nB))) :=
  {s(Fin.castAdd nB a0, Fin.natAdd nA b0),
    s(Fin.castAdd nB a0, Fin.natAdd nA b1)}

def proposition72cUnionEquiv
    {A B : Finset alpha} {x : A} {y z : B} {nA nB : Nat}
    {a0 : Fin nA} {b0 b1 : Fin nB}
    (L : Proposition72cLabeling A B x y z nA nB a0 b0 b1)
    (hAB : Disjoint A B) :
    (A ∪ B : Finset alpha) ≃ Fin (nA + nB) :=
  (Equiv.Finset.union A B hAB).symm |>.trans
    ((L.leftEquiv.sumCongr L.rightEquiv).trans finSumFinEquiv)

@[simp] lemma proposition72cUnionEquiv_apply_left
    {A B : Finset alpha} {x : A} {y z : B} {nA nB : Nat}
    {a0 : Fin nA} {b0 b1 : Fin nB}
    (L : Proposition72cLabeling A B x y z nA nB a0 b0 b1)
    (hAB : Disjoint A B) (a : A) :
    proposition72cUnionEquiv L hAB ⟨a.1, mem_union_left B a.2⟩ =
      Fin.castAdd nB (L.leftEquiv a) := by
  simp [proposition72cUnionEquiv]

@[simp] lemma proposition72cUnionEquiv_apply_right
    {A B : Finset alpha} {x : A} {y z : B} {nA nB : Nat}
    {a0 : Fin nA} {b0 b1 : Fin nB}
    (L : Proposition72cLabeling A B x y z nA nB a0 b0 b1)
    (hAB : Disjoint A B) (b : B) :
    proposition72cUnionEquiv L hAB ⟨b.1, mem_union_right A b.2⟩ =
      Fin.natAdd nA (L.rightEquiv b) := by
  simp [proposition72cUnionEquiv]

lemma proposition72cUnionEquiv_mem_side_iff
    {A B : Finset alpha} {x : A} {y z : B} {nA nB : Nat}
    {a0 : Fin nA} {b0 b1 : Fin nB}
    (L : Proposition72cLabeling A B x y z nA nB a0 b0 b1)
    (hAB : Disjoint A B) (u : (A ∪ B : Finset alpha)) :
    proposition72cUnionEquiv L hAB u ∈ proposition72cCanonicalSide nA nB ↔
      u.1 ∈ A := by
  classical
  by_cases huA : u.1 ∈ A
  · let a : A := ⟨u.1, huA⟩
    have hu : u = ⟨a.1, mem_union_left B a.2⟩ := Subtype.ext rfl
    constructor
    · exact fun _ ↦ huA
    · intro _
      rw [hu, proposition72cUnionEquiv_apply_left]
      simp [proposition72cCanonicalSide]
  · have huB : u.1 ∈ B := (mem_union.mp u.2).resolve_left huA
    let b : B := ⟨u.1, huB⟩
    have hu : u = ⟨b.1, mem_union_right A b.2⟩ := Subtype.ext rfl
    constructor
    · intro hmem
      rw [hu, proposition72cUnionEquiv_apply_right] at hmem
      rcases mem_map.mp hmem with ⟨i, _hi, heq⟩
      have hneq : Fin.castAdd nB i ≠ Fin.natAdd nA (L.rightEquiv b) := by
        intro h
        have hval := congrArg Fin.val h
        have hi := i.isLt
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
        omega
      exact (hneq heq).elim
    · exact fun h ↦ (huA h).elim

lemma proposition72cUnionEquiv_image_side
    {A B : Finset alpha} {x : A} {y z : B} {nA nB : Nat}
    {a0 : Fin nA} {b0 b1 : Fin nB}
    (L : Proposition72cLabeling A B x y z nA nB a0 b0 b1)
    (hAB : Disjoint A B) :
    proposition72cUnionEquiv L hAB ''
        {u : (A ∪ B : Finset alpha) | u.1 ∈ A} =
      (proposition72cCanonicalSide nA nB : Set (Fin (nA + nB))) := by
  ext v
  constructor
  · rintro ⟨u, huA, rfl⟩
    exact (proposition72cUnionEquiv_mem_side_iff L hAB u).mpr huA
  · intro hv
    let u := (proposition72cUnionEquiv L hAB).symm v
    refine ⟨u, ?_, (proposition72cUnionEquiv L hAB).apply_symm_apply v⟩
    apply (proposition72cUnionEquiv_mem_side_iff L hAB u).mp
    simpa [u] using hv

lemma proposition72cUnionEquiv_map_missing
    {A B : Finset alpha} {x : A} {y z : B} {nA nB : Nat}
    {a0 : Fin nA} {b0 b1 : Fin nB}
    (L : Proposition72cLabeling A B x y z nA nB a0 b0 b1)
    (hAB : Disjoint A B) :
    ({s((⟨x.1, mem_union_left B x.2⟩ : (A ∪ B : Finset alpha)),
        (⟨y.1, mem_union_right A y.2⟩ : (A ∪ B : Finset alpha))),
      s((⟨x.1, mem_union_left B x.2⟩ : (A ∪ B : Finset alpha)),
        (⟨z.1, mem_union_right A z.2⟩ : (A ∪ B : Finset alpha)))} :
        Finset (Sym2 (A ∪ B : Finset alpha))).map
        (proposition72cUnionEquiv L hAB).toEmbedding.sym2Map =
      proposition72cCanonicalMissing a0 b0 b1 := by
  classical
  rw [map_insert, map_singleton]
  change
    {s(proposition72cUnionEquiv L hAB
          ⟨x.1, mem_union_left B x.2⟩,
        proposition72cUnionEquiv L hAB
          ⟨y.1, mem_union_right A y.2⟩),
      s(proposition72cUnionEquiv L hAB
          ⟨x.1, mem_union_left B x.2⟩,
        proposition72cUnionEquiv L hAB
          ⟨z.1, mem_union_right A z.2⟩)} = _
  rw [proposition72cUnionEquiv_apply_left,
    proposition72cUnionEquiv_apply_right,
    proposition72cUnionEquiv_apply_right,
    L.left_apply, L.right_first, L.right_second]
  rfl

private lemma sym2Map_mem_map_iff
    {beta : Type*} [DecidableEq beta] (e : alpha ≃ beta)
    (p : Sym2 alpha) (M : Finset (Sym2 alpha)) :
    e.toEmbedding.sym2Map p ∈ M.map e.toEmbedding.sym2Map ↔ p ∈ M := by
  constructor
  · intro hp
    obtain ⟨q, hq, hqp⟩ := mem_map.mp hp
    have : q = p := e.toEmbedding.sym2Map.injective hqp
    simpa only [this] using hq
  · exact fun hp ↦ mem_map.mpr ⟨p, hp, rfl⟩

/-- After the distinguished vertices are labeled, the induced graph has the
same cross edges as the corresponding canonical two-edge-deletion graph. -/
lemma proposition72cInducedMap_sameCross
    {A B : Finset alpha} {x : A} {y z : B} {nA nB : Nat}
    {a0 : Fin nA} {b0 b1 : Fin nB}
    (L : Proposition72cLabeling A B x y z nA nB a0 b0 b1)
    (hAB : Disjoint A B)
    (G : SimpleGraph alpha)
    (hcross : ∀ a ∈ A, ∀ b ∈ B,
      G.Adj a b ↔ s(a, b) ∉ ({s(x.1, y.1), s(x.1, z.1)} : Finset (Sym2 alpha))) :
    SameCrossAdj
      ((G.induce ((A ∪ B : Finset alpha) : Set alpha)).map
        (proposition72cUnionEquiv L hAB).toEmbedding)
      ((⊤ : SimpleGraph (Fin (nA + nB))).deleteEdges
        ((({s((⟨x.1, mem_union_left B x.2⟩ : (A ∪ B : Finset alpha)),
              (⟨y.1, mem_union_right A y.2⟩ : (A ∪ B : Finset alpha))),
            s((⟨x.1, mem_union_left B x.2⟩ : (A ∪ B : Finset alpha)),
              (⟨z.1, mem_union_right A z.2⟩ : (A ∪ B : Finset alpha)))} :
              Finset (Sym2 (A ∪ B : Finset alpha))).map
          (proposition72cUnionEquiv L hAB).toEmbedding.sym2Map :
            Finset (Sym2 (Fin (nA + nB)))) : Set (Sym2 (Fin (nA + nB)))))
      (proposition72cCanonicalSide nA nB : Set (Fin (nA + nB))) := by
  classical
  let S := A ∪ B
  let e := proposition72cUnionEquiv L hAB
  let xS : S := ⟨x.1, mem_union_left B x.2⟩
  let yS : S := ⟨y.1, mem_union_right A y.2⟩
  let zS : S := ⟨z.1, mem_union_right A z.2⟩
  let M : Finset (Sym2 S) := {s(xS, yS), s(xS, zS)}
  let M0 : Finset (Sym2 alpha) := {s(x.1, y.1), s(x.1, z.1)}
  intro u v huv
  let p : S := e.symm u
  let q : S := e.symm v
  have huSide : u ∈ proposition72cCanonicalSide nA nB ↔ p.1 ∈ A := by
    have hp := proposition72cUnionEquiv_mem_side_iff L hAB p
    simpa only [e, p, e.apply_symm_apply] using hp
  have hvSide : v ∈ proposition72cCanonicalSide nA nB ↔ q.1 ∈ A := by
    have hq := proposition72cUnionEquiv_mem_side_iff L hAB q
    simpa only [e, q, e.apply_symm_apply] using hq
  have hpqSide : ¬(p.1 ∈ A ↔ q.1 ∈ A) := by
    intro h
    exact huv (huSide.trans (h.trans hvSide.symm))
  have huvNe : u ≠ v := by
    intro huvEq
    apply huv
    rw [huvEq]
  have hCanonical :
      ((⊤ : SimpleGraph (Fin (nA + nB))).deleteEdges
        ((M.map e.toEmbedding.sym2Map : Finset (Sym2 (Fin (nA + nB)))) :
          Set (Sym2 (Fin (nA + nB))))).Adj u v ↔
        s(u, v) ∉ M.map e.toEmbedding.sym2Map := by
    simp [huvNe]
  by_cases hpA : p.1 ∈ A
  · have hqA : q.1 ∉ A := fun hqA ↦ hpqSide ⟨fun _ ↦ hqA, fun _ ↦ hpA⟩
    have hqB : q.1 ∈ B := (mem_union.mp q.2).resolve_left hqA
    let a : A := ⟨p.1, hpA⟩
    let b : B := ⟨q.1, hqB⟩
    have hpEq : p = ⟨a.1, mem_union_left B a.2⟩ := Subtype.ext rfl
    have hqEq : q = ⟨b.1, mem_union_right A b.2⟩ := Subtype.ext rfl
    have hMapAdj :
        ((G.induce ((S : Finset alpha) : Set alpha)).map e.toEmbedding).Adj u v ↔
          G.Adj a.1 b.1 := by
      rw [← e.apply_symm_apply u, ← e.apply_symm_apply v]
      change ((G.induce ((S : Finset alpha) : Set alpha)).map e.toEmbedding).Adj
        (e p) (e q) ↔ G.Adj a.1 b.1
      calc
        _ ↔ (G.induce ((S : Finset alpha) : Set alpha)).Adj p q :=
          SimpleGraph.map_adj_apply
        _ ↔ G.Adj p.1 q.1 := SimpleGraph.induce_adj
        _ ↔ G.Adj a.1 b.1 := by simpa only [p, q, hpEq, hqEq]
    have hMissing : s(a.1, b.1) ∈ M0 ↔
        s(u, v) ∈ M.map e.toEmbedding.sym2Map := by
      calc
        s(a.1, b.1) ∈ M0 ↔
            s((⟨a.1, mem_union_left B a.2⟩ : S),
              (⟨b.1, mem_union_right A b.2⟩ : S)) ∈ M := by
                simp [M0, M, xS, yS, zS, Sym2.eq_iff]
        _ ↔ e.toEmbedding.sym2Map
              s((⟨a.1, mem_union_left B a.2⟩ : S),
                (⟨b.1, mem_union_right A b.2⟩ : S)) ∈
              M.map e.toEmbedding.sym2Map :=
            (sym2Map_mem_map_iff e _ M).symm
        _ ↔ s(u, v) ∈ M.map e.toEmbedding.sym2Map := by
          have heu : e (⟨a.1, mem_union_left B a.2⟩ : S) = u := by
            rw [← hpEq]
            exact e.apply_symm_apply u
          have hev : e (⟨b.1, mem_union_right A b.2⟩ : S) = v := by
            rw [← hqEq]
            exact e.apply_symm_apply v
          change s(e (⟨a.1, mem_union_left B a.2⟩ : S),
            e (⟨b.1, mem_union_right A b.2⟩ : S)) ∈ _ ↔ _
          rw [heu, hev]
    exact hMapAdj.trans ((hcross a.1 a.2 b.1 b.2).trans
      ((not_congr hMissing).trans hCanonical.symm))
  · have hqA : q.1 ∈ A := by
      by_contra hqA
      exact hpqSide ⟨fun h ↦ (hpA h).elim, fun h ↦ (hqA h).elim⟩
    have hpB : p.1 ∈ B := (mem_union.mp p.2).resolve_left hpA
    let a : A := ⟨q.1, hqA⟩
    let b : B := ⟨p.1, hpB⟩
    have hpEq : p = ⟨b.1, mem_union_right A b.2⟩ := Subtype.ext rfl
    have hqEq : q = ⟨a.1, mem_union_left B a.2⟩ := Subtype.ext rfl
    have hMapAdj :
        ((G.induce ((S : Finset alpha) : Set alpha)).map e.toEmbedding).Adj u v ↔
          G.Adj a.1 b.1 := by
      rw [← e.apply_symm_apply u, ← e.apply_symm_apply v]
      change ((G.induce ((S : Finset alpha) : Set alpha)).map e.toEmbedding).Adj
        (e p) (e q) ↔ G.Adj a.1 b.1
      calc
        _ ↔ (G.induce ((S : Finset alpha) : Set alpha)).Adj p q :=
          SimpleGraph.map_adj_apply
        _ ↔ G.Adj p.1 q.1 := SimpleGraph.induce_adj
        _ ↔ G.Adj a.1 b.1 := by
          simpa only [p, q, hpEq, hqEq] using G.adj_comm b.1 a.1
    have hMissing : s(a.1, b.1) ∈ M0 ↔
        s(u, v) ∈ M.map e.toEmbedding.sym2Map := by
      calc
        s(a.1, b.1) ∈ M0 ↔
            s((⟨a.1, mem_union_left B a.2⟩ : S),
              (⟨b.1, mem_union_right A b.2⟩ : S)) ∈ M := by
                simp [M0, M, xS, yS, zS, Sym2.eq_iff]
        _ ↔ e.toEmbedding.sym2Map
              s((⟨a.1, mem_union_left B a.2⟩ : S),
                (⟨b.1, mem_union_right A b.2⟩ : S)) ∈
              M.map e.toEmbedding.sym2Map :=
            (sym2Map_mem_map_iff e _ M).symm
        _ ↔ s(u, v) ∈ M.map e.toEmbedding.sym2Map := by
          have hev : e (⟨a.1, mem_union_left B a.2⟩ : S) = v := by
            rw [← hqEq]
            exact e.apply_symm_apply v
          have heu : e (⟨b.1, mem_union_right A b.2⟩ : S) = u := by
            rw [← hpEq]
            exact e.apply_symm_apply u
          change s(e (⟨a.1, mem_union_left B a.2⟩ : S),
            e (⟨b.1, mem_union_right A b.2⟩ : S)) ∈ _ ↔ _
          rw [hev, heu]
          exact Iff.intro (fun h ↦ by simpa only [Sym2.eq_swap] using h)
            (fun h ↦ by simpa only [Sym2.eq_swap] using h)
    exact hMapAdj.trans ((hcross a.1 a.2 b.1 b.2).trans
      ((not_congr hMissing).trans hCanonical.symm))

private theorem exists_packing_of_mapped_exact
    {beta : Type*} [Fintype beta] [DecidableEq beta]
    {G : SimpleGraph alpha} {side : Set alpha} (e : alpha ≃ beta)
    {canonicalSide : Set beta} {u : Finset beta → Real}
    (hside : e '' side = canonicalSide)
    (hu : IsFractionalInternalCrossPacking
      (G.map e.toEmbedding) canonicalSide u)
    (hsize : fractionalSize (G.map e.toEmbedding) u =
      ((internalEdgeFinset (G.map e.toEmbedding) canonicalSide).card : Real) / 2) :
    ∃ w : Finset alpha → Real,
      IsFractionalInternalCrossPacking G side w ∧
        fractionalSize G w = ((internalEdgeFinset G side).card : Real) / 2 := by
  classical
  let K := G.map e.toEmbedding
  let w := relabelWeight e.symm u
  have hmap : K.map e.symm.toEmbedding = G := by
    dsimp only [K]
    rw [SimpleGraph.map_map]
    simpa using G.map_id
  have hsideBack : e.symm '' canonicalSide = side := by
    rw [← hside]
    ext v
    simp
  have hw : IsFractionalInternalCrossPacking G side w := by
    have hrel := hu.relabel e.symm
    simpa only [w, K, hmap, hsideBack] using hrel
  refine ⟨w, hw, ?_⟩
  have hsizeRel : fractionalSize G w = fractionalSize K u := by
    simpa only [w, hmap] using fractionalSize_relabel K e.symm u
  have hIE := internalEdgeFinset_map_equiv G side e
  change internalEdgeFinset K (e '' side) =
    (internalEdgeFinset G side).map e.toEmbedding.sym2Map at hIE
  rw [hside] at hIE
  have hcard := congrArg Finset.card hIE
  simp only [card_map] at hcard
  rw [hsizeRel, hsize, hcard]

theorem proposition72cInducedPacking_of_certificate
    {A B : Finset alpha} {x : A} {y z : B} {nA nB : Nat}
    {a0 : Fin nA} {b0 b1 : Fin nB}
    (hAB : Disjoint A B) (hAcard : A.card = nA) (hBcard : B.card = nB)
    (hyz : y ≠ z) (hb : b0 ≠ b1)
    (C : Finset (Fin (nA + nB)))
    (Missing : Finset (Sym2 (Fin (nA + nB))))
    (hC : proposition72cCanonicalSide nA nB = C)
    (hMissing : proposition72cCanonicalMissing a0 b0 b1 = Missing)
    (hcertificate : ∀ K : SimpleGraph (Fin (nA + nB)),
      SameCrossAdj K
        ((⊤ : SimpleGraph (Fin (nA + nB))).deleteEdges
          (Missing : Set (Sym2 (Fin (nA + nB))))) (C : Set (Fin (nA + nB))) →
      ∃ u : Finset (Fin (nA + nB)) → Real,
        IsFractionalInternalCrossPacking K (C : Set (Fin (nA + nB))) u ∧
          fractionalSize K u =
            ((internalEdgeFinset K (C : Set (Fin (nA + nB)))).card : Real) / 2)
    (G : SimpleGraph alpha)
    (hcross : ∀ a ∈ A, ∀ b ∈ B,
      G.Adj a b ↔ s(a, b) ∉ ({s(x.1, y.1), s(x.1, z.1)} : Finset (Sym2 alpha))) :
    ∃ w : Finset (A ∪ B : Finset alpha) → Real,
      IsFractionalInternalCrossPacking
          (G.induce ((A ∪ B : Finset alpha) : Set alpha))
          {v : (A ∪ B : Finset alpha) | v.1 ∈ A} w ∧
        fractionalSize (G.induce ((A ∪ B : Finset alpha) : Set alpha)) w =
          ((internalEdgeFinset
            (G.induce ((A ∪ B : Finset alpha) : Set alpha))
            {v : (A ∪ B : Finset alpha) | v.1 ∈ A}).card : Real) / 2 := by
  classical
  let L : Proposition72cLabeling A B x y z nA nB a0 b0 b1 :=
    Classical.choice (exists_proposition72cLabeling
      (x := x) (y := y) (z := z) (a0 := a0) (b0 := b0) (b1 := b1)
      hAcard hBcard hyz hb)
  let e := proposition72cUnionEquiv L hAB
  let H := G.induce ((A ∪ B : Finset alpha) : Set alpha)
  have hside : e '' {v : (A ∪ B : Finset alpha) | v.1 ∈ A} =
      (C : Set (Fin (nA + nB))) := by
    rw [proposition72cUnionEquiv_image_side L hAB, hC]
  have hmapMissing :
      ({s((⟨x.1, mem_union_left B x.2⟩ : (A ∪ B : Finset alpha)),
          (⟨y.1, mem_union_right A y.2⟩ : (A ∪ B : Finset alpha))),
        s((⟨x.1, mem_union_left B x.2⟩ : (A ∪ B : Finset alpha)),
          (⟨z.1, mem_union_right A z.2⟩ : (A ∪ B : Finset alpha)))} :
          Finset (Sym2 (A ∪ B : Finset alpha))).map
          e.toEmbedding.sym2Map = Missing := by
    rw [proposition72cUnionEquiv_map_missing L hAB, hMissing]
  have hsame : SameCrossAdj (H.map e.toEmbedding)
      ((⊤ : SimpleGraph (Fin (nA + nB))).deleteEdges
        (Missing : Set (Sym2 (Fin (nA + nB)))))
      (C : Set (Fin (nA + nB))) := by
    have h := proposition72cInducedMap_sameCross L hAB G hcross
    simpa only [H, e, hmapMissing, hC] using h
  obtain ⟨u, hu, hsize⟩ := hcertificate (H.map e.toEmbedding) hsame
  exact exists_packing_of_mapped_exact e hside hu hsize

private theorem proposition72c33InducedPacking
    {G : SimpleGraph alpha} {A B : Finset alpha} {x : A} {y z : B}
    (hAB : Disjoint A B) (hAcard : A.card = 3) (hBcard : B.card = 3)
    (hyz : y ≠ z)
    (hcross : ∀ a ∈ A, ∀ b ∈ B,
      G.Adj a b ↔ s(a, b) ∉ ({s(x.1, y.1), s(x.1, z.1)} : Finset (Sym2 alpha))) :
    ∃ w : Finset (A ∪ B : Finset alpha) → Real,
      IsFractionalInternalCrossPacking
          (G.induce ((A ∪ B : Finset alpha) : Set alpha))
          {v : (A ∪ B : Finset alpha) | v.1 ∈ A} w ∧
        fractionalSize (G.induce ((A ∪ B : Finset alpha) : Set alpha)) w =
          ((internalEdgeFinset
            (G.induce ((A ∪ B : Finset alpha) : Set alpha))
            {v : (A ∪ B : Finset alpha) | v.1 ∈ A}).card : Real) / 2 := by
  apply proposition72cInducedPacking_of_certificate
    (x := x) (y := y) (z := z)
    (a0 := (0 : Fin 3)) (b0 := (0 : Fin 3)) (b1 := (1 : Fin 3))
    hAB hAcard hBcard hyz
    (show (0 : Fin 3) ≠ 1 by decide)
    proposition72c33A proposition72c33Missing
  · decide
  · decide
  · intro K hK
    exact ⟨zeroExtendTriangleWeight K proposition72c33Weight,
      proposition72c33CanonicalPacking_arbitraryInternal (by
        simpa [proposition72c33Graph] using hK)⟩
  · exact hcross

private theorem proposition72c34InducedPacking
    {G : SimpleGraph alpha} {A B : Finset alpha} {x : A} {y z : B}
    (hAB : Disjoint A B) (hAcard : A.card = 3) (hBcard : B.card = 4)
    (hyz : y ≠ z)
    (hcross : ∀ a ∈ A, ∀ b ∈ B,
      G.Adj a b ↔ s(a, b) ∉ ({s(x.1, y.1), s(x.1, z.1)} : Finset (Sym2 alpha))) :
    ∃ w : Finset (A ∪ B : Finset alpha) → Real,
      IsFractionalInternalCrossPacking
          (G.induce ((A ∪ B : Finset alpha) : Set alpha))
          {v : (A ∪ B : Finset alpha) | v.1 ∈ A} w ∧
        fractionalSize (G.induce ((A ∪ B : Finset alpha) : Set alpha)) w =
          ((internalEdgeFinset
            (G.induce ((A ∪ B : Finset alpha) : Set alpha))
            {v : (A ∪ B : Finset alpha) | v.1 ∈ A}).card : Real) / 2 := by
  apply proposition72cInducedPacking_of_certificate
    (x := x) (y := y) (z := z)
    (a0 := (0 : Fin 3)) (b0 := (0 : Fin 4)) (b1 := (1 : Fin 4))
    hAB hAcard hBcard hyz
    (show (0 : Fin 4) ≠ 1 by decide)
    proposition72c34A proposition72c34Missing
  · decide
  · decide
  · intro K hK
    exact ⟨zeroExtendTriangleWeight K proposition72c34Weight,
      proposition72c34CanonicalPacking_arbitraryInternal (by
        simpa [proposition72c34Graph] using hK)⟩
  · exact hcross

private theorem proposition72c44InducedPacking
    {G : SimpleGraph alpha} {A B : Finset alpha} {x : A} {y z : B}
    (hAB : Disjoint A B) (hAcard : A.card = 4) (hBcard : B.card = 4)
    (hyz : y ≠ z)
    (hcross : ∀ a ∈ A, ∀ b ∈ B,
      G.Adj a b ↔ s(a, b) ∉ ({s(x.1, y.1), s(x.1, z.1)} : Finset (Sym2 alpha))) :
    ∃ w : Finset (A ∪ B : Finset alpha) → Real,
      IsFractionalInternalCrossPacking
          (G.induce ((A ∪ B : Finset alpha) : Set alpha))
          {v : (A ∪ B : Finset alpha) | v.1 ∈ A} w ∧
        fractionalSize (G.induce ((A ∪ B : Finset alpha) : Set alpha)) w =
          ((internalEdgeFinset
            (G.induce ((A ∪ B : Finset alpha) : Set alpha))
            {v : (A ∪ B : Finset alpha) | v.1 ∈ A}).card : Real) / 2 := by
  apply proposition72cInducedPacking_of_certificate
    (x := x) (y := y) (z := z)
    (a0 := (0 : Fin 4)) (b0 := (0 : Fin 4)) (b1 := (1 : Fin 4))
    hAB hAcard hBcard hyz
    (show (0 : Fin 4) ≠ 1 by decide)
    proposition72c44A proposition72c44Missing
  · decide
  · decide
  · intro K hK
    exact ⟨zeroExtendTriangleWeight K proposition72c44Weight,
      proposition72c44CanonicalPacking_arbitraryInternal (by
        simpa [proposition72c44Graph] using hK)⟩
  · exact hcross

private theorem proposition72c45InducedPacking
    {G : SimpleGraph alpha} {A B : Finset alpha} {x : A} {y z : B}
    (hAB : Disjoint A B) (hAcard : A.card = 4) (hBcard : B.card = 5)
    (hyz : y ≠ z)
    (hcross : ∀ a ∈ A, ∀ b ∈ B,
      G.Adj a b ↔ s(a, b) ∉ ({s(x.1, y.1), s(x.1, z.1)} : Finset (Sym2 alpha))) :
    ∃ w : Finset (A ∪ B : Finset alpha) → Real,
      IsFractionalInternalCrossPacking
          (G.induce ((A ∪ B : Finset alpha) : Set alpha))
          {v : (A ∪ B : Finset alpha) | v.1 ∈ A} w ∧
        fractionalSize (G.induce ((A ∪ B : Finset alpha) : Set alpha)) w =
          ((internalEdgeFinset
            (G.induce ((A ∪ B : Finset alpha) : Set alpha))
            {v : (A ∪ B : Finset alpha) | v.1 ∈ A}).card : Real) / 2 := by
  apply proposition72cInducedPacking_of_certificate
    (x := x) (y := y) (z := z)
    (a0 := (0 : Fin 4)) (b0 := (0 : Fin 5)) (b1 := (1 : Fin 5))
    hAB hAcard hBcard hyz
    (show (0 : Fin 5) ≠ 1 by decide)
    proposition72c45A proposition72c45Missing
  · decide
  · decide
  · intro K hK
    exact ⟨zeroExtendTriangleWeight K proposition72c45Weight,
      proposition72c45CanonicalPacking_arbitraryInternal (by
        simpa [proposition72c45Graph] using hK)⟩
  · exact hcross

/-- The four size pairs for which Proposition 7.2(c) is used in the
pentagon-extension argument. -/
def Proposition72cSmallSizes (a b : Nat) : Prop :=
  (a = 3 ∧ b = 3) ∨ (a = 3 ∧ b = 4) ∨
    (a = 4 ∧ b = 4) ∨ (a = 4 ∧ b = 5)

/-- Exact arbitrary-blob form of Proposition 7.2(c) for all four size pairs
needed in Section 7.  The only absent cross edges share the displayed
endpoint `x`. -/
theorem proposition72c_small_twoBlobPacking_exact
    {G : SimpleGraph alpha} {A B : Finset alpha} {x y z : alpha}
    (hAB : Disjoint A B) (hx : x ∈ A) (hy : y ∈ B) (hz : z ∈ B)
    (hyz : y ≠ z) (hsizes : Proposition72cSmallSizes A.card B.card)
    (hcross : ∀ a ∈ A, ∀ b ∈ B,
      G.Adj a b ↔ s(a, b) ∉ ({s(x, y), s(x, z)} : Finset (Sym2 alpha))) :
    ∃ w : Finset alpha → Real,
      IsFractionalInternalCrossPacking G (A : Set alpha) w ∧
        fractionalSize G w =
          ((sideEdgeFinset G A).card : Real) / 2 +
            ((sideEdgeFinset G B).card : Real) / 2 := by
  classical
  let xa : A := ⟨x, hx⟩
  let yb : B := ⟨y, hy⟩
  let zb : B := ⟨z, hz⟩
  have hyz' : yb ≠ zb := by
    intro h
    exact hyz (congrArg Subtype.val h)
  have hcross' : ∀ a ∈ A, ∀ b ∈ B,
      G.Adj a b ↔
        s(a, b) ∉ ({s(xa.1, yb.1), s(xa.1, zb.1)} : Finset (Sym2 alpha)) := by
    simpa only [xa, yb, zb] using hcross
  rcases hsizes with h33 | h34 | h44 | h45
  · obtain ⟨u, hu, hsize⟩ := proposition72c33InducedPacking
      hAB h33.1 h33.2 hyz' hcross'
    refine ⟨extendInducedWeight (A ∪ B) u, hu.extendInduced, ?_⟩
    rw [fractionalSize_extendInducedWeight, hsize,
      card_internalEdgeFinset_induce_union_eq_sideEdgeFinset hAB]
    push_cast
    ring
  · obtain ⟨u, hu, hsize⟩ := proposition72c34InducedPacking
      hAB h34.1 h34.2 hyz' hcross'
    refine ⟨extendInducedWeight (A ∪ B) u, hu.extendInduced, ?_⟩
    rw [fractionalSize_extendInducedWeight, hsize,
      card_internalEdgeFinset_induce_union_eq_sideEdgeFinset hAB]
    push_cast
    ring
  · obtain ⟨u, hu, hsize⟩ := proposition72c44InducedPacking
      hAB h44.1 h44.2 hyz' hcross'
    refine ⟨extendInducedWeight (A ∪ B) u, hu.extendInduced, ?_⟩
    rw [fractionalSize_extendInducedWeight, hsize,
      card_internalEdgeFinset_induce_union_eq_sideEdgeFinset hAB]
    push_cast
    ring
  · obtain ⟨u, hu, hsize⟩ := proposition72c45InducedPacking
      hAB h45.1 h45.2 hyz' hcross'
    refine ⟨extendInducedWeight (A ∪ B) u, hu.extendInduced, ?_⟩
    rw [fractionalSize_extendInducedWeight, hsize,
      card_internalEdgeFinset_induce_union_eq_sideEdgeFinset hAB]
    push_cast
    ring

end

end Erdos76
