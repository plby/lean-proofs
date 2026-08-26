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
import ErdosProblems.Erdos76.PentagonTwoBlobExceptionalCanonicalGeneral

/-!
# The arbitrary-blob form of Proposition 7.2(d)

We canonically label a two-edge matching between blobs of sizes three and
five, transport the checked `Fin 8` certificate, and extend it by zero to the
ambient graph.
-/

open Finset

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α]

structure Proposition72dLabeling
    (A B : Finset α) (M : Finset (Sym2 α))
    (hM : IsABCrossMatching A B M) where
  label : M ≃ Fin 2
  leftEquiv : A ≃ Fin 3
  rightEquiv : B ≃ Fin 5
  left_apply : ∀ m : M,
    leftEquiv (crossMatchingOrientation hM m).1 =
      Fin.castAdd 1 (label m)
  right_apply : ∀ m : M,
    rightEquiv (crossMatchingOrientation hM m).2 =
      Fin.castAdd 3 (label m)

theorem exists_proposition72dLabeling
    {A B : Finset α} {M : Finset (Sym2 α)}
    (hAcard : A.card = 3) (hBcard : B.card = 5)
    (hMcard : M.card = 2) (hM : IsABCrossMatching A B M) :
    Nonempty (Proposition72dLabeling A B M hM) := by
  classical
  let label : M ≃ Fin 2 := Fintype.equivFinOfCardEq (by simpa using hMcard)
  let left : M ↪ A :=
    ⟨fun m ↦ (crossMatchingOrientation hM m).1,
      crossMatchingOrientation_left_injective hM⟩
  let right : M ↪ B :=
    ⟨fun m ↦ (crossMatchingOrientation hM m).2,
      crossMatchingOrientation_right_injective hM⟩
  let a₀ : A ≃ Fin 3 := Fintype.equivFinOfCardEq (by simpa using hAcard)
  let b₀ : B ≃ Fin 5 := Fintype.equivFinOfCardEq (by simpa using hBcard)
  let targetA : M ↪ Fin 3 := label.toEmbedding.trans (Fin.castAddEmb 1)
  let targetB : M ↪ Fin 5 := label.toEmbedding.trans (Fin.castAddEmb 3)
  obtain ⟨σA, hσA⟩ := Equiv.Perm.exists_extending_pair
    (fun m : M ↦ a₀ (left m)) targetA
    (a₀.injective.comp left.injective) targetA.injective
  obtain ⟨σB, hσB⟩ := Equiv.Perm.exists_extending_pair
    (fun m : M ↦ b₀ (right m)) targetB
    (b₀.injective.comp right.injective) targetB.injective
  let eA : A ≃ Fin 3 := a₀.trans σA
  let eB : B ≃ Fin 5 := b₀.trans σB
  refine ⟨⟨label, eA, eB, ?_, ?_⟩⟩
  · intro m
    exact hσA m
  · intro m
    exact hσB m

private lemma oriented_mk_injective
    {A B : Finset α} (hAB : Disjoint A B)
    {a a' : A} {b b' : B} (h : s(a.1, b.1) = s(a'.1, b'.1)) :
    a = a' ∧ b = b' := by
  rcases Sym2.eq_iff.mp h with hdir | hswap
  · exact ⟨Subtype.ext hdir.1, Subtype.ext hdir.2⟩
  · exfalso
    exact Finset.disjoint_left.mp hAB a.2
      (hswap.1.symm ▸ b'.2)

lemma Proposition72dLabeling.mem_matching_iff
    {A B : Finset α} {M : Finset (Sym2 α)}
    {hM : IsABCrossMatching A B M}
    (L : Proposition72dLabeling A B M hM) (hAB : Disjoint A B)
    (a : A) (b : B) :
    s(a.1, b.1) ∈ M ↔
      ∃ i : Fin 2,
        L.leftEquiv a = Fin.castAdd 1 i ∧
          L.rightEquiv b = Fin.castAdd 3 i := by
  classical
  constructor
  · intro hab
    let m : M := ⟨s(a.1, b.1), hab⟩
    have horient : s(a.1, b.1) =
        s((crossMatchingOrientation hM m).1.1,
          (crossMatchingOrientation hM m).2.1) := by
      exact crossMatchingOrientation_spec hM m
    have hm := oriented_mk_injective hAB horient
    refine ⟨L.label m, ?_, ?_⟩
    · rw [hm.1]
      exact L.left_apply m
    · rw [hm.2]
      exact L.right_apply m
  · rintro ⟨i, hai, hbi⟩
    let m : M := L.label.symm i
    have hma : a = (crossMatchingOrientation hM m).1 := by
      apply L.leftEquiv.injective
      rw [hai, L.left_apply]
      simp [m]
    have hmb : b = (crossMatchingOrientation hM m).2 := by
      apply L.rightEquiv.injective
      rw [hbi, L.right_apply]
      simp [m]
    rw [hma, hmb, ← crossMatchingOrientation_spec hM m]
    exact m.2

def proposition72dUnionEquiv
    {A B : Finset α} {M : Finset (Sym2 α)}
    {hM : IsABCrossMatching A B M}
    (L : Proposition72dLabeling A B M hM) (hAB : Disjoint A B) :
    (A ∪ B : Finset α) ≃ Proposition72dVertex :=
  (Equiv.Finset.union A B hAB).symm |>.trans
    ((L.leftEquiv.sumCongr L.rightEquiv).trans finSumFinEquiv)

@[simp] lemma proposition72dUnionEquiv_apply_left
    {A B : Finset α} {M : Finset (Sym2 α)}
    {hM : IsABCrossMatching A B M}
    (L : Proposition72dLabeling A B M hM) (hAB : Disjoint A B) (a : A) :
    proposition72dUnionEquiv L hAB
        ⟨a.1, mem_union_left B a.2⟩ =
      Fin.castAdd 5 (L.leftEquiv a) := by
  simp [proposition72dUnionEquiv]
  exact finSumFinEquiv_apply_left _

@[simp] lemma proposition72dUnionEquiv_apply_right
    {A B : Finset α} {M : Finset (Sym2 α)}
    {hM : IsABCrossMatching A B M}
    (L : Proposition72dLabeling A B M hM) (hAB : Disjoint A B) (b : B) :
    proposition72dUnionEquiv L hAB
        ⟨b.1, mem_union_right A b.2⟩ =
      Fin.natAdd 3 (L.rightEquiv b) := by
  simp [proposition72dUnionEquiv]
  exact finSumFinEquiv_apply_right _

private lemma proposition72dCanonicalMissing_oriented_iff
    (a : Fin 3) (b : Fin 5) :
    s(Fin.castAdd 5 a, Fin.natAdd 3 b) ∈ proposition72dCanonicalMissing ↔
      ∃ i : Fin 2, a = Fin.castAdd 1 i ∧ b = Fin.castAdd 3 i := by
  fin_cases a <;> fin_cases b
  all_goals decide

lemma proposition72dUnionEquiv_matching_iff
    {A B : Finset α} {M : Finset (Sym2 α)}
    {hM : IsABCrossMatching A B M}
    (L : Proposition72dLabeling A B M hM) (hAB : Disjoint A B)
    (a : A) (b : B) :
    s(a.1, b.1) ∈ M ↔
      s(proposition72dUnionEquiv L hAB
          ⟨a.1, mem_union_left B a.2⟩,
        proposition72dUnionEquiv L hAB
          ⟨b.1, mem_union_right A b.2⟩) ∈
        proposition72dCanonicalMissing := by
  rw [L.mem_matching_iff hAB,
    proposition72dUnionEquiv_apply_left,
    proposition72dUnionEquiv_apply_right,
    proposition72dCanonicalMissing_oriented_iff]

private lemma finCastAdd_mem_proposition72dCanonicalA (i : Fin 3) :
    Fin.castAdd 5 i ∈ proposition72dCanonicalA := by
  fin_cases i <;> decide

private lemma finNatAdd_not_mem_proposition72dCanonicalA (i : Fin 5) :
    Fin.natAdd 3 i ∉ proposition72dCanonicalA := by
  fin_cases i <;> decide

lemma proposition72dUnionEquiv_mem_canonicalA_iff
    {A B : Finset α} {M : Finset (Sym2 α)}
    {hM : IsABCrossMatching A B M}
    (L : Proposition72dLabeling A B M hM) (hAB : Disjoint A B)
    (x : (A ∪ B : Finset α)) :
    proposition72dUnionEquiv L hAB x ∈ proposition72dCanonicalA ↔
      x.1 ∈ A := by
  classical
  by_cases hxA : x.1 ∈ A
  · let a : A := ⟨x.1, hxA⟩
    have hx : x = ⟨a.1, mem_union_left B a.2⟩ := Subtype.ext rfl
    constructor
    · exact fun _ ↦ hxA
    · intro _
      rw [hx, proposition72dUnionEquiv_apply_left]
      exact finCastAdd_mem_proposition72dCanonicalA _
  · have hxB : x.1 ∈ B := (mem_union.mp x.2).resolve_left hxA
    let b : B := ⟨x.1, hxB⟩
    have hx : x = ⟨b.1, mem_union_right A b.2⟩ := Subtype.ext rfl
    constructor
    · intro hmem
      rw [hx, proposition72dUnionEquiv_apply_right] at hmem
      exact (finNatAdd_not_mem_proposition72dCanonicalA _ hmem).elim
    · exact fun h ↦ (hxA h).elim

lemma proposition72dUnionEquiv_image_side
    {A B : Finset α} {M : Finset (Sym2 α)}
    {hM : IsABCrossMatching A B M}
    (L : Proposition72dLabeling A B M hM) (hAB : Disjoint A B) :
    proposition72dUnionEquiv L hAB ''
        {x : (A ∪ B : Finset α) | x.1 ∈ A} =
      (proposition72dCanonicalA : Set Proposition72dVertex) := by
  ext u
  constructor
  · rintro ⟨x, hxA, rfl⟩
    exact (proposition72dUnionEquiv_mem_canonicalA_iff L hAB x).mpr hxA
  · intro hu
    let x := (proposition72dUnionEquiv L hAB).symm u
    refine ⟨x, ?_, (proposition72dUnionEquiv L hAB).apply_symm_apply u⟩
    apply (proposition72dUnionEquiv_mem_canonicalA_iff L hAB x).mp
    simpa [x] using hu

lemma proposition72dInducedMap_sameCross
    {G : SimpleGraph α} {A B : Finset α} {M : Finset (Sym2 α)}
    {hM : IsABCrossMatching A B M}
    (L : Proposition72dLabeling A B M hM) (hAB : Disjoint A B)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b ↔ s(a, b) ∉ M) :
    SameCrossAdj
      ((G.induce ((A ∪ B : Finset α) : Set α)).map
        (proposition72dUnionEquiv L hAB).toEmbedding)
      proposition72dCanonicalGraph
      (proposition72dCanonicalA : Set Proposition72dVertex) := by
  classical
  let S := A ∪ B
  let e := proposition72dUnionEquiv L hAB
  intro u v huv
  let x : S := e.symm u
  let y : S := e.symm v
  have huSide : u ∈ proposition72dCanonicalA ↔ x.1 ∈ A := by
    have hx := proposition72dUnionEquiv_mem_canonicalA_iff L hAB x
    simpa only [e, x, e.apply_symm_apply] using hx
  have hvSide : v ∈ proposition72dCanonicalA ↔ y.1 ∈ A := by
    have hy := proposition72dUnionEquiv_mem_canonicalA_iff L hAB y
    simpa only [e, y, e.apply_symm_apply] using hy
  have hxySide : ¬(x.1 ∈ A ↔ y.1 ∈ A) := by
    intro h
    exact huv (huSide.trans (h.trans hvSide.symm))
  have huvNe : u ≠ v := by
    intro huvEq
    apply huv
    rw [huvEq]
  have hCanonical : proposition72dCanonicalGraph.Adj u v ↔
      s(u, v) ∉ proposition72dCanonicalMissing := by
    simp [proposition72dCanonicalGraph, huvNe]
  by_cases hxA : x.1 ∈ A
  · have hyA : y.1 ∉ A := fun hyA ↦ hxySide ⟨fun _ ↦ hyA, fun _ ↦ hxA⟩
    have hyB : y.1 ∈ B := (mem_union.mp y.2).resolve_left hyA
    let a : A := ⟨x.1, hxA⟩
    let b : B := ⟨y.1, hyB⟩
    have hxEq : x = ⟨a.1, mem_union_left B a.2⟩ := Subtype.ext rfl
    have hyEq : y = ⟨b.1, mem_union_right A b.2⟩ := Subtype.ext rfl
    have hMapAdj :
        ((G.induce ((S : Finset α) : Set α)).map e.toEmbedding).Adj u v ↔
          G.Adj a.1 b.1 := by
      rw [← e.apply_symm_apply u, ← e.apply_symm_apply v]
      change ((G.induce ((S : Finset α) : Set α)).map e.toEmbedding).Adj
        (e x) (e y) ↔ G.Adj a.1 b.1
      calc
        _ ↔ (G.induce ((S : Finset α) : Set α)).Adj x y :=
          SimpleGraph.map_adj_apply
        _ ↔ G.Adj x.1 y.1 := SimpleGraph.induce_adj
        _ ↔ G.Adj a.1 b.1 := by simpa only [x, y, hxEq, hyEq]
    have hMatching : s(a.1, b.1) ∈ M ↔
        s(u, v) ∈ proposition72dCanonicalMissing := by
      have hm := proposition72dUnionEquiv_matching_iff L hAB a b
      simpa only [e, ← hxEq, ← hyEq, e.apply_symm_apply, x, y] using hm
    exact hMapAdj.trans ((hcross a.1 a.2 b.1 b.2).trans
      ((not_congr hMatching).trans hCanonical.symm))

  · have hyA : y.1 ∈ A := by
      by_contra hyA
      exact hxySide ⟨fun h ↦ (hxA h).elim, fun h ↦ (hyA h).elim⟩
    have hxB : x.1 ∈ B := (mem_union.mp x.2).resolve_left hxA
    let a : A := ⟨y.1, hyA⟩
    let b : B := ⟨x.1, hxB⟩
    have hxEq : x = ⟨b.1, mem_union_right A b.2⟩ := Subtype.ext rfl
    have hyEq : y = ⟨a.1, mem_union_left B a.2⟩ := Subtype.ext rfl
    have hMapAdj :
        ((G.induce ((S : Finset α) : Set α)).map e.toEmbedding).Adj u v ↔
          G.Adj a.1 b.1 := by
      rw [← e.apply_symm_apply u, ← e.apply_symm_apply v]
      change ((G.induce ((S : Finset α) : Set α)).map e.toEmbedding).Adj
        (e x) (e y) ↔ G.Adj a.1 b.1
      calc
        _ ↔ (G.induce ((S : Finset α) : Set α)).Adj x y :=
          SimpleGraph.map_adj_apply
        _ ↔ G.Adj x.1 y.1 := SimpleGraph.induce_adj
        _ ↔ G.Adj a.1 b.1 := by
          simpa only [x, y, hxEq, hyEq] using G.adj_comm b.1 a.1
    have hMatching : s(a.1, b.1) ∈ M ↔
        s(u, v) ∈ proposition72dCanonicalMissing := by
      have hm := proposition72dUnionEquiv_matching_iff L hAB a b
      rw [show s(u, v) = s(v, u) from Sym2.eq_swap]
      simpa only [e, ← hxEq, ← hyEq, e.apply_symm_apply, x, y] using hm
    exact hMapAdj.trans ((hcross a.1 a.2 b.1 b.2).trans
      ((not_congr hMatching).trans hCanonical.symm))

theorem proposition72dInducedPacking
    {G : SimpleGraph α} {A B : Finset α} {M : Finset (Sym2 α)}
    (hAB : Disjoint A B) (hAcard : A.card = 3) (hBcard : B.card = 5)
    (hMcard : M.card = 2) (hM : IsABCrossMatching A B M)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b ↔ s(a, b) ∉ M) :
    ∃ w : Finset (A ∪ B : Finset α) → ℝ,
      IsFractionalInternalCrossPacking
          (G.induce (((A ∪ B : Finset α) : Set α)))
          {x : (A ∪ B : Finset α) | x.1 ∈ A} w ∧
        fractionalSize
            (G.induce (((A ∪ B : Finset α) : Set α))) w =
          ((internalEdgeFinset
            (G.induce (((A ∪ B : Finset α) : Set α)))
            {x : (A ∪ B : Finset α) | x.1 ∈ A}).card : ℝ) / 2 := by
  classical
  let L := Classical.choice
    (exists_proposition72dLabeling hAcard hBcard hMcard hM)
  let e := proposition72dUnionEquiv L hAB
  apply proposition72dPacking_of_equiv e
  · exact proposition72dUnionEquiv_image_side L hAB
  · exact proposition72dInducedMap_sameCross L hAB hcross

private lemma embedding_sym2Map_mem_sym2_map_iff
    {β : Type*} [DecidableEq β] (f : α ↪ β)
    (p : Sym2 α) (t : Finset α) :
    f.sym2Map p ∈ (t.map f).sym2 ↔ p ∈ t.sym2 := by
  rw [Finset.sym2_map]
  constructor
  · intro hp
    obtain ⟨q, hq, hqp⟩ := mem_map.mp hp
    have : q = p := f.sym2Map.injective hqp
    simpa only [this] using hq
  · exact fun hp ↦ mem_map.mpr ⟨p, hp, rfl⟩

lemma mem_internalCrossTriangles_induce_map
    {G : SimpleGraph α} (S : Finset α) (s : Set α)
    {t : Finset S}
    (ht : t ∈ internalCrossTriangles (G.induce (S : Set α))
      {x : S | x.1 ∈ s}) :
    t.map (inducedEmbedding S) ∈ internalCrossTriangles G s := by
  classical
  rcases mem_internalCrossTriangles.mp ht with ⟨htClique, htOne⟩
  apply mem_internalCrossTriangles.mpr
  refine ⟨?_, ?_⟩
  · rw [inducedEmbedding_eq_setEmbedding]
    exact (SimpleGraph.isNClique_induce_iff
      (G := G) (S : Set α) t 3).mp htClique
  · have hfilter :
        (internalEdgeFinset G s).filter
            (fun e ↦ e ∈ (t.map (inducedEmbedding S)).sym2) =
          ((internalEdgeFinset (G.induce (S : Set α))
            {x : S | x.1 ∈ s}).filter (fun p ↦ p ∈ t.sym2)).map
              (inducedEmbedding S).sym2Map := by
      ext e
      constructor
      · intro he
        rcases mem_filter.mp he with ⟨heInternal, het⟩
        rw [Finset.sym2_map] at het
        obtain ⟨p, hpt, rfl⟩ := mem_map.mp het
        apply mem_map.mpr
        refine ⟨p, mem_filter.mpr ⟨?_, hpt⟩, rfl⟩
        rcases mem_filter.mp heInternal with ⟨heEdge, heSame⟩
        induction p using Sym2.inductionOn with
        | hf x y =>
            have hmap :
                (inducedEmbedding S).sym2Map s(x, y) = s(x.1, y.1) := rfl
            rw [hmap] at heEdge heSame
            apply mem_filter.mpr
            refine ⟨?_, ?_⟩
            · apply SimpleGraph.mem_edgeFinset.mpr
              change G.Adj x.1 y.1
              exact SimpleGraph.mem_edgeFinset.mp heEdge
            · rw [sameSide_mk]
              change x.1 ∈ s ↔ y.1 ∈ s
              exact (sameSide_mk s x.1 y.1).mp heSame
      · intro he
        obtain ⟨p, hp, rfl⟩ := mem_map.mp he
        rcases mem_filter.mp hp with ⟨hpInternal, hpt⟩
        rcases mem_filter.mp hpInternal with ⟨hpEdge, hpSame⟩
        apply mem_filter.mpr
        refine ⟨?_, (embedding_sym2Map_mem_sym2_map_iff
          (inducedEmbedding S) p t).mpr hpt⟩
        induction p using Sym2.inductionOn with
        | hf x y =>
            have hmap :
                (inducedEmbedding S).sym2Map s(x, y) = s(x.1, y.1) := rfl
            rw [hmap]
            apply mem_filter.mpr
            refine ⟨?_, ?_⟩
            · apply SimpleGraph.mem_edgeFinset.mpr
              have hpAdj := SimpleGraph.mem_edgeFinset.mp hpEdge
              change G.Adj x.1 y.1 at hpAdj
              exact hpAdj
            · apply (sameSide_mk s x.1 y.1).mpr
              rw [sameSide_mk] at hpSame
              exact hpSame
    rw [hfilter, card_map]
    exact htOne

lemma IsFractionalInternalCrossPacking.extendInduced
    {G : SimpleGraph α} {S : Finset α} {s : Set α}
    {w : Finset S → ℝ}
    (hw : IsFractionalInternalCrossPacking
      (G.induce (S : Set α)) {x : S | x.1 ∈ s} w) :
    IsFractionalInternalCrossPacking G s (extendInducedWeight S w) := by
  classical
  refine ⟨hw.1.extendInduced, ?_⟩
  intro t htNot
  by_cases htS : t ⊆ S
  · rw [extendInducedWeight, dif_pos htS]
    apply hw.2
    intro htCross
    apply htNot
    have hmapped := mem_internalCrossTriangles_induce_map S s htCross
    have hmap :
        (restrictToInduced S t htS).map (inducedEmbedding S) = t := by
      simpa only [restrictToInduced, inducedEmbedding] using
        (Finset.subtype_map_of_mem htS)
    simpa only [hmap] using hmapped
  · exact extendInducedWeight_eq_zero htS

private lemma card_sideEdgeFinset_induce_superset
    {G : SimpleGraph α} {S T : Finset α} (hTS : T ⊆ S) :
    (sideEdgeFinset (G.induce (S : Set α))
        {x : S | x.1 ∈ T}).card =
      (sideEdgeFinset G T).card := by
  classical
  let H : SimpleGraph S := G.induce (S : Set α)
  let Ts : Finset S := {x | x.1 ∈ T}
  let e : {x : S // x ∈ (Ts : Set S)} ≃ T :=
    { toFun := fun x ↦ ⟨x.1.1, by simpa [Ts] using x.2⟩
      invFun := fun t ↦ ⟨⟨t.1, hTS t.2⟩, by simp [Ts]⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := by
        intro t
        apply Subtype.ext
        rfl }
  let iso : H.induce (Ts : Set S) ≃g G.induce (T : Set α) :=
    { __ := e
      map_rel_iff' := Iff.rfl }
  change (sideEdgeFinset H Ts).card = _
  calc
    (sideEdgeFinset H Ts).card =
        (H.induce (Ts : Set S)).edgeFinset.card := card_sideEdgeFinset H Ts
    _ = (G.induce (T : Set α)).edgeFinset.card := iso.card_edgeFinset_eq
    _ = (sideEdgeFinset G T).card := (card_sideEdgeFinset G T).symm

private lemma sideEdgeFinset_disjoint_of_disjoint
    {G : SimpleGraph α} {A B : Finset α} (hAB : Disjoint A B) :
    Disjoint (sideEdgeFinset G A) (sideEdgeFinset G B) := by
  classical
  rw [Finset.disjoint_left]
  intro e heA heB
  rcases mem_filter.mp heA with ⟨_, heAs⟩
  rcases mem_filter.mp heB with ⟨_, heBs⟩
  induction e using Sym2.inductionOn with
  | hf x y =>
      have hxPair : x ∈ s(x, y).toFinset := by simp
      exact Finset.disjoint_left.mp hAB (heAs hxPair) (heBs hxPair)

private lemma card_internalEdgeFinset_of_side_partition
    {G : SimpleGraph α} {A B : Finset α}
    (hcomp : (A : Set α)ᶜ.toFinset = B) (hAB : Disjoint A B) :
    (internalEdgeFinset G (A : Set α)).card =
      (sideEdgeFinset G A).card + (sideEdgeFinset G B).card := by
  classical
  have hcoeA : (A : Set α).toFinset = A := by
    ext x
    simp
  have hsideA : sideEdgeFinset G (A : Set α).toFinset =
      sideEdgeFinset G A := congrArg (sideEdgeFinset G) hcoeA
  have hsideB : sideEdgeFinset G (A : Set α)ᶜ.toFinset =
      sideEdgeFinset G B := congrArg (sideEdgeFinset G) hcomp
  calc
    (internalEdgeFinset G (A : Set α)).card =
        (sideEdgeFinset G (A : Set α).toFinset ∪
          sideEdgeFinset G (A : Set α)ᶜ.toFinset).card := by
      apply congrArg Finset.card
      ext e
      induction e using Sym2.inductionOn with
      | hf x y =>
          by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;>
            simp [internalEdgeFinset, sideEdgeFinset, sameSide_mk,
              subset_iff, hx, hy]
    _ = (sideEdgeFinset G A ∪ sideEdgeFinset G B).card := by
      rw [hsideA, hsideB]
    _ = (sideEdgeFinset G A).card + (sideEdgeFinset G B).card :=
      card_union_of_disjoint (sideEdgeFinset_disjoint_of_disjoint hAB)

private lemma card_internalEdgeFinset_induce_union
    {G : SimpleGraph α} {A B : Finset α} (hAB : Disjoint A B) :
    (internalEdgeFinset
        (G.induce (((A ∪ B : Finset α) : Set α)))
        {x : (A ∪ B : Finset α) | x.1 ∈ A}).card =
      (sideEdgeFinset G A).card + (sideEdgeFinset G B).card := by
  classical
  let S : Finset α := A ∪ B
  let H : SimpleGraph S := G.induce (S : Set α)
  let As : Finset S := {x | x.1 ∈ A}
  let Bs : Finset S := {x | x.1 ∈ B}
  have hAsSet : (As : Set S) = {x : S | x.1 ∈ A} := by
    ext x
    simp [As]
  have hcomp : (As : Set S)ᶜ.toFinset = Bs := by
    ext x
    simp only [Set.mem_toFinset, Set.mem_compl_iff]
    simp only [Finset.mem_coe, As, Bs, mem_filter, mem_univ, true_and]
    constructor
    · intro hxA
      exact (mem_union.mp x.2).resolve_left hxA
    · intro hxB hxA
      exact Finset.disjoint_left.mp hAB hxA hxB
  have hcardA : (sideEdgeFinset H As).card =
      (sideEdgeFinset G A).card := by
    simpa only [H, As, S] using
      (card_sideEdgeFinset_induce_superset (G := G)
        (S := A ∪ B) (T := A) (fun _ hx ↦ mem_union_left B hx))
  have hcardB : (sideEdgeFinset H Bs).card =
      (sideEdgeFinset G B).card := by
    simpa only [H, Bs, S] using
      (card_sideEdgeFinset_induce_superset (G := G)
        (S := A ∪ B) (T := B) (fun _ hx ↦ mem_union_right A hx))
  have hAsBs : Disjoint As Bs := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact Finset.disjoint_left.mp hAB (by simpa [As] using hxA)
      (by simpa [Bs] using hxB)
  have hpart := card_internalEdgeFinset_of_side_partition
    (G := H) hcomp hAsBs
  change (internalEdgeFinset H {x : S | x.1 ∈ A}).card = _
  calc
    (internalEdgeFinset H {x : S | x.1 ∈ A}).card =
        (internalEdgeFinset H (As : Set S)).card := by rw [hAsSet]
    _ = (sideEdgeFinset H As).card + (sideEdgeFinset H Bs).card := hpart
    _ = (sideEdgeFinset G A).card + (sideEdgeFinset G B).card := by
      rw [hcardA, hcardB]

/-- The internal edges of the induced two-blob graph are exactly the edges
internal to either displayed blob.  This public wrapper is reused by the
other cases of Proposition 7.2. -/
lemma card_internalEdgeFinset_induce_union_eq_sideEdgeFinset
    {G : SimpleGraph α} {A B : Finset α} (hAB : Disjoint A B) :
    (internalEdgeFinset
        (G.induce (((A ∪ B : Finset α) : Set α)))
        {x : (A ∪ B : Finset α) | x.1 ∈ A}).card =
      (sideEdgeFinset G A).card + (sideEdgeFinset G B).card :=
  card_internalEdgeFinset_induce_union hAB

/-- Exact arbitrary-blob form of Proposition 7.2(d): deleting a two-edge
matching between blobs of sizes three and five admits a half-internal-edge
fractional cross packing, regardless of the colours inside the blobs. -/
theorem proposition72d_twoBlobPacking_exact
    {G : SimpleGraph α} {A B : Finset α} {M : Finset (Sym2 α)}
    (hAB : Disjoint A B) (hAcard : A.card = 3) (hBcard : B.card = 5)
    (hMcard : M.card = 2) (hM : IsABCrossMatching A B M)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b ↔ s(a, b) ∉ M) :
    ∃ w : Finset α → ℝ,
      IsFractionalInternalCrossPacking G (A : Set α) w ∧
        fractionalSize G w =
          ((sideEdgeFinset G A).card : ℝ) / 2 +
            ((sideEdgeFinset G B).card : ℝ) / 2 := by
  classical
  obtain ⟨u, hu, hsize⟩ :=
    proposition72dInducedPacking hAB hAcard hBcard hMcard hM hcross
  refine ⟨extendInducedWeight (A ∪ B) u, hu.extendInduced, ?_⟩
  rw [fractionalSize_extendInducedWeight, hsize,
    card_internalEdgeFinset_induce_union hAB]
  push_cast
  ring

end

end Erdos76
