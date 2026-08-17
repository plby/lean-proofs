/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

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

import ErdosProblems.Erdos223.CarrierFive
import ErdosProblems.Erdos223.LocalSphere

/-!
# Stable-partition shape in dimension five

This module proves the sound finite-obstruction consequence of a stable
two-class diameter-graph partition.  Under an explicit retained-fiber size
bound, every retained class is cospherical and its affine direction has
dimension at most three.

It deliberately does not claim that both retained affine ranks cannot be
three: weak five-dimensional carriers can have an off-circle point in each
crossed sphere, giving rank three in both classes while only the off/off
cross-pair is missing.
-/

open scoped EuclideanGeometry RealInnerProductSpace SimpleGraph

namespace Erdos223.FiveWeakCarrier

noncomputable section

private lemma card_biUnion_bad_le'
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S Q : Finset V) (B : ℕ)
    (hbad : ∀ x ∈ Q, (S.filter fun y ↦ ¬ G.Adj x y).card ≤ B) :
    (Q.biUnion fun x ↦ S.filter fun y ↦ ¬ G.Adj x y).card ≤ Q.card * B := by
  calc
    (Q.biUnion fun x ↦ S.filter fun y ↦ ¬ G.Adj x y).card
        ≤ ∑ x ∈ Q, (S.filter fun y ↦ ¬ G.Adj x y).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ Q, B := Finset.sum_le_sum fun x hx ↦ hbad x hx
    _ = Q.card * B := by simp

private lemma stable_bad_in_opposite_fiber_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {p : ℕ} {epsilon : ℝ} (P : Stability.StablePartition G p epsilon)
    (_hepsilon : 0 ≤ epsilon) {i j : Fin p} (hij : i ≠ j)
    {x : V} (hx : x ∈ Stability.retainedFiber P.color P.exceptional i) :
    ((Stability.retainedFiber P.color P.exceptional j).filter
      fun y ↦ ¬ G.Adj x y).card ≤
      ⌈epsilon * (Fintype.card V : ℝ)⌉₊ := by
  classical
  let Bad := (Stability.retainedFiber P.color P.exceptional j).filter
    fun y ↦ ¬ G.Adj x y
  let R := Stability.retainedCrossNonneighbors G P.color P.exceptional x
  have hsub : Bad ⊆ R := by
    intro y hy
    have hy' := Finset.mem_filter.mp hy
    have hxi := (Stability.mem_retainedFiber P.color P.exceptional i x).1 hx
    have hyj :=
      (Stability.mem_retainedFiber P.color P.exceptional j y).1 hy'.1
    rw [Stability.mem_retainedCrossNonneighbors]
    exact ⟨hyj.2, by simpa [hxi.1, hyj.1] using hij, hy'.2⟩
  have hcardR : (Bad.card : ℝ) ≤ (R.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hsmall := P.crossNonneighbors_small i x hx
  have hceil : epsilon * (Fintype.card V : ℝ) ≤
      (⌈epsilon * (Fintype.card V : ℝ)⌉₊ : ℝ) :=
    Nat.le_ceil (epsilon * (Fintype.card V : ℝ))
  have hlt : (Bad.card : ℝ) <
      (⌈epsilon * (Fintype.card V : ℝ)⌉₊ : ℝ) :=
    hcardR.trans_lt (hsmall.trans_le hceil)
  have : Bad.card < ⌈epsilon * (Fintype.card V : ℝ)⌉₊ := by
    exact_mod_cast hlt
  exact Nat.le_of_lt this

/-- Any set of at most five retained vertices in one class has three common
neighbors in the other retained class, under the explicit union-bound
hypothesis used by the dimension-five geometric argument. -/
theorem exists_three_common_cross_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {epsilon : ℝ} (P : Stability.StablePartition G 2 epsilon)
    (hepsilon : 0 ≤ epsilon) {i j : Fin 2} (hij : i ≠ j)
    (Q : Finset V)
    (hQsub : Q ⊆ Stability.retainedFiber P.color P.exceptional i)
    (hQcard : Q.card ≤ 5)
    (hlarge : 5 * ⌈epsilon * (Fintype.card V : ℝ)⌉₊ + 3 ≤
      (Stability.retainedFiber P.color P.exceptional j).card) :
    ∃ T : Finset V,
      T ⊆ Stability.retainedFiber P.color P.exceptional j ∧ T.card = 3 ∧
      ∀ x ∈ Q, ∀ y ∈ T, G.Adj x y := by
  classical
  let S := Stability.retainedFiber P.color P.exceptional j
  let B := ⌈epsilon * (Fintype.card V : ℝ)⌉₊
  let Bad := Q.biUnion fun x ↦ S.filter fun y ↦ ¬ G.Adj x y
  have hbad : ∀ x ∈ Q, (S.filter fun y ↦ ¬ G.Adj x y).card ≤ B := by
    intro x hx
    exact stable_bad_in_opposite_fiber_le G P hepsilon hij (hQsub hx)
  have hBadS : Bad ⊆ S := by
    intro y hy
    simp only [Bad, Finset.mem_biUnion, Finset.mem_filter] at hy
    obtain ⟨x, _hx, hyS, _⟩ := hy
    exact hyS
  have hBad : Bad.card ≤ Q.card * B :=
    card_biUnion_bad_le' G S Q B hbad
  have hBad' : Bad.card ≤ 5 * B :=
    hBad.trans (Nat.mul_le_mul_right B hQcard)
  have hthree : 3 ≤ (S \ Bad).card := by
    rw [Finset.card_sdiff_of_subset hBadS]
    change 5 * B + 3 ≤ S.card at hlarge
    omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hthree
  refine ⟨T, hTsub.trans Finset.sdiff_subset, hTcard, ?_⟩
  intro x hx y hy
  have hyDiff : y ∈ S \ Bad := hTsub hy
  by_contra hxy
  exact (Finset.mem_sdiff.mp hyDiff).2 (by
    simp only [Bad, Finset.mem_biUnion, Finset.mem_filter]
    exact ⟨x, hx, (Finset.mem_sdiff.mp hyDiff).1, hxy⟩)

private lemma finrank_affineSpan_eq_two_of_card_three_on_sphere
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : Finset E) (hTcard : T.card = 3) (q : E) (hTq : ∀ x ∈ T, dist x q = 1) :
    Module.finrank ℝ (affineSpan ℝ (↑T : Set E)).direction = 2 := by
  classical
  let e : Fin 3 ≃ {x // x ∈ T} := (Finset.equivFinOfCardEq hTcard).symm
  let b : Fin 3 → E := fun i ↦ e i
  have hb_inj : Function.Injective b := by
    intro i j hij
    exact e.injective (Subtype.ext hij)
  have hcos : EuclideanGeometry.Cospherical (↑T : Set E) := by
    exact ⟨q, 1, hTq⟩
  have hb_mem : Set.range b ⊆ (↑T : Set E) := by
    rintro _ ⟨i, rfl⟩
    exact (e i).2
  have hbAI : AffineIndependent ℝ b := hcos.affineIndependent hb_mem hb_inj
  have hrange : Set.range b = (↑T : Set E) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hx
      obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  rw [← hrange, direction_affineSpan]
  exact hbAI.finrank_vectorSpan (by norm_num)

/-- Every five selected points in one retained fiber are cospherical and
have affine-direction rank at most three.  This is the exact local
finite-obstruction consequence of stable cross-nonneighbor control. -/
theorem five_point_subset_rank_le_three_and_cospherical
    {A : Finset (Point 5)} {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) 2 epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hlarge : ∀ i : Fin 2,
      5 * ⌈epsilon * (A.card : ℝ)⌉₊ + 3 ≤
        (Stability.retainedFiber P.color P.exceptional i).card)
    {i : Fin 2} (Q : Finset {x // x ∈ A})
    (hQsub : Q ⊆ Stability.retainedFiber P.color P.exceptional i)
    (hQcard : Q.card = 5) :
    Module.finrank ℝ
        (affineSpan ℝ (↑(Q.map ⟨Subtype.val, Subtype.val_injective⟩) :
          Set (Point 5))).direction ≤ 3 ∧
      EuclideanGeometry.Cospherical
        (↑(Q.map ⟨Subtype.val, Subtype.val_injective⟩) : Set (Point 5)) := by
  classical
  let j : Fin 2 := if i = 0 then 1 else 0
  have hij : i ≠ j := by
    fin_cases i <;> simp [j]
  obtain ⟨T, hTsub, hTcard, hcross⟩ :=
    exists_three_common_cross_neighbors (diameterGraph A) P hepsilon hij Q hQsub
      (by omega) (by simpa using hlarge j)
  let emb : {x // x ∈ A} ↪ Point 5 := ⟨Subtype.val, Subtype.val_injective⟩
  let Qp : Finset (Point 5) := Q.map emb
  let Tp : Finset (Point 5) := T.map emb
  have hQpcard : Qp.card = 5 := by simpa [Qp, emb] using hQcard
  have hTpcard : Tp.card = 3 := by simpa [Tp, emb] using hTcard
  have hcrossDist : ∀ x ∈ Qp, ∀ y ∈ Tp, dist x y = 1 := by
    intro x hx y hy
    change x ∈ Q.map emb at hx
    change y ∈ T.map emb at hy
    rw [Finset.mem_map] at hx
    rw [Finset.mem_map] at hy
    obtain ⟨x', hx'Q, rfl⟩ := hx
    obtain ⟨y', hy'T, rfl⟩ := hy
    exact (diameterGraph_adj A x' y').1 (hcross x' hx'Q y' hy'T)
  obtain ⟨horth, c, r, s, hc, hr0, hs0, hQr, hTs, hrs⟩ :=
    completeBipartiteGeometry_finset Qp Tp (by omega) (by omega) hcrossDist
  have hTpRank :
      Module.finrank ℝ (affineSpan ℝ (↑Tp : Set (Point 5))).direction = 2 := by
    obtain ⟨q, hq⟩ := Qp.nonempty_of_ne_empty (by
      intro h
      have : Qp.card = 0 := by simp [h]
      omega)
    apply finrank_affineSpan_eq_two_of_card_three_on_sphere Tp hTpcard q
    intro y hy
    simpa [dist_comm] using hcrossDist q hq y hy
  have hleOrth :
      (affineSpan ℝ (↑Tp : Set (Point 5))).direction ≤
        (affineSpan ℝ (↑Qp : Set (Point 5))).directionᗮ := by
    exact horth.ge
  have hTpLe :
      Module.finrank ℝ (affineSpan ℝ (↑Tp : Set (Point 5))).direction ≤
        Module.finrank ℝ
          (affineSpan ℝ (↑Qp : Set (Point 5))).directionᗮ :=
    Submodule.finrank_mono hleOrth
  have hsum :=
    (affineSpan ℝ (↑Qp : Set (Point 5))).direction.finrank_add_finrank_orthogonal
  have hQrank :
      Module.finrank ℝ (affineSpan ℝ (↑Qp : Set (Point 5))).direction ≤ 3 := by
    have hamb : Module.finrank ℝ (Point 5) = 5 := by simp [Point]
    rw [hTpRank] at hTpLe
    rw [hamb] at hsum
    omega
  refine ⟨?_, ?_⟩
  · simpa [Qp, emb] using hQrank
  · simpa [Qp, emb] using (show EuclideanGeometry.Cospherical
      (↑Qp : Set (Point 5)) from ⟨c, r, hQr⟩)

private theorem subset_cospherical_center_mem_affineSpan
    {A : Finset (Point 5)} {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) 2 epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hlarge : ∀ i : Fin 2,
      5 * ⌈epsilon * (A.card : ℝ)⌉₊ + 3 ≤
        (Stability.retainedFiber P.color P.exceptional i).card)
    {i : Fin 2} (Q : Finset {x // x ∈ A})
    (hQsub : Q ⊆ Stability.retainedFiber P.color P.exceptional i)
    (hQne : Q.Nonempty) (hQcard : Q.card ≤ 5) :
    ∃ c : Point 5, ∃ r : ℝ,
      c ∈ affineSpan ℝ
        (↑(Q.map ⟨Subtype.val, Subtype.val_injective⟩) : Set (Point 5)) ∧
      ∀ x ∈ Q.map ⟨Subtype.val, Subtype.val_injective⟩, dist x c = r := by
  classical
  let j : Fin 2 := if i = 0 then 1 else 0
  have hij : i ≠ j := by
    fin_cases i <;> simp [j]
  obtain ⟨T, hTsub, hTcard, hcross⟩ :=
    exists_three_common_cross_neighbors (diameterGraph A) P hepsilon hij Q hQsub
      hQcard (by simpa using hlarge j)
  let emb : {x // x ∈ A} ↪ Point 5 := ⟨Subtype.val, Subtype.val_injective⟩
  let Qp : Finset (Point 5) := Q.map emb
  let Tp : Finset (Point 5) := T.map emb
  have hQpne : Qp.Nonempty := by simpa [Qp, emb] using hQne
  have hTpne : Tp.Nonempty := by
    rw [← Finset.card_pos, show Tp.card = 3 by simpa [Tp, emb] using hTcard]
    decide
  have hcrossDist : ∀ x ∈ Qp, ∀ y ∈ Tp, dist x y = 1 := by
    intro x hx y hy
    change x ∈ Q.map emb at hx
    change y ∈ T.map emb at hy
    rw [Finset.mem_map] at hx hy
    obtain ⟨x', hx'Q, rfl⟩ := hx
    obtain ⟨y', hy'T, rfl⟩ := hy
    exact (diameterGraph_adj A x' y').1 (hcross x' hx'Q y' hy'T)
  obtain ⟨_horth, c, r, _s, hc, _hr0, _hs0, hQr, _hTs, _hrs⟩ :=
    completeBipartiteGeometry hQpne.to_set hTpne.to_set hcrossDist
  refine ⟨c, r, ?_, ?_⟩
  · simpa [Qp, emb] using hc
  · simpa [Qp, emb] using hQr

/-- Under the same explicit finite-obstruction bound, the entire retained
fiber has affine-direction rank at most three. -/
theorem retainedFiber_affineSpan_finrank_le_three
    {A : Finset (Point 5)} {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) 2 epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hlarge : ∀ i : Fin 2,
      5 * ⌈epsilon * (A.card : ℝ)⌉₊ + 3 ≤
        (Stability.retainedFiber P.color P.exceptional i).card)
    (i : Fin 2) :
    Module.finrank ℝ
      (affineSpan ℝ
        (↑((Stability.retainedFiber P.color P.exceptional i).map
          ⟨Subtype.val, Subtype.val_injective⟩) : Set (Point 5))).direction ≤ 3 := by
  classical
  let F := Stability.retainedFiber P.color P.exceptional i
  let emb : {x // x ∈ A} ↪ Point 5 := ⟨Subtype.val, Subtype.val_injective⟩
  let Fp : Finset (Point 5) := F.map emb
  change Module.finrank ℝ (affineSpan ℝ (↑Fp : Set (Point 5))).direction ≤ 3
  by_contra hnot
  have hrank : 4 ≤
      Module.finrank ℝ (affineSpan ℝ (↑Fp : Set (Point 5))).direction := by
    omega
  obtain ⟨t, htFp, hspan, htAI⟩ :=
    exists_affineIndependent ℝ (Point 5) (↑Fp : Set (Point 5))
  have htfinite : t.Finite := Fp.finite_toSet.subset htFp
  let tf : Finset (Point 5) := htfinite.toFinset
  have htne : t.Nonempty := by
    by_contra hne
    have ht0 : t = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hz : Module.finrank ℝ
        (affineSpan ℝ (↑Fp : Set (Point 5))).direction = 0 := by
      rw [← hspan, ht0]
      simp
    omega
  have htcard : 5 ≤ tf.card := by
    have htfSub : (↑tf : Set (Point 5)) ⊆ t := by
      intro x hx
      exact htfinite.mem_toFinset.mp hx
    have htfAI : AffineIndependent ℝ
        ((↑) : {x // x ∈ tf} → Point 5) := htAI.mono htfSub
    letI : Nonempty {x // x ∈ tf} :=
      ⟨⟨htne.some, htfinite.mem_toFinset.mpr htne.some_mem⟩⟩
    have hdim := htfAI.finrank_vectorSpan_add_one
    have hrange : Set.range ((↑) : {x // x ∈ tf} → Point 5) =
        (↑tf : Set (Point 5)) := Subtype.range_coe
    have hdim' : Module.finrank ℝ
        (vectorSpan ℝ (↑tf : Set (Point 5))) + 1 = tf.card := by
      rw [hrange] at hdim
      simpa only [Fintype.card_coe] using hdim
    have htcoe : (↑tf : Set (Point 5)) = t := htfinite.coe_toFinset
    rw [htcoe, ← direction_affineSpan, hspan] at hdim'
    omega
  obtain ⟨Qp, hQptf, hQpcard⟩ := Finset.exists_subset_card_eq htcard
  have hQpt : (↑Qp : Set (Point 5)) ⊆ t := by
    intro x hx
    exact htfinite.mem_toFinset.mp (hQptf hx)
  have hQpFp : Qp ⊆ Fp := by
    intro x hx
    exact htFp (hQpt hx)
  let Q : Finset {x // x ∈ A} := F.filter fun x ↦ (x : Point 5) ∈ Qp
  have hQsub : Q ⊆ F := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hmapQ : Q.map emb = Qp := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact (Finset.mem_filter.mp hy).2
    · intro hx
      have hxFp : x ∈ Fp := hQpFp hx
      change x ∈ F.map emb at hxFp
      rw [Finset.mem_map] at hxFp
      obtain ⟨y, hyF, hyx⟩ := hxFp
      refine Finset.mem_map.mpr ⟨y, ?_, hyx⟩
      apply Finset.mem_filter.mpr
      refine ⟨hyF, ?_⟩
      change (y : Point 5) ∈ Qp
      have hyx' : (y : Point 5) = x := by simpa [emb] using hyx
      rw [hyx']
      exact hx
  have hQcard : Q.card = 5 := by
    calc
      Q.card = (Q.map emb).card := by simp
      _ = Qp.card := congrArg Finset.card hmapQ
      _ = 5 := hQpcard
  have hlocal := five_point_subset_rank_le_three_and_cospherical
    P hepsilon hlarge Q (by simpa [F] using hQsub) hQcard
  have hmapQ' :
      Q.map ⟨Subtype.val, Subtype.val_injective⟩ = Qp := by
    simpa [emb] using hmapQ
  have hlocalRank :
      Module.finrank ℝ (affineSpan ℝ (↑Qp : Set (Point 5))).direction ≤ 3 := by
    rw [← hmapQ']
    exact hlocal.1
  have hQAI : AffineIndependent ℝ
      ((↑) : {x // x ∈ Qp} → Point 5) := htAI.mono hQpt
  have hQrank :
      Module.finrank ℝ (affineSpan ℝ (↑Qp : Set (Point 5))).direction = 4 := by
    rw [direction_affineSpan, ← @Subtype.range_coe _ (↑Qp : Set (Point 5))]
    apply hQAI.finrank_vectorSpan
    simpa using hQpcard
  omega

/-- Each retained fiber is globally cospherical.  The center is obtained as
the circumcenter of an affine basis; the at-most-five-point obstruction
shows every further retained point lies on that same sphere. -/
theorem retainedFiber_cospherical
    {A : Finset (Point 5)} {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) 2 epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hlarge : ∀ i : Fin 2,
      5 * ⌈epsilon * (A.card : ℝ)⌉₊ + 3 ≤
        (Stability.retainedFiber P.color P.exceptional i).card)
    (i : Fin 2) :
    EuclideanGeometry.Cospherical
      (↑((Stability.retainedFiber P.color P.exceptional i).map
        ⟨Subtype.val, Subtype.val_injective⟩) : Set (Point 5)) := by
  classical
  let F := Stability.retainedFiber P.color P.exceptional i
  let emb : {x // x ∈ A} ↪ Point 5 := ⟨Subtype.val, Subtype.val_injective⟩
  let Fp : Finset (Point 5) := F.map emb
  have hFcard : 3 ≤ F.card :=
    (show 3 ≤ 5 * ⌈epsilon * (A.card : ℝ)⌉₊ + 3 by omega).trans (hlarge i)
  have hFpne : Fp.Nonempty := by
    rw [← Finset.card_pos]
    simpa [Fp, emb] using (show 0 < F.card by omega)
  obtain ⟨t, htFp, hspan, htAI⟩ :=
    exists_affineIndependent ℝ (Point 5) (↑Fp : Set (Point 5))
  have htfinite : t.Finite := Fp.finite_toSet.subset htFp
  let tf : Finset (Point 5) := htfinite.toFinset
  have htcoe : (↑tf : Set (Point 5)) = t := htfinite.coe_toFinset
  have htfSub : (↑tf : Set (Point 5)) ⊆ t := by simpa [htcoe]
  have htfAI : AffineIndependent ℝ
      ((↑) : {x // x ∈ tf} → Point 5) := htAI.mono htfSub
  have htfne : tf.Nonempty := by
    by_contra hne
    have htf0 : tf = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    obtain ⟨x, hx⟩ := hFpne
    have hxspan : x ∈ affineSpan ℝ (↑Fp : Set (Point 5)) :=
      mem_affineSpan ℝ hx
    rw [← hspan, ← htcoe, htf0] at hxspan
    have hxbot : x ∈ (⊥ : AffineSubspace ℝ (Point 5)) := by simpa using hxspan
    exact AffineSubspace.notMem_bot ℝ (Point 5) x hxbot
  let n := Module.finrank ℝ (affineSpan ℝ (↑Fp : Set (Point 5))).direction
  have htfcard : tf.card = n + 1 := by
    letI : Nonempty {x // x ∈ tf} := htfne.to_subtype
    have hdim := htfAI.finrank_vectorSpan_add_one
    have hrange : Set.range ((↑) : {x // x ∈ tf} → Point 5) =
        (↑tf : Set (Point 5)) := Subtype.range_coe
    rw [hrange] at hdim
    have hspan' : affineSpan ℝ (↑tf : Set (Point 5)) =
        affineSpan ℝ (↑Fp : Set (Point 5)) := by simpa [htcoe] using hspan
    rw [← direction_affineSpan, hspan'] at hdim
    simpa [n] using hdim.symm
  have hnle : n ≤ 3 := by
    exact retainedFiber_affineSpan_finrank_le_three P hepsilon hlarge i
  let e : Fin (n + 1) ≃ {x // x ∈ tf} :=
    (Finset.equivFinOfCardEq htfcard).symm
  let pts : Fin (n + 1) → Point 5 := fun k ↦ e k
  have hptsAI : AffineIndependent ℝ pts := by
    exact htfAI.comp_embedding e.toEmbedding
  let S : Affine.Simplex ℝ (Point 5) n := ⟨pts, hptsAI⟩
  have hrangePts : Set.range S.points = (↑tf : Set (Point 5)) := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact (e k).2
    · intro hx
      obtain ⟨k, hk⟩ := e.surjective ⟨x, hx⟩
      exact ⟨k, congrArg Subtype.val hk⟩
  have hspanTf : affineSpan ℝ (↑tf : Set (Point 5)) =
      affineSpan ℝ (↑Fp : Set (Point 5)) := by simpa [htcoe] using hspan
  change EuclideanGeometry.Cospherical (↑Fp : Set (Point 5))
  refine ⟨S.circumcenter, S.circumradius, ?_⟩
  intro x hxFp
  have htfFp : tf ⊆ Fp := by
    intro y hy
    exact htFp (htfinite.mem_toFinset.mp hy)
  let Qp : Finset (Point 5) := insert x tf
  have hQpFp : Qp ⊆ Fp := by
    intro y hy
    change y ∈ insert x tf at hy
    rw [Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · exact hxFp
    · exact htfFp hy
  let Q : Finset {x // x ∈ A} := F.filter fun y ↦ (y : Point 5) ∈ Qp
  have hQsub : Q ⊆ F := by
    intro y hy
    exact (Finset.mem_filter.mp hy).1
  have hmapQ : Q.map emb = Qp := by
    ext y
    constructor
    · intro hy
      rw [Finset.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      exact (Finset.mem_filter.mp hz).2
    · intro hy
      have hyFp := hQpFp hy
      change y ∈ F.map emb at hyFp
      rw [Finset.mem_map] at hyFp
      obtain ⟨z, hzF, hzy⟩ := hyFp
      refine Finset.mem_map.mpr ⟨z, Finset.mem_filter.mpr ⟨hzF, ?_⟩, hzy⟩
      have hzy' : (z : Point 5) = y := by simpa [emb] using hzy
      rw [hzy']
      exact hy
  have hQne : Q.Nonempty := by
    rw [← Finset.card_pos, ← Finset.card_map (f := emb), hmapQ]
    exact Finset.card_pos.mpr (Finset.insert_nonempty x tf)
  have hQcard : Q.card ≤ 5 := by
    have hQpCard : Qp.card ≤ tf.card + 1 := Finset.card_insert_le x tf
    have : tf.card ≤ 4 := by rw [htfcard]; omega
    rw [← Finset.card_map (f := emb), hmapQ]
    omega
  obtain ⟨c, r, hc, hQr⟩ := subset_cospherical_center_mem_affineSpan
    P hepsilon hlarge Q (by simpa [F] using hQsub) hQne hQcard
  have hmapQ' : Q.map ⟨Subtype.val, Subtype.val_injective⟩ = Qp := by
    simpa [emb] using hmapQ
  have hQspan : affineSpan ℝ (↑Qp : Set (Point 5)) =
      affineSpan ℝ (↑Fp : Set (Point 5)) := by
    apply le_antisymm
    · exact affineSpan_mono ℝ hQpFp
    · rw [← hspanTf]
      apply affineSpan_mono ℝ
      intro y hy
      exact Finset.mem_insert_of_mem hy
  have hcS : c ∈ affineSpan ℝ (Set.range S.points) := by
    rw [hrangePts, hspanTf, ← hQspan]
    simpa [hmapQ'] using hc
  have hSc : ∀ k, dist (S.points k) c = r := by
    intro k
    apply hQr
    rw [hmapQ']
    apply Finset.mem_insert_of_mem
    exact (e k).2
  have hcEq : c = S.circumcenter := S.eq_circumcenter_of_dist_eq hcS hSc
  have hrEq : r = S.circumradius := by
    have h0 := hSc 0
    rw [hcEq, S.dist_circumcenter_eq_circumradius] at h0
    exact h0.symm
  rw [← hcEq, ← hrEq]
  apply hQr
  rw [hmapQ']
  exact Finset.mem_insert_self x tf

/-- The sound stable-partition shape conclusion in dimension five: every
retained class is a cospherical set of affine dimension at most three. -/
theorem retainedFibers_rank_le_three_and_cospherical
    {A : Finset (Point 5)} {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) 2 epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hlarge : ∀ i : Fin 2,
      5 * ⌈epsilon * (A.card : ℝ)⌉₊ + 3 ≤
        (Stability.retainedFiber P.color P.exceptional i).card) :
    ∀ i : Fin 2,
      Module.finrank ℝ
          (affineSpan ℝ
            (↑((Stability.retainedFiber P.color P.exceptional i).map
              ⟨Subtype.val, Subtype.val_injective⟩) : Set (Point 5))).direction ≤ 3 ∧
        EuclideanGeometry.Cospherical
          (↑((Stability.retainedFiber P.color P.exceptional i).map
            ⟨Subtype.val, Subtype.val_injective⟩) : Set (Point 5)) := by
  intro i
  exact ⟨retainedFiber_affineSpan_finrank_le_three P hepsilon hlarge i,
    retainedFiber_cospherical P hepsilon hlarge i⟩

/-- A convenient real-valued sufficient-size hypothesis implying the exact
ceiling bound in `retainedFibers_rank_le_three_and_cospherical`. -/
theorem retainedFibers_rank_le_three_and_cospherical_of_real_bound
    {A : Finset (Point 5)} {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) 2 epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hnumeric :
      5 * (epsilon * (A.card : ℝ) + 1) + 3 ≤
        (A.card : ℝ) / 2 - epsilon * (A.card : ℝ)) :
    ∀ i : Fin 2,
      Module.finrank ℝ
          (affineSpan ℝ
            (↑((Stability.retainedFiber P.color P.exceptional i).map
              ⟨Subtype.val, Subtype.val_injective⟩) : Set (Point 5))).direction ≤ 3 ∧
        EuclideanGeometry.Cospherical
          (↑((Stability.retainedFiber P.color P.exceptional i).map
            ⟨Subtype.val, Subtype.val_injective⟩) : Set (Point 5)) := by
  apply retainedFibers_rank_le_three_and_cospherical P hepsilon
  intro i
  have hceil : (⌈epsilon * (A.card : ℝ)⌉₊ : ℝ) <
      epsilon * (A.card : ℝ) + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg hepsilon (by positivity))
  have hbal := (abs_lt.mp (P.balanced i)).1
  have hlower : (A.card : ℝ) / 2 - epsilon * (A.card : ℝ) <
      ((Stability.retainedFiber P.color P.exceptional i).card : ℝ) := by
    norm_num at hbal
    linarith
  have hcast : ((5 * ⌈epsilon * (A.card : ℝ)⌉₊ + 3 : ℕ) : ℝ) <
      ((Stability.retainedFiber P.color P.exceptional i).card : ℝ) := by
    norm_num [Nat.cast_add, Nat.cast_mul]
    nlinarith
  exact_mod_cast hcast.le

end

end Erdos223.FiveWeakCarrier
