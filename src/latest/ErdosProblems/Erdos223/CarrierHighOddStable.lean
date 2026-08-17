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

import ErdosProblems.Erdos223.CarrierEven
import ErdosProblems.Erdos223.LocalSphere

/-!
# Stable retained-fiber shape in odd dimensions at least nine

For a stable `p`-partition of a diameter graph in `Point (2 * p + 1)`, with
`p ≥ 4`, every sufficiently large retained fiber is cospherical and has
affine dimension at most three.  The proof extends each five-point subset
to mutually cross-unit selections in all other fibers.  Those foreign
fibers provide `p - 1` pairwise orthogonal affine planes, leaving at most
three ambient dimensions for the distinguished subset.

This module intentionally makes no uniqueness assertion about rank-three
fibers.  A weak odd carrier may have rank three in several fibers while
only a bounded number of off-equator cross pairs are missing.  That defect
is removed later by the extremal weak-to-strong replacement argument.
-/

open scoped EuclideanGeometry RealInnerProductSpace SimpleGraph

namespace Erdos223.HighOddStable

noncomputable section

/-- An orthogonal family consisting of a distinguished subspace and one
subspace of dimension at least two for every other part leaves at most
three dimensions for the distinguished subspace in `Point (2*p+1)`. -/
lemma finrank_le_three_of_orthogonal_planes
    {p : ℕ} (i : Fin p)
    (U : Submodule ℝ (Point (2 * p + 1)))
    (V : {j : Fin p // j ≠ i} → Submodule ℝ (Point (2 * p + 1)))
    (hVrank : ∀ j, 2 ≤ Module.finrank ℝ (V j))
    (hUV : ∀ j, U ⟂ V j)
    (hVV : ∀ j k, j ≠ k → V j ⟂ V k) :
    Module.finrank ℝ U ≤ 3 := by
  let W : Option {j : Fin p // j ≠ i} →
      Submodule ℝ (Point (2 * p + 1))
    | none => U
    | some j => V j
  have hpair : Pairwise (fun a b ↦ W a ⟂ W b) := by
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none => exact (hab rfl).elim
        | some b => exact hUV b
    | some a =>
        cases b with
        | none => exact (hUV a).symm
        | some b =>
            apply hVV a b
            intro h
            apply hab
            exact congrArg some h
  have horth : OrthogonalFamily ℝ (fun a => W a)
      (fun a => (W a).subtypeₗᵢ) := OrthogonalFamily.of_pairwise hpair
  have hinj := horth.independent.dfinsupp_lsum_injective
  have hdim :=
    (DFinsupp.lsum ℕ fun a => (W a).subtype).finrank_le_finrank_of_injective hinj
  change Module.finrank ℝ
      (DirectSum (Option {j : Fin p // j ≠ i}) fun a ↦ W a) ≤
        Module.finrank ℝ (Point (2 * p + 1)) at hdim
  rw [Module.finrank_directSum] at hdim
  have hcard : Fintype.card {j : Fin p // j ≠ i} = p - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    simp
  have hsum : 2 * (p - 1) ≤
      ∑ j : {j : Fin p // j ≠ i}, Module.finrank ℝ (V j) := by
    calc
      2 * (p - 1) = ∑ _j : {j : Fin p // j ≠ i}, 2 := by
        simp [hcard, Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun j _ ↦ hVrank j
  have hamb : Module.finrank ℝ (Point (2 * p + 1)) = 2 * p + 1 := by
    simp [Point]
  have hdim' : Module.finrank ℝ U +
      ∑ j : {j : Fin p // j ≠ i}, Module.finrank ℝ (V j) ≤
        2 * p + 1 := by
    simpa [W, hamb] using hdim
  have htotal : Module.finrank ℝ U + 2 * (p - 1) ≤ 2 * p + 1 :=
    (Nat.add_le_add_left hsum _).trans hdim'
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  omega

private lemma stable_bad_in_foreign_fiber_le
    {p : ℕ} {A : Finset (Point (2 * p + 1))} {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    {i j : Fin p} (hij : i ≠ j)
    {x : {x // x ∈ A}}
    (hx : x ∈ Stability.retainedFiber P.color P.exceptional i) :
    ((((Stability.retainedFiber P.color P.exceptional j).filter
      fun y ↦ ¬ (diameterGraph A).Adj x y).card : ℕ) : ℝ) ≤
        epsilon * A.card := by
  let Bad := (Stability.retainedFiber P.color P.exceptional j).filter
    fun y ↦ ¬ (diameterGraph A).Adj x y
  let R := Stability.retainedCrossNonneighbors (diameterGraph A)
    P.color P.exceptional x
  have hsub : Bad ⊆ R := by
    intro y hy
    have hy' := Finset.mem_filter.mp hy
    have hxi := (Stability.mem_retainedFiber P.color P.exceptional i x).mp hx
    have hyj :=
      (Stability.mem_retainedFiber P.color P.exceptional j y).mp hy'.1
    rw [Stability.mem_retainedCrossNonneighbors]
    exact ⟨hyj.2, by simpa [hxi.1, hyj.1] using hij, hy'.2⟩
  have hcard : (Bad.card : ℝ) ≤ (R.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hsmall := P.crossNonneighbors_small i x hx
  simpa [Bad, R] using hcard.trans hsmall.le

private lemma finrank_affineSpan_eq_two_of_card_three_on_sphere
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : Finset E) (hTcard : T.card = 3) (q : E)
    (hTq : ∀ x ∈ T, dist x q = 1) :
    Module.finrank ℝ (affineSpan ℝ (↑T : Set E)).direction = 2 := by
  classical
  let e : Fin 3 ≃ {x // x ∈ T} := (Finset.equivFinOfCardEq hTcard).symm
  let b : Fin 3 → E := fun i ↦ e i
  have hb_inj : Function.Injective b := by
    intro i j hij
    exact e.injective (Subtype.ext hij)
  have hcos : EuclideanGeometry.Cospherical (↑T : Set E) := ⟨q, 1, hTq⟩
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

private theorem small_subset_geometry
    {p : ℕ} (hp : 4 ≤ p)
    {A : Finset (Point (2 * p + 1))} {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hlarge : ∀ k : Fin p,
      (((p * 5 : ℕ) : ℝ) * (epsilon * A.card) + 5 ≤
        (Stability.retainedFiber P.color P.exceptional k).card))
    {i : Fin p} (Q : Finset {x // x ∈ A})
    (hQsub : Q ⊆ Stability.retainedFiber P.color P.exceptional i)
    (hQne : Q.Nonempty) (hQcard : Q.card ≤ 5) :
    Module.finrank ℝ
        (affineSpan ℝ (↑(Q.map ⟨Subtype.val, Subtype.val_injective⟩) :
          Set (Point (2 * p + 1)))).direction ≤ 3 ∧
      ∃ c : Point (2 * p + 1), ∃ r : ℝ,
        c ∈ affineSpan ℝ
          (↑(Q.map ⟨Subtype.val, Subtype.val_injective⟩) :
            Set (Point (2 * p + 1))) ∧
        ∀ x ∈ Q.map ⟨Subtype.val, Subtype.val_injective⟩, dist x c = r := by
  classical
  let G := diameterGraph A
  let S : Fin p → Finset {x // x ∈ A} :=
    fun k ↦ Stability.retainedFiber P.color P.exceptional k
  let b : ℝ := epsilon * A.card
  have hb : 0 ≤ b := mul_nonneg hepsilon (by positivity)
  have hbad : ∀ k l, k ≠ l → ∀ x ∈ S k,
      ((((S l).filter fun y ↦ ¬ G.Adj x y).card : ℕ) : ℝ) ≤ b := by
    intro k l hkl x hx
    exact stable_bad_in_foreign_fiber_le P hkl hx
  obtain ⟨T, hT, hQT, hcross⟩ :=
    EvenStableSelection.exists_complete_parts_containing
      G S i Q 5 b hb hQsub hQcard (by simpa [S, b] using hlarge) hbad
  let emb : {x // x ∈ A} ↪ Point (2 * p + 1) :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let Qp : Finset (Point (2 * p + 1)) := Q.map emb
  let Tp : Fin p → Finset (Point (2 * p + 1)) := fun k ↦ (T k).map emb
  have hTpcard (k : Fin p) : (Tp k).card = 5 := by
    simpa [Tp, emb] using (hT k).2
  have hQpne : Qp.Nonempty := by
    simpa [Qp, emb] using hQne
  have hTpne (k : Fin p) : (Tp k).Nonempty := by
    rw [← Finset.card_pos, hTpcard]
    decide
  have hcrossTp : ∀ k l, k ≠ l → ∀ x ∈ Tp k, ∀ y ∈ Tp l,
      dist x y = 1 := by
    intro k l hkl x hx y hy
    rw [Finset.mem_map] at hx hy
    obtain ⟨x', hx'T, rfl⟩ := hx
    obtain ⟨y', hy'T, rfl⟩ := hy
    exact (diameterGraph_adj A x' y').mp
      (hcross k l hkl x' hx'T y' hy'T)
  have hcrossQ : ∀ j, i ≠ j → ∀ x ∈ Qp, ∀ y ∈ Tp j,
      dist x y = 1 := by
    intro j hij x hx y hy
    rw [Finset.mem_map] at hx hy
    obtain ⟨x', hx'Q, rfl⟩ := hx
    obtain ⟨y', hy'T, rfl⟩ := hy
    exact (diameterGraph_adj A x' y').mp
      (hcross i j hij x' (hQT hx'Q) y' hy'T)
  let U := (affineSpan ℝ (↑Qp : Set (Point (2 * p + 1)))).direction
  let V : {j : Fin p // j ≠ i} → Submodule ℝ (Point (2 * p + 1)) :=
    fun j ↦ (affineSpan ℝ (↑(Tp j) : Set (Point (2 * p + 1)))).direction
  have hVrank (j : {j : Fin p // j ≠ i}) :
      2 ≤ Module.finrank ℝ (V j) := by
    have hthree : 3 ≤ (Tp j).card := by rw [hTpcard]; omega
    obtain ⟨R, hRT, hRcard⟩ := Finset.exists_subset_card_eq hthree
    obtain ⟨q, hqQ⟩ := hQpne
    have hRrank :
        Module.finrank ℝ
          (affineSpan ℝ (↑R : Set (Point (2 * p + 1)))).direction = 2 := by
      apply finrank_affineSpan_eq_two_of_card_three_on_sphere R hRcard q
      intro y hy
      simpa [dist_comm] using hcrossQ j j.property.symm q hqQ y (hRT hy)
    have hspan : affineSpan ℝ (↑R : Set (Point (2 * p + 1))) ≤
        affineSpan ℝ (↑(Tp j) : Set (Point (2 * p + 1))) :=
      affineSpan_mono ℝ hRT
    calc
      2 = Module.finrank ℝ
          (affineSpan ℝ (↑R : Set (Point (2 * p + 1)))).direction :=
        hRrank.symm
      _ ≤ Module.finrank ℝ
          (affineSpan ℝ (↑(Tp j) : Set (Point (2 * p + 1)))).direction :=
        Submodule.finrank_mono (AffineSubspace.direction_le hspan)
      _ = Module.finrank ℝ (V j) := rfl
  have hUV (j : {j : Fin p // j ≠ i}) : U ⟂ V j := by
    apply affineSpan_direction_isOrtho_of_cross_dist_eq
      hQpne.to_set (hTpne j).to_set 1
    exact hcrossQ j j.property.symm
  have hVV (j k : {j : Fin p // j ≠ i}) (hjk : j ≠ k) : V j ⟂ V k := by
    apply affineSpan_direction_isOrtho_of_cross_dist_eq
      (hTpne j).to_set (hTpne k).to_set 1
    apply hcrossTp j k
    intro h
    apply hjk
    exact Subtype.ext h
  have hQrank : Module.finrank ℝ U ≤ 3 :=
    finrank_le_three_of_orthogonal_planes i U V hVrank hUV hVV
  let j : Fin p := if i.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hij : i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    by_cases hi : i.val = 0
    · simp [j, hi] at hv
    · simp [j, hi] at hv
  obtain ⟨_horth, c, r, _s, hc, _hr0, _hs0, hQr, _hTs, _hrs⟩ :=
    completeBipartiteGeometry hQpne.to_set (hTpne j).to_set
      (hcrossQ j hij)
  refine ⟨?_, ?_⟩
  · simpa [U, Qp, emb] using hQrank
  · refine ⟨c, r, ?_, ?_⟩
    · simpa [Qp, emb] using hc
    · simpa [Qp, emb] using hQr

/-- Every five retained points in one fiber are cospherical and span at
most three affine dimensions. -/
theorem five_point_subset_rank_le_three_and_cospherical
    {p : ℕ} (hp : 4 ≤ p)
    {A : Finset (Point (2 * p + 1))} {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hlarge : ∀ k : Fin p,
      (((p * 5 : ℕ) : ℝ) * (epsilon * A.card) + 5 ≤
        (Stability.retainedFiber P.color P.exceptional k).card))
    {i : Fin p} (Q : Finset {x // x ∈ A})
    (hQsub : Q ⊆ Stability.retainedFiber P.color P.exceptional i)
    (hQcard : Q.card = 5) :
    Module.finrank ℝ
        (affineSpan ℝ (↑(Q.map ⟨Subtype.val, Subtype.val_injective⟩) :
          Set (Point (2 * p + 1)))).direction ≤ 3 ∧
      EuclideanGeometry.Cospherical
        (↑(Q.map ⟨Subtype.val, Subtype.val_injective⟩) :
          Set (Point (2 * p + 1))) := by
  have hQne : Q.Nonempty := by
    rw [← Finset.card_pos, hQcard]
    decide
  obtain ⟨hrank, c, r, _hc, hQr⟩ :=
    small_subset_geometry hp P hepsilon hlarge Q hQsub hQne hQcard.le
  exact ⟨hrank, c, r, hQr⟩

/-- Every sufficiently large retained fiber has affine dimension at most
three. -/
theorem retainedFiber_affineSpan_finrank_le_three
    {p : ℕ} (hp : 4 ≤ p)
    {A : Finset (Point (2 * p + 1))} {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hlarge : ∀ k : Fin p,
      (((p * 5 : ℕ) : ℝ) * (epsilon * A.card) + 5 ≤
        (Stability.retainedFiber P.color P.exceptional k).card))
    (i : Fin p) :
    Module.finrank ℝ
      (affineSpan ℝ
        (↑((Stability.retainedFiber P.color P.exceptional i).map
          ⟨Subtype.val, Subtype.val_injective⟩) :
            Set (Point (2 * p + 1)))).direction ≤ 3 := by
  classical
  let F := Stability.retainedFiber P.color P.exceptional i
  let emb : {x // x ∈ A} ↪ Point (2 * p + 1) :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let Fp : Finset (Point (2 * p + 1)) := F.map emb
  change Module.finrank ℝ
    (affineSpan ℝ (↑Fp : Set (Point (2 * p + 1)))).direction ≤ 3
  by_contra hnot
  have hrank : 4 ≤ Module.finrank ℝ
      (affineSpan ℝ (↑Fp : Set (Point (2 * p + 1)))).direction := by
    omega
  obtain ⟨t, htFp, hspan, htAI⟩ :=
    exists_affineIndependent ℝ (Point (2 * p + 1))
      (↑Fp : Set (Point (2 * p + 1)))
  have htfinite : t.Finite := Fp.finite_toSet.subset htFp
  let tf : Finset (Point (2 * p + 1)) := htfinite.toFinset
  have htne : t.Nonempty := by
    by_contra hne
    have ht0 : t = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hz : Module.finrank ℝ
        (affineSpan ℝ (↑Fp : Set (Point (2 * p + 1)))).direction = 0 := by
      rw [← hspan, ht0]
      simp
    omega
  have htcard : 5 ≤ tf.card := by
    have htfSub : (↑tf : Set (Point (2 * p + 1))) ⊆ t := by
      intro x hx
      exact htfinite.mem_toFinset.mp hx
    have htfAI : AffineIndependent ℝ
        ((↑) : {x // x ∈ tf} → Point (2 * p + 1)) := htAI.mono htfSub
    let : Nonempty {x // x ∈ tf} :=
      ⟨⟨htne.some, htfinite.mem_toFinset.mpr htne.some_mem⟩⟩
    have hdim := htfAI.finrank_vectorSpan_add_one
    have hrange : Set.range ((↑) : {x // x ∈ tf} → Point (2 * p + 1)) =
        (↑tf : Set (Point (2 * p + 1))) := Subtype.range_coe
    have hdim' : Module.finrank ℝ
        (vectorSpan ℝ (↑tf : Set (Point (2 * p + 1)))) + 1 = tf.card := by
      rw [hrange] at hdim
      simpa only [Fintype.card_coe] using hdim
    have htcoe : (↑tf : Set (Point (2 * p + 1))) = t := htfinite.coe_toFinset
    rw [htcoe, ← direction_affineSpan, hspan] at hdim'
    omega
  obtain ⟨Qp, hQptf, hQpcard⟩ := Finset.exists_subset_card_eq htcard
  have hQpt : (↑Qp : Set (Point (2 * p + 1))) ⊆ t := by
    intro x hx
    exact htfinite.mem_toFinset.mp (hQptf hx)
  have hQpFp : Qp ⊆ Fp := by
    intro x hx
    exact htFp (hQpt hx)
  let Q : Finset {x // x ∈ A} := F.filter fun x ↦
    (x : Point (2 * p + 1)) ∈ Qp
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
      have hyx' : (y : Point (2 * p + 1)) = x := by simpa [emb] using hyx
      rw [hyx']
      exact hx
  have hQcard : Q.card = 5 := by
    calc
      Q.card = (Q.map emb).card := by simp
      _ = Qp.card := congrArg Finset.card hmapQ
      _ = 5 := hQpcard
  have hlocal := five_point_subset_rank_le_three_and_cospherical
    hp P hepsilon hlarge Q (by simpa [F] using hQsub) hQcard
  have hmapQ' : Q.map ⟨Subtype.val, Subtype.val_injective⟩ = Qp := by
    simpa [emb] using hmapQ
  have hlocalRank : Module.finrank ℝ
      (affineSpan ℝ (↑Qp : Set (Point (2 * p + 1)))).direction ≤ 3 := by
    rw [← hmapQ']
    exact hlocal.1
  have hQAI : AffineIndependent ℝ
      ((↑) : {x // x ∈ Qp} → Point (2 * p + 1)) := htAI.mono hQpt
  have hQrank : Module.finrank ℝ
      (affineSpan ℝ (↑Qp : Set (Point (2 * p + 1)))).direction = 4 := by
    rw [direction_affineSpan,
      ← @Subtype.range_coe _ (↑Qp : Set (Point (2 * p + 1)))]
    apply hQAI.finrank_vectorSpan
    simpa using hQpcard
  omega

/-- Every sufficiently large retained fiber is globally cospherical.  A
circumcenter of an affine basis is forced to be the center for every further
point by the at-most-five-point geometry theorem. -/
theorem retainedFiber_cospherical
    {p : ℕ} (hp : 4 ≤ p)
    {A : Finset (Point (2 * p + 1))} {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hlarge : ∀ k : Fin p,
      (((p * 5 : ℕ) : ℝ) * (epsilon * A.card) + 5 ≤
        (Stability.retainedFiber P.color P.exceptional k).card))
    (i : Fin p) :
    EuclideanGeometry.Cospherical
      (↑((Stability.retainedFiber P.color P.exceptional i).map
        ⟨Subtype.val, Subtype.val_injective⟩) :
          Set (Point (2 * p + 1))) := by
  classical
  let F := Stability.retainedFiber P.color P.exceptional i
  let emb : {x // x ∈ A} ↪ Point (2 * p + 1) :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let Fp : Finset (Point (2 * p + 1)) := F.map emb
  have hFcard : 5 ≤ F.card := by
    have hs := hlarge i
    have hb : 0 ≤ epsilon * (A.card : ℝ) :=
      mul_nonneg hepsilon (by positivity)
    have hcoef : (0 : ℝ) ≤ p * 5 := by positivity
    have hfiveR : (5 : ℝ) ≤ F.card := by
      dsimp [F]
      nlinarith [mul_nonneg hcoef hb]
    exact_mod_cast hfiveR
  have hFpne : Fp.Nonempty := by
    rw [← Finset.card_pos]
    simpa [Fp, emb] using (show 0 < F.card by omega)
  obtain ⟨t, htFp, hspan, htAI⟩ :=
    exists_affineIndependent ℝ (Point (2 * p + 1))
      (↑Fp : Set (Point (2 * p + 1)))
  have htfinite : t.Finite := Fp.finite_toSet.subset htFp
  let tf : Finset (Point (2 * p + 1)) := htfinite.toFinset
  have htcoe : (↑tf : Set (Point (2 * p + 1))) = t := htfinite.coe_toFinset
  have htfSub : (↑tf : Set (Point (2 * p + 1))) ⊆ t := by simp [htcoe]
  have htfAI : AffineIndependent ℝ
      ((↑) : {x // x ∈ tf} → Point (2 * p + 1)) := htAI.mono htfSub
  have htfne : tf.Nonempty := by
    by_contra hne
    have htf0 : tf = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    obtain ⟨x, hx⟩ := hFpne
    have hxspan : x ∈ affineSpan ℝ (↑Fp : Set (Point (2 * p + 1))) :=
      mem_affineSpan ℝ hx
    rw [← hspan, ← htcoe, htf0] at hxspan
    have hxbot : x ∈ (⊥ : AffineSubspace ℝ (Point (2 * p + 1))) := by
      simpa using hxspan
    exact AffineSubspace.notMem_bot ℝ (Point (2 * p + 1)) x hxbot
  let n := Module.finrank ℝ
    (affineSpan ℝ (↑Fp : Set (Point (2 * p + 1)))).direction
  have htfcard : tf.card = n + 1 := by
    let : Nonempty {x // x ∈ tf} := htfne.to_subtype
    have hdim := htfAI.finrank_vectorSpan_add_one
    have hrange : Set.range ((↑) : {x // x ∈ tf} → Point (2 * p + 1)) =
        (↑tf : Set (Point (2 * p + 1))) := Subtype.range_coe
    rw [hrange] at hdim
    have hspan' : affineSpan ℝ (↑tf : Set (Point (2 * p + 1))) =
        affineSpan ℝ (↑Fp : Set (Point (2 * p + 1))) := by
      simpa [htcoe] using hspan
    rw [← direction_affineSpan, hspan'] at hdim
    simpa [n] using hdim.symm
  have hnle : n ≤ 3 := by
    exact retainedFiber_affineSpan_finrank_le_three hp P hepsilon hlarge i
  let e : Fin (n + 1) ≃ {x // x ∈ tf} :=
    (Finset.equivFinOfCardEq htfcard).symm
  let pts : Fin (n + 1) → Point (2 * p + 1) := fun k ↦ e k
  have hptsAI : AffineIndependent ℝ pts :=
    htfAI.comp_embedding e.toEmbedding
  let simplex : Affine.Simplex ℝ (Point (2 * p + 1)) n := ⟨pts, hptsAI⟩
  have hrangePts : Set.range simplex.points =
      (↑tf : Set (Point (2 * p + 1))) := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact (e k).2
    · intro hx
      obtain ⟨k, hk⟩ := e.surjective ⟨x, hx⟩
      exact ⟨k, congrArg Subtype.val hk⟩
  have hspanTf : affineSpan ℝ (↑tf : Set (Point (2 * p + 1))) =
      affineSpan ℝ (↑Fp : Set (Point (2 * p + 1))) := by
    simpa [htcoe] using hspan
  change EuclideanGeometry.Cospherical
    (↑Fp : Set (Point (2 * p + 1)))
  refine ⟨simplex.circumcenter, simplex.circumradius, ?_⟩
  intro x hxFp
  have htfFp : tf ⊆ Fp := by
    intro y hy
    exact htFp (htfinite.mem_toFinset.mp hy)
  let Qp : Finset (Point (2 * p + 1)) := insert x tf
  have hQpFp : Qp ⊆ Fp := by
    intro y hy
    change y ∈ insert x tf at hy
    rw [Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · exact hxFp
    · exact htfFp hy
  let Q : Finset {x // x ∈ A} := F.filter fun y ↦
    (y : Point (2 * p + 1)) ∈ Qp
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
      have hzy' : (z : Point (2 * p + 1)) = y := by simpa [emb] using hzy
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
  obtain ⟨_hrank, c, r, hc, hQr⟩ := small_subset_geometry
    hp P hepsilon hlarge Q (by simpa [F] using hQsub) hQne hQcard
  have hmapQ' : Q.map ⟨Subtype.val, Subtype.val_injective⟩ = Qp := by
    simpa [emb] using hmapQ
  have hQspan : affineSpan ℝ (↑Qp : Set (Point (2 * p + 1))) =
      affineSpan ℝ (↑Fp : Set (Point (2 * p + 1))) := by
    apply le_antisymm
    · exact affineSpan_mono ℝ hQpFp
    · rw [← hspanTf]
      apply affineSpan_mono ℝ
      intro y hy
      exact Finset.mem_insert_of_mem hy
  have hcS : c ∈ affineSpan ℝ (Set.range simplex.points) := by
    rw [hrangePts, hspanTf, ← hQspan]
    simpa [hmapQ'] using hc
  have hSc : ∀ k, dist (simplex.points k) c = r := by
    intro k
    apply hQr
    rw [hmapQ']
    apply Finset.mem_insert_of_mem
    exact (e k).2
  have hcEq : c = simplex.circumcenter :=
    simplex.eq_circumcenter_of_dist_eq hcS hSc
  have hrEq : r = simplex.circumradius := by
    have h0 := hSc 0
    rw [hcEq, simplex.dist_circumcenter_eq_circumradius] at h0
    exact h0.symm
  rw [← hcEq, ← hrEq]
  apply hQr
  rw [hmapQ']
  exact Finset.mem_insert_self x tf

/-- Stable high-odd retained-fiber shape: every retained class is
cospherical and has affine dimension at most three. -/
theorem retainedFibers_rank_le_three_and_cospherical
    {p : ℕ} (hp : 4 ≤ p)
    {A : Finset (Point (2 * p + 1))} {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hlarge : ∀ k : Fin p,
      (((p * 5 : ℕ) : ℝ) * (epsilon * A.card) + 5 ≤
        (Stability.retainedFiber P.color P.exceptional k).card)) :
    ∀ i : Fin p,
      Module.finrank ℝ
          (affineSpan ℝ
            (↑((Stability.retainedFiber P.color P.exceptional i).map
              ⟨Subtype.val, Subtype.val_injective⟩) :
                Set (Point (2 * p + 1)))).direction ≤ 3 ∧
        EuclideanGeometry.Cospherical
          (↑((Stability.retainedFiber P.color P.exceptional i).map
            ⟨Subtype.val, Subtype.val_injective⟩) :
              Set (Point (2 * p + 1))) := by
  intro i
  exact ⟨retainedFiber_affineSpan_finrank_le_three hp P hepsilon hlarge i,
    retainedFiber_cospherical hp P hepsilon hlarge i⟩

/-- A balanced-partition numerical condition implying the fiberwise size
hypothesis of `retainedFibers_rank_le_three_and_cospherical`. -/
theorem retainedFibers_rank_le_three_and_cospherical_of_real_bound
    {p : ℕ} (hp : 4 ≤ p)
    {A : Finset (Point (2 * p + 1))} {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hnumeric :
      (5 * (p : ℝ)) * (epsilon * A.card) + 5 ≤
        (A.card : ℝ) / p - epsilon * A.card) :
    ∀ i : Fin p,
      Module.finrank ℝ
          (affineSpan ℝ
            (↑((Stability.retainedFiber P.color P.exceptional i).map
              ⟨Subtype.val, Subtype.val_injective⟩) :
                Set (Point (2 * p + 1)))).direction ≤ 3 ∧
        EuclideanGeometry.Cospherical
          (↑((Stability.retainedFiber P.color P.exceptional i).map
            ⟨Subtype.val, Subtype.val_injective⟩) :
              Set (Point (2 * p + 1))) := by
  apply retainedFibers_rank_le_three_and_cospherical hp P hepsilon
  intro i
  have hbal : -(epsilon * (A.card : ℝ)) <
      ((Stability.retainedFiber P.color P.exceptional i).card : ℝ) -
        (A.card : ℝ) / p := by
    simpa using (abs_lt.mp (P.balanced i)).1
  have hlower : (A.card : ℝ) / p - epsilon * A.card <
      ((Stability.retainedFiber P.color P.exceptional i).card : ℝ) := by
    linarith
  have hcoef : (((p * 5 : ℕ) : ℝ)) = 5 * (p : ℝ) := by
    norm_num [Nat.cast_mul]
    ring
  rw [hcoef]
  exact hnumeric.trans hlower.le

end

end Erdos223.HighOddStable
