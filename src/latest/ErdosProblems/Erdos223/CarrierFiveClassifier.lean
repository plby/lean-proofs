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

import ErdosProblems.Erdos223.CarrierFiveStable
import ErdosProblems.Erdos223.CarrierFiveCompletion

/-!
# Classification of stable five-dimensional retained cores

The stable-partition shape theorem leaves four possible affine-rank pairs.
This module treats all four, including the genuine rank-three/rank-three weak
case.  Interlocking four-point and three-point anchors construct one shifted
weak carrier containing both retained fibers in its crossed spheres.
-/

open scoped EuclideanGeometry RealInnerProductSpace SimpleGraph

namespace Erdos223.FiveWeakCarrier

noncomputable section

private theorem exists_affineBasis_finset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Finset E) (hFne : F.Nonempty) (n : ℕ)
    (hdim : Module.finrank ℝ (affineSpan ℝ (↑F : Set E)).direction = n) :
    ∃ a : Fin (n + 1) → E,
      AffineIndependent ℝ a ∧ Set.range a ⊆ (↑F : Set E) ∧
      affineSpan ℝ (Set.range a) = affineSpan ℝ (↑F : Set E) := by
  classical
  obtain ⟨t, htF, hspan, htAI⟩ := exists_affineIndependent ℝ E (↑F : Set E)
  have htfinite : t.Finite := F.finite_toSet.subset htF
  let tf : Finset E := htfinite.toFinset
  have htcoe : (↑tf : Set E) = t := htfinite.coe_toFinset
  have htfSub : (↑tf : Set E) ⊆ t := by simpa [htcoe]
  have htfAI : AffineIndependent ℝ ((↑) : {x // x ∈ tf} → E) := htAI.mono htfSub
  have htfne : tf.Nonempty := by
    by_contra hne
    have htf0 : tf = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    obtain ⟨x, hx⟩ := hFne
    have hxspan : x ∈ affineSpan ℝ (↑F : Set E) := mem_affineSpan ℝ hx
    rw [← hspan, ← htcoe, htf0] at hxspan
    have hxbot : x ∈ (⊥ : AffineSubspace ℝ E) := by simpa using hxspan
    exact AffineSubspace.notMem_bot ℝ E x hxbot
  have htfcard : tf.card = n + 1 := by
    letI : Nonempty {x // x ∈ tf} := htfne.to_subtype
    have h := htfAI.finrank_vectorSpan_add_one
    have hrange : Set.range ((↑) : {x // x ∈ tf} → E) = (↑tf : Set E) :=
      Subtype.range_coe
    rw [hrange] at h
    have hspan' : affineSpan ℝ (↑tf : Set E) = affineSpan ℝ (↑F : Set E) := by
      simpa [htcoe] using hspan
    rw [← direction_affineSpan, hspan', hdim] at h
    simpa using h.symm
  let e : Fin (n + 1) ≃ {x // x ∈ tf} := (Finset.equivFinOfCardEq htfcard).symm
  let a : Fin (n + 1) → E := fun i ↦ e i
  have ha : AffineIndependent ℝ a := htfAI.comp_embedding e.toEmbedding
  have harange : Set.range a = (↑tf : Set E) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hx
      obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  refine ⟨a, ha, ?_, ?_⟩
  · rw [harange, htcoe]
    exact htF
  · rw [harange, htcoe]
    exact hspan

private theorem subset_affineSphere_of_cospherical_anchor
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {F : Set E} (hFcos : EuclideanGeometry.Cospherical F)
    (n : ℕ) (hFdim : Module.finrank ℝ (affineSpan ℝ F).direction = n)
    (a : Fin (n + 1) → E) (ha : AffineIndependent ℝ a)
    (haF : Set.range a ⊆ F)
    (P : AffineSubspace ℝ E) (c : E) (R : ℝ)
    (hPdim : Module.finrank ℝ P.direction = n) (hcP : c ∈ P)
    (hamem : ∀ i, a i ∈ P ∧ dist (a i) c = R) :
    ∀ x ∈ F, x ∈ P ∧ dist x c = R := by
  have hspanAP : affineSpan ℝ (Set.range a) = P := by
    apply ha.affineSpan_eq_of_le_of_card_eq_finrank_add_one
    · apply affineSpan_le.2
      rintro _ ⟨i, rfl⟩
      exact (hamem i).1
    · rw [hPdim]
      norm_num
  have hspanAF : affineSpan ℝ (Set.range a) = affineSpan ℝ F := by
    have hle := affineSpan_mono ℝ haF
    have hdirle := AffineSubspace.direction_le hle
    have hdimeq : Module.finrank ℝ (affineSpan ℝ (Set.range a)).direction = n := by
      rw [direction_affineSpan]
      exact ha.finrank_vectorSpan (by norm_num)
    have hdirEq : (affineSpan ℝ (Set.range a)).direction =
        (affineSpan ℝ F).direction := by
      apply Submodule.eq_of_le_of_finrank_eq hdirle
      rw [hdimeq, hFdim]
    exact AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdirEq
      ⟨a 0, mem_affineSpan ℝ (Set.mem_range_self 0)⟩ hle
  have hPF : P = affineSpan ℝ F := hspanAP.symm.trans hspanAF
  have hFne : F.Nonempty := ⟨a 0, haF (Set.mem_range_self 0)⟩
  let _ : Nonempty (affineSpan ℝ F) :=
    ⟨⟨a 0, mem_affineSpan ℝ (haF (Set.mem_range_self 0))⟩⟩
  obtain ⟨cF, hcF, rF, hFr⟩ :=
    (EuclideanGeometry.cospherical_iff_exists_mem_of_finiteDimensional
      (subset_affineSpan ℝ F)).mp hFcos
  let S : Affine.Simplex ℝ E n := ⟨a, ha⟩
  have hcCirc : c = S.circumcenter := by
    apply S.eq_circumcenter_of_dist_eq
    · rw [show affineSpan ℝ (Set.range S.points) = P by simpa [S] using hspanAP]
      exact hcP
    · intro i
      simpa [S] using (hamem i).2
  have hcFCirc : cF = S.circumcenter := by
    apply S.eq_circumcenter_of_dist_eq
    · rw [show affineSpan ℝ (Set.range S.points) = affineSpan ℝ F by
          simpa [S] using hspanAF]
      exact hcF
    · intro i
      simpa [S] using hFr (a i) (haF (Set.mem_range_self i))
  have hrEq : rF = R := by
    have h1 := hFr (a 0) (haF (Set.mem_range_self 0))
    have h2 := (hamem 0).2
    rw [hcFCirc, ← hcCirc] at h1
    linarith
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [hPF]
    exact mem_affineSpan ℝ hx
  · rw [← hrEq, hcCirc.trans hcFCirc.symm]
    exact hFr x hx

private theorem subset_firstCircle_of_rank_two_anchor
    (C : Carrier) {F : Set (Point 5)}
    (hFcos : EuclideanGeometry.Cospherical F)
    (hFdim : Module.finrank ℝ (affineSpan ℝ F).direction = 2)
    (a : Fin 3 → Point 5) (ha : AffineIndependent ℝ a)
    (haF : Set.range a ⊆ F) (hamem : ∀ i, a i ∈ C.firstCircle) :
    F ⊆ C.firstCircle := by
  intro x hx
  exact subset_affineSphere_of_cospherical_anchor hFcos 2 hFdim a ha haF
    C.firstPlane C.firstCenter C.firstRadius C.first_finrank C.firstCenter_mem
    hamem x hx

private theorem subset_secondCircle_of_rank_two_anchor
    (C : Carrier) {F : Set (Point 5)}
    (hFcos : EuclideanGeometry.Cospherical F)
    (hFdim : Module.finrank ℝ (affineSpan ℝ F).direction = 2)
    (a : Fin 3 → Point 5) (ha : AffineIndependent ℝ a)
    (haF : Set.range a ⊆ F) (hamem : ∀ i, a i ∈ C.secondCircle) :
    F ⊆ C.secondCircle := by
  intro x hx
  exact subset_affineSphere_of_cospherical_anchor hFcos 2 hFdim a ha haF
    C.secondPlane C.secondCenter C.secondRadius C.second_finrank C.secondCenter_mem
    hamem x hx

private theorem subset_firstSphere_of_rank_three_anchor
    (C : Carrier) {F : Set (Point 5)}
    (hFcos : EuclideanGeometry.Cospherical F)
    (hFdim : Module.finrank ℝ (affineSpan ℝ F).direction = 3)
    (a : Fin 4 → Point 5) (ha : AffineIndependent ℝ a)
    (haF : Set.range a ⊆ F) (hamem : ∀ i, a i ∈ C.firstSphere) :
    F ⊆ C.firstSphere := by
  let P : AffineSubspace ℝ (Point 5) :=
    AffineSubspace.mk' C.secondCenter C.secondPlane.directionᗮ
  have hPdim : Module.finrank ℝ P.direction = 3 := by
    rw [show P.direction = C.secondPlane.directionᗮ by simp [P]]
    have h := C.secondPlane.direction.finrank_add_finrank_orthogonal
    rw [C.second_finrank] at h
    have hamb : Module.finrank ℝ (Point 5) = 5 := by simp
    rw [hamb] at h
    omega
  have hcP : C.secondCenter ∈ P := AffineSubspace.self_mem_mk' _ _
  intro x hx
  exact subset_affineSphere_of_cospherical_anchor hFcos 3 hFdim a ha haF P
    C.secondCenter C.firstSphereRadius hPdim hcP hamem x hx

private theorem subset_secondSphere_of_rank_three_anchor
    (C : Carrier) {F : Set (Point 5)}
    (hFcos : EuclideanGeometry.Cospherical F)
    (hFdim : Module.finrank ℝ (affineSpan ℝ F).direction = 3)
    (a : Fin 4 → Point 5) (ha : AffineIndependent ℝ a)
    (haF : Set.range a ⊆ F) (hamem : ∀ i, a i ∈ C.secondSphere) :
    F ⊆ C.secondSphere := by
  let P : AffineSubspace ℝ (Point 5) :=
    AffineSubspace.mk' C.firstCenter C.firstPlane.directionᗮ
  have hPdim : Module.finrank ℝ P.direction = 3 := by
    rw [show P.direction = C.firstPlane.directionᗮ by simp [P]]
    have h := C.firstPlane.direction.finrank_add_finrank_orthogonal
    rw [C.first_finrank] at h
    have hamb : Module.finrank ℝ (Point 5) = 5 := by simp
    rw [hamb] at h
    omega
  have hcP : C.firstCenter ∈ P := AffineSubspace.self_mem_mk' _ _
  intro x hx
  exact subset_affineSphere_of_cospherical_anchor hFcos 3 hFdim a ha haF P
    C.firstCenter C.secondSphereRadius hPdim hcP hamem x hx

/-- Quantitative stability forces every retained fiber to have affine rank
exactly two or three.  Rank one is excluded by any three retained vertices:
the common-neighbor lemma puts them on one nondegenerate sphere. -/
theorem retainedFiber_finrank_eq_two_or_three
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
            ⟨Subtype.val, Subtype.val_injective⟩) : Set (Point 5))).direction = 2 ∨
      Module.finrank ℝ
        (affineSpan ℝ
          (↑((Stability.retainedFiber P.color P.exceptional i).map
            ⟨Subtype.val, Subtype.val_injective⟩) : Set (Point 5))).direction = 3 := by
  classical
  let F := Stability.retainedFiber P.color P.exceptional i
  have hFcard : 3 ≤ F.card :=
    (show 3 ≤ 5 * ⌈epsilon * (A.card : ℝ)⌉₊ + 3 by omega).trans (hlarge i)
  obtain ⟨Q, hQsub, hQcard⟩ := Finset.exists_subset_card_eq hFcard
  let j : Fin 2 := if i = 0 then 1 else 0
  have hij : i ≠ j := by fin_cases i <;> simp [j]
  obtain ⟨T, hTsub, hTcard, hcross⟩ :=
    exists_three_common_cross_neighbors (diameterGraph A) P hepsilon hij Q
      (by simpa [F] using hQsub) (by omega) (by simpa using hlarge j)
  let eQ : Fin 3 ≃ {x // x ∈ Q} := (Finset.equivFinOfCardEq hQcard).symm
  let eT : Fin 3 ≃ {x // x ∈ T} := (Finset.equivFinOfCardEq hTcard).symm
  let a : Fin 3 → Point 5 := fun k ↦ (eQ k).1
  let b : Fin 3 → Point 5 := fun k ↦ (eT k).1
  have haInj : Function.Injective a := by
    intro k l hkl
    exact eQ.injective (Subtype.ext (Subtype.ext hkl))
  have hcos : EuclideanGeometry.Cospherical (Set.range a) := by
    refine ⟨b 0, 1, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact (diameterGraph_adj A (eQ k).1 (eT 0).1).1
      (hcross (eQ k).1 (eQ k).2 (eT 0).1 (eT 0).2)
  have ha : AffineIndependent ℝ a :=
    hcos.affineIndependent Set.Subset.rfl haInj
  have harank : Module.finrank ℝ
      (affineSpan ℝ (Set.range a)).direction = 2 := by
    rw [direction_affineSpan]
    exact ha.finrank_vectorSpan (by norm_num)
  let emb : {x // x ∈ A} ↪ Point 5 := ⟨Subtype.val, Subtype.val_injective⟩
  let Fp : Finset (Point 5) := F.map emb
  have haF : Set.range a ⊆ (↑Fp : Set (Point 5)) := by
    rintro _ ⟨k, rfl⟩
    apply Finset.mem_map.mpr
    exact ⟨(eQ k).1, hQsub (eQ k).2, rfl⟩
  have hle := AffineSubspace.direction_le (affineSpan_mono ℝ haF)
  have hlower : 2 ≤ Module.finrank ℝ (affineSpan ℝ (↑Fp : Set (Point 5))).direction := by
    rw [← harank]
    exact Submodule.finrank_mono hle
  have hupper : Module.finrank ℝ
      (affineSpan ℝ (↑Fp : Set (Point 5))).direction ≤ 3 := by
    simpa [Fp, F, emb] using
      retainedFiber_affineSpan_finrank_le_three P hepsilon hlarge i
  change Module.finrank ℝ (affineSpan ℝ (↑Fp : Set (Point 5))).direction = 2 ∨
    Module.finrank ℝ (affineSpan ℝ (↑Fp : Set (Point 5))).direction = 3
  omega

private theorem exists_affineIndependent_four_extending_three
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Finset E)
    (hFdim : Module.finrank ℝ (affineSpan ℝ (↑F : Set E)).direction = 3)
    (b : Fin 3 → E) (hb : AffineIndependent ℝ b)
    (hbF : Set.range b ⊆ (↑F : Set E)) :
    ∃ b4 : Fin 4 → E, AffineIndependent ℝ b4 ∧
      Set.range b4 ⊆ (↑F : Set E) ∧ Set.range b ⊆ Set.range b4 := by
  classical
  have hbrank : Module.finrank ℝ (affineSpan ℝ (Set.range b)).direction = 2 := by
    rw [direction_affineSpan]
    exact hb.finrank_vectorSpan (by norm_num)
  have hex : ∃ y ∈ F, y ∉ affineSpan ℝ (Set.range b) := by
    by_contra hnot
    push Not at hnot
    have hFle : affineSpan ℝ (↑F : Set E) ≤ affineSpan ℝ (Set.range b) := by
      apply affineSpan_le.2
      intro y hy
      exact hnot y hy
    have hble : affineSpan ℝ (Set.range b) ≤ affineSpan ℝ (↑F : Set E) :=
      affineSpan_mono ℝ hbF
    have heq := le_antisymm hFle hble
    have := congrArg (fun S : AffineSubspace ℝ E ↦ Module.finrank ℝ S.direction) heq
    rw [hFdim, hbrank] at this
    omega
  obtain ⟨y, hyF, hyout⟩ := hex
  let b4 : Fin 4 → E := Fin.cases y b
  have hbRange : Set.range b ⊆ Set.range b4 := by
    intro z hz
    obtain ⟨i, rfl⟩ := hz
    exact ⟨Fin.succ i, by simp [b4]⟩
  have hyRange : y ∈ Set.range b4 := ⟨0, rfl⟩
  have hle : affineSpan ℝ (Set.range b) ≤ affineSpan ℝ (Set.range b4) :=
    affineSpan_mono ℝ hbRange
  have hlt : affineSpan ℝ (Set.range b) < affineSpan ℝ (Set.range b4) := by
    refine lt_of_le_of_ne hle ?_
    intro heq
    apply hyout
    rw [heq]
    exact mem_affineSpan ℝ hyRange
  have hdirlt := AffineSubspace.direction_lt_of_nonempty hlt
    ⟨b 0, mem_affineSpan ℝ (Set.mem_range_self 0)⟩
  have hranklt := Submodule.finrank_lt_finrank_of_lt hdirlt
  have hrankle : Module.finrank ℝ (vectorSpan ℝ (Set.range b4)) ≤ 3 :=
    finrank_vectorSpan_range_le ℝ b4 (by norm_num)
  have hb4rank : Module.finrank ℝ (vectorSpan ℝ (Set.range b4)) = 3 := by
    rw [hbrank, direction_affineSpan] at hranklt
    omega
  have hb4 : AffineIndependent ℝ b4 :=
    (affineIndependent_iff_finrank_vectorSpan_eq ℝ b4 (by norm_num)).2 hb4rank
  refine ⟨b4, hb4, ?_, hbRange⟩
  rintro z ⟨i, rfl⟩
  refine Fin.cases hyF ?_ i
  intro k
  exact hbF (Set.mem_range_self k)

private theorem exists_cross_unit_triple_of_point_subset
    {A : Finset (Point 5)} {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) 2 epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hlarge : ∀ i : Fin 2,
      5 * ⌈epsilon * (A.card : ℝ)⌉₊ + 3 ≤
        (Stability.retainedFiber P.color P.exceptional i).card)
    {i j : Fin 2} (hij : i ≠ j)
    (Qp : Finset (Point 5)) (hQpne : Qp.Nonempty)
    (hQpsub : Qp ⊆
      (Stability.retainedFiber P.color P.exceptional i).map
        ⟨Subtype.val, Subtype.val_injective⟩)
    (hQpcard : Qp.card ≤ 5) :
    ∃ b : Fin 3 → Point 5,
      AffineIndependent ℝ b ∧
      Set.range b ⊆
        (↑((Stability.retainedFiber P.color P.exceptional j).map
          ⟨Subtype.val, Subtype.val_injective⟩) : Set (Point 5)) ∧
      ∀ x ∈ Qp, ∀ k, dist x (b k) = 1 := by
  classical
  let Fi := Stability.retainedFiber P.color P.exceptional i
  let Fj := Stability.retainedFiber P.color P.exceptional j
  let emb : {x // x ∈ A} ↪ Point 5 := ⟨Subtype.val, Subtype.val_injective⟩
  let Q : Finset {x // x ∈ A} := Fi.filter fun x ↦ (x : Point 5) ∈ Qp
  have hmapQ : Q.map emb = Qp := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact (Finset.mem_filter.mp hy).2
    · intro hx
      have hxFi := hQpsub hx
      change x ∈ Fi.map emb at hxFi
      rw [Finset.mem_map] at hxFi
      obtain ⟨y, hyFi, hyx⟩ := hxFi
      refine Finset.mem_map.mpr ⟨y, Finset.mem_filter.mpr ⟨hyFi, ?_⟩, hyx⟩
      have hyx' : (y : Point 5) = x := by simpa [emb] using hyx
      rw [hyx']
      exact hx
  have hQsub : Q ⊆ Fi := fun _ hx ↦ (Finset.mem_filter.mp hx).1
  have hQcard : Q.card ≤ 5 := by
    rw [← Finset.card_map (f := emb), hmapQ]
    exact hQpcard
  obtain ⟨T, hTsub, hTcard, hcross⟩ :=
    exists_three_common_cross_neighbors (diameterGraph A) P hepsilon hij Q
      (by simpa [Fi] using hQsub) hQcard (by simpa using hlarge j)
  let eT : Fin 3 ≃ {x // x ∈ T} := (Finset.equivFinOfCardEq hTcard).symm
  let b : Fin 3 → Point 5 := fun k ↦ (eT k).1
  have hbInj : Function.Injective b := by
    intro k l hkl
    exact eT.injective (Subtype.ext (Subtype.ext hkl))
  obtain ⟨q, hq⟩ := hQpne
  have hqQ : q ∈ Q.map emb := by simpa [hmapQ] using hq
  rw [Finset.mem_map] at hqQ
  obtain ⟨qv, hqvQ, hqveq⟩ := hqQ
  have hqveq' : (qv : Point 5) = q := by simpa [emb] using hqveq
  have hbcos : EuclideanGeometry.Cospherical (Set.range b) := by
    refine ⟨q, 1, ?_⟩
    rintro _ ⟨k, rfl⟩
    have hd := (diameterGraph_adj A qv (eT k).1).1
      (hcross qv hqvQ (eT k).1 (eT k).2)
    simpa [b, hqveq', dist_comm] using hd
  have hb : AffineIndependent ℝ b :=
    hbcos.affineIndependent Set.Subset.rfl hbInj
  refine ⟨b, hb, ?_, ?_⟩
  · rintro _ ⟨k, rfl⟩
    apply Finset.mem_map.mpr
    exact ⟨(eT k).1, hTsub (eT k).2, rfl⟩
  · intro x hx k
    have hxQ : x ∈ Q.map emb := by simpa [hmapQ] using hx
    rw [Finset.mem_map] at hxQ
    obtain ⟨xv, hxvQ, hxveq⟩ := hxQ
    have hxveq' : (xv : Point 5) = x := by simpa [emb] using hxveq
    have hd := (diameterGraph_adj A xv (eT k).1).1
      (hcross xv hxvQ (eT k).1 (eT k).2)
    simpa [b, hxveq'] using hd

/-- Every sufficiently large stable two-class core in dimension five lies in
one faithful weak carrier.  The proof handles all four possible affine-rank
pairs, including the genuine rank-three/rank-three weak branch. -/
theorem exists_carrier_of_stablePartition_retained_core
    {A : Finset (Point 5)} {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) 2 epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hlarge : ∀ i : Fin 2,
      5 * ⌈epsilon * (A.card : ℝ)⌉₊ + 3 ≤
        (Stability.retainedFiber P.color P.exceptional i).card) :
    ∃ C : Carrier,
      (∀ v ∈ Stability.retainedFiber P.color P.exceptional 0,
        (v : Point 5) ∈ C.firstSphere) ∧
      ∀ v ∈ Stability.retainedFiber P.color P.exceptional 1,
        (v : Point 5) ∈ C.secondSphere := by
  classical
  let F0 := Stability.retainedFiber P.color P.exceptional (0 : Fin 2)
  let F1 := Stability.retainedFiber P.color P.exceptional (1 : Fin 2)
  let emb : {x // x ∈ A} ↪ Point 5 := ⟨Subtype.val, Subtype.val_injective⟩
  let X0 : Finset (Point 5) := F0.map emb
  let X1 : Finset (Point 5) := F1.map emb
  have hF0card : 3 ≤ F0.card :=
    (show 3 ≤ 5 * ⌈epsilon * (A.card : ℝ)⌉₊ + 3 by omega).trans (hlarge 0)
  have hF1card : 3 ≤ F1.card :=
    (show 3 ≤ 5 * ⌈epsilon * (A.card : ℝ)⌉₊ + 3 by omega).trans (hlarge 1)
  have hX0ne : X0.Nonempty := by
    rw [← Finset.card_pos]
    simpa [X0, F0, emb] using (show 0 < F0.card by omega)
  have hX1ne : X1.Nonempty := by
    rw [← Finset.card_pos]
    simpa [X1, F1, emb] using (show 0 < F1.card by omega)
  have hX0cos : EuclideanGeometry.Cospherical (↑X0 : Set (Point 5)) := by
    simpa [X0, F0, emb] using retainedFiber_cospherical P hepsilon hlarge 0
  have hX1cos : EuclideanGeometry.Cospherical (↑X1 : Set (Point 5)) := by
    simpa [X1, F1, emb] using retainedFiber_cospherical P hepsilon hlarge 1
  have hdim0 := retainedFiber_finrank_eq_two_or_three P hepsilon hlarge 0
  have hdim1 := retainedFiber_finrank_eq_two_or_three P hepsilon hlarge 1
  change (Module.finrank ℝ (affineSpan ℝ (↑X0 : Set (Point 5))).direction = 2 ∨
      Module.finrank ℝ (affineSpan ℝ (↑X0 : Set (Point 5))).direction = 3) at hdim0
  change (Module.finrank ℝ (affineSpan ℝ (↑X1 : Set (Point 5))).direction = 2 ∨
      Module.finrank ℝ (affineSpan ℝ (↑X1 : Set (Point 5))).direction = 3) at hdim1
  rcases hdim0 with h02 | h03
  · rcases hdim1 with h12 | h13
    · -- rank two / rank two
      obtain ⟨a, ha, haX0, _haSpan⟩ := exists_affineBasis_finset X0 hX0ne 2 h02
      let Qa : Finset (Point 5) := Finset.univ.image a
      have hQaCard : Qa.card = 3 := by
        change (Finset.univ.image a).card = 3
        rw [Finset.card_image_of_injective _ ha.injective]
        simp
      have hQaNe : Qa.Nonempty := by rw [← Finset.card_pos, hQaCard]; decide
      have hQaX0 : Qa ⊆ X0 := by
        intro x hx
        change x ∈ Finset.univ.image a at hx
        rw [Finset.mem_image] at hx
        obtain ⟨i, _hi, rfl⟩ := hx
        exact haX0 (Set.mem_range_self i)
      obtain ⟨b, hb, hbX1, hab⟩ := exists_cross_unit_triple_of_point_subset
        P hepsilon hlarge (by decide : (0 : Fin 2) ≠ 1) Qa hQaNe
        (by simpa [X0, F0, emb] using hQaX0) (by omega)
      have hcross : ∀ i j, dist (a i) (b j) = 1 := by
        intro i j
        apply hab (a i)
        simp [Qa]
      obtain ⟨C, haC, hbC, _hfirst, _hsecond⟩ :=
        exists_carrier_of_cross_unit_triples_with_completion a b ha hb hcross
      have hX0circle : (↑X0 : Set (Point 5)) ⊆ C.firstCircle :=
        subset_firstCircle_of_rank_two_anchor C hX0cos h02 a ha haX0 haC
      have hX1circle : (↑X1 : Set (Point 5)) ⊆ C.secondCircle :=
        subset_secondCircle_of_rank_two_anchor C hX1cos h12 b hb hbX1 hbC
      refine ⟨C, ?_, ?_⟩
      · intro v hv
        apply C.firstCircle_subset_firstSphere
        apply hX0circle
        exact Finset.mem_map.mpr ⟨v, by simpa [F0] using hv, rfl⟩
      · intro v hv
        apply C.secondCircle_subset_secondSphere
        apply hX1circle
        exact Finset.mem_map.mpr ⟨v, by simpa [F1] using hv, rfl⟩
    · -- rank two / rank three
      obtain ⟨b4, hb4, hb4X1, _hb4Span⟩ := exists_affineBasis_finset X1 hX1ne 3 h13
      let Qb : Finset (Point 5) := Finset.univ.image b4
      have hQbCard : Qb.card = 4 := by
        change (Finset.univ.image b4).card = 4
        rw [Finset.card_image_of_injective _ hb4.injective]
        simp
      have hQbNe : Qb.Nonempty := by rw [← Finset.card_pos, hQbCard]; decide
      have hQbX1 : Qb ⊆ X1 := by
        intro x hx
        change x ∈ Finset.univ.image b4 at hx
        rw [Finset.mem_image] at hx
        obtain ⟨i, _hi, rfl⟩ := hx
        exact hb4X1 (Set.mem_range_self i)
      obtain ⟨a, ha, haX0, hba⟩ := exists_cross_unit_triple_of_point_subset
        P hepsilon hlarge (by decide : (1 : Fin 2) ≠ 0) Qb hQbNe
        (by simpa [X1, F1, emb] using hQbX1) (by omega)
      let b : Fin 3 → Point 5 := fun i ↦ b4 i.castSucc
      have hb : AffineIndependent ℝ b := hb4.comp_embedding Fin.castSuccEmb
      have hbX1 : Set.range b ⊆ (↑X1 : Set (Point 5)) := by
        rintro _ ⟨i, rfl⟩
        exact hb4X1 (Set.mem_range_self i.castSucc)
      have hcross : ∀ i j, dist (a i) (b j) = 1 := by
        intro i j
        simpa [b, dist_comm] using hba (b4 j.castSucc) (by simp [Qb]) i
      obtain ⟨C, haC, hbC, _hfirst, hsecond⟩ :=
        exists_carrier_of_cross_unit_triples_with_completion a b ha hb hcross
      have hX0circle : (↑X0 : Set (Point 5)) ⊆ C.firstCircle :=
        subset_firstCircle_of_rank_two_anchor C hX0cos h02 a ha haX0 haC
      have hb4C : ∀ i, b4 i ∈ C.secondSphere := by
        intro i
        apply hsecond
        intro j
        simpa [dist_comm] using hba (b4 i) (by simp [Qb]) j
      have hX1sphere : (↑X1 : Set (Point 5)) ⊆ C.secondSphere :=
        subset_secondSphere_of_rank_three_anchor C hX1cos h13 b4 hb4 hb4X1 hb4C
      refine ⟨C, ?_, ?_⟩
      · intro v hv
        exact C.firstCircle_subset_firstSphere (hX0circle
          (Finset.mem_map.mpr ⟨v, by simpa [F0] using hv, rfl⟩))
      · intro v hv
        exact hX1sphere (Finset.mem_map.mpr ⟨v, by simpa [F1] using hv, rfl⟩)
  · rcases hdim1 with h12 | h13
    · -- rank three / rank two
      obtain ⟨a4, ha4, ha4X0, _ha4Span⟩ := exists_affineBasis_finset X0 hX0ne 3 h03
      let Qa : Finset (Point 5) := Finset.univ.image a4
      have hQaCard : Qa.card = 4 := by
        change (Finset.univ.image a4).card = 4
        rw [Finset.card_image_of_injective _ ha4.injective]
        simp
      have hQaNe : Qa.Nonempty := by rw [← Finset.card_pos, hQaCard]; decide
      have hQaX0 : Qa ⊆ X0 := by
        intro x hx
        change x ∈ Finset.univ.image a4 at hx
        rw [Finset.mem_image] at hx
        obtain ⟨i, _hi, rfl⟩ := hx
        exact ha4X0 (Set.mem_range_self i)
      obtain ⟨b, hb, hbX1, hab⟩ := exists_cross_unit_triple_of_point_subset
        P hepsilon hlarge (by decide : (0 : Fin 2) ≠ 1) Qa hQaNe
        (by simpa [X0, F0, emb] using hQaX0) (by omega)
      let a : Fin 3 → Point 5 := fun i ↦ a4 i.castSucc
      have ha : AffineIndependent ℝ a := ha4.comp_embedding Fin.castSuccEmb
      have haX0 : Set.range a ⊆ (↑X0 : Set (Point 5)) := by
        rintro _ ⟨i, rfl⟩
        exact ha4X0 (Set.mem_range_self i.castSucc)
      have hcross : ∀ i j, dist (a i) (b j) = 1 := by
        intro i j
        exact hab (a4 i.castSucc) (by simp [Qa]) j
      obtain ⟨C, haC, hbC, hfirst, _hsecond⟩ :=
        exists_carrier_of_cross_unit_triples_with_completion a b ha hb hcross
      have ha4C : ∀ i, a4 i ∈ C.firstSphere := by
        intro i
        exact hfirst (a4 i) (fun j ↦ hab (a4 i) (by simp [Qa]) j)
      have hX0sphere : (↑X0 : Set (Point 5)) ⊆ C.firstSphere :=
        subset_firstSphere_of_rank_three_anchor C hX0cos h03 a4 ha4 ha4X0 ha4C
      have hX1circle : (↑X1 : Set (Point 5)) ⊆ C.secondCircle :=
        subset_secondCircle_of_rank_two_anchor C hX1cos h12 b hb hbX1 hbC
      refine ⟨C, ?_, ?_⟩
      · intro v hv
        exact hX0sphere (Finset.mem_map.mpr ⟨v, by simpa [F0] using hv, rfl⟩)
      · intro v hv
        exact C.secondCircle_subset_secondSphere (hX1circle
          (Finset.mem_map.mpr ⟨v, by simpa [F1] using hv, rfl⟩))
    · -- rank three / rank three: two interlocking completion anchors
      obtain ⟨a4, ha4, ha4X0, _ha4Span⟩ := exists_affineBasis_finset X0 hX0ne 3 h03
      let Qa : Finset (Point 5) := Finset.univ.image a4
      have hQaCard : Qa.card = 4 := by
        change (Finset.univ.image a4).card = 4
        rw [Finset.card_image_of_injective _ ha4.injective]
        simp
      have hQaNe : Qa.Nonempty := by rw [← Finset.card_pos, hQaCard]; decide
      have hQaX0 : Qa ⊆ X0 := by
        intro x hx
        change x ∈ Finset.univ.image a4 at hx
        rw [Finset.mem_image] at hx
        obtain ⟨i, _hi, rfl⟩ := hx
        exact ha4X0 (Set.mem_range_self i)
      obtain ⟨b, hb, hbX1, hab⟩ := exists_cross_unit_triple_of_point_subset
        P hepsilon hlarge (by decide : (0 : Fin 2) ≠ 1) Qa hQaNe
        (by simpa [X0, F0, emb] using hQaX0) (by omega)
      obtain ⟨b4, hb4, hb4X1, hbB4⟩ :=
        exists_affineIndependent_four_extending_three X1 h13 b hb hbX1
      let Qb : Finset (Point 5) := Finset.univ.image b4
      have hQbCard : Qb.card = 4 := by
        change (Finset.univ.image b4).card = 4
        rw [Finset.card_image_of_injective _ hb4.injective]
        simp
      have hQbNe : Qb.Nonempty := by rw [← Finset.card_pos, hQbCard]; decide
      have hQbX1 : Qb ⊆ X1 := by
        intro x hx
        change x ∈ Finset.univ.image b4 at hx
        rw [Finset.mem_image] at hx
        obtain ⟨i, _hi, rfl⟩ := hx
        exact hb4X1 (Set.mem_range_self i)
      obtain ⟨a, ha, haX0, hba⟩ := exists_cross_unit_triple_of_point_subset
        P hepsilon hlarge (by decide : (1 : Fin 2) ≠ 0) Qb hQbNe
        (by simpa [X1, F1, emb] using hQbX1) (by omega)
      have hcross : ∀ i j, dist (a i) (b j) = 1 := by
        intro i j
        obtain ⟨k, hk⟩ := hbB4 (Set.mem_range_self j)
        rw [← hk]
        simpa [dist_comm] using hba (b4 k) (by simp [Qb]) i
      obtain ⟨C, _haC, _hbC, hfirst, hsecond⟩ :=
        exists_carrier_of_cross_unit_triples_with_completion a b ha hb hcross
      have ha4C : ∀ i, a4 i ∈ C.firstSphere := by
        intro i
        exact hfirst (a4 i) (fun j ↦ hab (a4 i) (by simp [Qa]) j)
      have hb4C : ∀ i, b4 i ∈ C.secondSphere := by
        intro i
        apply hsecond
        intro j
        simpa [dist_comm] using hba (b4 i) (by simp [Qb]) j
      have hX0sphere : (↑X0 : Set (Point 5)) ⊆ C.firstSphere :=
        subset_firstSphere_of_rank_three_anchor C hX0cos h03 a4 ha4 ha4X0 ha4C
      have hX1sphere : (↑X1 : Set (Point 5)) ⊆ C.secondSphere :=
        subset_secondSphere_of_rank_three_anchor C hX1cos h13 b4 hb4 hb4X1 hb4C
      refine ⟨C, ?_, ?_⟩
      · intro v hv
        exact hX0sphere (Finset.mem_map.mpr ⟨v, by simpa [F0] using hv, rfl⟩)
      · intro v hv
        exact hX1sphere (Finset.mem_map.mpr ⟨v, by simpa [F1] using hv, rfl⟩)

/-- Real-valued sufficient-size form of the retained-core classifier. -/
theorem exists_carrier_of_stablePartition_retained_core_of_real_bound
    {A : Finset (Point 5)} {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) 2 epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hnumeric :
      5 * (epsilon * (A.card : ℝ) + 1) + 3 ≤
        (A.card : ℝ) / 2 - epsilon * (A.card : ℝ)) :
    ∃ C : Carrier,
      (∀ v ∈ Stability.retainedFiber P.color P.exceptional 0,
        (v : Point 5) ∈ C.firstSphere) ∧
      ∀ v ∈ Stability.retainedFiber P.color P.exceptional 1,
        (v : Point 5) ∈ C.secondSphere := by
  apply exists_carrier_of_stablePartition_retained_core P hepsilon
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
