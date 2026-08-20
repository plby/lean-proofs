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

import ErdosProblems.Erdos735.PolarBoundaryOrder
import ErdosProblems.Erdos735.RedChordSector
import ErdosProblems.Erdos735.SignVectorDoubleRestrictionCount
import ErdosProblems.Erdos735.CyclicSupportingEdge
import ErdosProblems.Erdos957.HullGeometryBridge

/-!
# Supporting edges in the concrete polar boundary order

This file records that the genuine cyclic order constructed for a polar
boundary has the expected universal property: every strict supporting edge
of the polygon is one of its consecutive pairs, in one of the two possible
orientations.  This is the order-theoretic bridge used to identify weak
restriction-sector endpoints with actual projective boundary vertices.
-/

open Classical

namespace Erdos735.SignVector.PolarBoundaryEndpointBridge

noncomputable section

open Erdos957
open Matrix
open PolarFace PolarPlaneChart

lemma dotCLM_apply_comm (y z : Vec3) : dotCLM y z = z ⬝ᵥ y := by
  rw [dotCLM_apply, dotProduct_comm]

/-- A compact nontrivial exposed face has at least two extreme points. -/
theorem extremePoints_nontrivial_of_isExposed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {A F : Set E}
    (hAcompact : IsCompact A) (hFconvex : Convex ℝ F)
    (hFA : IsExposed ℝ A F) (hFnontrivial : F.Nontrivial) :
    (F.extremePoints ℝ).Nontrivial := by
  have hFcompact : IsCompact F := hFA.isCompact hAcompact
  have hFnonempty : F.Nonempty := hFnontrivial.nonempty
  obtain ⟨e, he⟩ := hFcompact.extremePoints_nonempty hFnonempty
  by_contra hnot
  have hsubsingle : (F.extremePoints ℝ).Subsingleton :=
    Set.not_nontrivial_iff.mp hnot
  have heq : F.extremePoints ℝ = {e} :=
    Set.eq_singleton_iff_unique_mem.mpr
      ⟨he, fun z hz ↦ hsubsingle hz he⟩
  have hkrein := closure_convexHull_extremePoints hFcompact hFconvex
  rw [heq, convexHull_singleton, closure_singleton] at hkrein
  have hFsingle : F = {e} := hkrein.symm
  rw [hFsingle] at hFnontrivial
  exact Set.not_nontrivial_singleton hFnontrivial

/-- Three points in the affine polar plane which vanish on one further
nonzero covector are collinear after applying the concrete planar chart. -/
theorem orientedTurn_coord_eq_zero_of_common_zero
    {x y p q r : Vec3} (hx : x ≠ 0) (hy : y ≠ 0)
    (hpx : p ⬝ᵥ x = 1) (hqx : q ⬝ᵥ x = 1) (hrx : r ⬝ᵥ x = 1)
    (hpy : p ⬝ᵥ y = 0) (hqy : q ⬝ᵥ y = 0) (hry : r ⬝ᵥ y = 0) :
    orientedTurn (coord x p) (coord x q) (coord x r) = 0 := by
  have hxy : x ⨯₃ y ≠ 0 := by
    intro hcross
    have hdep : ¬ LinearIndependent ℝ ![x, y] := by
      rw [← crossProduct_ne_zero_iff_linearIndependent]
      exact not_ne_iff.mpr hcross
    rw [LinearIndependent.pair_iff' hx] at hdep
    push_neg at hdep
    obtain ⟨a, hay⟩ := hdep
    have hpa := congrArg (fun z : Vec3 ↦ p ⬝ᵥ z) hay
    simp only [dotProduct_smul, smul_eq_mul, hpx, mul_one] at hpa
    have ha : a = 0 := by linarith
    apply hy
    rw [← hay, ha, zero_smul]
  have hxpq : x ⬝ᵥ (q - p) = 0 := by
    rw [dotProduct_sub, dotProduct_comm x q, dotProduct_comm x p, hqx, hpx]
    ring
  have hypq : y ⬝ᵥ (q - p) = 0 := by
    rw [dotProduct_sub, dotProduct_comm y q, dotProduct_comm y p, hqy, hpy]
    ring
  have hxpr : x ⬝ᵥ (r - p) = 0 := by
    rw [dotProduct_sub, dotProduct_comm x r, dotProduct_comm x p, hrx, hpx]
    ring
  have hypr : y ⬝ᵥ (r - p) = 0 := by
    rw [dotProduct_sub, dotProduct_comm y r, dotProduct_comm y p, hry, hpy]
    ring
  obtain ⟨a, ha⟩ := eq_smul_cross_of_dot_eq_zero hxy hxpq hypq
  obtain ⟨b, hb⟩ := eq_smul_cross_of_dot_eq_zero hxy hxpr hypr
  rw [orientedTurn_eq_crossVec]
  by_cases hx2 : x 2 = 0
  · by_cases hx1 : x 1 = 0
    · have hq1 : q 1 - p 1 = a * (x ⨯₃ y) 1 := by
        have := congrArg (fun z : Vec3 ↦ z 1) ha
        simpa using this
      have hq2 : q 2 - p 2 = a * (x ⨯₃ y) 2 := by
        have := congrArg (fun z : Vec3 ↦ z 2) ha
        simpa using this
      have hr1 : r 1 - p 1 = b * (x ⨯₃ y) 1 := by
        have := congrArg (fun z : Vec3 ↦ z 1) hb
        simpa using this
      have hr2 : r 2 - p 2 = b * (x ⨯₃ y) 2 := by
        have := congrArg (fun z : Vec3 ↦ z 2) hb
        simpa using this
      simp [coord, hx2, hx1, crossVec]
      rw [hq1, hq2, hr1, hr2]
      ring
    · have hq0 : q 0 - p 0 = a * (x ⨯₃ y) 0 := by
        have := congrArg (fun z : Vec3 ↦ z 0) ha
        simpa using this
      have hq2 : q 2 - p 2 = a * (x ⨯₃ y) 2 := by
        have := congrArg (fun z : Vec3 ↦ z 2) ha
        simpa using this
      have hr0 : r 0 - p 0 = b * (x ⨯₃ y) 0 := by
        have := congrArg (fun z : Vec3 ↦ z 0) hb
        simpa using this
      have hr2 : r 2 - p 2 = b * (x ⨯₃ y) 2 := by
        have := congrArg (fun z : Vec3 ↦ z 2) hb
        simpa using this
      simp [coord, hx2, hx1, crossVec]
      rw [hq0, hq2, hr0, hr2]
      ring
  · have hq0 : q 0 - p 0 = a * (x ⨯₃ y) 0 := by
      have := congrArg (fun z : Vec3 ↦ z 0) ha
      simpa using this
    have hq1 : q 1 - p 1 = a * (x ⨯₃ y) 1 := by
      have := congrArg (fun z : Vec3 ↦ z 1) ha
      simpa using this
    have hr0 : r 0 - p 0 = b * (x ⨯₃ y) 0 := by
      have := congrArg (fun z : Vec3 ↦ z 0) hb
      simpa using this
    have hr1 : r 1 - p 1 = b * (x ⨯₃ y) 1 := by
      have := congrArg (fun z : Vec3 ↦ z 1) hb
      simpa using this
    simp [coord, hx2, crossVec]
    rw [hq0, hq1, hr0, hr1]
    ring

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

/-- Weak realization gives nonnegative evaluation on every normalized polar
point. -/
theorem polarPoint_dot_nonneg_of_weak
    {n : I → Vec3} {s : I → Bool} {x y : Vec3}
    (hx : Realizes n s x)
    (hy : RedChordSector.WeaklyRealizes n s y) (i : I) :
    0 ≤ polarPoint n s x i ⬝ᵥ y := by
  rw [polarPoint, smul_dotProduct, orientedNormal_dot]
  exact mul_nonneg (inv_pos.mpr (polarDenom_pos hx i)).le (hy i)

/-- Two distinct normalized polar generators on a weak endpoint hyperplane
force two consecutive boundary owners on that hyperplane.  The conclusion
is label-preserving and remains valid at a multiple projective crossing. -/
theorem exists_consecutive_zero_owners
    {n : I → Vec3} (f : StrictFace n) {x y : Vec3}
    (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (hy0 : y ≠ 0) (hy : RedChordSector.WeaklyRealizes n f.1 y)
    {i j : I} (hij : i ≠ j)
    (hiy : polarPoint n f.1 x i ⬝ᵥ y = 0)
    (hjy : polarPoint n f.1 x j ⬝ᵥ y = 0) :
    ∃ t : Fin (hullVertexCount (boundaryPolygon n f.1 x)),
      polarPoint n f.1 x
          (PolarBoundaryOrder.boundaryOwner f hx hcross hspan t) ⬝ᵥ y = 0 ∧
      polarPoint n f.1 x
          (PolarBoundaryOrder.boundaryOwner f hx hcross hspan
            (cyclicSucc t)) ⬝ᵥ y = 0 := by
  let P3 := polarPoints n f.1 x
  let H : Set Vec3 := convexHull ℝ (P3 : Set Vec3)
  let L : Vec3 →L[ℝ] ℝ := dotCLM y
  let F : Set Vec3 := H ∩ {z | L z = 0}
  have hx0 : x ≠ 0 := witness_ne_zero hx
  have hiyL : L (polarPoint n f.1 x i) = 0 := by
    simpa only [L, dotCLM_apply_comm] using hiy
  have hjyL : L (polarPoint n f.1 x j) = 0 := by
    simpa only [L, dotCLM_apply_comm] using hjy
  have hHnonneg : H ⊆ {z | 0 ≤ L z} := by
    apply convexHull_min
    · intro z hz
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hz
      exact polarPoint_dot_nonneg_of_weak hx hy k
    · exact (convex_Ici (0 : ℝ)).linear_preimage L.toLinearMap
  have hpiF : polarPoint n f.1 x i ∈ F := by
    refine ⟨subset_convexHull ℝ (P3 : Set Vec3)
      (polarPoint_mem_polarPoints n f.1 x i), ?_⟩
    exact hiyL
  have hpjF : polarPoint n f.1 x j ∈ F := by
    refine ⟨subset_convexHull ℝ (P3 : Set Vec3)
      (polarPoint_mem_polarPoints n f.1 x j), ?_⟩
    exact hjyL
  have hFnontrivial : F.Nontrivial := ⟨_, hpiF, _, hpjF,
    (polarPoint_injective hx hcross).ne hij⟩
  have hHexposed : IsExposed ℝ H F := by
    intro _
    refine ⟨-L, ?_⟩
    ext z
    constructor
    · rintro ⟨hzH, hz0⟩
      change L z = 0 at hz0
      refine ⟨hzH, ?_⟩
      intro w hwH
      have hw := hHnonneg hwH
      simp only [ContinuousLinearMap.neg_apply]
      change 0 ≤ L w at hw
      rw [hz0]
      linarith
    · rintro ⟨hzH, hzmax⟩
      refine ⟨hzH, ?_⟩
      have hznonneg := hHnonneg hzH
      have hcomp := hzmax (polarPoint n f.1 x i) hpiF.1
      simp only [ContinuousLinearMap.neg_apply] at hcomp
      change 0 ≤ L z at hznonneg
      change L z = 0
      rw [hiyL] at hcomp
      linarith
  have hHcompact : IsCompact H :=
    Set.Finite.isCompact_convexHull ℝ P3.finite_toSet
  have hFconvex : Convex ℝ F := by
    apply (convex_convexHull ℝ (P3 : Set Vec3)).inter
    exact (Submodule.convex L.ker)
  have hFextreme : (F.extremePoints ℝ).Nontrivial :=
    extremePoints_nontrivial_of_isExposed hHcompact hFconvex hHexposed hFnontrivial
  obtain ⟨u, huF, v, hvF, huv⟩ := hFextreme
  have huH : u ∈ H.extremePoints ℝ :=
    hHexposed.isExtreme.extremePoints_subset_extremePoints huF
  have hvH : v ∈ H.extremePoints ℝ :=
    hHexposed.isExtreme.extremePoints_subset_extremePoints hvF
  have huP3 : u ∈ P3 := extremePoints_convexHull_subset huH
  have hvP3 : v ∈ P3 := extremePoints_convexHull_subset hvH
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp huP3
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hvP3
  have hab : a ≠ b := by
    intro hab
    subst b
    exact huv rfl
  have haext : polarPoint n f.1 x a ∈
      (convexHull ℝ (P3 : Set Vec3)).extremePoints ℝ := huH
  have hbext : polarPoint n f.1 x b ∈
      (convexHull ℝ (P3 : Set Vec3)).extremePoints ℝ := hvH
  have haowner : a ∈ edgeOwners n f.1 := by
    rw [mem_edgeOwners, edgeFeasible_faceEdgeCode_iff_extreme hx hcross]
    exact haext
  have hbowner : b ∈ edgeOwners n f.1 := by
    rw [mem_edgeOwners, edgeFeasible_faceEdgeCode_iff_extreme hx hcross]
    exact hbext
  have hay : polarPoint n f.1 x a ⬝ᵥ y = 0 := by
    have := (extremePoints_subset huF).2
    change L (polarPoint n f.1 x a) = 0 at this
    simpa only [L, dotCLM_apply_comm] using this
  have hby : polarPoint n f.1 x b ⬝ᵥ y = 0 := by
    have := (extremePoints_subset hvF).2
    change L (polarPoint n f.1 x b) = 0 at this
    simpa only [L, dotCLM_apply_comm] using this
  let pa := ownerPoint n f.1 x a
  let pb := ownerPoint n f.1 x b
  have hpaHull : pa ∈ hullVertices (boundaryPolygon n f.1 x) :=
    ownerPoint_mem_hullVertices hx hcross haowner
  have hpbHull : pb ∈ hullVertices (boundaryPolygon n f.1 x) :=
    ownerPoint_mem_hullVertices hx hcross hbowner
  let l : Plane →L[ℝ] ℝ := -(chartFunctional x (dotCLM y))
  have hpa_ne_pb : pa ≠ pb :=
    (ownerPoint_injective hx hcross).ne hab
  have hexists_pos : ∃ k, 0 < polarPoint n f.1 x k ⬝ᵥ y := by
    by_contra hnot
    push Not at hnot
    have hall : ∀ k, polarPoint n f.1 x k ⬝ᵥ y = 0 := by
      intro k
      exact le_antisymm (hnot k) (polarPoint_dot_nonneg_of_weak hx hy k)
    have hsubset : (P3 : Set Vec3) ⊆ (dotCLM y).ker := by
      intro z hz
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hz
      change dotCLM y (polarPoint n f.1 x k) = 0
      simpa only [dotCLM_apply_comm] using hall k
    have hle : Submodule.span ℝ (P3 : Set Vec3) ≤ (dotCLM y).ker :=
      (Submodule.span_le).2 hsubset
    have htop : Submodule.span ℝ (P3 : Set Vec3) = ⊤ :=
      span_polarPoints_eq_top_of_span_normals_eq_top hx hspan
    rw [htop] at hle
    have hself : y ⬝ᵥ y = 0 := by
      have hyker := hle (show y ∈ (⊤ : Submodule ℝ Vec3) by simp)
      change dotCLM y y = 0 at hyker
      simpa [dotCLM_apply] using hyker
    exact hy0 (dotProduct_self_eq_zero.mp hself)
  have hlne : l ≠ 0 := by
    intro hl0
    obtain ⟨k, hky⟩ := hexists_pos
    have heq : l (ownerPoint n f.1 x k) = l pa := by rw [hl0]; rfl
    have hsub := chartFunctional_coord_sub hx0
      (polarPoint_dot_witness hx k) (polarPoint_dot_witness hx a) (dotCLM y)
    dsimp only [l, pa, ownerPoint] at heq
    simp only [ContinuousLinearMap.neg_apply, neg_inj] at heq
    rw [heq, sub_self, dotCLM_apply_comm, dotCLM_apply_comm, hay] at hsub
    linarith
  have hlab : l pa = l pb := by
    dsimp only [l, pa, pb, ownerPoint]
    simp only [ContinuousLinearMap.neg_apply, neg_inj]
    have hsub := chartFunctional_coord_sub hx0
      (polarPoint_dot_witness hx a) (polarPoint_dot_witness hx b) (dotCLM y)
    rw [dotCLM_apply_comm, hay, dotCLM_apply_comm, hby, sub_self] at hsub
    exact sub_eq_zero.mp hsub
  have hlmax : ∀ z ∈ boundaryPolygon n f.1 x, l z ≤ l pa := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    have hky := polarPoint_dot_nonneg_of_weak hx hy k
    have hsub := chartFunctional_coord_sub hx0
      (polarPoint_dot_witness hx k) (polarPoint_dot_witness hx a) (dotCLM y)
    dsimp only [l, pa, ownerPoint]
    simp only [ContinuousLinearMap.neg_apply]
    rw [dotCLM_apply_comm, dotCLM_apply_comm, hay] at hsub
    linarith
  have hlstrict : ∀ z ∈ hullVertices (boundaryPolygon n f.1 x),
      z ≠ pa → z ≠ pb → l z < l pa := by
    intro z hzHull hzpa hzpb
    have hzPoly : z ∈ boundaryPolygon n f.1 x :=
      hullVertices_subset _ hzHull
    obtain ⟨k, hkowner, rfl⟩ := Finset.mem_image.mp hzPoly
    have hka : k ≠ a := by
      intro hka
      subst k
      exact hzpa rfl
    have hkb : k ≠ b := by
      intro hkb
      subst k
      exact hzpb rfl
    have hky_nonneg := polarPoint_dot_nonneg_of_weak hx hy k
    have hky_ne : polarPoint n f.1 x k ⬝ᵥ y ≠ 0 := by
      intro hky
      have hturn := orientedTurn_coord_eq_zero_of_common_zero hx0 hy0
        (polarPoint_dot_witness hx a) (polarPoint_dot_witness hx b)
        (polarPoint_dot_witness hx k) hay hby hky
      have hnotcol := hullVertices_not_collinear_three
        (boundaryPolygon n f.1 x) hpaHull hpbHull
        (ownerPoint_mem_hullVertices hx hcross hkowner)
        hpa_ne_pb ((ownerPoint_injective hx hcross).ne hkb).symm
        ((ownerPoint_injective hx hcross).ne hka).symm
      apply hnotcol
      apply collinear_of_crossVec_sub_eq_zero hpa_ne_pb
      rw [orientedTurn_eq_crossVec] at hturn
      simpa only [pa, pb, ownerPoint] using hturn
    have hky_pos : 0 < polarPoint n f.1 x k ⬝ᵥ y :=
      lt_of_le_of_ne hky_nonneg (Ne.symm hky_ne)
    have hsub := chartFunctional_coord_sub hx0
      (polarPoint_dot_witness hx k) (polarPoint_dot_witness hx a) (dotCLM y)
    dsimp only [l, pa, ownerPoint]
    simp only [ContinuousLinearMap.neg_apply]
    rw [dotCLM_apply_comm, dotCLM_apply_comm, hay] at hsub
    linarith
  have hedge : IsStrictSupportingEdge (boundaryPolygon n f.1 x) pa pb :=
    ⟨hpa_ne_pb, l, hlne, hlab, hlmax, hlstrict⟩
  let P := PolarBoundaryOrder.boundaryHullOrder f hx hcross hspan
  have hthree : 3 ≤ (hullVertices (boundaryPolygon n f.1 x)).card := by
    rw [hullVertices_boundaryPolygon hx hcross]
    exact PolarBoundaryOrder.three_le_boundaryPolygon_card f hx hcross hspan
  rcases Erdos735.CyclicSupportingEdge.strictSupportingEdge_eq_consecutive_or_reverse
      P hthree hpaHull hpbHull hedge with
    hforward | hreverse
  · obtain ⟨t, hta, htb⟩ := hforward
    refine ⟨t, ?_, ?_⟩
    · have hown : PolarBoundaryOrder.boundaryOwner f hx hcross hspan t = a :=
        ownerPoint_injective hx hcross <| by
          rw [PolarBoundaryOrder.ownerPoint_boundaryOwner f hx hcross hspan t]
          simpa only [P, pa] using hta
      rwa [hown]
    · have hown : PolarBoundaryOrder.boundaryOwner f hx hcross hspan
          (cyclicSucc t) = b := ownerPoint_injective hx hcross <| by
            rw [PolarBoundaryOrder.ownerPoint_boundaryOwner f hx hcross hspan
              (cyclicSucc t)]
            simpa only [P, pb] using htb
      rwa [hown]
  · obtain ⟨t, htb, hta⟩ := hreverse
    refine ⟨t, ?_, ?_⟩
    · have hown : PolarBoundaryOrder.boundaryOwner f hx hcross hspan t = b :=
        ownerPoint_injective hx hcross <| by
          rw [PolarBoundaryOrder.ownerPoint_boundaryOwner f hx hcross hspan t]
          simpa only [P, pb] using htb
      rwa [hown]
    · have hown : PolarBoundaryOrder.boundaryOwner f hx hcross hspan
          (cyclicSucc t) = a := ownerPoint_injective hx hcross <| by
            rw [PolarBoundaryOrder.ownerPoint_boundaryOwner f hx hcross hspan
              (cyclicSucc t)]
            simpa only [P, pa] using hta
      rwa [hown]

/-- A lifted supporting covector of a genuine polar corner is nonzero. -/
theorem cornerVector_ne_zero
    {n : I → Vec3} (f : StrictFace n) {x : Vec3}
    (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (hullVertexCount (boundaryPolygon n f.1 x))) :
    PolarBoundaryOrder.cornerVector f hx hcross hspan t ≠ 0 := by
  let P := PolarBoundaryOrder.boundaryHullOrder f hx hcross hspan
  have hthree : 3 ≤ hullVertexCount (boundaryPolygon n f.1 x) := by
    rw [hullVertexCount, hullVertices_boundaryPolygon hx hcross]
    exact PolarBoundaryOrder.three_le_boundaryPolygon_card f hx hcross hspan
  have herase : 0 <
      (((Finset.univ : Finset (Fin (hullVertexCount
        (boundaryPolygon n f.1 x)))).erase t).erase (cyclicSucc t)).card := by
    rw [Finset.card_erase_of_mem]
    · rw [Finset.card_erase_of_mem]
      · simp only [Finset.card_univ, Fintype.card_fin]
        omega
      · exact Finset.mem_univ _
    · exact Finset.mem_erase.mpr
        ⟨fun h ↦ P.consecutive_ne t (congrArg P.vertex h).symm,
          Finset.mem_univ _⟩
  obtain ⟨u, hu⟩ := Finset.card_pos.mp herase
  have hut : u ≠ t :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hu).2).1
  have hus : u ≠ cyclicSucc t := (Finset.mem_erase.mp hu).1
  have hstrict :=
    (PolarBoundaryOrder.cornerFunctional_spec f hx hcross hspan t).2.2.2
      (P.vertex u) (P.vertex_mem_hullVertices u)
      (P.vertex.injective.ne hut) (P.vertex.injective.ne hus)
  have hpos : 0 < polarPoint n f.1 x
      (PolarBoundaryOrder.boundaryOwner f hx hcross hspan u) ⬝ᵥ
        PolarBoundaryOrder.cornerVector f hx hcross hspan t := by
    rw [PolarBoundaryOrder.polarPoint_dot_cornerVector,
      PolarBoundaryOrder.ownerPoint_boundaryOwner f hx hcross hspan u]
    exact sub_pos.mpr hstrict
  intro hzero
  rw [hzero, dotProduct_zero] at hpos
  exact (lt_irrefl 0 hpos)

/-- Every edge displayed by a cyclic hull order is the counterclockwise
gift-wrap successor of its first vertex. -/
theorem CyclicHullOrder.isCCWNext {A : Finset Point}
    (P : CyclicHullOrder A) (i : Fin (hullVertexCount A)) :
    IsCCWNext A (P.vertex i) (P.vertex (cyclicSucc i)) := by
  refine ⟨P.vertex_mem_hullVertices _, P.edge_support i, ?_⟩
  intro z hz hzp hzq
  have hnonneg :
      0 ≤ crossVec (P.vertex (cyclicSucc i) - P.vertex i)
        (z - P.vertex i) :=
    Erdos957HullGeometryBridge.cyclic_edge_cross_nonneg P i
      (hullVertices_subset A hz)
  have hne :
      crossVec (P.vertex (cyclicSucc i) - P.vertex i)
        (z - P.vertex i) ≠ 0 := by
    intro hzero
    exact (hullVertices_not_collinear_three A
      (P.vertex_mem_hullVertices i)
      (P.vertex_mem_hullVertices (cyclicSucc i)) hz
      (P.consecutive_ne i) hzq.symm hzp.symm)
      (collinear_of_crossVec_sub_eq_zero (P.consecutive_ne i) hzero)
  rw [orientedTurn_eq_crossVec]
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- Reversing a strict supporting edge preserves strict support. -/
theorem isStrictSupportingEdge_swap {A : Finset Point} {p q : Point}
    (h : IsStrictSupportingEdge A p q) : IsStrictSupportingEdge A q p := by
  obtain ⟨hpq, l, hl, hpqlevel, hmax, hstrict⟩ := h
  refine ⟨hpq.symm, l, hl, hpqlevel.symm, ?_, ?_⟩
  · intro z hz
    rw [← hpqlevel]
    exact hmax z hz
  · intro z hz hzq hzp
    rw [← hpqlevel]
    exact hstrict z hz hzp hzq

/-- A strict supporting edge of a planar finite hull has a coherent
orientation: either it or its reversal is the counterclockwise successor. -/
theorem isCCWNext_or_reverse_of_strictSupportingEdge
    {A : Finset Point} (hthree : 3 ≤ (hullVertices A).card)
    {p q : Point} (hp : p ∈ hullVertices A) (hq : q ∈ hullVertices A)
    (hedge : IsStrictSupportingEdge A p q) :
    IsCCWNext A p q ∨ IsCCWNext A q p := by
  obtain ⟨hpq, l, hl, hpqlevel, hmax, hstrict⟩ := hedge
  have herase : 0 < (((hullVertices A).erase p).erase q).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hpq.symm, hq⟩),
      Finset.card_erase_of_mem hp]
    omega
  obtain ⟨r, hr⟩ := Finset.card_pos.mp herase
  have hrq : r ≠ q := (Finset.mem_erase.mp hr).1
  have hrp : r ≠ p := (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1
  have hrhull : r ∈ hullVertices A :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).2
  have hturnne : orientedTurn p q r ≠ 0 := by
    rw [orientedTurn_eq_crossVec]
    intro hzero
    exact (hullVertices_not_collinear_three A hp hq hrhull hpq
      hrq.symm hrp.symm) (collinear_of_crossVec_sub_eq_zero hpq hzero)
  have hlu : l (q - p) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact hpqlevel.symm
  have hlr : l (r - p) < 0 := by
    rw [map_sub]
    exact sub_neg.mpr (hstrict r hrhull hrp hrq)
  have hdet := support_turn_coordinate_det l (q - p) (r - p)
  rw [hlu, zero_mul, zero_sub, ← orientedTurn_eq_crossVec] at hdet
  by_cases hpos : 0 < orientedTurn p q r
  · left
    refine ⟨hq, ⟨hpq, l, hl, hpqlevel, hmax, hstrict⟩, ?_⟩
    intro z hz hzp hzq
    have hlz : l (z - p) < 0 := by
      rw [map_sub]
      exact sub_neg.mpr (hstrict z hz hzp hzq)
    have hdetz := support_turn_coordinate_det l (q - p) (z - p)
    rw [hlu, zero_mul, zero_sub, ← orientedTurn_eq_crossVec] at hdetz
    have hquarter : 0 < quarterTurnFunctional l (q - p) := by
      have hcoef := support_coefficient_sq_pos hl
      nlinarith
    have hcoef := support_coefficient_sq_pos hl
    nlinarith
  · right
    have hneg : orientedTurn p q r < 0 := lt_of_le_of_ne
      (le_of_not_gt hpos) hturnne
    refine ⟨hp, isStrictSupportingEdge_swap
      ⟨hpq, l, hl, hpqlevel, hmax, hstrict⟩, ?_⟩
    intro z hz hzq hzp
    have hlz : l (z - p) < 0 := by
      rw [map_sub]
      exact sub_neg.mpr (hstrict z hz hzp hzq)
    have hdetz := support_turn_coordinate_det l (q - p) (z - p)
    rw [hlu, zero_mul, zero_sub, ← orientedTurn_eq_crossVec] at hdetz
    have hquarter : quarterTurnFunctional l (q - p) < 0 := by
      have hcoef := support_coefficient_sq_pos hl
      nlinarith
    have hforward : orientedTurn p q z < 0 := by
      have hcoef := support_coefficient_sq_pos hl
      nlinarith
    have hreverse : orientedTurn q p z = -orientedTurn p q z := by
      simp only [orientedTurn]
      ring
    rw [hreverse]
    linarith

/-- Every strict supporting edge of the polygon is a consecutive pair in a
given cyclic hull order, possibly read backwards. -/
theorem strictSupportingEdge_eq_consecutive_or_reverse
    {A : Finset Point} (P : CyclicHullOrder A)
    (hthree : 3 ≤ (hullVertices A).card)
    {p q : Point} (hp : p ∈ hullVertices A) (hq : q ∈ hullVertices A)
    (hedge : IsStrictSupportingEdge A p q) :
    (∃ i, P.vertex i = p ∧ P.vertex (cyclicSucc i) = q) ∨
      (∃ i, P.vertex i = q ∧ P.vertex (cyclicSucc i) = p) := by
  rcases isCCWNext_or_reverse_of_strictSupportingEdge hthree hp hq hedge with
    hpq | hqp
  · obtain ⟨i, hi, -⟩ := P.existsUnique_vertex_eq hp
    left
    refine ⟨i, hi, ?_⟩
    have hcyclic := CyclicHullOrder.isCCWNext P i
    have hunique :=
      (Classical.choose_spec (hullVertex_existsUnique_isCCWNext A hthree hp)).2
    exact (hunique _ (hi ▸ hcyclic)).trans (hunique _ hpq).symm
  · obtain ⟨i, hi, -⟩ := P.existsUnique_vertex_eq hq
    right
    refine ⟨i, hi, ?_⟩
    have hcyclic := CyclicHullOrder.isCCWNext P i
    have hunique :=
      (Classical.choose_spec (hullVertex_existsUnique_isCCWNext A hthree hq)).2
    exact (hunique _ (hi ▸ hcyclic)).trans (hunique _ hqp).symm

end

end Erdos735.SignVector.PolarBoundaryEndpointBridge
