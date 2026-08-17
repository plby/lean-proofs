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

import ErdosProblems.Erdos223.Basic
import ErdosProblems.Erdos223.CompleteBipartiteGeometry
import ErdosProblems.Erdos223.Stability
import Mathlib.Geometry.Euclidean.Circumcenter

/-!
# Five-dimensional weak Lenz carriers

This module models the shifted two-circle geometry specific to dimension
five.  Two cross-unit affine-independent triples span orthogonal two-planes;
their circumcenters may differ along the one-dimensional orthogonal defect.
Each circle nevertheless lies on the three-sphere centered at the other
circle's center.  The resulting crossed sphere--circle pairs are all at unit
distance.

The final lemmas package the exact additional domination hypotheses under
which a stable two-color core is contained in one fixed weak carrier.
-/

open scoped EuclideanGeometry RealInnerProductSpace

namespace Erdos223.FiveWeakCarrier

noncomputable section

/-- Intrinsic form of Swanepoel's five-dimensional weak carrier.  The two
rank-two seed circles may have different centers along their common
one-dimensional orthogonal defect.  The first weak sphere is centered at the
second circle center, and conversely. -/
structure Carrier where
  firstPlane : AffineSubspace ℝ (Point 5)
  secondPlane : AffineSubspace ℝ (Point 5)
  firstCenter : Point 5
  secondCenter : Point 5
  firstRadius : ℝ
  secondRadius : ℝ
  firstSphereRadius : ℝ
  secondSphereRadius : ℝ
  firstCenter_mem : firstCenter ∈ firstPlane
  secondCenter_mem : secondCenter ∈ secondPlane
  first_finrank : Module.finrank ℝ firstPlane.direction = 2
  second_finrank : Module.finrank ℝ secondPlane.direction = 2
  direction_isOrtho : firstPlane.direction ⟂ secondPlane.direction
  center_vsub_mem_first_orthogonal :
    secondCenter -ᵥ firstCenter ∈ firstPlane.directionᗮ
  center_vsub_mem_second_orthogonal :
    firstCenter -ᵥ secondCenter ∈ secondPlane.directionᗮ
  firstRadius_nonneg : 0 ≤ firstRadius
  secondRadius_nonneg : 0 ≤ secondRadius
  firstSphereRadius_nonneg : 0 ≤ firstSphereRadius
  secondSphereRadius_nonneg : 0 ≤ secondSphereRadius
  firstSphereRadius_sq :
    firstSphereRadius ^ 2 =
      firstRadius ^ 2 + dist firstCenter secondCenter ^ 2
  secondSphereRadius_sq :
    secondSphereRadius ^ 2 =
      secondRadius ^ 2 + dist firstCenter secondCenter ^ 2
  first_cross_radius_sq : firstSphereRadius ^ 2 + secondRadius ^ 2 = 1
  second_cross_radius_sq : firstRadius ^ 2 + secondSphereRadius ^ 2 = 1

namespace Carrier

variable (C : Carrier)

def firstCircle : Set (Point 5) :=
  {x | x ∈ C.firstPlane ∧ dist x C.firstCenter = C.firstRadius}

def secondCircle : Set (Point 5) :=
  {x | x ∈ C.secondPlane ∧ dist x C.secondCenter = C.secondRadius}

/-- The three-dimensional sphere containing the first seed circle. -/
def firstSphere : Set (Point 5) :=
  {x | x -ᵥ C.secondCenter ∈ C.secondPlane.directionᗮ ∧
    dist x C.secondCenter = C.firstSphereRadius}

/-- The three-dimensional sphere containing the second seed circle. -/
def secondSphere : Set (Point 5) :=
  {x | x -ᵥ C.firstCenter ∈ C.firstPlane.directionᗮ ∧
    dist x C.firstCenter = C.secondSphereRadius}

@[simp] theorem mem_firstCircle {x : Point 5} :
    x ∈ C.firstCircle ↔
      x ∈ C.firstPlane ∧ dist x C.firstCenter = C.firstRadius := Iff.rfl

@[simp] theorem mem_secondCircle {x : Point 5} :
    x ∈ C.secondCircle ↔
      x ∈ C.secondPlane ∧ dist x C.secondCenter = C.secondRadius := Iff.rfl

@[simp] theorem mem_firstSphere {x : Point 5} :
    x ∈ C.firstSphere ↔
      x -ᵥ C.secondCenter ∈ C.secondPlane.directionᗮ ∧
      dist x C.secondCenter = C.firstSphereRadius := Iff.rfl

@[simp] theorem mem_secondSphere {x : Point 5} :
    x ∈ C.secondSphere ↔
      x -ᵥ C.firstCenter ∈ C.firstPlane.directionᗮ ∧
      dist x C.firstCenter = C.secondSphereRadius := Iff.rfl

private theorem firstCircle_vsub_secondCenter_mem_orthogonal
    {x : Point 5} (hx : x ∈ C.firstCircle) :
    x -ᵥ C.secondCenter ∈ C.secondPlane.directionᗮ := by
  have hxf : x -ᵥ C.firstCenter ∈ C.firstPlane.direction :=
    AffineSubspace.vsub_mem_direction hx.1 C.firstCenter_mem
  have hxforth : x -ᵥ C.firstCenter ∈ C.secondPlane.directionᗮ :=
    C.direction_isOrtho.symm.ge hxf
  have hcent : C.firstCenter -ᵥ C.secondCenter ∈ C.secondPlane.directionᗮ :=
    C.center_vsub_mem_second_orthogonal
  rw [← vsub_add_vsub_cancel x C.firstCenter C.secondCenter]
  exact C.secondPlane.directionᗮ.add_mem hxforth hcent

private theorem secondCircle_vsub_firstCenter_mem_orthogonal
    {x : Point 5} (hx : x ∈ C.secondCircle) :
    x -ᵥ C.firstCenter ∈ C.firstPlane.directionᗮ := by
  have hxs : x -ᵥ C.secondCenter ∈ C.secondPlane.direction :=
    AffineSubspace.vsub_mem_direction hx.1 C.secondCenter_mem
  have hxsorth : x -ᵥ C.secondCenter ∈ C.firstPlane.directionᗮ := by
    exact C.direction_isOrtho.ge hxs
  have hcent : C.secondCenter -ᵥ C.firstCenter ∈ C.firstPlane.directionᗮ :=
    C.center_vsub_mem_first_orthogonal
  rw [← vsub_add_vsub_cancel x C.secondCenter C.firstCenter]
  exact C.firstPlane.directionᗮ.add_mem hxsorth hcent

theorem firstCircle_subset_firstSphere : C.firstCircle ⊆ C.firstSphere := by
  intro x hx
  have hxorth := C.firstCircle_vsub_secondCenter_mem_orthogonal hx
  have hdir : x -ᵥ C.firstCenter ∈ C.firstPlane.direction :=
    AffineSubspace.vsub_mem_direction hx.1 C.firstCenter_mem
  have hcent := C.center_vsub_mem_first_orthogonal
  have hcent' : C.firstCenter -ᵥ C.secondCenter ∈ C.firstPlane.directionᗮ := by
    simpa only [neg_vsub_eq_vsub_rev] using C.firstPlane.directionᗮ.neg_mem hcent
  have hinner : inner ℝ (x -ᵥ C.firstCenter)
      (C.firstCenter -ᵥ C.secondCenter) = 0 := by
    rw [real_inner_comm]
    exact ((Submodule.mem_orthogonal' _ _).mp hcent') _ hdir
  have hnorm : ‖(x -ᵥ C.firstCenter) +
      (C.firstCenter -ᵥ C.secondCenter)‖ ^ 2 =
      ‖x -ᵥ C.firstCenter‖ ^ 2 +
      ‖C.firstCenter -ᵥ C.secondCenter‖ ^ 2 := by
    simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real hinner
  refine ⟨hxorth, ?_⟩
  have hsq : dist x C.secondCenter ^ 2 = C.firstSphereRadius ^ 2 := by
    calc
      dist x C.secondCenter ^ 2 =
          ‖(x -ᵥ C.firstCenter) +
            (C.firstCenter -ᵥ C.secondCenter)‖ ^ 2 := by
              rw [dist_eq_norm_vsub]
              congr 2
              exact (vsub_add_vsub_cancel x C.firstCenter C.secondCenter).symm
      _ = ‖x -ᵥ C.firstCenter‖ ^ 2 +
          ‖C.firstCenter -ᵥ C.secondCenter‖ ^ 2 := hnorm
      _ = C.firstRadius ^ 2 + dist C.firstCenter C.secondCenter ^ 2 := by
        rw [show ‖x -ᵥ C.firstCenter‖ = C.firstRadius by
          simpa [dist_eq_norm_vsub] using hx.2]
        rw [← dist_eq_norm_vsub]
      _ = C.firstSphereRadius ^ 2 := C.firstSphereRadius_sq.symm
  nlinarith [dist_nonneg (x := x) (y := C.secondCenter), C.firstSphereRadius_nonneg]

theorem secondCircle_subset_secondSphere : C.secondCircle ⊆ C.secondSphere := by
  intro x hx
  have hxorth := C.secondCircle_vsub_firstCenter_mem_orthogonal hx
  have hdir : x -ᵥ C.secondCenter ∈ C.secondPlane.direction :=
    AffineSubspace.vsub_mem_direction hx.1 C.secondCenter_mem
  have hcent := C.center_vsub_mem_second_orthogonal
  have hcent' : C.secondCenter -ᵥ C.firstCenter ∈ C.secondPlane.directionᗮ := by
    simpa only [neg_vsub_eq_vsub_rev] using C.secondPlane.directionᗮ.neg_mem hcent
  have hinner : inner ℝ (x -ᵥ C.secondCenter)
      (C.secondCenter -ᵥ C.firstCenter) = 0 := by
    rw [real_inner_comm]
    exact ((Submodule.mem_orthogonal' _ _).mp hcent') _ hdir
  have hnorm : ‖(x -ᵥ C.secondCenter) +
      (C.secondCenter -ᵥ C.firstCenter)‖ ^ 2 =
      ‖x -ᵥ C.secondCenter‖ ^ 2 +
      ‖C.secondCenter -ᵥ C.firstCenter‖ ^ 2 := by
    simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real hinner
  refine ⟨hxorth, ?_⟩
  have hsq : dist x C.firstCenter ^ 2 = C.secondSphereRadius ^ 2 := by
    calc
      dist x C.firstCenter ^ 2 =
          ‖(x -ᵥ C.secondCenter) +
            (C.secondCenter -ᵥ C.firstCenter)‖ ^ 2 := by
              rw [dist_eq_norm_vsub]
              congr 2
              exact (vsub_add_vsub_cancel x C.secondCenter C.firstCenter).symm
      _ = ‖x -ᵥ C.secondCenter‖ ^ 2 +
          ‖C.secondCenter -ᵥ C.firstCenter‖ ^ 2 := hnorm
      _ = C.secondRadius ^ 2 + dist C.firstCenter C.secondCenter ^ 2 := by
        rw [show ‖x -ᵥ C.secondCenter‖ = C.secondRadius by
          simpa [dist_eq_norm_vsub] using hx.2]
        rw [← dist_eq_norm_vsub, dist_comm]
      _ = C.secondSphereRadius ^ 2 := C.secondSphereRadius_sq.symm
  nlinarith [dist_nonneg (x := x) (y := C.firstCenter), C.secondSphereRadius_nonneg]

/-- Every first-sphere/second-circle cross pair is a unit pair. -/
theorem dist_eq_one_of_mem_firstSphere_mem_secondCircle
    {x y : Point 5} (hx : x ∈ C.firstSphere) (hy : y ∈ C.secondCircle) :
    dist x y = 1 := by
  have hyDir : y -ᵥ C.secondCenter ∈ C.secondPlane.direction :=
    AffineSubspace.vsub_mem_direction hy.1 C.secondCenter_mem
  have hinner : inner ℝ (x -ᵥ C.secondCenter)
      (y -ᵥ C.secondCenter) = 0 :=
    ((Submodule.mem_orthogonal' _ _).mp hx.1) _ hyDir
  have hnorm : ‖(x -ᵥ C.secondCenter) -
      (y -ᵥ C.secondCenter)‖ ^ 2 =
      ‖x -ᵥ C.secondCenter‖ ^ 2 +
      ‖y -ᵥ C.secondCenter‖ ^ 2 := by
    simpa [pow_two] using norm_sub_sq_eq_norm_sq_add_norm_sq_real hinner
  have hsq : dist x y ^ 2 = 1 := by
    calc
      dist x y ^ 2 = ‖(x -ᵥ C.secondCenter) -
          (y -ᵥ C.secondCenter)‖ ^ 2 := by
        rw [dist_eq_norm_vsub]
        congr 2
        simp [vsub_eq_sub]
      _ = ‖x -ᵥ C.secondCenter‖ ^ 2 +
          ‖y -ᵥ C.secondCenter‖ ^ 2 := hnorm
      _ = C.firstSphereRadius ^ 2 + C.secondRadius ^ 2 := by
        rw [show ‖x -ᵥ C.secondCenter‖ = C.firstSphereRadius by
          simpa [dist_eq_norm_vsub] using hx.2]
        rw [show ‖y -ᵥ C.secondCenter‖ = C.secondRadius by
          simpa [dist_eq_norm_vsub] using hy.2]
      _ = 1 := C.first_cross_radius_sq
  nlinarith [dist_nonneg (x := x) (y := y)]

/-- Every first-circle/second-sphere cross pair is a unit pair. -/
theorem dist_eq_one_of_mem_firstCircle_mem_secondSphere
    {x y : Point 5} (hx : x ∈ C.firstCircle) (hy : y ∈ C.secondSphere) :
    dist x y = 1 := by
  have hxDir : x -ᵥ C.firstCenter ∈ C.firstPlane.direction :=
    AffineSubspace.vsub_mem_direction hx.1 C.firstCenter_mem
  have hinner : inner ℝ (x -ᵥ C.firstCenter)
      (y -ᵥ C.firstCenter) = 0 :=
    by
      rw [real_inner_comm]
      exact ((Submodule.mem_orthogonal' _ _).mp hy.1) _ hxDir
  have hnorm : ‖(x -ᵥ C.firstCenter) -
      (y -ᵥ C.firstCenter)‖ ^ 2 =
      ‖x -ᵥ C.firstCenter‖ ^ 2 +
      ‖y -ᵥ C.firstCenter‖ ^ 2 := by
    simpa [pow_two] using norm_sub_sq_eq_norm_sq_add_norm_sq_real hinner
  have hsq : dist x y ^ 2 = 1 := by
    calc
      dist x y ^ 2 = ‖(x -ᵥ C.firstCenter) -
          (y -ᵥ C.firstCenter)‖ ^ 2 := by
        rw [dist_eq_norm_vsub]
        congr 2
        simp [vsub_eq_sub]
      _ = ‖x -ᵥ C.firstCenter‖ ^ 2 +
          ‖y -ᵥ C.firstCenter‖ ^ 2 := hnorm
      _ = C.firstRadius ^ 2 + C.secondSphereRadius ^ 2 := by
        rw [show ‖x -ᵥ C.firstCenter‖ = C.firstRadius by
          simpa [dist_eq_norm_vsub] using hx.2]
        rw [show ‖y -ᵥ C.firstCenter‖ = C.secondSphereRadius by
          simpa [dist_eq_norm_vsub] using hy.2]
      _ = 1 := C.second_cross_radius_sq
  nlinarith [dist_nonneg (x := x) (y := y)]

end Carrier

private def triplePlane (x : Fin 3 → Point 5) : AffineSubspace ℝ (Point 5) :=
  affineSpan ℝ (Set.range x)

private lemma triplePlane_finrank {x : Fin 3 → Point 5}
    (hx : AffineIndependent ℝ x) :
    Module.finrank ℝ (triplePlane x).direction = 2 := by
  rw [triplePlane, direction_affineSpan]
  exact hx.finrank_vectorSpan (by norm_num)

private lemma dist_sq_eq_add_of_orthogonal
    {u v : Point 5} (h : inner ℝ u v = 0) :
    ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real h

/-- Two affinely independent cross-unit triples in `ℝ⁵` canonically build
the shifted weak carrier.  Moreover, every point at unit distance from the
opposite seed triple is forced onto the corresponding three-sphere. -/
theorem exists_carrier_of_cross_unit_triples_with_completion
    (a b : Fin 3 → Point 5)
    (ha : AffineIndependent ℝ a) (hb : AffineIndependent ℝ b)
    (hcross : ∀ i j, dist (a i) (b j) = 1) :
    ∃ C : Carrier,
      (∀ i, a i ∈ C.firstCircle) ∧
      (∀ j, b j ∈ C.secondCircle) ∧
      (∀ q : Point 5, (∀ j, dist q (b j) = 1) → q ∈ C.firstSphere) ∧
      ∀ q : Point 5, (∀ i, dist q (a i) = 1) → q ∈ C.secondSphere := by
  let SA : Affine.Simplex ℝ (Point 5) 2 := ⟨a, ha⟩
  let SB : Affine.Simplex ℝ (Point 5) 2 := ⟨b, hb⟩
  let PA := triplePlane a
  let PB := triplePlane b
  let cA : Point 5 := SA.circumcenter
  let cB : Point 5 := SB.circumcenter
  let rA : ℝ := SA.circumradius
  let rB : ℝ := SB.circumradius
  let RA : ℝ := dist (a 0) cB
  let RB : ℝ := dist (b 0) cA
  have hcA : cA ∈ PA := by
    simpa [cA, PA, SA, triplePlane] using SA.circumcenter_mem_affineSpan
  have hcB : cB ∈ PB := by
    simpa [cB, PB, SB, triplePlane] using SB.circumcenter_mem_affineSpan
  have hdistA (i : Fin 3) : dist (a i) cA = rA := by
    simpa [cA, rA, SA] using SA.dist_circumcenter_eq_circumradius i
  have hdistB (j : Fin 3) : dist (b j) cB = rB := by
    simpa [cB, rB, SB] using SB.dist_circumcenter_eq_circumradius j
  have hA_cB : ∀ i, dist (a i) cB = RA := by
    obtain ⟨-, q, rb, ra, hq, -, -, hqb, hqa, -⟩ :=
      completeBipartiteGeometry
        (A := Set.range b) (B := Set.range a)
        (Set.range_nonempty _) (Set.range_nonempty _)
        (by rintro _ ⟨j, rfl⟩ _ ⟨i, rfl⟩; simpa [dist_comm] using hcross i j)
    have hqeq : q = cB := by
      apply SB.eq_circumcenter_of_dist_eq
      · simpa [SB, PB, triplePlane] using hq
      · intro j
        simpa [SB] using hqb (b j) ⟨j, rfl⟩
    intro i
    have hi := hqa (a i) ⟨i, rfl⟩
    have h0 := hqa (a 0) ⟨0, rfl⟩
    simpa [RA, hqeq] using hi.trans h0.symm
  have hB_cA : ∀ j, dist (b j) cA = RB := by
    obtain ⟨-, q, ra, rb, hq, -, -, hqa, hqb, -⟩ :=
      completeBipartiteGeometry
        (A := Set.range a) (B := Set.range b)
        (Set.range_nonempty _) (Set.range_nonempty _)
        (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact hcross i j)
    have hqeq : q = cA := by
      apply SA.eq_circumcenter_of_dist_eq
      · simpa [SA, PA, triplePlane] using hq
      · intro i
        simpa [SA] using hqa (a i) ⟨i, rfl⟩
    intro j
    have hj := hqb (b j) ⟨j, rfl⟩
    have h0 := hqb (b 0) ⟨0, rfl⟩
    simpa [RB, hqeq] using hj.trans h0.symm
  have hprojA : ↑(SA.orthogonalProjectionSpan cB) = cA := by
    apply SA.orthogonalProjection_eq_circumcenter_of_dist_eq
    exact hA_cB
  have hprojB : ↑(SB.orthogonalProjectionSpan cA) = cB := by
    apply SB.orthogonalProjection_eq_circumcenter_of_dist_eq
    exact hB_cA
  have hBAorth : cB -ᵥ cA ∈ PA.directionᗮ := by
    rw [← hprojA]
    change cB -ᵥ ↑(SA.orthogonalProjectionSpan cB) ∈
      (affineSpan ℝ (Set.range SA.points)).directionᗮ
    exact EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal
      (affineSpan ℝ (Set.range SA.points)) cB
  have hABorth : cA -ᵥ cB ∈ PB.directionᗮ := by
    rw [← hprojB]
    change cA -ᵥ ↑(SB.orthogonalProjectionSpan cA) ∈
      (affineSpan ℝ (Set.range SB.points)).directionᗮ
    exact EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal
      (affineSpan ℝ (Set.range SB.points)) cA
  have horth : PA.direction ⟂ PB.direction := by
    apply affineSpan_direction_isOrtho_of_cross_dist_eq
      (A := Set.range a) (B := Set.range b) (radius := 1)
      (Set.range_nonempty _) (Set.range_nonempty _)
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hcross i j
  have hRA_sq : RA ^ 2 = rA ^ 2 + dist cA cB ^ 2 := by
    have hdir : a 0 -ᵥ cA ∈ PA.direction :=
      AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ ⟨0, rfl⟩) hcA
    have hABorth' : cA -ᵥ cB ∈ PA.directionᗮ := by
      simpa only [neg_vsub_eq_vsub_rev] using PA.directionᗮ.neg_mem hBAorth
    have hi : inner ℝ (a 0 -ᵥ cA) (cA -ᵥ cB) = 0 := by
      rw [real_inner_comm]
      exact ((Submodule.mem_orthogonal' _ _).mp hABorth') _ hdir
    have hn := dist_sq_eq_add_of_orthogonal hi
    calc
      RA ^ 2 = ‖(a 0 -ᵥ cA) + (cA -ᵥ cB)‖ ^ 2 := by
        change dist (a 0) cB ^ 2 = _
        rw [dist_eq_norm_vsub]
        congr 2
        exact (vsub_add_vsub_cancel (a 0) cA cB).symm
      _ = ‖a 0 -ᵥ cA‖ ^ 2 + ‖cA -ᵥ cB‖ ^ 2 := hn
      _ = rA ^ 2 + dist cA cB ^ 2 := by
        rw [show ‖a 0 -ᵥ cA‖ = rA by
          simpa [dist_eq_norm_vsub] using hdistA 0]
        rw [← dist_eq_norm_vsub]
  have hRB_sq : RB ^ 2 = rB ^ 2 + dist cA cB ^ 2 := by
    have hdir : b 0 -ᵥ cB ∈ PB.direction :=
      AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ ⟨0, rfl⟩) hcB
    have hBAorth' : cB -ᵥ cA ∈ PB.directionᗮ := by
      simpa only [neg_vsub_eq_vsub_rev] using PB.directionᗮ.neg_mem hABorth
    have hi : inner ℝ (b 0 -ᵥ cB) (cB -ᵥ cA) = 0 := by
      rw [real_inner_comm]
      exact ((Submodule.mem_orthogonal' _ _).mp hBAorth') _ hdir
    have hn := dist_sq_eq_add_of_orthogonal hi
    calc
      RB ^ 2 = ‖(b 0 -ᵥ cB) + (cB -ᵥ cA)‖ ^ 2 := by
        change dist (b 0) cA ^ 2 = _
        rw [dist_eq_norm_vsub]
        congr 2
        exact (vsub_add_vsub_cancel (b 0) cB cA).symm
      _ = ‖b 0 -ᵥ cB‖ ^ 2 + ‖cB -ᵥ cA‖ ^ 2 := hn
      _ = rB ^ 2 + dist cA cB ^ 2 := by
        rw [show ‖b 0 -ᵥ cB‖ = rB by
          simpa [dist_eq_norm_vsub] using hdistB 0]
        rw [← dist_eq_norm_vsub, dist_comm]
  have hRA_rB : RA ^ 2 + rB ^ 2 = 1 := by
    have haorth : a 0 -ᵥ cB ∈ PB.directionᗮ := by
      have hp : ↑(SB.orthogonalProjectionSpan (a 0)) = cB := by
        apply SB.orthogonalProjection_eq_circumcenter_of_dist_eq
        intro j
        change dist (b j) (a 0) = 1
        simpa only [dist_comm] using hcross 0 j
      rw [← hp]
      change a 0 -ᵥ ↑(SB.orthogonalProjectionSpan (a 0)) ∈
        (affineSpan ℝ (Set.range SB.points)).directionᗮ
      exact EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal
        (affineSpan ℝ (Set.range SB.points)) (a 0)
    have hbdir : b 0 -ᵥ cB ∈ PB.direction :=
      AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ ⟨0, rfl⟩) hcB
    have hi := ((Submodule.mem_orthogonal' _ _).mp haorth) _ hbdir
    have hn : ‖(a 0 -ᵥ cB) - (b 0 -ᵥ cB)‖ ^ 2 =
        ‖a 0 -ᵥ cB‖ ^ 2 + ‖b 0 -ᵥ cB‖ ^ 2 := by
      simpa [pow_two] using norm_sub_sq_eq_norm_sq_add_norm_sq_real hi
    calc
      RA ^ 2 + rB ^ 2 =
          ‖a 0 -ᵥ cB‖ ^ 2 + ‖b 0 -ᵥ cB‖ ^ 2 := by
        rw [show ‖a 0 -ᵥ cB‖ = RA by simpa [dist_eq_norm_vsub] using hA_cB 0]
        rw [show ‖b 0 -ᵥ cB‖ = rB by simpa [dist_eq_norm_vsub] using hdistB 0]
      _ = ‖(a 0 -ᵥ cB) - (b 0 -ᵥ cB)‖ ^ 2 := hn.symm
      _ = dist (a 0) (b 0) ^ 2 := by
        rw [dist_eq_norm_vsub]
        congr 2
        simp [vsub_eq_sub]
      _ = 1 := by rw [hcross 0 0]; norm_num
  have hrA_RB : rA ^ 2 + RB ^ 2 = 1 := by
    have hadir : a 0 -ᵥ cA ∈ PA.direction :=
      AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ ⟨0, rfl⟩) hcA
    have hborth : b 0 -ᵥ cA ∈ PA.directionᗮ := by
      have hp : ↑(SA.orthogonalProjectionSpan (b 0)) = cA := by
        apply SA.orthogonalProjection_eq_circumcenter_of_dist_eq
        intro i
        exact hcross i 0
      rw [← hp]
      change b 0 -ᵥ ↑(SA.orthogonalProjectionSpan (b 0)) ∈
        (affineSpan ℝ (Set.range SA.points)).directionᗮ
      exact EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal
        (affineSpan ℝ (Set.range SA.points)) (b 0)
    have hi := ((Submodule.mem_orthogonal' _ _).mp hborth) _ hadir
    rw [real_inner_comm] at hi
    have hn : ‖(a 0 -ᵥ cA) - (b 0 -ᵥ cA)‖ ^ 2 =
        ‖a 0 -ᵥ cA‖ ^ 2 + ‖b 0 -ᵥ cA‖ ^ 2 := by
      simpa [pow_two] using norm_sub_sq_eq_norm_sq_add_norm_sq_real hi
    calc
      rA ^ 2 + RB ^ 2 =
          ‖a 0 -ᵥ cA‖ ^ 2 + ‖b 0 -ᵥ cA‖ ^ 2 := by
        rw [show ‖a 0 -ᵥ cA‖ = rA by simpa [dist_eq_norm_vsub] using hdistA 0]
        rw [show ‖b 0 -ᵥ cA‖ = RB by simpa [dist_eq_norm_vsub] using hB_cA 0]
      _ = ‖(a 0 -ᵥ cA) - (b 0 -ᵥ cA)‖ ^ 2 := hn.symm
      _ = dist (a 0) (b 0) ^ 2 := by
        rw [dist_eq_norm_vsub]
        congr 2
        simp [vsub_eq_sub]
      _ = 1 := by rw [hcross 0 0]; norm_num
  let C : Carrier :=
    { firstPlane := PA
      secondPlane := PB
      firstCenter := cA
      secondCenter := cB
      firstRadius := rA
      secondRadius := rB
      firstSphereRadius := RA
      secondSphereRadius := RB
      firstCenter_mem := hcA
      secondCenter_mem := hcB
      first_finrank := triplePlane_finrank ha
      second_finrank := triplePlane_finrank hb
      direction_isOrtho := horth
      center_vsub_mem_first_orthogonal := hBAorth
      center_vsub_mem_second_orthogonal := hABorth
      firstRadius_nonneg := SA.circumradius_nonneg
      secondRadius_nonneg := SB.circumradius_nonneg
      firstSphereRadius_nonneg := dist_nonneg
      secondSphereRadius_nonneg := dist_nonneg
      firstSphereRadius_sq := hRA_sq
      secondSphereRadius_sq := hRB_sq
      first_cross_radius_sq := hRA_rB
      second_cross_radius_sq := hrA_RB }
  have hbaseA (i : Fin 3) : a i ∈ C.firstCircle := by
    exact ⟨mem_affineSpan ℝ ⟨i, rfl⟩, hdistA i⟩
  have hbaseB (j : Fin 3) : b j ∈ C.secondCircle := by
    exact ⟨mem_affineSpan ℝ ⟨j, rfl⟩, hdistB j⟩
  refine ⟨C, hbaseA, hbaseB, ?_, ?_⟩
  · intro q hq
    have hproj : ↑(SB.orthogonalProjectionSpan q) = cB := by
      apply SB.orthogonalProjection_eq_circumcenter_of_dist_eq
      intro j
      simpa [dist_comm] using hq j
    have hqorth : q -ᵥ cB ∈ PB.directionᗮ := by
      rw [← hproj]
      change q -ᵥ ↑(SB.orthogonalProjectionSpan q) ∈
        (affineSpan ℝ (Set.range SB.points)).directionᗮ
      exact EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal
        (affineSpan ℝ (Set.range SB.points)) q
    have hbdir : b 0 -ᵥ cB ∈ PB.direction :=
      AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ ⟨0, rfl⟩) hcB
    have hi := ((Submodule.mem_orthogonal' _ _).mp hqorth) _ hbdir
    have hn : ‖(q -ᵥ cB) - (b 0 -ᵥ cB)‖ ^ 2 =
        ‖q -ᵥ cB‖ ^ 2 + ‖b 0 -ᵥ cB‖ ^ 2 := by
      simpa [pow_two] using norm_sub_sq_eq_norm_sq_add_norm_sq_real hi
    have hsq : dist q cB ^ 2 + rB ^ 2 = 1 := by
      calc
        dist q cB ^ 2 + rB ^ 2 =
            ‖q -ᵥ cB‖ ^ 2 + ‖b 0 -ᵥ cB‖ ^ 2 := by
          rw [dist_eq_norm_vsub]
          rw [show ‖b 0 -ᵥ cB‖ = rB by simpa [dist_eq_norm_vsub] using hdistB 0]
        _ = ‖(q -ᵥ cB) - (b 0 -ᵥ cB)‖ ^ 2 := hn.symm
        _ = dist q (b 0) ^ 2 := by
          rw [dist_eq_norm_vsub]
          congr 2
          simp [vsub_eq_sub]
        _ = 1 := by rw [hq 0]; norm_num
    refine ⟨hqorth, ?_⟩
    nlinarith [dist_nonneg (x := q) (y := cB), show 0 ≤ RA from dist_nonneg,
      hRA_rB]
  · intro q hq
    have hproj : ↑(SA.orthogonalProjectionSpan q) = cA := by
      apply SA.orthogonalProjection_eq_circumcenter_of_dist_eq
      intro i
      simpa [dist_comm] using hq i
    have hqorth : q -ᵥ cA ∈ PA.directionᗮ := by
      rw [← hproj]
      change q -ᵥ ↑(SA.orthogonalProjectionSpan q) ∈
        (affineSpan ℝ (Set.range SA.points)).directionᗮ
      exact EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal
        (affineSpan ℝ (Set.range SA.points)) q
    have hadir : a 0 -ᵥ cA ∈ PA.direction :=
      AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ ⟨0, rfl⟩) hcA
    have hi := ((Submodule.mem_orthogonal' _ _).mp hqorth) _ hadir
    have hn : ‖(q -ᵥ cA) - (a 0 -ᵥ cA)‖ ^ 2 =
        ‖q -ᵥ cA‖ ^ 2 + ‖a 0 -ᵥ cA‖ ^ 2 := by
      simpa [pow_two] using norm_sub_sq_eq_norm_sq_add_norm_sq_real hi
    have hsq : dist q cA ^ 2 + rA ^ 2 = 1 := by
      calc
        dist q cA ^ 2 + rA ^ 2 =
            ‖q -ᵥ cA‖ ^ 2 + ‖a 0 -ᵥ cA‖ ^ 2 := by
          rw [dist_eq_norm_vsub]
          rw [show ‖a 0 -ᵥ cA‖ = rA by simpa [dist_eq_norm_vsub] using hdistA 0]
        _ = ‖(q -ᵥ cA) - (a 0 -ᵥ cA)‖ ^ 2 := hn.symm
        _ = dist q (a 0) ^ 2 := by
          rw [dist_eq_norm_vsub]
          congr 2
          simp [vsub_eq_sub]
        _ = 1 := by rw [hq 0]; norm_num
    refine ⟨hqorth, ?_⟩
    nlinarith [dist_nonneg (x := q) (y := cA), show 0 ≤ RB from dist_nonneg,
      hrA_RB]

end

end Erdos223.FiveWeakCarrier

open scoped EuclideanGeometry RealInnerProductSpace SimpleGraph

namespace Erdos223.FiveWeakCarrier

noncomputable section

private lemma three_points_on_unit_sphere_independent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {a b c q : E} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haq : dist a q = 1) (hbq : dist b q = 1) (hcq : dist c q = 1) :
    LinearIndependent ℝ ![b - a, c - a] := by
  have hu : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  rw [LinearIndependent.pair_iff' hu]
  intro t ht
  have h_a : inner ℝ (a - q) (a - q) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, haq]
    norm_num
  have h_b : inner ℝ (b - q) (b - q) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hbq]
    norm_num
  have h_c : inner ℝ (c - q) (c - q) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hcq]
    norm_num
  have hu_pos : 0 < inner ℝ (b - a) (b - a) := (real_inner_self_pos).2 hu
  have hb_split : b - q = (a - q) + (b - a) := by abel
  have hc_split : c - q = (a - q) + (c - a) := by abel
  rw [hb_split] at h_b
  rw [hc_split, ← ht] at h_c
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right] at h_b h_c
  rw [real_inner_comm (a - q) (b - a)] at h_b h_c
  have hpoly : (t * (t - 1)) * inner ℝ (b - a) (b - a) = 0 := by
    linear_combination h_c - h_a - t * h_b + t * h_a
  have ht_factor : t * (t - 1) = 0 :=
    (mul_eq_zero.mp hpoly).resolve_right (ne_of_gt hu_pos)
  rcases mul_eq_zero.mp ht_factor with ht0 | ht1
  · subst t
    apply hac
    have hca : c = a := sub_eq_zero.mp (by simpa using ht.symm)
    exact hca.symm
  · have ht' : t = 1 := sub_eq_zero.mp ht1
    subst t
    apply hbc
    have huv : b - a = c - a := by simpa using ht
    calc
      b = (b - a) + a := (sub_add_cancel b a).symm
      _ = (c - a) + a := congrArg (fun z : E ↦ z + a) huv
      _ = c := sub_add_cancel c a

private lemma affineIndependent_fin_three_of_injective_of_equidistant
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : Fin 3 → E) (hx : Function.Injective x) (q : E)
    (hqx : ∀ i, dist (x i) q = 1) : AffineIndependent ℝ x := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ x 0]
  let e := finSuccAboveEquiv (0 : Fin 3)
  have hpair := three_points_on_unit_sphere_independent
    (a := x 0) (b := x 1) (c := x 2) (q := q)
    (fun h ↦ (by decide : (0 : Fin 3) ≠ 1) (hx h))
    (fun h ↦ (by decide : (0 : Fin 3) ≠ 2) (hx h))
    (fun h ↦ (by decide : (1 : Fin 3) ≠ 2) (hx h))
    (hqx 0) (hqx 1) (hqx 2)
  have heq : ((fun i' : {i' : Fin 3 // i' ≠ 0} ↦ x i' -ᵥ x 0) ∘ e) =
      ![x 1 - x 0, x 2 - x 0] := by
    funext k
    fin_cases k <;> rfl
  exact (linearIndependent_equiv' e heq).mp hpair

/-- Exact retained-core premise needed to turn stable-partition vertices into
one fixed weak carrier: the two seed triples must dominate the opposite
retained fibers.  Stability by itself only gives few missing cross edges, so
these domination hypotheses are intentionally explicit. -/
theorem exists_carrier_of_stablePartition_seeded_retained_core
    {A : Finset (Point 5)} {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) 2 epsilon)
    (a b : Fin 3 → {x // x ∈ A})
    (_ha_mem : ∀ i, a i ∈ Stability.retainedFiber P.color P.exceptional 0)
    (_hb_mem : ∀ j, b j ∈ Stability.retainedFiber P.color P.exceptional 1)
    (ha_inj : Function.Injective a) (hb_inj : Function.Injective b)
    (hcross : ∀ i j, (diameterGraph A).Adj (a i) (b j))
    (hdom_first : ∀ v ∈ Stability.retainedFiber P.color P.exceptional 0,
      ∀ j, (diameterGraph A).Adj v (b j))
    (hdom_second : ∀ v ∈ Stability.retainedFiber P.color P.exceptional 1,
      ∀ i, (diameterGraph A).Adj (a i) v) :
    ∃ C : Carrier,
      (∀ v ∈ Stability.retainedFiber P.color P.exceptional 0,
        (v : Point 5) ∈ C.firstSphere) ∧
      ∀ v ∈ Stability.retainedFiber P.color P.exceptional 1,
        (v : Point 5) ∈ C.secondSphere := by
  let a' : Fin 3 → Point 5 := fun i ↦ a i
  let b' : Fin 3 → Point 5 := fun j ↦ b j
  have ha'_inj : Function.Injective a' := by
    intro i j hij
    exact ha_inj (Subtype.ext hij)
  have hb'_inj : Function.Injective b' := by
    intro i j hij
    exact hb_inj (Subtype.ext hij)
  have hdist (i j : Fin 3) : dist (a' i) (b' j) = 1 :=
    (diameterGraph_adj A (a i) (b j)).1 (hcross i j)
  have ha_aff : AffineIndependent ℝ a' :=
    affineIndependent_fin_three_of_injective_of_equidistant
      a' ha'_inj (b' 0) (fun i ↦ hdist i 0)
  have hb_aff : AffineIndependent ℝ b' :=
    affineIndependent_fin_three_of_injective_of_equidistant
      b' hb'_inj (a' 0) (fun j ↦ by simpa [dist_comm] using hdist 0 j)
  obtain ⟨C, -, -, hfirst, hsecond⟩ :=
    exists_carrier_of_cross_unit_triples_with_completion a' b' ha_aff hb_aff hdist
  refine ⟨C, ?_, ?_⟩
  · intro v hv
    apply hfirst (v : Point 5)
    intro j
    exact (diameterGraph_adj A v (b j)).1 (hdom_first v hv j)
  · intro v hv
    apply hsecond (v : Point 5)
    intro i
    simpa [dist_comm] using
      (diameterGraph_adj A (a i) v).1 (hdom_second v hv i)

/-- If the retained two-color core is already complete bipartite and each
fiber has at least three vertices, cross-complete triples can be chosen and
the entire retained core lies on one five-dimensional weak carrier. -/
theorem exists_carrier_of_stablePartition_complete_retained_core
    {A : Finset (Point 5)} {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) 2 epsilon)
    (hcard : ∀ i : Fin 2,
      3 ≤ (Stability.retainedFiber P.color P.exceptional i).card)
    (hcomplete : ∀ v ∈ Stability.retainedFiber P.color P.exceptional 0,
      ∀ w ∈ Stability.retainedFiber P.color P.exceptional 1,
        (diameterGraph A).Adj v w) :
    ∃ C : Carrier,
      (∀ v ∈ Stability.retainedFiber P.color P.exceptional 0,
        (v : Point 5) ∈ C.firstSphere) ∧
      ∀ v ∈ Stability.retainedFiber P.color P.exceptional 1,
        (v : Point 5) ∈ C.secondSphere := by
  classical
  let F0 := Stability.retainedFiber P.color P.exceptional (0 : Fin 2)
  let F1 := Stability.retainedFiber P.color P.exceptional (1 : Fin 2)
  obtain ⟨T0, hT0sub, hT0card⟩ := Finset.exists_subset_card_eq (hcard 0)
  obtain ⟨T1, hT1sub, hT1card⟩ := Finset.exists_subset_card_eq (hcard 1)
  let e0 : Fin 3 ≃ {v // v ∈ T0} := (Finset.equivFinOfCardEq hT0card).symm
  let e1 : Fin 3 ≃ {v // v ∈ T1} := (Finset.equivFinOfCardEq hT1card).symm
  let a : Fin 3 → {x // x ∈ A} := fun i ↦ (e0 i).1
  let b : Fin 3 → {x // x ∈ A} := fun j ↦ (e1 j).1
  have ha_mem (i : Fin 3) : a i ∈ F0 := hT0sub (e0 i).2
  have hb_mem (j : Fin 3) : b j ∈ F1 := hT1sub (e1 j).2
  apply exists_carrier_of_stablePartition_seeded_retained_core P a b
  · exact ha_mem
  · exact hb_mem
  · intro i j hij
    exact e0.injective (Subtype.ext hij)
  · intro i j hij
    exact e1.injective (Subtype.ext hij)
  · intro i j
    exact hcomplete (a i) (ha_mem i) (b j) (hb_mem j)
  · exact fun v hv j ↦ hcomplete v hv (b j) (hb_mem j)
  · intro v hv i
    exact hcomplete (a i) (ha_mem i) v hv

end

end Erdos223.FiveWeakCarrier
