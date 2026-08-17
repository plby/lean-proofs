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
import ErdosProblems.Erdos223.LenzOptimization
import ErdosProblems.Erdos223.Stability
import ErdosProblems.Erdos223.CompleteBipartiteGeometry
import ErdosProblems.Erdos223.LocalCircle

/-!
# Odd-dimensional weak and strong Lenz carriers

This file formalizes the carrier used in Section 5.3 of Swanepoel's proof of
the eventual exact result for Erdős Problem 223.  In dimension `2 * p + 1`,
write the space as one common axis and `p` mutually orthogonal coordinate
planes.  The `i`th weak component is the radius-`1 / sqrt 2` two-sphere in
the sum of the axis and the `i`th plane; its equator is the corresponding
circle.  A finite set is strong when points off the equators occur in at most
one component.

The definition is given in canonical coordinates and transported by a
linear isometric equivalence and a translation.  Thus it represents exactly
the Euclidean-motion-invariant definition in the paper without carrying a
large orthogonal-direct-sum structure through every later argument.

The second part of the file is the finite optimization at the heart of
Proposition 14.  It is stated for the numerical profile extracted from a
weak carrier: `size i` is the size of the `i`th sphere class and `off i` the
number of its non-equatorial points.  The result isolates the precise
weak-to-strong implication: attaining the strong Lenz lower bound forces
the cross-defect `sum_{i<j} off i * off j` to vanish, hence at most one
component contains off-equator points.
-/

open scoped BigOperators EuclideanGeometry RealInnerProductSpace SimpleGraph
open Fintype

namespace Erdos223
namespace CarrierOdd

noncomputable section

/-! ## The canonical weak carrier -/

/-- The first coordinate of the `i`th coordinate plane. -/
def planeFirst (p : ℕ) (i : Fin p) : Fin (2 * p + 1) :=
  ⟨2 * i, by omega⟩

/-- The second coordinate of the `i`th coordinate plane. -/
def planeSecond (p : ℕ) (i : Fin p) : Fin (2 * p + 1) :=
  ⟨2 * i + 1, by omega⟩

/-- The coordinate of the common one-dimensional axis. -/
def axisIndex (p : ℕ) : Fin (2 * p + 1) :=
  ⟨2 * p, by omega⟩

lemma planeFirst_ne_planeSecond (p : ℕ) (i j : Fin p) :
    planeFirst p i ≠ planeSecond p j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [planeFirst, planeSecond] at hv
  omega

lemma planeFirst_ne_axisIndex (p : ℕ) (i : Fin p) :
    planeFirst p i ≠ axisIndex p := by
  intro h
  have hv := congrArg Fin.val h
  simp only [planeFirst, axisIndex] at hv
  omega

lemma planeSecond_ne_axisIndex (p : ℕ) (i : Fin p) :
    planeSecond p i ≠ axisIndex p := by
  intro h
  have hv := congrArg Fin.val h
  simp only [planeSecond, axisIndex] at hv
  omega

lemma planeFirst_injective (p : ℕ) : Function.Injective (planeFirst p) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [planeFirst] at hv
  omega

lemma planeSecond_injective (p : ℕ) : Function.Injective (planeSecond p) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [planeSecond] at hv
  omega

/-- A vector is supported on the common axis and the `i`th coordinate
plane. -/
def InAxisPlane {p : ℕ} (i : Fin p) (x : Point (2 * p + 1)) : Prop :=
  ∀ j, j ≠ planeFirst p i → j ≠ planeSecond p i →
    j ≠ axisIndex p → x j = 0

/-- The canonical radius-`1 / sqrt 2` sphere belonging to part `i`. -/
def OnSphere {p : ℕ} (i : Fin p) (x : Point (2 * p + 1)) : Prop :=
  InAxisPlane i x ∧ ‖x‖ = 1 / Real.sqrt 2

/-- The equatorial circle of the canonical sphere belonging to part `i`. -/
def OnEquator {p : ℕ} (i : Fin p) (x : Point (2 * p + 1)) : Prop :=
  OnSphere i x ∧ x (axisIndex p) = 0

lemma OnEquator.onSphere {p : ℕ} {i : Fin p} {x : Point (2 * p + 1)}
    (h : OnEquator i x) : OnSphere i x := h.1

lemma inner_eq_axis_mul_of_onSpheres {p : ℕ} {i j : Fin p} (hij : i ≠ j)
    {x y : Point (2 * p + 1)} (hx : OnSphere i x) (hy : OnSphere j y) :
    inner ℝ x y = x (axisIndex p) * y (axisIndex p) := by
  classical
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  have hsum :
      (∑ k : Fin (2 * p + 1), y k * x k) =
        y (axisIndex p) * x (axisIndex p) := by
    apply Finset.sum_eq_single (axisIndex p)
    · intro k _ hka
      by_cases hkf : k = planeFirst p i
      · have hkyf : k ≠ planeFirst p j := by
          intro h
          apply hij
          exact planeFirst_injective p (hkf.symm.trans h)
        have hkys : k ≠ planeSecond p j := by
          intro h
          exact planeFirst_ne_planeSecond p i j (hkf.symm.trans h)
        rw [hy.1 k hkyf hkys hka]
        simp
      · by_cases hks : k = planeSecond p i
        · have hkyf : k ≠ planeFirst p j := by
            intro h
            exact planeFirst_ne_planeSecond p j i (h.symm.trans hks)
          have hkys : k ≠ planeSecond p j := by
            intro h
            apply hij
            exact planeSecond_injective p (hks.symm.trans h)
          rw [hy.1 k hkyf hkys hka]
          simp
        · rw [hx.1 k hkf hks hka]
          simp
    · intro ha
      exact (ha (Finset.mem_univ _)).elim
  simpa [mul_comm] using hsum

lemma dist_sq_eq_one_sub_two_mul_axis {p : ℕ} {i j : Fin p} (hij : i ≠ j)
    {x y : Point (2 * p + 1)} (hx : OnSphere i x) (hy : OnSphere j y) :
    dist x y ^ 2 = 1 - 2 * (x (axisIndex p) * y (axisIndex p)) := by
  have hsqrt : Real.sqrt (2 : ℝ) ^ 2 = 2 := by norm_num
  have hinner := inner_eq_axis_mul_of_onSpheres hij hx hy
  have hinner' : inner ℝ y x = x (axisIndex p) * y (axisIndex p) := by
    rw [real_inner_comm]
    exact hinner
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hinner', hinner,
    hx.2, hy.2, div_pow, hsqrt]
  ring

/-- The diameter constraint forces the axis coordinates of points in
distinct weak components to have the same weak sign.  This is the sign
fact used when choosing the safe replacement pole in the no-pole case. -/
lemma axis_mul_nonneg_of_onSpheres_of_dist_le_one
    {p : ℕ} {i j : Fin p} (hij : i ≠ j)
    {x y : Point (2 * p + 1)} (hx : OnSphere i x) (hy : OnSphere j y)
    (hxy : dist x y ≤ 1) :
    0 ≤ x (axisIndex p) * y (axisIndex p) := by
  have hsq := dist_sq_eq_one_sub_two_mul_axis hij hx hy
  have hdist : 0 ≤ dist x y := dist_nonneg
  nlinarith

/-- Between two distinct weak components, unit distance is equivalent to at
least one endpoint lying on its equator. -/
theorem dist_eq_one_iff_mem_equator_of_onSpheres {p : ℕ} {i j : Fin p}
    (hij : i ≠ j) {x y : Point (2 * p + 1)}
    (hx : OnSphere i x) (hy : OnSphere j y) :
    dist x y = 1 ↔ OnEquator i x ∨ OnEquator j y := by
  have hsq := dist_sq_eq_one_sub_two_mul_axis hij hx hy
  constructor
  · intro hd
    rw [hd] at hsq
    have hmul : x (axisIndex p) * y (axisIndex p) = 0 := by nlinarith
    rcases mul_eq_zero.mp hmul with hx0 | hy0
    · exact Or.inl ⟨hx, hx0⟩
    · exact Or.inr ⟨hy, hy0⟩
  · rintro (⟨-, hx0⟩ | ⟨-, hy0⟩)
    · rw [hx0, zero_mul] at hsq
      have hd : 0 ≤ dist x y := dist_nonneg
      nlinarith
    · rw [hy0, mul_zero] at hsq
      have hd : 0 ≤ dist x y := dist_nonneg
      nlinarith

theorem dist_eq_one_of_onEquator_onSphere {p : ℕ} {i j : Fin p}
    (hij : i ≠ j) {x y : Point (2 * p + 1)}
    (hx : OnEquator i x) (hy : OnSphere j y) : dist x y = 1 :=
  (dist_eq_one_iff_mem_equator_of_onSpheres hij hx.onSphere hy).2 (.inl hx)

/-- A Euclidean-motion copy of the canonical odd-dimensional weak Lenz
carrier. -/
structure Carrier (d p : ℕ) where
  center : Point d
  coord : Point (2 * p + 1) ≃ₗᵢ[ℝ] Point d

/-- Move a canonical coordinate vector into the ambient carrier. -/
def Carrier.place {d p : ℕ} (K : Carrier d p) (x : Point (2 * p + 1)) : Point d :=
  K.center + K.coord x

lemma Carrier.place_injective {d p : ℕ} (K : Carrier d p) :
    Function.Injective K.place := by
  intro x y hxy
  apply K.coord.injective
  exact add_left_cancel hxy

@[simp] lemma Carrier.dist_place {d p : ℕ} (K : Carrier d p)
    (x y : Point (2 * p + 1)) : dist (K.place x) (K.place y) = dist x y := by
  rw [dist_eq_norm, dist_eq_norm]
  change ‖(K.center + K.coord x) - (K.center + K.coord y)‖ = ‖x - y‖
  rw [add_sub_add_left_eq_sub, ← K.coord.map_sub]
  exact K.coord.norm_map (x - y)

/-- The `i`th two-sphere of a transported carrier. -/
def Carrier.sphere {d p : ℕ} (K : Carrier d p) (i : Fin p) : Set (Point d) :=
  K.place '' {x | OnSphere i x}

/-- The `i`th equatorial circle of a transported carrier. -/
def Carrier.equator {d p : ℕ} (K : Carrier d p) (i : Fin p) : Set (Point d) :=
  K.place '' {x | OnEquator i x}

lemma Carrier.equator_subset_sphere {d p : ℕ} (K : Carrier d p) (i : Fin p) :
    K.equator i ⊆ K.sphere i := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hx.onSphere, rfl⟩

theorem Carrier.dist_eq_one_iff_mem_equator_of_mem_spheres
    {d p : ℕ} (K : Carrier d p) {i j : Fin p} (hij : i ≠ j)
    {x y : Point d} (hx : x ∈ K.sphere i) (hy : y ∈ K.sphere j) :
    dist x y = 1 ↔ x ∈ K.equator i ∨ y ∈ K.equator j := by
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  rw [K.dist_place]
  constructor
  · intro hdist
    rcases (dist_eq_one_iff_mem_equator_of_onSpheres hij hx' hy').1 hdist with h | h
    · exact Or.inl ⟨x', h, rfl⟩
    · exact Or.inr ⟨y', h, rfl⟩
  · rintro (⟨_, hxEq, hxe⟩ | ⟨_, hyEq, hye⟩)
    · have heq := K.place_injective hxe
      subst heq
      exact (dist_eq_one_iff_mem_equator_of_onSpheres hij hx' hy').2 (.inl hxEq)
    · have heq := K.place_injective hye
      subst heq
      exact (dist_eq_one_iff_mem_equator_of_onSpheres hij hx' hy').2 (.inr hyEq)

theorem Carrier.dist_eq_one_of_mem_equator_mem_sphere
    {d p : ℕ} (K : Carrier d p) {i j : Fin p} (hij : i ≠ j)
    {x y : Point d} (hx : x ∈ K.equator i) (hy : y ∈ K.sphere j) :
    dist x y = 1 :=
  (K.dist_eq_one_iff_mem_equator_of_mem_spheres hij
    (K.equator_subset_sphere i hx) hy).2 (.inl hx)

theorem Carrier.axis_mul_nonneg_of_mem_spheres_of_dist_le_one
    {d p : ℕ} (K : Carrier d p) {i j : Fin p} (hij : i ≠ j)
    {x y : Point (2 * p + 1)} (hx : K.place x ∈ K.sphere i)
    (hy : K.place y ∈ K.sphere j) (hxy : dist (K.place x) (K.place y) ≤ 1) :
    0 ≤ x (axisIndex p) * y (axisIndex p) := by
  obtain ⟨x', hx', hxeq⟩ := hx
  obtain ⟨y', hy', hyeq⟩ := hy
  have ex : x' = x := K.place_injective hxeq
  have ey : y' = y := K.place_injective hyeq
  subst ex
  subst ey
  apply axis_mul_nonneg_of_onSpheres_of_dist_le_one hij hx' hy'
  simpa using hxy

/-- A finite set is contained in the union of the two-spheres of an odd
weak Lenz carrier. -/
def IsWeakCarrierSet {d p : ℕ} (A : Finset (Point d)) : Prop :=
  ∃ K : Carrier d p, ∀ x ∈ A, ∃ i : Fin p, x ∈ K.sphere i

/-- A finite set is contained in one carrier sphere and the equators of all
other components.  This is Swanepoel's strong odd Lenz configuration. -/
def IsStrongCarrierSet {d p : ℕ} (A : Finset (Point d)) : Prop :=
  ∃ (K : Carrier d p) (s : Fin p), ∀ x ∈ A,
    x ∈ K.sphere s ∨ ∃ i : Fin p, i ≠ s ∧ x ∈ K.equator i

/-- The exact coordinate certificate produced at the end of an affine
orthogonal-decomposition argument. -/
theorem isWeakCarrierSet_of_coordinate_certificate
    {p : ℕ} {A : Finset (Point (2 * p + 1))}
    (center : Point (2 * p + 1))
    (coord : Point (2 * p + 1) ≃ₗᵢ[ℝ] Point (2 * p + 1))
    (part : {x : Point (2 * p + 1) // x ∈ A} → Fin p)
    (hsupport : ∀ (x : {x : Point (2 * p + 1) // x ∈ A}),
      InAxisPlane (part x) (coord.symm (x.1 - center)))
    (hradius : ∀ (x : {x : Point (2 * p + 1) // x ∈ A}),
      ‖coord.symm (x.1 - center)‖ = 1 / Real.sqrt 2) :
    IsWeakCarrierSet (p := p) A := by
  let K : Carrier (2 * p + 1) p := { center := center, coord := coord }
  refine ⟨K, ?_⟩
  intro x hx
  let xA : {x : Point (2 * p + 1) // x ∈ A} := ⟨x, hx⟩
  let z : Point (2 * p + 1) := coord.symm (x - center)
  refine ⟨part xA, z, ⟨hsupport xA, hradius xA⟩, ?_⟩
  change center + coord (coord.symm (x - center)) = x
  rw [coord.apply_symm_apply]
  abel

theorem isWeakCarrierSet_of_coordinate_certificate_sq
    {p : ℕ} {A : Finset (Point (2 * p + 1))}
    (center : Point (2 * p + 1))
    (coord : Point (2 * p + 1) ≃ₗᵢ[ℝ] Point (2 * p + 1))
    (part : {x : Point (2 * p + 1) // x ∈ A} → Fin p)
    (hsupport : ∀ (x : {x : Point (2 * p + 1) // x ∈ A}),
      InAxisPlane (part x) (coord.symm (x.1 - center)))
    (hradiusSq : ∀ (x : {x : Point (2 * p + 1) // x ∈ A}),
      ‖coord.symm (x.1 - center)‖ ^ 2 = (1 : ℝ) / 2) :
    IsWeakCarrierSet (p := p) A := by
  apply isWeakCarrierSet_of_coordinate_certificate center coord part hsupport
  intro x
  have hsqrt : Real.sqrt (2 : ℝ) ^ 2 = 2 := by norm_num
  have hsqrtpos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have htarget : (1 / Real.sqrt (2 : ℝ)) ^ 2 = (1 : ℝ) / 2 := by
    rw [div_pow, one_pow, hsqrt]
  have hnorm := norm_nonneg (coord.symm (x.1 - center))
  have htargetnonneg : 0 ≤ (1 / Real.sqrt (2 : ℝ)) :=
    (one_div_pos.mpr hsqrtpos).le
  nlinarith [hradiusSq x]

theorem IsStrongCarrierSet.isWeak {d p : ℕ} {A : Finset (Point d)}
    (h : IsStrongCarrierSet (p := p) A) : IsWeakCarrierSet (p := p) A := by
  obtain ⟨K, s, hA⟩ := h
  refine ⟨K, fun x hx ↦ ?_⟩
  rcases hA x hx with hs | ⟨i, -, hi⟩
  · exact ⟨s, hs⟩
  · exact ⟨i, K.equator_subset_sphere i hi⟩

/-! A weak carrier set becomes a genuinely disjoint finite profile after
choosing, for each point, one sphere containing it.  This matters only for
the two common poles, which lie in every sphere. -/

/-- A choice of a carrier component for every point of a finite set. -/
structure Assignment {d p : ℕ} (A : Finset (Point d)) where
  carrier : Carrier d p
  part : {x : Point d // x ∈ A} → Fin p
  mem_sphere : ∀ x, x.1 ∈ carrier.sphere (part x)

namespace Assignment

variable {d p : ℕ} {A : Finset (Point d)} (Q : Assignment (p := p) A)

/-- The assigned points of part `i` that do not lie on its equator. -/
def offPoints (i : Fin p) : Finset {x : Point d // x ∈ A} := by
  classical
  exact Finset.univ.filter fun x ↦
    Q.part x = i ∧ x.1 ∉ Q.carrier.equator i

/-- The number of assigned non-equatorial points in part `i`. -/
def offCount (i : Fin p) : ℕ := (Q.offPoints i).card

lemma mem_offPoints_iff {i : Fin p} {x : {x : Point d // x ∈ A}} :
    x ∈ Q.offPoints i ↔
      Q.part x = i ∧ x.1 ∉ Q.carrier.equator i := by
  simp [offPoints]

lemma mem_equator_of_offCount_eq_zero (i : Fin p) (hi : Q.offCount i = 0)
    (x : {x : Point d // x ∈ A}) (hx : Q.part x = i) :
    x.1 ∈ Q.carrier.equator i := by
  by_contra hxeq
  have hxoff : x ∈ Q.offPoints i := Q.mem_offPoints_iff.mpr ⟨hx, hxeq⟩
  have hpos : 0 < Q.offCount i := by
    rw [offCount, Finset.card_pos]
    exact ⟨x, hxoff⟩
  omega

/-- In different assigned parts, two non-equatorial points cannot form a
diameter.  This is the geometric statement represented numerically by the
cross defect. -/
theorem dist_ne_one_of_mem_offPoints {i j : Fin p} (hij : i ≠ j)
    {x y : {x : Point d // x ∈ A}}
    (hxpart : Q.part x = i) (hypart : Q.part y = j)
    (hxoff : x ∈ Q.offPoints i) (hyoff : y ∈ Q.offPoints j) :
    dist x.1 y.1 ≠ 1 := by
  intro hdist
  have hxsphere : x.1 ∈ Q.carrier.sphere i := by
    simpa [hxpart] using Q.mem_sphere x
  have hysphere : y.1 ∈ Q.carrier.sphere j := by
    simpa [hypart] using Q.mem_sphere y
  rcases (Q.carrier.dist_eq_one_iff_mem_equator_of_mem_spheres hij
    hxsphere hysphere).1 hdist with hxeq | hyeq
  · exact (Q.mem_offPoints_iff.mp hxoff).2 hxeq
  · exact (Q.mem_offPoints_iff.mp hyoff).2 hyeq

theorem isWeakCarrierSet (Q : Assignment (p := p) A) :
    IsWeakCarrierSet (p := p) A := by
  refine ⟨Q.carrier, ?_⟩
  intro x hx
  let xA : {x : Point d // x ∈ A} := ⟨x, hx⟩
  exact ⟨Q.part xA, Q.mem_sphere xA⟩

/-- Numerical strongness of an assigned weak profile upgrades the original
finite set to a strong carrier set. -/
theorem isStrongCarrierSet (hp : 0 < p)
    (hstrong : ∀ i j, i ≠ j → Q.offCount i = 0 ∨ Q.offCount j = 0) :
    IsStrongCarrierSet (p := p) A := by
  classical
  by_cases hactive : ∃ s : Fin p, Q.offCount s ≠ 0
  · obtain ⟨s, hs⟩ := hactive
    refine ⟨Q.carrier, s, ?_⟩
    intro x hx
    let xA : {x : Point d // x ∈ A} := ⟨x, hx⟩
    by_cases his : Q.part xA = s
    · exact .inl (by simpa [his] using Q.mem_sphere xA)
    · have hoff : Q.offCount (Q.part xA) = 0 := by
        rcases hstrong s (Q.part xA) (by intro h; exact his h.symm) with hs0 | hi0
        · exact (hs hs0).elim
        · exact hi0
      exact .inr ⟨Q.part xA, his, Q.mem_equator_of_offCount_eq_zero
        (Q.part xA) hoff xA rfl⟩
  · let s : Fin p := ⟨0, hp⟩
    have hoff (i : Fin p) : Q.offCount i = 0 := by
      by_contra hi
      exact hactive ⟨i, hi⟩
    refine ⟨Q.carrier, s, ?_⟩
    intro x hx
    let xA : {x : Point d // x ∈ A} := ⟨x, hx⟩
    by_cases his : Q.part xA = s
    · exact .inl (by simpa [his] using Q.mem_sphere xA)
    · exact .inr ⟨Q.part xA, his,
        Q.mem_equator_of_offCount_eq_zero (Q.part xA) (hoff _) xA rfl⟩

end Assignment

/-- Every weak carrier set admits an assigned finite profile. -/
theorem exists_assignment_of_isWeakCarrierSet {d p : ℕ}
    {A : Finset (Point d)} (hA : IsWeakCarrierSet (p := p) A) :
    Nonempty (Assignment (p := p) A) := by
  classical
  obtain ⟨K, hK⟩ := hA
  let choosePart (x : {x : Point d // x ∈ A}) : Fin p :=
    Classical.choose (hK x.1 x.2)
  exact ⟨{
    carrier := K
    part := choosePart
    mem_sphere := fun x ↦ Classical.choose_spec (hK x.1 x.2) }⟩

/-! ## Safe common poles for the corrected replacement -/

/-- Canonical coordinate preimage of an ambient carrier point. -/
def Carrier.unplace {d p : ℕ} (K : Carrier d p) (x : Point d) :
    Point (2 * p + 1) := K.coord.symm (x - K.center)

@[simp] lemma Carrier.place_unplace {d p : ℕ} (K : Carrier d p)
    (x : Point d) : K.place (K.unplace x) = x := by
  simp only [Carrier.place, Carrier.unplace, LinearIsometryEquiv.apply_symm_apply]
  abel

@[simp] lemma Carrier.unplace_place {d p : ℕ} (K : Carrier d p)
    (x : Point (2 * p + 1)) : K.unplace (K.place x) = x := by
  apply K.place_injective
  simp

/-- The two common canonical poles. -/
def positivePole (p : ℕ) : Point (2 * p + 1) :=
  EuclideanSpace.single (axisIndex p) (1 / Real.sqrt 2)

def negativePole (p : ℕ) : Point (2 * p + 1) :=
  EuclideanSpace.single (axisIndex p) (- (1 / Real.sqrt 2))

@[simp] lemma positivePole_axis (p : ℕ) :
    positivePole p (axisIndex p) = 1 / Real.sqrt 2 := by
  simp [positivePole]

@[simp] lemma negativePole_axis (p : ℕ) :
    negativePole p (axisIndex p) = - (1 / Real.sqrt 2) := by
  simp [negativePole]

lemma positivePole_onSphere {p : ℕ} (i : Fin p) :
    OnSphere i (positivePole p) := by
  refine ⟨?_, ?_⟩
  · intro j _ _ hja
    simp [positivePole, hja]
  · simp [positivePole, Real.norm_eq_abs]

lemma negativePole_onSphere {p : ℕ} (i : Fin p) :
    OnSphere i (negativePole p) := by
  refine ⟨?_, ?_⟩
  · intro j _ _ hja
    simp [negativePole, hja]
  · simp [negativePole, Real.norm_eq_abs]

lemma positivePole_not_onEquator {p : ℕ} (i : Fin p) :
    ¬ OnEquator i (positivePole p) := by
  intro h
  have hpos : (0 : ℝ) < 1 / Real.sqrt 2 := by positivity
  simpa using h.2

lemma negativePole_not_onEquator {p : ℕ} (i : Fin p) :
    ¬ OnEquator i (negativePole p) := by
  intro h
  have hpos : (0 : ℝ) < 1 / Real.sqrt 2 := by positivity
  simpa using h.2

lemma dist_positivePole_le_one_of_onSphere_of_axis_nonneg
    {p : ℕ} {r i : Fin p} (hri : r ≠ i)
    {x : Point (2 * p + 1)} (hx : OnSphere i x)
    (haxis : 0 ≤ x (axisIndex p)) :
    dist (positivePole p) x ≤ 1 := by
  have hsq := dist_sq_eq_one_sub_two_mul_axis hri
    (positivePole_onSphere r) hx
  have hp : (0 : ℝ) < 1 / Real.sqrt 2 := by positivity
  have hd : 0 ≤ dist (positivePole p) x := dist_nonneg
  rw [positivePole_axis] at hsq
  nlinarith

lemma dist_negativePole_le_one_of_onSphere_of_axis_nonpos
    {p : ℕ} {r i : Fin p} (hri : r ≠ i)
    {x : Point (2 * p + 1)} (hx : OnSphere i x)
    (haxis : x (axisIndex p) ≤ 0) :
    dist (negativePole p) x ≤ 1 := by
  have hsq := dist_sq_eq_one_sub_two_mul_axis hri
    (negativePole_onSphere r) hx
  have hp : (0 : ℝ) < 1 / Real.sqrt 2 := by positivity
  have hd : 0 ≤ dist (negativePole p) x := dist_nonneg
  rw [negativePole_axis] at hsq
  nlinarith

namespace Assignment

variable {d p : ℕ} {A : Finset (Point d)} (Q : Assignment (p := p) A)

/-- Axis coordinate of an assigned point in canonical carrier coordinates. -/
def axisCoord (x : {x : Point d // x ∈ A}) : ℝ :=
  Q.carrier.unplace x.1 (axisIndex p)

lemma unplace_onSphere (x : {x : Point d // x ∈ A}) :
    OnSphere (Q.part x) (Q.carrier.unplace x.1) := by
  obtain ⟨z, hz, hzx⟩ := Q.mem_sphere x
  have hz' : z = Q.carrier.unplace x.1 := by
    apply Q.carrier.place_injective
    simpa using hzx
  simpa [hz'] using hz

lemma axisCoord_ne_zero_of_mem_offPoints
    {i : Fin p} {x : {x : Point d // x ∈ A}}
    (hx : x ∈ Q.offPoints i) : Q.axisCoord x ≠ 0 := by
  intro hzero
  have hxpart : Q.part x = i := (Q.mem_offPoints_iff.mp hx).1
  have heq : x.1 ∈ Q.carrier.equator i := by
    refine ⟨Q.carrier.unplace x.1, ?_, Q.carrier.place_unplace x.1⟩
    refine ⟨?_, ?_⟩
    · simpa [hxpart] using Q.unplace_onSphere x
    · simpa [axisCoord] using hzero
  exact (Q.mem_offPoints_iff.mp hx).2 heq

lemma axisCoord_mul_nonneg_of_ne_part
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1)
    {x y : {x : Point d // x ∈ A}} (hpart : Q.part x ≠ Q.part y) :
    0 ≤ Q.axisCoord x * Q.axisCoord y := by
  apply axis_mul_nonneg_of_onSpheres_of_dist_le_one hpart
    (Q.unplace_onSphere x) (Q.unplace_onSphere y)
  rw [← Q.carrier.dist_place]
  simpa using hdiam x.1 x.2 y.1 y.2

/-- Outside an active component, all axis coordinates have one common weak
sign. -/
theorem exists_common_axis_sign_outside
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1)
    (r : Fin p) (hr : 0 < Q.offCount r) :
    (∀ x : {x : Point d // x ∈ A}, Q.part x ≠ r → 0 ≤ Q.axisCoord x) ∨
      (∀ x : {x : Point d // x ∈ A}, Q.part x ≠ r → Q.axisCoord x ≤ 0) := by
  rw [offCount, Finset.card_pos] at hr
  obtain ⟨a, ha⟩ := hr
  have hapart : Q.part a = r := (Q.mem_offPoints_iff.mp ha).1
  have hane : Q.axisCoord a ≠ 0 := Q.axisCoord_ne_zero_of_mem_offPoints ha
  rcases lt_or_gt_of_ne hane with haNeg | haPos
  · refine Or.inr ?_
    intro x hxr
    have hprod := Q.axisCoord_mul_nonneg_of_ne_part hdiam
      (show Q.part a ≠ Q.part x by simpa [hapart] using hxr.symm)
    nlinarith
  · refine Or.inl ?_
    intro x hxr
    have hprod := Q.axisCoord_mul_nonneg_of_ne_part hdiam
      (show Q.part a ≠ Q.part x by simpa [hapart] using hxr.symm)
    nlinarith

/-- An active component admits a common pole whose insertion preserves the
diameter bound against every point assigned outside that component. -/
theorem exists_safe_pole_outside
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1)
    (r : Fin p) (hr : 0 < Q.offCount r) :
    ∃ z : Point (2 * p + 1),
      OnSphere r z ∧ ¬ OnEquator r z ∧
      ∀ x : {x : Point d // x ∈ A}, Q.part x ≠ r →
        dist (Q.carrier.place z) x.1 ≤ 1 := by
  rcases Q.exists_common_axis_sign_outside hdiam r hr with hpos | hneg
  · refine ⟨positivePole p, positivePole_onSphere r,
      positivePole_not_onEquator r, ?_⟩
    intro x hxr
    have hx := dist_positivePole_le_one_of_onSphere_of_axis_nonneg
      (r := r) (i := Q.part x) hxr.symm (Q.unplace_onSphere x) (hpos x hxr)
    calc
      dist (Q.carrier.place (positivePole p)) x.1 =
          dist (Q.carrier.place (positivePole p))
            (Q.carrier.place (Q.carrier.unplace x.1)) := by simp
      _ = dist (positivePole p) (Q.carrier.unplace x.1) :=
        Q.carrier.dist_place _ _
      _ ≤ 1 := hx
  · refine ⟨negativePole p, negativePole_onSphere r,
      negativePole_not_onEquator r, ?_⟩
    intro x hxr
    have hx := dist_negativePole_le_one_of_onSphere_of_axis_nonpos
      (r := r) (i := Q.part x) hxr.symm (Q.unplace_onSphere x) (hneg x hxr)
    calc
      dist (Q.carrier.place (negativePole p)) x.1 =
          dist (Q.carrier.place (negativePole p))
            (Q.carrier.place (Q.carrier.unplace x.1)) := by simp
      _ = dist (negativePole p) (Q.carrier.unplace x.1) :=
        Q.carrier.dist_place _ _
      _ ≤ 1 := hx

end Assignment

namespace AssignmentIntegration

variable {d p : ℕ} {A : Finset (Point d)}

/-- A carrier assignment need only respect the stable coloring on retained
vertices.  The coloring of an exceptional vertex is bookkeeping data and
has no geometric meaning. -/
def AgreesOnRetained (Q : Assignment (p := p) A) {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) p epsilon) : Prop :=
  ∀ x : {x : Point d // x ∈ A}, x ∉ P.exceptional → Q.part x = P.color x

/-- The disjoint assigned fiber of carrier class `i`. -/
def partFinset (Q : Assignment (p := p) A) (i : Fin p) :
    Finset {x : Point d // x ∈ A} := by
  classical
  exact Finset.univ.filter fun x ↦ Q.part x = i

def partCard (Q : Assignment (p := p) A) (i : Fin p) : ℕ :=
  (partFinset Q i).card

@[simp] lemma mem_partFinset_iff (Q : Assignment (p := p) A)
    {i : Fin p} {x : {x : Point d // x ∈ A}} :
    x ∈ partFinset Q i ↔ Q.part x = i := by
  simp [partFinset]

lemma sum_partCard (Q : Assignment (p := p) A) :
    ∑ i, partCard Q i = A.card := by
  classical
  have h := Finset.sum_fiberwise (Finset.univ :
    Finset {x : Point d // x ∈ A}) Q.part (fun _ ↦ (1 : ℕ))
  simpa [partCard, partFinset] using h

lemma retainedFiber_subset_partFinset
    (Q : Assignment (p := p) A) {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (hagrees : AgreesOnRetained Q P) (i : Fin p) :
    Stability.retainedFiber P.color P.exceptional i ⊆ partFinset Q i := by
  intro x hx
  have hx' := (Stability.mem_retainedFiber P.color P.exceptional i x).mp hx
  rw [mem_partFinset_iff, hagrees x hx'.2]
  exact hx'.1

lemma partCard_ge_three_of_stablePartition
    (Q : Assignment (p := p) A) {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (hagrees : AgreesOnRetained Q P)
    (hlarge : ∀ _i : Fin p,
      (3 : ℝ) + epsilon * A.card < (A.card : ℝ) / p) :
    ∀ i, 3 ≤ partCard Q i := by
  intro i
  let R := Stability.retainedFiber P.color P.exceptional i
  have hbal' : |(R.card : ℝ) - (A.card : ℝ) / p| <
      epsilon * (A.card : ℝ) := by
    simpa [R] using P.balanced i
  have hbelow : - (epsilon * (A.card : ℝ)) <
      (R.card : ℝ) - (A.card : ℝ) / p := (abs_lt.mp hbal').1
  have hRreal : (3 : ℝ) < R.card := by
    have := hlarge i
    nlinarith
  have hRnat : 3 ≤ R.card := by exact_mod_cast hRreal.le
  exact hRnat.trans (Finset.card_le_card
    (retainedFiber_subset_partFinset Q P hagrees i))

end AssignmentIntegration

/-! ## From a stable partition to exact cross-unit seeds -/

/-- A retained vertex has three diameter neighbors in any other retained
fiber as soon as that fiber is larger than its global nonneighbor
allowance by two.  This is the basic greedy step used to extract the
complete tripartite seeds in the stability-to-carrier argument. -/
theorem Stability.StablePartition.exists_three_cross_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {p : ℕ} {epsilon : ℝ} (P : Stability.StablePartition G p epsilon)
    {i j : Fin p} (hij : i ≠ j) {v : V}
    (hv : v ∈ Stability.retainedFiber P.color P.exceptional i)
    (hlarge : epsilon * (Fintype.card V : ℝ) + 2 <
      ((Stability.retainedFiber P.color P.exceptional j).card : ℝ)) :
    ∃ T : Finset V,
      T.card = 3 ∧
      T ⊆ Stability.retainedFiber P.color P.exceptional j ∧
      ∀ w ∈ T, G.Adj v w := by
  classical
  let F := Stability.retainedFiber P.color P.exceptional j
  let N := F.filter fun w ↦ G.Adj v w
  let M := F.filter fun w ↦ ¬ G.Adj v w
  have hMsub : M ⊆
      Stability.retainedCrossNonneighbors G P.color P.exceptional v := by
    intro w hw
    have hwm := Finset.mem_filter.mp hw
    have hwfiber := Stability.mem_retainedFiber P.color P.exceptional j w |>.1 hwm.1
    have hvfiber := Stability.mem_retainedFiber P.color P.exceptional i v |>.1 hv
    rw [Stability.mem_retainedCrossNonneighbors]
    exact ⟨hwfiber.2, by simpa [hvfiber.1, hwfiber.1] using hij, hwm.2⟩
  have hMcard : (M.card : ℝ) ≤
      ((Stability.retainedCrossNonneighbors G P.color P.exceptional v).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hMsub
  have hMsmall := P.crossNonneighbors_small i v hv
  have hsplitNat : N.card + M.card = F.card := by
    exact Finset.card_filter_add_card_filter_not (s := F) (fun w ↦ G.Adj v w)
  have hsplit : (N.card : ℝ) + (M.card : ℝ) = (F.card : ℝ) := by
    exact_mod_cast hsplitNat
  have hNgt : (2 : ℝ) < N.card := by
    dsimp only [F] at hlarge hsplit
    nlinarith
  have hNcard : 3 ≤ N.card := by
    have : 2 < N.card := by exact_mod_cast hNgt
    omega
  obtain ⟨T, hTN, hTcard⟩ := Finset.exists_subset_card_eq hNcard
  refine ⟨T, hTcard, ?_, ?_⟩
  · intro w hw
    exact (Finset.mem_filter.mp (hTN hw)).1
  · intro w hw
    exact (Finset.mem_filter.mp (hTN hw)).2

private lemma card_biUnion_bad_le
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

private lemma exists_card_subset_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S Q : Finset V) (B t : ℕ)
    (hbad : ∀ x ∈ Q, (S.filter fun y ↦ ¬ G.Adj x y).card ≤ B)
    (hsize : Q.card * B + t ≤ S.card) :
    ∃ T : Finset V, T ⊆ S ∧ T.card = t ∧
      ∀ y ∈ T, ∀ x ∈ Q, G.Adj x y := by
  classical
  let Bad : Finset V := Q.biUnion fun x ↦ S.filter fun y ↦ ¬ G.Adj x y
  have hBadS : Bad ⊆ S := by
    intro y hy
    simp only [Bad, Finset.mem_biUnion, Finset.mem_filter] at hy
    obtain ⟨x, _hx, hyS, _⟩ := hy
    exact hyS
  have hBad : Bad.card ≤ Q.card * B := card_biUnion_bad_le G S Q B hbad
  have ht : t ≤ (S \ Bad).card := by
    rw [Finset.card_sdiff_of_subset hBadS]
    omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq ht
  refine ⟨T, hTsub.trans Finset.sdiff_subset, hTcard, ?_⟩
  intro y hy x hx
  have hyDiff : y ∈ S \ Bad := hTsub hy
  have hyNotBad : y ∉ Bad := (Finset.mem_sdiff.mp hyDiff).2
  by_contra hxy
  apply hyNotBad
  simp only [Bad, Finset.mem_biUnion, Finset.mem_filter]
  exact ⟨x, hx, (Finset.mem_sdiff.mp hyDiff).1, hxy⟩

/-- Greedily select equal-size blocks from specified parts, preserving all
cross edges and all edges from a fixed base set. -/
theorem exists_complete_on_finset_with_base
    {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : ι → Finset V) (I : Finset ι) (Q₀ : Finset V) (q B t : ℕ)
    (hIq : Q₀.card + I.card * t ≤ q)
    (hsize : ∀ i ∈ I, q * B + t ≤ (S i).card)
    (hbad : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ x ∈ S i,
      ((S j).filter fun y ↦ ¬ G.Adj x y).card ≤ B)
    (hbadBase : ∀ x ∈ Q₀, ∀ j ∈ I,
      ((S j).filter fun y ↦ ¬ G.Adj x y).card ≤ B) :
    ∃ T : ι → Finset V,
      (∀ i ∈ I, T i ⊆ S i ∧ (T i).card = t) ∧
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j →
        ∀ x ∈ T i, ∀ y ∈ T j, G.Adj x y) ∧
      ∀ x ∈ Q₀, ∀ i ∈ I, ∀ y ∈ T i, G.Adj x y := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨fun _ ↦ ∅, by simp, by simp, by simp⟩
  | @insert a I ha ih =>
      have hIqI : Q₀.card + I.card * t ≤ q := by
        apply le_trans (Nat.add_le_add_left
          (Nat.mul_le_mul_right t (Nat.le_add_right I.card 1)) Q₀.card)
        simpa [Finset.card_insert_of_notMem ha] using hIq
      obtain ⟨T, hT, hcross, hbase⟩ := ih hIqI
        (fun i hi ↦ hsize i (Finset.mem_insert_of_mem hi))
        (fun i hi j hj hij x hx ↦
          hbad i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij x hx)
        (fun x hx j hj ↦ hbadBase x hx j (Finset.mem_insert_of_mem hj))
      let Q : Finset V := Q₀ ∪ I.biUnion T
      have hQcard : Q.card ≤ q := by
        calc
          Q.card ≤ Q₀.card + (I.biUnion T).card := by
            simpa [Q] using Finset.card_union_le Q₀ (I.biUnion T)
          _ ≤ Q₀.card + ∑ i ∈ I, (T i).card :=
            Nat.add_le_add_left Finset.card_biUnion_le Q₀.card
          _ = Q₀.card + ∑ _i ∈ I, t := by
            congr 1
            exact Finset.sum_congr rfl fun i hi ↦ (hT i hi).2
          _ = Q₀.card + I.card * t := by simp
          _ ≤ q := hIqI
      have hbadQ : ∀ x ∈ Q,
          ((S a).filter fun y ↦ ¬ G.Adj x y).card ≤ B := by
        intro x hx
        simp only [Q, Finset.mem_union, Finset.mem_biUnion] at hx
        rcases hx with hx₀ | ⟨i, hi, hxi⟩
        · exact hbadBase x hx₀ a (Finset.mem_insert_self a I)
        · exact hbad i (Finset.mem_insert_of_mem hi) a
            (Finset.mem_insert_self a I) (fun hia ↦ ha (hia ▸ hi)) x ((hT i hi).1 hxi)
      have hsizeA : Q.card * B + t ≤ (S a).card := by
        exact (Nat.add_le_add_right (Nat.mul_le_mul_right B hQcard) t).trans
          (hsize a (Finset.mem_insert_self a I))
      obtain ⟨Ta, hTaS, hTaCard, hTaAdj⟩ :=
        exists_card_subset_adj G (S a) Q B t hbadQ hsizeA
      let T' : ι → Finset V := Function.update T a Ta
      refine ⟨T', ?_, ?_, ?_⟩
      · intro i hi
        by_cases hia : i = a
        · subst i
          simpa [T'] using And.intro hTaS hTaCard
        · have hiI : i ∈ I := (Finset.mem_insert.mp hi).resolve_left hia
          simpa [T', hia] using hT i hiI
      · intro i hi j hj hij x hxi y hyj
        by_cases hia : i = a
        · subst i
          have hja : j ≠ a := fun h ↦ hij h.symm
          have hjI : j ∈ I := (Finset.mem_insert.mp hj).resolve_left hja
          have hyQ : y ∈ Q := by
            simp only [Q, Finset.mem_union, Finset.mem_biUnion]
            exact Or.inr ⟨j, hjI, by simpa [T', hja] using hyj⟩
          exact (G.adj_comm y x).mp
            (hTaAdj x (by simpa [T'] using hxi) y hyQ)
        · have hiI : i ∈ I := (Finset.mem_insert.mp hi).resolve_left hia
          by_cases hja : j = a
          · subst j
            have hxQ : x ∈ Q := by
              simp only [Q, Finset.mem_union, Finset.mem_biUnion]
              exact Or.inr ⟨i, hiI, by simpa [T', hia] using hxi⟩
            exact hTaAdj y (by simpa [T'] using hyj) x hxQ
          · have hjI : j ∈ I := (Finset.mem_insert.mp hj).resolve_left hja
            exact hcross i hiI j hjI hij x (by simpa [T', hia] using hxi)
              y (by simpa [T', hja] using hyj)
      · intro x hx i hi y hy
        by_cases hia : i = a
        · subst i
          apply hTaAdj y (by simpa [T'] using hy) x
          simp only [Q, Finset.mem_union]
          exact Or.inl hx
        · exact hbase x hx i ((Finset.mem_insert.mp hi).resolve_left hia) y
            (by simpa [T', hia] using hy)

private theorem exists_complete_multipartite
    {V : Type*} [Fintype V] [DecidableEq V] {p : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Fin p → Finset V) (q B t : ℕ)
    (hpq : p * t ≤ q)
    (hsize : ∀ i, q * B + t ≤ (S i).card)
    (hbad : ∀ i j, i ≠ j → ∀ x ∈ S i,
      ((S j).filter fun y ↦ ¬ G.Adj x y).card ≤ B) :
    ∃ T : Fin p → Finset V,
      (∀ i, T i ⊆ S i ∧ (T i).card = t) ∧
      ∀ i j, i ≠ j → ∀ x ∈ T i, ∀ y ∈ T j, G.Adj x y := by
  simpa using exists_complete_on_finset_with_base G S Finset.univ ∅ q B t
    (by simpa using hpq) (fun i _ ↦ hsize i)
    (fun i _ j _ hij x hx ↦ hbad i j hij x hx) (by simp)

private lemma completeEquipartite_isContained_of_selected
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {p : ℕ}
    (S T : Fin p → Finset V)
    (hT : ∀ i, T i ⊆ S i ∧ (T i).card = 3)
    (hfiber : ∀ i x, x ∈ S i → ∀ j, x ∈ S j → i = j)
    (hcross : ∀ i j, i ≠ j → ∀ x ∈ T i, ∀ y ∈ T j, G.Adj x y) :
    SimpleGraph.completeEquipartiteGraph p 3 ⊑ G := by
  apply Stability.completeEquipartiteGraph_isContained_of_parts T
  · intro i j hij
    have hi : (T i).Nonempty := Finset.card_pos.mp (by rw [(hT i).2]; decide)
    obtain ⟨x, hx⟩ := hi
    apply hfiber i x ((hT i).1 hx) j
    apply (hT j).1
    rw [← hij]
    exact hx
  · exact fun i ↦ (hT i).2
  · intro i j hij x hx y hy
    exact hcross i j hij x hx y hy

/-- The stable partition contains an exact `K_p(3)` once every retained
fiber is large compared with the union of the at most `3p` exceptional
nonneighbor sets encountered by the greedy selection. -/
theorem stablePartition_completeEquipartiteGraph_three_isContained
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {p : ℕ} {epsilon : ℝ} (P : Stability.StablePartition G p epsilon)
    (_hepsilon : 0 ≤ epsilon)
    (hnumeric :
      (((3 * p) * ⌈epsilon * (Fintype.card V : ℝ)⌉₊ + 3 : ℕ) : ℝ) ≤
        (Fintype.card V : ℝ) / p - epsilon * (Fintype.card V : ℝ)) :
    SimpleGraph.completeEquipartiteGraph p 3 ⊑ G := by
  classical
  let S : Fin p → Finset V :=
    fun i ↦ Stability.retainedFiber P.color P.exceptional i
  let B : ℕ := ⌈epsilon * (Fintype.card V : ℝ)⌉₊
  have hsize : ∀ i, (3 * p) * B + 3 ≤ (S i).card := by
    intro i
    have habs := (abs_lt.mp (P.balanced i)).1
    have hlower : (Fintype.card V : ℝ) / p - epsilon * (Fintype.card V : ℝ) <
        ((S i).card : ℝ) := by
      dsimp only [S]
      linarith
    exact_mod_cast hnumeric.trans_lt hlower |>.le
  have hbad : ∀ i j, i ≠ j → ∀ x ∈ S i,
      ((S j).filter fun y ↦ ¬ G.Adj x y).card ≤ B := by
    intro i j hij x hx
    let Bad := (S j).filter fun y ↦ ¬ G.Adj x y
    let R := Stability.retainedCrossNonneighbors G P.color P.exceptional x
    have hsub : Bad ⊆ R := by
      intro y hy
      have hy' := Finset.mem_filter.mp hy
      have hxi := (Stability.mem_retainedFiber P.color P.exceptional i x).1 hx
      have hyj := (Stability.mem_retainedFiber P.color P.exceptional j y).1 hy'.1
      rw [Stability.mem_retainedCrossNonneighbors]
      exact ⟨hyj.2, by simpa [hxi.1, hyj.1] using hij, hy'.2⟩
    have hcardR : (Bad.card : ℝ) ≤ (R.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hsmall := P.crossNonneighbors_small i x hx
    have hceil : epsilon * (Fintype.card V : ℝ) ≤ (B : ℝ) := by
      exact Nat.le_ceil (epsilon * (Fintype.card V : ℝ))
    have hltR : (Bad.card : ℝ) < (B : ℝ) :=
      hcardR.trans_lt (hsmall.trans_le hceil)
    have hlt : Bad.card < B := by exact_mod_cast hltR
    exact Nat.le_of_lt hlt
  obtain ⟨T, hT, hcross⟩ :=
    exists_complete_multipartite G S (3 * p) B 3 (by omega) hsize hbad
  apply completeEquipartite_isContained_of_selected S T hT
  · intro i x hxi j hxj
    have hi := (Stability.mem_retainedFiber P.color P.exceptional i x).1 hxi
    have hj := (Stability.mem_retainedFiber P.color P.exceptional j x).1 hxj
    exact hi.1.symm.trans hj.1
  · exact hcross

theorem stablePartition_completeEquipartiteGraph_three_isContained_of_real_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {p : ℕ} {epsilon : ℝ} (P : Stability.StablePartition G p epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hnumeric :
      (3 * (p : ℝ)) * (epsilon * (Fintype.card V : ℝ) + 1) + 3 ≤
        (Fintype.card V : ℝ) / p - epsilon * (Fintype.card V : ℝ)) :
    SimpleGraph.completeEquipartiteGraph p 3 ⊑ G := by
  apply stablePartition_completeEquipartiteGraph_three_isContained P hepsilon
  have hceil : (⌈epsilon * (Fintype.card V : ℝ)⌉₊ : ℝ) <
      epsilon * (Fintype.card V : ℝ) + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg hepsilon (by positivity))
  have hp0 : (0 : ℝ) ≤ 3 * p := by positivity
  norm_num [Nat.cast_add, Nat.cast_mul] at ⊢
  nlinarith [mul_le_mul_of_nonneg_left hceil.le hp0]

/-- A contained `K_p(3)` in a diameter graph can be unpacked as three-point
geometric seeds, with every cross-part distance equal to one. -/
theorem exists_three_point_seedFamily_of_completeEquipartite
    {d p : ℕ} {A : Finset (Point d)}
    (hseed : SimpleGraph.completeEquipartiteGraph p 3 ⊑ diameterGraph A) :
    ∃ S : Fin p → Finset (Point d),
      (∀ i, (S i).card = 3) ∧
      ∀ i j, i ≠ j → ∀ x ∈ S i, ∀ y ∈ S j, dist x y = 1 := by
  classical
  obtain ⟨K⟩ :=
    SimpleGraph.completeEquipartiteGraph_isContained_iff.mp hseed
  have hparts : K.parts.card = p := K.card_parts.resolve_right (by norm_num)
  let e : Fin p ≃ {s // s ∈ K.parts} :=
    (Finset.equivFinOfCardEq hparts).symm
  let valEmbedding : {x : Point d // x ∈ A} ↪ Point d :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let S : Fin p → Finset (Point d) := fun i ↦ (e i).1.map valEmbedding
  refine ⟨S, ?_, ?_⟩
  · intro i
    rw [show (S i).card = (e i).1.card by simp [S, valEmbedding]]
    exact K.card_mem_parts (e i).2
  · intro i j hij x hx y hy
    obtain ⟨xA, hxpart, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨yA, hypart, rfl⟩ := Finset.mem_map.mp hy
    have heij : (e i).1 ≠ (e j).1 := by
      intro h
      exact hij (e.injective (Subtype.ext h))
    have hadj : (diameterGraph A).Adj xA yA :=
      K.isCompleteBetween (e i).2 (e j).2 heij hxpart hypart
    exact (diameterGraph_adj A xA yA).1 hadj

/-- The geometric rigidity yielded by each pair of three-point seeds:
their affine directions are orthogonal, and both lie on concentric spheres
whose squared radii add to one. -/
theorem exists_three_point_seedFamily_with_pairGeometry
    {d p : ℕ} {A : Finset (Point d)}
    (hseed : SimpleGraph.completeEquipartiteGraph p 3 ⊑ diameterGraph A) :
    ∃ S : Fin p → Finset (Point d),
      (∀ i, (S i).card = 3) ∧
      (∀ i j, i ≠ j → ∀ x ∈ S i, ∀ y ∈ S j, dist x y = 1) ∧
      ∀ i j, i ≠ j →
        (affineSpan ℝ (S i : Set (Point d))).direction ⟂
            (affineSpan ℝ (S j : Set (Point d))).direction ∧
          ∃ c : Point d, ∃ r s : ℝ,
            c ∈ affineSpan ℝ (S i : Set (Point d)) ∧
            0 < r ∧ 0 < s ∧
            (∀ a ∈ S i, dist a c = r) ∧
            (∀ b ∈ S j, dist b c = s) ∧ r ^ 2 + s ^ 2 = 1 := by
  obtain ⟨S, hcard, hcross⟩ :=
    exists_three_point_seedFamily_of_completeEquipartite hseed
  refine ⟨S, hcard, hcross, ?_⟩
  intro i j hij
  apply completeBipartiteGeometry_finset_pos
  · simp [hcard i]
  · simp [hcard j]
  · exact hcross i j hij

/-! ## The leftover-axis equations -/

/-- Four distinct parts remove the one-dimensional translation freedom of
pairwise cross-unit circles. -/
theorem axis_center_of_four_parts
    {p : ℕ} (z radiusSq : Fin p → ℝ)
    (hcross : ∀ {i j : Fin p}, i ≠ j →
      radiusSq i + radiusSq j + (z i - z j) ^ 2 = 1)
    {i j k l : Fin p}
    (_hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hzij : z i ≠ z j) :
    ∀ m, radiusSq m + (z m - z k) ^ 2 = (1 : ℝ) / 2 := by
  have hik' := hcross hik
  have hjk' := hcross hjk
  have hil' := hcross hil
  have hjl' := hcross hjl
  have hkl' := hcross hkl
  have hzlk : z l = z k := by
    by_contra hne
    have hprod : (z i - z j) * (z l - z k) = 0 := by nlinarith
    exact hzij (sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right
      (sub_ne_zero.mpr hne)))
  rw [hzlk] at hil' hjl' hkl'
  have hrkl : radiusSq k = radiusSq l := by nlinarith
  have hrk : radiusSq k = (1 : ℝ) / 2 := by nlinarith
  intro m
  by_cases hmi : m = i
  · subst m
    nlinarith
  by_cases hmj : m = j
  · subst m
    nlinarith
  have him := hcross hmi
  have hjm := hcross hmj
  have hzmk : z m = z k := by
    by_contra hne
    have hprod : (z i - z j) * (z m - z k) = 0 := by nlinarith
    exact hzij (sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right
      (sub_ne_zero.mpr hne)))
  have hrm : radiusSq m = radiusSq k := by
    have hsq : (z k - z i) ^ 2 = (z i - z k) ^ 2 := by ring
    rw [hzmk] at him
    nlinarith
  rw [hzmk, hrm, hrk]
  norm_num

theorem axis_center_of_three_equal_parts
    {p : ℕ} (z radiusSq : Fin p → ℝ)
    (hcross : ∀ {i j : Fin p}, i ≠ j →
      radiusSq i + radiusSq j + (z i - z j) ^ 2 = 1)
    {i j k : Fin p} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hz : ∀ m, z m = z i) :
    ∀ m, radiusSq m + (z m - z i) ^ 2 = (1 : ℝ) / 2 := by
  have hij' := hcross hij
  have hik' := hcross hik
  have hjk' := hcross hjk
  have hri : radiusSq i = (1 : ℝ) / 2 := by
    rw [hz j] at hij'
    rw [hz k] at hik'
    rw [hz j, hz k] at hjk'
    nlinarith
  intro m
  rw [hz m, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
  by_cases hmi : m = i
  · simpa [hmi] using hri
  have him := hcross hmi
  rw [hz m] at him
  nlinarith

/-- With at least four parts, the pairwise circle equations alone have a
global weak-carrier center on the leftover axis. -/
theorem exists_axis_weak_center_of_four_le
    {p : ℕ} (z radiusSq : Fin p → ℝ) (hp : 4 ≤ p)
    (hcross : ∀ {i j : Fin p}, i ≠ j →
      radiusSq i + radiusSq j + (z i - z j) ^ 2 = 1) :
    ∃ s : ℝ, ∀ m, radiusSq m + (z m - s) ^ 2 = (1 : ℝ) / 2 := by
  let j : Fin p := ⟨0, by omega⟩
  by_cases hzall : ∀ m, z m = z j
  · let i : Fin p := ⟨1, by omega⟩
    let k : Fin p := ⟨2, by omega⟩
    have hij : i ≠ j := by norm_num [i, j]
    have hik : i ≠ k := by norm_num [i, k]
    have hjk : j ≠ k := by norm_num [j, k]
    refine ⟨z i, ?_⟩
    exact axis_center_of_three_equal_parts z radiusSq hcross
      (i := i) (j := j) (k := k) hij hik hjk
      (fun m ↦ (hzall m).trans (hzall i).symm)
  · push Not at hzall
    obtain ⟨i, hzij⟩ := hzall
    have hij : i ≠ j := by
      intro h
      exact hzij (congrArg z h)
    let S : Finset (Fin p) := (Finset.univ.erase i).erase j
    have hjmem : j ∈ Finset.univ.erase i := by simp [hij.symm]
    have hScard : S.card = p - 2 := by
      dsimp [S]
      rw [Finset.card_erase_of_mem hjmem,
        Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin]
      omega
    have hS : 1 < S.card := by omega
    obtain ⟨k, hkS, l, hlS, hkl⟩ := Finset.one_lt_card.mp hS
    have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hkS).2).1
    have hkj : k ≠ j := (Finset.mem_erase.mp hkS).1
    have hli : l ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hlS).2).1
    have hlj : l ≠ j := (Finset.mem_erase.mp hlS).1
    refine ⟨z k, axis_center_of_four_parts z radiusSq hcross
      hij hki.symm hli.symm hkj.symm hlj.symm hkl hzij⟩

/-- A point at unit distance from every cross-unit circle is a pole: with
three parts, all circle centers coincide and all squared radii are one half. -/
theorem pole_forces_equal_centers_and_half_radius
    {p : ℕ} (z radiusSq : Fin p → ℝ) (q : ℝ)
    (hp : 3 ≤ p)
    (hcross : ∀ {i j : Fin p}, i ≠ j →
      radiusSq i + radiusSq j + (z i - z j) ^ 2 = 1)
    (hpole : ∀ i, radiusSq i + (z i - q) ^ 2 = 1) :
    ∃ s : ℝ, (∀ i, z i = s) ∧ (∀ i, radiusSq i = (1 : ℝ) / 2) := by
  let i : Fin p := ⟨0, by omega⟩
  let j : Fin p := ⟨1, by omega⟩
  let k : Fin p := ⟨2, by omega⟩
  have hij : i ≠ j := by norm_num [i, j]
  have hik : i ≠ k := by norm_num [i, k]
  have hjk : j ≠ k := by norm_num [j, k]
  have hprod {a b : Fin p} (hab : a ≠ b) :
      2 * (z a - q) * (z b - q) = 1 := by
    have hab' := hcross hab
    have ha := hpole a
    have hb := hpole b
    nlinarith
  have hti : z i - q ≠ 0 := by
    intro hi
    have := hprod hij
    rw [hi] at this
    norm_num at this
  have htk : z k - q ≠ 0 := by
    intro hk
    have := hprod hik
    rw [hk] at this
    norm_num at this
  have hzij : z i = z j := by
    have hikp := hprod hik
    have hjkp := hprod hjk
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show (z i - z j) * (z k - q) = 0 by nlinarith)).resolve_right
    exact htk
  have hallz (m : Fin p) : z m = z i := by
    by_cases hmi : m = i
    · exact congrArg z hmi
    by_cases hmj : m = j
    · exact (congrArg z hmj).trans hzij.symm
    have hmkp := hprod hmi
    have hjkp := hprod hij.symm
    have : (z m - z j) * (z i - q) = 0 := by nlinarith
    have hmjz : z m = z j :=
      sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hti)
    exact hmjz.trans hzij.symm
  refine ⟨z i, hallz, ?_⟩
  have hsq : (z i - q) ^ 2 = (1 : ℝ) / 2 := by
    have := hprod hij
    rw [← hzij] at this
    simp only [pow_two]
    nlinarith
  intro m
  have hm := hpole m
  rw [hallz m] at hm
  nlinarith

/-- The coordinate vector on the leftover common axis. -/
def axisVector (p : ℕ) (s : ℝ) : Point (2 * p + 1) :=
  EuclideanSpace.single (axisIndex p) s

@[simp] theorem axisVector_apply {p : ℕ} (s : ℝ) (j : Fin (2 * p + 1)) :
    axisVector p s j = if j = axisIndex p then s else 0 := by
  simp [axisVector]

/-- Once the leftover-axis center has been selected, a coaxial circle
certificate transports directly to the canonical odd weak carrier. -/
theorem isWeakCarrierSet_of_coaxial_circle_certificate_of_axis_center
    {p : ℕ} {A : Finset (Point (2 * p + 1))}
    (baseCenter : Point (2 * p + 1))
    (coord : Point (2 * p + 1) ≃ₗᵢ[ℝ] Point (2 * p + 1))
    (part : {x : Point (2 * p + 1) // x ∈ A} → Fin p)
    (z radiusSq : Fin p → ℝ)
    (s : ℝ)
    (hs : ∀ i, radiusSq i + (z i - s) ^ 2 = (1 : ℝ) / 2)
    (hsupport : ∀ (x : {x : Point (2 * p + 1) // x ∈ A}),
      InAxisPlane (part x) (coord.symm (x.1 - baseCenter)))
    (haxis : ∀ (x : {x : Point (2 * p + 1) // x ∈ A}),
      coord.symm (x.1 - baseCenter) (axisIndex p) = z (part x))
    (hnormSq : ∀ (x : {x : Point (2 * p + 1) // x ∈ A}),
      ‖coord.symm (x.1 - baseCenter)‖ ^ 2 =
        radiusSq (part x) + (z (part x)) ^ 2) :
    IsWeakCarrierSet (p := p) A := by
  let center := baseCenter + coord (axisVector p s)
  apply isWeakCarrierSet_of_coordinate_certificate_sq center coord part
  · intro x q hqf hqs hqa
    have hu := hsupport x q hqf hqs hqa
    have he : axisVector p s q = 0 := by simp [axisVector_apply, hqa]
    change (coord.symm (x.1 - center)) q = 0
    have hcoord : coord.symm (x.1 - center) =
        coord.symm (x.1 - baseCenter) - axisVector p s := by
      dsimp [center]
      rw [show x.1 - (baseCenter + coord (axisVector p s)) =
          (x.1 - baseCenter) - coord (axisVector p s) by abel]
      rw [map_sub, coord.symm_apply_apply]
    rw [hcoord, PiLp.sub_apply, hu, he, sub_zero]
  · intro x
    let u := coord.symm (x.1 - baseCenter)
    let e := axisVector p s
    have hcoord : coord.symm (x.1 - center) = u - e := by
      dsimp [center, u, e]
      rw [show x.1 - (baseCenter + coord (axisVector p s)) =
          (x.1 - baseCenter) - coord (axisVector p s) by abel]
      rw [map_sub, coord.symm_apply_apply]
    rw [hcoord, norm_sub_sq_real]
    have hinner : inner ℝ u e = s * z (part x) := by
      dsimp [e, axisVector]
      rw [EuclideanSpace.inner_single_right]
      have huaxis : u (axisIndex p) = z (part x) := by
        simpa [u] using haxis x
      simp [huaxis]
    have hnorme : ‖e‖ ^ 2 = s ^ 2 := by
      dsimp [e, axisVector]
      rw [PiLp.norm_single, Real.norm_eq_abs, sq_abs]
    rw [hinner, hnorme, hnormSq x]
    have hpart := hs (part x)
    nlinarith

/-- With at least four parts, pairwise cross-unit circle equations select
the needed common axis center. -/
theorem isWeakCarrierSet_of_coaxial_circle_certificate_four
    {p : ℕ} {A : Finset (Point (2 * p + 1))} (hp : 4 ≤ p)
    (baseCenter : Point (2 * p + 1))
    (coord : Point (2 * p + 1) ≃ₗᵢ[ℝ] Point (2 * p + 1))
    (part : {x : Point (2 * p + 1) // x ∈ A} → Fin p)
    (z radiusSq : Fin p → ℝ)
    (hsupport : ∀ (x : {x : Point (2 * p + 1) // x ∈ A}),
      InAxisPlane (part x) (coord.symm (x.1 - baseCenter)))
    (haxis : ∀ (x : {x : Point (2 * p + 1) // x ∈ A}),
      coord.symm (x.1 - baseCenter) (axisIndex p) = z (part x))
    (hnormSq : ∀ (x : {x : Point (2 * p + 1) // x ∈ A}),
      ‖coord.symm (x.1 - baseCenter)‖ ^ 2 =
        radiusSq (part x) + (z (part x)) ^ 2)
    (hcross : ∀ {i j : Fin p}, i ≠ j →
      radiusSq i + radiusSq j + (z i - z j) ^ 2 = 1) :
    IsWeakCarrierSet (p := p) A := by
  obtain ⟨s, hs⟩ := exists_axis_weak_center_of_four_le z radiusSq hp hcross
  exact isWeakCarrierSet_of_coaxial_circle_certificate_of_axis_center
    baseCenter coord part z radiusSq s hs hsupport haxis hnormSq

/-- Pole branch, valid already for `p ≥ 3`: a universal unit-distance
point removes the exceptional one-axis-parameter freedom. -/
theorem isWeakCarrierSet_of_coaxial_circle_certificate_pole
    {p : ℕ} {A : Finset (Point (2 * p + 1))} (hp : 3 ≤ p)
    (baseCenter : Point (2 * p + 1))
    (coord : Point (2 * p + 1) ≃ₗᵢ[ℝ] Point (2 * p + 1))
    (part : {x : Point (2 * p + 1) // x ∈ A} → Fin p)
    (z radiusSq : Fin p → ℝ) (q : ℝ)
    (hsupport : ∀ (x : {x : Point (2 * p + 1) // x ∈ A}),
      InAxisPlane (part x) (coord.symm (x.1 - baseCenter)))
    (haxis : ∀ (x : {x : Point (2 * p + 1) // x ∈ A}),
      coord.symm (x.1 - baseCenter) (axisIndex p) = z (part x))
    (hnormSq : ∀ (x : {x : Point (2 * p + 1) // x ∈ A}),
      ‖coord.symm (x.1 - baseCenter)‖ ^ 2 =
        radiusSq (part x) + (z (part x)) ^ 2)
    (hcross : ∀ {i j : Fin p}, i ≠ j →
      radiusSq i + radiusSq j + (z i - z j) ^ 2 = 1)
    (hpole : ∀ i, radiusSq i + (z i - q) ^ 2 = 1) :
    IsWeakCarrierSet (p := p) A := by
  obtain ⟨s, hz, hr⟩ :=
    pole_forces_equal_centers_and_half_radius z radiusSq q hp hcross hpole
  have hs (i : Fin p) : radiusSq i + (z i - s) ^ 2 = (1 : ℝ) / 2 := by
    rw [hz i, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, hr i]
  exact isWeakCarrierSet_of_coaxial_circle_certificate_of_axis_center
    baseCenter coord part z radiusSq s hs hsupport haxis hnormSq

/-! ## The cross defect and strongness -/

/-- The complete multipartite cross-pair count associated with two size
profiles. -/
def pairProductSum {p : ℕ} (a b : Fin p → ℕ) : ℕ :=
  ∑ i, ∑ j with i < j, a i * b j

/-- The defect in the cross-edge count of a weak odd carrier.  Off-equator
points in two different sphere components cannot be at unit distance, so
the missing cross pairs are exactly these products. -/
def crossDefect {p : ℕ} (off : Fin p → ℕ) : ℕ :=
  pairProductSum off off

/-- The numerical strongness condition: at most one component contains an
off-equator point. -/
def IsStrongProfile {p : ℕ} (off : Fin p → ℕ) : Prop :=
  ∀ i j, i ≠ j → off i = 0 ∨ off j = 0

theorem Assignment.isStrongCarrierSet_of_isStrongProfile
    {d p : ℕ} {A : Finset (Point d)} (Q : Assignment (p := p) A)
    (hp : 0 < p) (hstrong : IsStrongProfile Q.offCount) :
    IsStrongCarrierSet (p := p) A :=
  Q.isStrongCarrierSet hp hstrong

theorem crossDefect_eq_zero_iff {p : ℕ} (off : Fin p → ℕ) :
    crossDefect off = 0 ↔ IsStrongProfile off := by
  classical
  rw [crossDefect, pairProductSum, Finset.sum_eq_zero_iff]
  constructor
  · intro h i j hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hz := (Finset.sum_eq_zero_iff.mp (h i (Finset.mem_univ i)))
          j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hij⟩)
      exact Nat.mul_eq_zero.mp hz
    · have hz := (Finset.sum_eq_zero_iff.mp (h j (Finset.mem_univ j)))
          i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hji⟩)
      exact (Nat.mul_eq_zero.mp hz).symm
  · intro h i _
    apply Finset.sum_eq_zero
    intro j hj
    exact Nat.mul_eq_zero.mpr (h i j (ne_of_lt (Finset.mem_filter.mp hj).2))

theorem crossDefect_eq_zero_of_isStrongProfile {p : ℕ} {off : Fin p → ℕ}
    (h : IsStrongProfile off) : crossDefect off = 0 :=
  (crossDefect_eq_zero_iff off).2 h

theorem isStrongProfile_of_crossDefect_eq_zero {p : ℕ} {off : Fin p → ℕ}
    (h : crossDefect off = 0) : IsStrongProfile off :=
  (crossDefect_eq_zero_iff off).1 h

/-- The missing cross pairs incident to a specified component. -/
def defectFrom {p : ℕ} (off : Fin p → ℕ) (r : Fin p) : ℕ :=
  ∑ i ∈ Finset.univ.erase r, off r * off i

/-- The number of off-equator points outside a specified component. -/
def otherOffTotal {p : ℕ} (off : Fin p → ℕ) (r : Fin p) : ℕ :=
  ∑ i ∈ Finset.univ.erase r, off i

/-- An abstract replacement principle.  If replacing component `r` gains
all of its incident cross defect and cannot improve an optimum, every other
component is equatorial. -/
theorem weak_to_strong_of_replacement_gain {p edges replacementEdges : ℕ}
    (off : Fin p → ℕ) (r : Fin p) (hr : 0 < off r)
    (hoptimal : replacementEdges ≤ edges)
    (hgain : edges + defectFrom off r ≤ replacementEdges) :
    IsStrongProfile off := by
  have hdefect : defectFrom off r = 0 := by omega
  have hoff (i : Fin p) (hir : i ≠ r) : off i = 0 := by
    have hmem : i ∈ Finset.univ.erase r := by simp [hir]
    have hprod : off r * off i = 0 :=
      (Finset.sum_eq_zero_iff.mp hdefect) i hmem
    exact (Nat.mul_eq_zero.mp hprod).resolve_left (Nat.ne_of_gt hr)
  intro i j hij
  rcases eq_or_ne i r with rfl | hir
  · exact Or.inr (hoff j (by simpa using hij.symm))
  · exact Or.inl (hoff i hir)

/-- The corrected no-pole replacement argument.

Replacing all `size r` points in sphere `r` by one pole and `size r - 1`
equatorial points changes the cross contribution by
`(off r - 1) * otherOffTotal off r`.  The subtraction of one is essential:
the new pole is not at unit distance from off-equator points in other
components. -/
theorem weak_to_strong_of_corrected_noPole_replacement
    {p edges replacementEdges : ℕ}
    (size off inside : Fin p → ℕ) (r : Fin p)
    (hr : 0 < off r)
    (hinside : inside r ≤ size r)
    (hsingleton : off r = 1 → inside r < size r)
    (hoptimal : replacementEdges ≤ edges)
    (hgain : edges + (size r - inside r) +
      (off r - 1) * otherOffTotal off r ≤ replacementEdges) :
    IsStrongProfile off := by
  have hlocalGap : size r - inside r = 0 := by omega
  have hinsEq : inside r = size r := by omega
  have hnotone : off r ≠ 1 := by
    intro hone
    have := hsingleton hone
    omega
  have hoffSubPos : 0 < off r - 1 := by omega
  have hcrossGap : (off r - 1) * otherOffTotal off r = 0 := by omega
  have hother : otherOffTotal off r = 0 :=
    (Nat.mul_eq_zero.mp hcrossGap).resolve_left (Nat.ne_of_gt hoffSubPos)
  have hoff (i : Fin p) (hir : i ≠ r) : off i = 0 := by
    have hmem : i ∈ Finset.univ.erase r := by simp [hir]
    exact (Finset.sum_eq_zero_iff.mp hother) i hmem
  intro i j hij
  rcases eq_or_ne i r with rfl | hir
  · exact Or.inr (hoff j (by simpa using hij.symm))
  · exact Or.inl (hoff i hir)

/-- In the geometric application, a sphere class with a unique
off-equator point has at most two local diameters.  This convenient wrapper
turns that bound and `3 ≤ size r` into the strict local deficit needed by
the corrected replacement argument. -/
theorem weak_to_strong_of_corrected_noPole_replacement_of_local_two
    {p edges replacementEdges : ℕ}
    (size off inside : Fin p → ℕ) (r : Fin p)
    (hr : 0 < off r)
    (hsize : 3 ≤ size r)
    (hinside : inside r ≤ size r)
    (hsingletonTwo : off r = 1 → inside r ≤ 2)
    (hoptimal : replacementEdges ≤ edges)
    (hgain : edges + (size r - inside r) +
      (off r - 1) * otherOffTotal off r ≤ replacementEdges) :
    IsStrongProfile off := by
  apply weak_to_strong_of_corrected_noPole_replacement
    size off inside r hr hinside
  · intro hone
    have := hsingletonTwo hone
    omega
  · exact hoptimal
  · exact hgain

/-- For a class with at least two off-equator points, the corrected
whole-class replacement and extremality already force every other class to
be equatorial. -/
lemma otherOffTotal_eq_zero_of_corrected_replacement_of_two_le
    {p edges replacementEdges : ℕ}
    (size off inside : Fin p → ℕ) (r : Fin p)
    (hoff : 2 ≤ off r) (_hinside : inside r ≤ size r)
    (hoptimal : replacementEdges ≤ edges)
    (hgain : edges + (size r - inside r) +
      (off r - 1) * otherOffTotal off r ≤ replacementEdges) :
    otherOffTotal off r = 0 := by
  have hcross : (off r - 1) * otherOffTotal off r = 0 := by omega
  have hpos : 0 < off r - 1 := by omega
  exact (Nat.mul_eq_zero.mp hcross).resolve_left (Nat.ne_of_gt hpos)

lemma isStrongProfile_of_otherOffTotal_eq_zero {p : ℕ}
    (off : Fin p → ℕ) (r : Fin p) (hzero : otherOffTotal off r = 0) :
    IsStrongProfile off := by
  have hoff (i : Fin p) (hir : i ≠ r) : off i = 0 := by
    have hmem : i ∈ Finset.univ.erase r := by simp [hir]
    exact (Finset.sum_eq_zero_iff.mp hzero) i hmem
  intro i j hij
  rcases eq_or_ne i r with rfl | hir
  · exact Or.inr (hoff j (by simpa using hij.symm))
  · exact Or.inl (hoff i hir)

/-! ## Finite optimization with a common pole -/

/-- The numerical data extracted from a diameter-one weak carrier that
contains one common pole.  The common pole is excluded from `size`; its
incident local edges are included in `inside`.

The `cross_add_defect` field is the exact cross-sphere calculation, and
`inside_le` is the radius-`1 / sqrt 2` local sphere bound. -/
structure WeakCarrierCounts (p : ℕ) where
  size : Fin p → ℕ
  off : Fin p → ℕ
  cross : Fin p → Fin p → ℕ
  inside : Fin p → ℕ
  off_le_size : ∀ i, off i ≤ size i
  cross_add_defect : ∀ {i j : Fin p}, i < j →
    cross i j + off i * off j = size i * size j
  inside_le : ∀ i, inside i ≤ size i + 1

namespace WeakCarrierCounts

variable {p : ℕ} (W : WeakCarrierCounts p)

/-- Total cross-component diameter count. -/
def crossSum : ℕ := ∑ i, ∑ j with i < j, W.cross i j

/-- Sum of the local sphere diameter counts, each including the common
pole. -/
def localSum : ℕ := ∑ i, W.inside i

/-- Total diameter count represented by the profile. -/
def edgeCount : ℕ := W.crossSum + W.localSum

/-- Number of non-pole points represented by the profile. -/
def partTotal : ℕ := ∑ i, W.size i

lemma crossSum_add_crossDefect :
    W.crossSum + crossDefect W.off = pairProductSum W.size W.size := by
  rw [crossSum, crossDefect, pairProductSum, pairProductSum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  exact W.cross_add_defect (Finset.mem_filter.mp hj).2

lemma localSum_le : W.localSum ≤ W.partTotal + p := by
  calc
    W.localSum ≤ ∑ i : Fin p, (W.size i + 1) :=
      Finset.sum_le_sum fun i _ ↦ W.inside_le i
    _ = (∑ i : Fin p, W.size i) + ∑ _i : Fin p, 1 :=
      Finset.sum_add_distrib
    _ = W.partTotal + p := by simp [partTotal]

/-- Full weak-carrier count plus the off-equator defect is bounded by the
complete multipartite contribution plus the local sphere allowance. -/
lemma edgeCount_add_crossDefect_le {T : ℕ}
    (hT : pairProductSum W.size W.size ≤ T) :
    W.edgeCount + crossDefect W.off ≤ T + W.partTotal + p := by
  calc
    W.edgeCount + crossDefect W.off =
        (W.crossSum + crossDefect W.off) + W.localSum := by
      simp only [edgeCount]
      omega
    _ = pairProductSum W.size W.size + W.localSum := by
      rw [W.crossSum_add_crossDefect]
    _ ≤ T + (W.partTotal + p) := Nat.add_le_add hT W.localSum_le
    _ = T + W.partTotal + p := by omega

/-- Swanepoel's valid with-pole weak-to-strong optimization.  Reaching the
strong benchmark forces the entire cross defect to vanish. -/
theorem weak_to_strong_of_lower_bound_with_pole {T : ℕ}
    (hT : pairProductSum W.size W.size ≤ T)
    (hlower : T + W.partTotal + p ≤ W.edgeCount) :
    IsStrongProfile W.off := by
  apply isStrongProfile_of_crossDefect_eq_zero
  have hu := W.edgeCount_add_crossDefect_le hT
  omega

/-- A wrapper matching the usual notation: there are `n - 1` non-pole
points. -/
theorem weak_to_strong_of_total_eq_n_sub_one {T n : ℕ}
    (htotal : W.partTotal = n - 1)
    (hT : pairProductSum W.size W.size ≤ T)
    (hlower : T + (n - 1) + p ≤ W.edgeCount) :
    IsStrongProfile W.off := by
  apply W.weak_to_strong_of_lower_bound_with_pole hT
  simpa [htotal] using hlower

end WeakCarrierCounts

/-! The following wrappers connect the numerical optimization back to the
geometric carrier predicate.  All geometric work is concentrated in
constructing the exact `WeakCarrierCounts` record; once its `off` profile
agrees with the assigned profile, strongness is no longer merely a
counting statement. -/

theorem Assignment.isStrongCarrierSet_of_lower_bound_with_pole
    {d p : ℕ} {A : Finset (Point d)} (Q : Assignment (p := p) A)
    (hp : 0 < p) (W : WeakCarrierCounts p) (hoff : W.off = Q.offCount)
    {T : ℕ} (hT : pairProductSum W.size W.size ≤ T)
    (hlower : T + W.partTotal + p ≤ W.edgeCount) :
    IsStrongCarrierSet (p := p) A := by
  apply Q.isStrongCarrierSet_of_isStrongProfile hp
  have hs := W.weak_to_strong_of_lower_bound_with_pole hT hlower
  simpa [hoff] using hs

theorem Assignment.isStrongCarrierSet_of_corrected_noPole_replacement
    {d p edges replacementEdges : ℕ} {A : Finset (Point d)}
    (Q : Assignment (p := p) A) (hp : 0 < p)
    (size inside : Fin p → ℕ) (r : Fin p) (hr : 0 < Q.offCount r)
    (hinside : inside r ≤ size r)
    (hsingleton : Q.offCount r = 1 → inside r < size r)
    (hoptimal : replacementEdges ≤ edges)
    (hgain : edges + (size r - inside r) +
      (Q.offCount r - 1) * otherOffTotal Q.offCount r ≤ replacementEdges) :
    IsStrongCarrierSet (p := p) A := by
  apply Q.isStrongCarrierSet_of_isStrongProfile hp
  exact weak_to_strong_of_corrected_noPole_replacement
    size Q.offCount inside r hr hinside hsingleton hoptimal hgain

/-! ## The exact odd correction term -/

/-- Adding one vertex to a balanced `p`-partite Turán graph adds
`n - n / p` edges. -/
theorem turanNumber_succ (p n : ℕ) (hp : 0 < p) :
    turanNumber p (n + 1) = turanNumber p n + (n - n / p) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hnp : n < p
      · have top_card (q : ℕ) (hq : q ≤ p) : turanNumber p q = q.choose 2 := by
          let e : SimpleGraph.turanGraph q p ≃g (⊤ : SimpleGraph (Fin q)) :=
            { Equiv.refl (Fin q) with
              map_rel_iff' := by
                exact (congrArg (fun G : SimpleGraph (Fin q) ↦ G.Adj _ _)
                  (SimpleGraph.turanGraph_eq_top.mpr (.inr hq))).symm.to_iff }
          change (SimpleGraph.turanGraph q p).edgeFinset.card = q.choose 2
          rw [e.card_edgeFinset_eq,
            SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
        rw [top_card n hnp.le, top_card (n + 1) (by omega), Nat.choose_succ_succ,
          Nat.div_eq_of_lt hnp]
        simp
        ac_rfl
      · let k := n - p
        have hnk : n = k + p := by omega
        have hk : k < n := by omega
        rw [show n + 1 = (k + 1) + p by omega,
          show turanNumber p ((k + 1) + p) =
              turanNumber p (k + 1) + (k + 1) * (p - 1) + p.choose 2 by
            exact SimpleGraph.card_edgeFinset_turanGraph_add,
          hnk,
          show turanNumber p (k + p) =
              turanNumber p k + k * (p - 1) + p.choose 2 by
            exact SimpleGraph.card_edgeFinset_turanGraph_add,
          ih k hk, Nat.add_div_right k hp]
        have hdiv : k / p ≤ k := Nat.div_le_self k p
        have hsub : k + p - (k / p + 1) = (k - k / p) + (p - 1) := by omega
        rw [hsub, add_mul]
        simp only [one_mul]
        omega

/-- The two standard forms of the odd-dimensional correction agree:
`t_p(n-1) + n-1+p = t_p(n) + ceil(n/p) + p-1`. -/
theorem turanNumber_pred_add (p n : ℕ) (hp : 0 < p) (hn : 0 < n) :
    turanNumber p (n - 1) + n = turanNumber p n + ceilQuot n p := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hceil : ceilQuot (k + 1) p = k / p + 1 := by
    rw [ceilQuot_eq_succ_pred_div (by omega) hp]
    simp
  rw [Nat.add_one_sub_one, turanNumber_succ p k hp, hceil]
  have hdiv : k / p ≤ k := Nat.div_le_self k p
  omega

theorem turanNumber_pred_add_correction (p n : ℕ) (hp : 0 < p) (hn : 0 < n) :
    turanNumber p (n - 1) + (n - 1) + p =
      turanNumber p n + ceilQuot n p + (p - 1) := by
  have h := turanNumber_pred_add p n hp hn
  omega

/-! ## Turán optimization for arbitrary part sizes -/

/-- Twice the number of cross pairs in a finite part-size profile. -/
def orderedCross {p : ℕ} (m : Fin p → ℕ) : ℕ :=
  ∑ i, ∑ j with i ≠ j, m i * m j

lemma orderedCross_succ (p : ℕ) (m : Fin (p + 1) → ℕ) :
    orderedCross m =
      2 * m 0 * (∑ i : Fin p, m i.succ) +
        orderedCross (fun i : Fin p ↦ m i.succ) := by
  have zero_ne_succ (i : Fin p) : (0 : Fin (p + 1)) ≠ i.succ :=
    (Fin.succ_ne_zero i).symm
  simp only [orderedCross]
  simp_rw [Finset.sum_filter]
  simp [Fin.sum_univ_succ, zero_ne_succ, Finset.sum_add_distrib,
    Finset.mul_sum]
  have hcomm : (∑ i : Fin p, m i.succ * m 0) =
      ∑ i : Fin p, m 0 * m i.succ := by
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm]
  have hdouble : (∑ i : Fin p, 2 * m 0 * m i.succ) =
      (∑ i : Fin p, m 0 * m i.succ) +
        ∑ i : Fin p, m 0 * m i.succ := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hcomm, hdouble]
  ac_rfl

lemma two_dvd_orderedCross {p : ℕ} (m : Fin p → ℕ) : 2 ∣ orderedCross m := by
  induction p with
  | zero => simp [orderedCross]
  | succ p ih =>
      rw [orderedCross_succ]
      apply dvd_add
      · use m 0 * ∑ i : Fin p, m i.succ
        ring
      · exact ih (fun i ↦ m i.succ)

/-- The number of unordered cross pairs in a part-size profile. -/
def crossPairs {p : ℕ} (m : Fin p → ℕ) : ℕ := orderedCross m / 2

lemma two_mul_crossPairs {p : ℕ} (m : Fin p → ℕ) :
    2 * crossPairs m = orderedCross m := by
  exact Nat.mul_div_cancel' (two_dvd_orderedCross m)

lemma orderedCross_comp_equiv {p : ℕ} (m : Fin p → ℕ)
    (e : Fin p ≃ Fin p) :
    orderedCross (fun i ↦ m (e i)) = orderedCross m := by
  simp only [orderedCross]
  simp_rw [Finset.sum_filter]
  calc
    (∑ i, ∑ j, if i ≠ j then m (e i) * m (e j) else 0) =
        ∑ i, ∑ j, if e i ≠ e j then m (e i) * m (e j) else 0 := by simp
    _ = ∑ i, ∑ j, if e i ≠ j then m (e i) * m j else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      exact Equiv.sum_comp e (fun j ↦ if e i ≠ j then m (e i) * m j else 0)
    _ = ∑ i, ∑ j, if i ≠ j then m i * m j else 0 :=
      Equiv.sum_comp e (fun i ↦ ∑ j, if i ≠ j then m i * m j else 0)

lemma crossPairs_comp_equiv {p : ℕ} (m : Fin p → ℕ)
    (e : Fin p ≃ Fin p) :
    crossPairs (fun i ↦ m (e i)) = crossPairs m := by
  simp [crossPairs, orderedCross_comp_equiv]

lemma crossPairs_succ (p : ℕ) (m : Fin (p + 1) → ℕ) :
    crossPairs m =
      m 0 * (∑ i : Fin p, m i.succ) +
        crossPairs (fun i : Fin p ↦ m i.succ) := by
  apply mul_left_cancel₀ (by norm_num : (2 : ℕ) ≠ 0)
  rw [two_mul_crossPairs m, orderedCross_succ, mul_add,
    two_mul_crossPairs (fun i : Fin p ↦ m i.succ)]
  ring

/-- The complete multipartite graph with arbitrary part sizes is
`K_(p+1)`-free, so its cross-pair count is at most the balanced Turán
number. -/
lemma orderedCross_le_two_turan {p : ℕ} (m : Fin p → ℕ) :
    orderedCross m ≤ 2 * turanNumber p (∑ i, m i) := by
  let H : SimpleGraph (Σ i, Fin (m i)) :=
    ⟨fun x y ↦ x.1 ≠ y.1, by tauto, by tauto⟩
  have cfH : H.CliqueFree (p + 1) := fun s ⟨hs₁, hs₂⟩ ↦ by
    have c := (s.image (·.1)).card_le_univ
    rw [Fintype.card_fin] at c
    apply absurd c
    have ic : (SetLike.coe s).InjOn (·.1) :=
      fun v mv w mw e ↦ not_imp_not.mp (hs₁ mv mw) e
    rw [not_le, Finset.card_image_of_injOn ic]
    omega
  replace cfH := cfH.card_edgeFinset_le
  simp_rw [← SimpleGraph.card_edgeFinset_turanGraph] at cfH
  rw [show Fintype.card (Σ i, Fin (m i)) = ∑ i, m i by simp] at cfH
  have eH : orderedCross m = 2 * H.edgeFinset.card := by
    have degree_eq_sum (i : Σ i, Fin (m i)) :
        H.degree i = ∑ j, if H.Adj i j then 1 else 0 :=
      H.degree_eq_sum_if_adj i
    simp_rw [← SimpleGraph.sum_degrees_eq_twice_card_edges,
      degree_eq_sum, Fintype.sum_sigma, H]
    have rsum (c₁ c₂ : Fin p) :
        (∑ x : Fin (m c₁), ∑ y : Fin (m c₂), if c₁ ≠ c₂ then 1 else 0) =
          if c₁ ≠ c₂ then m c₁ * m c₂ else 0 := by simp
    conv_rhs =>
      enter [2, c₁]
      rw [Finset.sum_comm]
      enter [2, c₂]
      rw [rsum]
    simp_rw [orderedCross, Finset.sum_filter]
  rwa [eH, mul_le_mul_iff_right₀ zero_lt_two]

theorem crossPairs_le_turan {p : ℕ} (m : Fin p → ℕ) :
    crossPairs m ≤ turanNumber p (∑ i, m i) := by
  have h := orderedCross_le_two_turan m
  rw [← two_mul_crossPairs] at h
  omega

lemma pairProductSum_succ (p : ℕ) (m : Fin (p + 1) → ℕ) :
    pairProductSum m m =
      m 0 * (∑ i : Fin p, m i.succ) +
        pairProductSum (fun i : Fin p ↦ m i.succ)
          (fun i : Fin p ↦ m i.succ) := by
  simp only [pairProductSum]
  simp_rw [Finset.sum_filter]
  simp [Fin.sum_univ_succ, Finset.mul_sum]

/-- The earlier order-based definition of cross pairs agrees with the
symmetrized graph-theoretic definition. -/
lemma pairProductSum_eq_crossPairs {p : ℕ} (m : Fin p → ℕ) :
    pairProductSum m m = crossPairs m := by
  induction p with
  | zero => simp [pairProductSum, crossPairs, orderedCross]
  | succ p ih =>
      rw [pairProductSum_succ, crossPairs_succ, ih]

/-- Exact optimization when the distinguished full sphere is part zero.
Removing one point from that part turns the local correction into the
standard `t_p(n-1)+n` expression. -/
theorem strongCarrierOptimization_zero (p n : ℕ)
    (m : Fin (p + 1) → ℕ) (hsum : ∑ i, m i = n) :
    crossPairs m + m 0 + p ≤
      turanNumber (p + 1) n + ceilQuot n (p + 1) + p := by
  by_cases hm0 : m 0 = 0
  · have hcross := crossPairs_le_turan m
    rw [hsum] at hcross
    omega
  · have hm0pos : 0 < m 0 := Nat.pos_of_ne_zero hm0
    let tailSum := ∑ i : Fin p, m i.succ
    have hsum' : m 0 + tailSum = n := by
      simpa only [Fin.sum_univ_succ] using hsum
    let m' : Fin (p + 1) → ℕ :=
      Fin.cases (m 0 - 1) (fun i ↦ m i.succ)
    have hm'_sum : ∑ i, m' i = n - 1 := by
      rw [Fin.sum_univ_succ]
      simp only [m', Fin.cases_zero, Fin.cases_succ]
      omega
    have hcross' := crossPairs_le_turan m'
    rw [hm'_sum] at hcross'
    have hrel : crossPairs m + m 0 = crossPairs m' + n := by
      rw [crossPairs_succ p m, crossPairs_succ p m']
      simp only [m', Fin.cases_zero, Fin.cases_succ]
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm0
      have hsumk : k + 1 + tailSum = n := by omega
      rw [hk]
      simp only [Nat.add_one_sub_one]
      rw [← hsumk]
      simp only [tailSum, Nat.succ_eq_add_one]
      ring
    have hnpos : 0 < n := by omega
    have ht := turanNumber_pred_add (p + 1) n (by omega) hnpos
    omega

/-- The exact optimization with an arbitrary distinguished full-sphere
part. -/
theorem strongCarrierOptimization_distinguished (p n : ℕ) (hp : 0 < p)
    (m : Fin p → ℕ) (hsum : ∑ i, m i = n) (r : Fin p) :
    crossPairs m + m r + (p - 1) ≤
      turanNumber p n + ceilQuot n p + (p - 1) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  let e : Fin (q + 1) ≃ Fin (q + 1) := Equiv.swap 0 r
  let m' : Fin (q + 1) → ℕ := fun i ↦ m (e i)
  have hm'_sum : ∑ i, m' i = n := by
    exact (Equiv.sum_comp e m).trans hsum
  have h := strongCarrierOptimization_zero q n m' hm'_sum
  rw [crossPairs_comp_equiv m e] at h
  simpa [m', e] using h

/-- The exact strong-carrier optimization, in the order-based cross-pair
notation used by `WeakCarrierCounts`. -/
theorem strongCarrierOptimization_pairProductSum_zero (p n : ℕ)
    (m : Fin (p + 1) → ℕ) (hsum : ∑ i, m i = n) :
    pairProductSum m m + m 0 + p ≤
      turanNumber (p + 1) n + ceilQuot n (p + 1) + p := by
  rw [pairProductSum_eq_crossPairs]
  exact strongCarrierOptimization_zero p n m hsum

theorem strongCarrierOptimization_pairProductSum_distinguished
    (p n : ℕ) (hp : 0 < p) (m : Fin p → ℕ)
    (hsum : ∑ i, m i = n) (r : Fin p) :
    pairProductSum m m + m r + (p - 1) ≤
      turanNumber p n + ceilQuot n p + (p - 1) := by
  rw [pairProductSum_eq_crossPairs]
  exact strongCarrierOptimization_distinguished p n hp m hsum r

/-- The all-concyclic leftover-axis branch cannot attain the strong odd
Lenz lower bound.  This is the exact numerical endpoint needed in dimension
seven: complete cross pairs contribute at most the Turán number, while a
large-radius circle contributes at most one local diameter. -/
theorem allConcyclic_profile_lt_strongLower
    {p n : ℕ} (hp : 0 < p) (size inside : Fin p → ℕ)
    (hsum : ∑ i, size i = n) (hinside : ∀ i, inside i ≤ 1)
    (hceil : 1 < ceilQuot n p) :
    pairProductSum size size + ∑ i, inside i <
      turanNumber p n + ceilQuot n p + (p - 1) := by
  have hcross : pairProductSum size size ≤ turanNumber p n := by
    rw [pairProductSum_eq_crossPairs, ← hsum]
    exact crossPairs_le_turan size
  have hlocal : ∑ i, inside i ≤ p := by
    calc
      ∑ i, inside i ≤ ∑ _i : Fin p, 1 :=
        Finset.sum_le_sum fun i _hi ↦ hinside i
      _ = p := by simp
  omega

/-! ## The repaired no-pole extremal argument -/

/-- Fully finite repaired no-pole classifier.  If some class has at least
two off-equator points, the corrected replacement makes it unique.  If all
classes have at most one, the elementary local bound `inside ≤ 3` gives
`edges ≤ t_p(n)+3p`, contradicting the strong lower correction. -/
theorem noPole_extremal_isStrongProfile
    {p n edges : ℕ} (size off inside : Fin p → ℕ)
    (hsum : ∑ i, size i = n)
    (hedges : edges + crossDefect off =
      pairProductSum size size + ∑ i, inside i)
    (hlocalSmall : ∀ i, off i ≤ 1 → inside i ≤ 3)
    (hreplacement_large : ∀ r, 2 ≤ off r → otherOffTotal off r = 0)
    (hlower : turanNumber p n + ceilQuot n p + (p - 1) ≤ edges)
    (hcorrection : 3 * p < ceilQuot n p + (p - 1)) :
    IsStrongProfile off := by
  by_cases hlarge : ∃ r, 2 ≤ off r
  · obtain ⟨r, hr⟩ := hlarge
    exact isStrongProfile_of_otherOffTotal_eq_zero off r
      (hreplacement_large r hr)
  · have hoffSmall (i : Fin p) : off i ≤ 1 := by
      by_contra h
      exact hlarge ⟨i, by omega⟩
    have hlocal : (∑ i, inside i) ≤ 3 * p := by
      calc
        (∑ i, inside i) ≤ ∑ _i : Fin p, 3 :=
          Finset.sum_le_sum fun i _ ↦ hlocalSmall i (hoffSmall i)
        _ = 3 * p := by simp [mul_comm]
    have hcross : pairProductSum size size ≤ turanNumber p n := by
      rw [pairProductSum_eq_crossPairs, ← hsum]
      exact crossPairs_le_turan size
    have hu : edges + crossDefect off ≤ turanNumber p n + 3 * p := by
      rw [hedges]
      exact Nat.add_le_add hcross hlocal
    omega

/-- The repaired no-pole classifier with its uniqueness conclusion derived
from explicit replacement configurations and extremality. -/
theorem noPole_extremal_isStrongProfile_of_replacements
    {p n edges : ℕ} (size off inside : Fin p → ℕ)
    (hsum : ∑ i, size i = n)
    (hedges : edges + crossDefect off =
      pairProductSum size size + ∑ i, inside i)
    (hinside : ∀ i, inside i ≤ size i)
    (hlocalSmall : ∀ i, off i ≤ 1 → inside i ≤ 3)
    (hreplacement : ∀ r, 2 ≤ off r → ∃ replacementEdges,
      replacementEdges ≤ edges ∧
      edges + (size r - inside r) +
        (off r - 1) * otherOffTotal off r ≤ replacementEdges)
    (hlower : turanNumber p n + ceilQuot n p + (p - 1) ≤ edges)
    (hcorrection : 3 * p < ceilQuot n p + (p - 1)) :
    IsStrongProfile off := by
  apply noPole_extremal_isStrongProfile size off inside hsum hedges hlocalSmall
  · intro r hr
    obtain ⟨replacementEdges, hoptimal, hgain⟩ := hreplacement r hr
    exact otherOffTotal_eq_zero_of_corrected_replacement_of_two_le
      size off inside r hr (hinside r) hoptimal hgain
  · exact hlower
  · exact hcorrection

lemma three_mul_lt_ceilQuot_add_pred_of_large {p n : ℕ}
    (hp : 0 < p) (hn : p * (2 * p + 1) < n) :
    3 * p < ceilQuot n p + (p - 1) := by
  have hn0 : 0 < n := by omega
  rw [ceilQuot_eq_succ_pred_div hn0 hp]
  have hmul : (2 * p + 1) * p ≤ n - 1 := by
    rw [Nat.mul_comm]
    omega
  have hdiv : 2 * p + 1 ≤ (n - 1) / p :=
    (Nat.le_div_iff_mul_le hp).2 hmul
  omega

/-- Geometrically minimal form: a replacement is required only while some
other component remains active.  This is precisely when the cross-part
sign constraint supplies a safe choice of pole. -/
theorem noPole_extremal_isStrongProfile_of_conditional_replacements
    {p n edges : ℕ} (size off inside : Fin p → ℕ)
    (hsum : ∑ i, size i = n)
    (hedges : edges + crossDefect off =
      pairProductSum size size + ∑ i, inside i)
    (hinside : ∀ i, inside i ≤ size i)
    (hlocalSmall : ∀ i, off i ≤ 1 → inside i ≤ 3)
    (hreplacement : ∀ r, 2 ≤ off r → 0 < otherOffTotal off r →
      ∃ replacementEdges,
        replacementEdges ≤ edges ∧
        edges + (size r - inside r) +
          (off r - 1) * otherOffTotal off r ≤ replacementEdges)
    (hlower : turanNumber p n + ceilQuot n p + (p - 1) ≤ edges)
    (hcorrection : 3 * p < ceilQuot n p + (p - 1)) :
    IsStrongProfile off := by
  apply noPole_extremal_isStrongProfile size off inside hsum hedges hlocalSmall
  · intro r hr
    by_contra hother
    have hotherPos : 0 < otherOffTotal off r := Nat.pos_of_ne_zero hother
    obtain ⟨replacementEdges, hoptimal, hgain⟩ :=
      hreplacement r hr hotherPos
    exact hother (otherOffTotal_eq_zero_of_corrected_replacement_of_two_le
      size off inside r hr (hinside r) hoptimal hgain)
  · exact hlower
  · exact hcorrection

theorem noPole_extremal_isStrongProfile_of_conditional_replacements_of_large
    {p n edges : ℕ} (size off inside : Fin p → ℕ)
    (hp : 0 < p) (hn : p * (2 * p + 1) < n)
    (hsum : ∑ i, size i = n)
    (hedges : edges + crossDefect off =
      pairProductSum size size + ∑ i, inside i)
    (hinside : ∀ i, inside i ≤ size i)
    (hlocalSmall : ∀ i, off i ≤ 1 → inside i ≤ 3)
    (hreplacement : ∀ r, 2 ≤ off r → 0 < otherOffTotal off r →
      ∃ replacementEdges,
        replacementEdges ≤ edges ∧
        edges + (size r - inside r) +
          (off r - 1) * otherOffTotal off r ≤ replacementEdges)
    (hlower : turanNumber p n + ceilQuot n p + (p - 1) ≤ edges) :
    IsStrongProfile off :=
  noPole_extremal_isStrongProfile_of_conditional_replacements
    size off inside hsum hedges hinside hlocalSmall hreplacement hlower
      (three_mul_lt_ceilQuot_add_pred_of_large hp hn)

namespace AssignmentIntegration

/-- Stable-partition/extremality wrapper for the repaired no-pole
classifier.  The geometric replacement witness is a genuine point
configuration; global extremality supplies its non-improvement inequality. -/
theorem Assignment.isStrongCarrierSet_of_extremal_noPole_replacements
    {d p : ℕ} {A : Finset (Point d)}
    (Q : Assignment (p := p) A) (hp : 0 < p)
    {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (hagrees : AgreesOnRetained Q P)
    (hlarge : ∀ _i : Fin p,
      (3 : ℝ) + epsilon * A.card < (A.card : ℝ) / p)
    (inside : Fin p → ℕ)
    (hedges : diameterPairCount A + crossDefect Q.offCount =
      pairProductSum (partCard Q) (partCard Q) + ∑ i, inside i)
    (hinside : ∀ i, inside i ≤ partCard Q i)
    (hlocalSmall : ∀ i, Q.offCount i ≤ 1 → inside i ≤ 3)
    (hAextremal : diameterPairCount A = f d A.card)
    (hreplacementGeometry : ∀ r, 2 ≤ Q.offCount r → 3 ≤ partCard Q r →
      ∃ A' : Finset (Point d),
        A'.card = A.card ∧ IsDiameterOne A' ∧
        diameterPairCount A + (partCard Q r - inside r) +
          (Q.offCount r - 1) * otherOffTotal Q.offCount r ≤
            diameterPairCount A')
    (hlower : turanNumber p A.card + ceilQuot A.card p + (p - 1) ≤
      diameterPairCount A)
    (hcorrection : 3 * p < ceilQuot A.card p + (p - 1)) :
    IsStrongCarrierSet (p := p) A := by
  apply Q.isStrongCarrierSet hp
  apply noPole_extremal_isStrongProfile_of_replacements
    (partCard Q) Q.offCount inside
  · exact sum_partCard Q
  · exact hedges
  · exact hinside
  · exact hlocalSmall
  · intro r hr
    have hrsize : 3 ≤ partCard Q r :=
      partCard_ge_three_of_stablePartition Q P hagrees hlarge r
    obtain ⟨A', hcard, hdiam, hgain⟩ :=
      hreplacementGeometry r hr hrsize
    refine ⟨diameterPairCount A', ?_, hgain⟩
    calc
      diameterPairCount A' ≤ f d A.card :=
        diameterPairCount_le_f hcard hdiam
      _ = diameterPairCount A := hAextremal.symm
  · exact hlower
  · exact hcorrection

theorem Assignment.isStrongCarrierSet_of_extremal_noPole_replacements_of_large
    {d p : ℕ} {A : Finset (Point d)}
    (Q : Assignment (p := p) A) (hp : 0 < p)
    {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (hagrees : AgreesOnRetained Q P)
    (hlarge : ∀ _i : Fin p,
      (3 : ℝ) + epsilon * A.card < (A.card : ℝ) / p)
    (inside : Fin p → ℕ)
    (hedges : diameterPairCount A + crossDefect Q.offCount =
      pairProductSum (partCard Q) (partCard Q) + ∑ i, inside i)
    (hinside : ∀ i, inside i ≤ partCard Q i)
    (hlocalSmall : ∀ i, Q.offCount i ≤ 1 → inside i ≤ 3)
    (hAextremal : diameterPairCount A = f d A.card)
    (hreplacementGeometry : ∀ r, 2 ≤ Q.offCount r → 3 ≤ partCard Q r →
      ∃ A' : Finset (Point d),
        A'.card = A.card ∧ IsDiameterOne A' ∧
        diameterPairCount A + (partCard Q r - inside r) +
          (Q.offCount r - 1) * otherOffTotal Q.offCount r ≤
            diameterPairCount A')
    (hlower : turanNumber p A.card + ceilQuot A.card p + (p - 1) ≤
      diameterPairCount A)
    (hn : p * (2 * p + 1) < A.card) :
    IsStrongCarrierSet (p := p) A := by
  apply Assignment.isStrongCarrierSet_of_extremal_noPole_replacements
    Q hp P hagrees hlarge inside hedges hinside hlocalSmall hAextremal
      hreplacementGeometry hlower
  exact three_mul_lt_ceilQuot_add_pred_of_large hp hn

end AssignmentIntegration

end

end CarrierOdd
end Erdos223

#print axioms Erdos223.CarrierOdd.noPole_extremal_isStrongProfile_of_conditional_replacements_of_large
#print axioms Erdos223.CarrierOdd.stablePartition_completeEquipartiteGraph_three_isContained_of_real_bound
