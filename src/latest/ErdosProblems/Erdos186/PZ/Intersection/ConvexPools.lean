/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.Alternating
import ErdosProblems.Erdos186.PZ.Intersection.CoefficientAlternating
import ErdosProblems.Erdos186.PZ.Intersection.CenteredZonotope
import ErdosProblems.Erdos186.PZ.Intersection.Irreducibility
import ErdosProblems.Erdos186.PZ.Basic

/-!
# Lattice pools obtained from a capped convex combination

This file carries out the finite reindexing step at the start of the
Pham--Zakharov intersection argument.  A capped centered combination is
initially indexed by the subtype of the real image of a finite lattice set.
We recover the distinguished lattice point, pull the coefficients back to
the lattice, and split the remaining lattice points into two balanced,
disjoint pools.  The weighted centers of the two oriented deviation pools
are then equal.

No subset-sum or lattice-intersection conclusion is assumed here.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- The canonical real Euclidean embedding of the integer lattice. -/
def latticeEuclidean {d : ℕ} (x : LatticePoint d) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i ↦ (x i : ℝ)

theorem latticeEuclidean_injective {d : ℕ} :
    Function.Injective (latticeEuclidean (d := d)) := by
  intro x y hxy
  funext i
  have hcoord := congrFun (congrArg WithLp.ofLp hxy) i
  have hcast : (x i : ℝ) = (y i : ℝ) := by
    simpa [latticeEuclidean] using hcoord
  exact_mod_cast hcast

/-- A finite lattice set viewed in real Euclidean space. -/
def realImage {d : ℕ} (A : Finset (LatticePoint d)) :
    Finset (EuclideanSpace ℝ (Fin d)) :=
  A.image latticeEuclidean

theorem mem_realImage_of_mem {d : ℕ} {A : Finset (LatticePoint d)}
    {x : LatticePoint d} (hx : x ∈ A) :
    latticeEuclidean x ∈ realImage A := by
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

@[simp] theorem card_realImage {d : ℕ} (A : Finset (LatticePoint d)) :
    (realImage A).card = A.card := by
  classical
  exact Finset.card_image_of_injective _ latticeEuclidean_injective

/-- Pull a function on the real-image subtype back to the ambient lattice.
Outside `A` the value is set to zero. -/
def pullCoefficient {d : ℕ} (A : Finset (LatticePoint d))
    (c : realImage A → ℝ) (x : LatticePoint d) : ℝ :=
  if hx : latticeEuclidean x ∈ realImage A then
    c ⟨latticeEuclidean x, hx⟩
  else 0

@[simp] theorem pullCoefficient_of_mem {d : ℕ}
    {A : Finset (LatticePoint d)} (c : realImage A → ℝ)
    {x : LatticePoint d} (hx : x ∈ A) :
    pullCoefficient A c x =
      c ⟨latticeEuclidean x, mem_realImage_of_mem hx⟩ := by
  rw [pullCoefficient, dif_pos (mem_realImage_of_mem hx)]

/-- The distinguished real-image point has a unique lattice preimage in
`A`.  Existence is all that the pool construction needs. -/
theorem exists_lattice_preimage {d : ℕ} {A : Finset (LatticePoint d)}
    (a₀ : realImage A) :
    ∃ a ∈ A, latticeEuclidean a =
      (a₀ : EuclideanSpace ℝ (Fin d)) := by
  exact Finset.mem_image.mp a₀.property

/-- The lattice points of `A` and the points of its real image are
canonically equivalent. -/
def latticeRealImageEquiv {d : ℕ} (A : Finset (LatticePoint d)) :
    A ≃ realImage A :=
  Equiv.ofBijective
    (fun x : A ↦
      (⟨latticeEuclidean x.1, mem_realImage_of_mem x.2⟩ : realImage A))
    ⟨by
      intro x y hxy
      apply Subtype.ext
      apply latticeEuclidean_injective
      exact congrArg Subtype.val hxy,
    by
      intro y
      obtain ⟨x, hxA, hxy⟩ := Finset.mem_image.mp y.2
      refine ⟨⟨x, hxA⟩, Subtype.ext ?_⟩
      exact hxy⟩

@[simp] theorem latticeRealImageEquiv_apply {d : ℕ}
    (A : Finset (LatticePoint d)) (x : A) :
    ((latticeRealImageEquiv A x : realImage A) :
      EuclideanSpace ℝ (Fin d)) = latticeEuclidean x.1 :=
  rfl

@[simp] theorem pullCoefficient_subtype {d : ℕ}
    (A : Finset (LatticePoint d)) (c : realImage A → ℝ) (x : A) :
    pullCoefficient A c x.1 = c (latticeRealImageEquiv A x) := by
  rw [pullCoefficient_of_mem c x.2]
  congr 1

/-- Reindex a centered sum from the lattice set to its real-image subtype. -/
theorem sum_pullCoefficient_centered {d : ℕ}
    (A : Finset (LatticePoint d)) (c : realImage A → ℝ)
    (a : LatticePoint d) :
    (∑ x ∈ A, pullCoefficient A c x •
        (latticeEuclidean x - latticeEuclidean a)) =
      ∑ y : realImage A, c y •
        ((y : EuclideanSpace ℝ (Fin d)) - latticeEuclidean a) := by
  rw [← Finset.sum_attach]
  simp_rw [pullCoefficient_subtype]
  exact (latticeRealImageEquiv A).sum_comp
    (fun y : realImage A ↦ c y •
      ((y : EuclideanSpace ℝ (Fin d)) - latticeEuclidean a))

/-- Reindex the total coefficient mass from the real-image subtype to the
original lattice set. -/
theorem sum_pullCoefficient {d : ℕ}
    (A : Finset (LatticePoint d)) (c : realImage A → ℝ) :
    (∑ x ∈ A, pullCoefficient A c x) = ∑ y : realImage A, c y := by
  rw [← Finset.sum_attach]
  simp_rw [pullCoefficient_subtype]
  exact (latticeRealImageEquiv A).sum_comp c

/-- Concrete output of the capped-combination partition step. -/
structure ConvexPoolsData {d : ℕ} (A : Finset (LatticePoint d))
    (a₀ : realImage A) (c : realImage A → ℝ) (mu : ℝ) where
  a : LatticePoint d
  a_mem : a ∈ A
  a_image : latticeEuclidean a =
    (a₀ : EuclideanSpace ℝ (Fin d))
  A₁ : Finset (LatticePoint d)
  A₂ : Finset (LatticePoint d)
  union_eq : A₁ ∪ A₂ = A.erase a
  disjoint : Disjoint A₁ A₂
  card_A₁ : A₁.card = (A.card - 1) / 2
  card_A₂ : A₂.card = (A.card - 1) - (A.card - 1) / 2
  card_lower_A₁ : (A.card - 2) / 2 ≤ A₁.card
  card_lower_A₂ : (A.card - 2) / 2 ≤ A₂.card
  coefficient_bounds : ∀ x ∈ A,
    0 ≤ pullCoefficient A c x ∧
      pullCoefficient A c x ≤ (mu * A.card)⁻¹
  /-- The source coefficient-ordered alternating split makes the two side
  masses differ by at most one coefficient cap. -/
  coefficient_mass_difference :
    |(∑ x ∈ A₁, pullCoefficient A c x) -
        ∑ x ∈ A₂, pullCoefficient A c x| ≤
      (mu * A.card)⁻¹
  coefficient_sum : (∑ x ∈ A, pullCoefficient A c x) = 1
  centered_balance :
    (∑ x ∈ A₁, pullCoefficient A c x •
        (latticeEuclidean x - latticeEuclidean a)) =
      ∑ x ∈ A₂, pullCoefficient A c x •
        (latticeEuclidean a - latticeEuclidean x)

namespace ConvexPoolsData

variable {d : ℕ} {A : Finset (LatticePoint d)}
    {a₀ : realImage A} {c : realImage A → ℝ} {mu : ℝ}

theorem A₁_subset_erase (D : ConvexPoolsData A a₀ c mu) :
    D.A₁ ⊆ A.erase D.a := by
  rw [← D.union_eq]
  exact Finset.subset_union_left

theorem A₂_subset_erase (D : ConvexPoolsData A a₀ c mu) :
    D.A₂ ⊆ A.erase D.a := by
  rw [← D.union_eq]
  exact Finset.subset_union_right

/-- Coordinate form of the equality of the two weighted deviation centers.
This is the form consumed by the centered-zonotope estimates. -/
theorem centered_balance_coordinate (D : ConvexPoolsData A a₀ c mu)
    (i : Fin d) :
    (∑ x ∈ D.A₁, pullCoefficient A c x *
        (((x - D.a) i : ℤ) : ℝ)) =
      ∑ x ∈ D.A₂, pullCoefficient A c x *
        (((D.a - x) i : ℤ) : ℝ) := by
  have h := congrFun (congrArg WithLp.ofLp D.centered_balance) i
  simpa [latticeEuclidean, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    using h

theorem coefficient_bounds_A₁ (D : ConvexPoolsData A a₀ c mu)
    {x : LatticePoint d} (hx : x ∈ D.A₁) :
    0 ≤ pullCoefficient A c x ∧
      pullCoefficient A c x ≤ (mu * A.card)⁻¹ :=
  D.coefficient_bounds x (Finset.mem_of_mem_erase (D.A₁_subset_erase hx))

theorem coefficient_bounds_A₂ (D : ConvexPoolsData A a₀ c mu)
    {x : LatticePoint d} (hx : x ∈ D.A₂) :
    0 ≤ pullCoefficient A c x ∧
      pullCoefficient A c x ≤ (mu * A.card)⁻¹ :=
  D.coefficient_bounds x (Finset.mem_of_mem_erase (D.A₂_subset_erase hx))

/-- Total coefficient mass remaining after removing the distinguished point. -/
theorem coefficient_mass_sum_sides (D : ConvexPoolsData A a₀ c mu) :
    (∑ x ∈ D.A₁, pullCoefficient A c x) +
        ∑ x ∈ D.A₂, pullCoefficient A c x =
      1 - pullCoefficient A c D.a := by
  rw [← Finset.sum_union D.disjoint, D.union_eq]
  have herase := Finset.sum_erase_add A (pullCoefficient A c) D.a_mem
  linarith [D.coefficient_sum]

/-- Each side retains half the mass outside `a`, up to one coefficient cap. -/
theorem coefficient_mass_lower_A₁ (D : ConvexPoolsData A a₀ c mu) :
    (1 - pullCoefficient A c D.a - (mu * A.card)⁻¹) / 2 ≤
      ∑ x ∈ D.A₁, pullCoefficient A c x := by
  have hdiff := (abs_le.mp D.coefficient_mass_difference).1
  have hsum := D.coefficient_mass_sum_sides
  linarith

/-- Symmetric mass lower bound for the reverse side. -/
theorem coefficient_mass_lower_A₂ (D : ConvexPoolsData A a₀ c mu) :
    (1 - pullCoefficient A c D.a - (mu * A.card)⁻¹) / 2 ≤
      ∑ x ∈ D.A₂, pullCoefficient A c x := by
  have hdiff := (abs_le.mp D.coefficient_mass_difference).2
  have hsum := D.coefficient_mass_sum_sides
  linarith

/-- Coefficients on the forward deviation set `A₁-a`. -/
def forwardCoefficient (D : ConvexPoolsData A a₀ c mu)
    (v : LatticePoint d) : ℝ :=
  pullCoefficient A c (v + D.a)

/-- Coefficients on the reverse deviation set `a-A₂`. -/
def reverseCoefficient (D : ConvexPoolsData A a₀ c mu)
    (v : LatticePoint d) : ℝ :=
  pullCoefficient A c (D.a - v)

@[simp] theorem forwardCoefficient_deviation
    (D : ConvexPoolsData A a₀ c mu) (x : LatticePoint d) :
    D.forwardCoefficient (x - D.a) = pullCoefficient A c x := by
  simp [forwardCoefficient]

@[simp] theorem reverseCoefficient_deviation
    (D : ConvexPoolsData A a₀ c mu) (x : LatticePoint d) :
    D.reverseCoefficient (D.a - x) = pullCoefficient A c x := by
  simp [reverseCoefficient]

theorem forwardCoefficient_bounds
    (D : ConvexPoolsData A a₀ c mu) {v : LatticePoint d}
    (hv : v ∈ orientedTranslate .forward D.a D.A₁) :
    0 ≤ D.forwardCoefficient v ∧
      D.forwardCoefficient v ≤ (mu * A.card)⁻¹ := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
  simpa [orientedDeviation] using D.coefficient_bounds_A₁ hx

theorem reverseCoefficient_bounds
    (D : ConvexPoolsData A a₀ c mu) {v : LatticePoint d}
    (hv : v ∈ orientedTranslate .reverse D.a D.A₂) :
    0 ≤ D.reverseCoefficient v ∧
      D.reverseCoefficient v ≤ (mu * A.card)⁻¹ := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
  simpa [orientedDeviation] using D.coefficient_bounds_A₂ hx

/-- The two oriented deviation zonotopes have the same weighted center. -/
theorem zonotopeCenter_forward_eq_reverse
    (D : ConvexPoolsData A a₀ c mu) :
    zonotopeCenter (orientedTranslate .forward D.a D.A₁)
        D.forwardCoefficient =
      zonotopeCenter (orientedTranslate .reverse D.a D.A₂)
        D.reverseCoefficient := by
  funext i
  change
    (∑ v ∈ orientedTranslate .forward D.a D.A₁,
        D.forwardCoefficient v * realVector v i) =
      ∑ v ∈ orientedTranslate .reverse D.a D.A₂,
        D.reverseCoefficient v * realVector v i
  calc
    _ = ∑ x ∈ D.A₁, pullCoefficient A c x *
        (((x - D.a) i : ℤ) : ℝ) := by
      rw [show orientedTranslate .forward D.a D.A₁ =
          D.A₁.image (orientedDeviation .forward D.a) by rfl]
      rw [Finset.sum_image
        (orientedDeviation_injective .forward D.a).injOn]
      apply Finset.sum_congr rfl
      intro x hx
      simp [orientedDeviation, realVector]
    _ = ∑ x ∈ D.A₂, pullCoefficient A c x *
        (((D.a - x) i : ℤ) : ℝ) := D.centered_balance_coordinate i
    _ = _ := by
      rw [show orientedTranslate .reverse D.a D.A₂ =
          D.A₂.image (orientedDeviation .reverse D.a) by rfl]
      rw [Finset.sum_image
        (orientedDeviation_injective .reverse D.a).injOn]
      apply Finset.sum_congr rfl
      intro x hx
      simp [orientedDeviation, realVector]

/-- The cap is small enough for the centered-zonotope translation lemma as
soon as the global cap `(mu*|A|)^{-1}` is at most `1/2`. -/
theorem forwardCoefficient_half
    (D : ConvexPoolsData A a₀ c mu)
    (hhalf : (mu * A.card)⁻¹ ≤ (1 : ℝ) / 2)
    {v : LatticePoint d}
    (hv : v ∈ orientedTranslate .forward D.a D.A₁) :
    0 ≤ D.forwardCoefficient v ∧ D.forwardCoefficient v ≤ (1 : ℝ) / 2 := by
  exact ⟨(D.forwardCoefficient_bounds hv).1,
    (D.forwardCoefficient_bounds hv).2.trans hhalf⟩

theorem reverseCoefficient_half
    (D : ConvexPoolsData A a₀ c mu)
    (hhalf : (mu * A.card)⁻¹ ≤ (1 : ℝ) / 2)
    {v : LatticePoint d}
    (hv : v ∈ orientedTranslate .reverse D.a D.A₂) :
    0 ≤ D.reverseCoefficient v ∧ D.reverseCoefficient v ≤ (1 : ℝ) / 2 := by
  exact ⟨(D.reverseCoefficient_bounds hv).1,
    (D.reverseCoefficient_bounds hv).2.trans hhalf⟩

/-- The elementary Lemma 14 inclusion on the forward pool, now with all
coefficient bounds discharged by the capped combination. -/
theorem forward_center_add_centeredZonotope_subset
    (D : ConvexPoolsData A a₀ c mu)
    (hhalf : (mu * A.card)⁻¹ ≤ (1 : ℝ) / 2) :
    (fun z ↦
      zonotopeCenter (orientedTranslate .forward D.a D.A₁)
          D.forwardCoefficient + z) ''
        centeredZonotope (orientedTranslate .forward D.a D.A₁)
          D.forwardCoefficient ⊆
      zonotope (orientedTranslate .forward D.a D.A₁) := by
  exact lemma14_center_add_centeredZonotope_subset _ _
    (fun _ hv ↦ D.forwardCoefficient_half hhalf hv)

/-- The corresponding elementary Lemma 14 inclusion on the reverse pool. -/
theorem reverse_center_add_centeredZonotope_subset
    (D : ConvexPoolsData A a₀ c mu)
    (hhalf : (mu * A.card)⁻¹ ≤ (1 : ℝ) / 2) :
    (fun z ↦
      zonotopeCenter (orientedTranslate .reverse D.a D.A₂)
          D.reverseCoefficient + z) ''
        centeredZonotope (orientedTranslate .reverse D.a D.A₂)
          D.reverseCoefficient ⊆
      zonotope (orientedTranslate .reverse D.a D.A₂) := by
  exact lemma14_center_add_centeredZonotope_subset _ _
    (fun _ hv ↦ D.reverseCoefficient_half hhalf hv)

end ConvexPoolsData

/-- A capped centered combination on the real image yields the two balanced
lattice pools used by the two orientations of the intersection argument. -/
theorem exists_convexPoolsData {d : ℕ}
    (A : Finset (LatticePoint d)) (a₀ : realImage A)
    (c : realImage A → ℝ) (mu : ℝ)
    (hc : ∀ x, 0 ≤ c x ∧ c x ≤ (mu * A.card)⁻¹)
    (hsum : (∑ x, c x) = 1)
    (hcenter : (∑ x, c x •
      ((x : EuclideanSpace ℝ (Fin d)) - a₀)) = 0) :
    Nonempty (ConvexPoolsData A a₀ c mu) := by
  obtain ⟨a, ha, ha_image⟩ := exists_lattice_preimage a₀
  have hbounds : ∀ x ∈ A,
      0 ≤ pullCoefficient A c x ∧
        pullCoefficient A c x ≤ (mu * A.card)⁻¹ := by
    intro x hx
    rw [pullCoefficient_of_mem c hx]
    exact hc _
  obtain ⟨A₂, A₁, hunion', hdisjoint', hcard₂', hcard₁', hmass'⟩ :=
    exists_coefficientBalanced_partition_erase A a ha
      (pullCoefficient A c) (mu * A.card)⁻¹
      (fun x hx ↦ (hbounds x hx).1) (fun x hx ↦ (hbounds x hx).2)
  have hunion : A₁ ∪ A₂ = A.erase a := by
    simpa only [Finset.union_comm] using hunion'
  have hdisjoint : Disjoint A₁ A₂ := hdisjoint'.symm
  have hcardErase : (A.erase a).card = A.card - 1 :=
    Finset.card_erase_of_mem ha
  have hcard₁ : A₁.card = (A.card - 1) / 2 := by
    rw [hcard₁', hcardErase]
  have hcard₂ : A₂.card = (A.card - 1) - (A.card - 1) / 2 := by
    rw [hcard₂', hcardErase]
    omega
  have hlower₁ : (A.card - 2) / 2 ≤ A₁.card := by
    rw [hcard₁]
    omega
  have hlower₂ : (A.card - 2) / 2 ≤ A₂.card := by
    rw [hcard₂]
    omega
  have hmass :
      |(∑ x ∈ A₁, pullCoefficient A c x) -
          ∑ x ∈ A₂, pullCoefficient A c x| ≤
        (mu * A.card)⁻¹ := by
    simpa only [abs_sub_comm] using hmass'
  have hcenter' :
      (∑ x ∈ A, pullCoefficient A c x •
        (latticeEuclidean x - latticeEuclidean a)) = 0 := by
    rw [sum_pullCoefficient_centered]
    simpa only [ha_image] using hcenter
  have hsum' : (∑ x ∈ A, pullCoefficient A c x) = 1 := by
    rw [sum_pullCoefficient]
    exact hsum
  refine ⟨{
    a := a
    a_mem := ha
    a_image := ha_image
    A₁ := A₁
    A₂ := A₂
    union_eq := hunion
    disjoint := hdisjoint
    card_A₁ := hcard₁
    card_A₂ := hcard₂
    card_lower_A₁ := hlower₁
    card_lower_A₂ := hlower₂
    coefficient_bounds := hbounds
    coefficient_mass_difference := hmass
    coefficient_sum := hsum'
    centered_balance := ?_ }⟩
  exact centered_balance_of_partition ha hunion hdisjoint
    (pullCoefficient A c) latticeEuclidean hcenter'

end

end Erdos186.PZ.Intersection
