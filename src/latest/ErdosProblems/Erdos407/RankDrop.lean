/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos407.AdelicMinkowski
import ErdosProblems.Erdos407.ApproximationDomain
import ErdosProblems.Erdos407.DeterminantGap
import ErdosProblems.Erdos407.HeightBoxes
import ErdosProblems.Erdos407.GLRAuxiliary
import ErdosProblems.Erdos407.IntegralCoordinateChange
import ErdosProblems.Erdos407.RealDeterminantGap
import ErdosProblems.Erdos407.RestrictionIndex
import ErdosProblems.Erdos407.RothIndex
import ErdosProblems.Erdos407.SmallIntegerNonvanishing
import ErdosProblems.Erdos407.SubspaceHeights
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Rank drop for the rational three-place approximation domains

This file packages the linear-algebraic rank-drop mechanism used in the
specialization of the Subspace Theorem to `K = ℚ` and
`S = {∞, 2, 3}`.  The important point is that the rank-drop assertion below
is a theorem, not a hypothesis: it follows from the three-place determinant
gap in `DeterminantGap.lean`.

There are four layers.

* `integralApproximationDomain` is the set of integral points satisfying one
  fixed array of local bounds, and `approximationSpan` is its rational span.
* A small product of the `3n` radii forces that span to have rank `< n`.
* The orthogonal complement of the span supplies a nonzero rational
  hyperplane normal.  Its determinant height is exactly the height of the
  span.  The cofactor formulation records the determinant identity used in
  Goel--Lunia--Ray, Lemma 4.22.
* A strictly descending chain of rational spans has length at most the
  ambient dimension, hence at most five in the application.

All statements are specialized to rational vectors and the three selected
places.  No compactness, limit, rank-drop, or Subspace-Theorem assumption is
introduced here.
-/

namespace Erdos407.RankDrop

open scoped BigOperators Matrix

attribute [local instance] Matrix.seminormedAddCommGroup

abbrev RatVector (n : ℕ) := Fin n → ℚ
abbrev IntVector (n : ℕ) := Fin n → ℤ
abbrev LocalRadii (n : ℕ) := PadicSubspace.Place23 → Fin n → ℚ
abbrev LocalForms (n : ℕ) :=
  PadicSubspace.Place23 → Fin n → PadicSubspace.RatLinearForm n

/-- Coefficient vector of the `i`-th form in the basis dual to the local
form basis.  If `A` is the matrix whose rows are the coefficients of the
forms `L_i`, this is column `i` of `A⁻¹`, hence row `i` of `(Aᵀ)⁻¹`.

This is the vector denoted `\hat L_{v,i}` in GLR Lemma 4.22.  It acts on a
hyperplane normal, rather than on a point of the approximation box. -/
noncomputable def dualCoefficientVector {n : ℕ} (L : LocalForms n)
    (v : PadicSubspace.Place23) (i : Fin n) : RatVector n :=
  fun j ↦ (PadicSubspace.formMatrix L v)⁻¹ j i

/-- Expansion of a vector in the transpose of the local form basis.  This
identity fixes the direction of the duality used below. -/
theorem dual_reconstruction {n : ℕ} (L : LocalForms n)
    (hL : PadicSubspace.IsNonsingularFamily L)
    (v : PadicSubspace.Place23) (b : RatVector n) :
    (∑ i, (dualCoefficientVector L v i ⬝ᵥ b) •
      PadicSubspace.coefficientVector (L v i)) = b := by
  classical
  let A := PadicSubspace.formMatrix L v
  have hdet : A.det ≠ 0 := PadicSubspace.formMatrix_det_ne_zero hL v
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hunit
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, dotProduct,
    dualCoefficientVector, PadicSubspace.coefficientVector]
  change (∑ i, (∑ k, A⁻¹ k i * b k) * A i j) = b j
  calc
    (∑ i, (∑ k, A⁻¹ k i * b k) * A i j) =
        Matrix.vecMul (Matrix.vecMul b A⁻¹) A j := by
          simp only [Matrix.vecMul, dotProduct]
          apply Finset.sum_congr rfl
          intro i _
          congr 1
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = Matrix.vecMul b (A⁻¹ * A) j := by
      rw [Matrix.vecMul_vecMul]
    _ = b j := by rw [hinv]; simp

/-- A dual coefficient row becomes the corresponding standard coordinate
row after the local change of coordinates. -/
theorem dualCoefficientVector_vecMul_transpose {n : ℕ} (L : LocalForms n)
    (hL : PadicSubspace.IsNonsingularFamily L)
    (v : PadicSubspace.Place23) (i : Fin n) :
    Matrix.vecMul (dualCoefficientVector L v i)
      (PadicSubspace.formMatrix L v)ᵀ =
        (Pi.single i (1 : ℚ) : RatVector n) := by
  classical
  let A := PadicSubspace.formMatrix L v
  have hdet : A.det ≠ 0 := PadicSubspace.formMatrix_det_ne_zero hL v
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hmul : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hunit
  funext k
  change (∑ j, A⁻¹ j i * A k j) =
    (Pi.single i (1 : ℚ) : RatVector n) k
  calc
    (∑ j, A⁻¹ j i * A k j) = (A * A⁻¹) k i := by
      simp only [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (1 : Matrix (Fin n) (Fin n) ℚ) k i := by rw [hmul]
    _ = (Pi.single i (1 : ℚ) : RatVector n) k := by
      rw [Matrix.one_apply]
      simp [Pi.single_apply, eq_comm]

/-! ## Approximation-domain span and rank -/

/-- Integral points satisfying one fixed set of bounds at `∞`, `2`, and `3`. -/
def integralApproximationDomain {n : ℕ} (L : LocalForms n)
    (c : LocalRadii n) : Set (IntVector n) :=
  {x | ∀ v i, PadicSubspace.placeNorm v
    (L v i (PadicSubspace.intCastVec x)) ≤ c v i}

@[simp] theorem mem_integralApproximationDomain {n : ℕ}
    {L : LocalForms n} {c : LocalRadii n} {x : IntVector n} :
    x ∈ integralApproximationDomain L c ↔
      ∀ v i, PadicSubspace.placeNorm v
        (L v i (PadicSubspace.intCastVec x)) ≤ c v i :=
  Iff.rfl

/-- The rational points obtained from an integral approximation domain. -/
def rationalApproximationDomain {n : ℕ} (L : LocalForms n)
    (c : LocalRadii n) : Set (RatVector n) :=
  PadicSubspace.intCastVec '' integralApproximationDomain L c

/-- The rational span denoted `V(Q)` in the Subspace-Theorem argument. -/
def approximationSpan {n : ℕ} (L : LocalForms n) (c : LocalRadii n) :
    Submodule ℚ (RatVector n) :=
  Submodule.span ℚ (rationalApproximationDomain L c)

/-- Rank of the approximation domain, i.e. the dimension of its rational span. -/
noncomputable def approximationRank {n : ℕ} (L : LocalForms n)
    (c : LocalRadii n) : ℕ :=
  Module.finrank ℚ (approximationSpan L c)

theorem mem_approximationSpan {n : ℕ} {L : LocalForms n}
    {c : LocalRadii n} {x : IntVector n}
    (hx : x ∈ integralApproximationDomain L c) :
    PadicSubspace.intCastVec x ∈ approximationSpan L c :=
  Submodule.subset_span ⟨x, hx, rfl⟩

/-- No approximation domain has rank larger than its ambient dimension. -/
theorem approximationRank_le_dimension {n : ℕ} (L : LocalForms n)
    (c : LocalRadii n) : approximationRank L c ≤ n := by
  simpa [approximationRank] using Submodule.finrank_le (approximationSpan L c)

/-- The order-theoretic successive-minimum predicate is exactly a lower bound
for the dimension of the rational span. -/
theorem hasRankAtLeast_iff_le_finrank {n r : ℕ} (D : Set (RatVector n)) :
    AdelicMinkowski.HasRankAtLeast D r ↔
      r ≤ PadicSubspace.rationalSetRank D := by
  constructor
  · rintro ⟨f, hf, hfD⟩
    exact PadicSubspace.card_le_rationalSetRank_of_linearIndependent hf hfD
  · intro hr
    obtain ⟨f, hf, hfD⟩ :=
      PadicSubspace.exists_independent_family_card_rationalSetRank D
    let e : Fin r → Fin (PadicSubspace.rationalSetRank D) := Fin.castLE hr
    refine ⟨f ∘ e, hf.comp e (Fin.castLE_injective hr), ?_⟩
    intro i
    exact hfD (e i)

/-- Full rank is equivalent to the existence of an independent ambient-size
family in the set. -/
theorem hasFullRank_iff {n : ℕ} (D : Set (RatVector n)) :
    AdelicMinkowski.HasRankAtLeast D n ↔
      PadicSubspace.rationalSetRank D = n := by
  rw [hasRankAtLeast_iff_le_finrank]
  exact ⟨fun h ↦ Nat.le_antisymm
      (PadicSubspace.rationalSetRank_le_dimension D) h,
    fun h ↦ h.ge⟩

/-! ## The concrete three-place determinant rank drop -/

/-- The determinant gap forces a genuine rank drop in the whole integral
approximation domain.  This is the rational three-place form of the first
successive-minimum rank drop: an independent `n`-tuple would have nonzero
integral determinant, whose `{∞,2,3}` norm product is at least one, while the
local row bounds make the same determinant strictly smaller. -/
theorem approximationRank_lt_of_radiiProduct {n : ℕ}
    (L : LocalForms n) (c : LocalRadii n)
    (hc : ∀ v i, 0 ≤ c v i)
    (hsmall : (Nat.factorial n : ℚ) ^ 3 *
        PadicSubspace.localRadiiProduct c <
      PadicSubspace.formDetProduct L) :
    approximationRank L c < n := by
  apply lt_of_not_ge
  intro hfull
  have hrank : approximationRank L c = n :=
    Nat.le_antisymm (approximationRank_le_dimension L c) hfull
  have hsetrank :
      PadicSubspace.rationalSetRank
        (rationalApproximationDomain L c) = n := by
    change Module.finrank ℚ
      (Submodule.span ℚ (rationalApproximationDomain L c)) = n
    change Module.finrank ℚ
      (Submodule.span ℚ (rationalApproximationDomain L c)) = n at hrank
    exact hrank
  obtain ⟨f₀, hfi₀, hfD₀⟩ :=
    PadicSubspace.exists_independent_family_card_rationalSetRank
      (rationalApproximationDomain L c)
  let e : Fin n → Fin
      (PadicSubspace.rationalSetRank (rationalApproximationDomain L c)) :=
    Fin.cast hsetrank.symm
  let f : Fin n → RatVector n := f₀ ∘ e
  have hfi : LinearIndependent ℚ f := hfi₀.comp e (Fin.cast_injective _)
  have hfD : ∀ i, f i ∈ rationalApproximationDomain L c := fun i ↦ hfD₀ (e i)
  choose x hx hfx using hfD
  have hxmem : ∀ j v i,
      PadicSubspace.placeNorm v
        (L v i (PadicSubspace.intCastVec (x j))) ≤ c v i := by
    intro j
    exact hx j
  have hcast : (fun j ↦ PadicSubspace.intCastVec (x j)) = f := by
    funext j
    exact hfx j
  have hnot := PadicSubspace.not_linearIndependent_of_local_bounds
    L x c hc hxmem hsmall
  exact hnot (hcast.symm ▸ hfi)

/-- The dimension-`≤ 5` wrapper used after dehomogenizing an equation with at
most six terms. -/
theorem approximationRank_lt_dim_le_five {n : ℕ} (_hn : n ≤ 5)
    (L : LocalForms n) (c : LocalRadii n)
    (hc : ∀ v i, 0 ≤ c v i)
    (hsmall : (Nat.factorial n : ℚ) ^ 3 *
        PadicSubspace.localRadiiProduct c <
      PadicSubspace.formDetProduct L) :
    approximationRank L c < n :=
  approximationRank_lt_of_radiiProduct L c hc hsmall

/-! ## Orthogonal kernels, height, and hyperplane extraction -/

/-- The annihilator of the approximation span. -/
def approximationKernel {n : ℕ} (L : LocalForms n) (c : LocalRadii n) :
    Submodule ℚ (RatVector n) :=
  SubspaceHeights.orthogonal (approximationSpan L c)

/-- Orthogonal duality preserves the determinant height of the approximation
span. -/
theorem approximationKernel_height {n : ℕ} (L : LocalForms n)
    (c : LocalRadii n) :
    SubspaceHeights.subspaceHeight (approximationKernel L c) =
      SubspaceHeights.subspaceHeight (approximationSpan L c) :=
  SubspaceHeights.subspaceHeight_orthogonal _

theorem approximationKernel_finrank {n : ℕ} (L : LocalForms n)
    (c : LocalRadii n) :
    Module.finrank ℚ (approximationKernel L c) = n - approximationRank L c := by
  unfold approximationKernel approximationRank
  convert SubspaceHeights.finrank_orthogonal (approximationSpan L c) using 1

/-- A concrete rank drop produces a nonzero normal vector.  The normal lies
in the height-dual orthogonal kernel, and hence annihilates every point of the
original approximation domain. -/
theorem exists_height_dual_hyperplane_of_rank_lt {n : ℕ}
    (L : LocalForms n) (c : LocalRadii n)
    (hrank : approximationRank L c < n) :
    ∃ b : RatVector n,
      b ≠ 0 ∧
      b ∈ approximationKernel L c ∧
      (∀ x ∈ integralApproximationDomain L c,
        (PadicSubspace.intCastVec x) ⬝ᵥ b = 0) ∧
      SubspaceHeights.subspaceHeight (approximationKernel L c) =
        SubspaceHeights.subspaceHeight (approximationSpan L c) := by
  have hkpos : 0 < Module.finrank ℚ (approximationKernel L c) := by
    rw [approximationKernel_finrank]
    omega
  have hkbot : approximationKernel L c ≠ ⊥ := by
    intro hk
    rw [hk, finrank_bot] at hkpos
    omega
  obtain ⟨b, hbmem, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hkbot
  refine ⟨b, hb0, hbmem, ?_, approximationKernel_height L c⟩
  intro x hx
  exact (SubspaceHeights.mem_orthogonal_iff.mp hbmem)
    (PadicSubspace.intCastVec x) (mem_approximationSpan hx)

/-- Fully concrete rank-drop/hyperplane theorem obtained by combining the
three-place determinant gap with height duality. -/
theorem exists_height_dual_hyperplane_of_radiiProduct {n : ℕ}
    (L : LocalForms n) (c : LocalRadii n)
    (hc : ∀ v i, 0 ≤ c v i)
    (hsmall : (Nat.factorial n : ℚ) ^ 3 *
        PadicSubspace.localRadiiProduct c <
      PadicSubspace.formDetProduct L) :
    ∃ b : RatVector n,
      b ≠ 0 ∧
      b ∈ approximationKernel L c ∧
      (∀ x ∈ integralApproximationDomain L c,
        (PadicSubspace.intCastVec x) ⬝ᵥ b = 0) ∧
      SubspaceHeights.subspaceHeight (approximationKernel L c) =
        SubspaceHeights.subspaceHeight (approximationSpan L c) :=
  exists_height_dual_hyperplane_of_rank_lt L c
    (approximationRank_lt_of_radiiProduct L c hc hsmall)

/-! ## Finite collections of concrete small boxes -/

/-- A local box carrying the explicit determinant inequality which makes it
rank-dropping.  This is data, rather than a rank-drop assumption: both fields
are elementary inequalities about its radii. -/
structure SmallBox {n : ℕ} (L : LocalForms n) where
  radii : LocalRadii n
  nonneg : ∀ v i, 0 ≤ radii v i
  determinantGap :
    (Nat.factorial n : ℚ) ^ 3 *
        PadicSubspace.localRadiiProduct radii <
      PadicSubspace.formDetProduct L

namespace SmallBox

def domain {n : ℕ} {L : LocalForms n} (B : SmallBox L) : Set (IntVector n) :=
  integralApproximationDomain L B.radii

theorem rank_lt {n : ℕ} {L : LocalForms n} (B : SmallBox L) :
    approximationRank L B.radii < n :=
  approximationRank_lt_of_radiiProduct L B.radii B.nonneg B.determinantGap

theorem exists_normal {n : ℕ} {L : LocalForms n} (B : SmallBox L) :
    ∃ b : RatVector n, b ≠ 0 ∧
      ∀ x ∈ B.domain, (PadicSubspace.intCastVec x) ⬝ᵥ b = 0 := by
  obtain ⟨b, hb0, _hbker, hvan, _hheight⟩ :=
    exists_height_dual_hyperplane_of_radiiProduct
      L B.radii B.nonneg B.determinantGap
  exact ⟨b, hb0, hvan⟩

end SmallBox

/-- A finite family of boxes satisfying the explicit determinant gaps gives
a finite proper-hyperplane cover. -/
theorem finiteHyperplaneCover_of_smallBoxes {n : ℕ} {L : LocalForms n}
    {X : Set (IntVector n)} (C : Finset (SmallBox L))
    (hcover : ∀ x ∈ X, ∃ B ∈ C, x ∈ B.domain) :
    PadicSubspace.HasFiniteHyperplaneCover X := by
  classical
  choose normal hnormal0 hnormal using fun B : SmallBox L ↦ B.exists_normal
  let normals : Finset (RatVector n) := C.image normal
  refine ⟨normals, ?_, ?_⟩
  · intro b hb
    obtain ⟨B, _hBC, rfl⟩ := Finset.mem_image.mp hb
    exact hnormal0 B
  · intro x hx
    obtain ⟨B, hBC, hxB⟩ := hcover x hx
    refine ⟨normal B, Finset.mem_image.mpr ⟨B, hBC, rfl⟩, ?_⟩
    rw [PadicSubspace.OnHyperplane]
    simpa only [dotProduct, PadicSubspace.intCastVec_apply, mul_comm] using
      hnormal B x hxB

/-! ## Finite support patterns in the GLR height-gap argument -/

/-- At each of the three places, a support pattern records a subset of the
local forms.  There are only finitely many such patterns. -/
abbrev LocalSupportPattern (n : ℕ) :=
  PadicSubspace.Place23 → Finset (Fin n)

/-- The rational span of all *dual* coefficient rows omitted by a support
pattern.  The use of the dual basis is essential here: the small-minor
coordinates in Lemma 4.22 are coordinates of the hyperplane normal in the
dual local basis, not values of the original local forms on that normal. -/
def omittedNormalSpan {n : ℕ} (F : LocalForms n)
    (I : LocalSupportPattern n) : Submodule ℚ (RatVector n) :=
  Submodule.span ℚ
    {b | ∃ v i, i ∉ I v ∧ b = dualCoefficientVector F v i}

/-- The common space of possible hyperplane normals for a support pattern:
it is the intersection of the kernels of all omitted dual local forms. -/
def omittedNormalKernel {n : ℕ} (F : LocalForms n)
    (I : LocalSupportPattern n) : Submodule ℚ (RatVector n) :=
  SubspaceHeights.orthogonal (omittedNormalSpan F I)

theorem mem_omittedNormalKernel_iff {n : ℕ} (F : LocalForms n)
    (I : LocalSupportPattern n) (b : RatVector n) :
    b ∈ omittedNormalKernel F I ↔
      ∀ v i, i ∉ I v →
        dualCoefficientVector F v i ⬝ᵥ b = 0 := by
  constructor
  · intro hb v i hi
    exact (SubspaceHeights.mem_orthogonal_iff.mp hb)
      (dualCoefficientVector F v i)
      (Submodule.subset_span ⟨v, i, hi, rfl⟩)
  · intro hb
    rw [omittedNormalKernel, SubspaceHeights.mem_orthogonal_iff]
    intro y hy
    refine Submodule.span_induction
      (p := fun y _ ↦ y ⬝ᵥ b = 0) ?_ ?_ ?_ ?_ hy
    · rintro x ⟨v, i, hi, rfl⟩
      exact hb v i hi
    · simp
    · intro x y _ _ hx hy
      rw [add_dotProduct, hx, hy, add_zero]
    · intro a x _ hx
      rw [smul_dotProduct, hx, smul_zero]

/-- The fixed exceptional hyperplane belonging to a support pattern.  The
normal supplied by the small-cofactor branch of GLR Lemma 4.22 lies in
`omittedNormalKernel`; when that kernel is a line, its orthogonal complement
is the only possible codimension-one approximation span. -/
def exceptionalSpace {n : ℕ} (F : LocalForms n)
    (I : LocalSupportPattern n) : Submodule ℚ (RatVector n) :=
  SubspaceHeights.orthogonal (omittedNormalKernel F I)

@[simp] theorem exceptionalSpace_eq_omittedNormalSpan {n : ℕ}
    (F : LocalForms n) (I : LocalSupportPattern n) :
    exceptionalSpace F I = omittedNormalSpan F I := by
  simp [exceptionalSpace, omittedNormalKernel]

theorem exceptionalSpace_height {n : ℕ} (F : LocalForms n)
    (I : LocalSupportPattern n) :
    SubspaceHeights.subspaceHeight (exceptionalSpace F I) =
      SubspaceHeights.subspaceHeight (omittedNormalSpan F I) :=
  by simp

/-- The repaired GLR Lemma 4.22 uses a finite exceptional family (and then
passes to one member on an infinite subfamily).  Finiteness is immediate
because the three-place support-pattern type is finite. -/
theorem finite_exceptionalSpaces {n : ℕ} (F : LocalForms n) :
    (Set.range (exceptionalSpace F)).Finite :=
  Set.finite_range _

/-- A `Finset` presentation of the same finite exceptional family, convenient
for the disjunction in the repaired height-gap lemma. -/
noncomputable def exceptionalSpacesFinset {n : ℕ} (F : LocalForms n) :
    Finset (Submodule ℚ (RatVector n)) :=
  Finset.univ.image (exceptionalSpace F)

@[simp] theorem mem_exceptionalSpacesFinset_iff {n : ℕ}
    (F : LocalForms n) (W : Submodule ℚ (RatVector n)) :
    W ∈ exceptionalSpacesFinset F ↔ ∃ I, exceptionalSpace F I = W := by
  classical
  simp [exceptionalSpacesFinset]

theorem mem_orthogonal_span_singleton_iff {n : ℕ} (b x : RatVector n) :
    x ∈ SubspaceHeights.orthogonal (ℚ ∙ b) ↔ b ⬝ᵥ x = 0 := by
  constructor
  · intro hx
    exact (SubspaceHeights.mem_orthogonal_iff.mp hx) b
      (Submodule.mem_span_singleton_self b)
  · intro hbx
    rw [SubspaceHeights.mem_orthogonal_iff]
    intro y hy
    refine Submodule.span_induction
      (p := fun y _ ↦ y ⬝ᵥ x = 0) ?_ ?_ ?_ ?_ hy
    · intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      exact hbx
    · simp
    · intro y z _ _ hy hz
      rw [add_dotProduct, hy, hz, add_zero]
    · intro a y _ hy
      rw [smul_dotProduct, hy, smul_zero]

/-- Linear-algebraic closure of the exceptional branch in the repaired
height-gap lemma.  If the possible-normal space for a pattern is a line,
then any codimension-one space annihilated by a nonzero normal in that line
is the unique exceptional hyperplane attached to the pattern. -/
theorem codimOne_eq_exceptionalSpace_of_patternNormal {n : ℕ}
    (F : LocalForms n) (I : LocalSupportPattern n)
    (W : Submodule ℚ (RatVector n)) (b : RatVector n)
    (hWdim : Module.finrank ℚ W + 1 = n)
    (hb0 : b ≠ 0) (hb : b ∈ omittedNormalKernel F I)
    (hkernelDim : Module.finrank ℚ (omittedNormalKernel F I) = 1)
    (horth : ∀ x ∈ W, x ⬝ᵥ b = 0) :
    W = exceptionalSpace F I := by
  have hspanle : ℚ ∙ b ≤ omittedNormalKernel F I :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr hb
  have hspan : ℚ ∙ b = omittedNormalKernel F I := by
    apply Submodule.eq_of_le_of_finrank_le hspanle
    rw [finrank_span_singleton hb0, hkernelDim]
  have hle : W ≤ SubspaceHeights.orthogonal (ℚ ∙ b) := by
    intro x hx
    rw [mem_orthogonal_span_singleton_iff]
    rw [dotProduct_comm]
    exact horth x hx
  have hWrank : Module.finrank ℚ W = n - 1 := by omega
  have hOrank : Module.finrank ℚ
      (SubspaceHeights.orthogonal (ℚ ∙ b)) = n - 1 := by
    rw [SubspaceHeights.finrank_orthogonal, finrank_span_singleton hb0]
  have hW : W = SubspaceHeights.orthogonal (ℚ ∙ b) := by
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [hWrank, hOrank]
  rw [exceptionalSpace, ← hspan]
  exact hW

/-- Infinite pigeonholing for the finite cofactor-support patterns in the
height-gap proof. -/
theorem exists_infinite_same_supportPattern {n : ℕ} {α : Type*}
    (X : Set α) (hX : X.Infinite) (pattern : α → LocalSupportPattern n) :
    ∃ I, {x | x ∈ X ∧ pattern x = I}.Infinite :=
  HeightBoxes.exists_infinite_fiber X hX pattern

/-! ## The real-exponent domains used in GLR Theorem 4.14 -/

/-- Integral points in the real-radius approximation box of
`HeightBoxes.lean`. -/
def realIntegralApproximationDomain {n : ℕ} (L : LocalForms n)
    (Q : ℕ) (c : HeightBoxes.LocalConstants n) : Set (IntVector n) :=
  {x | HeightBoxes.InApproximationBox L (Q : ℝ) c
    (PadicSubspace.intCastVec x)}

/-- The actual approximation domain used by GLR: rational points integral
away from `2` and `3`.  Exterior-power witnesses naturally live here, not
in the integer-only subdomain above. -/
def realSIntegralApproximationDomain {n : ℕ} (L : LocalForms n)
    (Q : ℕ) (c : HeightBoxes.LocalConstants n) : Set (RatVector n) :=
  {x | AdelicMinkowski.InZOneSix x ∧
    HeightBoxes.InApproximationBox L (Q : ℝ) c x}

/-! The scalar arithmetic of `ℤ[1/6]`.  We keep this presentation tied to
`AdelicMinkowski.denominator`, so finite exterior-power witnesses and their
cofactor determinants use exactly the same denominator lattice. -/

namespace SIntegerSix

def IsSInteger (q : ℚ) : Prop :=
  ∃ k : ℕ, ∃ z : ℤ, q = (z : ℚ) / AdelicMinkowski.denominator k

theorem zero : IsSInteger 0 := ⟨0, 0, by simp⟩

theorem one : IsSInteger 1 := ⟨0, 1, by simp⟩

theorem intCast (z : ℤ) : IsSInteger (z : ℚ) :=
  ⟨0, z, by simp⟩

theorem neg {q : ℚ} (hq : IsSInteger q) : IsSInteger (-q) := by
  obtain ⟨k, z, rfl⟩ := hq
  exact ⟨k, -z, by push_cast; ring⟩

theorem add {q r : ℚ} (hq : IsSInteger q) (hr : IsSInteger r) :
    IsSInteger (q + r) := by
  obtain ⟨k, z, rfl⟩ := hq
  obtain ⟨l, w, rfl⟩ := hr
  refine ⟨k + l,
    z * AdelicMinkowski.denominator l +
      w * AdelicMinkowski.denominator k, ?_⟩
  simp only [AdelicMinkowski.denominator, pow_add]
  push_cast
  field_simp

theorem mul {q r : ℚ} (hq : IsSInteger q) (hr : IsSInteger r) :
    IsSInteger (q * r) := by
  obtain ⟨k, z, rfl⟩ := hq
  obtain ⟨l, w, rfl⟩ := hr
  refine ⟨k + l, z * w, ?_⟩
  simp only [AdelicMinkowski.denominator, pow_add]
  push_cast
  ring

theorem sum {ι : Type*} [Fintype ι] (q : ι → ℚ)
    (hq : ∀ i, IsSInteger (q i)) : IsSInteger (∑ i, q i) := by
  classical
  simpa using Finset.sum_induction (s := Finset.univ) q IsSInteger
    (fun _ _ ↦ add) zero (fun i _ ↦ hq i)

theorem prod {ι : Type*} [Fintype ι] (q : ι → ℚ)
    (hq : ∀ i, IsSInteger (q i)) : IsSInteger (∏ i, q i) := by
  classical
  simpa using Finset.prod_induction (s := Finset.univ) q IsSInteger
    (fun _ _ ↦ mul) one (fun i _ ↦ hq i)

theorem det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ) (hM : ∀ i j, IsSInteger (M i j)) :
    IsSInteger M.det := by
  rw [Matrix.det_apply]
  apply sum
  intro σ
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul]
    exact prod _ (fun i ↦ hM (σ i) i)
  · rw [hs]
    simpa [Units.smul_def] using
      neg (prod _ (fun i ↦ hM (σ i) i))

theorem of_inZOneSix_coordinate {n : ℕ} {x : RatVector n}
    (hx : AdelicMinkowski.InZOneSix x) (i : Fin n) :
    IsSInteger (x i) := by
  obtain ⟨k, z, hz⟩ := hx
  exact ⟨k, z i, hz i⟩

/-- A common rational scale of a primitive integral vector is in
`ℤ[1/6]` as soon as all scaled coordinates are. -/
theorem scale_isSInteger_of_primitive {ι : Type*} [Fintype ι]
    {z : ι → ℤ} (hz : Primitive.IsPrimitive z) {q : ℚ}
    (hcoord : ∀ i, IsSInteger (q * (z i : ℚ))) : IsSInteger q := by
  obtain ⟨u, hu⟩ := hz
  have hsum : q = ∑ i, (u i : ℚ) * (q * (z i : ℚ)) := by
    calc
      q = q * (∑ i, (u i : ℚ) * (z i : ℚ)) := by
        rw [show (∑ i, (u i : ℚ) * (z i : ℚ)) = 1 by
          exact_mod_cast hu, mul_one]
      _ = ∑ i, (u i : ℚ) * (q * (z i : ℚ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  rw [hsum]
  apply sum
  intro i
  exact mul (intCast (u i)) (hcoord i)

theorem normalizationScale_isSInteger {ι : Type*} [Fintype ι]
    {x : ι → ℚ} (hx : x ≠ 0) (hcoord : ∀ i, IsSInteger (x i)) :
    IsSInteger (Primitive.normalizationScale x) := by
  apply scale_isSInteger_of_primitive (Primitive.normalize_primitive hx)
  intro i
  have heq := congrFun (Primitive.eq_normalizationScale_smul x) i
  change x i = Primitive.normalizationScale x *
    (Primitive.normalize x i : ℚ) at heq
  rw [← heq]
  exact hcoord i

/-- The restricted product formula for a nonzero element of `ℤ[1/6]`. -/
theorem one_le_normProduct23 {q : ℚ} (hq : IsSInteger q) (hq0 : q ≠ 0) :
    1 ≤ PadicProduct.normProduct23 q := by
  obtain ⟨k, z, hz⟩ := hq
  let D : ℕ := AdelicMinkowski.denominator k
  have hDpos : 0 < D := AdelicMinkowski.denominator_pos k
  have hD0 : (D : ℚ) ≠ 0 := by positivity
  have hz0 : z ≠ 0 := by
    intro hz0
    apply hq0
    rw [hz, hz0]
    simp
  have hDunit : PadicProduct.IsUnit23 (D : ℚ) := by
    refine ⟨(k : ℤ), (k : ℤ), Or.inl ?_⟩
    simp only [D, AdelicMinkowski.denominator, Nat.cast_pow,
      Nat.cast_ofNat, zpow_natCast]
    rw [← mul_pow]
    norm_num
  have hmul : q * (D : ℚ) = z := by
    rw [hz]
    change (z : ℚ) / (AdelicMinkowski.denominator k : ℚ) *
      (AdelicMinkowski.denominator k : ℚ) = (z : ℚ)
    exact div_mul_cancel₀ _ (by
      exact_mod_cast AdelicMinkowski.denominator_ne_zero k)
  have hprod := PadicSubspace.one_le_threePlaceProduct_int hz0
  rw [← hmul, PadicProduct.normProduct23_mul,
    hDunit.normProduct23_eq_one, mul_one] at hprod
  exact hprod

end SIntegerSix

/-- Rational span `V(Q)` for a fixed real exponent array. -/
def realApproximationSpan {n : ℕ} (L : LocalForms n)
    (Q : ℕ) (c : HeightBoxes.LocalConstants n) :
    Submodule ℚ (RatVector n) :=
  Submodule.span ℚ
    (PadicSubspace.intCastVec '' realIntegralApproximationDomain L Q c)

/-- Rational span of the `ℤ[1/6]` approximation domain. -/
def realSApproximationSpan {n : ℕ} (L : LocalForms n)
    (Q : ℕ) (c : HeightBoxes.LocalConstants n) :
    Submodule ℚ (RatVector n) :=
  Submodule.span ℚ (realSIntegralApproximationDomain L Q c)

/-- Rank of the real-exponent approximation domain `V(Q)`. -/
noncomputable def realApproximationRank {n : ℕ} (L : LocalForms n)
    (Q : ℕ) (c : HeightBoxes.LocalConstants n) : ℕ :=
  Module.finrank ℚ (realApproximationSpan L Q c)

noncomputable def realSApproximationRank {n : ℕ} (L : LocalForms n)
    (Q : ℕ) (c : HeightBoxes.LocalConstants n) : ℕ :=
  Module.finrank ℚ (realSApproximationSpan L Q c)

theorem realSApproximationRank_le_dimension {n : ℕ} (L : LocalForms n)
    (Q : ℕ) (c : HeightBoxes.LocalConstants n) :
    realSApproximationRank L Q c ≤ n := by
  simpa [realSApproximationRank] using
    Submodule.finrank_le (realSApproximationSpan L Q c)

theorem mem_realSApproximationSpan {n : ℕ} {L : LocalForms n}
    {Q : ℕ} {c : HeightBoxes.LocalConstants n} {x : RatVector n}
    (hx : x ∈ realSIntegralApproximationDomain L Q c) :
    x ∈ realSApproximationSpan L Q c :=
  Submodule.subset_span hx

theorem realApproximationRank_le_dimension {n : ℕ} (L : LocalForms n)
    (Q : ℕ) (c : HeightBoxes.LocalConstants n) :
    realApproximationRank L Q c ≤ n := by
  simpa [realApproximationRank] using
    Submodule.finrank_le (realApproximationSpan L Q c)

theorem mem_realApproximationSpan {n : ℕ} {L : LocalForms n}
    {Q : ℕ} {c : HeightBoxes.LocalConstants n} {x : IntVector n}
    (hx : x ∈ realIntegralApproximationDomain L Q c) :
    PadicSubspace.intCastVec x ∈ realApproximationSpan L Q c :=
  Submodule.subset_span ⟨x, hx, rfl⟩

/-- The direct real-radius determinant gap applies to the fine logarithmic
boxes without rounding their exponents. -/
theorem realApproximationRank_lt_of_radiiProduct {n : ℕ}
    (L : LocalForms n) (Q : ℕ) (c : HeightBoxes.LocalConstants n)
    (hsmall : (Nat.factorial n : ℝ) ^ 3 *
        HeightBoxes.exponentRadiiProduct (Q : ℝ) c <
      PadicSubspace.realFormDetProduct L) :
    realApproximationRank L Q c < n := by
  apply lt_of_not_ge
  intro hfull
  have hrank : realApproximationRank L Q c = n :=
    Nat.le_antisymm (realApproximationRank_le_dimension L Q c) hfull
  let D : Set (RatVector n) :=
    PadicSubspace.intCastVec '' realIntegralApproximationDomain L Q c
  have hsetrank : PadicSubspace.rationalSetRank D = n := by
    change Module.finrank ℚ (Submodule.span ℚ D) = n
    change Module.finrank ℚ
      (Submodule.span ℚ
        (PadicSubspace.intCastVec '' realIntegralApproximationDomain L Q c)) = n
    change Module.finrank ℚ
      (Submodule.span ℚ
        (PadicSubspace.intCastVec '' realIntegralApproximationDomain L Q c)) = n
      at hrank
    exact hrank
  obtain ⟨f₀, hfi₀, hfD₀⟩ :=
    PadicSubspace.exists_independent_family_card_rationalSetRank D
  let e : Fin n → Fin (PadicSubspace.rationalSetRank D) :=
    Fin.cast hsetrank.symm
  let f : Fin n → RatVector n := f₀ ∘ e
  have hfi : LinearIndependent ℚ f :=
    hfi₀.comp e (Fin.cast_injective _)
  have hfD : ∀ i, f i ∈ D := fun i ↦ hfD₀ (e i)
  choose x hx hfx using hfD
  have hxmem : ∀ j v i,
      (PadicSubspace.placeNorm v
        (L v i (PadicSubspace.intCastVec (x j))) : ℝ) ≤
          HeightBoxes.exponentRadius (Q : ℝ) c v i := by
    intro j
    simpa [realIntegralApproximationDomain, HeightBoxes.InApproximationBox,
      HeightBoxes.realPlaceNorm] using hx j
  have hcast : (fun j ↦ PadicSubspace.intCastVec (x j)) = f := by
    funext j
    exact hfx j
  have hdep := PadicSubspace.not_linearIndependent_of_real_local_bounds
    L x (HeightBoxes.exponentRadius (Q : ℝ) c)
    (fun v i ↦ Real.rpow_nonneg (Nat.cast_nonneg Q) (c v i)) hxmem (by
      simpa [PadicSubspace.realLocalRadiiProduct,
        HeightBoxes.exponentRadiiProduct] using hsmall)
  apply hdep
  rw [hcast]
  exact hfi

/-- A negative total exponent makes all sufficiently large real-exponent
boxes rank deficient.  This is the elementary determinant stage preceding
the codimension-one stabilization theorem. -/
theorem eventually_realApproximationRank_lt {n : ℕ}
    (L : LocalForms n) (hL : PadicSubspace.IsNonsingularFamily L)
    (c : HeightBoxes.LocalConstants n) {delta : ℝ} (hdelta : 0 < delta)
    (hc : (∑ v, ∑ i, c v i) ≤ -delta) :
    ∀ᶠ Q : ℕ in Filter.atTop, realApproximationRank L Q c < n := by
  have hdet : 0 < PadicSubspace.realFormDetProduct L :=
    PadicSubspace.realFormDetProduct_pos hL
  have htendsto : Filter.Tendsto
      (fun Q : ℕ ↦ (Nat.factorial n : ℝ) ^ 3 * (Q : ℝ) ^ (-delta))
      Filter.atTop (nhds 0) :=
    by
      simpa [Function.comp_def] using
        ((tendsto_rpow_neg_atTop hdelta).comp
          tendsto_natCast_atTop_atTop).const_mul ((Nat.factorial n : ℝ) ^ 3)
  have hsmallEventually : ∀ᶠ Q : ℕ in Filter.atTop,
      (Nat.factorial n : ℝ) ^ 3 * (Q : ℝ) ^ (-delta) <
        PadicSubspace.realFormDetProduct L :=
    htendsto.eventually (Iio_mem_nhds hdet)
  filter_upwards [hsmallEventually, Filter.eventually_ge_atTop 1] with Q hsmall hQ
  apply realApproximationRank_lt_of_radiiProduct L Q c
  calc
    (Nat.factorial n : ℝ) ^ 3 *
        HeightBoxes.exponentRadiiProduct (Q : ℝ) c ≤
      (Nat.factorial n : ℝ) ^ 3 * (Q : ℝ) ^ (-delta) := by
        gcongr
        exact HeightBoxes.exponentRadiiProduct_le (by exact_mod_cast hQ) hc
    _ < PadicSubspace.realFormDetProduct L := hsmall

theorem exists_rankDeficient_cutoff {n : ℕ}
    (L : LocalForms n) (hL : PadicSubspace.IsNonsingularFamily L)
    (c : HeightBoxes.LocalConstants n) {delta : ℝ} (hdelta : 0 < delta)
    (hc : (∑ v, ∑ i, c v i) ≤ -delta) :
    ∃ Q₀ : ℕ, ∀ Q, Q₀ ≤ Q → realApproximationRank L Q c < n := by
  simpa only [Filter.eventually_atTop] using
    eventually_realApproximationRank_lt L hL c hdelta hc

/-! ## Roth-index extraction and bounded nonvanishing -/

/-- A canonical finite coordinate numbering for all variables in all blocks. -/
noncomputable def blockVarEquivFin (m n : ℕ) :
    RothIndex.BlockVar m n ≃ Fin (Fintype.card (RothIndex.BlockVar m n)) :=
  Fintype.equivFin _

/-- Flatten a block polynomial to a `Fin`-indexed polynomial so the
finite-grid lemma applies without changing its coefficients. -/
noncomputable def flattenBlockPolynomial {m n : ℕ}
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ) :
    MvPolynomial (Fin (Fintype.card (RothIndex.BlockVar m n))) ℚ :=
  MvPolynomial.rename (blockVarEquivFin m n) P

theorem flattenBlockPolynomial_ne_zero {m n : ℕ}
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0) :
    flattenBlockPolynomial P ≠ 0 := by
  intro hflat
  apply hP
  apply MvPolynomial.rename_injective (blockVarEquivFin m n)
    (blockVarEquivFin m n).injective
  simpa [flattenBlockPolynomial] using hflat

/-- The corrected derivative/nonvanishing step in GLR §5.1.  A bound for
the ideal index first extracts a divided derivative nonzero on the product
of the hyperplanes; finite-grid Hermite interpolation then supplies a
bounded integral point and one additional coordinatewise-small Hasse order
where that restricted derivative is nonzero. -/
theorem exists_bounded_nonzero_restrictedDerivative_of_formIndex_le
    {m n : ℕ} (M : GeneralizedRoth.FormFamily m n)
    (hM : ∀ j, M j ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0)
    (d : Fin m → ℕ) {indexBound : ℚ}
    (hindex : GeneralizedRoth.formIndex M hM P d ≤ indexBound)
    {gridBound : ℕ} (hgrid : 1 ≤ gridBound) :
    ∃ I : RestrictionIndex.NormalOrder m,
      RestrictionIndex.normalWeight d I ≤ indexBound ∧
      ∃ z : Fin (Fintype.card (RothIndex.BlockVar m n)) → ℤ,
        (∀ i, |z i| ≤ (gridBound : ℤ)) ∧
        ∃ J : Fin (Fintype.card (RothIndex.BlockVar m n)) →₀ ℕ,
          (∀ i, J i ≤ MvPolynomial.degreeOf i
              (flattenBlockPolynomial
                (RestrictionIndex.restrictedDividedDerivative M hM P I)) /
              gridBound) ∧
          RothIndex.hasseCoeff
              (flattenBlockPolynomial
                (RestrictionIndex.restrictedDividedDerivative M hM P I))
              (fun i ↦ (z i : ℚ)) J ≠ 0 := by
  obtain ⟨I, hIweight, hI⟩ :=
    RestrictionIndex.exists_restrictedDividedDerivative_of_formIndex_le
      M hM hP d hindex
  have hflat : flattenBlockPolynomial
      (RestrictionIndex.restrictedDividedDerivative M hM P I) ≠ 0 :=
    flattenBlockPolynomial_ne_zero hI
  obtain ⟨z, hz, J, hJ, hnonzero⟩ :=
    SmallIntegerNonvanishing.exists_smallInteger_hasseCoeff_ne_zero_div
      _ hflat hgrid
  exact ⟨I, hIweight, z, hz, J, hJ, hnonzero⟩

/-! ## Rational form of the auxiliary polynomial -/

/-- Extend the integral auxiliary polynomial to `ℚ`.  The auxiliary
construction uses the ambient coordinate count `n + 1`, while the Roth-index
API uses the projective dimension `n`. -/
noncomputable def rationalAuxiliaryPolynomial {blocks n : ℕ}
    {degree : Fin blocks → ℕ}
    (c : AuxiliaryPolynomial.MonomialIndex blocks (n + 1) degree → ℤ) :
    MvPolynomial (RothIndex.BlockVar blocks n) ℚ :=
  MvPolynomial.map (Int.castRingHom ℚ) (AuxiliaryPolynomial.ofCoefficients c)

@[simp] theorem coeff_rationalAuxiliaryPolynomial {blocks n : ℕ}
    {degree : Fin blocks → ℕ}
    (c : AuxiliaryPolynomial.MonomialIndex blocks (n + 1) degree → ℤ)
    (e : RothIndex.BlockVar blocks n →₀ ℕ) :
    MvPolynomial.coeff e (rationalAuxiliaryPolynomial c) =
      ((MvPolynomial.coeff e (AuxiliaryPolynomial.ofCoefficients c) : ℤ) : ℚ) := by
  rw [rationalAuxiliaryPolynomial, MvPolynomial.coeff_map]
  rfl

theorem rationalAuxiliaryPolynomial_ne_zero {blocks n : ℕ}
    {degree : Fin blocks → ℕ}
    {c : AuxiliaryPolynomial.MonomialIndex blocks (n + 1) degree → ℤ}
    (hc : AuxiliaryPolynomial.ofCoefficients c ≠ 0) :
    rationalAuxiliaryPolynomial c ≠ 0 := by
  exact (MvPolynomial.map_injective
    (Int.castRingHom ℚ) Int.cast_injective).ne hc

/-- Scalar extension preserves the exact block multidegrees returned by the
integral auxiliary-polynomial construction. -/
theorem rationalAuxiliaryPolynomial_isMultiHomogeneous {blocks n : ℕ}
    {degree : Fin blocks → ℕ}
    (c : AuxiliaryPolynomial.MonomialIndex blocks (n + 1) degree → ℤ)
    (hc : GLRAuxiliary.IsMultihomogeneous degree
      (AuxiliaryPolynomial.ofCoefficients c)) :
    RothIndex.IsMultiHomogeneous (rationalAuxiliaryPolynomial c) degree := by
  intro J hJ j
  apply hc J ?_ j
  rw [rationalAuxiliaryPolynomial, MvPolynomial.coeff_map] at hJ
  intro hz
  apply hJ
  simp [hz]

/-- The projective coefficient height of the rational auxiliary polynomial
is controlled by the sup norm of its integral coefficient vector. -/
theorem projectiveCoeffHeight_rationalAuxiliaryPolynomial_le {blocks n : ℕ}
    {degree : Fin blocks → ℕ}
    (c : AuxiliaryPolynomial.MonomialIndex blocks (n + 1) degree → ℤ) :
    PolynomialHeights.projectiveCoeffHeight (rationalAuxiliaryPolynomial c) ≤
      Real.log (max 1 ⌈‖c‖⌉₊) := by
  classical
  let Pz : MvPolynomial (RothIndex.BlockVar blocks n) ℤ :=
    AuxiliaryPolynomial.ofCoefficients c
  let Pq : MvPolynomial (RothIndex.BlockVar blocks n) ℚ :=
    rationalAuxiliaryPolynomial c
  let B : ℕ := max 1 ⌈‖c‖⌉₊
  have hB : 0 < B := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have ha : ∀ J : Pq.support, (MvPolynomial.coeff J.1 Pz).natAbs ≤ B := by
    intro J
    have hnorm : ‖MvPolynomial.coeff J.1 Pz‖ ≤ ‖c‖ := by
      have hJq : MvPolynomial.coeff J.1 Pq ≠ 0 :=
        MvPolynomial.mem_support_iff.mp J.2
      have hJz : J.1 ∈ Pz.support := by
        rw [MvPolynomial.mem_support_iff]
        change MvPolynomial.coeff J.1
          (rationalAuxiliaryPolynomial c) ≠ 0 at hJq
        rw [rationalAuxiliaryPolynomial, MvPolynomial.coeff_map] at hJq
        change MvPolynomial.coeff J.1
          (AuxiliaryPolynomial.ofCoefficients c) ≠ 0
        intro hz
        apply hJq
        simp [hz]
      obtain ⟨M, hM⟩ := AuxiliaryPolynomial.exists_index_of_mem_support c hJz
      change ‖MvPolynomial.coeff J.1
        (AuxiliaryPolynomial.ofCoefficients c)‖ ≤ ‖c‖
      rw [← hM, AuxiliaryPolynomial.coeff_ofCoefficients]
      exact norm_le_pi_norm c M
    have habs : ((MvPolynomial.coeff J.1 Pz).natAbs : ℝ) ≤ ‖c‖ := by
      rw [Int.norm_eq_abs] at hnorm
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hnorm
    have hceil : ‖c‖ ≤ (⌈‖c‖⌉₊ : ℝ) := Nat.le_ceil _
    have hmax : (⌈‖c‖⌉₊ : ℝ) ≤ (B : ℝ) := by
      exact_mod_cast (le_max_right 1 ⌈‖c‖⌉₊)
    exact_mod_cast habs.trans (hceil.trans hmax)
  have h := PolynomialHeights.logHeight_intCast_le_log
    (fun J : Pq.support ↦ MvPolynomial.coeff J.1 Pz) B hB ha
  change Height.logHeight
      (fun J : (rationalAuxiliaryPolynomial c).support ↦
        MvPolynomial.coeff J.1 (rationalAuxiliaryPolynomial c)) ≤ _
  simpa [Pq, Pz, coeff_rationalAuxiliaryPolynomial, B] using h

/-- Monotone version used with the explicit Bombieri--Vaaler norm bound. -/
theorem projectiveCoeffHeight_rationalAuxiliaryPolynomial_le_of_norm_le
    {blocks n : ℕ} {degree : Fin blocks → ℕ}
    (c : AuxiliaryPolynomial.MonomialIndex blocks (n + 1) degree → ℤ)
    {C : ℝ} (hc : ‖c‖ ≤ C) :
    PolynomialHeights.projectiveCoeffHeight (rationalAuxiliaryPolynomial c) ≤
      Real.log (max 1 ⌈C⌉₊) := by
  calc
    PolynomialHeights.projectiveCoeffHeight (rationalAuxiliaryPolynomial c) ≤
        Real.log (max 1 ⌈‖c‖⌉₊) :=
      projectiveCoeffHeight_rationalAuxiliaryPolynomial_le c
    _ ≤ Real.log (max 1 ⌈C⌉₊) := by
      apply Real.log_le_log
      · exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one
          (le_max_left 1 ⌈‖c‖⌉₊))
      · exact_mod_cast max_le_max_left 1 (Nat.ceil_mono hc)

/-- Passing from a nonnegative real coefficient bound to the natural bound
used by `logHeight_intCast_le_log` costs at most a factor two. -/
theorem log_max_natCeil_le_log_two_mul_max {C : ℝ} (hC : 0 ≤ C) :
    Real.log (max 1 ⌈C⌉₊) ≤ Real.log (2 * max 1 C) := by
  apply Real.log_le_log
  · exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one
      (le_max_left 1 ⌈C⌉₊))
  · have hceil : (⌈C⌉₊ : ℝ) ≤ C + 1 :=
      (Nat.ceil_lt_add_one hC).le
    apply max_le
    · have hmax : (1 : ℝ) ≤ max 1 C := le_max_left _ _
      linarith
    · have hmaxC : C ≤ max 1 C := le_max_right _ _
      have hmaxOne : (1 : ℝ) ≤ max 1 C := le_max_left _ _
      exact hceil.trans (by linarith)

/-- Consequently a logarithmic real bound linear in a positive integral
degree remains linear after taking the natural ceiling. -/
theorem log_max_natCeil_le_linear {C A D : ℝ}
    (hC : 0 ≤ C) (hD : 1 ≤ D)
    (hbound : Real.log (max 1 C) ≤ A * D) :
    Real.log (max 1 ⌈C⌉₊) ≤ (A + Real.log 2) * D := by
  have hmaxpos : 0 < max (1 : ℝ) C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  calc
    Real.log (max 1 ⌈C⌉₊) ≤ Real.log (2 * max 1 C) :=
      log_max_natCeil_le_log_two_mul_max hC
    _ = Real.log 2 + Real.log (max 1 C) := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hmaxpos.ne']
    _ ≤ Real.log 2 + A * D := by linarith
    _ ≤ Real.log 2 * D + A * D := by
      have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hgrow : Real.log 2 ≤ Real.log 2 * D := by
        nlinarith [mul_nonneg hlog (sub_nonneg.mpr hD)]
      linarith
    _ = (A + Real.log 2) * D := by ring

/-- A reusable final absorption estimate.  If the logarithm of a fixed
prefactor grows at most linearly in a total degree `S`, if `S` is at most
`B * D`, and the negative approximation exponent saves `kappa * D`, then
half of that saving absorbs the whole prefactor.  This is the real-arithmetic
step at the end of the three-place product-formula contradiction. -/
theorem prefactor_mul_exp_lt_one_of_log_le_linear
    {P C S B kappa D E : ℝ}
    (hP : 0 < P) (hC : 0 ≤ C) (hD : 0 < D)
    (hkappa : 0 < kappa)
    (hlog : Real.log P ≤ C * S)
    (hdegree : S ≤ B * D)
    (hslope : C * B ≤ kappa / 2)
    (hexponent : E ≤ -kappa * D) :
    P * Real.exp E < 1 := by
  have hCB : C * S ≤ C * (B * D) :=
    mul_le_mul_of_nonneg_left hdegree hC
  have hslopeD : (C * B) * D ≤ (kappa / 2) * D :=
    mul_le_mul_of_nonneg_right hslope hD.le
  have hlog' : Real.log P ≤ (kappa / 2) * D := by
    calc
      Real.log P ≤ C * S := hlog
      _ ≤ C * (B * D) := hCB
      _ = (C * B) * D := by ring
      _ ≤ (kappa / 2) * D := hslopeD
  have hkappaD : 0 < kappa * D := mul_pos hkappa hD
  have hnegative : Real.log P + E < 0 := by
    linarith
  rw [← Real.exp_log hP, ← Real.exp_add]
  exact (Real.exp_lt_one_iff).2 hnegative

/-! ## Reconstruction of transformed derivative coefficients -/

theorem blockDegree_sub_order_eq_residual {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (I : GLRAuxiliary.DerivativeIndex blocks coords degree)
    (M : AuxiliaryPolynomial.MonomialIndex blocks coords degree)
    (hle : ∀ x, I.order x ≤ AuxiliaryPolynomial.exponent M x)
    (h : Fin blocks) :
    SymmetricPower.blockDegreeOfFinsupp
      (AuxiliaryPolynomial.toFinsupp M - GLRAuxiliary.orderFinsupp I) h =
      GLRAuxiliary.residualDegree I h := by
  unfold SymmetricPower.blockDegreeOfFinsupp GLRAuxiliary.residualDegree
  change (∑ j,
      (AuxiliaryPolynomial.exponent M (h, j) - I.order (h, j))) =
    degree h - I.blockOrder h
  have hi : ∀ j : Fin coords,
      I.order (h, j) ≤ AuxiliaryPolynomial.exponent M (h, j) :=
    fun j ↦ hle (h, j)
  rw [← AuxiliaryPolynomial.sum_exponent_block M h]
  rw [show I.blockOrder h = ∑ j, I.order (h, j) by
    exact (AuxiliaryPolynomial.sum_exponent_block I.2 h).symm]
  have hsum : ∀ s : Finset (Fin coords),
      (∀ j ∈ s, I.order (h, j) ≤ AuxiliaryPolynomial.exponent M (h, j)) →
      (∑ j ∈ s,
          (AuxiliaryPolynomial.exponent M (h, j) - I.order (h, j))) =
        (∑ j ∈ s, AuxiliaryPolynomial.exponent M (h, j)) -
          ∑ j ∈ s, I.order (h, j) := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
        have ha' := hs a (Finset.mem_insert_self a s)
        have hs' : ∀ j ∈ s,
            I.order (h, j) ≤ AuxiliaryPolynomial.exponent M (h, j) := by
          intro j hj
          exact hs j (Finset.mem_insert_of_mem hj)
        have hssum : (∑ j ∈ s, I.order (h, j)) ≤
            ∑ j ∈ s, AuxiliaryPolynomial.exponent M (h, j) := by
          exact Finset.sum_le_sum fun j hj ↦ hs' j hj
        rw [ih hs']
        omega
  exact hsum Finset.univ (fun j _ ↦ hi j)

theorem chooseProduct_ne_zero_implies_order_le {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (I : GLRAuxiliary.DerivativeIndex blocks coords degree)
    (M : AuxiliaryPolynomial.MonomialIndex blocks coords degree)
    (hne : (∏ x, (Nat.choose (AuxiliaryPolynomial.exponent M x)
      (I.order x) : ℤ)) ≠ 0) :
    ∀ x, I.order x ≤ AuxiliaryPolynomial.exponent M x := by
  intro x
  have hx : (Nat.choose (AuxiliaryPolynomial.exponent M x)
      (I.order x) : ℤ) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hne) x (Finset.mem_univ x)
  have hxN : Nat.choose (AuxiliaryPolynomial.exponent M x)
      (I.order x) ≠ 0 := by exact_mod_cast hx
  exact Nat.not_lt.mp (mt Nat.choose_eq_zero_iff.mpr hxN)

/-- A divided derivative of the fixed multihomogeneous coefficient vector
has no monomials outside its residual block multidegree. -/
theorem ofCoefficients_coeff_dividedDerivativeOfCoefficients
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (I : GLRAuxiliary.DerivativeIndex blocks coords degree)
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ) :
    AuxiliaryPolynomial.ofCoefficients
        (fun J : GLRAuxiliary.ResidualMonomialIndex I ↦
          MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp J)
            (GLRAuxiliary.dividedDerivativeOfCoefficients I c)) =
      GLRAuxiliary.dividedDerivativeOfCoefficients I c := by
  classical
  ext e
  by_cases hdegree : SymmetricPower.blockDegreeOfFinsupp e =
      GLRAuxiliary.residualDegree I
  · let J : GLRAuxiliary.ResidualMonomialIndex I :=
      SymmetricPower.monomialIndexOfFinsuppOfEq e hdegree
    have hJ : AuxiliaryPolynomial.toFinsupp J = e := by simp [J]
    rw [← hJ, AuxiliaryPolynomial.coeff_ofCoefficients]
  · have hleft : MvPolynomial.coeff e
        (AuxiliaryPolynomial.ofCoefficients
          (fun J : GLRAuxiliary.ResidualMonomialIndex I ↦
            MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp J)
              (GLRAuxiliary.dividedDerivativeOfCoefficients I c))) = 0 := by
      apply MvPolynomial.notMem_support_iff.mp
      intro he
      apply hdegree
      funext h
      exact AuxiliaryPolynomial.blockDegree_of_mem_support _ he h
    rw [hleft]
    symm
    simp only [GLRAuxiliary.dividedDerivativeOfCoefficients,
      MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
      GLRAuxiliary.dividedDerivativeMonomial, MvPolynomial.coeff_monomial]
    apply Finset.sum_eq_zero
    intro M _hM
    split_ifs with he
    · have hp : (∏ x, (Nat.choose (AuxiliaryPolynomial.exponent M x)
          (I.order x) : ℤ)) = 0 := by
        by_contra hp
        apply hdegree
        rw [← he]
        funext h
        exact blockDegree_sub_order_eq_residual I M
          (chooseProduct_ne_zero_implies_order_le I M hp) h
      simp [hp]
    · simp

/-- Reconstruct the whole changed divided derivative from the transformed
coefficients.  Thus the vanishing theorem for `transformedCoefficient`
controls every monomial of the actual changed derivative, not only a
distinguished subfamily of coefficients. -/
theorem ofCoefficients_transformedCoefficient
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (T : PadicSubspace.Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (v : PadicSubspace.Place23)
    (I : GLRAuxiliary.DerivativeIndex blocks coords degree)
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ) :
    AuxiliaryPolynomial.ofCoefficients
        (fun J : GLRAuxiliary.ResidualMonomialIndex I ↦
          GLRAuxiliary.transformedCoefficient T v I J c) =
      GLRAuxiliary.changeCoordinates T v
        (GLRAuxiliary.dividedDerivativeOfCoefficients I c) := by
  classical
  let q : GLRAuxiliary.ResidualMonomialIndex I → ℤ := fun J ↦
    MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp J)
      (GLRAuxiliary.dividedDerivativeOfCoefficients I c)
  have hderiv : AuxiliaryPolynomial.ofCoefficients q =
      GLRAuxiliary.dividedDerivativeOfCoefficients I c :=
    ofCoefficients_coeff_dividedDerivativeOfCoefficients I c
  have htrans : ∀ J : GLRAuxiliary.ResidualMonomialIndex I,
      GLRAuxiliary.transformedCoefficient T v I J c =
        GLRAuxiliary.changedCoefficient T v J q := by
    intro J
    rw [GLRAuxiliary.transformedCoefficient_eq_coeff,
      GLRAuxiliary.changedCoefficient_eq_coeff, hderiv]
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [GLRAuxiliary.map_ofCoefficients]
  simp_rw [htrans]
  rw [GLRAuxiliary.ofCoefficients_cast_changedCoefficient]
  rw [GLRAuxiliary.map_changeCoordinates, ← hderiv,
    GLRAuxiliary.map_ofCoefficients]

/-! ## Logarithmic multidegrees -/

/-- A deliberately generous denominator for the fixed error parameter.
The constants are uniform in the proof and remain valid in the exterior
dimensions (at most ten in the application). -/
def rankDropEtaDenominator (n : ℕ) : ℕ := 100 * n * n

def rankDropEta (n : ℕ) : ℚ :=
  1 / rankDropEtaDenominator n

/-- Four ambient-dimension inverse-square units give enough room for the
three-place auxiliary-polynomial row count. -/
def rankDropBlocks (n : ℕ) : ℕ :=
  4 * n * (rankDropEtaDenominator n) ^ 2

def rankDropSigma (n : ℕ) : ℚ :=
  (rankDropEta n / 4) ^ (2 ^ (rankDropBlocks n - 1))

/-- The Roth separation parameter attached to freely chosen auxiliary
parameters.  It is real-valued because that is the interface of the
generalized Roth lemma. -/
noncomputable def rankDropSigmaAt (blocks : ℕ) (eta : ℚ) : ℝ :=
  ((eta : ℝ) / 4) ^ (2 ^ (blocks - 1))

theorem rankDropSigmaAt_pos {blocks : ℕ} {eta : ℚ} (heta : 0 < eta) :
    0 < rankDropSigmaAt blocks eta := by
  exact pow_pos (div_pos (by exact_mod_cast heta) (by norm_num)) _

theorem rankDropSigmaAt_le_half {blocks : ℕ} {eta : ℚ}
    (heta : 0 < eta) (hetaOne : eta ≤ 1) :
    rankDropSigmaAt blocks eta ≤ (1 : ℝ) / 2 := by
  have hbase0 : (0 : ℝ) ≤ (eta : ℝ) / 4 :=
    div_nonneg (by exact_mod_cast heta.le) (by norm_num)
  have hbase1 : (eta : ℝ) / 4 ≤ 1 := by
    have : (eta : ℝ) ≤ 1 := by exact_mod_cast hetaOne
    linarith
  have hexp : 2 ^ (blocks - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  calc
    rankDropSigmaAt blocks eta =
        ((eta : ℝ) / 4) ^ (2 ^ (blocks - 1)) := rfl
    _ ≤ (eta : ℝ) / 4 := pow_le_of_le_one hbase0 hbase1 hexp
    _ ≤ (1 : ℝ) / 2 := by
      have : (eta : ℝ) ≤ 1 := by exact_mod_cast hetaOne
      linarith

/-- The deliberately chosen separation parameter has exactly the root used
in the GLR index extraction. -/
theorem rothRoot_rankDropSigmaAt {blocks : ℕ} {eta : ℚ} (heta : 0 < eta) :
    GeneralizedRoth.rothRoot blocks (rankDropSigmaAt blocks eta) =
      (eta : ℝ) / 4 := by
  unfold GeneralizedRoth.rothRoot rankDropSigmaAt
  exact Real.pow_rpow_inv_natCast
    (div_nonneg (by exact_mod_cast heta.le) (by norm_num))
    (pow_ne_zero _ (by norm_num))

theorem twice_blocks_mul_rothRoot_rankDropSigmaAt
    {blocks : ℕ} {eta : ℚ} (heta : 0 < eta) :
    2 * (blocks : ℝ) * GeneralizedRoth.rothRoot blocks
      (rankDropSigmaAt blocks eta) =
        (blocks : ℝ) * (eta : ℝ) / 2 := by
  rw [rothRoot_rankDropSigmaAt heta]
  ring

theorem rankDropEtaDenominator_pos {n : ℕ} (hn : 0 < n) :
    0 < rankDropEtaDenominator n := by
  simp [rankDropEtaDenominator, hn]

theorem rankDropEta_pos {n : ℕ} (hn : 0 < n) :
    0 < rankDropEta n := by
  rw [rankDropEta]
  exact one_div_pos.mpr (by
    exact_mod_cast rankDropEtaDenominator_pos hn)

theorem rankDropBlocks_pos {n : ℕ} (hn : 0 < n) :
    0 < rankDropBlocks n := by
  unfold rankDropBlocks
  exact Nat.mul_pos (Nat.mul_pos (by norm_num) hn)
    (pow_pos (rankDropEtaDenominator_pos hn) _)

theorem rankDropBlocks_mul_eta_sq {n : ℕ} (hn : 0 < n) :
    (rankDropBlocks n : ℚ) * rankDropEta n ^ 2 = 4 * n := by
  have hden : (rankDropEtaDenominator n : ℚ) ≠ 0 := by
    exact_mod_cast (rankDropEtaDenominator_pos hn).ne'
  simp only [rankDropBlocks, rankDropEta, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_pow]
  field_simp

theorem three_lt_rankDropBlocks_mul_eta_sq {n : ℕ} (hn : 0 < n) :
    (3 : ℚ) < rankDropBlocks n * rankDropEta n ^ 2 := by
  rw [rankDropBlocks_mul_eta_sq hn]
  exact_mod_cast (show 3 < 4 * n by omega)

/-- The exact strict inequality required by
`GLRAuxiliary.card_vanishingRow_lt`. -/
theorem three_mul_dimension_lt_rankDropBlocks_mul_eta_sq {n : ℕ}
    (hn : 0 < n) :
    (3 : ℚ) * n < rankDropBlocks n * rankDropEta n ^ 2 := by
  rw [rankDropBlocks_mul_eta_sq hn]
  exact mul_lt_mul_of_pos_right (by norm_num) (by exact_mod_cast hn)

/-- Choose a rational auxiliary error below any prescribed positive real
threshold and then enough blocks for the three-place row count. -/
theorem exists_rankDropAuxiliaryParameters {coords : ℕ}
    (hcoords : 0 < coords) {target : ℝ} (htarget : 0 < target) :
    ∃ (blocks : ℕ) (eta : ℚ),
      0 < blocks ∧ 0 < eta ∧ eta ≤ 1 ∧ (eta : ℝ) < target ∧
        (3 : ℚ) * coords < blocks * eta ^ 2 := by
  let t : ℝ := min 1 target
  have ht : 0 < t := lt_min (by norm_num) htarget
  obtain ⟨eta, heta0R, hetat⟩ := exists_rat_btwn ht
  have heta0 : (0 : ℚ) < eta := by exact_mod_cast heta0R
  have hetaOneR : (eta : ℝ) < 1 :=
    hetat.trans_le (min_le_left 1 target)
  have hetaOne : eta ≤ 1 := by exact_mod_cast hetaOneR.le
  have hetaTarget : (eta : ℝ) < target :=
    hetat.trans_le (min_le_right 1 target)
  obtain ⟨blocks, hblocks⟩ := exists_nat_gt
    (((3 : ℚ) * coords) / eta ^ 2)
  have hquotNonneg : (0 : ℚ) ≤
      ((3 : ℚ) * coords) / eta ^ 2 := by positivity
  have hblocksPos : 0 < blocks := by
    have : (0 : ℚ) < blocks := hquotNonneg.trans_lt hblocks
    exact_mod_cast this
  refine ⟨blocks, eta, hblocksPos, heta0, hetaOne, hetaTarget, ?_⟩
  exact (div_lt_iff₀ (sq_pos_of_pos heta0)).mp hblocks

/-- Strong-margin parameter choice.  The factor six leaves at least half of
the coefficient space free after imposing all three-place support rows,
which gives a degree-independent Siegel exponent. -/
theorem exists_rankDropAuxiliaryParametersStrong {coords : ℕ}
    (hcoords : 0 < coords) {target : ℝ} (htarget : 0 < target) :
    ∃ (blocks : ℕ) (eta : ℚ),
      0 < blocks ∧ 0 < eta ∧ eta ≤ 1 ∧ (eta : ℝ) < target ∧
        (6 : ℚ) * coords < blocks * eta ^ 2 := by
  let t : ℝ := min 1 target
  have ht : 0 < t := lt_min (by norm_num) htarget
  obtain ⟨eta, heta0R, hetat⟩ := exists_rat_btwn ht
  have heta0 : (0 : ℚ) < eta := by exact_mod_cast heta0R
  have hetaOneR : (eta : ℝ) < 1 :=
    hetat.trans_le (min_le_left 1 target)
  have hetaOne : eta ≤ 1 := by exact_mod_cast hetaOneR.le
  have hetaTarget : (eta : ℝ) < target :=
    hetat.trans_le (min_le_right 1 target)
  obtain ⟨blocks, hblocks⟩ := exists_nat_gt
    (((6 : ℚ) * coords) / eta ^ 2)
  have hquotNonneg : (0 : ℚ) ≤
      ((6 : ℚ) * coords) / eta ^ 2 := by positivity
  have hblocksPos : 0 < blocks := by
    have : (0 : ℚ) < blocks := hquotNonneg.trans_lt hblocks
    exact_mod_cast this
  refine ⟨blocks, eta, hblocksPos, heta0, hetaOne, hetaTarget, ?_⟩
  exact (div_lt_iff₀ (sq_pos_of_pos heta0)).mp hblocks

/-- The GLR auxiliary construction with a freely chosen error parameter and
number of blocks.  This form is needed when the fixed local exponents have
arbitrary size: one first chooses `eta` relative to their finite `L¹` norm,
then enlarges `blocks` to meet the elementary row-count inequality. -/
theorem exists_rankDropAuxiliaryAt {blocks coords : ℕ}
    (L : LocalForms coords) (hL : PadicSubspace.IsNonsingularFamily L)
    (eta : ℚ) (hblocks : 0 < blocks) (hcoords : 0 < coords)
    {degree : Fin blocks → ℕ} (hdegree : ∀ h, 0 < degree h)
    (heta : 0 < eta) (hmany : (3 : ℚ) * coords < blocks * eta ^ 2) :
    ∃ coeff : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ,
      coeff ≠ 0 ∧
      AuxiliaryPolynomial.ofCoefficients coeff ≠ 0 ∧
      GLRAuxiliary.IsMultihomogeneous degree
        (AuxiliaryPolynomial.ofCoefficients coeff) ∧
      (∀ v : PadicSubspace.Place23,
        ∀ K : AuxiliaryPolynomial.MonomialIndex blocks coords degree,
          GLRAuxiliary.OutsideSupportBand eta K →
            GLRAuxiliary.changedCoefficient
              (fun v ↦ PadicSubspace.integralInverseFormMatrix L v) v K coeff = 0) ∧
      (∀ v : PadicSubspace.Place23,
        ∀ I : GLRAuxiliary.DerivativeIndex blocks coords degree,
        ∀ J : GLRAuxiliary.ResidualMonomialIndex I,
            GLRAuxiliary.derivativeWeight I ≤ blocks * eta →
            GLRAuxiliary.OutsideCentralBand eta J →
              GLRAuxiliary.transformedCoefficient
                (fun v ↦ PadicSubspace.integralInverseFormMatrix L v)
                v I J coeff = 0) ∧
      ‖coeff‖ ≤ GLRAuxiliary.coefficientHeightBound
        (degree := degree) eta
          (fun v ↦ PadicSubspace.integralInverseFormMatrix L v) ∧
      (∀ v : PadicSubspace.Place23,
        ∀ I : GLRAuxiliary.DerivativeIndex blocks coords degree,
        ∀ J : GLRAuxiliary.ResidualMonomialIndex I,
          ‖GLRAuxiliary.transformedCoefficient
            (fun v ↦ PadicSubspace.integralInverseFormMatrix L v)
              v I J coeff‖ ≤
            Fintype.card
              (AuxiliaryPolynomial.MonomialIndex blocks coords degree) *
              ‖GLRAuxiliary.fullCoefficientMatrix (degree := degree)
                (fun v ↦ PadicSubspace.integralInverseFormMatrix L v)‖ *
                GLRAuxiliary.coefficientHeightBound
                  (degree := degree) eta
                    (fun v ↦ PadicSubspace.integralInverseFormMatrix L v)) := by
  exact GLRAuxiliary.exists_glrAuxiliaryWithVanishing eta
    (fun v ↦ PadicSubspace.integralInverseFormMatrix L v)
    (PadicSubspace.integralInverseFormMatrix_det_ne_zero hL)
    hblocks hcoords hdegree heta hmany

/-- The unconditional GLR auxiliary polynomial at the concrete rank-drop
parameters and the canonical integral inverse local coordinate changes. -/
theorem exists_rankDropAuxiliary {n : ℕ} (hn : 0 < n)
    (L : LocalForms n) (hL : PadicSubspace.IsNonsingularFamily L)
    {degree : Fin (rankDropBlocks n) → ℕ}
    (hdegree : ∀ h, 0 < degree h) :
    ∃ coeff : AuxiliaryPolynomial.MonomialIndex
        (rankDropBlocks n) n degree → ℤ,
      coeff ≠ 0 ∧
      AuxiliaryPolynomial.ofCoefficients coeff ≠ 0 ∧
      GLRAuxiliary.IsMultihomogeneous degree
        (AuxiliaryPolynomial.ofCoefficients coeff) ∧
      (∀ v : PadicSubspace.Place23,
        ∀ K : AuxiliaryPolynomial.MonomialIndex
          (rankDropBlocks n) n degree,
          GLRAuxiliary.OutsideSupportBand (rankDropEta n) K →
            GLRAuxiliary.changedCoefficient
              (fun v ↦ PadicSubspace.integralInverseFormMatrix L v) v K coeff = 0) ∧
      (∀ v : PadicSubspace.Place23,
        ∀ I : GLRAuxiliary.DerivativeIndex (rankDropBlocks n) n degree,
        ∀ J : GLRAuxiliary.ResidualMonomialIndex I,
            GLRAuxiliary.derivativeWeight I ≤
              rankDropBlocks n * rankDropEta n →
            GLRAuxiliary.OutsideCentralBand (rankDropEta n) J →
              GLRAuxiliary.transformedCoefficient
                (fun v ↦ PadicSubspace.integralInverseFormMatrix L v)
                v I J coeff = 0) ∧
      ‖coeff‖ ≤ GLRAuxiliary.coefficientHeightBound
        (degree := degree) (rankDropEta n)
          (fun v ↦ PadicSubspace.integralInverseFormMatrix L v) ∧
      (∀ v : PadicSubspace.Place23,
        ∀ I : GLRAuxiliary.DerivativeIndex (rankDropBlocks n) n degree,
        ∀ J : GLRAuxiliary.ResidualMonomialIndex I,
          ‖GLRAuxiliary.transformedCoefficient
            (fun v ↦ PadicSubspace.integralInverseFormMatrix L v)
              v I J coeff‖ ≤
            Fintype.card
              (AuxiliaryPolynomial.MonomialIndex
                (rankDropBlocks n) n degree) *
              ‖GLRAuxiliary.fullCoefficientMatrix (degree := degree)
                (fun v ↦ PadicSubspace.integralInverseFormMatrix L v)‖ *
                GLRAuxiliary.coefficientHeightBound
                  (degree := degree) (rankDropEta n)
                    (fun v ↦ PadicSubspace.integralInverseFormMatrix L v)) := by
  exact exists_rankDropAuxiliaryAt L hL (rankDropEta n)
    (rankDropBlocks_pos hn) hn hdegree (rankDropEta_pos hn)
    (three_mul_dimension_lt_rankDropBlocks_mul_eta_sq hn)

theorem rankDropSigma_pos {n : ℕ} (hn : 0 < n) :
    0 < rankDropSigma n := by
  unfold rankDropSigma
  exact pow_pos (div_pos (rankDropEta_pos hn) (by norm_num)) _

theorem rankDropEta_le_one {n : ℕ} (hn : 0 < n) :
    rankDropEta n ≤ 1 := by
  have hden : (1 : ℚ) ≤ rankDropEtaDenominator n := by
    exact_mod_cast rankDropEtaDenominator_pos hn
  have hdenpos : (0 : ℚ) < rankDropEtaDenominator n :=
    zero_lt_one.trans_le hden
  rw [rankDropEta, div_le_iff₀ hdenpos]
  simpa using hden

theorem rankDropSigma_le_half {n : ℕ} (hn : 0 < n) :
    rankDropSigma n ≤ (1 / 2 : ℚ) := by
  have hbase0 : (0 : ℚ) ≤ rankDropEta n / 4 :=
    (div_nonneg (rankDropEta_pos hn).le (by norm_num))
  have hbase1 : rankDropEta n / 4 ≤ (1 : ℚ) := by
    have := rankDropEta_le_one hn
    linarith
  have hexp : 2 ^ (rankDropBlocks n - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  calc
    rankDropSigma n =
        (rankDropEta n / 4) ^ (2 ^ (rankDropBlocks n - 1)) := rfl
    _ ≤ rankDropEta n / 4 := pow_le_of_le_one hbase0 hbase1 hexp
    _ ≤ (1 / 2 : ℚ) := by
      have := rankDropEta_le_one hn
      linarith

/-- The degree `⌊D / log Q⌋` used for the block at scale `Q`. -/
noncomputable def logarithmicDegree (D : ℝ) (Q : ℕ) : ℕ :=
  ⌊D / Real.log (Q : ℝ)⌋₊

theorem logarithmicDegree_cast_le {D : ℝ} {Q : ℕ}
    (hD : 0 ≤ D) (hQ : 2 ≤ Q) :
    (logarithmicDegree D Q : ℝ) ≤ D / Real.log (Q : ℝ) := by
  apply Nat.floor_le
  positivity

theorem div_log_lt_logarithmicDegree_add_one {D : ℝ} {Q : ℕ}
    (hD : 0 ≤ D) (hQ : 2 ≤ Q) :
    D / Real.log (Q : ℝ) < logarithmicDegree D Q + 1 := by
  exact Nat.lt_floor_add_one _

/-- Multiplying the floor estimates by `log Q` shows that every block has
weighted scale `d_Q log Q` within one logarithmic unit below `D`. -/
theorem logarithmicDegree_mul_log_bounds {D : ℝ} {Q : ℕ}
    (hD : 0 ≤ D) (hQ : 2 ≤ Q) :
    D - Real.log (Q : ℝ) <
        (logarithmicDegree D Q : ℝ) * Real.log (Q : ℝ) ∧
      (logarithmicDegree D Q : ℝ) * Real.log (Q : ℝ) ≤ D := by
  have hQreal : (1 : ℝ) < Q := by exact_mod_cast hQ
  have hlog : 0 < Real.log (Q : ℝ) := Real.log_pos hQreal
  have hlower := div_log_lt_logarithmicDegree_add_one hD hQ
  have hupper := logarithmicDegree_cast_le hD hQ
  constructor
  · have := (div_lt_iff₀ hlog).mp hlower
    push_cast at this
    nlinarith
  · exact (le_div_iff₀ hlog).mp hupper

/-- A convenient floor-stability lemma: any real separation inequality with
one unit of slack descends to the corresponding inequality between natural
block degrees. -/
theorem logarithmicDegree_ratio_of_slack {D sigma : ℝ} {Q R : ℕ}
    (hD : 0 ≤ D) (hQ : 2 ≤ Q) (hR : 2 ≤ R)
    (hsigma : 0 ≤ sigma)
    (hsep : D / Real.log (R : ℝ) ≤
      sigma * (D / Real.log (Q : ℝ) - 1)) :
    (logarithmicDegree D R : ℝ) ≤
      sigma * logarithmicDegree D Q := by
  have hRfloor := logarithmicDegree_cast_le hD hR
  have hQfloor := div_log_lt_logarithmicDegree_add_one hD hQ
  have hslack : D / Real.log (Q : ℝ) - 1 <
      logarithmicDegree D Q := by
    push_cast at hQfloor ⊢
    linarith
  exact hRfloor.trans (hsep.trans
    (mul_le_mul_of_nonneg_left hslack.le hsigma))

/-- The total logarithmic multidegree is controlled by the smallest scale.
This is the elementary estimate which converts every coefficient-height
bound linear in `∑ h, degree h` into a bound whose slope in `D` can be
made arbitrarily small by moving the first selected scale to the right. -/
theorem sum_logarithmicDegree_le_minScale {blocks : ℕ} {D : ℝ}
    {Q : Fin blocks → ℕ} (hD : 0 ≤ D) (hQ : ∀ h, 2 ≤ Q h)
    (h₀ : Fin blocks) (hmin : ∀ h, Q h₀ ≤ Q h) :
    (∑ h, (logarithmicDegree D (Q h) : ℝ)) ≤
      (blocks : ℝ) * (D / Real.log (Q h₀ : ℝ)) := by
  have hlog₀ : 0 < Real.log (Q h₀ : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) (hQ h₀))
  calc
    (∑ h, (logarithmicDegree D (Q h) : ℝ)) ≤
        ∑ _h : Fin blocks, D / Real.log (Q h₀ : ℝ) := by
      apply Finset.sum_le_sum
      intro h _
      refine (logarithmicDegree_cast_le hD (hQ h)).trans ?_
      have hlog : Real.log (Q h₀ : ℝ) ≤ Real.log (Q h : ℝ) := by
        apply Real.strictMonoOn_log.monotoneOn
        · change (0 : ℝ) < (Q h₀ : ℝ)
          exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) (hQ h₀))
        · change (0 : ℝ) < (Q h : ℝ)
          exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) (hQ h))
        · exact_mod_cast hmin h
      exact div_le_div_of_nonneg_left hD hlog₀ hlog
    _ = (blocks : ℝ) * (D / Real.log (Q h₀ : ℝ)) := by
      simp

/-- The set whose finiteness is the exact dimension-generic conclusion of
the rational specialization of GLR Theorem 4.14: the distinct codimension-one
spaces occurring as `V(Q)`.  It is defined separately from scales because a
single exceptional space can occur at infinitely many scales. -/
def sCodimOneApproximationSpaces {n : ℕ} (L : LocalForms n)
    (c : HeightBoxes.LocalConstants n) : Set (Submodule ℚ (RatVector n)) :=
  {W | ∃ Q : ℕ, 2 ≤ Q ∧ W = realSApproximationSpan L Q c ∧
    Module.finrank ℚ W + 1 = n}

/-- A canonical scale for a codimension-one `ℤ[1/6]` approximation span. -/
noncomputable def sCodimOneScale {n : ℕ} {L : LocalForms n}
    {c : HeightBoxes.LocalConstants n}
    (W : sCodimOneApproximationSpaces L c) : ℕ :=
  Classical.choose W.2

theorem sCodimOneScale_ge_two {n : ℕ} {L : LocalForms n}
    {c : HeightBoxes.LocalConstants n}
    (W : sCodimOneApproximationSpaces L c) : 2 ≤ sCodimOneScale W :=
  (Classical.choose_spec W.2).1

theorem sCodimOne_eq_span_scale {n : ℕ} {L : LocalForms n}
    {c : HeightBoxes.LocalConstants n}
    (W : sCodimOneApproximationSpaces L c) :
    W.1 = realSApproximationSpan L (sCodimOneScale W) c :=
  (Classical.choose_spec W.2).2.1

theorem sCodimOne_finrank_add_one {n : ℕ} {L : LocalForms n}
    {c : HeightBoxes.LocalConstants n}
    (W : sCodimOneApproximationSpaces L c) :
    Module.finrank ℚ W.1 + 1 = n :=
  (Classical.choose_spec W.2).2.2

def codimOneApproximationSpaces {n : ℕ} (L : LocalForms n)
    (c : HeightBoxes.LocalConstants n) : Set (Submodule ℚ (RatVector n)) :=
  {W | ∃ Q : ℕ, 2 ≤ Q ∧ W = realApproximationSpan L Q c ∧
    Module.finrank ℚ W + 1 = n}

/-- A canonical scale witnessing membership in the codimension-one family. -/
noncomputable def codimOneScale {n : ℕ} {L : LocalForms n}
    {c : HeightBoxes.LocalConstants n}
    (W : codimOneApproximationSpaces L c) : ℕ :=
  Classical.choose W.2

theorem codimOneScale_ge_two {n : ℕ} {L : LocalForms n}
    {c : HeightBoxes.LocalConstants n}
    (W : codimOneApproximationSpaces L c) : 2 ≤ codimOneScale W :=
  (Classical.choose_spec W.2).1

theorem codimOne_eq_span_scale {n : ℕ} {L : LocalForms n}
    {c : HeightBoxes.LocalConstants n}
    (W : codimOneApproximationSpaces L c) :
    W.1 = realApproximationSpan L (codimOneScale W) c :=
  (Classical.choose_spec W.2).2.1

theorem codimOne_finrank_add_one {n : ℕ} {L : LocalForms n}
    {c : HeightBoxes.LocalConstants n}
    (W : codimOneApproximationSpaces L c) :
    Module.finrank ℚ W.1 + 1 = n :=
  (Classical.choose_spec W.2).2.2

/-- Row matrix of a rational family. -/
def rationalRowMatrix {m n : ℕ} (x : Fin m → RatVector n) :
    Matrix (Fin m) (Fin n) ℚ :=
  fun i j ↦ x i j

/-- Local-form evaluation matrix of a rational family. -/
def rationalLocalEvaluationRowMatrix {m n : ℕ} (L : LocalForms n)
    (v : PadicSubspace.Place23) (x : Fin m → RatVector n) :
    Matrix (Fin m) (Fin n) ℚ :=
  fun h i ↦ L v i (x h)

theorem rationalLocalEvaluationRowMatrix_eq_mul {m n : ℕ}
    (L : LocalForms n) (v : PadicSubspace.Place23)
    (x : Fin m → RatVector n) :
    rationalLocalEvaluationRowMatrix L v x =
      rationalRowMatrix x * (PadicSubspace.formMatrix L v)ᵀ := by
  ext h i
  change L v i (x h) = ∑ j, x h j * L v i (Pi.single j 1)
  rw [PadicSubspace.linearForm_eq_sum_coeff]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The bordered cofactor matrix identity for rational rows.  This is the
version used for the `ℤ[1/6]` approximation domain. -/
theorem rational_bordered_localEvaluation_eq_mul {m : ℕ}
    (L : LocalForms (m + 1))
    (hL : PadicSubspace.IsNonsingularFamily L)
    (v : PadicSubspace.Place23) (x : Fin m → RatVector (m + 1))
    (i : Fin (m + 1)) :
    SubspaceHeights.borderedMatrix (rationalRowMatrix x)
        (dualCoefficientVector L v i) *
        (PadicSubspace.formMatrix L v)ᵀ =
      SubspaceHeights.borderedMatrix
        (rationalLocalEvaluationRowMatrix L v x)
        (Pi.single i (1 : ℚ) : RatVector (m + 1)) := by
  ext r k
  cases r using Fin.cases with
  | zero =>
      change Matrix.vecMul (dualCoefficientVector L v i)
        (PadicSubspace.formMatrix L v)ᵀ k =
          (Pi.single i (1 : ℚ) : RatVector (m + 1)) k
      exact congrFun (dualCoefficientVector_vecMul_transpose L hL v i) k
  | succ h =>
      change (rationalRowMatrix x * (PadicSubspace.formMatrix L v)ᵀ) h k =
        rationalLocalEvaluationRowMatrix L v x h k
      exact congrArg (fun M ↦ M h k)
        (rationalLocalEvaluationRowMatrix_eq_mul L v x).symm

/-- Exact local-minor identity for rational rows. -/
theorem rational_cofactor_localEvaluation_eq_det_mul_dual {m : ℕ}
    (L : LocalForms (m + 1))
    (hL : PadicSubspace.IsNonsingularFamily L)
    (v : PadicSubspace.Place23) (x : Fin m → RatVector (m + 1))
    (i : Fin (m + 1)) :
    SubspaceHeights.cofactorVector
        (rationalLocalEvaluationRowMatrix L v x) i =
      (PadicSubspace.formMatrix L v).det *
        (dualCoefficientVector L v i ⬝ᵥ
          SubspaceHeights.cofactorVector (rationalRowMatrix x)) := by
  classical
  let X := rationalRowMatrix x
  let E := rationalLocalEvaluationRowMatrix L v x
  let A := PadicSubspace.formMatrix L v
  calc
    SubspaceHeights.cofactorVector E i =
        Pi.single i 1 ⬝ᵥ SubspaceHeights.cofactorVector E := by
      simp [dotProduct, Pi.single_apply]
    _ = (SubspaceHeights.borderedMatrix E (Pi.single i 1)).det :=
      SubspaceHeights.dotProduct_cofactorVector E (Pi.single i 1)
    _ = (SubspaceHeights.borderedMatrix X
        (dualCoefficientVector L v i) * Aᵀ).det := by
      congr 1
      exact (rational_bordered_localEvaluation_eq_mul L hL v x i).symm
    _ = (SubspaceHeights.borderedMatrix X
        (dualCoefficientVector L v i)).det * (Aᵀ).det := by
      rw [Matrix.det_mul]
    _ = (dualCoefficientVector L v i ⬝ᵥ
        SubspaceHeights.cofactorVector X) * A.det := by
      rw [Matrix.det_transpose]
      rw [SubspaceHeights.dotProduct_cofactorVector]
    _ = A.det * (dualCoefficientVector L v i ⬝ᵥ
        SubspaceHeights.cofactorVector X) := by ring

/-- Cofactor coordinates of a matrix with `ℤ[1/6]` entries again lie in
`ℤ[1/6]`. -/
theorem cofactorVector_isSInteger {m : ℕ}
    (x : Fin m → RatVector (m + 1))
    (hx : ∀ h j, SIntegerSix.IsSInteger (x h j)) (i : Fin (m + 1)) :
    SIntegerSix.IsSInteger
      (SubspaceHeights.cofactorVector (rationalRowMatrix x) i) := by
  rw [SubspaceHeights.cofactorVector_apply]
  apply SIntegerSix.mul
  · simpa using SIntegerSix.intCast ((-1 : ℤ) ^ (i : ℕ))
  · apply SIntegerSix.det
    intro h k
    exact hx h (i.succAbove k)

/-- Local Hadamard bound for a rational basis of the `ℤ[1/6]` domain. -/
theorem realPlaceNorm_rationalCofactor_localEvaluation_le {m : ℕ}
    (L : LocalForms (m + 1)) (Q : ℝ)
    (c : HeightBoxes.LocalConstants (m + 1))
    (x : Fin m → RatVector (m + 1))
    (hQ : 0 ≤ Q)
    (hx : ∀ h v i,
      HeightBoxes.realPlaceNorm v (L v i (x h)) ≤
        HeightBoxes.exponentRadius Q c v i)
    (v : PadicSubspace.Place23) (i : Fin (m + 1)) :
    HeightBoxes.realPlaceNorm v
        (SubspaceHeights.cofactorVector
          (rationalLocalEvaluationRowMatrix L v x) i) ≤
      (Nat.factorial m : ℝ) *
        ∏ k : Fin m, HeightBoxes.exponentRadius Q c v (i.succAbove k) := by
  classical
  let E := rationalLocalEvaluationRowMatrix L v x
  let M : Matrix (Fin m) (Fin m) ℚ := (E.submatrix id i.succAbove)ᵀ
  have hsign : PadicSubspace.placeNorm v ((-1 : ℚ) ^ (i : ℕ)) = 1 := by
    fin_cases v <;> simp [PadicSubspace.placeNorm]
  have hcof : HeightBoxes.realPlaceNorm v
      (SubspaceHeights.cofactorVector E i) =
      (PadicSubspace.placeNorm v M.det : ℝ) := by
    unfold HeightBoxes.realPlaceNorm M
    rw [SubspaceHeights.cofactorVector_apply,
      PadicSubspace.placeNorm_mul, hsign, one_mul, Matrix.det_transpose]
  rw [hcof]
  apply PadicSubspace.real_placeNorm_det_le_rowProduct v M
    (fun k ↦ HeightBoxes.exponentRadius Q c v (i.succAbove k))
  · intro k
    exact Real.rpow_nonneg hQ _
  · intro k h
    change (PadicSubspace.placeNorm v
      (L v (i.succAbove k) (x h)) : ℝ) ≤
        HeightBoxes.exponentRadius Q c v (i.succAbove k)
    exact hx h v (i.succAbove k)

theorem prod_omitted_exponentRadius_eq_rpow {m : ℕ} {Q : ℝ}
    (hQ : 0 < Q) (c : HeightBoxes.LocalConstants (m + 1))
    (i : PadicSubspace.Place23 → Fin (m + 1)) :
    (∏ v, ∏ k : Fin m,
      HeightBoxes.exponentRadius Q c v ((i v).succAbove k)) =
      Q ^ (∑ v, ∑ k : Fin m, c v ((i v).succAbove k)) := by
  simp only [HeightBoxes.exponentRadius]
  calc
    (∏ v, ∏ k : Fin m, Q ^ c v ((i v).succAbove k)) =
        ∏ v, Q ^ (∑ k : Fin m, c v ((i v).succAbove k)) := by
      apply Finset.prod_congr rfl
      intro v _
      exact (Real.rpow_sum_of_pos hQ
        (fun k : Fin m ↦ c v ((i v).succAbove k)) Finset.univ).symm
    _ = Q ^ (∑ v, ∑ k : Fin m, c v ((i v).succAbove k)) :=
      (Real.rpow_sum_of_pos hQ
        (fun v ↦ ∑ k : Fin m, c v ((i v).succAbove k)) Finset.univ).symm

theorem sum_omitted_localConstants_le {m : ℕ}
    (c : HeightBoxes.LocalConstants (m + 1))
    (i : PadicSubspace.Place23 → Fin (m + 1))
    (htotal : (∑ v, ∑ j, c v j) ≤ -(1 / 2 : ℝ))
    (hselected : -(1 / 4 : ℝ) ≤ ∑ v, c v (i v)) :
    (∑ v, ∑ k : Fin m, c v ((i v).succAbove k)) ≤ -(1 / 4 : ℝ) := by
  have hsplit :
      (∑ v, ∑ j, c v j) =
        (∑ v, c v (i v)) +
          ∑ v, ∑ k : Fin m, c v ((i v).succAbove k) := by
    calc
      (∑ v, ∑ j, c v j) =
          ∑ v, (c v (i v) +
            ∑ k : Fin m, c v ((i v).succAbove k)) := by
        apply Finset.sum_congr rfl
        intro v _
        exact Fin.sum_univ_succAbove (c v) (i v)
      _ = (∑ v, c v (i v)) +
          ∑ v, ∑ k : Fin m, c v ((i v).succAbove k) := by
        rw [Finset.sum_add_distrib]
  linarith

/-- Product upper bound in the large-cofactor branch of GLR Lemma 4.22. -/
theorem prod_selected_rationalCofactor_le {m : ℕ}
    (L : LocalForms (m + 1)) (Q : ℝ)
    (c : HeightBoxes.LocalConstants (m + 1))
    (x : Fin m → RatVector (m + 1))
    (hQ : 1 ≤ Q)
    (hx : ∀ h v j,
      HeightBoxes.realPlaceNorm v (L v j (x h)) ≤
        HeightBoxes.exponentRadius Q c v j)
    (i : PadicSubspace.Place23 → Fin (m + 1))
    (htotal : (∑ v, ∑ j, c v j) ≤ -(1 / 2 : ℝ))
    (hselected : -(1 / 4 : ℝ) ≤ ∑ v, c v (i v)) :
    (∏ v, HeightBoxes.realPlaceNorm v
      (SubspaceHeights.cofactorVector
        (rationalLocalEvaluationRowMatrix L v x) (i v))) ≤
      (Nat.factorial m : ℝ) ^ 3 * Q ^ (-(1 / 4 : ℝ)) := by
  have hlocal (v : PadicSubspace.Place23) :=
    realPlaceNorm_rationalCofactor_localEvaluation_le
      L Q c x (zero_le_one.trans hQ) hx v (i v)
  calc
    (∏ v, HeightBoxes.realPlaceNorm v
      (SubspaceHeights.cofactorVector
        (rationalLocalEvaluationRowMatrix L v x) (i v))) ≤
        ∏ v, ((Nat.factorial m : ℝ) *
          ∏ k : Fin m,
            HeightBoxes.exponentRadius Q c v ((i v).succAbove k)) := by
      exact Finset.prod_le_prod
        (fun v _ ↦ HeightBoxes.realPlaceNorm_nonneg _ _) (fun v _ ↦ hlocal v)
    _ = (Nat.factorial m : ℝ) ^ 3 *
        ∏ v, ∏ k : Fin m,
          HeightBoxes.exponentRadius Q c v ((i v).succAbove k) := by
      simp [Finset.prod_mul_distrib]
    _ = (Nat.factorial m : ℝ) ^ 3 *
        Q ^ (∑ v, ∑ k : Fin m, c v ((i v).succAbove k)) := by
      rw [prod_omitted_exponentRadius_eq_rpow (zero_lt_one.trans_le hQ)]
    _ ≤ (Nat.factorial m : ℝ) ^ 3 * Q ^ (-(1 / 4 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hQ
          (sum_omitted_localConstants_le c i htotal hselected)) (by positivity)

/-- Arbitrary-margin form of the omitted-exponent estimate. -/
theorem sum_omitted_localConstants_le_of_delta {m : ℕ}
    (c : HeightBoxes.LocalConstants (m + 1))
    (i : PadicSubspace.Place23 → Fin (m + 1))
    {delta theta : ℝ}
    (htotal : (∑ v, ∑ j, c v j) ≤ -delta)
    (hselected : -theta ≤ ∑ v, c v (i v)) :
    (∑ v, ∑ k : Fin m, c v ((i v).succAbove k)) ≤
      -(delta - theta) := by
  have hsplit :
      (∑ v, ∑ j, c v j) =
        (∑ v, c v (i v)) +
          ∑ v, ∑ k : Fin m, c v ((i v).succAbove k) := by
    calc
      (∑ v, ∑ j, c v j) =
          ∑ v, (c v (i v) +
            ∑ k : Fin m, c v ((i v).succAbove k)) := by
        apply Finset.sum_congr rfl
        intro v _
        exact Fin.sum_univ_succAbove (c v) (i v)
      _ = (∑ v, c v (i v)) +
          ∑ v, ∑ k : Fin m, c v ((i v).succAbove k) := by
        rw [Finset.sum_add_distrib]
  linarith

/-- Product upper bound with an arbitrary negative total exponent and a
chosen support margin. -/
theorem prod_selected_rationalCofactor_le_of_delta {m : ℕ}
    (L : LocalForms (m + 1)) (Q : ℝ)
    (c : HeightBoxes.LocalConstants (m + 1))
    (x : Fin m → RatVector (m + 1))
    (hQ : 1 ≤ Q)
    (hx : ∀ h v j,
      HeightBoxes.realPlaceNorm v (L v j (x h)) ≤
        HeightBoxes.exponentRadius Q c v j)
    (i : PadicSubspace.Place23 → Fin (m + 1))
    {delta theta : ℝ}
    (htotal : (∑ v, ∑ j, c v j) ≤ -delta)
    (hselected : -theta ≤ ∑ v, c v (i v)) :
    (∏ v, HeightBoxes.realPlaceNorm v
      (SubspaceHeights.cofactorVector
        (rationalLocalEvaluationRowMatrix L v x) (i v))) ≤
      (Nat.factorial m : ℝ) ^ 3 * Q ^ (-(delta - theta)) := by
  have hlocal (v : PadicSubspace.Place23) :=
    realPlaceNorm_rationalCofactor_localEvaluation_le
      L Q c x (zero_le_one.trans hQ) hx v (i v)
  calc
    (∏ v, HeightBoxes.realPlaceNorm v
      (SubspaceHeights.cofactorVector
        (rationalLocalEvaluationRowMatrix L v x) (i v))) ≤
        ∏ v, ((Nat.factorial m : ℝ) *
          ∏ k : Fin m,
            HeightBoxes.exponentRadius Q c v ((i v).succAbove k)) := by
      exact Finset.prod_le_prod
        (fun v _ ↦ HeightBoxes.realPlaceNorm_nonneg _ _) (fun v _ ↦ hlocal v)
    _ = (Nat.factorial m : ℝ) ^ 3 *
        ∏ v, ∏ k : Fin m,
          HeightBoxes.exponentRadius Q c v ((i v).succAbove k) := by
      simp [Finset.prod_mul_distrib]
    _ = (Nat.factorial m : ℝ) ^ 3 *
        Q ^ (∑ v, ∑ k : Fin m, c v ((i v).succAbove k)) := by
      rw [prod_omitted_exponentRadius_eq_rpow (zero_lt_one.trans_le hQ)]
    _ ≤ (Nat.factorial m : ℝ) ^ 3 * Q ^ (-(delta - theta)) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hQ
          (sum_omitted_localConstants_le_of_delta
            c i htotal hselected)) (by positivity)

/-- A codimension-one `ℤ[1/6]` approximation span has a rational basis
drawn from its defining domain and a nonzero cofactor normal. -/
theorem exists_sIntegral_basis_cofactor_normal {m : ℕ}
    {L : LocalForms (m + 1)} {c : HeightBoxes.LocalConstants (m + 1)}
    (W : sCodimOneApproximationSpaces L c) :
    ∃ x : Fin m → RatVector (m + 1),
      (∀ i, x i ∈ realSIntegralApproximationDomain L (sCodimOneScale W) c) ∧
      LinearIndependent ℚ x ∧
      W.1 = SubspaceHeights.rowSpace (rationalRowMatrix x) ∧
      SubspaceHeights.cofactorVector (rationalRowMatrix x) ≠ 0 ∧
      (∀ y ∈ W.1,
        y ⬝ᵥ SubspaceHeights.cofactorVector (rationalRowMatrix x) = 0) := by
  classical
  let D : Set (RatVector (m + 1)) :=
    realSIntegralApproximationDomain L (sCodimOneScale W) c
  have hW : W.1 = Submodule.span ℚ D := by
    simpa [D, realSApproximationSpan] using sCodimOne_eq_span_scale W
  have hdimW : Module.finrank ℚ W.1 = m := by
    have h := sCodimOne_finrank_add_one W
    omega
  have hrankD : PadicSubspace.rationalSetRank D = m := by
    change Module.finrank ℚ (Submodule.span ℚ D) = m
    rw [← hW, hdimW]
  obtain ⟨f₀, hfi₀, hfD₀⟩ :=
    PadicSubspace.exists_independent_family_card_rationalSetRank D
  let e : Fin m → Fin (PadicSubspace.rationalSetRank D) :=
    Fin.cast hrankD.symm
  let x : Fin m → RatVector (m + 1) := f₀ ∘ e
  have hxi : LinearIndependent ℚ x :=
    hfi₀.comp e (Fin.cast_injective _)
  have hxmem : ∀ i, x i ∈ D := fun i ↦ hfD₀ (e i)
  let A : Matrix (Fin m) (Fin (m + 1)) ℚ := rationalRowMatrix x
  have hA : LinearIndependent ℚ A.row := by
    change LinearIndependent ℚ x
    exact hxi
  have hrowle : SubspaceHeights.rowSpace A ≤ W.1 := by
    intro y hy
    refine Submodule.span_induction
      (p := fun y _ ↦ y ∈ W.1) ?_ (W.1.zero_mem) ?_ ?_ hy
    · rintro y ⟨i, rfl⟩
      rw [hW]
      exact Submodule.subset_span (hxmem i)
    · intro y z _ _ hy hz
      exact W.1.add_mem hy hz
    · intro a y _ hy
      exact W.1.smul_mem a hy
  have hrowdim : Module.finrank ℚ (SubspaceHeights.rowSpace A) = m := by
    change Module.finrank ℚ (Submodule.span ℚ (Set.range A.row)) = m
    simpa only [Fintype.card_fin] using finrank_span_eq_card hA
  have hrow : W.1 = SubspaceHeights.rowSpace A := by
    symm
    apply Submodule.eq_of_le_of_finrank_le hrowle
    rw [hrowdim, hdimW]
  have hcof0 : SubspaceHeights.cofactorVector A ≠ 0 :=
    SubspaceHeights.cofactorVector_ne_zero_of_linearIndependent_rows hA
  refine ⟨x, hxmem, hxi, hrow, hcof0, ?_⟩
  intro y hy
  rw [hrow] at hy
  refine Submodule.span_induction
    (p := fun y _ ↦ y ⬝ᵥ SubspaceHeights.cofactorVector A = 0)
      ?_ ?_ ?_ ?_ hy
  · rintro y ⟨i, rfl⟩
    exact SubspaceHeights.row_dotProduct_cofactorVector A i
  · simp
  · intro y z _ _ hy hz
    simp [add_dotProduct, hy, hz]
  · intro a y _ hy
    simp [smul_dotProduct, hy]

/-- The rational row matrix attached to an integral family of points. -/
def integralRowMatrix {m n : ℕ} (x : Fin m → IntVector n) :
    Matrix (Fin m) (Fin n) ℚ :=
  fun i j ↦ (x i j : ℚ)

/-- The same row matrix before casting to `ℚ`. -/
def integralRowMatrixInt {m n : ℕ} (x : Fin m → IntVector n) :
    Matrix (Fin m) (Fin n) ℤ :=
  fun i j ↦ x i j

/-- Integral signed maximal minors of an `m × (m+1)` integral matrix. -/
def integralCofactorVector {m : ℕ} (x : Fin m → IntVector (m + 1)) :
    IntVector (m + 1) :=
  fun j ↦ (-1 : ℤ) ^ (j : ℕ) *
    ((integralRowMatrixInt x).submatrix id j.succAbove).det

/-- Casting integral cofactors gives the rational cofactor vector used by
`SubspaceHeights`. -/
theorem intCast_integralCofactorVector {m : ℕ}
    (x : Fin m → IntVector (m + 1)) :
    PadicSubspace.intCastVec (integralCofactorVector x) =
      SubspaceHeights.cofactorVector (integralRowMatrix x) := by
  funext j
  rw [SubspaceHeights.cofactorVector_apply]
  change (((-1 : ℤ) ^ (j : ℕ) *
      ((integralRowMatrixInt x).submatrix id j.succAbove).det : ℤ) : ℚ) = _
  push_cast
  congr 1

/-- Primitive integral representative of the cofactor normal. -/
def primitiveCofactorVector {m : ℕ} (x : Fin m → IntVector (m + 1)) :
    IntVector (m + 1) :=
  Primitive.divideContent (integralCofactorVector x)

theorem integralCofactorVector_ne_zero_of_linearIndependent {m : ℕ}
    {x : Fin m → IntVector (m + 1)}
    (hx : LinearIndependent ℚ
      (fun i ↦ PadicSubspace.intCastVec (x i))) :
    integralCofactorVector x ≠ 0 := by
  have hrow : LinearIndependent ℚ (integralRowMatrix x).row := by
    change LinearIndependent ℚ
      (fun i ↦ PadicSubspace.intCastVec (x i))
    exact hx
  have hcof :=
    SubspaceHeights.cofactorVector_ne_zero_of_linearIndependent_rows hrow
  intro hzero
  apply hcof
  rw [← intCast_integralCofactorVector, hzero]
  rfl

theorem primitiveCofactorVector_primitive {m : ℕ}
    {x : Fin m → IntVector (m + 1)}
    (hx : LinearIndependent ℚ
      (fun i ↦ PadicSubspace.intCastVec (x i))) :
    Primitive.IsPrimitive (primitiveCofactorVector x) :=
  Primitive.divideContent_primitive
    (integralCofactorVector_ne_zero_of_linearIndependent hx)

theorem integralCofactor_eq_content_smul_primitive {m : ℕ}
    (x : Fin m → IntVector (m + 1)) :
    PadicSubspace.intCastVec (integralCofactorVector x) =
      (Primitive.content (integralCofactorVector x) : ℚ) •
        PadicSubspace.intCastVec (primitiveCofactorVector x) := by
  funext i
  change (integralCofactorVector x i : ℚ) =
    (Primitive.content (integralCofactorVector x) : ℚ) *
      (primitiveCofactorVector x i : ℚ)
  exact_mod_cast (Primitive.content_mul_divideContent
    (integralCofactorVector x) i).symm

/-- The logarithmic projective height of a primitive integral tuple is the
logarithm of its box height. -/
theorem logHeight_intCast_eq_log_boxHeight_of_primitive {n : ℕ}
    [NeZero n] {z : IntVector n} (hz : Primitive.IsPrimitive z) :
    Height.logHeight (PadicSubspace.intCastVec z) =
      Real.log (PadicSubspace.boxHeight z : ℝ) := by
  classical
  have hgcd : Finset.univ.gcd z = 1 := by
    obtain ⟨u, hu⟩ := hz
    have hdvd : Finset.univ.gcd z ∣ (1 : ℤ) := by
      rw [← hu]
      exact Finset.dvd_sum fun i hi ↦
        (Finset.gcd_dvd hi).mul_left (u i)
    rw [← Finset.normalize_gcd, normalize_eq_one]
    exact isUnit_iff_dvd_one.mpr hdvd
  have hheight := Rat.logHeight_eq_max_abs_of_gcd_eq_one (x := z) hgcd
  have huniv : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
  obtain ⟨i, _hi, hisup⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset (Fin n)) huniv (fun j ↦ (z j).natAbs)
  have hmax : (⨆ j, |z j|) = (PadicSubspace.boxHeight z : ℤ) := by
    apply le_antisymm
    · apply ciSup_le
      intro j
      rw [← Int.natCast_natAbs]
      exact_mod_cast PadicSubspace.natAbs_le_boxHeight z j
    · calc
        (PadicSubspace.boxHeight z : ℤ) = ((z i).natAbs : ℤ) := by
          exact_mod_cast hisup
        _ = |z i| := Int.natCast_natAbs (z i)
        _ ≤ ⨆ j, |z j| := Finite.le_ciSup (fun j ↦ |z j|) i
  rw [hmax] at hheight
  change Height.logHeight (Int.cast ∘ z) =
    Real.log (PadicSubspace.boxHeight z : ℝ)
  exact hheight

/-- The rational linear form with a prescribed integral coefficient vector.
The projective dimension parameter is `m`, so the coefficient vector has
ambient size `m+1`, matching `GeneralizedRoth`. -/
def primitiveNormalForm {m : ℕ} (z : IntVector (m + 1)) :
    GeneralizedRoth.RatLinearForm m :=
  PadicSubspace.intCastVec z

theorem primitiveNormalForm_ne_zero {m : ℕ} {z : IntVector (m + 1)}
    (hz : z ≠ 0) : primitiveNormalForm z ≠ 0 := by
  change Primitive.intCastVec z ≠ 0
  exact Primitive.intCastVec_ne_zero hz

/-- Exact translation from the primitive normal height in Lemma 4.22 to the
linear-form height used by the generalized Roth lemma. -/
theorem formHeight_primitiveNormalForm_eq_log_boxHeight {m : ℕ}
    {z : IntVector (m + 1)} (hz : Primitive.IsPrimitive z) :
    GeneralizedRoth.formHeight (primitiveNormalForm z) =
      Real.log (PadicSubspace.boxHeight z : ℝ) := by
  letI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  exact logHeight_intCast_eq_log_boxHeight_of_primitive hz

theorem logHeight₁_intCast_coordinate_le_log_boxHeight {n : ℕ}
    {z : IntVector n} (hz : z ≠ 0) (i : Fin n) :
    Height.logHeight₁ (z i : ℚ) ≤
      Real.log (PadicSubspace.boxHeight z : ℝ) := by
  have hHpos : 0 < PadicSubspace.boxHeight z :=
    PadicSubspace.boxHeight_pos hz
  rw [Rat.logHeight₁_eq_log_max]
  simp only [Rat.num_intCast, Rat.den_intCast]
  apply Real.log_le_log
  · positivity
  · exact_mod_cast (max_le
      (PadicSubspace.natAbs_le_boxHeight z i) hHpos)

/-- A fixed dual local form evaluated at a primitive integral normal has
affine height at most `n` times the projective normal height, up to an
explicit constant depending only on that dual form.  The deliberately loose
factor `n` is sufficient for the positive-slope height gap. -/
theorem dualCoordinate_logHeight_le {n : ℕ} [NeZero n]
    (L : LocalForms n) (v : PadicSubspace.Place23) (i : Fin n)
    {z : IntVector n} (hz : z ≠ 0) :
    Height.logHeight₁
        (dualCoefficientVector L v i ⬝ᵥ PadicSubspace.intCastVec z) ≤
      Real.log n +
        (∑ k, Height.logHeight₁ (dualCoefficientVector L v i k)) +
        n * Real.log (PadicSubspace.boxHeight z : ℝ) := by
  classical
  have hsum := Height.logHeight₁_sum_le
    (Finset.univ : Finset (Fin n))
    (fun k ↦ dualCoefficientVector L v i k * (z k : ℚ))
  have htotalWeight : Height.totalWeight ℚ = 1 := by
    rw [NumberField.totalWeight_eq_finrank]
    simp
  have hterm (k : Fin n) :
      Height.logHeight₁
          (dualCoefficientVector L v i k * (z k : ℚ)) ≤
        Height.logHeight₁ (dualCoefficientVector L v i k) +
          Real.log (PadicSubspace.boxHeight z : ℝ) := by
    exact (Height.logHeight₁_mul_le _ _).trans
      (add_le_add (le_refl _)
        (logHeight₁_intCast_coordinate_le_log_boxHeight hz k))
  calc
    Height.logHeight₁
        (dualCoefficientVector L v i ⬝ᵥ PadicSubspace.intCastVec z) ≤
        Real.log n + ∑ k,
          Height.logHeight₁
            (dualCoefficientVector L v i k * (z k : ℚ)) := by
      simpa [dotProduct, PadicSubspace.intCastVec, htotalWeight] using hsum
    _ ≤ Real.log n + ∑ k,
        (Height.logHeight₁ (dualCoefficientVector L v i k) +
          Real.log (PadicSubspace.boxHeight z : ℝ)) := by
      gcongr with k
      exact hterm k
    _ = Real.log n +
        (∑ k, Height.logHeight₁ (dualCoefficientVector L v i k)) +
        n * Real.log (PadicSubspace.boxHeight z : ℝ) := by
      simp [Finset.sum_add_distrib]
      ring

/-- Every one of the three normalized absolute values of a rational number
is bounded by its affine multiplicative height. -/
theorem realPlaceNorm_le_exp_logHeight₁
    (v : PadicSubspace.Place23) (q : ℚ) :
    HeightBoxes.realPlaceNorm v q ≤ Real.exp (Height.logHeight₁ q) := by
  have hdenposQ : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have hdenposR : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  rw [Rat.logHeight₁_eq_log_max, Real.exp_log (by positivity)]
  fin_cases v
  · simp only [HeightBoxes.realPlaceNorm]
    change ((|q| : ℚ) : ℝ) ≤ (max q.num.natAbs q.den : ℕ)
    have hnum : (|q.num| : ℚ) ≤ max q.num.natAbs q.den := by
      have habs : |(q.num : ℚ)| = (q.num.natAbs : ℚ) := by
        rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
      rw [habs]
      exact_mod_cast le_max_left q.num.natAbs q.den
    have hdenone : (1 : ℚ) ≤ q.den := by exact_mod_cast q.den_pos
    have hdiv : (|q.num| : ℚ) / q.den ≤ max q.num.natAbs q.den :=
      (div_le_iff₀ hdenposQ).2
        (hnum.trans (le_mul_of_one_le_right (by positivity) hdenone))
    exact_mod_cast (calc
      |q| = |(q.num : ℚ) / q.den| :=
        congrArg abs q.num_div_den.symm
      _ = (|q.num| : ℚ) / q.den := by rw [abs_div]; simp
      _ ≤ max q.num.natAbs q.den := hdiv)
  · simp only [HeightBoxes.realPlaceNorm]
    change (padicNorm 2 q : ℝ) ≤ (max q.num.natAbs q.den : ℕ)
    have hden0 : (q.den : ℚ) ≠ 0 := ne_of_gt hdenposQ
    have hpden0 : padicNorm 2 (q.den : ℚ) ≠ 0 :=
      padicNorm.nonzero hden0
    have hpdenpos : 0 < padicNorm 2 (q.den : ℚ) :=
      lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm hpden0)
    have h3 : padicNorm 3 (q.den : ℚ) ≤ 1 := by
      simpa only [Int.cast_natCast] using
        (padicNorm.of_int (p := 3) (q.den : ℤ))
    have hprod := PadicSubspace.one_le_threePlaceProduct_int
      (show (q.den : ℤ) ≠ 0 by exact_mod_cast q.den_ne_zero)
    rw [PadicProduct.normProduct23, PadicProduct.archNorm] at hprod
    have habs : |((q.den : ℤ) : ℚ)| = (q.den : ℚ) :=
      abs_of_pos (by exact_mod_cast q.den_pos)
    rw [habs] at hprod
    have hbase : (1 : ℚ) ≤ q.den * padicNorm 2 (q.den : ℚ) := by
      calc
        1 ≤ (q.den : ℚ) * padicNorm 2 (q.den : ℚ) *
            padicNorm 3 (q.den : ℚ) := hprod
        _ ≤ (q.den : ℚ) * padicNorm 2 (q.den : ℚ) * 1 :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = (q.den : ℚ) * padicNorm 2 (q.den : ℚ) := by ring
    have hinv : (padicNorm 2 (q.den : ℚ))⁻¹ ≤ q.den := by
      rw [inv_le_iff_one_le_mul₀ hpdenpos]
      simpa [mul_comm] using hbase
    have hq : padicNorm 2 q ≤ q.den := by
      calc
        padicNorm 2 q = padicNorm 2 ((q.num : ℚ) / q.den) := by
          rw [q.num_div_den]
        _ = padicNorm 2 (q.num : ℚ) /
            padicNorm 2 (q.den : ℚ) := padicNorm.div _ _
        _ ≤ 1 / padicNorm 2 (q.den : ℚ) :=
          div_le_div_of_nonneg_right
            (by simpa only [Int.cast_id] using
              (padicNorm.of_int (p := 2) q.num))
            (padicNorm.nonneg _)
        _ ≤ q.den := by simpa [div_eq_mul_inv] using hinv
    exact_mod_cast hq.trans (by exact_mod_cast le_max_right q.num.natAbs q.den)

  · simp only [HeightBoxes.realPlaceNorm]
    change (padicNorm 3 q : ℝ) ≤ (max q.num.natAbs q.den : ℕ)
    have hden0 : (q.den : ℚ) ≠ 0 := ne_of_gt hdenposQ
    have hpden0 : padicNorm 3 (q.den : ℚ) ≠ 0 :=
      padicNorm.nonzero hden0
    have hpdenpos : 0 < padicNorm 3 (q.den : ℚ) :=
      lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm hpden0)
    have h2 : padicNorm 2 (q.den : ℚ) ≤ 1 := by
      simpa only [Int.cast_natCast] using
        (padicNorm.of_int (p := 2) (q.den : ℤ))
    have hprod := PadicSubspace.one_le_threePlaceProduct_int
      (show (q.den : ℤ) ≠ 0 by exact_mod_cast q.den_ne_zero)
    rw [PadicProduct.normProduct23, PadicProduct.archNorm] at hprod
    have habs : |((q.den : ℤ) : ℚ)| = (q.den : ℚ) :=
      abs_of_pos (by exact_mod_cast q.den_pos)
    rw [habs] at hprod
    have hbase : (1 : ℚ) ≤ q.den * padicNorm 3 (q.den : ℚ) := by
      calc
        1 ≤ (q.den : ℚ) * padicNorm 2 (q.den : ℚ) *
            padicNorm 3 (q.den : ℚ) := hprod
        _ ≤ (q.den : ℚ) * 1 * padicNorm 3 (q.den : ℚ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h2 (by positivity))
            (padicNorm.nonneg _)
        _ = (q.den : ℚ) * padicNorm 3 (q.den : ℚ) := by ring
    have hinv : (padicNorm 3 (q.den : ℚ))⁻¹ ≤ q.den := by
      rw [inv_le_iff_one_le_mul₀ hpdenpos]
      simpa [mul_comm] using hbase
    have hq : padicNorm 3 q ≤ q.den := by
      calc
        padicNorm 3 q = padicNorm 3 ((q.num : ℚ) / q.den) := by
          rw [q.num_div_den]
        _ = padicNorm 3 (q.num : ℚ) /
            padicNorm 3 (q.den : ℚ) := padicNorm.div _ _
        _ ≤ 1 / padicNorm 3 (q.den : ℚ) :=
          div_le_div_of_nonneg_right
            (by simpa only [Int.cast_id] using
              (padicNorm.of_int (p := 3) q.num))
            (padicNorm.nonneg _)
        _ ≤ q.den := by simpa [div_eq_mul_inv] using hinv
    exact_mod_cast hq.trans (by exact_mod_cast le_max_right q.num.natAbs q.den)

theorem realPlaceNorm_mul (v : PadicSubspace.Place23) (q r : ℚ) :
    HeightBoxes.realPlaceNorm v (q * r) =
      HeightBoxes.realPlaceNorm v q * HeightBoxes.realPlaceNorm v r := by
  unfold HeightBoxes.realPlaceNorm
  norm_cast
  exact PadicSubspace.placeNorm_mul v q r

theorem prod_realPlaceNorm_eq_normProduct23 (q : ℚ) :
    (∏ v, HeightBoxes.realPlaceNorm v q) = PadicProduct.normProduct23 q := by
  have h := congrArg ((↑) : ℚ → ℝ)
    (PadicSubspace.prod_placeNorm_eq_threePlaceProduct q)
  simpa [HeightBoxes.realPlaceNorm] using h

/-- The inverse form of the preceding height bound. -/
theorem exp_neg_logHeight₁_le_realPlaceNorm
    (v : PadicSubspace.Place23) {q : ℚ} (hq : q ≠ 0) :
    Real.exp (-Height.logHeight₁ q) ≤ HeightBoxes.realPlaceNorm v q := by
  have hnorm : 0 < HeightBoxes.realPlaceNorm v q := by
    fin_cases v
    · simpa [HeightBoxes.realPlaceNorm, PadicSubspace.placeNorm] using
        abs_pos.mpr hq
    · simp only [HeightBoxes.realPlaceNorm]
      exact_mod_cast lt_of_le_of_ne (padicNorm.nonneg _)
        (Ne.symm (padicNorm.nonzero hq))
    · simp only [HeightBoxes.realPlaceNorm]
      exact_mod_cast lt_of_le_of_ne (padicNorm.nonneg _)
        (Ne.symm (padicNorm.nonzero hq))
  have hinv := realPlaceNorm_le_exp_logHeight₁ v q⁻¹
  have hnormInv : HeightBoxes.realPlaceNorm v q⁻¹ =
      (HeightBoxes.realPlaceNorm v q)⁻¹ := by
    fin_cases v
    · simp [HeightBoxes.realPlaceNorm, PadicSubspace.placeNorm, abs_inv]
    · change (padicNorm 2 q⁻¹ : ℝ) = (padicNorm 2 q : ℝ)⁻¹
      norm_cast
      rw [show q⁻¹ = 1 / q by simp, padicNorm.div]
      simp
    · change (padicNorm 3 q⁻¹ : ℝ) = (padicNorm 3 q : ℝ)⁻¹
      norm_cast
      rw [show q⁻¹ = 1 / q by simp, padicNorm.div]
      simp
  rw [Height.logHeight₁_inv, hnormInv] at hinv
  rw [Real.exp_neg, ← inv_inv (HeightBoxes.realPlaceNorm v q)]
  exact (inv_le_inv₀ (Real.exp_pos _)
    (inv_pos.mpr hnorm)).2 hinv

/-- The product-formula lower bound for the selected nonzero cofactors,
expressed through the primitive integral normal.  Together with
`prod_selected_rationalCofactor_le` this is the quantitative branch of the
repaired GLR Lemma 4.22. -/
theorem realFormDet_mul_exp_neg_normalHeight_le_selectedCofactors {m : ℕ}
    (L : LocalForms (m + 1))
    (hL : PadicSubspace.IsNonsingularFamily L)
    (x : Fin m → RatVector (m + 1))
    (hxlin : LinearIndependent ℚ x)
    (hxS : ∀ h, AdelicMinkowski.InZOneSix (x h))
    (i : PadicSubspace.Place23 → Fin (m + 1))
    (hcof : ∀ v,
      SubspaceHeights.cofactorVector
        (rationalLocalEvaluationRowMatrix L v x) (i v) ≠ 0) :
    PadicSubspace.realFormDetProduct L *
        Real.exp (-(
          (∑ v, (Real.log (m + 1) +
            ∑ k, Height.logHeight₁ (dualCoefficientVector L v (i v) k))) +
          3 * (m + 1) *
            Real.log (PadicSubspace.boxHeight
              (Primitive.normalize
                (SubspaceHeights.cofactorVector (rationalRowMatrix x))) : ℝ))) ≤
      ∏ v, HeightBoxes.realPlaceNorm v
        (SubspaceHeights.cofactorVector
          (rationalLocalEvaluationRowMatrix L v x) (i v)) := by
  classical
  letI : NeZero (m + 1) := ⟨by omega⟩
  let b : RatVector (m + 1) :=
    SubspaceHeights.cofactorVector (rationalRowMatrix x)
  have hrow : LinearIndependent ℚ (rationalRowMatrix x).row := by
    change LinearIndependent ℚ x
    exact hxlin
  have hb0 : b ≠ 0 :=
    SubspaceHeights.cofactorVector_ne_zero_of_linearIndependent_rows hrow
  let z : IntVector (m + 1) := Primitive.normalize b
  let q : ℚ := Primitive.normalizationScale b
  have hz0 : z ≠ 0 := Primitive.normalize_ne_zero hb0
  have hq0 : q ≠ 0 := Primitive.normalizationScale_ne_zero hb0
  have hbscale : b = q • PadicSubspace.intCastVec z := by
    exact Primitive.eq_normalizationScale_smul b
  have hbS (j : Fin (m + 1)) : SIntegerSix.IsSInteger (b j) := by
    apply cofactorVector_isSInteger x
    intro h k
    exact SIntegerSix.of_inZOneSix_coordinate (hxS h) k
  have hqS : SIntegerSix.IsSInteger q := by
    apply SIntegerSix.normalizationScale_isSInteger hb0
    exact hbS
  have hqprod : (1 : ℝ) ≤ ∏ v, HeightBoxes.realPlaceNorm v q := by
    rw [prod_realPlaceNorm_eq_normProduct23]
    exact_mod_cast SIntegerSix.one_le_normProduct23 hqS hq0
  let s : PadicSubspace.Place23 → ℚ := fun v ↦
    dualCoefficientVector L v (i v) ⬝ᵥ PadicSubspace.intCastVec z
  have hdot (v : PadicSubspace.Place23) :
      dualCoefficientVector L v (i v) ⬝ᵥ b = q * s v := by
    rw [hbscale]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, s]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hs0 (v : PadicSubspace.Place23) : s v ≠ 0 := by
    intro hsv
    apply hcof v
    rw [rational_cofactor_localEvaluation_eq_det_mul_dual L hL v x (i v),
      hdot v, hsv, mul_zero, mul_zero]
  have hfactor (v : PadicSubspace.Place23) :
      HeightBoxes.realPlaceNorm v
          (SubspaceHeights.cofactorVector
            (rationalLocalEvaluationRowMatrix L v x) (i v)) =
        HeightBoxes.realPlaceNorm v (PadicSubspace.formMatrix L v).det *
          HeightBoxes.realPlaceNorm v q *
            HeightBoxes.realPlaceNorm v (s v) := by
    rw [rational_cofactor_localEvaluation_eq_det_mul_dual L hL v x (i v),
      hdot v, realPlaceNorm_mul, realPlaceNorm_mul]
    ring
  have hsLower (v : PadicSubspace.Place23) :
      Real.exp (-Height.logHeight₁ (s v)) ≤
        HeightBoxes.realPlaceNorm v (s v) :=
    exp_neg_logHeight₁_le_realPlaceNorm v (hs0 v)
  have hprodSLower :
      Real.exp (-(∑ v, Height.logHeight₁ (s v))) ≤
        ∏ v, HeightBoxes.realPlaceNorm v (s v) := by
    calc
      Real.exp (-(∑ v, Height.logHeight₁ (s v))) =
          ∏ v, Real.exp (-Height.logHeight₁ (s v)) := by
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.sum_neg_distrib]
      _ ≤ ∏ v, HeightBoxes.realPlaceNorm v (s v) :=
        Finset.prod_le_prod (fun v _ ↦ (Real.exp_pos _).le)
          (fun v _ ↦ hsLower v)
  have hheight (v : PadicSubspace.Place23) :
      Height.logHeight₁ (s v) ≤
        Real.log (m + 1) +
          (∑ k, Height.logHeight₁ (dualCoefficientVector L v (i v) k)) +
          (m + 1) * Real.log (PadicSubspace.boxHeight z : ℝ) := by
    simpa [s, Nat.cast_add, Nat.cast_one] using
      (dualCoordinate_logHeight_le L v (i v) hz0)
  have hheightSum :
      (∑ v, Height.logHeight₁ (s v)) ≤
        (∑ v, (Real.log (m + 1) +
          ∑ k, Height.logHeight₁ (dualCoefficientVector L v (i v) k))) +
          3 * (m + 1) * Real.log (PadicSubspace.boxHeight z : ℝ) := by
    calc
      (∑ v, Height.logHeight₁ (s v)) ≤
          ∑ v, (Real.log (m + 1) +
            (∑ k, Height.logHeight₁
              (dualCoefficientVector L v (i v) k)) +
            (m + 1) * Real.log (PadicSubspace.boxHeight z : ℝ)) := by
        exact Finset.sum_le_sum fun v _ ↦ hheight v
      _ = (∑ v, (Real.log (m + 1) +
          ∑ k, Height.logHeight₁ (dualCoefficientVector L v (i v) k))) +
          3 * (m + 1) * Real.log (PadicSubspace.boxHeight z : ℝ) := by
        simp [Finset.sum_add_distrib]
        ring
  have hExp :
      Real.exp (-(
        (∑ v, (Real.log (m + 1) +
          ∑ k, Height.logHeight₁ (dualCoefficientVector L v (i v) k))) +
          3 * (m + 1) * Real.log (PadicSubspace.boxHeight z : ℝ))) ≤
        ∏ v, HeightBoxes.realPlaceNorm v (s v) := by
    exact (Real.exp_le_exp.mpr (neg_le_neg hheightSum)).trans hprodSLower
  have hprodEq :
      (∏ v, HeightBoxes.realPlaceNorm v
        (SubspaceHeights.cofactorVector
          (rationalLocalEvaluationRowMatrix L v x) (i v))) =
        PadicSubspace.realFormDetProduct L *
          (∏ v, HeightBoxes.realPlaceNorm v q) *
            ∏ v, HeightBoxes.realPlaceNorm v (s v) := by
    simp_rw [hfactor, Finset.prod_mul_distrib]
    have hdet : (∏ v, HeightBoxes.realPlaceNorm v
        (PadicSubspace.formMatrix L v).det) =
        PadicSubspace.realFormDetProduct L := by
      simp [HeightBoxes.realPlaceNorm, PadicSubspace.realFormDetProduct,
        PadicSubspace.formDetProduct]
    rw [hdet]
  rw [hprodEq]
  have hprodSnonneg : 0 ≤ ∏ v, HeightBoxes.realPlaceNorm v (s v) :=
    Finset.prod_nonneg fun v _ ↦ HeightBoxes.realPlaceNorm_nonneg _ _
  have hqmul : (∏ v, HeightBoxes.realPlaceNorm v (s v)) ≤
      (∏ v, HeightBoxes.realPlaceNorm v q) *
        ∏ v, HeightBoxes.realPlaceNorm v (s v) := by
    exact le_mul_of_one_le_left hprodSnonneg hqprod
  simpa only [z, b, mul_assoc] using
    (mul_le_mul_of_nonneg_left (hExp.trans hqmul)
      (PadicSubspace.realFormDetProduct_nonneg L))

/-- Explicit positive-slope normal-height gap in the nonexceptional
large-cofactor branch.  The coefficient of `log Q` is `1/4`; dividing the
conclusion by `3(m+1)` gives the usual linear lower bound for the height of
the primitive hyperplane normal. -/
theorem selectedCofactor_normalHeight_gap {m : ℕ}
    (L : LocalForms (m + 1))
    (hL : PadicSubspace.IsNonsingularFamily L)
    (Q : ℝ) (hQ : 1 < Q)
    (c : HeightBoxes.LocalConstants (m + 1))
    (x : Fin m → RatVector (m + 1))
    (hxlin : LinearIndependent ℚ x)
    (hxS : ∀ h, AdelicMinkowski.InZOneSix (x h))
    (hxbox : ∀ h v j,
      HeightBoxes.realPlaceNorm v (L v j (x h)) ≤
        HeightBoxes.exponentRadius Q c v j)
    (i : PadicSubspace.Place23 → Fin (m + 1))
    (hcof : ∀ v,
      SubspaceHeights.cofactorVector
        (rationalLocalEvaluationRowMatrix L v x) (i v) ≠ 0)
    (htotal : (∑ v, ∑ j, c v j) ≤ -(1 / 2 : ℝ))
    (hselected : -(1 / 4 : ℝ) ≤ ∑ v, c v (i v)) :
    (1 / 4 : ℝ) * Real.log Q +
        Real.log (PadicSubspace.realFormDetProduct L) -
        (∑ v, (Real.log (m + 1) +
          ∑ k, Height.logHeight₁ (dualCoefficientVector L v (i v) k))) -
        3 * Real.log (Nat.factorial m : ℝ) ≤
      3 * (m + 1) *
        Real.log (PadicSubspace.boxHeight
          (Primitive.normalize
            (SubspaceHeights.cofactorVector (rationalRowMatrix x))) : ℝ) := by
  let C : ℝ := ∑ v, (Real.log (m + 1) +
    ∑ k, Height.logHeight₁ (dualCoefficientVector L v (i v) k))
  let H : ℝ := Real.log (PadicSubspace.boxHeight
    (Primitive.normalize
      (SubspaceHeights.cofactorVector (rationalRowMatrix x))) : ℝ)
  have hlower := realFormDet_mul_exp_neg_normalHeight_le_selectedCofactors
    L hL x hxlin hxS i hcof
  have hupper := prod_selected_rationalCofactor_le
    L Q c x hQ.le hxbox i htotal hselected
  have hcompare :
      PadicSubspace.realFormDetProduct L *
          Real.exp (-(C + 3 * (m + 1) * H)) ≤
        (Nat.factorial m : ℝ) ^ 3 * Q ^ (-(1 / 4 : ℝ)) := by
    exact hlower.trans hupper
  have hF : 0 < PadicSubspace.realFormDetProduct L :=
    PadicSubspace.realFormDetProduct_pos hL
  have hfac : (0 : ℝ) < Nat.factorial m := by positivity
  have hQpos : 0 < Q := zero_lt_one.trans hQ
  have hleft : 0 < PadicSubspace.realFormDetProduct L *
      Real.exp (-(C + 3 * (m + 1) * H)) := mul_pos hF (Real.exp_pos _)
  have hright : 0 < (Nat.factorial m : ℝ) ^ 3 *
      Q ^ (-(1 / 4 : ℝ)) :=
    mul_pos (pow_pos hfac _) (Real.rpow_pos_of_pos hQpos _)
  have hlog := Real.strictMonoOn_log.monotoneOn hleft hright hcompare
  rw [Real.log_mul hF.ne' (Real.exp_ne_zero _), Real.log_exp,
    Real.log_mul (pow_ne_zero _ hfac.ne')
      (Real.rpow_pos_of_pos hQpos _).ne',
    Real.log_pow, Real.log_rpow hQpos] at hlog
  dsimp [C, H] at hlog ⊢
  push_cast at hlog ⊢
  linarith

/-- Arbitrary-margin form of the normal-height gap. -/
theorem selectedCofactor_normalHeight_gap_of_delta {m : ℕ}
    (L : LocalForms (m + 1))
    (hL : PadicSubspace.IsNonsingularFamily L)
    (Q : ℝ) (hQ : 1 < Q)
    (c : HeightBoxes.LocalConstants (m + 1))
    (x : Fin m → RatVector (m + 1))
    (hxlin : LinearIndependent ℚ x)
    (hxS : ∀ h, AdelicMinkowski.InZOneSix (x h))
    (hxbox : ∀ h v j,
      HeightBoxes.realPlaceNorm v (L v j (x h)) ≤
        HeightBoxes.exponentRadius Q c v j)
    (i : PadicSubspace.Place23 → Fin (m + 1))
    (hcof : ∀ v,
      SubspaceHeights.cofactorVector
        (rationalLocalEvaluationRowMatrix L v x) (i v) ≠ 0)
    {delta theta : ℝ}
    (htotal : (∑ v, ∑ j, c v j) ≤ -delta)
    (hselected : -theta ≤ ∑ v, c v (i v)) :
    (delta - theta) * Real.log Q +
        Real.log (PadicSubspace.realFormDetProduct L) -
        (∑ v, (Real.log (m + 1) +
          ∑ k, Height.logHeight₁ (dualCoefficientVector L v (i v) k))) -
        3 * Real.log (Nat.factorial m : ℝ) ≤
      3 * (m + 1) *
        Real.log (PadicSubspace.boxHeight
          (Primitive.normalize
            (SubspaceHeights.cofactorVector (rationalRowMatrix x))) : ℝ) := by
  let C : ℝ := ∑ v, (Real.log (m + 1) +
    ∑ k, Height.logHeight₁ (dualCoefficientVector L v (i v) k))
  let H : ℝ := Real.log (PadicSubspace.boxHeight
    (Primitive.normalize
      (SubspaceHeights.cofactorVector (rationalRowMatrix x))) : ℝ)
  have hlower := realFormDet_mul_exp_neg_normalHeight_le_selectedCofactors
    L hL x hxlin hxS i hcof
  have hupper := prod_selected_rationalCofactor_le_of_delta
    L Q c x hQ.le hxbox i htotal hselected
  have hcompare :
      PadicSubspace.realFormDetProduct L *
          Real.exp (-(C + 3 * (m + 1) * H)) ≤
        (Nat.factorial m : ℝ) ^ 3 * Q ^ (-(delta - theta)) :=
    hlower.trans hupper
  have hF : 0 < PadicSubspace.realFormDetProduct L :=
    PadicSubspace.realFormDetProduct_pos hL
  have hfac : (0 : ℝ) < Nat.factorial m := by positivity
  have hQpos : 0 < Q := zero_lt_one.trans hQ
  have hleft : 0 < PadicSubspace.realFormDetProduct L *
      Real.exp (-(C + 3 * (m + 1) * H)) := mul_pos hF (Real.exp_pos _)
  have hright : 0 < (Nat.factorial m : ℝ) ^ 3 *
      Q ^ (-(delta - theta)) :=
    mul_pos (pow_pos hfac _) (Real.rpow_pos_of_pos hQpos _)
  have hlog := Real.strictMonoOn_log.monotoneOn hleft hright hcompare
  rw [Real.log_mul hF.ne' (Real.exp_ne_zero _), Real.log_exp,
    Real.log_mul (pow_ne_zero _ hfac.ne')
      (Real.rpow_pos_of_pos hQpos _).ne',
    Real.log_pow, Real.log_rpow hQpos] at hlog
  dsimp [C, H] at hlog ⊢
  push_cast at hlog ⊢
  linarith

/-- Support of the local cofactor coordinates of a codimension-one basis. -/
noncomputable def cofactorSupportPattern {m : ℕ}
    (L : LocalForms (m + 1)) (x : Fin m → RatVector (m + 1)) :
    LocalSupportPattern (m + 1) :=
  fun v ↦ Finset.univ.filter fun i ↦
    SubspaceHeights.cofactorVector
      (rationalLocalEvaluationRowMatrix L v x) i ≠ 0

@[simp] theorem mem_cofactorSupportPattern_iff {m : ℕ}
    (L : LocalForms (m + 1)) (x : Fin m → RatVector (m + 1))
    (v : PadicSubspace.Place23) (i : Fin (m + 1)) :
    i ∈ cofactorSupportPattern L x v ↔
      SubspaceHeights.cofactorVector
        (rationalLocalEvaluationRowMatrix L v x) i ≠ 0 := by
  simp [cofactorSupportPattern]

theorem cofactorSupportPattern_nonempty {m : ℕ}
    (L : LocalForms (m + 1))
    (hL : PadicSubspace.IsNonsingularFamily L)
    (x : Fin m → RatVector (m + 1))
    (hxlin : LinearIndependent ℚ x)
    (v : PadicSubspace.Place23) :
    (cofactorSupportPattern L x v).Nonempty := by
  let b := SubspaceHeights.cofactorVector (rationalRowMatrix x)
  have hrow : LinearIndependent ℚ (rationalRowMatrix x).row := by
    change LinearIndependent ℚ x
    exact hxlin
  have hb0 : b ≠ 0 :=
    SubspaceHeights.cofactorVector_ne_zero_of_linearIndependent_rows hrow
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have hzero (i : Fin (m + 1)) :
      SubspaceHeights.cofactorVector
        (rationalLocalEvaluationRowMatrix L v x) i = 0 := by
    by_contra hi
    have : i ∈ cofactorSupportPattern L x v :=
      mem_cofactorSupportPattern_iff L x v i |>.2 hi
    rw [hempty] at this
    simp at this
  have hdual (i : Fin (m + 1)) :
      dualCoefficientVector L v i ⬝ᵥ b = 0 := by
    have hid := rational_cofactor_localEvaluation_eq_det_mul_dual
      L hL v x i
    rw [hzero i] at hid
    exact (mul_eq_zero.mp hid.symm).resolve_left
      (PadicSubspace.formMatrix_det_ne_zero hL v)
  have hrecon := dual_reconstruction L hL v b
  have : b = 0 := by
    rw [← hrecon]
    simp [hdual]
  exact hb0 this

theorem cofactorNormal_mem_omittedNormalKernel {m : ℕ}
    (L : LocalForms (m + 1))
    (hL : PadicSubspace.IsNonsingularFamily L)
    (x : Fin m → RatVector (m + 1)) :
    SubspaceHeights.cofactorVector (rationalRowMatrix x) ∈
      omittedNormalKernel L (cofactorSupportPattern L x) := by
  rw [mem_omittedNormalKernel_iff]
  intro v i hi
  have hcof : SubspaceHeights.cofactorVector
      (rationalLocalEvaluationRowMatrix L v x) i = 0 := by
    by_contra hne
    exact hi (mem_cofactorSupportPattern_iff L x v i |>.2 hne)
  have hid := rational_cofactor_localEvaluation_eq_det_mul_dual L hL v x i
  rw [hcof] at hid
  exact (mul_eq_zero.mp hid.symm).resolve_left
    (PadicSubspace.formMatrix_det_ne_zero hL v)

/-- Finite-pattern dichotomy for a nonexceptional codimension-one span.
Either one nonzero cofactor at each place has sufficiently large total
exponent, or the corresponding possible-normal space has dimension at
least two and its support-maximizing tuple has total exponent `< -1/4`. -/
theorem selectedCofactor_or_patternKernel_rank_two {m : ℕ}
    (L : LocalForms (m + 1))
    (hL : PadicSubspace.IsNonsingularFamily L)
    (c : HeightBoxes.LocalConstants (m + 1))
    (W : Submodule ℚ (RatVector (m + 1)))
    (hWdim : Module.finrank ℚ W + 1 = m + 1)
    (hWnonexceptional : W ∉ Set.range (exceptionalSpace L))
    (x : Fin m → RatVector (m + 1))
    (hxlin : LinearIndependent ℚ x)
    (hWrow : W = SubspaceHeights.rowSpace (rationalRowMatrix x)) :
    (∃ i : PadicSubspace.Place23 → Fin (m + 1),
      (∀ v, SubspaceHeights.cofactorVector
        (rationalLocalEvaluationRowMatrix L v x) (i v) ≠ 0) ∧
      -(1 / 4 : ℝ) ≤ ∑ v, c v (i v)) ∨
    (∃ i : PadicSubspace.Place23 → Fin (m + 1),
      (∀ v, i v ∈ cofactorSupportPattern L x v) ∧
      (∑ v, c v (i v)) < -(1 / 4 : ℝ) ∧
      2 ≤ Module.finrank ℚ
        (omittedNormalKernel L (cofactorSupportPattern L x))) := by
  classical
  choose i hi himax using fun v ↦ Finset.exists_max_image
    (cofactorSupportPattern L x v) (c v)
      (cofactorSupportPattern_nonempty L hL x hxlin v)
  by_cases hsum : -(1 / 4 : ℝ) ≤ ∑ v, c v (i v)
  · left
    refine ⟨i, ?_, hsum⟩
    intro v
    exact mem_cofactorSupportPattern_iff L x v (i v) |>.1 (hi v)
  · right
    refine ⟨i, hi, lt_of_not_ge hsum, ?_⟩
    let b := SubspaceHeights.cofactorVector (rationalRowMatrix x)
    have hrow : LinearIndependent ℚ (rationalRowMatrix x).row := by
      change LinearIndependent ℚ x
      exact hxlin
    have hb0 : b ≠ 0 :=
      SubspaceHeights.cofactorVector_ne_zero_of_linearIndependent_rows hrow
    have hbmem : b ∈ omittedNormalKernel L (cofactorSupportPattern L x) :=
      cofactorNormal_mem_omittedNormalKernel L hL x
    have hdimpos : 0 < Module.finrank ℚ
        (omittedNormalKernel L (cofactorSupportPattern L x)) := by
      exact Submodule.one_le_finrank_iff.mpr (by
        intro hbot
        rw [hbot] at hbmem
        exact hb0 (by simpa using hbmem))
    have hdimne : Module.finrank ℚ
        (omittedNormalKernel L (cofactorSupportPattern L x)) ≠ 1 := by
      intro hdim
      apply hWnonexceptional
      refine ⟨cofactorSupportPattern L x, ?_⟩
      symm
      apply codimOne_eq_exceptionalSpace_of_patternNormal
        L (cofactorSupportPattern L x) W b hWdim hb0 hbmem hdim
      intro y hy
      rw [hWrow] at hy
      refine Submodule.span_induction
        (p := fun y _ ↦ y ⬝ᵥ b = 0) ?_ ?_ ?_ ?_ hy
      · rintro y ⟨j, rfl⟩
        exact SubspaceHeights.row_dotProduct_cofactorVector
          (rationalRowMatrix x) j
      · simp
      · intro y z _ _ hy hz
        simp [add_dotProduct, hy, hz]
      · intro a y _ hy
        simp [smul_dotProduct, hy]
    omega

/-- Threshold-parametric finite-pattern dichotomy. -/
theorem selectedCofactor_or_patternKernel_rank_two_of_threshold {m : ℕ}
    (L : LocalForms (m + 1))
    (hL : PadicSubspace.IsNonsingularFamily L)
    (c : HeightBoxes.LocalConstants (m + 1))
    (theta : ℝ)
    (W : Submodule ℚ (RatVector (m + 1)))
    (hWdim : Module.finrank ℚ W + 1 = m + 1)
    (hWnonexceptional : W ∉ Set.range (exceptionalSpace L))
    (x : Fin m → RatVector (m + 1))
    (hxlin : LinearIndependent ℚ x)
    (hWrow : W = SubspaceHeights.rowSpace (rationalRowMatrix x)) :
    (∃ i : PadicSubspace.Place23 → Fin (m + 1),
      (∀ v, SubspaceHeights.cofactorVector
        (rationalLocalEvaluationRowMatrix L v x) (i v) ≠ 0) ∧
      -theta ≤ ∑ v, c v (i v)) ∨
    (∃ i : PadicSubspace.Place23 → Fin (m + 1),
      (∀ v, i v ∈ cofactorSupportPattern L x v) ∧
      (∀ v j, j ∈ cofactorSupportPattern L x v →
        c v j ≤ c v (i v)) ∧
      (∑ v, c v (i v)) < -theta ∧
      2 ≤ Module.finrank ℚ
        (omittedNormalKernel L (cofactorSupportPattern L x))) := by
  classical
  choose i hi himax using fun v ↦ Finset.exists_max_image
    (cofactorSupportPattern L x v) (c v)
      (cofactorSupportPattern_nonempty L hL x hxlin v)
  by_cases hsum : -theta ≤ ∑ v, c v (i v)
  · left
    refine ⟨i, ?_, hsum⟩
    intro v
    exact mem_cofactorSupportPattern_iff L x v (i v) |>.1 (hi v)
  · right
    refine ⟨i, hi, himax, lt_of_not_ge hsum, ?_⟩
    let b := SubspaceHeights.cofactorVector (rationalRowMatrix x)
    have hrow : LinearIndependent ℚ (rationalRowMatrix x).row := by
      change LinearIndependent ℚ x
      exact hxlin
    have hb0 : b ≠ 0 :=
      SubspaceHeights.cofactorVector_ne_zero_of_linearIndependent_rows hrow
    have hbmem : b ∈ omittedNormalKernel L (cofactorSupportPattern L x) :=
      cofactorNormal_mem_omittedNormalKernel L hL x
    have hdimpos : 0 < Module.finrank ℚ
        (omittedNormalKernel L (cofactorSupportPattern L x)) := by
      exact Submodule.one_le_finrank_iff.mpr (by
        intro hbot
        rw [hbot] at hbmem
        exact hb0 (by simpa using hbmem))
    have hdimne : Module.finrank ℚ
        (omittedNormalKernel L (cofactorSupportPattern L x)) ≠ 1 := by
      intro hdim
      apply hWnonexceptional
      refine ⟨cofactorSupportPattern L x, ?_⟩
      symm
      apply codimOne_eq_exceptionalSpace_of_patternNormal
        L (cofactorSupportPattern L x) W b hWdim hb0 hbmem hdim
      intro y hy
      rw [hWrow] at hy
      refine Submodule.span_induction
        (p := fun y _ ↦ y ⬝ᵥ b = 0) ?_ ?_ ?_ ?_ hy
      · rintro y ⟨j, rfl⟩
        exact SubspaceHeights.row_dotProduct_cofactorVector
          (rationalRowMatrix x) j
      · simp
      · intro y z _ _ hy hz
        simp [add_dotProduct, hy, hz]
      · intro a y _ hy
        simp [smul_dotProduct, hy]
    omega

/-- Expansion of the pairing with a possible normal using only the active
dual coordinates of a support pattern. -/
theorem dotProduct_eq_sum_support {n : ℕ}
    (L : LocalForms n) (hL : PadicSubspace.IsNonsingularFamily L)
    (I : LocalSupportPattern n) {w : RatVector n}
    (hw : w ∈ omittedNormalKernel L I)
    (v : PadicSubspace.Place23) (y : RatVector n) :
    y ⬝ᵥ w = ∑ j ∈ I v,
      (dualCoefficientVector L v j ⬝ᵥ w) * L v j y := by
  classical
  have hrecon := dual_reconstruction L hL v w
  have hall : y ⬝ᵥ w = ∑ j,
      (dualCoefficientVector L v j ⬝ᵥ w) * L v j y := by
    calc
      y ⬝ᵥ w = y ⬝ᵥ (∑ j,
          (dualCoefficientVector L v j ⬝ᵥ w) •
            PadicSubspace.coefficientVector (L v j)) :=
        congrArg (fun u ↦ y ⬝ᵥ u) hrecon.symm
      _ = ∑ j, (dualCoefficientVector L v j ⬝ᵥ w) * L v j y := by
        rw [dotProduct_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [dotProduct_smul]
        simp only [smul_eq_mul]
        rw [dotProduct_comm y, PadicSubspace.linearForm_eq_dotProduct]
        rfl
  rw [hall]
  symm
  apply Finset.sum_subset (Finset.subset_univ (I v))
  intro j _hj hjI
  have hz := (mem_omittedNormalKernel_iff L I w).1 hw v j hjI
  simp [hz]

/-- One-place upper bound for pairing a box point with a possible normal.
The selected support index is assumed to maximize the local exponent. -/
theorem realPlaceNorm_dotProduct_le_supportRadius {n : ℕ}
    (L : LocalForms n) (hL : PadicSubspace.IsNonsingularFamily L)
    (I : LocalSupportPattern n) {w : RatVector n}
    (hw : w ∈ omittedNormalKernel L I)
    (Q : ℝ) (hQ : 1 ≤ Q) (c : HeightBoxes.LocalConstants n)
    {y : RatVector n}
    (hy : HeightBoxes.InApproximationBox L Q c y)
    (v : PadicSubspace.Place23) (i : Fin n) (hi : i ∈ I v)
    (himax : ∀ j ∈ I v, c v j ≤ c v i) :
    HeightBoxes.realPlaceNorm v (y ⬝ᵥ w) ≤
      (∑ j ∈ I v,
        HeightBoxes.realPlaceNorm v (dualCoefficientVector L v j ⬝ᵥ w)) *
          HeightBoxes.exponentRadius Q c v i := by
  classical
  let abv : AbsoluteValue ℚ ℚ :=
    IsAbsoluteValue.toAbsoluteValue (PadicSubspace.placeNorm v)
  have hsumQ : PadicSubspace.placeNorm v (y ⬝ᵥ w) ≤
      ∑ j ∈ I v, PadicSubspace.placeNorm v
        ((dualCoefficientVector L v j ⬝ᵥ w) * L v j y) := by
    rw [dotProduct_eq_sum_support L hL I hw v y]
    exact abv.sum_le (I v)
      (fun j ↦ (dualCoefficientVector L v j ⬝ᵥ w) * L v j y)
  have hsumR : HeightBoxes.realPlaceNorm v (y ⬝ᵥ w) ≤
      ∑ j ∈ I v, HeightBoxes.realPlaceNorm v
        ((dualCoefficientVector L v j ⬝ᵥ w) * L v j y) := by
    change ((PadicSubspace.placeNorm v (y ⬝ᵥ w) : ℚ) : ℝ) ≤
      ∑ j ∈ I v, ((PadicSubspace.placeNorm v
        ((dualCoefficientVector L v j ⬝ᵥ w) * L v j y) : ℚ) : ℝ)
    rw [← Rat.cast_sum]
    exact Rat.cast_le.mpr hsumQ
  calc
    HeightBoxes.realPlaceNorm v (y ⬝ᵥ w) ≤
        ∑ j ∈ I v, HeightBoxes.realPlaceNorm v
          ((dualCoefficientVector L v j ⬝ᵥ w) * L v j y) := hsumR
    _ = ∑ j ∈ I v,
        HeightBoxes.realPlaceNorm v (dualCoefficientVector L v j ⬝ᵥ w) *
          HeightBoxes.realPlaceNorm v (L v j y) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [realPlaceNorm_mul]
    _ ≤ ∑ j ∈ I v,
        HeightBoxes.realPlaceNorm v (dualCoefficientVector L v j ⬝ᵥ w) *
          HeightBoxes.exponentRadius Q c v i := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _
        (HeightBoxes.realPlaceNorm_nonneg _ _)
      exact (hy v j).trans
        (Real.rpow_le_rpow_of_exponent_le hQ (himax j hj))
    _ = (∑ j ∈ I v,
        HeightBoxes.realPlaceNorm v (dualCoefficientVector L v j ⬝ᵥ w)) *
          HeightBoxes.exponentRadius Q c v i := by
      rw [Finset.sum_mul]

/-- Pairing a `ℤ[1/6]` point with an integral vector again gives an
`S`-integer. -/
theorem dotProduct_isSInteger {n : ℕ} {y : RatVector n}
    (hy : AdelicMinkowski.InZOneSix y) (z : IntVector n) :
    SIntegerSix.IsSInteger (y ⬝ᵥ PadicSubspace.intCastVec z) := by
  classical
  apply SIntegerSix.sum
  intro j
  exact SIntegerSix.mul
    (SIntegerSix.of_inZOneSix_coordinate hy j)
    (SIntegerSix.intCast (z j))

/-- Product of the three one-place support bounds.  This is the quantitative
estimate used to eliminate the rank-at-least-two support-kernel branch in
the repaired Lemma 4.22. -/
theorem prod_realPlaceNorm_dotProduct_le_supportRadius {n : ℕ}
    (L : LocalForms n) (hL : PadicSubspace.IsNonsingularFamily L)
    (I : LocalSupportPattern n) {w : RatVector n}
    (hw : w ∈ omittedNormalKernel L I)
    (Q : ℝ) (hQ : 1 ≤ Q) (c : HeightBoxes.LocalConstants n)
    {y : RatVector n}
    (hy : HeightBoxes.InApproximationBox L Q c y)
    (i : PadicSubspace.Place23 → Fin n)
    (hi : ∀ v, i v ∈ I v)
    (himax : ∀ v j, j ∈ I v → c v j ≤ c v (i v)) :
    (∏ v, HeightBoxes.realPlaceNorm v (y ⬝ᵥ w)) ≤
      (∏ v, ∑ j ∈ I v,
        HeightBoxes.realPlaceNorm v (dualCoefficientVector L v j ⬝ᵥ w)) *
        Q ^ (∑ v, c v (i v)) := by
  classical
  calc
    (∏ v, HeightBoxes.realPlaceNorm v (y ⬝ᵥ w)) ≤
        ∏ v, ((∑ j ∈ I v,
          HeightBoxes.realPlaceNorm v
            (dualCoefficientVector L v j ⬝ᵥ w)) *
            HeightBoxes.exponentRadius Q c v (i v)) := by
      apply Finset.prod_le_prod
      · intro v _
        exact HeightBoxes.realPlaceNorm_nonneg _ _
      · intro v _
        exact realPlaceNorm_dotProduct_le_supportRadius
          L hL I hw Q hQ c hy v (i v) (hi v) (himax v)
    _ = (∏ v, ∑ j ∈ I v,
          HeightBoxes.realPlaceNorm v
            (dualCoefficientVector L v j ⬝ᵥ w)) *
        (∏ v, HeightBoxes.exponentRadius Q c v (i v)) := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ v, ∑ j ∈ I v,
          HeightBoxes.realPlaceNorm v
            (dualCoefficientVector L v j ⬝ᵥ w)) *
        Q ^ (∑ v, c v (i v)) := by
      congr 1
      simp only [HeightBoxes.exponentRadius]
      exact (Real.rpow_sum_of_pos (zero_lt_one.trans_le hQ)
        (fun v ↦ c v (i v)) Finset.univ).symm

/-- If the active exponent sum of a support pattern is negative, every
fixed integral possible normal annihilates every sufficiently large
`ℤ[1/6]` approximation box.  The cutoff may depend on the normal, which is
enough because a possible-normal space has a finite basis. -/
theorem eventually_dotProduct_eq_zero_of_pattern {n : ℕ}
    (L : LocalForms n) (hL : PadicSubspace.IsNonsingularFamily L)
    (I : LocalSupportPattern n) (c : HeightBoxes.LocalConstants n)
    (i : PadicSubspace.Place23 → Fin n)
    (hi : ∀ v, i v ∈ I v)
    (himax : ∀ v j, j ∈ I v → c v j ≤ c v (i v))
    (hsum : (∑ v, c v (i v)) < 0)
    (z : IntVector n)
    (hz : PadicSubspace.intCastVec z ∈ omittedNormalKernel L I) :
    ∀ᶠ Q : ℕ in Filter.atTop, ∀ y ∈
      realSIntegralApproximationDomain L Q c,
      y ⬝ᵥ PadicSubspace.intCastVec z = 0 := by
  classical
  let C : ℝ := ∏ v, ∑ j ∈ I v,
    HeightBoxes.realPlaceNorm v
      (dualCoefficientVector L v j ⬝ᵥ PadicSubspace.intCastVec z)
  have hdecay : Filter.Tendsto
      (fun Q : ℕ ↦ C * (Q : ℝ) ^ (∑ v, c v (i v)))
      Filter.atTop (nhds 0) := by
    have hneg : 0 < -(∑ v, c v (i v)) := neg_pos.mpr hsum
    convert ((tendsto_rpow_neg_atTop hneg).comp
      tendsto_natCast_atTop_atTop).const_mul C using 1 <;>
      simp only [Function.comp_apply, neg_neg, mul_zero]
  have hsmall : ∀ᶠ Q : ℕ in Filter.atTop,
      C * (Q : ℝ) ^ (∑ v, c v (i v)) < 1 :=
    hdecay.eventually (Iio_mem_nhds zero_lt_one)
  filter_upwards [hsmall, Filter.eventually_ge_atTop 1] with Q hsmallQ hQ
  intro y hy
  by_contra hdot
  have hS := dotProduct_isSInteger hy.1 z
  have hlower : (1 : ℝ) ≤
      ∏ v, HeightBoxes.realPlaceNorm v
        (y ⬝ᵥ PadicSubspace.intCastVec z) := by
    rw [prod_realPlaceNorm_eq_normProduct23]
    exact_mod_cast SIntegerSix.one_le_normProduct23 hS hdot
  have hupper := prod_realPlaceNorm_dotProduct_le_supportRadius
    L hL I hz (Q : ℝ) (by exact_mod_cast hQ) c hy.2 i hi himax
  exact (not_lt_of_ge (hlower.trans hupper)) hsmallQ

/-- The whole sufficiently large approximation span is orthogonal to a
negative-sum possible-normal space.  A finite basis makes the individual
normal-dependent cutoffs uniform. -/
theorem eventually_realSApproximationSpan_le_orthogonal_pattern {n : ℕ}
    (L : LocalForms n) (hL : PadicSubspace.IsNonsingularFamily L)
    (I : LocalSupportPattern n) (c : HeightBoxes.LocalConstants n)
    (i : PadicSubspace.Place23 → Fin n)
    (hi : ∀ v, i v ∈ I v)
    (himax : ∀ v j, j ∈ I v → c v j ≤ c v (i v))
    (hsum : (∑ v, c v (i v)) < 0) :
    ∀ᶠ Q : ℕ in Filter.atTop,
      realSApproximationSpan L Q c ≤
        SubspaceHeights.orthogonal (omittedNormalKernel L I) := by
  classical
  let K := omittedNormalKernel L I
  let B : Module.Basis (Fin (Module.finrank ℚ K)) ℚ K :=
    Module.finBasis ℚ K
  let z : Fin (Module.finrank ℚ K) → IntVector n := fun a ↦
    Primitive.normalize (((B a : K) : RatVector n))
  have hb0 (a : Fin (Module.finrank ℚ K)) :
      (((B a : K) : RatVector n)) ≠ 0 := by
    intro h
    apply B.ne_zero a
    apply Subtype.ext
    exact h
  have hzmem (a : Fin (Module.finrank ℚ K)) :
      PadicSubspace.intCastVec (z a) ∈ K := by
    change Primitive.intCastVec (z a) ∈ K
    have hbmem : ((B a : K) : RatVector n) ∈ K := (B a).property
    have heq := Primitive.eq_normalizationScale_smul
      (((B a : K) : RatVector n))
    rw [heq] at hbmem
    have hscaled := K.smul_mem
      (Primitive.normalizationScale (((B a : K) : RatVector n)))⁻¹ hbmem
    simpa only [smul_smul, inv_mul_cancel₀
      (Primitive.normalizationScale_ne_zero (hb0 a)), one_smul, z] using hscaled
  have hone (a : Fin (Module.finrank ℚ K)) :
      ∀ᶠ Q : ℕ in Filter.atTop, ∀ y ∈
        realSIntegralApproximationDomain L Q c,
        y ⬝ᵥ PadicSubspace.intCastVec (z a) = 0 := by
    exact eventually_dotProduct_eq_zero_of_pattern
      L hL I c i hi himax hsum (z a) (hzmem a)
  have hall : ∀ᶠ Q : ℕ in Filter.atTop,
      ∀ a : Fin (Module.finrank ℚ K), ∀ y ∈
        realSIntegralApproximationDomain L Q c,
        y ⬝ᵥ PadicSubspace.intCastVec (z a) = 0 := by
    rw [Filter.eventually_all]
    exact hone
  filter_upwards [hall] with Q hQ
  rw [realSApproximationSpan]
  apply Submodule.span_le.mpr
  intro y hy
  change y ∈ SubspaceHeights.orthogonal K
  rw [SubspaceHeights.mem_orthogonal_iff]
  intro w hw
  let F : K →ₗ[ℚ] ℚ :=
    ((SubspaceHeights.dotBilin n).flip y).comp K.subtype
  have hF : F = 0 := by
    apply B.ext
    intro a
    change (((B a : K) : RatVector n)) ⬝ᵥ y = 0
    rw [Primitive.eq_normalizationScale_smul
      (((B a : K) : RatVector n))]
    rw [smul_dotProduct]
    rw [dotProduct_comm]
    change Primitive.normalizationScale (((B a : K) : RatVector n)) •
      (y ⬝ᵥ PadicSubspace.intCastVec (z a)) = 0
    rw [hQ a y hy, smul_zero]
  have hwF := LinearMap.congr_fun hF ⟨w, hw⟩
  change w ⬝ᵥ y = 0 at hwF
  exact hwF

/-- Uniform finite-pattern form of the exceptional-branch exclusion.  At a
sufficiently large scale a codimension-one approximation span cannot have a
negative active exponent sum and a possible-normal space of rank at least
two. -/
theorem eventually_no_rankTwo_negative_pattern {n : ℕ}
    (L : LocalForms n) (hL : PadicSubspace.IsNonsingularFamily L)
    (c : HeightBoxes.LocalConstants n) :
    ∀ᶠ Q : ℕ in Filter.atTop,
      ∀ I : LocalSupportPattern n,
      ∀ i : PadicSubspace.Place23 → Fin n,
      (∀ v, i v ∈ I v) →
      (∀ v j, j ∈ I v → c v j ≤ c v (i v)) →
      (∑ v, c v (i v)) < 0 →
      2 ≤ Module.finrank ℚ (omittedNormalKernel L I) →
      Module.finrank ℚ (realSApproximationSpan L Q c) + 1 ≠ n := by
  classical
  have hone (I : LocalSupportPattern n)
      (i : PadicSubspace.Place23 → Fin n) :
      ∀ᶠ Q : ℕ in Filter.atTop,
        (∀ v, i v ∈ I v) →
        (∀ v j, j ∈ I v → c v j ≤ c v (i v)) →
        (∑ v, c v (i v)) < 0 →
        realSApproximationSpan L Q c ≤
          SubspaceHeights.orthogonal (omittedNormalKernel L I) := by
    by_cases hi : ∀ v, i v ∈ I v
    · by_cases himax : ∀ v j, j ∈ I v → c v j ≤ c v (i v)
      · by_cases hsum : (∑ v, c v (i v)) < 0
        · filter_upwards
            [eventually_realSApproximationSpan_le_orthogonal_pattern
              L hL I c i hi himax hsum] with Q hQ
          intro _ _ _
          exact hQ
        · exact Filter.Eventually.of_forall fun _ _ _ hs ↦ (hsum hs).elim
      · exact Filter.Eventually.of_forall fun _ _ hm ↦ (himax hm).elim
    · exact Filter.Eventually.of_forall fun _ h ↦ (hi h).elim
  have hall : ∀ᶠ Q : ℕ in Filter.atTop,
      ∀ I : LocalSupportPattern n,
      ∀ i : PadicSubspace.Place23 → Fin n,
        (∀ v, i v ∈ I v) →
        (∀ v j, j ∈ I v → c v j ≤ c v (i v)) →
        (∑ v, c v (i v)) < 0 →
        realSApproximationSpan L Q c ≤
          SubspaceHeights.orthogonal (omittedNormalKernel L I) := by
    rw [Filter.eventually_all]
    intro I
    rw [Filter.eventually_all]
    exact hone I
  filter_upwards [hall] with Q hQ
  intro I i hi himax hsum hrank hcodim
  have hmono : Module.finrank ℚ (realSApproximationSpan L Q c) ≤
      Module.finrank ℚ
        (SubspaceHeights.orthogonal (omittedNormalKernel L I)) :=
    Submodule.finrank_mono (hQ I i hi himax hsum)
  rw [SubspaceHeights.finrank_orthogonal] at hmono
  have hamb : Module.finrank ℚ (omittedNormalKernel L I) ≤ n := by
    simpa only [Module.finrank_fin_fun] using
      Submodule.finrank_le (omittedNormalKernel L I)
  have horth : n - Module.finrank ℚ (omittedNormalKernel L I) ≤ n - 2 := by
    exact Nat.sub_le_sub_left hrank n
  have hspan : Module.finrank ℚ (realSApproximationSpan L Q c) ≤ n - 2 :=
    hmono.trans horth
  omega

/-- Repaired Lemma 4.22 over `ℤ[1/6]`: after discarding the finite support
pattern family, every sufficiently large codimension-one approximation span
has an integral primitive normal whose height grows with positive slope.
The selected local indices are retained so later quantitative consumers can
use the exact (rather than a maximized) constant. -/
theorem exists_sCodimOne_normalHeight_cutoff_of_delta {m : ℕ}
    (L : LocalForms (m + 1))
    (hL : PadicSubspace.IsNonsingularFamily L)
    (c : HeightBoxes.LocalConstants (m + 1))
    {delta : ℝ} (hdelta : 0 < delta)
    (htotal : (∑ v, ∑ j, c v j) ≤ -delta) :
    ∃ Q₀ : ℕ, ∀ W : sCodimOneApproximationSpaces L c,
      Q₀ ≤ sCodimOneScale W →
      W.1 ∉ Set.range (exceptionalSpace L) →
      ∃ z : IntVector (m + 1),
      ∃ i : PadicSubspace.Place23 → Fin (m + 1),
        z ≠ 0 ∧
        Primitive.IsPrimitive z ∧
        (∀ y ∈ W.1, y ⬝ᵥ PadicSubspace.intCastVec z = 0) ∧
        (delta - delta / 2) * Real.log (sCodimOneScale W : ℝ) +
            Real.log (PadicSubspace.realFormDetProduct L) -
            (∑ v, (Real.log (m + 1) +
              ∑ k, Height.logHeight₁
                (dualCoefficientVector L v (i v) k))) -
            3 * Real.log (Nat.factorial m : ℝ) ≤
          3 * (m + 1) *
            Real.log (PadicSubspace.boxHeight z : ℝ) := by
  classical
  have hno := eventually_no_rankTwo_negative_pattern L hL c
  rw [Filter.eventually_atTop] at hno
  obtain ⟨Q₀, hQ₀⟩ := hno
  refine ⟨Q₀, ?_⟩
  intro W hWlarge hWnonexceptional
  obtain ⟨x, hxmem, hxlin, hWrow, hb0, hnormal⟩ :=
    exists_sIntegral_basis_cofactor_normal W
  have hdich := selectedCofactor_or_patternKernel_rank_two_of_threshold
    L hL c (delta / 2) W.1 (sCodimOne_finrank_add_one W)
      hWnonexceptional x hxlin hWrow
  rcases hdich with hselected | hkernel
  · obtain ⟨i, hcof, hselected⟩ := hselected
    let b := SubspaceHeights.cofactorVector (rationalRowMatrix x)
    let z : IntVector (m + 1) := Primitive.normalize b
    have hz0 : z ≠ 0 := Primitive.normalize_ne_zero hb0
    have hzprim : Primitive.IsPrimitive z := Primitive.normalize_primitive hb0
    have horth : ∀ y ∈ W.1,
        y ⬝ᵥ PadicSubspace.intCastVec z = 0 := by
      intro y hy
      have hyb := hnormal y hy
      have heq := Primitive.eq_normalizationScale_smul b
      change y ⬝ᵥ b = 0 at hyb
      rw [heq, dotProduct_smul] at hyb
      change Primitive.normalizationScale b *
        (y ⬝ᵥ PadicSubspace.intCastVec z) = 0 at hyb
      exact (mul_eq_zero.mp hyb).resolve_left
        (Primitive.normalizationScale_ne_zero hb0)
    have hQreal : (1 : ℝ) < sCodimOneScale W := by
      exact_mod_cast sCodimOneScale_ge_two W
    have hgap := selectedCofactor_normalHeight_gap_of_delta
      L hL (sCodimOneScale W : ℝ) hQreal c x hxlin
      (fun h ↦ (hxmem h).1) (fun h v j ↦ (hxmem h).2 v j)
      i hcof htotal hselected
    exact ⟨z, i, hz0, hzprim, horth, by simpa only [z, b] using hgap⟩
  · obtain ⟨i, hi, himax, hsum, hrank⟩ := hkernel
    have hsum0 : (∑ v, c v (i v)) < 0 := by
      linarith
    have hdim : Module.finrank ℚ
        (realSApproximationSpan L (sCodimOneScale W) c) + 1 = m + 1 := by
      rw [← sCodimOne_eq_span_scale W]
      exact sCodimOne_finrank_add_one W
    exact (hQ₀ (sCodimOneScale W) hWlarge
      (cofactorSupportPattern L x) i hi himax hsum0 hrank
      hdim).elim

/-- Uniform form-height version of the repaired Lemma 4.22.  The finitely
many possible selected local indices are absorbed into one enlarged cutoff,
leaving a positive height slope independent of that selection. -/
theorem exists_sCodimOne_primitiveNormal_formHeight_ge {m : ℕ}
    (L : LocalForms (m + 1))
    (hL : PadicSubspace.IsNonsingularFamily L)
    (c : HeightBoxes.LocalConstants (m + 1))
    {delta : ℝ} (hdelta : 0 < delta)
    (htotal : (∑ v, ∑ j, c v j) ≤ -delta) :
    ∃ Q₀ : ℕ, ∀ W : sCodimOneApproximationSpaces L c,
      Q₀ ≤ sCodimOneScale W →
      W.1 ∉ Set.range (exceptionalSpace L) →
      ∃ z : IntVector (m + 1),
        z ≠ 0 ∧
        Primitive.IsPrimitive z ∧
        (∀ y ∈ W.1, y ⬝ᵥ PadicSubspace.intCastVec z = 0) ∧
        delta / (12 * (m + 1)) *
            Real.log (sCodimOneScale W : ℝ) ≤
          GeneralizedRoth.formHeight (primitiveNormalForm z) := by
  classical
  let offset : (PadicSubspace.Place23 → Fin (m + 1)) → ℝ := fun i ↦
    Real.log (PadicSubspace.realFormDetProduct L) -
      (∑ v, (Real.log (m + 1) +
        ∑ k, Height.logHeight₁ (dualCoefficientVector L v (i v) k))) -
      3 * Real.log (Nat.factorial m : ℝ)
  let K : ℝ := ∑ i : PadicSubspace.Place23 → Fin (m + 1), |offset i|
  have hlogTendsto : Filter.Tendsto
      (fun Q : ℕ ↦ Real.log (Q : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hscaledTendsto : Filter.Tendsto
      (fun Q : ℕ ↦ (delta / 4) * Real.log (Q : ℝ))
      Filter.atTop Filter.atTop :=
    hlogTendsto.const_mul_atTop (div_pos hdelta (by norm_num))
  have hlargeEventually : ∀ᶠ Q : ℕ in Filter.atTop,
      K < (delta / 4) * Real.log (Q : ℝ) :=
    hscaledTendsto.eventually_gt_atTop K
  rw [Filter.eventually_atTop] at hlargeEventually
  obtain ⟨Q₁, hQ₁⟩ := hlargeEventually
  obtain ⟨Q₂, hQ₂⟩ :=
    exists_sCodimOne_normalHeight_cutoff_of_delta L hL c hdelta htotal
  refine ⟨max Q₁ Q₂, ?_⟩
  intro W hWlarge hWnonexceptional
  obtain ⟨z, i, hz0, hzprim, horth, hgap⟩ :=
    hQ₂ W ((le_max_right Q₁ Q₂).trans hWlarge) hWnonexceptional
  refine ⟨z, hz0, hzprim, horth, ?_⟩
  have hK : K ≤ (delta / 4) *
      Real.log (sCodimOneScale W : ℝ) :=
    (hQ₁ _ ((le_max_left Q₁ Q₂).trans hWlarge)).le
  have hiK : |offset i| ≤ K := by
    exact Finset.single_le_sum (fun j _ ↦ abs_nonneg (offset j))
      (Finset.mem_univ i)
  have hoffset : -K ≤ offset i :=
    (neg_le_neg hiK).trans (neg_abs_le (offset i))
  have hquarter : (delta / 4) *
      Real.log (sCodimOneScale W : ℝ) ≤
      3 * (m + 1) *
        Real.log (PadicSubspace.boxHeight z : ℝ) := by
    dsimp only [offset] at hoffset
    nlinarith
  rw [formHeight_primitiveNormalForm_eq_log_boxHeight hzprim]
  have hden : (0 : ℝ) < 3 * (m + 1) := by positivity
  have hdiv : ((delta / 4) *
      Real.log (sCodimOneScale W : ℝ)) / (3 * (m + 1)) ≤
      Real.log (PadicSubspace.boxHeight z : ℝ) :=
    (div_le_iff₀ hden).2 (by
      calc
        (delta / 4) * Real.log (sCodimOneScale W : ℝ) ≤
            3 * (m + 1) *
              Real.log (PadicSubspace.boxHeight z : ℝ) := hquarter
        _ = Real.log (PadicSubspace.boxHeight z : ℝ) *
            (3 * (m + 1)) := by ring)
  convert hdiv using 1 <;> field_simp <;> ring

@[simp] theorem integralRowMatrix_row {m n : ℕ}
    (x : Fin m → IntVector n) (i : Fin m) :
    (integralRowMatrix x).row i = PadicSubspace.intCastVec (x i) :=
  rfl

/-- The rectangular matrix of local-form values on a family of integral
points (points index rows and local forms index columns). -/
def localEvaluationRowMatrix {m n : ℕ} (L : LocalForms n)
    (v : PadicSubspace.Place23) (x : Fin m → IntVector n) :
    Matrix (Fin m) (Fin n) ℚ :=
  fun h i ↦ L v i (PadicSubspace.intCastVec (x h))

/-- Changing from standard coordinates to the local form coordinates is
right multiplication by the transpose of the local coefficient matrix. -/
theorem localEvaluationRowMatrix_eq_mul {m n : ℕ} (L : LocalForms n)
    (v : PadicSubspace.Place23) (x : Fin m → IntVector n) :
    localEvaluationRowMatrix L v x =
      integralRowMatrix x * (PadicSubspace.formMatrix L v)ᵀ := by
  ext h i
  change L v i (PadicSubspace.intCastVec (x h)) =
    ∑ j, (x h j : ℚ) * L v i (Pi.single j 1)
  rw [PadicSubspace.linearForm_eq_sum_coeff]
  apply Finset.sum_congr rfl
  intro j _
  rw [PadicSubspace.intCastVec_apply]
  ring

/-- The bordered cofactor matrix is compatible with the local coordinate
change.  Its first row is exactly the dual-basis identity row. -/
theorem bordered_localEvaluation_eq_mul {m : ℕ} (L : LocalForms (m + 1))
    (hL : PadicSubspace.IsNonsingularFamily L)
    (v : PadicSubspace.Place23) (x : Fin m → IntVector (m + 1))
    (i : Fin (m + 1)) :
    SubspaceHeights.borderedMatrix (integralRowMatrix x)
        (dualCoefficientVector L v i) *
        (PadicSubspace.formMatrix L v)ᵀ =
      SubspaceHeights.borderedMatrix (localEvaluationRowMatrix L v x)
        (Pi.single i (1 : ℚ) : RatVector (m + 1)) := by
  ext r k
  cases r using Fin.cases with
  | zero =>
      change Matrix.vecMul (dualCoefficientVector L v i)
        (PadicSubspace.formMatrix L v)ᵀ k =
          (Pi.single i (1 : ℚ) : RatVector (m + 1)) k
      exact congrFun (dualCoefficientVector_vecMul_transpose L hL v i) k
  | succ h =>
      change (integralRowMatrix x * (PadicSubspace.formMatrix L v)ᵀ) h k =
        localEvaluationRowMatrix L v x h k
      exact congrArg (fun M ↦ M h k)
        (localEvaluationRowMatrix_eq_mul L v x).symm

/-- Exact local-minor identity.  The `i`-th cofactor of the matrix of local
form values equals the determinant of the local form basis times the `i`-th
dual coordinate of the standard cofactor normal. -/
theorem cofactor_localEvaluation_eq_det_mul_dual {m : ℕ}
    (L : LocalForms (m + 1))
    (hL : PadicSubspace.IsNonsingularFamily L)
    (v : PadicSubspace.Place23) (x : Fin m → IntVector (m + 1))
    (i : Fin (m + 1)) :
    SubspaceHeights.cofactorVector (localEvaluationRowMatrix L v x) i =
      (PadicSubspace.formMatrix L v).det *
        (dualCoefficientVector L v i ⬝ᵥ
          SubspaceHeights.cofactorVector (integralRowMatrix x)) := by
  classical
  let X := integralRowMatrix x
  let E := localEvaluationRowMatrix L v x
  let A := PadicSubspace.formMatrix L v
  calc
    SubspaceHeights.cofactorVector E i =
        Pi.single i 1 ⬝ᵥ SubspaceHeights.cofactorVector E := by
      simp [dotProduct, Pi.single_apply]
    _ = (SubspaceHeights.borderedMatrix E (Pi.single i 1)).det :=
      SubspaceHeights.dotProduct_cofactorVector E (Pi.single i 1)
    _ = (SubspaceHeights.borderedMatrix X
        (dualCoefficientVector L v i) * Aᵀ).det := by
      congr 1
      exact (bordered_localEvaluation_eq_mul L hL v x i).symm
    _ = (SubspaceHeights.borderedMatrix X
        (dualCoefficientVector L v i)).det * (Aᵀ).det := by
      rw [Matrix.det_mul]
    _ = (dualCoefficientVector L v i ⬝ᵥ
        SubspaceHeights.cofactorVector X) * A.det := by
      rw [Matrix.det_transpose]
      rw [SubspaceHeights.dotProduct_cofactorVector]
    _ = A.det * (dualCoefficientVector L v i ⬝ᵥ
        SubspaceHeights.cofactorVector X) := by ring

/-- The local Hadamard/Leibniz bound for an omitted-form cofactor.  Notice
that the product contains precisely the `m` radii other than `i`. -/
theorem realPlaceNorm_cofactor_localEvaluation_le {m : ℕ}
    (L : LocalForms (m + 1)) (Q : ℝ)
    (c : HeightBoxes.LocalConstants (m + 1))
    (x : Fin m → IntVector (m + 1))
    (hQ : 0 ≤ Q)
    (hx : ∀ h v i,
      HeightBoxes.realPlaceNorm v
          (L v i (PadicSubspace.intCastVec (x h))) ≤
        HeightBoxes.exponentRadius Q c v i)
    (v : PadicSubspace.Place23) (i : Fin (m + 1)) :
    HeightBoxes.realPlaceNorm v
        (SubspaceHeights.cofactorVector
          (localEvaluationRowMatrix L v x) i) ≤
      (Nat.factorial m : ℝ) *
        ∏ k : Fin m, HeightBoxes.exponentRadius Q c v (i.succAbove k) := by
  classical
  let E := localEvaluationRowMatrix L v x
  let M : Matrix (Fin m) (Fin m) ℚ := (E.submatrix id i.succAbove)ᵀ
  have hsign : PadicSubspace.placeNorm v
      ((-1 : ℚ) ^ (i : ℕ)) = 1 := by
    fin_cases v <;> simp [PadicSubspace.placeNorm]
  have hcof : HeightBoxes.realPlaceNorm v
      (SubspaceHeights.cofactorVector E i) =
      (PadicSubspace.placeNorm v M.det : ℝ) := by
    unfold HeightBoxes.realPlaceNorm M
    rw [SubspaceHeights.cofactorVector_apply,
      PadicSubspace.placeNorm_mul, hsign, one_mul, Matrix.det_transpose]
  rw [hcof]
  apply PadicSubspace.real_placeNorm_det_le_rowProduct v M
    (fun k ↦ HeightBoxes.exponentRadius Q c v (i.succAbove k))
  · intro k
    exact Real.rpow_nonneg hQ _
  · intro k h
    change (PadicSubspace.placeNorm v
      (L v (i.succAbove k) (PadicSubspace.intCastVec (x h))) : ℝ) ≤
        HeightBoxes.exponentRadius Q c v (i.succAbove k)
    exact hx h v (i.succAbove k)

/-- A codimension-one approximation span in ambient dimension `m+1` has an
integral basis drawn from its defining box.  Its cofactor vector is a
nonzero defining form for the span.  This is the exact algebraic input for
the local-minor estimates in Lemma 4.22. -/
theorem exists_integral_basis_cofactor_normal {m : ℕ}
    {L : LocalForms (m + 1)} {c : HeightBoxes.LocalConstants (m + 1)}
    (W : codimOneApproximationSpaces L c) :
    ∃ x : Fin m → IntVector (m + 1),
      (∀ i, x i ∈ realIntegralApproximationDomain L (codimOneScale W) c) ∧
      LinearIndependent ℚ (fun i ↦ PadicSubspace.intCastVec (x i)) ∧
      W.1 = SubspaceHeights.rowSpace (integralRowMatrix x) ∧
      SubspaceHeights.cofactorVector (integralRowMatrix x) ≠ 0 ∧
      (∀ y ∈ W.1,
        y ⬝ᵥ SubspaceHeights.cofactorVector (integralRowMatrix x) = 0) := by
  classical
  let D : Set (RatVector (m + 1)) :=
    PadicSubspace.intCastVec ''
      realIntegralApproximationDomain L (codimOneScale W) c
  have hW : W.1 = Submodule.span ℚ D := by
    simpa [D, realApproximationSpan] using codimOne_eq_span_scale W
  have hdimW : Module.finrank ℚ W.1 = m := by
    have h := codimOne_finrank_add_one W
    omega
  have hrankD : PadicSubspace.rationalSetRank D = m := by
    change Module.finrank ℚ (Submodule.span ℚ D) = m
    rw [← hW, hdimW]
  obtain ⟨f₀, hfi₀, hfD₀⟩ :=
    PadicSubspace.exists_independent_family_card_rationalSetRank D
  let e : Fin m → Fin (PadicSubspace.rationalSetRank D) :=
    Fin.cast hrankD.symm
  let f : Fin m → RatVector (m + 1) := f₀ ∘ e
  have hfi : LinearIndependent ℚ f :=
    hfi₀.comp e (Fin.cast_injective _)
  have hfD : ∀ i, f i ∈ D := fun i ↦ hfD₀ (e i)
  choose x hx hfx using hfD
  have hcast : (fun i ↦ PadicSubspace.intCastVec (x i)) = f := by
    funext i
    exact hfx i
  have hxmem : ∀ i,
      x i ∈ realIntegralApproximationDomain L (codimOneScale W) c :=
    fun i ↦ hx i
  have hxi : LinearIndependent ℚ
      (fun i ↦ PadicSubspace.intCastVec (x i)) := by
    rw [hcast]
    exact hfi
  let A : Matrix (Fin m) (Fin (m + 1)) ℚ := integralRowMatrix x
  have hA : LinearIndependent ℚ A.row := by
    change LinearIndependent ℚ
      (fun i ↦ PadicSubspace.intCastVec (x i))
    exact hxi
  have hrowle : SubspaceHeights.rowSpace A ≤ W.1 := by
    intro y hy
    refine Submodule.span_induction
      (p := fun y _ ↦ y ∈ W.1) ?_ (W.1.zero_mem) ?_ ?_ hy
    · rintro y ⟨i, rfl⟩
      rw [integralRowMatrix_row]
      rw [hW]
      exact Submodule.subset_span ⟨x i, hxmem i, rfl⟩
    · intro y z _ _ hy hz
      exact W.1.add_mem hy hz
    · intro a y _ hy
      exact W.1.smul_mem a hy
  have hrowdim : Module.finrank ℚ (SubspaceHeights.rowSpace A) = m := by
    change Module.finrank ℚ
      (Submodule.span ℚ (Set.range A.row)) = m
    simpa only [Fintype.card_fin] using finrank_span_eq_card hA
  have hrow : W.1 = SubspaceHeights.rowSpace A := by
    symm
    apply Submodule.eq_of_le_of_finrank_le hrowle
    rw [hrowdim, hdimW]
  have hcof0 : SubspaceHeights.cofactorVector A ≠ 0 :=
    SubspaceHeights.cofactorVector_ne_zero_of_linearIndependent_rows hA
  refine ⟨x, hxmem, hxi, hrow, hcof0, ?_⟩
  intro y hy
  rw [hrow] at hy
  refine Submodule.span_induction
    (p := fun y _ ↦ y ⬝ᵥ SubspaceHeights.cofactorVector A = 0)
      ?_ ?_ ?_ ?_ hy
  · rintro y ⟨i, rfl⟩
    exact SubspaceHeights.row_dotProduct_cofactorVector A i
  · simp
  · intro y z _ _ hy hz
    simp [add_dotProduct, hy, hz]
  · intro a y _ hy
    simp [smul_dotProduct, hy]

theorem sCodimOne_isProper {n : ℕ} {L : LocalForms n}
    {c : HeightBoxes.LocalConstants n} (_hn : 0 < n)
    (W : sCodimOneApproximationSpaces L c) : W.1 < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro htop
  have hdim := sCodimOne_finrank_add_one W
  rw [htop] at hdim
  simp at hdim

theorem sCodimOneScale_injective {n : ℕ} {L : LocalForms n}
    {c : HeightBoxes.LocalConstants n} :
    Function.Injective
      (sCodimOneScale : sCodimOneApproximationSpaces L c → ℕ) := by
  intro W Z hscale
  apply Subtype.ext
  rw [sCodimOne_eq_span_scale W, sCodimOne_eq_span_scale Z, hscale]

/-- The scale is a proper height on the distinct codimension-one
`ℤ[1/6]` approximation spans. -/
theorem sCodimOneScale_isProper {n : ℕ} {L : LocalForms n}
    {c : HeightBoxes.LocalConstants n} :
    HeightBoxes.IsProperHeight
      (Set.univ : Set (sCodimOneApproximationSpaces L c))
      sCodimOneScale := by
  intro H
  have hpre :
      (sCodimOneScale ⁻¹' Set.Iic H :
        Set (sCodimOneApproximationSpaces L c)).Finite :=
    (Set.finite_Iic H).preimage sCodimOneScale_injective.injOn
  apply hpre.subset
  intro W hW
  exact hW.2

/-- Separated scale selection for distinct codimension-one `ℤ[1/6]`
approximation spans. -/
theorem exists_fastGrowing_sCodimOneSpaces {n : ℕ} {L : LocalForms n}
    {c : HeightBoxes.LocalConstants n}
    (hinfinite : (sCodimOneApproximationSpaces L c).Infinite)
    (Q₀ A m : ℕ) (hA : 1 ≤ A) :
    ∃ W : Fin (m + 1) → sCodimOneApproximationSpaces L c,
      Q₀ < sCodimOneScale (W 0) ∧
      (∀ i : Fin m,
        A * sCodimOneScale (W i.castSucc) < sCodimOneScale (W i.succ)) ∧
      Function.Injective W := by
  letI : Infinite (sCodimOneApproximationSpaces L c) := hinfinite.to_subtype
  obtain ⟨x, hx₀, hxgrow, hxinj⟩ := HeightBoxes.exists_fastGrowing
    (X := (Set.univ : Set (sCodimOneApproximationSpaces L c)))
    (h := (sCodimOneScale : sCodimOneApproximationSpaces L c → ℕ))
    sCodimOneScale_isProper Set.infinite_univ Q₀ A m hA
  let W : Fin (m + 1) → sCodimOneApproximationSpaces L c := fun i ↦ (x i).1
  refine ⟨W, hx₀, hxgrow, ?_⟩
  intro i j hij
  apply hxinj
  exact Subtype.ext hij

/-- Discard the finite support-pattern family before choosing separated
`ℤ[1/6]` approximation spans. -/
theorem exists_fastGrowing_nonexceptional_sCodimOneSpaces
    {n : ℕ} {L : LocalForms n} {c : HeightBoxes.LocalConstants n}
    (hinfinite : (sCodimOneApproximationSpaces L c).Infinite)
    (Q₀ A m : ℕ) (hA : 1 ≤ A) :
    ∃ W : Fin (m + 1) → sCodimOneApproximationSpaces L c,
      (∀ j, (W j).1 ∉ Set.range (exceptionalSpace L)) ∧
      Q₀ < sCodimOneScale (W 0) ∧
      (∀ i : Fin m,
        A * sCodimOneScale (W i.castSucc) < sCodimOneScale (W i.succ)) ∧
      Function.Injective W := by
  let E : Set (sCodimOneApproximationSpaces L c) :=
    {W | W.1 ∈ Set.range (exceptionalSpace L)}
  have hE : E.Finite := by
    exact (finite_exceptionalSpaces L).preimage
      (f := fun W : sCodimOneApproximationSpaces L c ↦ W.1)
      Subtype.val_injective.injOn
  letI : Infinite (sCodimOneApproximationSpaces L c) := hinfinite.to_subtype
  have hnonexceptional :
      ((Set.univ : Set (sCodimOneApproximationSpaces L c)) \ E).Infinite :=
    Set.infinite_univ.sdiff hE
  have hproper : HeightBoxes.IsProperHeight
      ((Set.univ : Set (sCodimOneApproximationSpaces L c)) \ E)
      sCodimOneScale := by
    intro H
    apply (sCodimOneScale_isProper (L := L) (c := c) H).subset
    intro W hW
    exact ⟨Set.mem_univ W, hW.2⟩
  obtain ⟨x, hx₀, hxgrow, hxinj⟩ := HeightBoxes.exists_fastGrowing
    hproper hnonexceptional Q₀ A m hA
  let W : Fin (m + 1) → sCodimOneApproximationSpaces L c := fun j ↦ (x j).1
  refine ⟨W, ?_, hx₀, hxgrow, ?_⟩
  · intro j hj
    exact (x j).2.2 hj
  · intro i j hij
    apply hxinj
    exact Subtype.ext hij

theorem codimOne_isProper {n : ℕ} {L : LocalForms n}
    {c : HeightBoxes.LocalConstants n} (_hn : 0 < n)
    (W : codimOneApproximationSpaces L c) : W.1 < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro htop
  have hdim := codimOne_finrank_add_one W
  rw [htop] at hdim
  simp at hdim

theorem codimOneScale_injective {n : ℕ} {L : LocalForms n}
    {c : HeightBoxes.LocalConstants n} :
    Function.Injective
      (codimOneScale : codimOneApproximationSpaces L c → ℕ) := by
  intro W Z hscale
  apply Subtype.ext
  rw [codimOne_eq_span_scale W, codimOne_eq_span_scale Z, hscale]

/-- The scale is a proper height on the set of distinct codimension-one
approximation spans. -/
theorem codimOneScale_isProper {n : ℕ} {L : LocalForms n}
    {c : HeightBoxes.LocalConstants n} :
    HeightBoxes.IsProperHeight
      (Set.univ : Set (codimOneApproximationSpaces L c)) codimOneScale := by
  intro H
  have hpre :
      (codimOneScale ⁻¹' Set.Iic H : Set (codimOneApproximationSpaces L c)).Finite :=
    (Set.finite_Iic H).preimage codimOneScale_injective.injOn
  apply hpre.subset
  intro W hW
  exact hW.2

/-- If the codimension-one family were infinite, it would contain an
arbitrarily long sequence with any prescribed multiplicative separation of
the scales.  This is the scale-selection step at the start of the proof of
GLR Theorem 4.14. -/
theorem exists_fastGrowing_codimOneSpaces {n : ℕ} {L : LocalForms n}
    {c : HeightBoxes.LocalConstants n}
    (hinfinite : (codimOneApproximationSpaces L c).Infinite)
    (Q₀ A m : ℕ) (hA : 1 ≤ A) :
    ∃ W : Fin (m + 1) → codimOneApproximationSpaces L c,
      Q₀ < codimOneScale (W 0) ∧
      (∀ i : Fin m,
        A * codimOneScale (W i.castSucc) < codimOneScale (W i.succ)) ∧
      Function.Injective W := by
  letI : Infinite (codimOneApproximationSpaces L c) := hinfinite.to_subtype
  obtain ⟨x, hx₀, hxgrow, hxinj⟩ := HeightBoxes.exists_fastGrowing
    (X := (Set.univ : Set (codimOneApproximationSpaces L c)))
    (h := (codimOneScale : codimOneApproximationSpaces L c → ℕ))
    codimOneScale_isProper Set.infinite_univ Q₀ A m hA
  let W : Fin (m + 1) → codimOneApproximationSpaces L c := fun i ↦ (x i).1
  refine ⟨W, hx₀, hxgrow, ?_⟩
  intro i j hij
  apply hxinj
  exact Subtype.ext hij

/-- The finite exceptional support-pattern family can be discarded before
selecting the separated scales.  This is the finite-family repair of the
single-exceptional-hyperplane assertion in the published Lemma 4.22. -/
theorem exists_fastGrowing_nonexceptional_codimOneSpaces
    {n : ℕ} {L : LocalForms n} {c : HeightBoxes.LocalConstants n}
    (hinfinite : (codimOneApproximationSpaces L c).Infinite)
    (Q₀ A m : ℕ) (hA : 1 ≤ A) :
    ∃ W : Fin (m + 1) → codimOneApproximationSpaces L c,
      (∀ j, (W j).1 ∉ Set.range (exceptionalSpace L)) ∧
      Q₀ < codimOneScale (W 0) ∧
      (∀ i : Fin m,
        A * codimOneScale (W i.castSucc) < codimOneScale (W i.succ)) ∧
      Function.Injective W := by
  let E : Set (codimOneApproximationSpaces L c) :=
    {W | W.1 ∈ Set.range (exceptionalSpace L)}
  have hE : E.Finite := by
    exact (finite_exceptionalSpaces L).preimage
      (f := fun W : codimOneApproximationSpaces L c ↦ W.1)
      Subtype.val_injective.injOn
  letI : Infinite (codimOneApproximationSpaces L c) := hinfinite.to_subtype
  have hnonexceptional :
      ((Set.univ : Set (codimOneApproximationSpaces L c)) \ E).Infinite :=
    Set.infinite_univ.sdiff hE
  have hproper : HeightBoxes.IsProperHeight
      ((Set.univ : Set (codimOneApproximationSpaces L c)) \ E)
      codimOneScale := by
    intro H
    apply (codimOneScale_isProper (L := L) (c := c) H).subset
    intro W hW
    exact ⟨Set.mem_univ W, hW.2⟩
  obtain ⟨x, hx₀, hxgrow, hxinj⟩ := HeightBoxes.exists_fastGrowing
    hproper hnonexceptional Q₀ A m hA
  let W : Fin (m + 1) → codimOneApproximationSpaces L c := fun j ↦ (x j).1
  refine ⟨W, ?_, hx₀, hxgrow, ?_⟩
  · intro j hj
    exact (x j).2.2 hj
  · intro i j hij
    apply hxinj
    exact Subtype.ext hij

/-! ## Finite proper subspaces give a finite hyperplane cover -/

/-- A finite collection of proper rational subspaces can be enlarged to a
finite collection of proper rational hyperplanes.  This is the final
linear-algebra step after GLR rank stabilization, and is independent of how
the finite family was obtained. -/
theorem finiteHyperplaneCover_of_finite_properSubspaces {n : ℕ}
    {X : Set (IntVector n)} {C : Set (Submodule ℚ (RatVector n))}
    (hC : C.Finite) (hproper : ∀ W ∈ C, W < ⊤)
    (hcover : ∀ x ∈ X, ∃ W ∈ C, PadicSubspace.intCastVec x ∈ W) :
    PadicSubspace.HasFiniteHyperplaneCover X := by
  classical
  letI : Fintype C := hC.fintype
  choose f hf hW _hker using fun W : C ↦
    GeneralPosition.properSubspace_le_kernel W.1 (hproper W.1 W.2)
  let normals : Finset (RatVector n) :=
    Finset.univ.image fun W : C ↦ PadicSubspace.coefficientVector (f W)
  refine ⟨normals, ?_, ?_⟩
  · intro b hb
    obtain ⟨W, _hW, rfl⟩ := Finset.mem_image.mp hb
    exact PadicSubspace.coefficientVector_ne_zero (hf W)
  · intro x hx
    obtain ⟨W, hWC, hxW⟩ := hcover x hx
    let wC : C := ⟨W, hWC⟩
    refine ⟨PadicSubspace.coefficientVector (f wC), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨wC, Finset.mem_univ _, rfl⟩
    · rw [PadicSubspace.OnHyperplane,
        ← PadicSubspace.linearForm_eq_dotProduct]
      exact hW wC hxW

/-! ## Cofactor form of the codimension-one extraction -/

/-- Cofactor package behind the determinant calculation in GLR Lemma 4.22.
Independent rows of an `m × (m+1)` coefficient matrix have a nonzero
cofactor vector; every row and therefore every point in their row span is
annihilated by that vector.  The homogeneous solution space has exactly the
matrix height. -/
theorem cofactor_hyperplane_and_height {m : ℕ}
    (A : Matrix (Fin m) (Fin (m + 1)) ℚ)
    (hA : LinearIndependent ℚ A.row) :
    SubspaceHeights.cofactorVector A ≠ 0 ∧
      (∀ x ∈ SubspaceHeights.rowSpace A,
        x ⬝ᵥ SubspaceHeights.cofactorVector A = 0) ∧
      SubspaceHeights.subspaceHeight (SubspaceHeights.solutionSpace A) =
        SubspaceHeights.matrixHeight A := by
  refine ⟨SubspaceHeights.cofactorVector_ne_zero_of_linearIndependent_rows hA,
    ?_, SubspaceHeights.solutionSpace_height_eq_matrixHeight A⟩
  intro x hx
  refine Submodule.span_induction
    (p := fun x _ ↦ x ⬝ᵥ SubspaceHeights.cofactorVector A = 0)
      ?_ ?_ ?_ ?_ hx
  · rintro x ⟨i, rfl⟩
    exact SubspaceHeights.row_dotProduct_cofactorVector A i
  · simp
  · intro x y _ _ hx hy
    simp [add_dotProduct, hx, hy]
  · intro a x _ hx
    simp [smul_dotProduct, hx]

/-! ## Strict-rank induction -/

/-- Along a strictly descending chain of finite-dimensional rational
subspaces, each step consumes at least one dimension. -/
theorem finrank_add_length_le_of_strictDescending {n k : ℕ}
    (W : ℕ → Submodule ℚ (RatVector n))
    (hW : ∀ i < k, W (i + 1) < W i) :
    Module.finrank ℚ (W k) + k ≤ Module.finrank ℚ (W 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hprefix : ∀ i < k, W (i + 1) < W i := by
        intro i hi
        exact hW i (hi.trans (Nat.lt_succ_self k))
      have hstep : Module.finrank ℚ (W (k + 1)) < Module.finrank ℚ (W k) :=
        Submodule.finrank_lt_finrank_of_lt (hW k (Nat.lt_succ_self k))
      have hih := ih hprefix
      omega

/-- A strictly descending chain of rational subspaces has length at most the
ambient dimension. -/
theorem strictDescending_length_le_dimension {n k : ℕ}
    (W : ℕ → Submodule ℚ (RatVector n))
    (hW : ∀ i < k, W (i + 1) < W i) : k ≤ n := by
  have hchain := finrank_add_length_le_of_strictDescending W hW
  have hamb : Module.finrank ℚ (W 0) ≤ n := by
    simpa using Submodule.finrank_le (W 0)
  omega

/-- In the Erdős 407 application no strict-rank induction can have more than
five steps. -/
theorem strictDescending_length_le_five {n k : ℕ} (hn : n ≤ 5)
    (W : ℕ → Submodule ℚ (RatVector n))
    (hW : ∀ i < k, W (i + 1) < W i) : k ≤ 5 :=
  (strictDescending_length_le_dimension W hW).trans hn

#print axioms approximationRank_lt_of_radiiProduct
#print axioms exists_height_dual_hyperplane_of_radiiProduct
#print axioms cofactor_hyperplane_and_height
#print axioms strictDescending_length_le_five

end Erdos407.RankDrop
