/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.GAP

/-!
# Rectangular sublattices and integral bases

This file isolates the algebraic lattice bookkeeping in the proof of
Conlon--Fox--Pham, Lemma 2.16.  For positive integral side lengths `v`, the
rectangular lattice is

`v₁ℤ × ... × v_dℤ ≤ ℤ^d`.

We prove that every subgroup containing it has a `Fin d`-indexed integral
basis, compute the index of the rectangular lattice, and bound the relative
index of the rectangular lattice in the larger subgroup.  The last section
records the coordinate decomposition used in the coefficient estimate in
CFP Lemma 2.16.
-/

namespace Erdos186.CFP.LatticeBasis

open scoped BigOperators
open Module

/-- An additive subgroup of the standard integral lattice. -/
abbrev Sublattice (d : ℕ) := AddSubgroup (LatticePoint d)

/-- The `i`th axis vector with (positive) step `v i`. -/
def axisVector {d : ℕ} (v : Fin d → ℕ) (i : Fin d) : LatticePoint d :=
  Pi.single i (v i : ℤ)

@[simp]
theorem axisVector_apply {d : ℕ} (v : Fin d → ℕ) (i j : Fin d) :
    axisVector v i j = if i = j then (v i : ℤ) else 0 := by
  by_cases hij : i = j <;> simp [axisVector, hij, eq_comm]

/-- The coordinatewise rectangular sublattice
`v₁ℤ × ... × v_dℤ`. -/
def rectangularSubgroup {d : ℕ} (v : Fin d → ℕ) : Sublattice d :=
  AddSubgroup.pi Set.univ fun i ↦ AddSubgroup.zmultiples (v i : ℤ)

@[simp]
theorem mem_rectangularSubgroup_iff {d : ℕ} {v : Fin d → ℕ}
    {x : LatticePoint d} :
    x ∈ rectangularSubgroup v ↔ ∀ i, (v i : ℤ) ∣ x i := by
  simp [rectangularSubgroup, AddSubgroup.mem_pi, Int.mem_zmultiples_iff]

@[simp]
theorem axisVector_mem_rectangularSubgroup {d : ℕ} (v : Fin d → ℕ)
    (i : Fin d) :
    axisVector v i ∈ rectangularSubgroup v := by
  rw [mem_rectangularSubgroup_iff]
  intro j
  by_cases hij : i = j
  · subst j
    simp
  · simp [axisVector_apply, hij]

/-- The rectangular lattice has index equal to the product of its side
lengths.  Positivity is not needed for the identity: if one side is zero,
both sides use the convention that an infinite index is `0`. -/
theorem rectangularSubgroup_index {d : ℕ} (v : Fin d → ℕ) :
    (rectangularSubgroup v).index = ∏ i, v i := by
  simp [rectangularSubgroup]

/-- Positive rectangular side lengths make the axis vectors linearly
independent over `ℤ`. -/
theorem linearIndependent_axisVector {d : ℕ} {v : Fin d → ℕ}
    (hv : ∀ i, 0 < v i) :
    LinearIndependent ℤ (axisVector v) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hi := congrFun hg i
  simp [axisVector, Pi.single_apply] at hi
  exact hi.resolve_right (ne_of_gt (hv i))

/-- A subgroup of `ℤ^d` containing a positive rectangular sublattice has
full integral rank: it admits a basis indexed by `Fin d`.

This packages two separate facts from Mathlib.  A submodule of a finite free
module over the PID `ℤ` has a finite basis (`Submodule.basisOfPid`), and
the rectangular axis vectors give the reverse rank inequality. -/
theorem exists_basis_of_rectangular_le {d : ℕ} {v : Fin d → ℕ}
    (hv : ∀ i, 0 < v i) (Gamma : Sublattice d)
    (hrect : rectangularSubgroup v ≤ Gamma) :
    Nonempty (Basis (Fin d) ℤ Gamma) := by
  classical
  let bstd : Basis (Fin d) ℤ (LatticePoint d) := Pi.basisFun ℤ (Fin d)
  obtain ⟨n, bGamma⟩ :=
    Submodule.basisOfPid bstd Gamma.toIntSubmodule
  let aGamma : Fin d → Gamma := fun i ↦
    ⟨axisVector v i, hrect (axisVector_mem_rectangularSubgroup v i)⟩
  have ha_ambient : LinearIndependent ℤ
      ((Gamma.toIntSubmodule.subtype : Gamma →ₗ[ℤ] LatticePoint d) ∘ aGamma) := by
    change LinearIndependent ℤ (axisVector v)
    exact linearIndependent_axisVector hv
  have ha : LinearIndependent ℤ aGamma :=
    LinearIndependent.of_comp Gamma.toIntSubmodule.subtype ha_ambient
  have hn_le : n ≤ d := by
    simpa using bstd.card_le_card_of_linearIndependent
      (bGamma.linearIndependent.map_injOn Gamma.toIntSubmodule.subtype
        Gamma.toIntSubmodule.injective_subtype.injOn)
  have hd_le : d ≤ n := by
    simpa using bGamma.card_le_card_of_linearIndependent ha
  have hnd : n = d := Nat.le_antisymm hn_le hd_le
  exact ⟨bGamma.reindex (finCongr hnd)⟩

/-- The relative index of a positive rectangular sublattice inside any
larger sublattice is at most the product of the side lengths.  This is the
precise cardinal bound `|Γ/H| ≤ v₁⋯v_d` used in CFP Lemma 2.16;
`AddSubgroup.relIndex` is the cardinal of that quotient. -/
theorem rectangular_relIndex_le_prod {d : ℕ} {v : Fin d → ℕ}
    (hv : ∀ i, 0 < v i) (Gamma : Sublattice d)
    (hrect : rectangularSubgroup v ≤ Gamma) :
    (rectangularSubgroup v).relIndex Gamma ≤ ∏ i, v i := by
  have hprod : 0 < ∏ i, v i := Finset.prod_pos fun i _ ↦ hv i
  have hindex : 0 < (rectangularSubgroup v).index := by
    rw [rectangularSubgroup_index]
    exact hprod
  rw [← rectangularSubgroup_index v]
  exact Nat.le_of_dvd hindex (AddSubgroup.relIndex_dvd_index_of_le hrect)

/-- The tower identity behind the preceding quotient bound. -/
theorem rectangular_relIndex_mul_index {d : ℕ} (v : Fin d → ℕ)
    (Gamma : Sublattice d) (hrect : rectangularSubgroup v ≤ Gamma) :
    (rectangularSubgroup v).relIndex Gamma * Gamma.index = ∏ i, v i := by
  rw [AddSubgroup.relIndex_mul_index hrect, rectangularSubgroup_index]

/-! ## Euclidean coordinate decomposition -/

/-- Coordinatewise quotient by the rectangular side lengths. -/
def rectangularQuotient {d : ℕ} (v : Fin d → ℕ)
    (y : LatticePoint d) : LatticePoint d :=
  fun i ↦ y i / (v i : ℤ)

/-- The rectangular-lattice part in coordinatewise Euclidean division. -/
def rectangularPart {d : ℕ} (v : Fin d → ℕ)
    (y : LatticePoint d) : LatticePoint d :=
  fun i ↦ (v i : ℤ) * rectangularQuotient v y i

/-- The coordinatewise nonnegative remainder. -/
def rectangularRemainder {d : ℕ} (v : Fin d → ℕ)
    (y : LatticePoint d) : LatticePoint d :=
  fun i ↦ y i % (v i : ℤ)

theorem rectangularPart_add_remainder {d : ℕ} (v : Fin d → ℕ)
    (y : LatticePoint d) :
    rectangularPart v y + rectangularRemainder v y = y := by
  funext i
  exact Int.mul_ediv_add_emod (y i) (v i : ℤ)

theorem rectangularPart_mem {d : ℕ} (v : Fin d → ℕ)
    (y : LatticePoint d) :
    rectangularPart v y ∈ rectangularSubgroup v := by
  rw [mem_rectangularSubgroup_iff]
  intro i
  exact ⟨rectangularQuotient v y i, by simp [rectangularPart]⟩

theorem rectangularRemainder_mem_of_mem {d : ℕ} {v : Fin d → ℕ}
    {Gamma : Sublattice d} (hrect : rectangularSubgroup v ≤ Gamma)
    {y : LatticePoint d} (hy : y ∈ Gamma) :
    rectangularRemainder v y ∈ Gamma := by
  have hz : rectangularPart v y ∈ Gamma := hrect (rectangularPart_mem v y)
  have hdecomp := rectangularPart_add_remainder v y
  have hrem : rectangularRemainder v y = y - rectangularPart v y := by
    funext i
    have hi := congrFun hdecomp i
    simp only [Pi.add_apply] at hi
    change rectangularPart v y i + rectangularRemainder v y i = y i at hi
    change rectangularRemainder v y i = y i - rectangularPart v y i
    omega
  rw [hrem]
  exact Gamma.sub_mem hy hz

theorem rectangularRemainder_nonneg {d : ℕ} {v : Fin d → ℕ}
    (hv : ∀ i, 0 < v i) (y : LatticePoint d) (i : Fin d) :
    0 ≤ rectangularRemainder v y i := by
  exact Int.emod_nonneg _ (by exact_mod_cast (ne_of_gt (hv i)))

theorem rectangularRemainder_lt {d : ℕ} {v : Fin d → ℕ}
    (hv : ∀ i, 0 < v i) (y : LatticePoint d) (i : Fin d) :
    rectangularRemainder v y i < (v i : ℤ) := by
  exact Int.emod_lt_of_pos _ (by exact_mod_cast (hv i))

/-! ## Basis coefficients -/

/-- The `i`th integral coefficient of a lattice element in a chosen basis. -/
noncomputable def basisCoeff {d : ℕ} {Gamma : Sublattice d}
    (b : Basis (Fin d) ℤ Gamma) (x : Gamma) (i : Fin d) : ℤ :=
  b.repr x i

/-- Reconstruction from all basis coefficients. -/
theorem sum_basisCoeff_smul {d : ℕ} {Gamma : Sublattice d}
    (b : Basis (Fin d) ℤ Gamma) (x : Gamma) :
    (∑ i, basisCoeff b x i • b i) = x := by
  exact b.sum_repr x

@[simp]
theorem basisCoeff_add {d : ℕ} {Gamma : Sublattice d}
    (b : Basis (Fin d) ℤ Gamma) (x y : Gamma) (i : Fin d) :
    basisCoeff b (x + y) i = basisCoeff b x i + basisCoeff b y i := by
  simp [basisCoeff]

@[simp]
theorem basisCoeff_zsmul {d : ℕ} {Gamma : Sublattice d}
    (b : Basis (Fin d) ℤ Gamma) (a : ℤ) (x : Gamma) (i : Fin d) :
    basisCoeff b (a • x) i = a * basisCoeff b x i := by
  simp [basisCoeff]

/-- Triangle inequality for the basis coefficient of a finite integral
linear combination. -/
theorem abs_basisCoeff_sum_le {d n : ℕ} {Gamma : Sublattice d}
    (b : Basis (Fin d) ℤ Gamma) (a : Fin n → ℤ) (x : Fin n → Gamma)
    (i : Fin d) :
    |basisCoeff b (∑ j, a j • x j) i| ≤
      ∑ j, |a j| * |basisCoeff b (x j) i| := by
  rw [show basisCoeff b (∑ j, a j • x j) i =
      ∑ j, a j * basisCoeff b (x j) i by
    simp [basisCoeff]]
  calc
    |∑ j, a j * basisCoeff b (x j) i| ≤
        ∑ j, |a j * basisCoeff b (x j) i| := by
          simpa using Finset.abs_sum_le_sum_abs
            (fun j ↦ a j * basisCoeff b (x j) i) Finset.univ
    _ = ∑ j, |a j| * |basisCoeff b (x j) i| := by simp [abs_mul]

/-- The rectangular part is the integral combination of the rectangular
axis vectors whose coefficients are the coordinatewise quotients. -/
theorem sum_rectangularQuotient_axisVector {d : ℕ} (v : Fin d → ℕ)
    (y : LatticePoint d) :
    (∑ j, rectangularQuotient v y j • axisVector v j) =
      rectangularPart v y := by
  funext i
  simp [rectangularQuotient, rectangularPart, axisVector, Pi.single_apply,
    mul_comm]

/-- An axis vector, bundled as a member of a lattice containing the
rectangular sublattice. -/
def axisVectorIn {d : ℕ} {v : Fin d → ℕ} {Gamma : Sublattice d}
    (hrect : rectangularSubgroup v ≤ Gamma) (i : Fin d) : Gamma :=
  ⟨axisVector v i, hrect (axisVector_mem_rectangularSubgroup v i)⟩

/-- The rectangular part of a lattice element, bundled in the larger
lattice. -/
def rectangularPartIn {d : ℕ} {v : Fin d → ℕ} {Gamma : Sublattice d}
    (hrect : rectangularSubgroup v ≤ Gamma) (y : Gamma) : Gamma :=
  ⟨rectangularPart v y, hrect (rectangularPart_mem v y)⟩

/-- The remainder of a lattice element, bundled in the larger lattice. -/
def rectangularRemainderIn {d : ℕ} {v : Fin d → ℕ}
    {Gamma : Sublattice d} (hrect : rectangularSubgroup v ≤ Gamma)
    (y : Gamma) : Gamma :=
  ⟨rectangularRemainder v y,
    rectangularRemainder_mem_of_mem hrect y.property⟩

@[simp]
theorem coe_axisVectorIn {d : ℕ} {v : Fin d → ℕ} {Gamma : Sublattice d}
    (hrect : rectangularSubgroup v ≤ Gamma) (i : Fin d) :
    (axisVectorIn hrect i : LatticePoint d) = axisVector v i := rfl

@[simp]
theorem coe_rectangularPartIn {d : ℕ} {v : Fin d → ℕ}
    {Gamma : Sublattice d} (hrect : rectangularSubgroup v ≤ Gamma)
    (y : Gamma) :
    (rectangularPartIn hrect y : LatticePoint d) = rectangularPart v y := rfl

@[simp]
theorem coe_rectangularRemainderIn {d : ℕ} {v : Fin d → ℕ}
    {Gamma : Sublattice d} (hrect : rectangularSubgroup v ≤ Gamma)
    (y : Gamma) :
    (rectangularRemainderIn hrect y : LatticePoint d) =
      rectangularRemainder v y := rfl

/-- Exact decomposition inside the larger lattice. -/
theorem rectangularPartIn_add_remainderIn {d : ℕ} {v : Fin d → ℕ}
    {Gamma : Sublattice d} (hrect : rectangularSubgroup v ≤ Gamma)
    (y : Gamma) :
    rectangularPartIn hrect y + rectangularRemainderIn hrect y = y := by
  apply Subtype.ext
  exact rectangularPart_add_remainder v y

/-- Exact axis-vector expansion of the rectangular part inside the larger
lattice. -/
theorem sum_rectangularQuotient_axisVectorIn {d : ℕ} {v : Fin d → ℕ}
    {Gamma : Sublattice d} (hrect : rectangularSubgroup v ≤ Gamma)
    (y : Gamma) :
    (∑ j, rectangularQuotient v y j • axisVectorIn hrect j) =
      rectangularPartIn hrect y := by
  apply Subtype.ext
  simpa using sum_rectangularQuotient_axisVector v y

/-- The coefficient estimate underlying the final paragraph of the lattice
part of CFP Lemma 2.16.  `Xi` bounds the chosen-basis coefficients of the
rectangular generators and of every residue representative.  The explicit
sum over coordinate quotients is essential. -/
theorem abs_basisCoeff_le_quotient_sum {d : ℕ} {v : Fin d → ℕ}
    {Gamma : Sublattice d} (hrect : rectangularSubgroup v ≤ Gamma)
    (hv : ∀ j, 0 < v j) (b : Basis (Fin d) ℤ Gamma) (Xi : ℕ)
    (haxis : ∀ j i,
      |basisCoeff b (axisVectorIn hrect j) i| ≤ (Xi : ℤ))
    (hresidue : ∀ (t : Gamma),
      (∀ j, 0 ≤ (t : LatticePoint d) j ∧
        (t : LatticePoint d) j < (v j : ℤ)) →
      ∀ i, |basisCoeff b t i| ≤ (Xi : ℤ))
    (y : Gamma) (i : Fin d) :
    |basisCoeff b y i| ≤
      ((∑ j, |rectangularQuotient v y j|) + 1) * (Xi : ℤ) := by
  have hpart :
      |basisCoeff b (rectangularPartIn hrect y) i| ≤
        ∑ j, |rectangularQuotient v y j| * (Xi : ℤ) := by
    rw [← sum_rectangularQuotient_axisVectorIn hrect y]
    refine (abs_basisCoeff_sum_le b (rectangularQuotient v y)
      (axisVectorIn hrect) i).trans ?_
    exact Finset.sum_le_sum fun j _ ↦
      mul_le_mul_of_nonneg_left (haxis j i) (abs_nonneg _)
  have hrem :
      |basisCoeff b (rectangularRemainderIn hrect y) i| ≤ (Xi : ℤ) := by
    apply hresidue
    intro j
    exact ⟨rectangularRemainder_nonneg hv y j,
      rectangularRemainder_lt hv y j⟩
  have hcoeff : basisCoeff b y i =
      basisCoeff b (rectangularPartIn hrect y) i +
        basisCoeff b (rectangularRemainderIn hrect y) i := by
    calc
      basisCoeff b y i = basisCoeff b
          (rectangularPartIn hrect y + rectangularRemainderIn hrect y) i :=
        congrArg (fun z : Gamma ↦ basisCoeff b z i)
          (rectangularPartIn_add_remainderIn hrect y).symm
      _ = _ := basisCoeff_add _ _ _ _
  rw [hcoeff]
  calc
    |basisCoeff b (rectangularPartIn hrect y) i +
        basisCoeff b (rectangularRemainderIn hrect y) i| ≤
        |basisCoeff b (rectangularPartIn hrect y) i| +
          |basisCoeff b (rectangularRemainderIn hrect y) i| := abs_add_le _ _
    _ ≤ (∑ j, |rectangularQuotient v y j| * (Xi : ℤ)) +
        (Xi : ℤ) := add_le_add hpart hrem
    _ = ((∑ j, |rectangularQuotient v y j|) + 1) * (Xi : ℤ) := by
      rw [add_mul, one_mul, Finset.sum_mul]

/-- A pointwise box bound controls the quotient coefficients occurring in
the rectangular part.  The conclusion is deliberately division-free. -/
theorem abs_rectangularQuotient_le_of_abs_le_mul {d : ℕ}
    {v w : Fin d → ℕ} (hv : ∀ i, 0 < v i) {y : LatticePoint d}
    (hy : ∀ i, |y i| ≤ (w i : ℤ) * (v i : ℤ)) (i : Fin d) :
    |rectangularQuotient v y i| ≤ (w i : ℤ) := by
  dsimp only [rectangularQuotient]
  have hv' : (0 : ℤ) < (v i : ℤ) := by exact_mod_cast hv i
  rw [abs_le]
  constructor
  · apply Int.le_ediv_of_mul_le hv'
    calc
      -(w i : ℤ) * (v i : ℤ) ≤ -|y i| := by
        simpa only [neg_mul] using neg_le_neg (hy i)
      _ ≤ y i := neg_abs_le _
  · apply Int.ediv_le_of_le_mul hv'
    exact (le_abs_self (y i)).trans (hy i)

/-- Box form of the basis-coefficient estimate.  If the `j`th ambient
coordinate is bounded by `w j * v j`, then every chosen-basis coefficient
is bounded by `(∑ j, w j + 1) * Xi`. -/
theorem abs_basisCoeff_le_box_sum {d : ℕ} {v w : Fin d → ℕ}
    {Gamma : Sublattice d} (hrect : rectangularSubgroup v ≤ Gamma)
    (hv : ∀ j, 0 < v j) (b : Basis (Fin d) ℤ Gamma) (Xi : ℕ)
    (haxis : ∀ j i,
      |basisCoeff b (axisVectorIn hrect j) i| ≤ (Xi : ℤ))
    (hresidue : ∀ (t : Gamma),
      (∀ j, 0 ≤ (t : LatticePoint d) j ∧
        (t : LatticePoint d) j < (v j : ℤ)) →
      ∀ i, |basisCoeff b t i| ≤ (Xi : ℤ))
    (y : Gamma)
    (hy : ∀ j, |(y : LatticePoint d) j| ≤
      (w j : ℤ) * (v j : ℤ)) (i : Fin d) :
    |basisCoeff b y i| ≤
      ((∑ j, (w j : ℤ)) + 1) * (Xi : ℤ) := by
  refine (abs_basisCoeff_le_quotient_sum hrect hv b Xi haxis hresidue y i).trans ?_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hsum : (∑ j, |rectangularQuotient v y j|) ≤
      ∑ j, (w j : ℤ) :=
    Finset.sum_le_sum fun j _ ↦
      abs_rectangularQuotient_le_of_abs_le_mul hv hy j
  simpa [add_comm] using add_le_add_right hsum 1

/-! ## A uniform bounded-basis choice

The printed proof of CFP Lemma 2.16 claims the sharper coordinate box
`[0, 2 * v i - 1]`.  For the later argument, only a bound depending on `v`
is needed.  The following construction obtains exactly that dependency
without invoking a Hermite-normal-form API: a superlattice of the
rectangular lattice is determined by the subset of the finite residue box
that it contains.  Hence there are only finitely many such superlattices,
and we may take a maximum over an arbitrarily chosen basis of each one.
-/

/-- The finite coordinate box of canonical residues modulo the rectangular
lattice. -/
abbrev ResidueCoord {d : ℕ} (v : Fin d → ℕ) :=
  (i : Fin d) → Fin (v i)

/-- The lattice point represented by a canonical residue coordinate. -/
def residuePoint {d : ℕ} {v : Fin d → ℕ}
    (r : ResidueCoord v) : LatticePoint d :=
  fun i ↦ ((r i : ℕ) : ℤ)

@[simp]
theorem residuePoint_apply {d : ℕ} {v : Fin d → ℕ}
    (r : ResidueCoord v) (i : Fin d) :
    residuePoint r i = ((r i : ℕ) : ℤ) := rfl

/-- Canonical residue coordinates of an arbitrary lattice point. -/
def remainderCoord {d : ℕ} {v : Fin d → ℕ}
    (hv : ∀ i, 0 < v i) (y : LatticePoint d) : ResidueCoord v :=
  fun i ↦ ⟨Int.toNat (rectangularRemainder v y i), by
    have hnonneg := rectangularRemainder_nonneg hv y i
    have hlt := rectangularRemainder_lt hv y i
    rw [Int.toNat_lt hnonneg]
    exact hlt⟩

@[simp]
theorem residuePoint_remainderCoord {d : ℕ} {v : Fin d → ℕ}
    (hv : ∀ i, 0 < v i) (y : LatticePoint d) :
    residuePoint (remainderCoord hv y) = rectangularRemainder v y := by
  funext i
  simp [remainderCoord, residuePoint,
    Int.toNat_of_nonneg (rectangularRemainder_nonneg hv y i)]

/-- The set of canonical residue classes contained in a sublattice. -/
noncomputable def residueSignature {d : ℕ} {v : Fin d → ℕ}
    (Gamma : Sublattice d) : Finset (ResidueCoord v) :=
  by
    classical
    exact Finset.univ.filter fun r ↦ residuePoint r ∈ Gamma

@[simp]
theorem mem_residueSignature {d : ℕ} {v : Fin d → ℕ}
    {Gamma : Sublattice d} {r : ResidueCoord v} :
    r ∈ residueSignature (v := v) Gamma ↔ residuePoint r ∈ Gamma := by
  simp [residueSignature]

/-- A superlattice of a positive rectangular lattice is determined by the
canonical residues that it contains. -/
theorem eq_of_residueSignature_eq {d : ℕ} {v : Fin d → ℕ}
    (hv : ∀ i, 0 < v i) {Gamma Lambda : Sublattice d}
    (hGamma : rectangularSubgroup v ≤ Gamma)
    (hLambda : rectangularSubgroup v ≤ Lambda)
    (hsig : residueSignature (v := v) Gamma =
      residueSignature (v := v) Lambda) :
    Gamma = Lambda := by
  apply le_antisymm
  · intro y hy
    have hryG : rectangularRemainder v y ∈ Gamma :=
      rectangularRemainder_mem_of_mem hGamma hy
    have hcoordG : remainderCoord hv y ∈ residueSignature Gamma := by
      rw [mem_residueSignature, residuePoint_remainderCoord]
      exact hryG
    rw [hsig, mem_residueSignature, residuePoint_remainderCoord] at hcoordG
    have hpartL : rectangularPart v y ∈ Lambda :=
      hLambda (rectangularPart_mem v y)
    rw [← rectangularPart_add_remainder v y]
    exact Lambda.add_mem hpartL hcoordG
  · intro y hy
    have hryL : rectangularRemainder v y ∈ Lambda :=
      rectangularRemainder_mem_of_mem hLambda hy
    have hcoordL : remainderCoord hv y ∈ residueSignature Lambda := by
      rw [mem_residueSignature, residuePoint_remainderCoord]
      exact hryL
    rw [← hsig, mem_residueSignature, residuePoint_remainderCoord] at hcoordL
    have hpartG : rectangularPart v y ∈ Gamma :=
      hGamma (rectangularPart_mem v y)
    rw [← rectangularPart_add_remainder v y]
    exact Gamma.add_mem hpartG hcoordL

/-- Sublattices containing a fixed rectangular lattice. -/
abbrev Superlattice {d : ℕ} (v : Fin d → ℕ) :=
  {Gamma : Sublattice d // rectangularSubgroup v ≤ Gamma}

/-- The residue signature embeds the type of superlattices in a finite
type. -/
theorem superlattice_signature_injective {d : ℕ} {v : Fin d → ℕ}
    (hv : ∀ i, 0 < v i) :
    Function.Injective
      (fun Gamma : Superlattice v ↦ residueSignature (v := v) Gamma.1) := by
  intro Gamma Lambda h
  apply Subtype.ext
  exact eq_of_residueSignature_eq hv Gamma.2 Lambda.2 h

/-- There are only finitely many sublattices between a positive rectangular
lattice and `ℤ^d`. -/
theorem finite_superlattice {d : ℕ} {v : Fin d → ℕ}
    (hv : ∀ i, 0 < v i) : Finite (Superlattice v) := by
  exact Finite.of_injective
    (fun Gamma : Superlattice v ↦ residueSignature (v := v) Gamma.1)
    (superlattice_signature_injective hv)

/-- A basis chosen for each superlattice. -/
noncomputable def chosenBasis {d : ℕ} {v : Fin d → ℕ}
    (hv : ∀ i, 0 < v i) (Gamma : Superlattice v) :
    Basis (Fin d) ℤ Gamma.1 :=
  Classical.choice (exists_basis_of_rectangular_le hv Gamma.1 Gamma.2)

/-- A uniform coordinate budget for bases of all superlattices of the
rectangular lattice.  It depends only on `v`, not on the particular
superlattice. -/
noncomputable def uniformBasisBound {d : ℕ} (v : Fin d → ℕ)
    (hv : ∀ i, 0 < v i) : ℕ := by
  letI : Fintype (Superlattice v) :=
    @Fintype.ofFinite (Superlattice v) (finite_superlattice hv)
  exact ∑ Gamma : Superlattice v, ∑ i, ∑ j,
    Int.natAbs (((chosenBasis hv Gamma i : Gamma.1) : LatticePoint d) j)

/-- Every superlattice has a basis whose ambient coordinates are bounded by
one number depending only on the rectangular side lengths. -/
theorem exists_basis_ambient_abs_le_uniformBasisBound {d : ℕ}
    {v : Fin d → ℕ} (hv : ∀ i, 0 < v i) (Gamma : Sublattice d)
    (hrect : rectangularSubgroup v ≤ Gamma) :
    ∃ b : Basis (Fin d) ℤ Gamma, ∀ i j,
      |((b i : Gamma) : LatticePoint d) j| ≤ (uniformBasisBound v hv : ℤ) := by
  letI : Fintype (Superlattice v) :=
    @Fintype.ofFinite (Superlattice v) (finite_superlattice hv)
  let Gamma' : Superlattice v := ⟨Gamma, hrect⟩
  refine ⟨chosenBasis hv Gamma', ?_⟩
  intro i j
  have hij : Int.natAbs
      ((((chosenBasis hv Gamma' i : Gamma'.1) : LatticePoint d)) j) ≤
      uniformBasisBound v hv := by
    change Int.natAbs
      ((((chosenBasis hv Gamma' i : Gamma'.1) : LatticePoint d)) j) ≤
      ∑ Delta : Superlattice v, ∑ k, ∑ l,
        Int.natAbs
          ((((chosenBasis hv Delta k : Delta.1) : LatticePoint d)) l)
    apply le_trans (Finset.single_le_sum
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j))
    apply le_trans (Finset.single_le_sum
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i))
    exact Finset.single_le_sum
      (f := fun Delta : Superlattice v ↦ ∑ k, ∑ l,
        Int.natAbs
          ((((chosenBasis hv Delta k : Delta.1) : LatticePoint d)) l))
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ Gamma')
  rw [← Int.natCast_natAbs]
  exact_mod_cast hij

end Erdos186.CFP.LatticeBasis
