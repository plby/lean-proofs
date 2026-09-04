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

import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import ErdosProblems.Erdos957.HullEdge

/-!
# Convex-hull core of Levi's triangle theorem

This file isolates the checked finite-dimensional and combinatorial core of
the standard proof of Levi's theorem.  After a selected projective line is
sent to infinity, affine lines are written `y = m*x+b`.  Upper and lower
envelope crossings are useful finite convex-hull certificates, but an
individual crossing does **not** by itself certify a triangular arrangement
face: several consecutive crossings can belong to one unbounded face.  Exact
degree-three extraction is therefore a separate projective/sign-vector step.

The cyclic successor on the coefficient polygon is constructed using the
checked finite gift-wrapping theorem from the Erdős 957 development.  Thus
the distinct-slope, two-dimensional affine theorem has no geometric fields
left as assumptions.  Repeated directions and transport from an arbitrary
selected projective line remain part of the projective extraction layer.
-/

open Set

namespace Erdos735
namespace LeviConvexCore

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The extreme points of the convex hull of a finite spanning set still
span the ambient finite-dimensional real vector space. -/
theorem affineSpan_extremePoints_convexHull_eq_top
    {s : Set V} (hs : s.Finite) (hspan : affineSpan ℝ s = ⊤) :
    affineSpan ℝ ((convexHull ℝ s).extremePoints ℝ) = ⊤ := by
  let C : Set V := convexHull ℝ s
  let X : Set V := C.extremePoints ℝ
  have hKM : closure (convexHull ℝ X) = C := by
    dsimp [C, X]
    exact closure_convexHull_extremePoints (hs.isCompact_convexHull ℝ)
      (convex_convexHull ℝ s)
  have hC_subset : C ⊆ affineSpan ℝ X := by
    rw [← hKM]
    exact closure_minimal
      (convexHull_min (subset_affineSpan ℝ X) (affineSpan ℝ X).convex)
      (affineSpan ℝ X).closed_of_finiteDimensional
  have hs_subset : s ⊆ affineSpan ℝ X :=
    (subset_convexHull ℝ s).trans hC_subset
  apply top_unique
  rw [← hspan]
  exact affineSpan_le.mpr hs_subset

/-- A finite set spanning a real `d`-dimensional vector space has at least
`d+1` extreme points in its convex hull. -/
theorem finrank_add_one_le_card_extremePoints
    {s : Set V} (hs : s.Finite) (hspan : affineSpan ℝ s = ⊤) :
    Module.finrank ℝ V + 1 ≤
      ((convexHull ℝ s).extremePoints ℝ).ncard := by
  let X : Set V := (convexHull ℝ s).extremePoints ℝ
  have hXfin : X.Finite := hs.subset (by
    dsimp [X]
    exact extremePoints_convexHull_subset)
  let : Fintype X := hXfin.fintype
  have hspanX : affineSpan ℝ X = ⊤ := by
    dsimp [X]
    exact affineSpan_extremePoints_convexHull_eq_top hs hspan
  have hXne : X.Nonempty :=
    AffineSubspace.nonempty_of_affineSpan_eq_top ℝ V V hspanX
  let : Nonempty X := hXne.to_subtype
  have hle := finrank_vectorSpan_range_add_one_le ℝ (fun x : X => (x : V))
  have hrange : Set.range (fun x : X => (x : V)) = X := by
    ext x
    simp
  rw [hrange,
    AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top ℝ V V hspanX] at hle
  simpa [Set.ncard] using hle

/-- An affine, nonvertical line, written `y = slope*x+intercept`. -/
structure AffineLine where
  slope : ℝ
  intercept : ℝ
deriving DecidableEq

def AffineLine.eval (L : AffineLine) (x : ℝ) : ℝ :=
  L.slope * x + L.intercept

/-- A finite affine line arrangement in a chart in which all represented
lines have distinct directions. -/
structure AffineArrangement (I : Type*) [Fintype I] where
  line : I → AffineLine
  slope_injective : Function.Injective fun i => (line i).slope

variable {I : Type*} [Fintype I] [DecidableEq I]

def AffineArrangement.coeff (A : AffineArrangement I) (i : I) : ℝ × ℝ :=
  ((A.line i).slope, (A.line i).intercept)

def AffineArrangement.coeffSet (A : AffineArrangement I) : Set (ℝ × ℝ) :=
  Set.range A.coeff

lemma AffineArrangement.coeff_injective (A : AffineArrangement I) :
    Function.Injective A.coeff := by
  intro i j hij
  apply A.slope_injective
  exact congrArg Prod.fst hij

lemma AffineArrangement.coeffSet_finite (A : AffineArrangement I) :
    A.coeffSet.Finite :=
  Set.finite_range A.coeff

def AffineArrangement.crossingX (A : AffineArrangement I) (i j : I) : ℝ :=
  ((A.line j).intercept - (A.line i).intercept) /
    ((A.line i).slope - (A.line j).slope)

def AffineArrangement.crossingY (A : AffineArrangement I) (i j : I) : ℝ :=
  (A.line i).eval (A.crossingX i j)

lemma AffineArrangement.eval_crossingX_eq (A : AffineArrangement I)
    {i j : I} (hij : i ≠ j) :
    (A.line i).eval (A.crossingX i j) =
      (A.line j).eval (A.crossingX i j) := by
  have hslope : (A.line i).slope - (A.line j).slope ≠ 0 := sub_ne_zero.mpr <| by
    intro h
    exact hij (A.slope_injective h)
  dsimp [AffineLine.eval, AffineArrangement.crossingX]
  field_simp
  ring

inductive EnvelopeSide
  | upper
  | lower
deriving DecidableEq

private def finTwoEquivEnvelopeSide : Fin 2 ≃ EnvelopeSide where
  toFun i := if i = 0 then .upper else .lower
  invFun
    | .upper => 0
    | .lower => 1
  left_inv i := by fin_cases i <;> simp
  right_inv s := by cases s <;> simp

instance : Fintype EnvelopeSide :=
  Fintype.ofEquiv (Fin 2) finTwoEquivEnvelopeSide

/-- Two affine lines form an upper or lower envelope crossing.  This is a
necessary local certificate for an unbounded face against the line at
infinity, but it does not record the degree of that face. -/
def AffineArrangement.IsEnvelopePair (A : AffineArrangement I)
    (i j : I) : EnvelopeSide → Prop
  | .upper => i ≠ j ∧ ∀ k,
      (A.line k).eval (A.crossingX i j) ≤ A.crossingY i j
  | .lower => i ≠ j ∧ ∀ k,
      A.crossingY i j ≤ (A.line k).eval (A.crossingX i j)

def AffineArrangement.ExtremeIndex (A : AffineArrangement I) :=
  {i : I // A.coeff i ∈ (convexHull ℝ A.coeffSet).extremePoints ℝ}

instance (A : AffineArrangement I) : Fintype A.ExtremeIndex :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

def AffineArrangement.extremeIndexToPoint (A : AffineArrangement I) :
    A.ExtremeIndex → (convexHull ℝ A.coeffSet).extremePoints ℝ :=
  fun i => ⟨A.coeff i.1, i.property⟩

lemma AffineArrangement.extremeIndexToPoint_bijective (A : AffineArrangement I) :
    Function.Bijective A.extremeIndexToPoint := by
  constructor
  · intro i j hij
    apply Subtype.ext
    apply A.coeff_injective
    change A.coeff i.1 = A.coeff j.1
    exact congrArg Subtype.val hij
  · intro p
    have hp : (p : ℝ × ℝ) ∈ A.coeffSet :=
      extremePoints_convexHull_subset p.property
    rcases hp with ⟨i, hi⟩
    refine ⟨⟨i, ?_⟩, ?_⟩
    · rw [hi]
      exact p.property
    · apply Subtype.ext
      exact hi

noncomputable def AffineArrangement.extremeIndexEquiv (A : AffineArrangement I) :
    A.ExtremeIndex ≃ (convexHull ℝ A.coeffSet).extremePoints ℝ :=
  Equiv.ofBijective A.extremeIndexToPoint A.extremeIndexToPoint_bijective

theorem AffineArrangement.three_le_card_extremeIndex (A : AffineArrangement I)
    (hspan : affineSpan ℝ A.coeffSet = ⊤) :
    3 ≤ Fintype.card A.ExtremeIndex := by
  have h := finrank_add_one_le_card_extremePoints A.coeffSet_finite hspan
  have hthree : 3 ≤ ((convexHull ℝ A.coeffSet).extremePoints ℝ).ncard := by
    simpa using h
  let X : Set (ℝ × ℝ) := (convexHull ℝ A.coeffSet).extremePoints ℝ
  have hXfin : X.Finite := A.coeffSet_finite.subset (by
    dsimp [X]
    exact extremePoints_convexHull_subset)
  let : Fintype X := hXfin.fintype
  calc
    3 ≤ Fintype.card X := by simpa [X, Set.ncard] using hthree
    _ = Fintype.card A.ExtremeIndex :=
      (Fintype.card_congr A.extremeIndexEquiv).symm

/-! ### A checked cyclic hull for the coefficient points -/

/-- The standard linear identification of pairs with the Euclidean plane
used by the gift-wrapping development for Erdős 957. -/
noncomputable def pairPointEquiv : (ℝ × ℝ) ≃L[ℝ] Erdos957.Point :=
  (ContinuousLinearEquiv.piFinTwo ℝ (fun _ : Fin 2 ↦ ℝ)).symm.trans
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm

@[simp] lemma pairPointEquiv_apply_fst (p : ℝ × ℝ) :
    pairPointEquiv p 0 = p.1 := by
  rfl

@[simp] lemma pairPointEquiv_apply_snd (p : ℝ × ℝ) :
    pairPointEquiv p 1 = p.2 := by
  rfl

noncomputable def AffineArrangement.coeffPoint (A : AffineArrangement I)
    (i : I) : Erdos957.Point :=
  pairPointEquiv (A.coeff i)

noncomputable def AffineArrangement.coeffFinset (A : AffineArrangement I) :
    Finset Erdos957.Point :=
  Finset.univ.image A.coeffPoint

lemma AffineArrangement.coeffPoint_injective (A : AffineArrangement I) :
    Function.Injective A.coeffPoint :=
  pairPointEquiv.injective.comp A.coeff_injective

@[simp] lemma AffineArrangement.mem_coeffFinset (A : AffineArrangement I)
    (p : Erdos957.Point) : p ∈ A.coeffFinset ↔ ∃ i, A.coeffPoint i = p := by
  simp [AffineArrangement.coeffFinset]

lemma AffineArrangement.coeffPoint_range (A : AffineArrangement I) :
    Set.range A.coeffPoint = pairPointEquiv '' A.coeffSet := by
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨A.coeff i, ⟨i, rfl⟩, rfl⟩
  · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩

lemma AffineArrangement.affineSpan_coeffPoint_eq_top (A : AffineArrangement I)
    (hspan : affineSpan ℝ A.coeffSet = ⊤) :
    affineSpan ℝ (Set.range A.coeffPoint) = ⊤ := by
  rw [A.coeffPoint_range]
  let f := pairPointEquiv.toLinearEquiv.toAffineEquiv
  change affineSpan ℝ (f '' A.coeffSet) = ⊤
  calc
    affineSpan ℝ (f '' A.coeffSet) =
        (affineSpan ℝ A.coeffSet).map f.toAffineMap := by
          simpa using (AffineSubspace.map_span f.toAffineMap A.coeffSet).symm
    _ = ⊤ := by
      rw [hspan]
      ext p
      simp only [AffineSubspace.mem_map, AffineSubspace.mem_top, true_and]
      constructor
      · intro
        trivial
      · intro
        exact pairPointEquiv.surjective p

lemma AffineArrangement.coe_coeffFinset (A : AffineArrangement I) :
    (A.coeffFinset : Set Erdos957.Point) = Set.range A.coeffPoint := by
  ext p
  simp

/-- A two-dimensional coefficient family has at least three vertices in the
finite hull used by the checked gift-wrapping construction. -/
theorem AffineArrangement.three_le_hullVertexCount (A : AffineArrangement I)
    (hspan : affineSpan ℝ A.coeffSet = ⊤) :
    3 ≤ Erdos957.hullVertexCount A.coeffFinset := by
  have h := finrank_add_one_le_card_extremePoints A.coeffFinset.finite_toSet
    (by rw [A.coe_coeffFinset]; exact A.affineSpan_coeffPoint_eq_top hspan)
  have hfinrank : Module.finrank ℝ Erdos957.Point = 2 := by
    rw [← LinearEquiv.finrank_eq pairPointEquiv.toLinearEquiv]
    simp
  rw [hfinrank] at h
  norm_num at h
  let X : Set Erdos957.Point :=
    (convexHull ℝ (A.coeffFinset : Set Erdos957.Point)).extremePoints ℝ
  have hXfin : X.Finite := A.coeffFinset.finite_toSet.subset (by
    dsimp [X]
    exact extremePoints_convexHull_subset)
  let : Fintype X := hXfin.fintype
  change 3 ≤ X.ncard at h
  have hXcard : X.ncard = Erdos957.hullVertexCount A.coeffFinset := by
    rw [Set.ncard_eq_toFinset_card']
    apply congrArg Finset.card
    ext x
    simp only [Set.mem_toFinset, Erdos957.mem_hullVertices, X]
  rwa [hXcard] at h

/-- The coefficient polygon's cyclic boundary order, constructed rather
than assumed. -/
noncomputable def AffineArrangement.coeffCyclicHullOrder
    (A : AffineArrangement I) (hspan : affineSpan ℝ A.coeffSet = ⊤) :
    Erdos957.CyclicHullOrder A.coeffFinset :=
  Erdos957.cyclicHullOrderOfThree A.coeffFinset
    (A.three_le_hullVertexCount hspan)

/-- Pull a continuous functional on the Euclidean coefficient plane back to
the pair `(slope, intercept)`. -/
noncomputable def pairFunctional (l : Erdos957.Point →L[ℝ] ℝ) :
    (ℝ × ℝ) →L[ℝ] ℝ :=
  l.comp pairPointEquiv.toContinuousLinearMap

lemma pairFunctional_apply (l : Erdos957.Point →L[ℝ] ℝ) (p : ℝ × ℝ) :
    pairFunctional l p = pairFunctional l (1, 0) * p.1 +
      pairFunctional l (0, 1) * p.2 := by
  have hp : p = p.1 • (1, 0) + p.2 • (0, 1) := by
    ext <;> simp
  rw [hp, map_add, map_smul, map_smul]
  simp [mul_comm]

/-- A strict supporting edge of the coefficient hull is exactly an upper or
lower envelope crossing of the corresponding affine lines. -/
lemma AffineArrangement.isEnvelopePair_of_strictSupportingEdge
    (A : AffineArrangement I) {i j : I}
    (h : Erdos957.IsStrictSupportingEdge A.coeffFinset
      (A.coeffPoint i) (A.coeffPoint j)) :
    ∃ side, A.IsEnvelopePair i j side := by
  rcases h with ⟨hpq, l, hl, heq, hmax, _⟩
  have hij : i ≠ j := by
    intro hij
    subst j
    exact hpq rfl
  let L := pairFunctional l
  let a : ℝ := L (1, 0)
  let b : ℝ := L (0, 1)
  have hformula (p : ℝ × ℝ) : L p = a * p.1 + b * p.2 := by
    exact pairFunctional_apply l p
  have heq' : L (A.coeff i) = L (A.coeff j) := heq
  have hb : b ≠ 0 := by
    intro hb
    have ha : a = 0 := by
      rw [hformula, hformula, hb] at heq'
      simp only [zero_mul, add_zero] at heq'
      have hslope : (A.line i).slope ≠ (A.line j).slope := by
        exact fun hs ↦ hij (A.slope_injective hs)
      dsimp [AffineArrangement.coeff] at heq'
      have hprod : a * ((A.line i).slope - (A.line j).slope) = 0 := by
        nlinarith
      rcases mul_eq_zero.mp hprod with ha | hs
      · exact ha
      · exact False.elim (hslope (sub_eq_zero.mp hs))
    have hL : L = 0 := by
      apply ContinuousLinearMap.ext
      intro p
      rw [hformula, ha, hb]
      simp
    apply hl
    apply ContinuousLinearMap.ext
    intro p
    obtain ⟨q, rfl⟩ := pairPointEquiv.surjective p
    change L q = 0
    rw [hL]
    rfl
  have hcross : A.crossingX i j = a / b := by
    rw [hformula, hformula] at heq'
    dsimp [AffineArrangement.coeff, AffineArrangement.crossingX] at heq' ⊢
    have hd : (A.line i).slope - (A.line j).slope ≠ 0 := by
      exact sub_ne_zero.mpr (fun hs ↦ hij (A.slope_injective hs))
    exact (div_eq_div_iff hd hb).2 (by nlinarith)
  by_cases hbpos : 0 < b
  · refine ⟨EnvelopeSide.upper, hij, ?_⟩
    intro k
    have hk := hmax (A.coeffPoint k) (by simp)
    change L (A.coeff k) ≤ L (A.coeff i) at hk
    rw [hformula, hformula] at hk
    dsimp [AffineArrangement.coeff] at hk
    have hab : b * (a / b) = a := by field_simp
    simp only [AffineArrangement.crossingY, AffineLine.eval, hcross]
    apply (mul_le_mul_iff_left₀ hbpos).mp
    calc
      ((A.line k).slope * (a / b) + (A.line k).intercept) * b =
          a * (A.line k).slope + b * (A.line k).intercept := by
            calc
              _ = b * ((A.line k).slope * (a / b) +
                  (A.line k).intercept) := mul_comm _ _
              _ = (b * (a / b)) * (A.line k).slope +
                  b * (A.line k).intercept := by ring
              _ = _ := by rw [hab]
      _ ≤ a * (A.line i).slope + b * (A.line i).intercept := hk
      _ = ((A.line i).slope * (a / b) + (A.line i).intercept) * b := by
            calc
              _ = (b * (a / b)) * (A.line i).slope +
                  b * (A.line i).intercept := by rw [hab]
              _ = b * ((A.line i).slope * (a / b) +
                  (A.line i).intercept) := by ring
              _ = _ := mul_comm _ _
  · have hbneg : b < 0 := lt_of_le_of_ne (le_of_not_gt hbpos) hb
    refine ⟨EnvelopeSide.lower, hij, ?_⟩
    intro k
    have hk := hmax (A.coeffPoint k) (by simp)
    change L (A.coeff k) ≤ L (A.coeff i) at hk
    rw [hformula, hformula] at hk
    dsimp [AffineArrangement.coeff] at hk
    have hab : b * (a / b) = a := by field_simp
    simp only [AffineArrangement.crossingY, AffineLine.eval, hcross]
    apply (mul_le_mul_left_of_neg hbneg).mp
    calc
      b * ((A.line k).slope * (a / b) + (A.line k).intercept) =
          a * (A.line k).slope + b * (A.line k).intercept := by
            calc
              _ = (b * (a / b)) * (A.line k).slope +
                  b * (A.line k).intercept := by ring
              _ = _ := by rw [hab]
      _ ≤ a * (A.line i).slope + b * (A.line i).intercept := hk
      _ = b * ((A.line i).slope * (a / b) + (A.line i).intercept) := by
            calc
              _ = (b * (a / b)) * (A.line i).slope +
                  b * (A.line i).intercept := by rw [hab]
              _ = _ := by ring

lemma successor_pair_injective {α : Type*} [DecidableEq α]
    (next : Equiv.Perm α) (hshort : ∀ x, next (next x) ≠ x) :
    Function.Injective (fun x => ({x, next x} : Finset α)) := by
  intro x y hxy
  change ({x, next x} : Finset α) = {y, next y} at hxy
  have hx : x ∈ ({y, next y} : Finset α) := by rw [← hxy]; simp
  have hx' : x = y ∨ x = next y := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hx
  rcases hx' with h | h
  · exact h
  have hnx : next x ∈ ({y, next y} : Finset α) := by rw [← hxy]; simp
  have hnx' : next x = y ∨ next x = next y := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hnx
  rcases hnx' with h' | h'
  · exfalso
    apply hshort y
    calc
      next (next y) = next x := congrArg next h.symm
      _ = y := h'
  · exact next.injective h'

/-- A combinatorial envelope-pair candidate adjacent to the selected line at
infinity.  The historical name is retained for downstream compatibility;
the structure alone contains neither an actual face nor a degree-three
proof. -/
structure AffineArrangement.InfinityTriangle (A : AffineArrangement I) where
  lineIndices : Finset I
  side : EnvelopeSide
  envelope : ∃ i j, lineIndices = {i, j} ∧ A.IsEnvelopePair i j side

instance (A : AffineArrangement I) : Fintype A.InfinityTriangle :=
  Fintype.ofInjective (fun t => (t.lineIndices, t.side)) <| by
    intro x y hxy
    cases x
    cases y
    simp_all

/-! ### Concrete coefficient-hull envelope candidates -/

/-- The injective coefficient map, bundled as an equivalence with its finite
range. -/
noncomputable def AffineArrangement.coeffPointEquiv (A : AffineArrangement I) :
    I ≃ {p // p ∈ A.coeffFinset} where
  toFun i := ⟨A.coeffPoint i, by simp⟩
  invFun p := Classical.choose (A.mem_coeffFinset p.1 |>.mp p.2)
  left_inv i := by
    apply A.coeffPoint_injective
    exact Classical.choose_spec
      (A.mem_coeffFinset (A.coeffPoint i) |>.mp (by simp))
  right_inv p := by
    apply Subtype.ext
    exact Classical.choose_spec (A.mem_coeffFinset p.1 |>.mp p.2)

/-- The line index belonging to a vertex in the checked cyclic coefficient
hull. -/
noncomputable def AffineArrangement.hullIndex
    (A : AffineArrangement I) (hspan : affineSpan ℝ A.coeffSet = ⊤)
    (t : Fin (Erdos957.hullVertexCount A.coeffFinset)) : I :=
  A.coeffPointEquiv.symm ⟨(A.coeffCyclicHullOrder hspan).vertex t,
    (A.coeffCyclicHullOrder hspan).vertex_mem t⟩

@[simp] lemma AffineArrangement.coeffPoint_hullIndex
    (A : AffineArrangement I) (hspan : affineSpan ℝ A.coeffSet = ⊤)
    (t : Fin (Erdos957.hullVertexCount A.coeffFinset)) :
    A.coeffPoint (A.hullIndex hspan t) =
      (A.coeffCyclicHullOrder hspan).vertex t := by
  exact congrArg Subtype.val (A.coeffPointEquiv.apply_symm_apply
    ⟨(A.coeffCyclicHullOrder hspan).vertex t,
      (A.coeffCyclicHullOrder hspan).vertex_mem t⟩)

lemma AffineArrangement.hullIndex_injective
    (A : AffineArrangement I) (hspan : affineSpan ℝ A.coeffSet = ⊤) :
    Function.Injective (A.hullIndex hspan) := by
  intro t u h
  apply (A.coeffCyclicHullOrder hspan).vertex.injective
  rw [← A.coeffPoint_hullIndex hspan, ← A.coeffPoint_hullIndex hspan, h]

/-- The envelope triangle determined by a consecutive coefficient-hull
edge. -/
noncomputable def AffineArrangement.hullTriangleAt
    (A : AffineArrangement I) (hspan : affineSpan ℝ A.coeffSet = ⊤)
    (t : Fin (Erdos957.hullVertexCount A.coeffFinset)) : A.InfinityTriangle := by
  let P := A.coeffCyclicHullOrder hspan
  let i := A.hullIndex hspan t
  let j := A.hullIndex hspan (Erdos957.cyclicSucc t)
  have hedge : Erdos957.IsStrictSupportingEdge A.coeffFinset
      (A.coeffPoint i) (A.coeffPoint j) := by
    simpa [P, i, j] using P.edge_support t
  let hs := A.isEnvelopePair_of_strictSupportingEdge hedge
  let side := Classical.choose hs
  let hside := Classical.choose_spec hs
  exact ⟨{i, j}, side, i, j, rfl, hside⟩

lemma AffineArrangement.hullTriangleAt_lineIndices
    (A : AffineArrangement I) (hspan : affineSpan ℝ A.coeffSet = ⊤)
    (t : Fin (Erdos957.hullVertexCount A.coeffFinset)) :
    (A.hullTriangleAt hspan t).lineIndices =
      {A.hullIndex hspan t, A.hullIndex hspan (Erdos957.cyclicSucc t)} := by
  simp [AffineArrangement.hullTriangleAt]

lemma AffineArrangement.cyclicSucc_sq_ne
    (A : AffineArrangement I) (hspan : affineSpan ℝ A.coeffSet = ⊤)
    (t : Fin (Erdos957.hullVertexCount A.coeffFinset)) :
    Erdos957.cyclicSucc (Erdos957.cyclicSucc t) ≠ t := by
  intro h
  have ht := (A.coeffCyclicHullOrder hspan).strict_turn t
  rw [h] at ht
  have hzero : Erdos957.orientedTurn
      ((A.coeffCyclicHullOrder hspan).vertex t)
      ((A.coeffCyclicHullOrder hspan).vertex (Erdos957.cyclicSucc t))
      ((A.coeffCyclicHullOrder hspan).vertex t) = 0 := by
    simp [Erdos957.orientedTurn]
    ring
  rw [hzero] at ht
  exact (lt_irrefl 0) ht

lemma AffineArrangement.hullTriangleAt_injective
    (A : AffineArrangement I) (hspan : affineSpan ℝ A.coeffSet = ⊤) :
    Function.Injective (A.hullTriangleAt hspan) := by
  intro t u htu
  have hpairsI := congrArg AffineArrangement.InfinityTriangle.lineIndices htu
  rw [A.hullTriangleAt_lineIndices hspan,
    A.hullTriangleAt_lineIndices hspan] at hpairsI
  let e : Fin (Erdos957.hullVertexCount A.coeffFinset) ↪ I :=
    ⟨A.hullIndex hspan, A.hullIndex_injective hspan⟩
  have hpairs : ({t, Erdos957.cyclicSucc t} : Finset _) =
      {u, Erdos957.cyclicSucc u} := by
    apply Finset.map_injective e
    simpa [e] using hpairsI
  exact successor_pair_injective (finRotate _) (A.cyclicSucc_sq_ne hspan) hpairs

/-- Fully constructed generic affine convex core: the coefficient hull
supplies at least three distinct envelope-pair candidates at infinity.  No
cyclic-hull field remains as an assumption.  Turning these candidates into
distinct degree-three faces requires additional geometry and cannot be
inferred from this theorem alone. -/
theorem AffineArrangement.three_infinityTriangles
    (A : AffineArrangement I) (hspan : affineSpan ℝ A.coeffSet = ⊤) :
    3 ≤ Fintype.card A.InfinityTriangle := by
  calc
    3 ≤ Erdos957.hullVertexCount A.coeffFinset :=
      A.three_le_hullVertexCount hspan
    _ = Fintype.card (Fin (Erdos957.hullVertexCount A.coeffFinset)) := by simp
    _ ≤ Fintype.card A.InfinityTriangle :=
      Fintype.card_le_of_injective (A.hullTriangleAt hspan)
        (A.hullTriangleAt_injective hspan)

/-- Cyclic boundary data for the coefficient polygon. -/
structure AffineArrangement.HullBoundarySuccessor (A : AffineArrangement I) where
  next : Equiv.Perm A.ExtremeIndex
  no_short_cycle : ∀ v, next (next v) ≠ v
  side : A.ExtremeIndex → EnvelopeSide
  envelope : ∀ v, A.IsEnvelopePair v.1 (next v).1 (side v)

noncomputable def AffineArrangement.HullBoundarySuccessor.triangleAt
    {A : AffineArrangement I} (H : A.HullBoundarySuccessor)
    (v : A.ExtremeIndex) : A.InfinityTriangle where
  lineIndices := {v.1, (H.next v).1}
  side := H.side v
  envelope := ⟨v.1, (H.next v).1, rfl, H.envelope v⟩

lemma AffineArrangement.HullBoundarySuccessor.triangleAt_injective
    {A : AffineArrangement I} (H : A.HullBoundarySuccessor) :
    Function.Injective H.triangleAt := by
  classical
  intro v w hvw
  have hedge :
      ({v, H.next v} : Finset A.ExtremeIndex) =
        ({w, H.next w} : Finset A.ExtremeIndex) := by
    let e : A.ExtremeIndex ↪ I := Function.Embedding.subtype _
    apply Finset.map_injective e
    have hedgeI := congrArg AffineArrangement.InfinityTriangle.lineIndices hvw
    dsimp [AffineArrangement.HullBoundarySuccessor.triangleAt] at hedgeI
    simp only [Finset.map_insert, Finset.map_singleton]
    exact hedgeI
  exact successor_pair_injective H.next H.no_short_cycle hedge

/-- The three-candidate conclusion from abstract coefficient-hull boundary
data.  As above, `InfinityTriangle` does not itself certify a face degree. -/
theorem AffineArrangement.three_infinityTriangles_of_hullBoundary
    (A : AffineArrangement I) (hspan : affineSpan ℝ A.coeffSet = ⊤)
    (H : A.HullBoundarySuccessor) :
    3 ≤ Fintype.card A.InfinityTriangle := by
  exact (A.three_le_card_extremeIndex hspan).trans <|
    Fintype.card_le_of_injective H.triangleAt H.triangleAt_injective

end

end LeviConvexCore

/-! ## Stage-4-facing finite formulation -/

/-- Levi's triangle property for a finite line/face arrangement: every line
is incident with at least three triangular faces. -/
def HasLeviTriangleProperty
    (Line Face : Type*) [Fintype Line] [Fintype Face]
    (faceDegree : Face → ℕ) (incident : Line → Face → Prop)
    [DecidableRel incident] : Prop :=
  ∀ ℓ, 3 ≤ (Finset.univ.filter fun f => incident ℓ f ∧ faceDegree f = 3).card

theorem HasLeviTriangleProperty.three_le_adjacent_triangles
    {Line Face : Type*} [Fintype Line] [Fintype Face]
    {faceDegree : Face → ℕ} {incident : Line → Face → Prop}
    [DecidableRel incident]
    (H : HasLeviTriangleProperty Line Face faceDegree incident) (ℓ : Line) :
    3 ≤ (Finset.univ.filter fun f => incident ℓ f ∧ faceDegree f = 3).card :=
  H ℓ

end Erdos735
