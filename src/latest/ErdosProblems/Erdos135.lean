/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 135.
https://www.erdosproblems.com/forum/thread/135

Informal authors:
- Terence Tao

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos135.md
-/
/-
This file formalizes Terence Tao's negative resolution of Erdős Problem 135.

The public theorem constructs, for every `n`, exactly `n` points in the
Euclidean plane such that every four determine at least five distances, while
the total number of distances is `O(n^2 / sqrt (log n))`.

Informal sources:
* T. Tao, "Planar point sets with forbidden 4-point patterns and few
  distinct distances", arXiv:2409.01343 (2024).
* A. Dumitrescu, "Distinct distances in planar point sets with forbidden
  4-point patterns", Discrete Math. 343 (2020), 111967.

The detailed mathematical reconstruction and Leanization plan are in
`tex/135.tex`.
-/

import Mathlib
import ErdosProblems.Erdos448.HalberstamComplete448
import Util.IncidenceGeometry.RichLinesBound
import Util.IncidenceGeometry.UnitDistanceBound
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import BoundedGaps.Maynard.PrimePredecessorMertens

open Filter Finset Real
open scoped BigOperators EuclideanGeometry Real

namespace Erdos135

set_option autoImplicit false

/-- The Euclidean plane used in the public statement. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The nonzero distances determined by a finite point set. -/
noncomputable def distinctDistances (S : Finset Plane) : Finset ℝ :=
  S.offDiag.image fun e => dist e.1 e.2

/-- The local hypothesis in Erdős Problem 135: every four points determine
at least five distances. -/
def HasPhi45 (S : Finset Plane) : Prop :=
  ∀ Q : Finset Plane, Q ⊆ S → Q.card = 4 → 5 ≤ (distinctDistances Q).card

/-- The number of distances in a finite point set. -/
noncomputable def distanceCount (S : Finset Plane) : ℕ :=
  (distinctDistances S).card

lemma distinctDistances_mono {S T : Finset Plane} (hST : S ⊆ T) :
    distinctDistances S ⊆ distinctDistances T := by
  intro d hd
  rcases Finset.mem_image.mp hd with ⟨e, he, rfl⟩
  rcases Finset.mem_offDiag.mp he with ⟨he1, he2, hne⟩
  exact Finset.mem_image.mpr
    ⟨e, Finset.mem_offDiag.mpr ⟨hST he1, hST he2, hne⟩, rfl⟩

lemma distanceCount_mono {S T : Finset Plane} (hST : S ⊆ T) :
    distanceCount S ≤ distanceCount T := by
  exact Finset.card_le_card (distinctDistances_mono hST)

lemma HasPhi45.mono {S T : Finset Plane} (hT : HasPhi45 T) (hST : S ⊆ T) :
    HasPhi45 S := by
  intro Q hQS hQcard
  exact hT Q (hQS.trans hST) hQcard

lemma HasPhi45.of_card_lt_four {S : Finset Plane} (hS : S.card < 4) :
    HasPhi45 S := by
  intro Q hQS hQcard
  have := Finset.card_le_card hQS
  omega

/-- Squared integer distance, used for the finite construction. -/
def intSqDist (x y : ℤ × ℤ) : ℤ :=
  (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2

lemma intSqDist_nonneg (x y : ℤ × ℤ) : 0 ≤ intSqDist x y := by
  dsimp [intSqDist]
  positivity

lemma intSqDist_comm (x y : ℤ × ℤ) : intSqDist x y = intSqDist y x := by
  dsimp [intSqDist]
  ring

lemma intSqDist_eq_zero_iff (x y : ℤ × ℤ) : intSqDist x y = 0 ↔ x = y := by
  constructor
  · intro h
    have h1sq : (x.1 - y.1) ^ 2 = 0 := by
      have hle : (x.1 - y.1) ^ 2 ≤ 0 := by
        simpa [intSqDist] using (show (x.1 - y.1) ^ 2 ≤ intSqDist x y by
          dsimp [intSqDist]
          exact le_add_of_nonneg_right (sq_nonneg _)) |>.trans_eq h
      exact le_antisymm hle (sq_nonneg _)
    have h2sq : (x.2 - y.2) ^ 2 = 0 := by
      have hle : (x.2 - y.2) ^ 2 ≤ 0 := by
        simpa [intSqDist] using (show (x.2 - y.2) ^ 2 ≤ intSqDist x y by
          dsimp [intSqDist]
          exact le_add_of_nonneg_left (sq_nonneg _)) |>.trans_eq h
      exact le_antisymm hle (sq_nonneg _)
    have h1 : x.1 - y.1 = 0 := (sq_eq_zero_iff).mp h1sq
    have h2 : x.2 - y.2 = 0 := (sq_eq_zero_iff).mp h2sq
    exact Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h2)
  · rintro rfl
    simp [intSqDist]

/-- The canonical embedding of integer pairs into the real Euclidean plane. -/
noncomputable def intPoint (x : ℤ × ℤ) : Plane :=
  WithLp.toLp 2 ![(x.1 : ℝ), (x.2 : ℝ)]

lemma intPoint_injective : Function.Injective intPoint := by
  intro x y hxy
  apply Prod.ext
  · have h := congrArg (fun z : Plane => z 0) hxy
    exact_mod_cast (show (x.1 : ℝ) = y.1 by simpa [intPoint] using h)
  · have h := congrArg (fun z : Plane => z 1) hxy
    exact_mod_cast (show (x.2 : ℝ) = y.2 by simpa [intPoint] using h)

lemma dist_intPoint_sq (x y : ℤ × ℤ) :
    dist (intPoint x) (intPoint y) ^ 2 = (intSqDist x y : ℝ) := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq, Real.sq_sqrt]
  · norm_num [intPoint, intSqDist, Fin.sum_univ_two]
  · positivity

lemma dist_intPoint_eq_iff {a b c d : ℤ × ℤ} :
    dist (intPoint a) (intPoint b) = dist (intPoint c) (intPoint d) ↔
      intSqDist a b = intSqDist c d := by
  constructor
  · intro h
    have hs := congrArg (fun z : ℝ => z ^ 2) h
    rw [dist_intPoint_sq, dist_intPoint_sq] at hs
    exact_mod_cast hs
  · intro h
    apply (sq_eq_sq₀ (dist_nonneg : 0 ≤ dist (intPoint a) (intPoint b))
      (dist_nonneg : 0 ≤ dist (intPoint c) (intPoint d))).mp
    rw [dist_intPoint_sq, dist_intPoint_sq]
    exact_mod_cast h

/-! ## Bad quadruples and the integer grid -/

/-- A four-point set which violates `Φ(4,5)`. -/
def IsBadQuad (Q : Finset Plane) : Prop :=
  Q.card = 4 ∧ distanceCount Q ≤ 4

/-- The violating four-subsets of a finite point set. -/
noncomputable def badQuads (S : Finset Plane) : Finset (Finset Plane) :=
  by
    classical
    exact (S.powersetCard 4).filter IsBadQuad

lemma mem_badQuads {S Q : Finset Plane} :
    Q ∈ badQuads S ↔ Q ⊆ S ∧ Q.card = 4 ∧ distanceCount Q ≤ 4 := by
  simp [badQuads, IsBadQuad, and_assoc]

lemma hasPhi45_iff_badQuads_eq_empty {S : Finset Plane} :
    HasPhi45 S ↔ badQuads S = ∅ := by
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro Q hQ
    rw [mem_badQuads] at hQ
    exact (Nat.not_succ_le_self 4) ((h Q hQ.1 hQ.2.1).trans hQ.2.2)
  · intro h Q hQS hQcard
    by_contra hlt
    have hle : distanceCount Q ≤ 4 := by
      simp only [distanceCount] at hlt ⊢
      omega
    have : Q ∈ badQuads S := mem_badQuads.mpr ⟨hQS, hQcard, hle⟩
    simp [h] at this

/-- The integer interval `0, ..., N-1`. -/
noncomputable def intRange (N : ℕ) : Finset ℤ :=
  Finset.Ico 0 (N : ℤ)

/-- The `N × N` integer grid. -/
noncomputable def intGrid (N : ℕ) : Finset (ℤ × ℤ) :=
  (intRange N) ×ˢ (intRange N)

@[simp] lemma card_intRange (N : ℕ) : (intRange N).card = N := by
  simp [intRange]

@[simp] lemma card_intGrid (N : ℕ) : (intGrid N).card = N ^ 2 := by
  simp [intGrid, pow_two]

lemma mem_intGrid {N : ℕ} {x : ℤ × ℤ} :
    x ∈ intGrid N ↔ 0 ≤ x.1 ∧ x.1 < N ∧ 0 ≤ x.2 ∧ x.2 < N := by
  simp only [intGrid, Finset.mem_product, intRange, Finset.mem_Ico]
  omega

/-- The real-plane image of the integer grid. -/
noncomputable def planeGrid (N : ℕ) : Finset Plane :=
  (intGrid N).image intPoint

@[simp] lemma card_planeGrid (N : ℕ) : (planeGrid N).card = N ^ 2 := by
  rw [planeGrid, Finset.card_image_of_injective _ intPoint_injective, card_intGrid]

/-- Four distinct integer points form an additive parallelogram when some
ordering has equal diagonal sums. -/
def ContainsParallelogram (Q : Finset (ℤ × ℤ)) : Prop :=
  ∃ a ∈ Q, ∃ b ∈ Q, ∃ c ∈ Q, ∃ d ∈ Q,
    [a, b, c, d].Nodup ∧ a + d = b + c

/-- A finite integer point set contains no additive parallelogram. -/
def ParallelogramFree (S : Finset (ℤ × ℤ)) : Prop :=
  ∀ Q ⊆ S, Q.card = 4 → ¬ ContainsParallelogram Q

/-- Bad integer quadruples which are not parallelograms.  This direct
definition is equivalent, by Dumitrescu's classification, to the union of
patterns `π₁, π₃, ..., π₈`. -/
noncomputable def otherBadIntQuads (S : Finset (ℤ × ℤ)) :
    Finset (Finset (ℤ × ℤ)) :=
  by
    classical
    exact (S.powersetCard 4).filter fun Q =>
      distanceCount (Q.image intPoint) ≤ 4 ∧ ¬ ContainsParallelogram Q

lemma mem_otherBadIntQuads {S Q : Finset (ℤ × ℤ)} :
    Q ∈ otherBadIntQuads S ↔
      Q ⊆ S ∧ Q.card = 4 ∧ distanceCount (Q.image intPoint) ≤ 4 ∧
        ¬ ContainsParallelogram Q := by
  simp [otherBadIntQuads, and_assoc]

lemma otherBadIntQuads_mono {S T : Finset (ℤ × ℤ)} (hST : S ⊆ T) :
    otherBadIntQuads S ⊆ otherBadIntQuads T := by
  intro Q hQ
  rw [mem_otherBadIntQuads] at hQ ⊢
  exact ⟨hQ.1.trans hST, hQ.2⟩

lemma otherBadIntQuads_subset_powerset {S : Finset (ℤ × ℤ)}
    {Q : Finset (ℤ × ℤ)} (hQ : Q ∈ otherBadIntQuads S) : Q ⊆ S :=
  (mem_otherBadIntQuads.mp hQ).1

lemma card_eq_four_of_mem_otherBadIntQuads {S : Finset (ℤ × ℤ)}
    {Q : Finset (ℤ × ℤ)} (hQ : Q ∈ otherBadIntQuads S) : Q.card = 4 :=
  (mem_otherBadIntQuads.mp hQ).2.1

lemma hasPhi45_image_of_parallelogramFree_of_no_otherBad
    {S : Finset (ℤ × ℤ)} (hpara : ParallelogramFree S)
    (hbad : otherBadIntQuads S = ∅) :
    HasPhi45 (S.image intPoint) := by
  rw [hasPhi45_iff_badQuads_eq_empty]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro R hR
  rw [mem_badQuads] at hR
  obtain ⟨Q, hQS, hQR⟩ :
      ∃ Q ⊆ S, Q.image intPoint = R := by
    refine ⟨S.filter fun x => intPoint x ∈ R, ?_, ?_⟩
    · exact Finset.filter_subset _ _
    · ext z
      constructor
      · intro hz
        rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
        exact (Finset.mem_filter.mp hx).2
      · intro hz
        have hzS : z ∈ S.image intPoint := hR.1 hz
        rcases Finset.mem_image.mp hzS with ⟨x, hxS, rfl⟩
        exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hxS, hz⟩, rfl⟩
  have hQcard : Q.card = 4 := by
    calc
      Q.card = (Q.image intPoint).card :=
        (Finset.card_image_of_injective _ intPoint_injective).symm
      _ = R.card := congrArg Finset.card hQR
      _ = 4 := hR.2.1
  by_cases hQP : ContainsParallelogram Q
  · exact hpara Q hQS hQcard hQP
  · have hmem : Q ∈ otherBadIntQuads S :=
      mem_otherBadIntQuads.mpr ⟨hQS, hQcard, by simpa [hQR] using hR.2.2, hQP⟩
    simp [hbad] at hmem

/-! ## A finite deletion lemma -/

section Deletion

variable {V : Type*} [DecidableEq V]

/-- Members of a bad family which survive inside `R`. -/
def containedBad (H : Finset (Finset V)) (R : Finset V) : Finset (Finset V) :=
  H.filter fun B => B ⊆ R

/-- All vertices which occur in a surviving bad set. -/
def badVertices (H : Finset (Finset V)) (R : Finset V) : Finset V :=
  (containedBad H R).biUnion id

/-- Delete every vertex which occurs in a surviving bad set. -/
def clean (H : Finset (Finset V)) (R : Finset V) : Finset V :=
  R \ badVertices H R

lemma clean_subset (H : Finset (Finset V)) (R : Finset V) :
    clean H R ⊆ R := by
  exact Finset.sdiff_subset

lemma not_subset_clean_of_mem_containedBad {H : Finset (Finset V)}
    {R B : Finset V} (hB : B ∈ containedBad H R) (hBne : B.Nonempty) :
    ¬ B ⊆ clean H R := by
  intro hsub
  obtain ⟨x, hxB⟩ := hBne
  have hxclean := hsub hxB
  have hxvertices : x ∈ badVertices H R := by
    exact Finset.mem_biUnion.mpr ⟨B, hB, hxB⟩
  exact (Finset.mem_sdiff.mp hxclean).2 hxvertices

lemma no_bad_subset_clean {H : Finset (Finset V)} {R B : Finset V}
    (hBH : B ∈ H) (hBne : B.Nonempty) :
    ¬ B ⊆ clean H R := by
  intro hsub
  have hBR : B ⊆ R := hsub.trans (clean_subset H R)
  exact not_subset_clean_of_mem_containedBad
    (show B ∈ containedBad H R by simp [containedBad, hBH, hBR]) hBne hsub

lemma card_badVertices_le_sum (H : Finset (Finset V)) (R : Finset V) :
    (badVertices H R).card ≤ ∑ B ∈ containedBad H R, B.card := by
  unfold badVertices
  exact Finset.card_biUnion_le

lemma card_badVertices_le_mul (H : Finset (Finset V)) (R : Finset V)
    (k : ℕ) (hcard : ∀ B ∈ H, B.card ≤ k) :
    (badVertices H R).card ≤ k * (containedBad H R).card := by
  calc
    (badVertices H R).card ≤ ∑ B ∈ containedBad H R, B.card :=
      card_badVertices_le_sum H R
    _ ≤ ∑ _B ∈ containedBad H R, k := by
      gcongr with B hB
      exact hcard B (Finset.mem_filter.mp hB).1
    _ = k * (containedBad H R).card := by simp [mul_comm]

lemma card_clean_add_loss (H : Finset (Finset V)) (R : Finset V) :
    R.card ≤ (clean H R).card + (badVertices H R).card := by
  calc
    R.card ≤ (clean H R ∪ badVertices H R).card := by
      apply Finset.card_le_card
      intro x hxR
      by_cases hx : x ∈ badVertices H R
      · exact Finset.mem_union_right _ hx
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxR, hx⟩)
    _ ≤ (clean H R).card + (badVertices H R).card :=
      Finset.card_union_le _ _

lemma card_clean_lower_bound (H : Finset (Finset V)) (R : Finset V)
    (k : ℕ) (hcard : ∀ B ∈ H, B.card ≤ k) :
    R.card ≤ (clean H R).card + k * (containedBad H R).card := by
  exact (card_clean_add_loss H R).trans
    (Nat.add_le_add_left (card_badVertices_le_mul H R k hcard) _)

end Deletion

section FiniteAveraging

variable {Ω : Type*}

/-- If the sum of integer scores is at least `L` times the number of
outcomes, some outcome has score at least `L`. -/
lemma exists_score_ge_average {outcomes : Finset Ω} (hout : outcomes.Nonempty)
    (score : Ω → ℤ) (L : ℤ)
    (hsum : (outcomes.card : ℤ) * L ≤ ∑ ω ∈ outcomes, score ω) :
    ∃ ω ∈ outcomes, L ≤ score ω := by
  classical
  by_contra h
  push Not at h
  obtain ⟨ω₀, hω₀⟩ := hout
  have hlt : (∑ ω ∈ outcomes, score ω) < ∑ _ω ∈ outcomes, L := by
    apply Finset.sum_lt_sum
    · intro ω hω
      exact (h ω hω).le
    · exact ⟨ω₀, hω₀, h ω₀ hω₀⟩
  simp only [Finset.sum_const, nsmul_eq_mul] at hlt
  exact (not_lt_of_ge hsum) (by simpa [mul_comm] using hlt)

end FiniteAveraging

/-! ## The affine finite-field parabola -/

/-- The five coefficients in Tao's affine-parabola family. -/
structure ParabolaCoeff (F : Type*) where
  a : F
  b : F
  c : F
  d : F
  e : F

namespace ParabolaCoeff

variable {F : Type*} [Field F]

/-- The two linear rows are independent. -/
def Nondegenerate (ω : ParabolaCoeff F) : Prop :=
  ω.a * ω.d - ω.b * ω.c ≠ 0

/-- The linear form which is squared. -/
def lhs (ω : ParabolaCoeff F) (z : F × F) : F :=
  ω.a * z.1 + ω.b * z.2

/-- The linear part on the right-hand side. -/
def rhsLin (ω : ParabolaCoeff F) (z : F × F) : F :=
  ω.c * z.1 + ω.d * z.2

/-- Membership in the affine parabola. -/
def OnParabola (ω : ParabolaCoeff F) (z : F × F) : Prop :=
  (ω.lhs z) ^ 2 = ω.rhsLin z + ω.e

lemma lhs_add (ω : ParabolaCoeff F) (x y : F × F) :
    ω.lhs (x + y) = ω.lhs x + ω.lhs y := by
  simp [lhs]
  ring

lemma rhsLin_add (ω : ParabolaCoeff F) (x y : F × F) :
    ω.rhsLin (x + y) = ω.rhsLin x + ω.rhsLin y := by
  simp [rhsLin]
  ring

lemma linearCoordinates_injective {ω : ParabolaCoeff F}
    (hω : ω.Nondegenerate) :
    Function.Injective fun z : F × F => (ω.lhs z, ω.rhsLin z) := by
  rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
  have hL : ω.a * x₁ + ω.b * y₁ = ω.a * x₂ + ω.b * y₂ := by
    simpa [lhs] using congrArg Prod.fst h
  have hR : ω.c * x₁ + ω.d * y₁ = ω.c * x₂ + ω.d * y₂ := by
    simpa [rhsLin] using congrArg Prod.snd h
  have hxprod : (ω.a * ω.d - ω.b * ω.c) * (x₁ - x₂) = 0 := by
    linear_combination ω.d * hL - ω.b * hR
  have hyprod : (ω.a * ω.d - ω.b * ω.c) * (y₁ - y₂) = 0 := by
    linear_combination -ω.c * hL + ω.a * hR
  have hx : x₁ = x₂ := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp hxprod).resolve_left hω)
  have hy : y₁ = y₂ := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp hyprod).resolve_left hω)
  exact Prod.ext hx hy

lemma rhsLin_eq_of_onParabola_of_lhs_eq {ω : ParabolaCoeff F}
    {x y : F × F} (hx : ω.OnParabola x) (hy : ω.OnParabola y)
    (hL : ω.lhs x = ω.lhs y) :
    ω.rhsLin x = ω.rhsLin y := by
  dsimp [OnParabola] at hx hy
  rw [hL] at hx
  linear_combination -hx + hy

lemma eq_of_onParabola_of_lhs_eq {ω : ParabolaCoeff F}
    (hω : ω.Nondegenerate) {x y : F × F}
    (hx : ω.OnParabola x) (hy : ω.OnParabola y)
    (hL : ω.lhs x = ω.lhs y) : x = y := by
  apply linearCoordinates_injective hω
  exact Prod.ext hL (rhsLin_eq_of_onParabola_of_lhs_eq hx hy hL)

/-- The identity at the heart of the parabola construction: four distinct
points on a nondegenerate parabola cannot obey a parallelogram relation. -/
lemma no_parallelogram {ω : ParabolaCoeff F} (hω : ω.Nondegenerate)
    (htwo : (2 : F) ≠ 0) {z₀ z₁ z₂ z₃ : F × F}
    (hz₀ : ω.OnParabola z₀) (hz₁ : ω.OnParabola z₁)
    (hz₂ : ω.OnParabola z₂) (hz₃ : ω.OnParabola z₃)
    (h01 : z₀ ≠ z₁) (h02 : z₀ ≠ z₂)
    (hadd : z₀ + z₃ = z₁ + z₂) : False := by
  have hLsum : ω.lhs z₀ + ω.lhs z₃ = ω.lhs z₁ + ω.lhs z₂ := by
    have := congrArg ω.lhs hadd
    simpa only [lhs_add] using this
  have hRsum : ω.rhsLin z₀ + ω.rhsLin z₃ =
      ω.rhsLin z₁ + ω.rhsLin z₂ := by
    have := congrArg ω.rhsLin hadd
    simpa only [rhsLin_add] using this
  have hsqsum : (ω.lhs z₀) ^ 2 + (ω.lhs z₃) ^ 2 =
      (ω.lhs z₁) ^ 2 + (ω.lhs z₂) ^ 2 := by
    dsimp [OnParabola] at hz₀ hz₁ hz₂ hz₃
    rw [hz₀, hz₁, hz₂, hz₃]
    linear_combination hRsum
  have hL3 : ω.lhs z₃ = ω.lhs z₁ + ω.lhs z₂ - ω.lhs z₀ := by
    linear_combination hLsum
  have hprod :
      (2 : F) * (ω.lhs z₁ - ω.lhs z₀) *
        (ω.lhs z₂ - ω.lhs z₀) = 0 := by
    rw [hL3] at hsqsum
    linear_combination hsqsum
  rcases mul_eq_zero.mp hprod with hfirst | h20
  · rcases mul_eq_zero.mp hfirst with htwo' | h10
    · exact htwo htwo'
    · apply h01
      exact (eq_of_onParabola_of_lhs_eq hω hz₀ hz₁ (sub_eq_zero.mp h10).symm)
  · apply h02
    exact (eq_of_onParabola_of_lhs_eq hω hz₀ hz₂ (sub_eq_zero.mp h20).symm)

end ParabolaCoeff

/-! ### Reduction of the integer grid modulo a prime -/

/-- Coordinatewise reduction modulo `p`. -/
def modPoint (p : ℕ) (z : ℤ × ℤ) : ZMod p × ZMod p :=
  ((z.1 : ZMod p), (z.2 : ZMod p))

lemma modPoint_add (p : ℕ) (x y : ℤ × ℤ) :
    modPoint p (x + y) = modPoint p x + modPoint p y := by
  simp [modPoint]

lemma int_eq_of_zmod_cast_eq {p : ℕ} {x y : ℤ}
    (hx0 : 0 ≤ x) (hxp : x < p) (hy0 : 0 ≤ y) (hyp : y < p)
    (hxy : (x : ZMod p) = (y : ZMod p)) : x = y := by
  rw [ZMod.intCast_eq_intCast_iff'] at hxy
  rw [Int.emod_eq_of_lt hx0 hxp, Int.emod_eq_of_lt hy0 hyp] at hxy
  exact hxy

lemma modPoint_injOn_intGrid {N p : ℕ} (hNp : N ≤ p) :
    Set.InjOn (modPoint p) (intGrid N : Set (ℤ × ℤ)) := by
  intro x hx y hy hxy
  change x ∈ intGrid N at hx
  change y ∈ intGrid N at hy
  rw [mem_intGrid] at hx hy
  apply Prod.ext
  · apply int_eq_of_zmod_cast_eq (p := p) hx.1 (by omega) hy.1 (by omega)
    exact congrArg Prod.fst hxy
  · apply int_eq_of_zmod_cast_eq (p := p) hx.2.2.1 (by omega) hy.2.2.1 (by omega)
    exact congrArg Prod.snd hxy

lemma two_ne_zero_zmod {p : ℕ} (hp : 2 < p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hpdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  have := Nat.le_of_dvd (by decide : 0 < 2) hpdiv
  omega

/-- The integer points of the grid lying on one affine parabola modulo `p`. -/
noncomputable def parabolaGrid (p N : ℕ) [Fact p.Prime]
    (ω : ParabolaCoeff (ZMod p)) : Finset (ℤ × ℤ) := by
  classical
  exact (intGrid N).filter fun z => ω.OnParabola (modPoint p z)

lemma mem_parabolaGrid {p N : ℕ} [Fact p.Prime]
    {ω : ParabolaCoeff (ZMod p)} {z : ℤ × ℤ} :
    z ∈ parabolaGrid p N ω ↔
      z ∈ intGrid N ∧ ω.OnParabola (modPoint p z) := by
  simp [parabolaGrid]

lemma parabolaGrid_subset_intGrid {p N : ℕ} [Fact p.Prime]
    (ω : ParabolaCoeff (ZMod p)) :
    parabolaGrid p N ω ⊆ intGrid N := by
  intro z hz
  exact (mem_parabolaGrid.mp hz).1

lemma parabolaGrid_parallelogramFree {p N : ℕ} [Fact p.Prime]
    (hNp : N ≤ p) (hp2 : 2 < p) (ω : ParabolaCoeff (ZMod p))
    (hω : ω.Nondegenerate) :
    ParallelogramFree (parabolaGrid p N ω) := by
  intro Q hQS _hQcard hQpara
  rcases hQpara with ⟨a, haQ, b, hbQ, c, hcQ, d, hdQ, hnodup, hadd⟩
  have haS := hQS haQ
  have hbS := hQS hbQ
  have hcS := hQS hcQ
  have hdS := hQS hdQ
  have ha := mem_parabolaGrid.mp haS
  have hb := mem_parabolaGrid.mp hbS
  have hc := mem_parabolaGrid.mp hcS
  have hd := mem_parabolaGrid.mp hdS
  have hinj := modPoint_injOn_intGrid hNp
  have hab : modPoint p a ≠ modPoint p b := by
    intro heq
    have : a = b := hinj ha.1 hb.1 heq
    subst b
    simp at hnodup
  have hac : modPoint p a ≠ modPoint p c := by
    intro heq
    have : a = c := hinj ha.1 hc.1 heq
    subst c
    simp at hnodup
  apply ParabolaCoeff.no_parallelogram hω (two_ne_zero_zmod hp2)
      ha.2 hb.2 hc.2 hd.2 hab hac
  simpa only [modPoint_add] using congrArg (modPoint p) hadd

/-! ### The finite outcome space -/

/-- We parametrize the nondegenerate coefficient space by an invertible
`2 × 2` matrix and the free constant coefficient. -/
abbrev ParabolaOutcome (p : ℕ) [Fact p.Prime] :=
  Matrix.GeneralLinearGroup (Fin 2) (ZMod p) × ZMod p

/-- Read an outcome as the five coefficients `(a,b,c,d,e)`. -/
def outcomeCoeff {p : ℕ} [Fact p.Prime] (o : ParabolaOutcome p) :
    ParabolaCoeff (ZMod p) where
  a := o.1 0 0
  b := o.1 0 1
  c := o.1 1 0
  d := o.1 1 1
  e := o.2

lemma outcomeCoeff_nondegenerate {p : ℕ} [Fact p.Prime]
    (o : ParabolaOutcome p) : (outcomeCoeff o).Nondegenerate := by
  change o.1 0 0 * o.1 1 1 - o.1 0 1 * o.1 1 0 ≠ 0
  simpa [Matrix.det_fin_two] using o.1.det_ne_zero

lemma card_parabolaOutcome (p : ℕ) [Fact p.Prime] :
    Fintype.card (ParabolaOutcome p) = p * (p ^ 2 - 1) * (p ^ 2 - p) := by
  rw [Fintype.card_prod, ZMod.card]
  rw [← Nat.card_eq_fintype_card, Matrix.card_GL_field]
  simp [Fin.prod_univ_two]
  ring

lemma card_GL_two (p : ℕ) [Fact p.Prime] :
    Fintype.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) =
      (p ^ 2 - 1) * (p ^ 2 - p) := by
  rw [← Nat.card_eq_fintype_card, Matrix.card_GL_field]
  simp [Fin.prod_univ_two]

/-- Outcomes whose curve contains a fixed finite-field point. -/
noncomputable def pointOutcomes {p : ℕ} [Fact p.Prime]
    (z : ZMod p × ZMod p) : Finset (ParabolaOutcome p) := by
  classical
  exact Finset.univ.filter fun o => (outcomeCoeff o).OnParabola z

lemma mem_pointOutcomes {p : ℕ} [Fact p.Prime]
    {z : ZMod p × ZMod p} {o : ParabolaOutcome p} :
    o ∈ pointOutcomes z ↔ (outcomeCoeff o).OnParabola z := by
  simp [pointOutcomes]

/-- Once the invertible matrix is fixed, the equation at one point uniquely
determines `e`. -/
def pointOutcomeEquiv {p : ℕ} [Fact p.Prime] (z : ZMod p × ZMod p) :
    {o : ParabolaOutcome p // (outcomeCoeff o).OnParabola z} ≃
      Matrix.GeneralLinearGroup (Fin 2) (ZMod p) where
  toFun o := o.1.1
  invFun g :=
    let ω : ParabolaCoeff (ZMod p) := {
      a := g 0 0, b := g 0 1, c := g 1 0, d := g 1 1, e := 0 }
    ⟨(g, ω.lhs z ^ 2 - ω.rhsLin z), by
      change ω.lhs z ^ 2 = ω.rhsLin z + (ω.lhs z ^ 2 - ω.rhsLin z)
      ring⟩
  left_inv o := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change
        (outcomeCoeff o.1).lhs z ^ 2 - (outcomeCoeff o.1).rhsLin z = o.1.2
      have ho :
          (outcomeCoeff o.1).lhs z ^ 2 =
            (outcomeCoeff o.1).rhsLin z + o.1.2 := by
        have ho' := o.2
        change
          (outcomeCoeff o.1).lhs z ^ 2 =
            (outcomeCoeff o.1).rhsLin z + o.1.2 at ho'
        exact ho'
      linear_combination ho
  right_inv _g := rfl

lemma card_pointOutcomes {p : ℕ} [Fact p.Prime]
    (z : ZMod p × ZMod p) :
    (pointOutcomes z).card =
      Fintype.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) := by
  classical
  calc
    (pointOutcomes z).card = Fintype.card ↑(pointOutcomes z) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card {o : ParabolaOutcome p // (outcomeCoeff o).OnParabola z} :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun _ => mem_pointOutcomes)
    _ = Fintype.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :=
      Fintype.card_congr (pointOutcomeEquiv z)

/-! ### A normalized four-point equation -/

/-- The quadratic obstruction obtained after sending three noncollinear
points to `(0,0)`, `(1,0)`, and `(0,1)`. -/
noncomputable def normalizedFourPoly {F : Type*} [CommRing F]
    (s t : F) : MvPolynomial (Fin 2) F :=
  MvPolynomial.C (s * (s - 1)) * MvPolynomial.X 0 ^ 2 +
    MvPolynomial.C (2 * s * t) * MvPolynomial.X 0 * MvPolynomial.X 1 +
    MvPolynomial.C (t * (t - 1)) * MvPolynomial.X 1 ^ 2

lemma eval_normalizedFourPoly {F : Type*} [CommRing F]
    (s t A B : F) :
    MvPolynomial.eval ![A, B] (normalizedFourPoly s t) =
      s * (s - 1) * A ^ 2 + 2 * s * t * A * B +
        t * (t - 1) * B ^ 2 := by
  simp [normalizedFourPoly]

lemma normalizedFourPoly_ne_zero {F : Type*} [Field F]
    (htwo : (2 : F) ≠ 0) {s t : F}
    (h0 : (s, t) ≠ (0, 0)) (h1 : (s, t) ≠ (1, 0))
    (h2 : (s, t) ≠ (0, 1)) :
    normalizedFourPoly s t ≠ 0 := by
  intro hpoly
  have hs : s * (s - 1) = 0 := by
    have h := congrArg (MvPolynomial.eval ![(1 : F), (0 : F)]) hpoly
    simpa [eval_normalizedFourPoly] using h
  have ht : t * (t - 1) = 0 := by
    have h := congrArg (MvPolynomial.eval ![(0 : F), (1 : F)]) hpoly
    simpa [eval_normalizedFourPoly] using h
  have hst : 2 * s * t = 0 := by
    have h := congrArg (MvPolynomial.eval ![(1 : F), (1 : F)]) hpoly
    rw [eval_normalizedFourPoly] at h
    simpa [hs, ht] using h
  rcases mul_eq_zero.mp hs with hs0 | hs1
  · rcases mul_eq_zero.mp ht with ht0 | ht1
    · exact h0 (Prod.ext hs0 ht0)
    · exact h2 (Prod.ext hs0 (sub_eq_zero.mp ht1))
  · have hs_one : s = 1 := sub_eq_zero.mp hs1
    rcases mul_eq_zero.mp ht with ht0 | ht1
    · exact h1 (Prod.ext hs_one ht0)
    · have ht_one : t = 1 := sub_eq_zero.mp ht1
      have : (2 : F) = 0 := by
        simpa [hs_one, ht_one] using hst
      exact htwo this

lemma normalizedFourPoly_totalDegree_le {F : Type*} [Field F]
    (s t : F) : (normalizedFourPoly s t).totalDegree ≤ 2 := by
  let q₀ : MvPolynomial (Fin 2) F :=
    MvPolynomial.C (s * (s - 1)) * MvPolynomial.X 0 ^ 2
  let q₁ : MvPolynomial (Fin 2) F :=
    MvPolynomial.C (2 * s * t) * MvPolynomial.X 0 * MvPolynomial.X 1
  let q₂ : MvPolynomial (Fin 2) F :=
    MvPolynomial.C (t * (t - 1)) * MvPolynomial.X 1 ^ 2
  have hpow (i : Fin 2) :
      (MvPolynomial.X i ^ 2 : MvPolynomial (Fin 2) F).totalDegree ≤ 2 := by
    simp
  have hxy :
      (MvPolynomial.X 0 * MvPolynomial.X 1 :
        MvPolynomial (Fin 2) F).totalDegree ≤ 2 := by
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  have hq₀ : q₀.totalDegree ≤ 2 := by
    change
      (MvPolynomial.C (s * (s - 1)) *
          (MvPolynomial.X 0 : MvPolynomial (Fin 2) F) ^ 2).totalDegree ≤ 2
    calc
      (MvPolynomial.C (s * (s - 1)) *
          (MvPolynomial.X 0 : MvPolynomial (Fin 2) F) ^ 2).totalDegree
          ≤ (MvPolynomial.C (s * (s - 1)) : MvPolynomial (Fin 2) F).totalDegree +
              ((MvPolynomial.X 0 : MvPolynomial (Fin 2) F) ^ 2).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 0 + 2 := Nat.add_le_add
        (le_of_eq (MvPolynomial.totalDegree_C (s * (s - 1)))) (hpow 0)
      _ = 2 := by omega
  have hq₁ : q₁.totalDegree ≤ 2 := by
    change
      (MvPolynomial.C (2 * s * t) * MvPolynomial.X 0 *
          MvPolynomial.X 1 : MvPolynomial (Fin 2) F).totalDegree ≤ 2
    calc
      (MvPolynomial.C (2 * s * t) * MvPolynomial.X 0 *
          MvPolynomial.X 1 : MvPolynomial (Fin 2) F).totalDegree
          ≤ (MvPolynomial.C (2 * s * t) * MvPolynomial.X 0 :
                MvPolynomial (Fin 2) F).totalDegree +
              (MvPolynomial.X 1 : MvPolynomial (Fin 2) F).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ ((MvPolynomial.C (2 * s * t) : MvPolynomial (Fin 2) F).totalDegree +
              (MvPolynomial.X 0 : MvPolynomial (Fin 2) F).totalDegree) +
            (MvPolynomial.X 1 : MvPolynomial (Fin 2) F).totalDegree :=
        Nat.add_le_add_right (MvPolynomial.totalDegree_mul _ _)
          (MvPolynomial.X 1 : MvPolynomial (Fin 2) F).totalDegree
      _ = 2 := by
        rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X,
          MvPolynomial.totalDegree_X]
  have hq₂ : q₂.totalDegree ≤ 2 := by
    change
      (MvPolynomial.C (t * (t - 1)) *
          (MvPolynomial.X 1 : MvPolynomial (Fin 2) F) ^ 2).totalDegree ≤ 2
    calc
      (MvPolynomial.C (t * (t - 1)) *
          (MvPolynomial.X 1 : MvPolynomial (Fin 2) F) ^ 2).totalDegree
          ≤ (MvPolynomial.C (t * (t - 1)) : MvPolynomial (Fin 2) F).totalDegree +
              ((MvPolynomial.X 1 : MvPolynomial (Fin 2) F) ^ 2).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 0 + 2 := Nat.add_le_add
        (le_of_eq (MvPolynomial.totalDegree_C (t * (t - 1)))) (hpow 1)
      _ = 2 := by omega
  change (q₀ + q₁ + q₂).totalDegree ≤ 2
  exact (MvPolynomial.totalDegree_add _ _).trans
    (max_le ((MvPolynomial.totalDegree_add _ _).trans (max_le hq₀ hq₁)) hq₂)

/-- Schwartz--Zippel gives at most `2p` possible first-row coordinate
pairs for a genuine fourth point. -/
lemma card_normalizedFourZeros_le {p : ℕ} [Fact p.Prime]
    (hp : 0 < p) (htwo : (2 : ZMod p) ≠ 0) {s t : ZMod p}
    (h0 : (s, t) ≠ (0, 0)) (h1 : (s, t) ≠ (1, 0))
    (h2 : (s, t) ≠ (0, 1)) :
    ((Fintype.piFinset fun _ : Fin 2 => (Finset.univ : Finset (ZMod p))).filter
      fun x => MvPolynomial.eval x (normalizedFourPoly s t) = 0).card ≤ 2 * p := by
  classical
  have hsz := MvPolynomial.schwartz_zippel_totalDegree
    (normalizedFourPoly_ne_zero htwo h0 h1 h2)
    (Finset.univ : Finset (ZMod p))
  have hdeg := normalizedFourPoly_totalDegree_le s t
  simp only [Finset.card_univ, ZMod.card] at hsz
  have hpq : (0 : ℚ≥0) < (p : ℚ≥0) := by exact_mod_cast hp
  have hratio :
      (((Fintype.piFinset fun _ : Fin 2 =>
          (Finset.univ : Finset (ZMod p))).filter fun x =>
            MvPolynomial.eval x (normalizedFourPoly s t) = 0).card : ℚ≥0) /
          (p : ℚ≥0) ^ 2 ≤ 2 / (p : ℚ≥0) := by
    exact hsz.trans (div_le_div_of_nonneg_right (by exact_mod_cast hdeg) hpq.le)
  have hcast :
      (((Fintype.piFinset fun _ : Fin 2 =>
          (Finset.univ : Finset (ZMod p))).filter fun x =>
            MvPolynomial.eval x (normalizedFourPoly s t) = 0).card : ℚ≥0) ≤
        (2 * p : ℕ) := by
    calc
      _ =
          ((((Fintype.piFinset fun _ : Fin 2 =>
              (Finset.univ : Finset (ZMod p))).filter fun x =>
                MvPolynomial.eval x (normalizedFourPoly s t) = 0).card : ℚ≥0) /
              (p : ℚ≥0) ^ 2) * (p : ℚ≥0) ^ 2 := by field_simp
      _ ≤ (2 / (p : ℚ≥0)) * (p : ℚ≥0) ^ 2 :=
        mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = (2 : ℚ≥0) * (p : ℚ≥0) := by field_simp
      _ = (2 * p : ℕ) := by norm_num
  exact_mod_cast hcast

/-! ### Affine normalization of four points -/

/-- The determinant of two coordinate vectors. -/
def pairDet {F : Type*} [CommRing F] (v w : F × F) : F :=
  v.1 * w.2 - v.2 * w.1

lemma exists_smul_of_pairDet_eq_zero {F : Type*} [Field F]
    {v w : F × F} (hv : v ≠ 0) (hdet : pairDet v w = 0) :
    ∃ k : F, w = k • v := by
  by_cases hv₁ : v.1 = 0
  · have hv₂ : v.2 ≠ 0 := by
      intro hv₂
      apply hv
      exact Prod.ext hv₁ hv₂
    have hw₁ : w.1 = 0 := by
      dsimp [pairDet] at hdet
      rw [hv₁, zero_mul, zero_sub, neg_eq_zero, mul_eq_zero] at hdet
      exact hdet.resolve_left hv₂
    refine ⟨w.2 / v.2, Prod.ext ?_ ?_⟩
    · simp [hw₁, hv₁]
    · simp [hv₂]
  · refine ⟨w.1 / v.1, Prod.ext ?_ ?_⟩
    · simp [hv₁]
    · dsimp [pairDet] at hdet
      dsimp
      field_simp
      linear_combination hdet

lemma row_eq_zero_of_pairDet_ne_zero {F : Type*} [Field F]
    {v₁ v₂ : F × F} (hdet : pairDet v₁ v₂ ≠ 0) {a b : F}
    (h₁ : a * v₁.1 + b * v₁.2 = 0)
    (h₂ : a * v₂.1 + b * v₂.2 = 0) : a = 0 ∧ b = 0 := by
  have ha : pairDet v₁ v₂ * a = 0 := by
    dsimp [pairDet]
    linear_combination v₂.2 * h₁ - v₁.2 * h₂
  have hb : pairDet v₁ v₂ * b = 0 := by
    dsimp [pairDet]
    linear_combination -v₂.1 * h₁ + v₁.1 * h₂
  exact ⟨(mul_eq_zero.mp ha).resolve_left hdet,
    (mul_eq_zero.mp hb).resolve_left hdet⟩

namespace ParabolaCoeff

variable {F : Type*} [Field F]

/-- Three noncollinear incidences and the values of the first linear row on
the two basis differences determine all five coefficients. -/
lemma eq_of_three_on_of_basis_lhs_eq {ω η : ParabolaCoeff F}
    {z₀ z₁ z₂ : F × F} (hdet : pairDet (z₁ - z₀) (z₂ - z₀) ≠ 0)
    (hω₀ : ω.OnParabola z₀) (hω₁ : ω.OnParabola z₁)
    (hω₂ : ω.OnParabola z₂) (hη₀ : η.OnParabola z₀)
    (hη₁ : η.OnParabola z₁) (hη₂ : η.OnParabola z₂)
    (hL₁ : ω.lhs (z₁ - z₀) = η.lhs (z₁ - z₀))
    (hL₂ : ω.lhs (z₂ - z₀) = η.lhs (z₂ - z₀)) : ω = η := by
  have hab := row_eq_zero_of_pairDet_ne_zero hdet
    (a := ω.a - η.a) (b := ω.b - η.b)
    (by
      dsimp [lhs] at hL₁ ⊢
      linear_combination hL₁)
    (by
      dsimp [lhs] at hL₂ ⊢
      linear_combination hL₂)
  have ha : ω.a = η.a := sub_eq_zero.mp hab.1
  have hb : ω.b = η.b := sub_eq_zero.mp hab.2
  have eω₀ := hω₀
  have eω₁ := hω₁
  have eω₂ := hω₂
  have eη₀ := hη₀
  have eη₁ := hη₁
  have eη₂ := hη₂
  dsimp [OnParabola, lhs, rhsLin] at eω₀ eω₁ eω₂ eη₀ eη₁ eη₂
  rw [ha, hb] at eω₀ eω₁ eω₂
  have hcd₁ :
      (ω.c - η.c) * (z₁ - z₀).1 + (ω.d - η.d) * (z₁ - z₀).2 = 0 := by
    change (ω.c - η.c) * (z₁.1 - z₀.1) +
      (ω.d - η.d) * (z₁.2 - z₀.2) = 0
    linear_combination -eω₁ + eω₀ + eη₁ - eη₀
  have hcd₂ :
      (ω.c - η.c) * (z₂ - z₀).1 + (ω.d - η.d) * (z₂ - z₀).2 = 0 := by
    change (ω.c - η.c) * (z₂.1 - z₀.1) +
      (ω.d - η.d) * (z₂.2 - z₀.2) = 0
    linear_combination -eω₂ + eω₀ + eη₂ - eη₀
  have hcd := row_eq_zero_of_pairDet_ne_zero hdet hcd₁ hcd₂
  have hc : ω.c = η.c := sub_eq_zero.mp hcd.1
  have hd : ω.d = η.d := sub_eq_zero.mp hcd.2
  have he : ω.e = η.e := by
    rw [hc, hd] at eω₀
    linear_combination -eω₀ + eη₀
  cases ω
  cases η
  simp_all

end ParabolaCoeff

/-- The first-row coordinates relative to an affine basis. -/
def basisLhsCoords {F : Type*} [Field F] (ω : ParabolaCoeff F)
    (z₀ z₁ z₂ : F × F) : Fin 2 → F :=
  ![ω.lhs (z₁ - z₀), ω.lhs (z₂ - z₀)]

lemma outcomeCoeff_injective {p : ℕ} [Fact p.Prime] :
    Function.Injective (outcomeCoeff : ParabolaOutcome p → ParabolaCoeff (ZMod p)) := by
  intro o q h
  apply Prod.ext
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact congrArg ParabolaCoeff.a h
    · exact congrArg ParabolaCoeff.b h
    · exact congrArg ParabolaCoeff.c h
    · exact congrArg ParabolaCoeff.d h
  · exact congrArg ParabolaCoeff.e h

/-- Barycentric coordinates of `z₃-z₀` in the ordered basis
`(z₁-z₀,z₂-z₀)`. -/
def affineCoordS {F : Type*} [Field F]
    (z₀ z₁ z₂ z₃ : F × F) : F :=
  pairDet (z₃ - z₀) (z₂ - z₀) / pairDet (z₁ - z₀) (z₂ - z₀)

def affineCoordT {F : Type*} [Field F]
    (z₀ z₁ z₂ z₃ : F × F) : F :=
  pairDet (z₁ - z₀) (z₃ - z₀) / pairDet (z₁ - z₀) (z₂ - z₀)

lemma affine_coord_decomposition {F : Type*} [Field F]
    {z₀ z₁ z₂ z₃ : F × F}
    (hdet : pairDet (z₁ - z₀) (z₂ - z₀) ≠ 0) :
    z₃ - z₀ = affineCoordS z₀ z₁ z₂ z₃ • (z₁ - z₀) +
      affineCoordT z₀ z₁ z₂ z₃ • (z₂ - z₀) := by
  apply Prod.ext
  · change z₃.1 - z₀.1 =
      (pairDet (z₃ - z₀) (z₂ - z₀) /
          pairDet (z₁ - z₀) (z₂ - z₀)) * (z₁.1 - z₀.1) +
        (pairDet (z₁ - z₀) (z₃ - z₀) /
          pairDet (z₁ - z₀) (z₂ - z₀)) * (z₂.1 - z₀.1)
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
    apply (eq_div_iff hdet).2
    simp only [pairDet, Prod.fst_sub, Prod.snd_sub]
    ring
  · change z₃.2 - z₀.2 =
      (pairDet (z₃ - z₀) (z₂ - z₀) /
          pairDet (z₁ - z₀) (z₂ - z₀)) * (z₁.2 - z₀.2) +
        (pairDet (z₁ - z₀) (z₃ - z₀) /
          pairDet (z₁ - z₀) (z₂ - z₀)) * (z₂.2 - z₀.2)
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
    apply (eq_div_iff hdet).2
    simp only [pairDet, Prod.fst_sub, Prod.snd_sub]
    ring

lemma affine_coords_distinct {F : Type*} [Field F]
    {z₀ z₁ z₂ z₃ : F × F}
    (hdet : pairDet (z₁ - z₀) (z₂ - z₀) ≠ 0)
    (h30 : z₃ ≠ z₀) (h31 : z₃ ≠ z₁) (h32 : z₃ ≠ z₂) :
    (affineCoordS z₀ z₁ z₂ z₃, affineCoordT z₀ z₁ z₂ z₃) ≠ (0, 0) ∧
      (affineCoordS z₀ z₁ z₂ z₃, affineCoordT z₀ z₁ z₂ z₃) ≠ (1, 0) ∧
      (affineCoordS z₀ z₁ z₂ z₃, affineCoordT z₀ z₁ z₂ z₃) ≠ (0, 1) := by
  have hdecomp := affine_coord_decomposition (z₃ := z₃) hdet
  constructor
  · intro h
    have hs := congrArg Prod.fst h
    have ht := congrArg Prod.snd h
    simp only at hs ht
    rw [hs, ht] at hdecomp
    simp only [zero_smul, zero_add] at hdecomp
    exact h30 (sub_eq_zero.mp hdecomp)
  constructor
  · intro h
    have hs := congrArg Prod.fst h
    have ht := congrArg Prod.snd h
    simp only at hs ht
    rw [hs, ht] at hdecomp
    simp only [one_smul, zero_smul, add_zero] at hdecomp
    exact h31 (sub_left_inj.mp hdecomp)
  · intro h
    have hs := congrArg Prod.fst h
    have ht := congrArg Prod.snd h
    simp only at hs ht
    rw [hs, ht] at hdecomp
    simp only [zero_smul, one_smul, zero_add] at hdecomp
    exact h32 (sub_left_inj.mp hdecomp)

namespace ParabolaCoeff

variable {F : Type*} [Field F]

lemma lhs_sub (ω : ParabolaCoeff F) (x y : F × F) :
    ω.lhs (x - y) = ω.lhs x - ω.lhs y := by
  simp [lhs]
  ring

lemma rhsLin_sub (ω : ParabolaCoeff F) (x y : F × F) :
    ω.rhsLin (x - y) = ω.rhsLin x - ω.rhsLin y := by
  simp [rhsLin]
  ring

lemma lhs_smul (ω : ParabolaCoeff F) (k : F) (x : F × F) :
    ω.lhs (k • x) = k * ω.lhs x := by
  simp [lhs]
  ring

lemma rhsLin_smul (ω : ParabolaCoeff F) (k : F) (x : F × F) :
    ω.rhsLin (k • x) = k * ω.rhsLin x := by
  simp [rhsLin]
  ring

lemma line_third_parameter {ω : ParabolaCoeff F} {x v : F × F} {k : F}
    (hx : ω.OnParabola x) (h₁ : ω.OnParabola (x + v))
    (hk : ω.OnParabola (x + k • v)) :
    k * (k - 1) * (ω.lhs v) ^ 2 = 0 := by
  have h₁' :
      (ω.lhs x + ω.lhs v) ^ 2 =
        ω.rhsLin x + ω.rhsLin v + ω.e := by
    simpa only [OnParabola, lhs_add, rhsLin_add, add_assoc] using h₁
  have hk' :
      (ω.lhs x + k * ω.lhs v) ^ 2 =
        ω.rhsLin x + k * ω.rhsLin v + ω.e := by
    simpa only [OnParabola, lhs_add, rhsLin_add, lhs_smul, rhsLin_smul,
      add_assoc] using hk
  dsimp [OnParabola] at hx
  linear_combination hk' - k * h₁' + (k - 1) * hx

/-- A nondegenerate affine parabola over a field has no collinear triple of
distinct points. -/
lemma no_three_collinear {ω : ParabolaCoeff F} (hω : ω.Nondegenerate)
    {x y z : F × F} (hx : ω.OnParabola x) (hy : ω.OnParabola y)
    (hz : ω.OnParabola z) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    pairDet (y - x) (z - x) ≠ 0 := by
  intro hdet
  have hv : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  obtain ⟨k, hk⟩ := exists_smul_of_pairDet_eq_zero hv hdet
  have hy' : ω.OnParabola (x + (y - x)) := by simpa using hy
  have hz' : ω.OnParabola (x + k • (y - x)) := by
    have : x + k • (y - x) = z := by
      rw [← hk]
      simp
    simpa [this] using hz
  have hk0 : k ≠ 0 := by
    intro hk0
    apply hxz
    have : z - x = 0 := by simpa [hk0] using hk
    exact (sub_eq_zero.mp this).symm
  have hk1 : k - 1 ≠ 0 := by
    intro hk1
    have hkone : k = 1 := sub_eq_zero.mp hk1
    apply hyz
    have : z - x = y - x := by simpa [hkone] using hk
    exact sub_left_inj.mp this.symm
  have hLv : ω.lhs (y - x) ≠ 0 := by
    intro hzero
    apply hxy
    apply eq_of_onParabola_of_lhs_eq hω hx hy
    rw [lhs_sub] at hzero
    exact (sub_eq_zero.mp hzero).symm
  have hprod := line_third_parameter hx hy' hz'
  rcases mul_eq_zero.mp hprod with hleft | hsq
  · exact hk1 ((mul_eq_zero.mp hleft).resolve_left hk0)
  · exact hLv (sq_eq_zero_iff.mp hsq)

/-- Four incidences, expressed in the affine basis determined by the first
three points, satisfy the normalized quadratic. -/
lemma normalized_equation_of_four {ω : ParabolaCoeff F}
    {z₀ z₁ z₂ z₃ : F × F} {s t : F}
    (hz₀ : ω.OnParabola z₀) (hz₁ : ω.OnParabola z₁)
    (hz₂ : ω.OnParabola z₂) (hz₃ : ω.OnParabola z₃)
    (hdecomp : z₃ - z₀ = s • (z₁ - z₀) + t • (z₂ - z₀)) :
    MvPolynomial.eval (basisLhsCoords ω z₀ z₁ z₂)
      (normalizedFourPoly s t) = 0 := by
  let v₁ := z₁ - z₀
  let v₂ := z₂ - z₀
  have hz₁eq : z₁ = z₀ + v₁ := by simp [v₁]
  have hz₂eq : z₂ = z₀ + v₂ := by simp [v₂]
  have hz₃eq : z₃ = (z₀ + s • v₁) + t • v₂ := by
    calc
      z₃ = z₀ + (z₃ - z₀) := by abel
      _ = z₀ + (s • v₁ + t • v₂) := by
        simpa [v₁, v₂] using congrArg (z₀ + ·) hdecomp
      _ = (z₀ + s • v₁) + t • v₂ := by abel
  have h₀' : (ω.lhs z₀) ^ 2 = ω.rhsLin z₀ + ω.e := hz₀
  have h₁' :
      (ω.lhs z₀ + ω.lhs v₁) ^ 2 =
        ω.rhsLin z₀ + ω.rhsLin v₁ + ω.e := by
    rw [hz₁eq] at hz₁
    simpa only [OnParabola, lhs_add, rhsLin_add, add_assoc] using hz₁
  have h₂' :
      (ω.lhs z₀ + ω.lhs v₂) ^ 2 =
        ω.rhsLin z₀ + ω.rhsLin v₂ + ω.e := by
    rw [hz₂eq] at hz₂
    simpa only [OnParabola, lhs_add, rhsLin_add, add_assoc] using hz₂
  have h₃' :
      (ω.lhs z₀ + s * ω.lhs v₁ + t * ω.lhs v₂) ^ 2 =
        ω.rhsLin z₀ + s * ω.rhsLin v₁ + t * ω.rhsLin v₂ + ω.e := by
    rw [hz₃eq] at hz₃
    simpa only [OnParabola, lhs_add, rhsLin_add, lhs_smul, rhsLin_smul,
      add_assoc] using hz₃
  change MvPolynomial.eval ![ω.lhs v₁, ω.lhs v₂]
      (normalizedFourPoly s t) = 0
  rw [eval_normalizedFourPoly]
  linear_combination h₃' - s * h₁' - t * h₂' + (s + t - 1) * h₀'

end ParabolaCoeff

/-- Outcomes whose affine parabola contains four specified finite-field
points. -/
noncomputable def fourOutcomes {p : ℕ} [Fact p.Prime]
    (z₀ z₁ z₂ z₃ : ZMod p × ZMod p) : Finset (ParabolaOutcome p) := by
  classical
  exact Finset.univ.filter fun o =>
    (outcomeCoeff o).OnParabola z₀ ∧ (outcomeCoeff o).OnParabola z₁ ∧
      (outcomeCoeff o).OnParabola z₂ ∧ (outcomeCoeff o).OnParabola z₃

lemma mem_fourOutcomes {p : ℕ} [Fact p.Prime]
    {z₀ z₁ z₂ z₃ : ZMod p × ZMod p} {o : ParabolaOutcome p} :
    o ∈ fourOutcomes z₀ z₁ z₂ z₃ ↔
      (outcomeCoeff o).OnParabola z₀ ∧ (outcomeCoeff o).OnParabola z₁ ∧
        (outcomeCoeff o).OnParabola z₂ ∧ (outcomeCoeff o).OnParabola z₃ := by
  simp [fourOutcomes]

/-- Tao's four-point incidence bound, in the stronger exact form `2p` for
the number of coefficient outcomes. -/
lemma card_fourOutcomes_le {p : ℕ} [Fact p.Prime]
    (hp : 0 < p) (htwo : (2 : ZMod p) ≠ 0)
    {z₀ z₁ z₂ z₃ : ZMod p × ZMod p}
    (h01 : z₀ ≠ z₁) (h02 : z₀ ≠ z₂) (h03 : z₀ ≠ z₃)
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃) :
    (fourOutcomes z₀ z₁ z₂ z₃).card ≤ 2 * p := by
  classical
  by_cases hdet : pairDet (z₁ - z₀) (z₂ - z₀) = 0
  · have hempty : fourOutcomes z₀ z₁ z₂ z₃ = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro o ho
      rw [mem_fourOutcomes] at ho
      exact (ParabolaCoeff.no_three_collinear (outcomeCoeff_nondegenerate o)
        ho.1 ho.2.1 ho.2.2.1 h01 h02 h12) hdet
    simp [hempty]
  · let s := affineCoordS z₀ z₁ z₂ z₃
    let t := affineCoordT z₀ z₁ z₂ z₃
    have hst := affine_coords_distinct hdet h03.symm h13.symm h23.symm
    have hdecomp := affine_coord_decomposition (z₃ := z₃) hdet
    let zeros : Finset (Fin 2 → ZMod p) :=
      (Fintype.piFinset fun _ : Fin 2 => (Finset.univ : Finset (ZMod p))).filter
        fun x => MvPolynomial.eval x (normalizedFourPoly s t) = 0
    calc
      (fourOutcomes z₀ z₁ z₂ z₃).card ≤ zeros.card := by
        apply Finset.card_le_card_of_injOn
          (fun o => basisLhsCoords (outcomeCoeff o) z₀ z₁ z₂)
        · intro o ho
          change o ∈ fourOutcomes z₀ z₁ z₂ z₃ at ho
          change basisLhsCoords (outcomeCoeff o) z₀ z₁ z₂ ∈ zeros
          rw [mem_fourOutcomes] at ho
          simp only [zeros, Finset.mem_filter, Fintype.mem_piFinset,
            Finset.mem_univ, implies_true, true_and]
          exact ParabolaCoeff.normalized_equation_of_four
            ho.1 ho.2.1 ho.2.2.1 ho.2.2.2 hdecomp
        · intro o ho q hq heq
          change o ∈ fourOutcomes z₀ z₁ z₂ z₃ at ho
          change q ∈ fourOutcomes z₀ z₁ z₂ z₃ at hq
          rw [mem_fourOutcomes] at ho hq
          apply outcomeCoeff_injective
          apply ParabolaCoeff.eq_of_three_on_of_basis_lhs_eq hdet
            ho.1 ho.2.1 ho.2.2.1 hq.1 hq.2.1 hq.2.2.1
          · have h := congrFun heq 0
            simpa [basisLhsCoords] using h
          · have h := congrFun heq 1
            simpa [basisLhsCoords] using h
      _ ≤ 2 * p := by
        exact card_normalizedFourZeros_le hp htwo hst.1 hst.2.1 hst.2.2

/-- Outcomes containing every point of a finite set. -/
noncomputable def setOutcomes {p : ℕ} [Fact p.Prime]
    (B : Finset (ZMod p × ZMod p)) : Finset (ParabolaOutcome p) := by
  classical
  exact Finset.univ.filter fun o =>
    ∀ z ∈ B, (outcomeCoeff o).OnParabola z

lemma mem_setOutcomes {p : ℕ} [Fact p.Prime]
    {B : Finset (ZMod p × ZMod p)} {o : ParabolaOutcome p} :
    o ∈ setOutcomes B ↔ ∀ z ∈ B, (outcomeCoeff o).OnParabola z := by
  simp [setOutcomes]

lemma card_setOutcomes_le_of_card_four {p : ℕ} [Fact p.Prime]
    (hp : 0 < p) (htwo : (2 : ZMod p) ≠ 0)
    {B : Finset (ZMod p × ZMod p)} (hB : B.card = 4) :
    (setOutcomes B).card ≤ 2 * p := by
  classical
  let e : B ≃ Fin 4 := Finset.equivFinOfCardEq hB
  let z : Fin 4 → ZMod p × ZMod p := fun i => (e.symm i : B)
  have hz (i : Fin 4) : z i ∈ B := (e.symm i).property
  have hzij {i j : Fin 4} (hij : i ≠ j) : z i ≠ z j := by
    intro h
    apply hij
    apply e.symm.injective
    exact Subtype.ext h
  calc
    (setOutcomes B).card ≤ (fourOutcomes (z 0) (z 1) (z 2) (z 3)).card := by
      apply Finset.card_le_card
      intro o ho
      rw [mem_setOutcomes] at ho
      rw [mem_fourOutcomes]
      exact ⟨ho _ (hz 0), ho _ (hz 1), ho _ (hz 2), ho _ (hz 3)⟩
    _ ≤ 2 * p := card_fourOutcomes_le hp htwo
      (hzij (by decide)) (hzij (by decide)) (hzij (by decide))
      (hzij (by decide)) (hzij (by decide)) (hzij (by decide))

/-! ### Exact finite moments -/

/-- The grid points selected by a coefficient outcome. -/
noncomputable def outcomeGrid (p N : ℕ) [Fact p.Prime]
    (o : ParabolaOutcome p) : Finset (ℤ × ℤ) :=
  parabolaGrid p N (outcomeCoeff o)

lemma mem_outcomeGrid {p N : ℕ} [Fact p.Prime]
    {o : ParabolaOutcome p} {z : ℤ × ℤ} :
    z ∈ outcomeGrid p N o ↔
      z ∈ intGrid N ∧ (outcomeCoeff o).OnParabola (modPoint p z) :=
  mem_parabolaGrid

/-- Exact first moment: a fixed point belongs to one outcome out of `p`. -/
lemma sum_card_outcomeGrid (p N : ℕ) [Fact p.Prime] :
    ∑ o : ParabolaOutcome p, (outcomeGrid p N o).card =
      (intGrid N).card *
        Fintype.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) := by
  classical
  calc
    ∑ o : ParabolaOutcome p, (outcomeGrid p N o).card =
        ∑ o : ParabolaOutcome p, ∑ z ∈ intGrid N,
          if (outcomeCoeff o).OnParabola (modPoint p z) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro o _ho
      simp only [outcomeGrid, parabolaGrid, Finset.card_eq_sum_ones,
        Finset.sum_filter]
    _ = ∑ z ∈ intGrid N, ∑ o : ParabolaOutcome p,
          if (outcomeCoeff o).OnParabola (modPoint p z) then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ _z ∈ intGrid N,
          Fintype.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) := by
      apply Finset.sum_congr rfl
      intro z _hz
      rw [← card_pointOutcomes (modPoint p z)]
      rw [pointOutcomes, Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = (intGrid N).card *
          Fintype.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) := by
      simp

lemma card_outcomes_containing_quad_le {p N : ℕ} [Fact p.Prime]
    (hp : 0 < p) (htwo : (2 : ZMod p) ≠ 0) (hNp : N ≤ p)
    {B : Finset (ℤ × ℤ)} (hBsub : B ⊆ intGrid N) (hBcard : B.card = 4) :
    (Finset.univ.filter fun o : ParabolaOutcome p => B ⊆ outcomeGrid p N o).card ≤
      2 * p := by
  classical
  have himgcard : (B.image (modPoint p)).card = 4 := by
    rw [Finset.card_image_of_injOn ((modPoint_injOn_intGrid hNp).mono hBsub), hBcard]
  have heq :
      Finset.univ.filter (fun o : ParabolaOutcome p => B ⊆ outcomeGrid p N o) =
        setOutcomes (B.image (modPoint p)) := by
    ext o
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_setOutcomes]
    constructor
    · intro ho u hu
      rcases Finset.mem_image.mp hu with ⟨z, hzB, rfl⟩
      exact (mem_outcomeGrid.mp (ho hzB)).2
    · intro ho z hzB
      exact mem_outcomeGrid.mpr
        ⟨hBsub hzB, ho _ (Finset.mem_image.mpr ⟨z, hzB, rfl⟩)⟩
  rw [heq]
  exact card_setOutcomes_le_of_card_four hp htwo himgcard

/-- The four-point incidence bound summed over a four-uniform family. -/
lemma sum_card_containedBad_le {p N : ℕ} [Fact p.Prime]
    (hp : 0 < p) (htwo : (2 : ZMod p) ≠ 0) (hNp : N ≤ p)
    (H : Finset (Finset (ℤ × ℤ)))
    (hHsub : ∀ B ∈ H, B ⊆ intGrid N)
    (hHcard : ∀ B ∈ H, B.card = 4) :
    ∑ o : ParabolaOutcome p, (containedBad H (outcomeGrid p N o)).card ≤
      H.card * (2 * p) := by
  classical
  calc
    ∑ o : ParabolaOutcome p, (containedBad H (outcomeGrid p N o)).card =
        ∑ o : ParabolaOutcome p, ∑ B ∈ H,
          if B ⊆ outcomeGrid p N o then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro o _ho
      rw [containedBad, Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ B ∈ H, ∑ o : ParabolaOutcome p,
          if B ⊆ outcomeGrid p N o then 1 else 0 := by
      rw [Finset.sum_comm]
    _ ≤ ∑ _B ∈ H, 2 * p := by
      apply Finset.sum_le_sum
      intro B hBH
      have hcount :
          (∑ o : ParabolaOutcome p,
              if B ⊆ outcomeGrid p N o then 1 else 0) =
            (Finset.univ.filter fun o : ParabolaOutcome p =>
              B ⊆ outcomeGrid p N o).card := by
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [hcount]
      exact card_outcomes_containing_quad_le hp htwo hNp
        (hHsub B hBH) (hHcard B hBH)
    _ = H.card * (2 * p) := by simp

lemma ParallelogramFree.mono {S T : Finset (ℤ × ℤ)}
    (hS : ParallelogramFree S) (hTS : T ⊆ S) : ParallelogramFree T := by
  intro Q hQT hQcard
  exact hS Q (hQT.trans hTS) hQcard

/-- Finite averaging followed by deletion.  The numerical hypothesis is the
cleared-denominator form of “expected vertices minus four times expected bad
quadruples is at least `L`.” -/
lemma exists_large_clean_parabola {p N : ℕ} [Fact p.Prime]
    (hp : 0 < p) (hp2 : 2 < p) (hNp : N ≤ p)
    (H : Finset (Finset (ℤ × ℤ)))
    (hHsub : ∀ B ∈ H, B ⊆ intGrid N)
    (hHcard : ∀ B ∈ H, B.card = 4) (L : ℕ)
    (haverage :
      Fintype.card (ParabolaOutcome p) * L + 8 * p * H.card ≤
        (intGrid N).card *
          Fintype.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) :
    ∃ o : ParabolaOutcome p,
      L ≤ (clean H (outcomeGrid p N o)).card ∧
      clean H (outcomeGrid p N o) ⊆ intGrid N ∧
      ParallelogramFree (clean H (outcomeGrid p N o)) ∧
      ∀ B ∈ H, ¬B ⊆ clean H (outcomeGrid p N o) := by
  classical
  let score : ParabolaOutcome p → ℤ := fun o =>
    ((outcomeGrid p N o).card : ℤ) -
      4 * ((containedBad H (outcomeGrid p N o)).card : ℤ)
  have hsize := sum_card_outcomeGrid p N
  have hbad := sum_card_containedBad_le hp (two_ne_zero_zmod hp2) hNp H hHsub hHcard
  have hloss :
      4 * (∑ o : ParabolaOutcome p,
        (containedBad H (outcomeGrid p N o)).card) ≤ 8 * p * H.card := by
    calc
      4 * (∑ o : ParabolaOutcome p,
          (containedBad H (outcomeGrid p N o)).card)
          ≤ 4 * (H.card * (2 * p)) := Nat.mul_le_mul_left 4 hbad
      _ = 8 * p * H.card := by ring
  have hNat :
      Fintype.card (ParabolaOutcome p) * L +
          4 * (∑ o : ParabolaOutcome p,
            (containedBad H (outcomeGrid p N o)).card) ≤
        ∑ o : ParabolaOutcome p, (outcomeGrid p N o).card := by
    rw [hsize]
    omega
  have hsum :
      (Fintype.card (ParabolaOutcome p) : ℤ) * (L : ℤ) ≤
        ∑ o : ParabolaOutcome p, score o := by
    have hscoreeq :
        (∑ o : ParabolaOutcome p, score o) =
          ((∑ o : ParabolaOutcome p, (outcomeGrid p N o).card : ℕ) : ℤ) -
            4 * ((∑ o : ParabolaOutcome p,
              (containedBad H (outcomeGrid p N o)).card : ℕ) : ℤ) := by
      dsimp [score]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      norm_cast
    rw [hscoreeq]
    have hcast :
        ((Fintype.card (ParabolaOutcome p) * L +
          4 * (∑ o : ParabolaOutcome p,
            (containedBad H (outcomeGrid p N o)).card) : ℕ) : ℤ) ≤
          ((∑ o : ParabolaOutcome p, (outcomeGrid p N o).card : ℕ) : ℤ) := by
      exact_mod_cast hNat
    push_cast at hcast
    omega
  obtain ⟨o, _ho, hoscore⟩ := exists_score_ge_average
    (outcomes := (Finset.univ : Finset (ParabolaOutcome p)))
    Finset.univ_nonempty score L (by simpa using hsum)
  refine ⟨o, ?_, ?_, ?_, ?_⟩
  · have hcast :
        (L : ℤ) + 4 * ((containedBad H (outcomeGrid p N o)).card : ℤ) ≤
          ((outcomeGrid p N o).card : ℤ) := by
      dsimp [score] at hoscore
      omega
    have hnat :
        L + 4 * (containedBad H (outcomeGrid p N o)).card ≤
          (outcomeGrid p N o).card := by exact_mod_cast hcast
    have hclean := card_clean_lower_bound H (outcomeGrid p N o) 4
      (fun B hBH => by rw [hHcard B hBH])
    omega
  · exact (clean_subset H (outcomeGrid p N o)).trans
      (parabolaGrid_subset_intGrid (outcomeCoeff o))
  · apply (parabolaGrid_parallelogramFree hNp hp2 (outcomeCoeff o)
      (outcomeCoeff_nondegenerate o)).mono
    exact clean_subset H (outcomeGrid p N o)
  · intro B hBH
    exact no_bad_subset_clean hBH (Finset.card_pos.mp (by
      rw [hHcard B hBH]
      decide))

lemma average_inequality_of_bad_bound
    {K D N p H : ℕ} [Fact p.Prime]
    (hDK : 32 * K ≤ D ^ 3)
    (hpLower : D * N < p) (hpUpper : p ≤ 2 * (D * N))
    (hH : H ≤ K * N ^ 5) :
    Fintype.card (ParabolaOutcome p) * (N / (4 * D)) + 8 * p * H ≤
      (intGrid N).card *
        Fintype.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) := by
  let G := (p ^ 2 - 1) * (p ^ 2 - p)
  have hpDN : D * N ≤ p := hpLower.le
  have hpm1 : D * N ≤ p - 1 := by omega
  have hbase : D ^ 2 * N ^ 2 ≤ p ^ 2 - p := by
    rw [show p ^ 2 - p = p * (p - 1) by
      calc
        p ^ 2 - p = p * p - p * 1 := by simp [pow_two]
        _ = p * (p - 1) := (Nat.mul_sub_left_distrib p p 1).symm]
    calc
      D ^ 2 * N ^ 2 = (D * N) * (D * N) := by ring
      _ ≤ p * (p - 1) := Nat.mul_le_mul hpDN hpm1
  have hpone : 1 ≤ p := by omega
  have hfirst : D ^ 2 * N ^ 2 ≤ p ^ 2 - 1 := by
    exact hbase.trans (by
      rw [pow_two]
      omega)
  have hGlow : D ^ 4 * N ^ 4 ≤ G := by
    dsimp [G]
    calc
      D ^ 4 * N ^ 4 = (D ^ 2 * N ^ 2) * (D ^ 2 * N ^ 2) := by ring
      _ ≤ (p ^ 2 - 1) * (p ^ 2 - p) := Nat.mul_le_mul hfirst hbase
  have hdiv : 4 * D * (N / (4 * D)) ≤ N := by
    simpa [mul_assoc] using Nat.mul_div_le N (4 * D)
  have hmain : 2 * p * (N / (4 * D)) ≤ N ^ 2 := by
    calc
      2 * p * (N / (4 * D)) ≤
          2 * (2 * (D * N)) * (N / (4 * D)) := by
        gcongr
      _ = N * (4 * D * (N / (4 * D))) := by ring
      _ ≤ N * N := Nat.mul_le_mul_left N hdiv
      _ = N ^ 2 := by ring
  have hDcube : 32 * K ≤ D ^ 3 := hDK
  have hlossCoeff : 32 * D * K ≤ D ^ 4 := by
    calc
      32 * D * K = D * (32 * K) := by ring
      _ ≤ D * D ^ 3 := Nat.mul_le_mul_left D hDcube
      _ = D ^ 4 := by ring
  have hloss : 16 * p * H ≤ N ^ 2 * G := by
    calc
      16 * p * H ≤ 16 * (2 * (D * N)) * (K * N ^ 5) := by
        gcongr
      _ = (32 * D * K) * N ^ 6 := by ring
      _ ≤ D ^ 4 * N ^ 6 := Nat.mul_le_mul_right (N ^ 6) hlossCoeff
      _ = N ^ 2 * (D ^ 4 * N ^ 4) := by ring
      _ ≤ N ^ 2 * G := Nat.mul_le_mul_left (N ^ 2) hGlow
  rw [card_parabolaOutcome, card_GL_two, card_intGrid]
  rw [Nat.mul_assoc p (p ^ 2 - 1) (p ^ 2 - p)]
  change p * G * (N / (4 * D)) + 8 * p * H ≤ N ^ 2 * G
  have hmain' : 2 * (p * G * (N / (4 * D))) ≤ N ^ 2 * G := by
    calc
      2 * (p * G * (N / (4 * D))) =
          (2 * p * (N / (4 * D))) * G := by ring
      _ ≤ N ^ 2 * G := Nat.mul_le_mul_right G hmain
  have hloss' : 2 * (8 * p * H) ≤ N ^ 2 * G := by
    convert hloss using 1; ring
  apply Nat.le_of_mul_le_mul_left (c := 2) _ (by decide)
  calc
    2 * (p * G * (N / (4 * D)) + 8 * p * H) =
        2 * (p * G * (N / (4 * D))) + 2 * (8 * p * H) := by ring
    _ ≤ N ^ 2 * G + N ^ 2 * G := Nat.add_le_add hmain' hloss'
    _ = 2 * (N ^ 2 * G) := by ring

/-- The finite construction, isolated from the lattice-counting input. -/
lemma exists_grid_subset_of_bad_bound {K N : ℕ} (hN : 1 ≤ N)
    (hbad : (otherBadIntQuads (intGrid N)).card ≤ K * N ^ 5) :
    ∃ S : Finset (ℤ × ℤ),
      S ⊆ intGrid N ∧ N / (128 * (K + 1)) ≤ S.card ∧
        HasPhi45 (S.image intPoint) := by
  classical
  let D := 32 * (K + 1)
  have hD : 1 ≤ D := by
    change 1 ≤ 32 * (K + 1)
    omega
  have hDN0 : D * N ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  obtain ⟨p, hpprime, hpLower, hpUpper⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (D * N) hDN0
  let : Fact p.Prime := ⟨hpprime⟩
  have hp : 0 < p := hpprime.pos
  have hp2 : 2 < p := by
    have h32 : 32 ≤ D * N := by
      calc
        32 = 32 * 1 * 1 := by ring
        _ ≤ 32 * (K + 1) * N := by gcongr; omega
        _ = D * N := by rfl
    exact (by omega : 2 < 32).trans (h32.trans_lt hpLower)
  have hNp : N ≤ p := by
    calc
      N = 1 * N := by simp
      _ ≤ D * N := Nat.mul_le_mul_right N hD
      _ ≤ p := hpLower.le
  have hDK : 32 * K ≤ D ^ 3 := by
    have hKD : 32 * K ≤ D := by
      dsimp [D]
      omega
    apply hKD.trans
    calc
      D = D * 1 * 1 := by simp
      _ ≤ D * D * D := by gcongr
      _ = D ^ 3 := by ring
  let H := otherBadIntQuads (intGrid N)
  have hHsub : ∀ B ∈ H, B ⊆ intGrid N := by
    intro B hB
    exact otherBadIntQuads_subset_powerset hB
  have hHcard : ∀ B ∈ H, B.card = 4 := by
    intro B hB
    exact card_eq_four_of_mem_otherBadIntQuads hB
  have havg :
      Fintype.card (ParabolaOutcome p) * (N / (4 * D)) + 8 * p * H.card ≤
        (intGrid N).card *
          Fintype.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :=
    average_inequality_of_bad_bound hDK hpLower hpUpper hbad
  obtain ⟨o, hcard, hsubset, hpara, hnone⟩ :=
    exists_large_clean_parabola (p := p) (N := N) hp hp2 hNp H hHsub hHcard
      (N / (4 * D)) havg
  let S := clean H (outcomeGrid p N o)
  have hother : otherBadIntQuads S = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro Q hQ
    have hQH : Q ∈ H := otherBadIntQuads_mono hsubset hQ
    exact hnone Q hQH (otherBadIntQuads_subset_powerset hQ)
  refine ⟨S, hsubset, ?_, ?_⟩
  · have hden : 4 * D = 128 * (K + 1) := by
      dsimp [D]
      ring
    simpa only [hden] using hcard
  · exact hasPhi45_image_of_parallelogramFree_of_no_otherBad hpara hother

/-! ## The arithmetic indicator for sums of two squares -/

/-- The natural numbers representable as a sum of two natural squares. -/
def IsSumTwoSquares (n : ℕ) : Prop := ∃ x y : ℕ, n = x ^ 2 + y ^ 2

instance (n : ℕ) : Decidable (IsSumTwoSquares n) := by
  unfold IsSumTwoSquares
  infer_instance

/-- Representability by two squares is multiplicative across coprime,
nonzero factors.  The reverse implication is the part supplied by Fermat's
factorization criterion in Mathlib. -/
lemma isSumTwoSquares_mul_iff_of_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hcop : m.Coprime n) :
    IsSumTwoSquares (m * n) ↔ IsSumTwoSquares m ∧ IsSumTwoSquares n := by
  rw [IsSumTwoSquares, IsSumTwoSquares, IsSumTwoSquares,
    Nat.eq_sq_add_sq_iff, Nat.eq_sq_add_sq_iff, Nat.eq_sq_add_sq_iff]
  have hpf := hcop.primeFactors_mul
  constructor
  · intro h
    constructor
    · intro q hqm hqmod
      have hq : q.Prime := Nat.prime_of_mem_primeFactors hqm
      have hqp : q ∈ (m * n).primeFactors := by
        rw [hpf]
        exact Finset.mem_union_left _ hqm
      have he := h q hqp hqmod
      let : Fact q.Prime := ⟨hq⟩
      have hnqd : ¬ q ∣ n := by
        intro hqn
        exact hq.ne_one (Nat.eq_one_of_dvd_coprimes hcop
          (Nat.mem_primeFactors.mp hqm).2.1 hqn)
      have hnval : padicValNat q n = 0 := by
        rw [← Nat.factorization_def n hq,
          Nat.factorization_eq_zero_of_not_dvd hnqd]
      rw [padicValNat.mul hm hn, hnval, add_zero] at he
      exact he
    · intro q hqn hqmod
      have hq : q.Prime := Nat.prime_of_mem_primeFactors hqn
      have hqp : q ∈ (m * n).primeFactors := by
        rw [hpf]
        exact Finset.mem_union_right _ hqn
      have he := h q hqp hqmod
      let : Fact q.Prime := ⟨hq⟩
      have hmqd : ¬ q ∣ m := by
        intro hqm
        exact hq.ne_one (Nat.eq_one_of_dvd_coprimes hcop hqm
          (Nat.mem_primeFactors.mp hqn).2.1)
      have hmval : padicValNat q m = 0 := by
        rw [← Nat.factorization_def m hq,
          Nat.factorization_eq_zero_of_not_dvd hmqd]
      rw [padicValNat.mul hm hn, hmval, zero_add] at he
      exact he
  · rintro ⟨hmrep, hnrep⟩ q hqmn hqmod
    rw [hpf] at hqmn
    rcases Finset.mem_union.mp hqmn with hqm | hqn
    · have hq : q.Prime := Nat.prime_of_mem_primeFactors hqm
      let : Fact q.Prime := ⟨hq⟩
      rw [padicValNat.mul hm hn]
      have hem := hmrep q hqm hqmod
      have hnqd : ¬ q ∣ n := by
        intro hqn
        exact hq.ne_one (Nat.eq_one_of_dvd_coprimes hcop
          (Nat.mem_primeFactors.mp hqm).2.1 hqn)
      have hnval : padicValNat q n = 0 := by
        rw [← Nat.factorization_def n hq,
          Nat.factorization_eq_zero_of_not_dvd hnqd]
      rw [hnval, add_zero]
      exact hem
    · have hq : q.Prime := Nat.prime_of_mem_primeFactors hqn
      let : Fact q.Prime := ⟨hq⟩
      rw [padicValNat.mul hm hn]
      have hen := hnrep q hqn hqmod
      have hmqd : ¬ q ∣ m := by
        intro hqm
        exact hq.ne_one (Nat.eq_one_of_dvd_coprimes hcop hqm
          (Nat.mem_primeFactors.mp hqn).2.1)
      have hmval : padicValNat q m = 0 := by
        rw [← Nat.factorization_def m hq,
          Nat.factorization_eq_zero_of_not_dvd hmqd]
      rw [hmval, zero_add]
      exact hen

/-- The zero-one arithmetic weight of positive sums of two squares. -/
def sumTwoSquaresWeight (n : ℕ) : ℝ :=
  if n = 0 then 0 else if IsSumTwoSquares n then 1 else 0

lemma sumTwoSquaresWeight_zero : sumTwoSquaresWeight 0 = 0 := by
  simp [sumTwoSquaresWeight]

lemma sumTwoSquaresWeight_one : sumTwoSquaresWeight 1 = 1 := by
  rw [sumTwoSquaresWeight, if_neg (by omega)]
  exact if_pos ⟨1, 0, by norm_num⟩

lemma sumTwoSquaresWeight_nonneg (n : ℕ) : 0 ≤ sumTwoSquaresWeight n := by
  simp only [sumTwoSquaresWeight]
  split_ifs <;> norm_num

lemma sumTwoSquaresWeight_mul_of_coprime {m n : ℕ} (hcop : m.Coprime n) :
    sumTwoSquaresWeight (m * n) =
      sumTwoSquaresWeight m * sumTwoSquaresWeight n := by
  by_cases hm : m = 0
  · subst m
    simp [sumTwoSquaresWeight]
  by_cases hn : n = 0
  · subst n
    simp [sumTwoSquaresWeight]
  have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm hn
  rw [sumTwoSquaresWeight, sumTwoSquaresWeight, sumTwoSquaresWeight,
    if_neg hm, if_neg hn, if_neg hmn]
  have hiff := isSumTwoSquares_mul_iff_of_coprime hm hn hcop
  by_cases hmr : IsSumTwoSquares m <;>
    by_cases hnr : IsSumTwoSquares n <;> simp [hmr, hnr, hiff]

lemma sumTwoSquaresWeight_le_one (n : ℕ) : sumTwoSquaresWeight n ≤ 1 := by
  simp only [sumTwoSquaresWeight]
  split_ifs <;> norm_num

lemma sumTwoSquaresWeight_prime_pow_le_one {p j : ℕ} (_hp : p.Prime) :
    sumTwoSquaresWeight (p ^ (j + 1)) ≤ (1 : ℝ) * 1 ^ j := by
  simpa using sumTwoSquaresWeight_le_one (p ^ (j + 1))

/-- Halberstam--Richert reduces the Landau--Ramanujan upper bound to the
finite Euler product of the sum-of-two-squares indicator. -/
lemma sumTwoSquaresWeight_mean_le_euler (N : ℕ) (hN : 2 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, sumTwoSquaresWeight n) ≤
      (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          ∏ p ∈ (N + 1).primesBelow,
            ∑' j : ℕ,
              sumTwoSquaresWeight (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
  exact HalberstamComplete448.halberstam_richert_explicit
    sumTwoSquaresWeight sumTwoSquaresWeight_zero sumTwoSquaresWeight_one
    (fun {_ _} h => sumTwoSquaresWeight_mul_of_coprime h)
    sumTwoSquaresWeight_nonneg 1 1 (by norm_num) (by norm_num) (by norm_num)
    (fun p hp j => sumTwoSquaresWeight_prime_pow_le_one hp) N hN

lemma isSumTwoSquares_prime_pow_iff {p j : ℕ} (hp : p.Prime) :
    IsSumTwoSquares (p ^ j) ↔ p % 4 ≠ 3 ∨ Even j := by
  rw [IsSumTwoSquares, Nat.eq_sq_add_sq_iff]
  by_cases hj : j = 0
  · subst j
    simp
  let : Fact p.Prime := ⟨hp⟩
  rw [Nat.primeFactors_pow p hj]
  simp [hp]
  tauto

lemma sumTwoSquaresWeight_prime_pow (p j : ℕ) (hp : p.Prime) :
    sumTwoSquaresWeight (p ^ j) =
      if p % 4 = 3 then (if Even j then 1 else 0) else 1 := by
  rw [sumTwoSquaresWeight, if_neg (pow_ne_zero _ hp.ne_zero)]
  by_cases hmod : p % 4 = 3 <;> by_cases hj : Even j <;>
    simp [hmod, hj, isSumTwoSquares_prime_pow_iff hp]

/-- Even natural numbers are canonically parametrized by their halves. -/
def evenNatEquiv : ℕ ≃ {n : ℕ // Even n} where
  toFun k := ⟨2 * k, ⟨k, by omega⟩⟩
  invFun n := n.1 / 2
  left_inv k := by simp
  right_inv n := by
    apply Subtype.ext
    rcases n.2 with ⟨k, hk⟩
    dsimp
    omega

lemma tsum_even_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' j : ℕ, if Even j then r ^ j else 0) = (1 - r ^ 2)⁻¹ := by
  calc
    (∑' j : ℕ, if Even j then r ^ j else 0) =
        ∑' j : {n : ℕ // Even n}, r ^ (j : ℕ) := by
          symm
          calc
            (∑' j : {n : ℕ // Even n}, r ^ (j : ℕ)) =
                ∑' j : ℕ, ({n : ℕ | Even n} : Set ℕ).indicator
                  (fun n => r ^ n) j :=
              tsum_subtype ({n : ℕ | Even n} : Set ℕ) (fun n => r ^ n)
            _ = ∑' j : ℕ, if Even j then r ^ j else 0 := by
              apply tsum_congr
              intro j
              by_cases hj : Even j <;> simp [Set.indicator, hj]
    _ = ∑' k : ℕ, r ^ ((evenNatEquiv k : {n : ℕ // Even n}) : ℕ) := by
      exact (evenNatEquiv.tsum_eq
        (fun j : {n : ℕ // Even n} => r ^ (j : ℕ))).symm
    _ = ∑' k : ℕ, (r ^ 2) ^ k := by
      congr 1
      funext k
      dsimp [evenNatEquiv]
      rw [← pow_mul]
    _ = (1 - r ^ 2)⁻¹ :=
      tsum_geometric_of_lt_one (sq_nonneg r) (by nlinarith)

/-- Exact local Euler factor for the positive sum-of-two-squares
indicator. -/
lemma sumTwoSquares_eulerFactor (p : ℕ) (hp : p.Prime) :
    (∑' j : ℕ,
        sumTwoSquaresWeight (p ^ j) / ((p ^ j : ℕ) : ℝ)) =
      if p % 4 = 3 then (1 - ((p : ℝ)⁻¹) ^ 2)⁻¹
      else (1 - (p : ℝ)⁻¹)⁻¹ := by
  let r : ℝ := (p : ℝ)⁻¹
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    dsimp [r]
    exact (inv_lt_one₀ (by positivity : (0 : ℝ) < p)).2 hpR
  by_cases hmod : p % 4 = 3
  · rw [if_pos hmod]
    calc
      (∑' j : ℕ,
          sumTwoSquaresWeight (p ^ j) / ((p ^ j : ℕ) : ℝ)) =
          ∑' j : ℕ, if Even j then r ^ j else 0 := by
            apply tsum_congr
            intro j
            rw [sumTwoSquaresWeight_prime_pow p j hp]
            by_cases hj : Even j <;>
              simp [hmod, hj, r, div_eq_mul_inv, inv_pow]
      _ = (1 - r ^ 2)⁻¹ := tsum_even_geometric hr0 hr1
      _ = (1 - ((p : ℝ)⁻¹) ^ 2)⁻¹ := by rfl
  · rw [if_neg hmod]
    calc
      (∑' j : ℕ,
          sumTwoSquaresWeight (p ^ j) / ((p ^ j : ℕ) : ℝ)) =
          ∑' j : ℕ, r ^ j := by
            apply tsum_congr
            intro j
            rw [sumTwoSquaresWeight_prime_pow p j hp]
            simp [hmod, r, div_eq_mul_inv, inv_pow]
      _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1
      _ = (1 - (p : ℝ)⁻¹)⁻¹ := by rfl

def rot90Int (z : ℤ × ℤ) : ℤ × ℤ := (-z.2, z.1)

def axisFirst (a b : ℤ × ℤ) : ℤ × ℤ := a + b

def axisSecond (a b : ℤ × ℤ) : ℤ × ℤ :=
  axisFirst a b + rot90Int (a - b)

lemma axisEncoding_injective : Function.Injective
    (fun ab : (ℤ × ℤ) × (ℤ × ℤ) =>
      (axisFirst ab.1 ab.2, axisSecond ab.1 ab.2)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h00 := congrArg (fun z => z.1.1) h
  have h01 := congrArg (fun z => z.1.2) h
  have h10 := congrArg (fun z => z.2.1) h
  have h11 := congrArg (fun z => z.2.2) h
  apply Prod.ext <;> apply Prod.ext <;>
    simp [axisFirst, axisSecond, rot90Int] at h00 h01 h10 h11 ⊢ <;> omega

lemma rot90Int_ne_zero {z : ℤ × ℤ} (hz : z ≠ 0) : rot90Int z ≠ 0 := by
  intro h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  apply hz
  apply Prod.ext <;> simp_all [rot90Int]

lemma axisFirst_ne_axisSecond {a b : ℤ × ℤ} (hab : a ≠ b) :
    axisFirst a b ≠ axisSecond a b := by
  intro h
  have hz : a - b ≠ 0 := sub_ne_zero.mpr hab
  apply rot90Int_ne_zero hz
  simpa [axisSecond] using sub_eq_zero.mpr h.symm

noncomputable def encodedAxis (a b : ℤ × ℤ) (hab : a ≠ b) :
    {ℓ : AffineSubspace ℝ Plane // IsAffineLine ℓ} :=
  ⟨affineSpan ℝ ({intPoint (axisFirst a b), intPoint (axisSecond a b)} : Set Plane),
    ⟨⟨intPoint (axisFirst a b), subset_affineSpan ℝ _ (by simp)⟩, by
      rw [direction_affineSpan, vectorSpan_pair]
      apply finrank_span_singleton
      rw [vsub_ne_zero]
      exact intPoint_injective.ne (axisFirst_ne_axisSecond hab)⟩⟩

lemma intPoint_axisSecond_sub_first (a b : ℤ × ℤ) :
    intPoint (axisSecond a b) - intPoint (axisFirst a b) =
      intPoint (rot90Int (a - b)) := by
  ext i
  fin_cases i <;> simp [intPoint, axisSecond, axisFirst, rot90Int]

lemma equidistant_dot_zero {a b c : ℤ × ℤ}
    (h : intSqDist c a = intSqDist c b) :
    ((2 * c.1 - (a.1 + b.1)) : ℤ) * (a.1 - b.1) +
      (2 * c.2 - (a.2 + b.2)) * (a.2 - b.2) = 0 := by
  dsimp [intSqDist] at h
  nlinarith

lemma equidistant_mem_encodedAxis {a b c : ℤ × ℤ} (hab : a ≠ b)
    (h : intSqDist c a = intSqDist c b) :
    intPoint (2 • c) ∈ (encodedAxis a b hab : AffineSubspace ℝ Plane) := by
  change intPoint (2 • c) ∈
    affineSpan ℝ ({intPoint (axisFirst a b), intPoint (axisSecond a b)} : Set Plane)
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  let v : ℝ × ℝ := ((a.1 - b.1 : ℤ), (a.2 - b.2 : ℤ))
  let w : ℝ × ℝ :=
    ((2 * c.1 - (a.1 + b.1) : ℤ), (2 * c.2 - (a.2 + b.2) : ℤ))
  have hzR :
      (((2 * c.1 - (a.1 + b.1) : ℤ) : ℝ) * ((a.1 - b.1 : ℤ) : ℝ) +
        ((2 * c.2 - (a.2 + b.2) : ℤ) : ℝ) * ((a.2 - b.2 : ℤ) : ℝ)) = 0 := by
    exact_mod_cast equidistant_dot_zero h
  have hdet : pairDet (-(v.2), v.1) w = 0 := by
    dsimp [pairDet, v, w]
    norm_num
    push_cast at hzR
    ring_nf at hzR ⊢
    nlinarith
  have hv : (-(v.2), v.1) ≠ (0 : ℝ × ℝ) := by
    intro hvz
    have h1 := congrArg Prod.fst hvz
    have h2 := congrArg Prod.snd hvz
    have hxR : (((a.1 - b.1 : ℤ) : ℝ)) = 0 := by simpa [v] using h2
    have hyR : (((a.2 - b.2 : ℤ) : ℝ)) = 0 := by
      have : -(((a.2 - b.2 : ℤ) : ℝ)) = 0 := by simpa [v] using h1
      linarith
    have hxZ : a.1 - b.1 = 0 := by exact_mod_cast hxR
    have hyZ : a.2 - b.2 = 0 := by exact_mod_cast hyR
    apply hab
    exact Prod.ext (sub_eq_zero.mp hxZ) (sub_eq_zero.mp hyZ)
  obtain ⟨t, ht⟩ := exists_smul_of_pairDet_eq_zero hv hdet
  have ht1 := congrArg Prod.fst ht
  have ht2 := congrArg Prod.snd ht
  refine ⟨t, ?_⟩
  ext i
  fin_cases i <;>
    simp [AffineMap.lineMap_apply, intPoint, axisFirst, axisSecond, rot90Int,
      v, w] at ht1 ht2 ⊢ <;>
    linarith

noncomputable def expandedIntRange (N : ℕ) : Finset ℤ :=
  Finset.Icc (-(N : ℤ)) (3 * (N : ℤ))

noncomputable def expandedIntGrid (N : ℕ) : Finset (ℤ × ℤ) :=
  expandedIntRange N ×ˢ expandedIntRange N

noncomputable def expandedPlaneGrid (N : ℕ) : Finset Plane :=
  (expandedIntGrid N).image intPoint

@[simp] lemma card_expandedIntRange (N : ℕ) :
    (expandedIntRange N).card = 4 * N + 1 := by
  simp [expandedIntRange]
  omega

@[simp] lemma card_expandedIntGrid (N : ℕ) :
    (expandedIntGrid N).card = (4 * N + 1) ^ 2 := by
  simp [expandedIntGrid, pow_two]

@[simp] lemma card_expandedPlaneGrid (N : ℕ) :
    (expandedPlaneGrid N).card = (4 * N + 1) ^ 2 := by
  rw [expandedPlaneGrid, Finset.card_image_of_injective _ intPoint_injective,
    card_expandedIntGrid]

lemma mem_expandedIntGrid {N : ℕ} {x : ℤ × ℤ} :
    x ∈ expandedIntGrid N ↔
      -(N : ℤ) ≤ x.1 ∧ x.1 ≤ 3 * N ∧
      -(N : ℤ) ≤ x.2 ∧ x.2 ≤ 3 * N := by
  simp only [expandedIntGrid, Finset.mem_product, expandedIntRange,
    Finset.mem_Icc]
  omega

lemma axisFirst_mem_expanded {N : ℕ} {a b : ℤ × ℤ}
    (ha : a ∈ intGrid N) (hb : b ∈ intGrid N) :
    axisFirst a b ∈ expandedIntGrid N := by
  rw [mem_expandedIntGrid]
  rw [mem_intGrid] at ha hb
  simp only [axisFirst, Prod.fst_add, Prod.snd_add]
  omega

lemma axisSecond_mem_expanded {N : ℕ} {a b : ℤ × ℤ}
    (ha : a ∈ intGrid N) (hb : b ∈ intGrid N) :
    axisSecond a b ∈ expandedIntGrid N := by
  rw [mem_expandedIntGrid]
  rw [mem_intGrid] at ha hb
  simp only [axisSecond, axisFirst, rot90Int, Prod.fst_add, Prod.snd_add,
    Prod.fst_sub, Prod.snd_sub]
  omega

lemma two_smul_mem_expanded {N : ℕ} {c : ℤ × ℤ}
    (hc : c ∈ intGrid N) : 2 • c ∈ expandedIntGrid N := by
  rw [mem_intGrid] at hc
  rw [mem_expandedIntGrid]
  change (-N : ℤ) ≤ 2 * c.1 ∧ 2 * c.1 ≤ 3 * N ∧
    (-N : ℤ) ≤ 2 * c.2 ∧ 2 * c.2 ≤ 3 * N
  omega

private lemma intPoint_mem_pair_line_parameter {m q x : ℤ × ℤ}
    (hx : intPoint x ∈
      affineSpan ℝ ({intPoint m, intPoint q} : Set Plane)) :
    ∃ t : ℝ,
      (x.1 : ℝ) = (m.1 : ℝ) + t * ((q.1 : ℝ) - m.1) ∧
      (x.2 : ℝ) = (m.2 : ℝ) + t * ((q.2 : ℝ) - m.2) := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hx
  rcases hx with ⟨t, ht⟩
  rw [AffineMap.lineMap_apply] at ht
  change t • (intPoint q - intPoint m) + intPoint m = intPoint x at ht
  refine ⟨t, ?_, ?_⟩
  · have h := congrArg (fun z : Plane => z 0) ht.symm
    simpa [intPoint, add_comm] using h
  · have h := congrArg (fun z : Plane => z 1) ht.symm
    simpa [intPoint, add_comm] using h

private lemma first_injOn_pair_line {m q : ℤ × ℤ} (hfirst : m.1 ≠ q.1) :
    Set.InjOn Prod.fst
      {x : ℤ × ℤ | intPoint x ∈
        affineSpan ℝ ({intPoint m, intPoint q} : Set Plane)} := by
  intro x hx y hy hxy
  obtain ⟨s, hs1, hs2⟩ := intPoint_mem_pair_line_parameter (m := m) (q := q) hx
  obtain ⟨t, ht1, ht2⟩ := intPoint_mem_pair_line_parameter (m := m) (q := q) hy
  have hmq : ((q.1 : ℝ) - m.1) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hfirst.symm)
  have hst : s = t := by
    have hxyR : (x.1 : ℝ) = y.1 := by exact_mod_cast hxy
    apply (mul_right_cancel₀ hmq)
    linarith
  apply Prod.ext hxy
  exact_mod_cast (by rw [hs2, ht2, hst] : (x.2 : ℝ) = y.2)

private lemma second_injOn_pair_line {m q : ℤ × ℤ} (hsecond : m.2 ≠ q.2) :
    Set.InjOn Prod.snd
      {x : ℤ × ℤ | intPoint x ∈
        affineSpan ℝ ({intPoint m, intPoint q} : Set Plane)} := by
  intro x hx y hy hxy
  obtain ⟨s, hs1, hs2⟩ := intPoint_mem_pair_line_parameter (m := m) (q := q) hx
  obtain ⟨t, ht1, ht2⟩ := intPoint_mem_pair_line_parameter (m := m) (q := q) hy
  have hmq : ((q.2 : ℝ) - m.2) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hsecond.symm)
  have hst : s = t := by
    have hxyR : (x.2 : ℝ) = y.2 := by exact_mod_cast hxy
    apply (mul_right_cancel₀ hmq)
    linarith
  apply Prod.ext
  · exact_mod_cast (by rw [hs1, ht1, hst] : (x.1 : ℝ) = y.1)
  · exact hxy

noncomputable def expandedGridOnPairLine (N : ℕ) (m q : ℤ × ℤ) : Finset Plane :=
  by
    classical
    exact (expandedPlaneGrid N).filter fun z =>
      z ∈ affineSpan ℝ ({intPoint m, intPoint q} : Set Plane)

noncomputable def expandedGridOnEncodedAxis (N : ℕ) (a b : ℤ × ℤ)
    (hab : a ≠ b) : Finset Plane :=
  by
    classical
    exact (expandedPlaneGrid N).filter fun z =>
      z ∈ (encodedAxis a b hab : AffineSubspace ℝ Plane)

lemma card_expanded_grid_on_pair_line_le {N : ℕ} {m q : ℤ × ℤ}
    (hmq : m ≠ q) :
    (expandedGridOnPairLine N m q).card ≤ 4 * N + 1 := by
  classical
  let T := (expandedIntGrid N).filter fun z =>
    intPoint z ∈ affineSpan ℝ ({intPoint m, intPoint q} : Set Plane)
  have hcard :
      (expandedGridOnPairLine N m q).card = T.card := by
    unfold expandedGridOnPairLine expandedPlaneGrid
    rw [Finset.filter_image]
    exact Finset.card_image_of_injective _ intPoint_injective
  rw [hcard]
  by_cases hfirst : m.1 = q.1
  · have hsecond : m.2 ≠ q.2 := by
      intro h
      exact hmq (Prod.ext hfirst h)
    calc
      T.card = (T.image Prod.snd).card :=
        (Finset.card_image_of_injOn
          ((second_injOn_pair_line hsecond).mono
            (by intro x hx; exact (Finset.mem_filter.mp hx).2))).symm
      _ ≤ (expandedIntRange N).card := by
        apply Finset.card_le_card
        intro z hz
        rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
        exact (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).2
      _ = 4 * N + 1 := card_expandedIntRange N
  · calc
      T.card = (T.image Prod.fst).card :=
        (Finset.card_image_of_injOn
          ((first_injOn_pair_line hfirst).mono
            (by intro x hx; exact (Finset.mem_filter.mp hx).2))).symm
      _ ≤ (expandedIntRange N).card := by
        apply Finset.card_le_card
        intro z hz
        rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
        exact (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1
      _ = 4 * N + 1 := card_expandedIntRange N

lemma card_expanded_grid_on_encodedAxis_le {N : ℕ} {a b : ℤ × ℤ}
    (hab : a ≠ b) :
    (expandedGridOnEncodedAxis N a b hab).card ≤ 4 * N + 1 := by
  classical
  change (expandedGridOnPairLine N (axisFirst a b) (axisSecond a b)).card ≤
    4 * N + 1
  exact card_expanded_grid_on_pair_line_le (N := N) (axisFirst_ne_axisSecond hab)

abbrev AffineRealLine :=
  {ell : AffineSubspace ℝ Plane // IsAffineLine ell}

noncomputable def lineRichness (P : Finset Plane) (ell : AffineRealLine) : ℕ := by
  classical
  exact (P.filter fun p => p ∈ (ell : AffineSubspace ℝ Plane)).card

lemma lineRichness_expanded_le (N : ℕ) (ell : AffineRealLine) :
    lineRichness (expandedPlaneGrid N) ell ≤ 4 * N + 1 := by
  classical
  by_cases hsmall : lineRichness (expandedPlaneGrid N) ell < 2
  · omega
  · have htwo : 2 ≤ lineRichness (expandedPlaneGrid N) ell := by omega
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp htwo
    have hpP : p ∈ expandedPlaneGrid N := (Finset.mem_filter.mp hp).1
    have hqP : q ∈ expandedPlaneGrid N := (Finset.mem_filter.mp hq).1
    have hpell : p ∈ (ell : AffineSubspace ℝ Plane) :=
      (Finset.mem_filter.mp hp).2
    have hqell : q ∈ (ell : AffineSubspace ℝ Plane) :=
      (Finset.mem_filter.mp hq).2
    rcases Finset.mem_image.mp hpP with ⟨m, hm, rfl⟩
    rcases Finset.mem_image.mp hqP with ⟨q, hq, heq⟩
    subst heq
    have hmq : m ≠ q := fun h => hpq (h ▸ rfl)
    have line_le :
        affineSpan ℝ ({intPoint m, intPoint q} : Set Plane) ≤ ell :=
      affineSpan_le.2 (by
        intro z hz
        rcases hz with (rfl | hz)
        · exact hpell
        · simpa only [Set.mem_singleton_iff] using hz ▸ hqell)
    have line_rank : Module.finrank ℝ
        (affineSpan ℝ ({intPoint m, intPoint q} : Set Plane)).direction = 1 := by
      rw [direction_affineSpan, vectorSpan_pair]
      exact finrank_span_singleton (vsub_ne_zero.2 (intPoint_injective.ne hmq))
    have dir_eq :
        (affineSpan ℝ ({intPoint m, intPoint q} : Set Plane)).direction =
          ell.1.direction :=
      Submodule.eq_of_le_of_finrank_eq
        (AffineSubspace.direction_le line_le)
        (line_rank.trans ell.2.2.symm)
    have line_eq :
        affineSpan ℝ ({intPoint m, intPoint q} : Set Plane) = ell.1 :=
      AffineSubspace.ext_of_direction_eq dir_eq
        ⟨intPoint m, subset_affineSpan ℝ _ (by simp), hpell⟩
    change ((expandedPlaneGrid N).filter fun z => z ∈ ell.1).card ≤ 4 * N + 1
    rw [← line_eq]
    exact card_expanded_grid_on_pair_line_le hmq

lemma fourth_power_le_four_mul_sum_cubes (j : ℕ) :
    j ^ 4 ≤ 4 * ∑ k ∈ Finset.Icc 1 j, k ^ 3 := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ j + 1)]
      nlinarith [sq_nonneg (j : ℤ), sq_nonneg ((j : ℤ) + 1)]

lemma line_fourth_moment_bound
    (C : ℝ) (hC : 0 < C)
    (hRich : ∀ (P : Finset Plane) (k : ℕ),
      2 ≤ k → (k : ℝ) ≤ Real.sqrt (P.card : ℝ) →
        ∃ L : Finset AffineRealLine,
          (∀ ell, ell ∈ L ↔ k ≤ lineRichness P ell) ∧
          (L.card : ℝ) ≤ C * (P.card : ℝ) ^ 2 / (k : ℝ) ^ 3)
    {N : ℕ} (hN : 1 ≤ N) (L : Finset AffineRealLine)
    (hL : ∀ ell ∈ L, 2 ≤ lineRichness (expandedPlaneGrid N) ell) :
    (∑ ell ∈ L, (lineRichness (expandedPlaneGrid N) ell : ℝ) ^ 4) ≤
      4 * (4 * N + 1) * C *
        ((expandedPlaneGrid N).card : ℝ) ^ 2 := by
  classical
  let P := expandedPlaneGrid N
  let B := 4 * N + 1
  have hPB : P.card = B ^ 2 := by
    simp [P, B]
  have hsqrt : Real.sqrt (P.card : ℝ) = B := by
    rw [hPB, Nat.cast_pow, Real.sqrt_sq_eq_abs]
    simp
  have hrichRange {k : ℕ} (hk2 : 2 ≤ k) (hkB : k ≤ B) :
      (k : ℝ) ≤ Real.sqrt (P.card : ℝ) := by
    rw [hsqrt]
    exact_mod_cast hkB
  have htail (k : ℕ) (hk1 : 1 ≤ k) (hkB : k ≤ B) :
      (k : ℝ) ^ 3 *
          (((L.filter fun ell => k ≤ lineRichness P ell).card : ℕ) : ℝ) ≤
        C * (P.card : ℝ) ^ 2 := by
    by_cases hk : k = 1
    · subst k
      have htwoB : 2 ≤ B := by dsimp [B]; omega
      obtain ⟨R, hRmem, hRcard⟩ := hRich P 2 (by omega) (hrichRange (by omega) htwoB)
      have hsub : L.filter (fun ell => 1 ≤ lineRichness P ell) ⊆ R := by
        intro ell hell
        exact (hRmem ell).2 (hL ell (Finset.mem_filter.mp hell).1)
      have hcard :
          (((L.filter fun ell => 1 ≤ lineRichness P ell).card : ℕ) : ℝ) ≤
            (R.card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have hden : (0 : ℝ) ≤ C * (P.card : ℝ) ^ 2 := by positivity
      norm_num
      calc
        (((L.filter fun ell => 1 ≤ lineRichness P ell).card : ℕ) : ℝ) ≤
            (R.card : ℝ) := hcard
        _ ≤ C * (P.card : ℝ) ^ 2 / (2 : ℝ) ^ 3 := hRcard
        _ ≤ C * (P.card : ℝ) ^ 2 := by norm_num; linarith
    · have hk2 : 2 ≤ k := by omega
      obtain ⟨R, hRmem, hRcard⟩ := hRich P k hk2 (hrichRange hk2 hkB)
      have hsub : L.filter (fun ell => k ≤ lineRichness P ell) ⊆ R := by
        intro ell hell
        exact (hRmem ell).2 (Finset.mem_filter.mp hell).2
      have hcard :
          (((L.filter fun ell => k ≤ lineRichness P ell).card : ℕ) : ℝ) ≤
            (R.card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      calc
        (k : ℝ) ^ 3 *
              (((L.filter fun ell => k ≤ lineRichness P ell).card : ℕ) : ℝ) ≤
            (k : ℝ) ^ 3 * (R.card : ℝ) :=
          mul_le_mul_of_nonneg_left hcard (by positivity)
        _ ≤ (k : ℝ) ^ 3 *
              (C * (P.card : ℝ) ^ 2 / (k : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_left hRcard (by positivity)
        _ = C * (P.card : ℝ) ^ 2 := by field_simp
  have hlineB (ell : AffineRealLine) : lineRichness P ell ≤ B := by
    exact lineRichness_expanded_le N ell
  have hextend (ell : AffineRealLine) :
      (∑ k ∈ Finset.Icc 1 (lineRichness P ell), (k : ℝ) ^ 3) =
        ∑ k ∈ Finset.Icc 1 B,
          if k ≤ lineRichness P ell then (k : ℝ) ^ 3 else 0 := by
    symm
    calc
      (∑ k ∈ Finset.Icc 1 B,
          if k ≤ lineRichness P ell then (k : ℝ) ^ 3 else 0) =
          ∑ k ∈ (Finset.Icc 1 B).filter
            (fun k => k ≤ lineRichness P ell), (k : ℝ) ^ 3 := by
        rw [Finset.sum_filter]
      _ = ∑ k ∈ Finset.Icc 1 (lineRichness P ell), (k : ℝ) ^ 3 := by
        congr 1
        ext k
        simp only [Finset.mem_filter, Finset.mem_Icc]
        have := hlineB ell
        omega
  calc
    (∑ ell ∈ L, (lineRichness P ell : ℝ) ^ 4) ≤
        ∑ ell ∈ L,
          4 * ∑ k ∈ Finset.Icc 1 (lineRichness P ell), (k : ℝ) ^ 3 := by
      apply Finset.sum_le_sum
      intro ell hell
      norm_cast
      exact fourth_power_le_four_mul_sum_cubes (lineRichness P ell)
    _ = 4 * ∑ k ∈ Finset.Icc 1 B,
          (k : ℝ) ^ 3 *
            (((L.filter fun ell => k ≤ lineRichness P ell).card : ℕ) : ℝ) := by
      simp_rw [hextend]
      rw [← Finset.mul_sum]
      rw [Finset.sum_comm]
      apply congrArg (fun z : ℝ => 4 * z)
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.sum_filter]
      simp [mul_comm]
    _ ≤ 4 * ∑ _k ∈ Finset.Icc 1 B, C * (P.card : ℝ) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro k hk
      exact htail k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
    _ ≤ 4 * B * C * (P.card : ℝ) ^ 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hcard : (Finset.Icc 1 B).card ≤ B := by simp
      have hnonneg : 0 ≤ C * (P.card : ℝ) ^ 2 := by positivity
      have hcast : ((Finset.Icc 1 B).card : ℝ) ≤ B := by exact_mod_cast hcard
      nlinarith
    _ = 4 * (4 * N + 1) * C *
          ((expandedPlaneGrid N).card : ℝ) ^ 2 := by simp [P, B]

noncomputable def lineThrough (a b : Plane) (hab : a ≠ b) : AffineRealLine :=
  ⟨affineSpan ℝ ({a, b} : Set Plane),
    ⟨⟨a, subset_affineSpan ℝ _ (by simp)⟩, by
      rw [direction_affineSpan, vectorSpan_pair]
      exact finrank_span_singleton (vsub_ne_zero.2 hab)⟩⟩

noncomputable def gridLines (P : Finset Plane) : Finset AffineRealLine := by
  classical
  exact P.offDiag.attach.image fun e =>
    lineThrough e.1.1 e.1.2 (Finset.mem_offDiag.mp e.2).2.2

@[simp] lemma mem_lineThrough_left (a b : Plane) (hab : a ≠ b) :
    a ∈ (lineThrough a b hab : AffineSubspace ℝ Plane) := by
  exact subset_affineSpan ℝ _ (by simp)

@[simp] lemma mem_lineThrough_right (a b : Plane) (hab : a ≠ b) :
    b ∈ (lineThrough a b hab : AffineSubspace ℝ Plane) := by
  exact subset_affineSpan ℝ _ (by simp)

lemma lineThrough_mem_gridLines {P : Finset Plane} {a b : Plane}
    (ha : a ∈ P) (hb : b ∈ P) (hab : a ≠ b) :
    lineThrough a b hab ∈ gridLines P := by
  classical
  apply Finset.mem_image.mpr
  let e : {z // z ∈ P.offDiag} :=
    ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩⟩
  refine ⟨e, Finset.mem_attach _ _, ?_⟩
  simp only [e]

lemma two_le_lineRichness_of_mem_gridLines {P : Finset Plane}
    {ell : AffineRealLine} (hell : ell ∈ gridLines P) :
    2 ≤ lineRichness P ell := by
  classical
  rcases Finset.mem_image.mp hell with ⟨e, _he, rfl⟩
  have he := Finset.mem_offDiag.mp e.2
  let hne : e.1.1 ≠ e.1.2 := he.2.2
  change 2 ≤ (P.filter fun z =>
    z ∈ (lineThrough e.1.1 e.1.2 hne : AffineSubspace ℝ Plane)).card
  have hlt : 1 < (P.filter fun z =>
      z ∈ (lineThrough e.1.1 e.1.2 hne : AffineSubspace ℝ Plane)).card :=
    Finset.one_lt_card.mpr
      ⟨e.1.1, Finset.mem_filter.mpr ⟨he.1, mem_lineThrough_left _ _ hne⟩,
       e.1.2, Finset.mem_filter.mpr ⟨he.2.1, mem_lineThrough_right _ _ hne⟩, he.2.2⟩
  omega

noncomputable abbrev PointOf (P : Finset Plane) := {z : Plane // z ∈ P}

noncomputable abbrev PointOn (P : Finset Plane) (ell : AffineRealLine) :=
  {z : PointOf P // (z.1 : Plane) ∈ (ell : AffineSubspace ℝ Plane)}

noncomputable abbrev CollinearFour (P : Finset Plane) :=
  {x : Fin 4 → PointOf P //
    ∃ hne : (x 0 : Plane) ≠ (x 1 : Plane), ∀ i, (x i : Plane) ∈
      (lineThrough (x 0 : Plane) (x 1 : Plane) hne : AffineSubspace ℝ Plane)}

noncomputable abbrev TaggedCollinearFour (P : Finset Plane) :=
  (ell : {ell // ell ∈ gridLines P}) × (Fin 4 → PointOn P ell.1)

noncomputable def tagCollinearFour (P : Finset Plane) :
    CollinearFour P → TaggedCollinearFour P := fun x =>
  let hne : (x.1 0 : Plane) ≠ (x.1 1 : Plane) := x.2.choose
  let ell := lineThrough (x.1 0 : Plane) (x.1 1 : Plane) hne
  ⟨⟨ell, lineThrough_mem_gridLines (x.1 0).2 (x.1 1).2 hne⟩,
    fun i => ⟨x.1 i, x.2.choose_spec i⟩⟩

lemma tagCollinearFour_injective (P : Finset Plane) :
    Function.Injective (tagCollinearFour P) := by
  intro x y h
  apply Subtype.ext
  funext i
  apply Subtype.ext
  exact congrArg (fun z : TaggedCollinearFour P =>
    (((z.2 i).1 : PointOf P) : Plane)) h

lemma card_PointOn (P : Finset Plane) (ell : AffineRealLine) :
    Nat.card (PointOn P ell) = lineRichness P ell := by
  classical
  calc
    Nat.card (PointOn P ell) =
        (P.attach.filter fun z : PointOf P =>
          (z.1 : Plane) ∈ (ell : AffineSubspace ℝ Plane)).card :=
      Nat.subtype_card _ (fun z => by simp)
    _ = (P.filter fun z => z ∈ (ell : AffineSubspace ℝ Plane)).card := by
      let f : PointOf P ↪ Plane :=
        ⟨fun z => z.1, Subtype.val_injective⟩
      have hmap :
          (P.attach.filter fun z : PointOf P =>
              (z.1 : Plane) ∈ (ell : AffineSubspace ℝ Plane)).map f =
            P.filter fun z => z ∈ (ell : AffineSubspace ℝ Plane) := by
        ext z
        simp [f, and_comm]
      rw [← hmap, Finset.card_map]
    _ = lineRichness P ell := rfl

lemma card_CollinearFour_le_sum (P : Finset Plane) :
    Nat.card (CollinearFour P) ≤
      ∑ ell ∈ gridLines P, (lineRichness P ell) ^ 4 := by
  classical
  calc
    Nat.card (CollinearFour P) ≤ Nat.card (TaggedCollinearFour P) :=
      Nat.card_le_card_of_injective (tagCollinearFour P) (tagCollinearFour_injective P)
    _ = ∑ ell : {ell // ell ∈ gridLines P},
          Nat.card (Fin 4 → PointOn P ell.1) := by
      unfold TaggedCollinearFour
      exact Nat.card_sigma
    _ = ∑ ell : {ell // ell ∈ gridLines P},
          (lineRichness P ell.1) ^ 4 := by
      apply Finset.sum_congr rfl
      intro ell _
      rw [Nat.card_fun, card_PointOn, Nat.card_eq_fintype_card, Fintype.card_fin]
    _ = ∑ ell ∈ gridLines P, (lineRichness P ell) ^ 4 := by
      exact (Finset.sum_subtype (p := fun ell => ell ∈ gridLines P)
        (gridLines P) (fun _ => Iff.rfl)
        (fun ell => (lineRichness P ell) ^ 4)).symm

/-! The finite colored-`K₄` classification used below.  A permutation of the
vertices puts every coloring of the six edges by at most four colors into
one of four convenient forms: an equilateral triangle, two opposite-edge
equalities, a kite, or an isosceles triangle with a fixed-length extension. -/

def edgeIndex4 : Fin 4 → Fin 4 → Fin 6 :=
  ![![0, 0, 1, 2], ![0, 0, 3, 4], ![1, 3, 0, 5], ![2, 4, 5, 0]]

def FourColorPatternAt (c : Fin 6 → Fin 4) (σ : Fin 4 → Fin 4) : Prop :=
  (Finset.univ.image σ).card = 4 ∧
  let D := fun i j : Fin 4 => c (edgeIndex4 (σ i) (σ j));
    (D 0 1 = D 0 2 ∧ D 0 2 = D 1 2) ∨
    (D 0 2 = D 1 3 ∧ D 0 3 = D 1 2) ∨
    (D 0 2 = D 1 2 ∧ D 0 3 = D 1 3) ∨
    (D 0 1 = D 0 2 ∧
      (D 0 3 = D 0 1 ∨ D 0 3 = D 0 2 ∨ D 0 3 = D 1 2 ∨
       D 1 3 = D 0 1 ∨ D 1 3 = D 0 2 ∨ D 1 3 = D 1 2 ∨
       D 2 3 = D 0 1 ∨ D 2 3 = D 0 2 ∨ D 2 3 = D 1 2))

instance (c : Fin 6 → Fin 4) (σ : Fin 4 → Fin 4) :
    Decidable (FourColorPatternAt c σ) := by
  unfold FourColorPatternAt
  infer_instance

def FourColorPattern (c : Fin 6 → Fin 4) : Prop :=
  ∃ σ : Fin 4 → Fin 4, FourColorPatternAt c σ

instance (c : Fin 6 → Fin 4) : Decidable (FourColorPattern c) := by
  unfold FourColorPattern
  infer_instance

def FourColorPermPattern (c : Fin 6 → Fin 4) : Prop :=
  ∃ σ : Equiv.Perm (Fin 4), FourColorPatternAt c σ

instance (c : Fin 6 → Fin 4) : Decidable (FourColorPermPattern c) := by
  unfold FourColorPermPattern
  infer_instance

lemma four_color_perm_pattern00 (c2 c3 c4 c5 : Fin 4) :
    FourColorPermPattern ![0, 0, c2, c3, c4, c5] := by
  decide +revert

lemma four_color_perm_pattern01 (c2 c3 c4 c5 : Fin 4) :
    FourColorPermPattern ![0, 1, c2, c3, c4, c5] := by
  decide +revert

lemma four_color_perm_pattern02 (c2 c3 c4 c5 : Fin 4) :
    FourColorPermPattern ![0, 2, c2, c3, c4, c5] := by
  decide +revert

lemma four_color_perm_pattern03 (c2 c3 c4 c5 : Fin 4) :
    FourColorPermPattern ![0, 3, c2, c3, c4, c5] := by
  decide +revert

lemma four_color_perm_pattern0 (c1 c2 c3 c4 c5 : Fin 4) :
    FourColorPermPattern ![0, c1, c2, c3, c4, c5] := by
  fin_cases c1
  · exact four_color_perm_pattern00 c2 c3 c4 c5
  · exact four_color_perm_pattern01 c2 c3 c4 c5
  · exact four_color_perm_pattern02 c2 c3 c4 c5
  · exact four_color_perm_pattern03 c2 c3 c4 c5

lemma FourColorPermPattern.map_injective (c : Fin 6 → Fin 4)
    (f : Fin 4 → Fin 4) (hf : Function.Injective f) :
    FourColorPermPattern (f ∘ c) → FourColorPermPattern c := by
  rintro ⟨σ, hcard, h⟩
  refine ⟨σ, hcard, ?_⟩
  simpa only [Function.comp_apply, hf.eq_iff] using h

lemma four_color_perm_pattern (c : Fin 6 → Fin 4) :
    FourColorPermPattern c := by
  let e : Fin 4 ≃ Fin 4 := Equiv.swap (c 0) 0
  let c' : Fin 6 → Fin 4 := e ∘ c
  have hc'0 : c' 0 = 0 := by simp [c', e]
  have h := four_color_perm_pattern0 (c' 1) (c' 2) (c' 3) (c' 4) (c' 5)
  have heq : ![0, c' 1, c' 2, c' 3, c' 4, c' 5] = c' := by
    funext i
    fin_cases i <;> simp [hc'0]
  rw [heq] at h
  exact h.map_injective c e e.injective

lemma four_color_pattern (c : Fin 6 → Fin 4) : FourColorPattern c := by
  obtain ⟨σ, hσ⟩ := four_color_perm_pattern c
  exact ⟨σ, hσ⟩

lemma no_equilateral_integer_triangle {a b c : ℤ × ℤ} (hab : a ≠ b)
    (h₁ : intSqDist a b = intSqDist a c)
    (h₂ : intSqDist a b = intSqDist b c) : False := by
  let u₁ : ℤ := b.1 - a.1
  let u₂ : ℤ := b.2 - a.2
  let v₁ : ℤ := c.1 - a.1
  let v₂ : ℤ := c.2 - a.2
  let s : ℤ := u₁ ^ 2 + u₂ ^ 2
  let dot : ℤ := u₁ * v₁ + u₂ * v₂
  let det : ℤ := u₁ * v₂ - u₂ * v₁
  have h₁' : s = v₁ ^ 2 + v₂ ^ 2 := by
    dsimp [intSqDist] at h₁
    dsimp [u₁, u₂, v₁, v₂, s]
    nlinarith [h₁]
  have h₂' : s = (u₁ - v₁) ^ 2 + (u₂ - v₂) ^ 2 := by
    dsimp [intSqDist] at h₂
    dsimp [u₁, u₂, v₁, v₂, s]
    nlinarith [h₂]
  have hsnonneg : 0 ≤ s := by dsimp [s]; positivity
  have hsne : s ≠ 0 := by
    intro hs
    have hu₁ : u₁ = 0 := by
      have : u₁ ^ 2 ≤ 0 := by
        calc
          u₁ ^ 2 ≤ u₁ ^ 2 + u₂ ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
          _ = 0 := by simpa [s] using hs
      exact (sq_eq_zero_iff.mp (le_antisymm this (sq_nonneg _)))
    have hu₂ : u₂ = 0 := by
      have : u₂ ^ 2 ≤ 0 := by
        calc
          u₂ ^ 2 ≤ u₁ ^ 2 + u₂ ^ 2 := le_add_of_nonneg_left (sq_nonneg _)
          _ = 0 := by simpa [s] using hs
      exact (sq_eq_zero_iff.mp (le_antisymm this (sq_nonneg _)))
    apply hab
    apply Prod.ext <;> dsimp [u₁, u₂] at hu₁ hu₂ ⊢ <;> omega
  have hspos : 0 < s := lt_of_le_of_ne hsnonneg (Ne.symm hsne)
  have hdot : 2 * dot = s := by
    dsimp [dot]
    nlinarith [h₁', h₂']
  have hlagrange : det ^ 2 + dot ^ 2 = s ^ 2 := by
    calc
      det ^ 2 + dot ^ 2 = s * (v₁ ^ 2 + v₂ ^ 2) := by
        dsimp [det, dot, s]
        ring
      _ = s ^ 2 := by rw [← h₁']; ring
  have hmain : 4 * det ^ 2 = 3 * s ^ 2 := by
    nlinarith
  have hsR : (0 : ℝ) < s := by exact_mod_cast hspos
  have hratioSq : (((2 * det : ℤ) : ℝ) / (s : ℝ)) ^ 2 = 3 := by
    have hmainR : (4 : ℝ) * (det : ℝ) ^ 2 = 3 * (s : ℝ) ^ 2 := by
      exact_mod_cast hmain
    calc
      (((2 * det : ℤ) : ℝ) / (s : ℝ)) ^ 2 =
          ((4 : ℝ) * (det : ℝ) ^ 2) / (s : ℝ) ^ 2 := by
        push_cast
        ring
      _ = 3 := (div_eq_iff (pow_ne_zero 2 hsR.ne')).2 hmainR
  have hsqrt : Real.sqrt 3 = |(((2 * det : ℤ) : ℝ) / (s : ℝ))| := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (abs_nonneg _)).mp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), sq_abs, hratioSq]
  have hirr := (Nat.Prime.irrational_sqrt (by norm_num : Nat.Prime 3)).ne_rational
    |2 * det| s
  apply hirr
  calc
    Real.sqrt ((3 : ℕ) : ℝ) = Real.sqrt (3 : ℝ) := by norm_num
    _ = |(((2 * det : ℤ) : ℝ) / (s : ℝ))| := hsqrt
    _ = ((|2 * det| : ℤ) : ℝ) / (s : ℝ) := by
      rw [abs_div, abs_of_pos hsR]
      norm_num

def edgeStart4 : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]

def edgeEnd4 : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]

lemma edgeStart4_ne_edgeEnd4 (i : Fin 6) : edgeStart4 i ≠ edgeEnd4 i := by
  fin_cases i <;> decide

lemma edgeIndex4_start_end (i : Fin 6) :
    edgeIndex4 (edgeStart4 i) (edgeEnd4 i) = i := by
  fin_cases i <;> rfl

def edgeSqDists (x : Fin 4 → ℤ × ℤ) (i : Fin 6) : ℤ :=
  intSqDist (x (edgeStart4 i)) (x (edgeEnd4 i))

lemma edgeSqDists_edgeIndex4_of_ne (x : Fin 4 → ℤ × ℤ) (i j : Fin 4) (hij : i ≠ j) :
    edgeSqDists x (edgeIndex4 i j) = intSqDist (x i) (x j) := by
  fin_cases i <;> fin_cases j <;>
    simp_all [edgeSqDists, edgeIndex4, edgeStart4, edgeEnd4, intSqDist] <;> ring

noncomputable def orderedQuadSet (x : Fin 4 → ℤ × ℤ) : Finset Plane :=
  (Finset.univ.image x).image intPoint

lemma edgeSqDists_range_card_le_distanceCount {x : Fin 4 → ℤ × ℤ}
    (hx : Function.Injective x) :
    (Finset.univ.image (edgeSqDists x)).card ≤
      distanceCount (orderedQuadSet x) := by
  classical
  let R := Finset.univ.image (edgeSqDists x)
  let root : ℤ → ℝ := fun z => Real.sqrt (z : ℝ)
  have hnonneg {z : ℤ} (hz : z ∈ R) : 0 ≤ z := by
    rcases Finset.mem_image.mp hz with ⟨i, _hi, rfl⟩
    exact intSqDist_nonneg _ _
  have hrootinj : Set.InjOn root R := by
    intro z hz w hw hzw
    have hs := congrArg (fun t : ℝ => t ^ 2) hzw
    rw [Real.sq_sqrt (by exact_mod_cast hnonneg hz),
      Real.sq_sqrt (by exact_mod_cast hnonneg hw)] at hs
    exact_mod_cast hs
  have hsubset : R.image root ⊆ distinctDistances (orderedQuadSet x) := by
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨z, hzR, rfl⟩
    rcases Finset.mem_image.mp hzR with ⟨i, _hi, rfl⟩
    let a := x (edgeStart4 i)
    let b := x (edgeEnd4 i)
    have hab : a ≠ b := hx.ne (edgeStart4_ne_edgeEnd4 i)
    have ha : intPoint a ∈ orderedQuadSet x := by
      exact Finset.mem_image.mpr ⟨a, Finset.mem_image.mpr
        ⟨edgeStart4 i, Finset.mem_univ _, rfl⟩, rfl⟩
    have hb : intPoint b ∈ orderedQuadSet x := by
      exact Finset.mem_image.mpr ⟨b, Finset.mem_image.mpr
        ⟨edgeEnd4 i, Finset.mem_univ _, rfl⟩, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨(intPoint a, intPoint b), Finset.mem_offDiag.mpr
      ⟨ha, hb, intPoint_injective.ne hab⟩, ?_⟩
    symm
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) dist_nonneg).mp
    rw [Real.sq_sqrt (by exact_mod_cast intSqDist_nonneg a b), dist_intPoint_sq]
    rfl
  calc
    (Finset.univ.image (edgeSqDists x)).card = R.card := rfl
    _ = (R.image root).card :=
      (Finset.card_image_of_injOn hrootinj).symm
    _ ≤ (distinctDistances (orderedQuadSet x)).card := Finset.card_le_card hsubset
    _ = distanceCount (orderedQuadSet x) := rfl

def OrderedDistancePattern (x : Fin 4 → ℤ × ℤ) : Prop :=
  ∃ σ : Fin 4 → Fin 4, Function.Injective σ ∧
    let D := fun i j : Fin 4 =>
      intSqDist (x (σ i)) (x (σ j))
    (D 0 1 = D 0 2 ∧ D 0 2 = D 1 2) ∨
    (D 0 2 = D 1 3 ∧ D 0 3 = D 1 2) ∨
    (D 0 2 = D 1 2 ∧ D 0 3 = D 1 3) ∨
    (D 0 1 = D 0 2 ∧
      (D 0 3 = D 0 1 ∨ D 0 3 = D 0 2 ∨ D 0 3 = D 1 2 ∨
       D 1 3 = D 0 1 ∨ D 1 3 = D 0 2 ∨ D 1 3 = D 1 2 ∨
       D 2 3 = D 0 1 ∨ D 2 3 = D 0 2 ∨ D 2 3 = D 1 2))

lemma ordered_distance_pattern_of_card_le_four
    {x : Fin 4 → ℤ × ℤ} (hx : Function.Injective x)
    (hcard : distanceCount (orderedQuadSet x) ≤ 4) :
    OrderedDistancePattern x := by
  classical
  let R := Finset.univ.image (edgeSqDists x)
  have hRcard : R.card ≤ 4 :=
    (edgeSqDists_range_card_le_distanceCount hx).trans hcard
  let e : R ≃ Fin (Fintype.card R) := Fintype.equivFin R
  let color : Fin 6 → Fin 4 := fun i =>
    ⟨(e ⟨edgeSqDists x i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩).1,
      (e ⟨edgeSqDists x i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩).2.trans_le
        (by simpa using hRcard)⟩
  have hcolor {i j : Fin 6} : color i = color j ↔
      edgeSqDists x i = edgeSqDists x j := by
    constructor
    · intro h
      have hv : (color i).val = (color j).val :=
        congrArg (fun z : Fin 4 => z.val) h
      have heq :
          e ⟨edgeSqDists x i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩ =
            e ⟨edgeSqDists x j, Finset.mem_image.mpr
              ⟨j, Finset.mem_univ _, rfl⟩⟩ := by
        exact Fin.ext hv
      exact congrArg Subtype.val (e.injective heq)
    · exact fun h => by simp only [color, h]
  obtain ⟨σ, hσcard, hp⟩ := four_color_pattern color
  have hσinj : Function.Injective σ := by
    have hc : (Finset.univ.image σ).card =
        (Finset.univ : Finset (Fin 4)).card := by simpa using hσcard
    have hi :=
      (Finset.card_image_iff (s := (Finset.univ : Finset (Fin 4))) (f := σ)).mp hc
    intro i j hij
    exact hi (Finset.mem_univ i) (Finset.mem_univ j) hij
  refine ⟨σ, hσinj, ?_⟩
  dsimp only
  simp only [hcolor] at hp
  have h01 := edgeSqDists_edgeIndex4_of_ne x (σ 0) (σ 1)
    (hσinj.ne (by decide))
  have h02 := edgeSqDists_edgeIndex4_of_ne x (σ 0) (σ 2)
    (hσinj.ne (by decide))
  have h03 := edgeSqDists_edgeIndex4_of_ne x (σ 0) (σ 3)
    (hσinj.ne (by decide))
  have h12 := edgeSqDists_edgeIndex4_of_ne x (σ 1) (σ 2)
    (hσinj.ne (by decide))
  have h13 := edgeSqDists_edgeIndex4_of_ne x (σ 1) (σ 3)
    (hσinj.ne (by decide))
  have h23 := edgeSqDists_edgeIndex4_of_ne x (σ 2) (σ 3)
    (hσinj.ne (by decide))
  simp only [h01, h02, h03, h12, h13, h23] at hp
  exact hp

/-! ## Injective encodings of the two four-point line patterns -/

noncomputable abbrev GridPoint (N : ℕ) := {z : ℤ × ℤ // z ∈ intGrid N}

noncomputable abbrev InjectiveGridFour (N : ℕ) :=
  {x : Fin 4 → GridPoint N // Function.Injective x}

noncomputable abbrev KiteFour (N : ℕ) :=
  {x : InjectiveGridFour N //
    intSqDist (x.1 0).1 (x.1 2).1 = intSqDist (x.1 1).1 (x.1 2).1 ∧
    intSqDist (x.1 0).1 (x.1 3).1 = intSqDist (x.1 1).1 (x.1 3).1}

noncomputable abbrev OppositeFour (N : ℕ) :=
  {x : InjectiveGridFour N //
    intSqDist (x.1 0).1 (x.1 2).1 = intSqDist (x.1 1).1 (x.1 3).1 ∧
    intSqDist (x.1 0).1 (x.1 3).1 = intSqDist (x.1 1).1 (x.1 2).1 ∧
    (x.1 0).1 + (x.1 1).1 ≠ (x.1 2).1 + (x.1 3).1}

def kiteCode (x : Fin 4 → ℤ × ℤ) : Fin 4 → ℤ × ℤ :=
  ![axisFirst (x 0) (x 1), axisSecond (x 0) (x 1), 2 • x 2, 2 • x 3]

lemma kiteCode_injective : Function.Injective kiteCode := by
  intro x y hxy
  have h0 := congrFun hxy (0 : Fin 4)
  have h1 := congrFun hxy (1 : Fin 4)
  have h2 := congrFun hxy (2 : Fin 4)
  have h3 := congrFun hxy (3 : Fin 4)
  have h01 : (x 0, x 1) = (y 0, y 1) :=
    axisEncoding_injective (Prod.ext h0 h1)
  have hx0 : x 0 = y 0 := congrArg Prod.fst h01
  have hx1 : x 1 = y 1 := congrArg Prod.snd h01
  have hx2 : x 2 = y 2 := by
    have h20 := congrArg Prod.fst h2
    have h21 := congrArg Prod.snd h2
    apply Prod.ext <;> simp [kiteCode] at h20 h21 ⊢ <;> omega
  have hx3 : x 3 = y 3 := by
    have h30 := congrArg Prod.fst h3
    have h31 := congrArg Prod.snd h3
    apply Prod.ext <;> simp [kiteCode] at h30 h31 ⊢ <;> omega
  funext i
  fin_cases i
  · exact hx0
  · exact hx1
  · exact hx2
  · exact hx3

noncomputable def kiteToCollinear (N : ℕ) :
    KiteFour N → CollinearFour (expandedPlaneGrid N) := fun x => by
  let a : ℤ × ℤ := (x.1.1 0).1
  let b : ℤ × ℤ := (x.1.1 1).1
  let c : ℤ × ℤ := (x.1.1 2).1
  let d : ℤ × ℤ := (x.1.1 3).1
  have hab : a ≠ b := by
    intro h
    have hx : x.1.1 0 = x.1.1 1 := Subtype.ext h
    exact (show (0 : Fin 4) ≠ 1 by decide) (x.1.2 hx)
  have ha : a ∈ intGrid N := (x.1.1 0).2
  have hb : b ∈ intGrid N := (x.1.1 1).2
  have hc : c ∈ intGrid N := (x.1.1 2).2
  have hd : d ∈ intGrid N := (x.1.1 3).2
  have hcode (i : Fin 4) : kiteCode (fun j => (x.1.1 j).1) i ∈ expandedIntGrid N := by
    fin_cases i
    · exact axisFirst_mem_expanded ha hb
    · exact axisSecond_mem_expanded ha hb
    · exact two_smul_mem_expanded hc
    · exact two_smul_mem_expanded hd
  let y : Fin 4 → PointOf (expandedPlaneGrid N) := fun i =>
    ⟨intPoint (kiteCode (fun j => (x.1.1 j).1) i),
      Finset.mem_image.mpr ⟨_, hcode i, rfl⟩⟩
  refine ⟨y, ?_⟩
  have hy01 : (y 0 : Plane) ≠ (y 1 : Plane) := by
    apply intPoint_injective.ne
    simpa [y, kiteCode, a, b] using axisFirst_ne_axisSecond hab
  refine ⟨hy01, ?_⟩
  intro i
  fin_cases i
  · exact mem_lineThrough_left _ _ hy01
  · exact mem_lineThrough_right _ _ hy01
  · change intPoint (2 • c) ∈
      affineSpan ℝ ({intPoint (axisFirst a b), intPoint (axisSecond a b)} : Set Plane)
    exact equidistant_mem_encodedAxis hab (by
      rw [intSqDist_comm c a, intSqDist_comm c b]
      exact x.2.1)
  · change intPoint (2 • d) ∈
      affineSpan ℝ ({intPoint (axisFirst a b), intPoint (axisSecond a b)} : Set Plane)
    exact equidistant_mem_encodedAxis hab (by
      rw [intSqDist_comm d a, intSqDist_comm d b]
      exact x.2.2)

lemma kiteToCollinear_injective (N : ℕ) :
    Function.Injective (kiteToCollinear N) := by
  intro x y hxy
  have hcode : kiteCode (fun i => (x.1.1 i).1) =
      kiteCode (fun i => (y.1.1 i).1) := by
    funext i
    apply intPoint_injective
    exact congrArg (fun z : CollinearFour (expandedPlaneGrid N) =>
      ((z.1 i).1 : Plane)) hxy
  have hpoints := kiteCode_injective hcode
  apply Subtype.ext
  apply Subtype.ext
  funext i
  apply Subtype.ext
  exact congrFun hpoints i

lemma card_KiteFour_le_collinear (N : ℕ) :
    Nat.card (KiteFour N) ≤
      Nat.card (CollinearFour (expandedPlaneGrid N)) :=
  Nat.card_le_card_of_injective (kiteToCollinear N) (kiteToCollinear_injective N)

def intDot (u v : ℤ × ℤ) : ℤ := u.1 * v.1 + u.2 * v.2

lemma opposite_equalities_dot_zero {a b c d : ℤ × ℤ}
    (h₁ : intSqDist a c = intSqDist b d)
    (h₂ : intSqDist a d = intSqDist b c) :
    intDot (c + d - (a + b)) (a - b) = 0 ∧
      intDot (c + d - (a + b)) (c - d) = 0 := by
  constructor <;>
    dsimp [intSqDist, intDot] at h₁ h₂ ⊢ <;>
    nlinarith [h₁, h₂]

lemma intPoint_add_rot90_mem_lineThrough {m n u : ℤ × ℤ}
    (hmn : m ≠ n) (horth : intDot (n - m) u = 0) :
    intPoint (m + rot90Int u) ∈
      (lineThrough (intPoint m) (intPoint n) (intPoint_injective.ne hmn) :
        AffineSubspace ℝ Plane) := by
  change intPoint (m + rot90Int u) ∈
    affineSpan ℝ ({intPoint m, intPoint n} : Set Plane)
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  let v : ℝ × ℝ := (((n.1 - m.1 : ℤ) : ℝ), ((n.2 - m.2 : ℤ) : ℝ))
  let w : ℝ × ℝ := ((-(u.2 : ℤ) : ℤ), u.1)
  have hv : v ≠ 0 := by
    intro hvz
    have h1 := congrArg Prod.fst hvz
    have h2 := congrArg Prod.snd hvz
    dsimp [v] at h1 h2
    have h1Z : n.1 - m.1 = 0 := by exact_mod_cast h1
    have h2Z : n.2 - m.2 = 0 := by exact_mod_cast h2
    exact hmn (Prod.ext (by omega) (by omega))
  have hdet : pairDet v w = 0 := by
    have horthR :
        ((n.1 - m.1 : ℤ) : ℝ) * (u.1 : ℝ) +
          ((n.2 - m.2 : ℤ) : ℝ) * (u.2 : ℝ) = 0 := by
      exact_mod_cast horth
    dsimp [pairDet, v, w]
    push_cast at horthR ⊢
    ring_nf at horthR ⊢
    exact horthR
  obtain ⟨t, ht⟩ := exists_smul_of_pairDet_eq_zero hv hdet
  refine ⟨t, ?_⟩
  rw [AffineMap.lineMap_apply]
  have ht1 := congrArg Prod.fst ht
  have ht2 := congrArg Prod.snd ht
  ext i
  fin_cases i <;>
    simp [intPoint, rot90Int, v, w] at ht1 ht2 ⊢ <;> linarith

lemma intPoint_second_add_rot90_mem_lineThrough {m n u : ℤ × ℤ}
    (hmn : m ≠ n) (horth : intDot (n - m) u = 0) :
    intPoint (n + rot90Int u) ∈
      (lineThrough (intPoint m) (intPoint n) (intPoint_injective.ne hmn) :
        AffineSubspace ℝ Plane) := by
  have horth' : intDot (m - n) u = 0 := by
    dsimp [intDot] at horth ⊢
    linarith
  have h := intPoint_add_rot90_mem_lineThrough (m := n) (n := m) (u := u)
    hmn.symm horth'
  change intPoint (n + rot90Int u) ∈
    affineSpan ℝ ({intPoint m, intPoint n} : Set Plane)
  change intPoint (n + rot90Int u) ∈
    affineSpan ℝ ({intPoint n, intPoint m} : Set Plane) at h
  rw [AffineSubspace.affineSpan_pair_comm]
  exact h

def oppositeCode (x : Fin 4 → ℤ × ℤ) : Fin 4 → ℤ × ℤ :=
  ![x 0 + x 1, x 2 + x 3,
    x 0 + x 1 + rot90Int (x 0 - x 1),
    x 2 + x 3 + rot90Int (x 2 - x 3)]

lemma oppositeCode_injective : Function.Injective oppositeCode := by
  intro x y hxy
  have h0 := congrFun hxy (0 : Fin 4)
  have h1 := congrFun hxy (1 : Fin 4)
  have h2 := congrFun hxy (2 : Fin 4)
  have h3 := congrFun hxy (3 : Fin 4)
  have h01 : (x 0, x 1) = (y 0, y 1) :=
    axisEncoding_injective (Prod.ext h0 h2)
  have h23 : (x 2, x 3) = (y 2, y 3) :=
    axisEncoding_injective (Prod.ext h1 h3)
  funext i
  fin_cases i
  · exact congrArg Prod.fst h01
  · exact congrArg Prod.snd h01
  · exact congrArg Prod.fst h23
  · exact congrArg Prod.snd h23

noncomputable def oppositeToCollinear (N : ℕ) :
    OppositeFour N → CollinearFour (expandedPlaneGrid N) := fun x => by
  let a : ℤ × ℤ := (x.1.1 0).1
  let b : ℤ × ℤ := (x.1.1 1).1
  let c : ℤ × ℤ := (x.1.1 2).1
  let d : ℤ × ℤ := (x.1.1 3).1
  let m : ℤ × ℤ := a + b
  let n : ℤ × ℤ := c + d
  have hmn : m ≠ n := x.2.2.2
  have ha : a ∈ intGrid N := (x.1.1 0).2
  have hb : b ∈ intGrid N := (x.1.1 1).2
  have hc : c ∈ intGrid N := (x.1.1 2).2
  have hd : d ∈ intGrid N := (x.1.1 3).2
  have hcode (i : Fin 4) : oppositeCode (fun j => (x.1.1 j).1) i ∈
      expandedIntGrid N := by
    fin_cases i
    · exact axisFirst_mem_expanded ha hb
    · exact axisFirst_mem_expanded hc hd
    · exact axisSecond_mem_expanded ha hb
    · exact axisSecond_mem_expanded hc hd
  let y : Fin 4 → PointOf (expandedPlaneGrid N) := fun i =>
    ⟨intPoint (oppositeCode (fun j => (x.1.1 j).1) i),
      Finset.mem_image.mpr ⟨_, hcode i, rfl⟩⟩
  refine ⟨y, ?_⟩
  have hy01 : (y 0 : Plane) ≠ (y 1 : Plane) := by
    apply intPoint_injective.ne
    simpa [y, oppositeCode, m, n] using hmn
  refine ⟨hy01, ?_⟩
  obtain ⟨hu, hv⟩ := opposite_equalities_dot_zero x.2.1 x.2.2.1
  intro i
  fin_cases i
  · exact mem_lineThrough_left _ _ hy01
  · exact mem_lineThrough_right _ _ hy01
  · change intPoint (m + rot90Int (a - b)) ∈
      (lineThrough (intPoint m) (intPoint n) (intPoint_injective.ne hmn) :
        AffineSubspace ℝ Plane)
    exact intPoint_add_rot90_mem_lineThrough hmn (by simpa [m, n] using hu)
  · change intPoint (n + rot90Int (c - d)) ∈
      (lineThrough (intPoint m) (intPoint n) (intPoint_injective.ne hmn) :
        AffineSubspace ℝ Plane)
    exact intPoint_second_add_rot90_mem_lineThrough hmn (by simpa [m, n] using hv)

lemma oppositeToCollinear_injective (N : ℕ) :
    Function.Injective (oppositeToCollinear N) := by
  intro x y hxy
  have hcode : oppositeCode (fun i => (x.1.1 i).1) =
      oppositeCode (fun i => (y.1.1 i).1) := by
    funext i
    apply intPoint_injective
    exact congrArg (fun z : CollinearFour (expandedPlaneGrid N) =>
      ((z.1 i).1 : Plane)) hxy
  have hpoints := oppositeCode_injective hcode
  apply Subtype.ext
  apply Subtype.ext
  funext i
  apply Subtype.ext
  exact congrFun hpoints i

lemma card_OppositeFour_le_collinear (N : ℕ) :
    Nat.card (OppositeFour N) ≤
      Nat.card (CollinearFour (expandedPlaneGrid N)) :=
  Nat.card_le_card_of_injective (oppositeToCollinear N)
    (oppositeToCollinear_injective N)

/-! ## Isosceles triples and the third rich-line moment -/

noncomputable abbrev CollinearThree (P : Finset Plane) :=
  {x : Fin 3 → PointOf P //
    ∃ hne : (x 0 : Plane) ≠ (x 1 : Plane), ∀ i, (x i : Plane) ∈
      (lineThrough (x 0 : Plane) (x 1 : Plane) hne : AffineSubspace ℝ Plane)}

noncomputable abbrev TaggedCollinearThree (P : Finset Plane) :=
  (ell : {ell // ell ∈ gridLines P}) × (Fin 3 → PointOn P ell.1)

noncomputable def tagCollinearThree (P : Finset Plane) :
    CollinearThree P → TaggedCollinearThree P := fun x =>
  let hne : (x.1 0 : Plane) ≠ (x.1 1 : Plane) := x.2.choose
  let ell := lineThrough (x.1 0 : Plane) (x.1 1 : Plane) hne
  ⟨⟨ell, lineThrough_mem_gridLines (x.1 0).2 (x.1 1).2 hne⟩,
    fun i => ⟨x.1 i, x.2.choose_spec i⟩⟩

lemma tagCollinearThree_injective (P : Finset Plane) :
    Function.Injective (tagCollinearThree P) := by
  intro x y h
  apply Subtype.ext
  funext i
  apply Subtype.ext
  exact congrArg (fun z : TaggedCollinearThree P =>
    (((z.2 i).1 : PointOf P) : Plane)) h

lemma card_CollinearThree_le_sum (P : Finset Plane) :
    Nat.card (CollinearThree P) ≤
      ∑ ell ∈ gridLines P, (lineRichness P ell) ^ 3 := by
  classical
  calc
    Nat.card (CollinearThree P) ≤ Nat.card (TaggedCollinearThree P) :=
      Nat.card_le_card_of_injective (tagCollinearThree P) (tagCollinearThree_injective P)
    _ = ∑ ell : {ell // ell ∈ gridLines P},
          Nat.card (Fin 3 → PointOn P ell.1) := by
      unfold TaggedCollinearThree
      exact Nat.card_sigma
    _ = ∑ ell : {ell // ell ∈ gridLines P},
          (lineRichness P ell.1) ^ 3 := by
      apply Finset.sum_congr rfl
      intro ell _
      rw [Nat.card_fun, card_PointOn, Nat.card_eq_fintype_card, Fintype.card_fin]
    _ = ∑ ell ∈ gridLines P, (lineRichness P ell) ^ 3 := by
      exact (Finset.sum_subtype (p := fun ell => ell ∈ gridLines P)
        (gridLines P) (fun _ => Iff.rfl)
        (fun ell => (lineRichness P ell) ^ 3)).symm

lemma third_power_le_three_mul_sum_squares (j : ℕ) :
    j ^ 3 ≤ 3 * ∑ k ∈ Finset.Icc 1 j, k ^ 2 := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ j + 1)]
      calc
        (j + 1) ^ 3 = j ^ 3 + 3 * j ^ 2 + 3 * j + 1 := by ring
        _ ≤ j ^ 3 + 3 * j ^ 2 + 6 * j + 3 := by omega
        _ = j ^ 3 + 3 * (j + 1) ^ 2 := by ring
        _ ≤ 3 * (∑ k ∈ Finset.Icc 1 j, k ^ 2) + 3 * (j + 1) ^ 2 :=
          Nat.add_le_add_right ih _
        _ = 3 * (∑ k ∈ Finset.Icc 1 j, k ^ 2 + (j + 1) ^ 2) := by ring

lemma line_third_moment_bound
    (C : ℝ) (hC : 0 < C)
    (hRich : ∀ (P : Finset Plane) (k : ℕ),
      2 ≤ k → (k : ℝ) ≤ Real.sqrt (P.card : ℝ) →
        ∃ L : Finset AffineRealLine,
          (∀ ell, ell ∈ L ↔ k ≤ lineRichness P ell) ∧
          (L.card : ℝ) ≤ C * (P.card : ℝ) ^ 2 / (k : ℝ) ^ 3)
    {N : ℕ} (hN : 1 ≤ N) (L : Finset AffineRealLine)
    (hL : ∀ ell ∈ L, 2 ≤ lineRichness (expandedPlaneGrid N) ell) :
    (∑ ell ∈ L, (lineRichness (expandedPlaneGrid N) ell : ℝ) ^ 3) ≤
      3 * C * ((expandedPlaneGrid N).card : ℝ) ^ 2 *
        (1 + Real.log (4 * N + 1 : ℕ)) := by
  classical
  let P := expandedPlaneGrid N
  let B := 4 * N + 1
  have hPB : P.card = B ^ 2 := by simp [P, B]
  have hsqrt : Real.sqrt (P.card : ℝ) = B := by
    rw [hPB, Nat.cast_pow, Real.sqrt_sq_eq_abs]
    simp
  have hrichRange {k : ℕ} (hk2 : 2 ≤ k) (hkB : k ≤ B) :
      (k : ℝ) ≤ Real.sqrt (P.card : ℝ) := by
    rw [hsqrt]
    exact_mod_cast hkB
  have htail (k : ℕ) (hk1 : 1 ≤ k) (hkB : k ≤ B) :
      (k : ℝ) ^ 2 *
          (((L.filter fun ell => k ≤ lineRichness P ell).card : ℕ) : ℝ) ≤
        C * (P.card : ℝ) ^ 2 / (k : ℝ) := by
    by_cases hk : k = 1
    · subst k
      have htwoB : 2 ≤ B := by dsimp [B]; omega
      obtain ⟨R, hRmem, hRcard⟩ := hRich P 2 (by omega) (hrichRange (by omega) htwoB)
      have hsub : L.filter (fun ell => 1 ≤ lineRichness P ell) ⊆ R := by
        intro ell hell
        exact (hRmem ell).2 (hL ell (Finset.mem_filter.mp hell).1)
      have hcard :
          (((L.filter fun ell => 1 ≤ lineRichness P ell).card : ℕ) : ℝ) ≤
            (R.card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      norm_num
      calc
        (((L.filter fun ell => 1 ≤ lineRichness P ell).card : ℕ) : ℝ) ≤
            (R.card : ℝ) := hcard
        _ ≤ C * (P.card : ℝ) ^ 2 / (2 : ℝ) ^ 3 := hRcard
        _ ≤ C * (P.card : ℝ) ^ 2 := by
          have : 0 ≤ C * (P.card : ℝ) ^ 2 := by positivity
          norm_num
          linarith
    · have hk2 : 2 ≤ k := by omega
      obtain ⟨R, hRmem, hRcard⟩ := hRich P k hk2 (hrichRange hk2 hkB)
      have hsub : L.filter (fun ell => k ≤ lineRichness P ell) ⊆ R := by
        intro ell hell
        exact (hRmem ell).2 (Finset.mem_filter.mp hell).2
      have hcard :
          (((L.filter fun ell => k ≤ lineRichness P ell).card : ℕ) : ℝ) ≤
            (R.card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      calc
        (k : ℝ) ^ 2 *
              (((L.filter fun ell => k ≤ lineRichness P ell).card : ℕ) : ℝ) ≤
            (k : ℝ) ^ 2 * (R.card : ℝ) :=
          mul_le_mul_of_nonneg_left hcard (by positivity)
        _ ≤ (k : ℝ) ^ 2 *
              (C * (P.card : ℝ) ^ 2 / (k : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_left hRcard (by positivity)
        _ = C * (P.card : ℝ) ^ 2 / (k : ℝ) := by
          field_simp
  have hlineB (ell : AffineRealLine) : lineRichness P ell ≤ B :=
    lineRichness_expanded_le N ell
  have hextend (ell : AffineRealLine) :
      (∑ k ∈ Finset.Icc 1 (lineRichness P ell), (k : ℝ) ^ 2) =
        ∑ k ∈ Finset.Icc 1 B,
          if k ≤ lineRichness P ell then (k : ℝ) ^ 2 else 0 := by
    symm
    calc
      (∑ k ∈ Finset.Icc 1 B,
          if k ≤ lineRichness P ell then (k : ℝ) ^ 2 else 0) =
          ∑ k ∈ (Finset.Icc 1 B).filter
            (fun k => k ≤ lineRichness P ell), (k : ℝ) ^ 2 := by
        rw [Finset.sum_filter]
      _ = ∑ k ∈ Finset.Icc 1 (lineRichness P ell), (k : ℝ) ^ 2 := by
        congr 1
        ext k
        simp only [Finset.mem_filter, Finset.mem_Icc]
        have := hlineB ell
        omega
  have hsumInv :
      (∑ k ∈ Finset.Icc 1 B, ((k : ℝ)⁻¹)) = (harmonic B : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  calc
    (∑ ell ∈ L, (lineRichness P ell : ℝ) ^ 3) ≤
        ∑ ell ∈ L,
          3 * ∑ k ∈ Finset.Icc 1 (lineRichness P ell), (k : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro ell hell
      norm_cast
      exact third_power_le_three_mul_sum_squares (lineRichness P ell)
    _ = 3 * ∑ k ∈ Finset.Icc 1 B,
          (k : ℝ) ^ 2 *
            (((L.filter fun ell => k ≤ lineRichness P ell).card : ℕ) : ℝ) := by
      simp_rw [hextend]
      rw [← Finset.mul_sum, Finset.sum_comm]
      apply congrArg (fun z : ℝ => 3 * z)
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.sum_filter]
      simp [mul_comm]
    _ ≤ 3 * ∑ k ∈ Finset.Icc 1 B,
          C * (P.card : ℝ) ^ 2 / (k : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro k hk
      exact htail k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
    _ = 3 * C * (P.card : ℝ) ^ 2 * (harmonic B : ℝ) := by
      rw [← hsumInv]
      simp_rw [div_eq_mul_inv]
      rw [← Finset.mul_sum]
      ring
    _ ≤ 3 * C * (P.card : ℝ) ^ 2 * (1 + Real.log B) := by
      gcongr
      exact harmonic_le_one_add_log B
    _ = 3 * C * ((expandedPlaneGrid N).card : ℝ) ^ 2 *
          (1 + Real.log (4 * N + 1 : ℕ)) := by simp [P, B]

noncomputable abbrev IsoscelesTriple (N : ℕ) :=
  {x : Fin 3 → GridPoint N //
    Function.Injective x ∧
      intSqDist (x 0).1 (x 1).1 = intSqDist (x 0).1 (x 2).1}

def isoscelesCode (x : Fin 3 → ℤ × ℤ) : Fin 3 → ℤ × ℤ :=
  ![axisFirst (x 1) (x 2), axisSecond (x 1) (x 2), 2 • x 0]

lemma isoscelesCode_injective : Function.Injective isoscelesCode := by
  intro x y hxy
  have h0 := congrFun hxy (0 : Fin 3)
  have h1 := congrFun hxy (1 : Fin 3)
  have h2 := congrFun hxy (2 : Fin 3)
  have h12 : (x 1, x 2) = (y 1, y 2) :=
    axisEncoding_injective (Prod.ext h0 h1)
  have hx0 : x 0 = y 0 := by
    have h20 := congrArg Prod.fst h2
    have h21 := congrArg Prod.snd h2
    apply Prod.ext <;> simp [isoscelesCode] at h20 h21 ⊢ <;> omega
  funext i
  fin_cases i
  · exact hx0
  · exact congrArg Prod.fst h12
  · exact congrArg Prod.snd h12

noncomputable def isoscelesToCollinear (N : ℕ) :
    IsoscelesTriple N → CollinearThree (expandedPlaneGrid N) := fun x => by
  let a : ℤ × ℤ := (x.1 0).1
  let b : ℤ × ℤ := (x.1 1).1
  let c : ℤ × ℤ := (x.1 2).1
  have hbc : b ≠ c := by
    intro h
    have hx : x.1 1 = x.1 2 := Subtype.ext h
    exact (show (1 : Fin 3) ≠ 2 by decide) (x.2.1 hx)
  have ha : a ∈ intGrid N := (x.1 0).2
  have hb : b ∈ intGrid N := (x.1 1).2
  have hc : c ∈ intGrid N := (x.1 2).2
  have hcode (i : Fin 3) : isoscelesCode (fun j => (x.1 j).1) i ∈
      expandedIntGrid N := by
    fin_cases i
    · exact axisFirst_mem_expanded hb hc
    · exact axisSecond_mem_expanded hb hc
    · exact two_smul_mem_expanded ha
  let y : Fin 3 → PointOf (expandedPlaneGrid N) := fun i =>
    ⟨intPoint (isoscelesCode (fun j => (x.1 j).1) i),
      Finset.mem_image.mpr ⟨_, hcode i, rfl⟩⟩
  refine ⟨y, ?_⟩
  have hy01 : (y 0 : Plane) ≠ (y 1 : Plane) := by
    apply intPoint_injective.ne
    simpa [y, isoscelesCode, b, c] using axisFirst_ne_axisSecond hbc
  refine ⟨hy01, ?_⟩
  intro i
  fin_cases i
  · exact mem_lineThrough_left _ _ hy01
  · exact mem_lineThrough_right _ _ hy01
  · change intPoint (2 • a) ∈
      affineSpan ℝ ({intPoint (axisFirst b c), intPoint (axisSecond b c)} : Set Plane)
    exact equidistant_mem_encodedAxis hbc (by
      simpa only [intSqDist_comm b a, intSqDist_comm c a] using x.2.2)

lemma isoscelesToCollinear_injective (N : ℕ) :
    Function.Injective (isoscelesToCollinear N) := by
  intro x y hxy
  have hcode : isoscelesCode (fun i => (x.1 i).1) =
      isoscelesCode (fun i => (y.1 i).1) := by
    funext i
    apply intPoint_injective
    exact congrArg (fun z : CollinearThree (expandedPlaneGrid N) =>
      ((z.1 i).1 : Plane)) hxy
  have hpoints := isoscelesCode_injective hcode
  apply Subtype.ext
  funext i
  apply Subtype.ext
  exact congrFun hpoints i

lemma card_IsoscelesTriple_le_collinear (N : ℕ) :
    Nat.card (IsoscelesTriple N) ≤
      Nat.card (CollinearThree (expandedPlaneGrid N)) :=
  Nat.card_le_card_of_injective (isoscelesToCollinear N)
    (isoscelesToCollinear_injective N)

lemma richLinesBound_in_lineRichness_form :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Finset Plane) (k : ℕ),
        2 ≤ k → (k : ℝ) ≤ Real.sqrt (P.card : ℝ) →
          ∃ L : Finset AffineRealLine,
            (∀ ell, ell ∈ L ↔ k ≤ lineRichness P ell) ∧
            (L.card : ℝ) ≤ C * (P.card : ℝ) ^ 2 / (k : ℝ) ^ 3 := by
  obtain ⟨C, hC, hRich⟩ := RichLinesBound
  refine ⟨C, hC, ?_⟩
  intro P k hk hs
  obtain ⟨L, hmem, hcard⟩ := hRich P k hk hs
  refine ⟨L, ?_, hcard⟩
  intro ell
  simpa [lineRichness] using hmem ell

lemma exists_collinearFour_grid_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (Nat.card (CollinearFour (expandedPlaneGrid N)) : ℝ) ≤
        C * (N : ℝ) ^ 5 := by
  obtain ⟨C₀, hC₀, hRich⟩ := richLinesBound_in_lineRichness_form
  refine ⟨12500 * C₀, by positivity, ?_⟩
  intro N hN
  have hcardNat := card_CollinearFour_le_sum (expandedPlaneGrid N)
  have hcardReal :
      (Nat.card (CollinearFour (expandedPlaneGrid N)) : ℝ) ≤
        ∑ ell ∈ gridLines (expandedPlaneGrid N),
          (lineRichness (expandedPlaneGrid N) ell : ℝ) ^ 4 := by
    exact_mod_cast hcardNat
  have hmoment := line_fourth_moment_bound C₀ hC₀ hRich hN
    (gridLines (expandedPlaneGrid N))
    (fun ell hell => two_le_lineRichness_of_mem_gridLines hell)
  have hB : ((4 * N + 1 : ℕ) : ℝ) ≤ 5 * (N : ℝ) := by
    norm_cast
    omega
  calc
    (Nat.card (CollinearFour (expandedPlaneGrid N)) : ℝ) ≤
        ∑ ell ∈ gridLines (expandedPlaneGrid N),
          (lineRichness (expandedPlaneGrid N) ell : ℝ) ^ 4 := hcardReal
    _ ≤ 4 * (4 * N + 1) * C₀ *
          ((expandedPlaneGrid N).card : ℝ) ^ 2 := hmoment
    _ = 4 * ((4 * N + 1 : ℕ) : ℝ) * C₀ *
          (((4 * N + 1 : ℕ) : ℝ) ^ 2) ^ 2 := by
      simp only [card_expandedPlaneGrid, Nat.cast_pow]
      push_cast
      rfl
    _ ≤ 4 * (5 * (N : ℝ)) * C₀ *
          ((5 * (N : ℝ)) ^ 2) ^ 2 := by gcongr
    _ = (12500 * C₀) * (N : ℝ) ^ 5 := by ring

lemma exists_isoscelesTriple_grid_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (Nat.card (IsoscelesTriple N) : ℝ) ≤
        C * (N : ℝ) ^ 4 * (1 + Real.log (4 * N + 1 : ℕ)) := by
  obtain ⟨C₀, hC₀, hRich⟩ := richLinesBound_in_lineRichness_form
  refine ⟨1875 * C₀, by positivity, ?_⟩
  intro N hN
  have hcardNat := card_CollinearThree_le_sum (expandedPlaneGrid N)
  have hcardReal :
      (Nat.card (CollinearThree (expandedPlaneGrid N)) : ℝ) ≤
        ∑ ell ∈ gridLines (expandedPlaneGrid N),
          (lineRichness (expandedPlaneGrid N) ell : ℝ) ^ 3 := by
    exact_mod_cast hcardNat
  have hmoment := line_third_moment_bound C₀ hC₀ hRich hN
    (gridLines (expandedPlaneGrid N))
    (fun ell hell => two_le_lineRichness_of_mem_gridLines hell)
  have hisos :
      (Nat.card (IsoscelesTriple N) : ℝ) ≤
        3 * C₀ * ((expandedPlaneGrid N).card : ℝ) ^ 2 *
          (1 + Real.log (4 * N + 1 : ℕ)) := by
    exact le_trans (by exact_mod_cast card_IsoscelesTriple_le_collinear N)
      (hcardReal.trans hmoment)
  have hB : ((4 * N + 1 : ℕ) : ℝ) ≤ 5 * (N : ℝ) := by
    norm_cast
    omega
  have hlogNonneg : 0 ≤ 1 + Real.log (4 * N + 1 : ℕ) := by
    have : (1 : ℝ) ≤ (4 * N + 1 : ℕ) := by norm_cast; omega
    positivity
  have hpow :
      (((4 * N + 1 : ℕ) : ℝ) ^ 2) ^ 2 ≤
        ((5 * (N : ℝ)) ^ 2) ^ 2 := by
    calc
      (((4 * N + 1 : ℕ) : ℝ) ^ 2) ^ 2 =
          (((4 * N + 1 : ℕ) : ℝ)) ^ 4 := by ring
      _ ≤ (5 * (N : ℝ)) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hB 4
      _ = ((5 * (N : ℝ)) ^ 2) ^ 2 := by ring
  calc
    (Nat.card (IsoscelesTriple N) : ℝ) ≤
        3 * C₀ * ((expandedPlaneGrid N).card : ℝ) ^ 2 *
          (1 + Real.log (4 * N + 1 : ℕ)) := hisos
    _ = 3 * C₀ * (((4 * N + 1 : ℕ) : ℝ) ^ 2) ^ 2 *
          (1 + Real.log (4 * N + 1 : ℕ)) := by
      simp only [card_expandedPlaneGrid, Nat.cast_pow]
    _ ≤ 3 * C₀ * ((5 * (N : ℝ)) ^ 2) ^ 2 *
          (1 + Real.log (4 * N + 1 : ℕ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (by positivity)) hlogNonneg
    _ = (1875 * C₀) * (N : ℝ) ^ 4 *
          (1 + Real.log (4 * N + 1 : ℕ)) := by ring

/-! ## Fixed-radius circles from the unit-distance theorem -/

noncomputable abbrev SphereNeighbor (N : ℕ) (a b : GridPoint N) :=
  {c : GridPoint N // c ≠ a ∧
    intSqDist a.1 c.1 = intSqDist a.1 b.1}

noncomputable abbrev RadiusCopy (N : ℕ) (a b : GridPoint N) :=
  GridPoint N × SphereNeighbor N a b

noncomputable abbrev OrderedUnitPair (P : Finset Plane) :=
  {q : Plane × Plane // q ∈ P.offDiag ∧ dist q.1 q.2 = 1}

lemma intGrid_subset_expandedIntGrid (N : ℕ) :
    intGrid N ⊆ expandedIntGrid N := by
  intro z hz
  rw [mem_intGrid] at hz
  rw [mem_expandedIntGrid]
  omega

lemma translate_difference_mem_expanded {N : ℕ} {t a c : ℤ × ℤ}
    (ht : t ∈ intGrid N) (ha : a ∈ intGrid N) (hc : c ∈ intGrid N) :
    t + (c - a) ∈ expandedIntGrid N := by
  rw [mem_intGrid] at ht ha hc
  rw [mem_expandedIntGrid]
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  omega

lemma intSqDist_translate_difference (t a c : ℤ × ℤ) :
    intSqDist t (t + (c - a)) = intSqDist a c := by
  simp only [intSqDist, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  ring

noncomputable def scaledExpandedPlaneGrid (N : ℕ) (a b : GridPoint N) :
    Finset Plane :=
  (expandedPlaneGrid N).image fun z =>
    (dist (intPoint a.1) (intPoint b.1))⁻¹ • z

noncomputable def radiusCopyToUnitPair (N : ℕ) (a b : GridPoint N)
    (hab : a ≠ b) :
    RadiusCopy N a b → OrderedUnitPair (scaledExpandedPlaneGrid N a b) := fun x => by
  let δ : ℝ := dist (intPoint a.1) (intPoint b.1)
  let t : ℤ × ℤ := x.1.1
  let c : ℤ × ℤ := x.2.1.1
  let u : ℤ × ℤ := t + (c - a.1)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact dist_pos.mpr (intPoint_injective.ne (by
      intro h
      exact hab (Subtype.ext h)))
  have htE : t ∈ expandedIntGrid N :=
    intGrid_subset_expandedIntGrid N x.1.2
  have huE : u ∈ expandedIntGrid N :=
    translate_difference_mem_expanded x.1.2 a.2 x.2.1.2
  have htP : intPoint t ∈ expandedPlaneGrid N := by
    exact Finset.mem_image.mpr ⟨t, htE, rfl⟩
  have huP : intPoint u ∈ expandedPlaneGrid N := by
    exact Finset.mem_image.mpr ⟨u, huE, rfl⟩
  have hfirst : δ⁻¹ • intPoint t ∈ scaledExpandedPlaneGrid N a b := by
    exact Finset.mem_image.mpr ⟨intPoint t, htP, rfl⟩
  have hsecond : δ⁻¹ • intPoint u ∈ scaledExpandedPlaneGrid N a b := by
    exact Finset.mem_image.mpr ⟨intPoint u, huP, rfl⟩
  have htu : t ≠ u := by
    intro h
    have hz : (0 : ℤ × ℤ) = c - a.1 := by
      apply add_left_cancel (a := t)
      simpa [u] using h
    have hca : c = a.1 := sub_eq_zero.mp hz.symm
    exact x.2.2.1 (Subtype.ext hca)
  have hscaled_ne : δ⁻¹ • intPoint t ≠ δ⁻¹ • intPoint u := by
    intro h
    have htuPoint : intPoint t = intPoint u :=
      smul_right_injective Plane (inv_ne_zero hδ.ne') h
    exact htu (intPoint_injective htuPoint)
  have hdistUnscaled : dist (intPoint t) (intPoint u) = δ := by
    dsimp [δ]
    apply dist_intPoint_eq_iff.mpr
    rw [intSqDist_translate_difference]
    exact x.2.2.2
  refine ⟨(δ⁻¹ • intPoint t, δ⁻¹ • intPoint u), ?_, ?_⟩
  · exact Finset.mem_offDiag.mpr ⟨hfirst, hsecond, hscaled_ne⟩
  · rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hδ),
      hdistUnscaled, inv_mul_cancel₀ hδ.ne']

lemma radiusCopyToUnitPair_injective (N : ℕ) (a b : GridPoint N)
    (hab : a ≠ b) : Function.Injective (radiusCopyToUnitPair N a b hab) := by
  intro x y hxy
  have hpair := congrArg (fun z : OrderedUnitPair (scaledExpandedPlaneGrid N a b) => z.1) hxy
  have hδ : dist (intPoint a.1) (intPoint b.1) ≠ 0 :=
    (dist_ne_zero.mpr (intPoint_injective.ne (by
      intro h
      exact hab (Subtype.ext h))))
  have hfirst := congrArg Prod.fst hpair
  have hsecond := congrArg Prod.snd hpair
  have htPoint : intPoint x.1.1 = intPoint y.1.1 :=
    smul_right_injective Plane (inv_ne_zero hδ) hfirst
  have ht : x.1.1 = y.1.1 := intPoint_injective htPoint
  have huPoint :
      intPoint (x.1.1 + (x.2.1.1 - a.1)) =
        intPoint (y.1.1 + (y.2.1.1 - a.1)) :=
    smul_right_injective Plane (inv_ne_zero hδ) hsecond
  have hu := intPoint_injective huPoint
  have hc : x.2.1.1 = y.2.1.1 := by
    rw [ht] at hu
    have hd : x.2.1.1 - a.1 = y.2.1.1 - a.1 := add_left_cancel hu
    calc
      x.2.1.1 = (x.2.1.1 - a.1) + a.1 := by abel
      _ = (y.2.1.1 - a.1) + a.1 := congrArg (fun z => z + a.1) hd
      _ = y.2.1.1 := by abel
  apply Prod.ext
  · exact Subtype.ext ht
  · exact Subtype.ext (Subtype.ext hc)

lemma card_GridPoint (N : ℕ) : Nat.card (GridPoint N) = N ^ 2 := by
  rw [Nat.subtype_card (intGrid N) (fun z => Iff.rfl), card_intGrid]

lemma card_OrderedUnitPair (P : Finset Plane) :
    Nat.card (OrderedUnitPair P) =
      (P.offDiag.filter fun q => dist q.1 q.2 = 1).card := by
  exact Nat.subtype_card _ (fun q => by simp)

lemma radiusCopy_card_le_orderedUnitPair (N : ℕ) (a b : GridPoint N)
    (hab : a ≠ b) :
    N ^ 2 * Nat.card (SphereNeighbor N a b) ≤
      ((scaledExpandedPlaneGrid N a b).offDiag.filter fun q =>
        dist q.1 q.2 = 1).card := by
  let : Fintype {q : Plane × Plane //
      q ∈ (scaledExpandedPlaneGrid N a b).offDiag} :=
    Fintype.ofFinset (scaledExpandedPlaneGrid N a b).offDiag
      (fun _ => Iff.rfl)
  let : Finite (OrderedUnitPair (scaledExpandedPlaneGrid N a b)) :=
    Finite.of_injective
      (fun q : OrderedUnitPair (scaledExpandedPlaneGrid N a b) =>
        (⟨q.1, q.2.1⟩ : {q : Plane × Plane //
          q ∈ (scaledExpandedPlaneGrid N a b).offDiag}))
      (by
        intro x y h
        apply Subtype.ext
        exact congrArg (fun z : {q : Plane × Plane //
          q ∈ (scaledExpandedPlaneGrid N a b).offDiag} => z.1) h)
  calc
    N ^ 2 * Nat.card (SphereNeighbor N a b) =
        Nat.card (RadiusCopy N a b) := by
      rw [Nat.card_prod, card_GridPoint]
    _ ≤ Nat.card (OrderedUnitPair (scaledExpandedPlaneGrid N a b)) :=
      Nat.card_le_card_of_injective (radiusCopyToUnitPair N a b hab)
        (radiusCopyToUnitPair_injective N a b hab)
    _ = ((scaledExpandedPlaneGrid N a b).offDiag.filter fun q =>
        dist q.1 q.2 = 1).card := card_OrderedUnitPair _

lemma card_scaledExpandedPlaneGrid (N : ℕ) (a b : GridPoint N)
    (hab : a ≠ b) :
    (scaledExpandedPlaneGrid N a b).card = (4 * N + 1) ^ 2 := by
  unfold scaledExpandedPlaneGrid
  rw [Finset.card_image_of_injective, card_expandedPlaneGrid]
  exact smul_right_injective Plane (inv_ne_zero (dist_ne_zero.mpr
    (intPoint_injective.ne (by
      intro h
      exact hab (Subtype.ext h)))))

lemma exists_radius_neighbor_mass_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N →
      ∀ (a b : GridPoint N), a ≠ b →
        ((N ^ 2 * Nat.card (SphereNeighbor N a b) : ℕ) : ℝ) ≤
          C * (N : ℝ) ^ ((8 : ℝ) / 3) := by
  obtain ⟨C₀, hC₀, hunit⟩ := IncidenceGeometry.unit_distance_upper_bound
  let C : ℝ := 2 * C₀ * (5 : ℝ) ^ ((8 : ℝ) / 3) + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro N hN a b hab
  let P := scaledExpandedPlaneGrid N a b
  let m := (P.offDiag.filter fun q => dist q.1 q.2 = 1).card
  have hcopyNat : N ^ 2 * Nat.card (SphereNeighbor N a b) ≤ m := by
    exact radiusCopy_card_le_orderedUnitPair N a b hab
  have hcopy :
      ((N ^ 2 * Nat.card (SphereNeighbor N a b) : ℕ) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hcopyNat
  have hmNat : m ≤ 2 * (m / 2) + 1 := by omega
  have hm : (m : ℝ) ≤ 2 * ((m / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast hmNat
  have hunitP : ((m / 2 : ℕ) : ℝ) ≤
      C₀ * (P.card : ℝ) ^ ((4 : ℝ) / 3) := by
    simpa [P, m, IncidenceGeometry.unitDistanceCount] using hunit P
  have hPcard : P.card = (4 * N + 1) ^ 2 := by
    exact card_scaledExpandedPlaneGrid N a b hab
  have hB : ((4 * N + 1 : ℕ) : ℝ) ≤ 5 * (N : ℝ) := by
    norm_cast
    omega
  have hPpow :
      (P.card : ℝ) ^ ((4 : ℝ) / 3) ≤
        (5 : ℝ) ^ ((8 : ℝ) / 3) *
          (N : ℝ) ^ ((8 : ℝ) / 3) := by
    calc
      (P.card : ℝ) ^ ((4 : ℝ) / 3) =
          ((((4 * N + 1 : ℕ) : ℝ) ^ 2) : ℝ) ^ ((4 : ℝ) / 3) := by
        rw [hPcard]
        norm_cast
      _ = ((4 * N + 1 : ℕ) : ℝ) ^ ((8 : ℝ) / 3) := by
        rw [← Real.rpow_natCast_mul (by positivity) 2]
        congr 1
        norm_num
      _ ≤ (5 * (N : ℝ)) ^ ((8 : ℝ) / 3) :=
        Real.rpow_le_rpow (by positivity) hB (by norm_num)
      _ = (5 : ℝ) ^ ((8 : ℝ) / 3) *
          (N : ℝ) ^ ((8 : ℝ) / 3) := by
        rw [Real.mul_rpow (by norm_num) (by positivity)]
  have hNpow : 1 ≤ (N : ℝ) ^ ((8 : ℝ) / 3) :=
    Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  calc
    ((N ^ 2 * Nat.card (SphereNeighbor N a b) : ℕ) : ℝ) ≤ (m : ℝ) := hcopy
    _ ≤ 2 * ((m / 2 : ℕ) : ℝ) + 1 := hm
    _ ≤ 2 * (C₀ * (P.card : ℝ) ^ ((4 : ℝ) / 3)) + 1 := by
      gcongr
    _ ≤ 2 * (C₀ * ((5 : ℝ) ^ ((8 : ℝ) / 3) *
          (N : ℝ) ^ ((8 : ℝ) / 3))) +
          (N : ℝ) ^ ((8 : ℝ) / 3) := by
      gcongr
    _ = C * (N : ℝ) ^ ((8 : ℝ) / 3) := by
      dsimp [C]
      ring

lemma exists_radius_neighbor_cube_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N →
      ∀ (a b : GridPoint N), a ≠ b →
        (Nat.card (SphereNeighbor N a b) : ℝ) ^ 3 ≤
          C * (N : ℝ) ^ 2 := by
  obtain ⟨A, hA, hmass⟩ := exists_radius_neighbor_mass_bound
  refine ⟨A ^ 3, by positivity, ?_⟩
  intro N hN a b hab
  let d : ℝ := Nat.card (SphereNeighbor N a b)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmass' : (N : ℝ) ^ 2 * d ≤
      A * (N : ℝ) ^ ((8 : ℝ) / 3) := by
    simpa [d, Nat.cast_mul, Nat.cast_pow] using hmass N hN a b hab
  have hquot :
      (N : ℝ) ^ ((8 : ℝ) / 3) / (N : ℝ) ^ 2 =
        (N : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_sub_natCast hNpos.ne' ((8 : ℝ) / 3) 2]
    congr 1
    norm_num
  have hd : d ≤ A * (N : ℝ) ^ ((2 : ℝ) / 3) := by
    have hddiv : d ≤
        (A * (N : ℝ) ^ ((8 : ℝ) / 3)) / (N : ℝ) ^ 2 :=
      (le_div_iff₀ (sq_pos_of_pos hNpos)).2 (by
        simpa [mul_comm] using hmass')
    rw [mul_div_assoc, hquot] at hddiv
    exact hddiv
  have hd0 : 0 ≤ d := by positivity
  have hcube := pow_le_pow_left₀ hd0 hd 3
  calc
    (Nat.card (SphereNeighbor N a b) : ℝ) ^ 3 = d ^ 3 := rfl
    _ ≤ (A * (N : ℝ) ^ ((2 : ℝ) / 3)) ^ 3 := hcube
    _ = A ^ 3 * (N : ℝ) ^ 2 := by
      rw [mul_pow, ← Real.rpow_mul_natCast (by positivity) ((2 : ℝ) / 3) 3]
      norm_num

/-! ## The nine isosceles-extension patterns -/

noncomputable instance gridPointFintype (N : ℕ) : Fintype (GridPoint N) :=
  Fintype.ofFinset (intGrid N) (fun _ => Iff.rfl)

def fin3ToFin4 (i : Fin 3) : Fin 4 := ⟨i.1, by omega⟩

def triangleEdgeStart : Fin 3 → Fin 3 := ![0, 0, 1]

def triangleEdgeEnd : Fin 3 → Fin 3 := ![1, 2, 2]

lemma triangleEdgeStart_ne_end (e : Fin 3) :
    triangleEdgeStart e ≠ triangleEdgeEnd e := by
  fin_cases e <;> decide

noncomputable abbrev ExtensionFiber (N : ℕ) (t : IsoscelesTriple N)
    (i e : Fin 3) :=
  {z : GridPoint N // z ≠ t.1 i ∧
    intSqDist (t.1 i).1 z.1 =
      intSqDist (t.1 (triangleEdgeStart e)).1
        (t.1 (triangleEdgeEnd e)).1}

noncomputable abbrev ExtensionFour (N : ℕ) (i e : Fin 3) :=
  {x : InjectiveGridFour N //
    intSqDist (x.1 0).1 (x.1 1).1 = intSqDist (x.1 0).1 (x.1 2).1 ∧
    intSqDist (x.1 (fin3ToFin4 i)).1 (x.1 3).1 =
      intSqDist (x.1 (fin3ToFin4 (triangleEdgeStart e))).1
        (x.1 (fin3ToFin4 (triangleEdgeEnd e))).1}

noncomputable abbrev TaggedExtensionFour (N : ℕ) (i e : Fin 3) :=
  (t : IsoscelesTriple N) × ExtensionFiber N t i e

noncomputable def tagExtensionFour (N : ℕ) (i e : Fin 3) :
    ExtensionFour N i e → TaggedExtensionFour N i e := fun x => by
  let t : Fin 3 → GridPoint N := fun j => x.1.1 (fin3ToFin4 j)
  have htinj : Function.Injective t := by
    intro j k hjk
    have hindex : fin3ToFin4 j = fin3ToFin4 k := x.1.2 hjk
    exact Fin.ext (congrArg (fun q : Fin 4 => q.1) hindex)
  let T : IsoscelesTriple N := ⟨t, htinj, x.2.1⟩
  have hz : x.1.1 3 ≠ T.1 i := by
    intro h
    have hindex : (3 : Fin 4) = fin3ToFin4 i := x.1.2 h
    have := congrArg Fin.val hindex
    simp [fin3ToFin4] at this
    have hi := i.isLt
    omega
  exact ⟨T, ⟨x.1.1 3, hz, x.2.2⟩⟩

lemma tagExtensionFour_injective (N : ℕ) (i e : Fin 3) :
    Function.Injective (tagExtensionFour N i e) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  funext j
  fin_cases j
  · exact congrArg (fun z : TaggedExtensionFour N i e => z.1.1 0) hxy
  · exact congrArg (fun z : TaggedExtensionFour N i e => z.1.1 1) hxy
  · exact congrArg (fun z : TaggedExtensionFour N i e => z.1.1 2) hxy
  · exact congrArg (fun z : TaggedExtensionFour N i e => z.2.1) hxy

noncomputable def extensionFiberEquivSphere {N : ℕ} {t : IsoscelesTriple N}
    {i e : Fin 3} (z : ExtensionFiber N t i e) :
    ExtensionFiber N t i e ≃ SphereNeighbor N (t.1 i) z.1 where
  toFun y := ⟨y.1, y.2.1, y.2.2.trans z.2.2.symm⟩
  invFun y := ⟨y.1, y.2.1, y.2.2.trans z.2.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

lemma extensionFiber_cube_bound (C : ℝ)
    (hCnonneg : 0 ≤ C)
    (hC : ∀ (N : ℕ), 1 ≤ N → ∀ (a b : GridPoint N), a ≠ b →
      (Nat.card (SphereNeighbor N a b) : ℝ) ^ 3 ≤ C * (N : ℝ) ^ 2)
    (N : ℕ) (hN : 1 ≤ N) (t : IsoscelesTriple N) (i e : Fin 3) :
    (Nat.card (ExtensionFiber N t i e) : ℝ) ^ 3 ≤
      C * (N : ℝ) ^ 2 := by
  by_cases hzero : Nat.card (ExtensionFiber N t i e) = 0
  · have hzero' : Fintype.card (ExtensionFiber N t i e) = 0 := by
      simpa [Nat.card_eq_fintype_card] using hzero
    rw [Nat.card_eq_fintype_card, hzero']
    norm_num
    exact mul_nonneg hCnonneg (sq_nonneg _)
  · have hpos : 0 < Nat.card (ExtensionFiber N t i e) := Nat.pos_of_ne_zero hzero
    have hne : Nonempty (ExtensionFiber N t i e) := (Nat.card_pos_iff.mp hpos).1
    let z : ExtensionFiber N t i e := Classical.choice hne
    rw [Nat.card_congr (extensionFiberEquivSphere z)]
    exact hC N hN (t.1 i) z.1 z.2.1.symm

lemma extensionFour_card_le_tagged (N : ℕ) (i e : Fin 3) :
    Nat.card (ExtensionFour N i e) ≤ Nat.card (TaggedExtensionFour N i e) :=
  Nat.card_le_card_of_injective (tagExtensionFour N i e)
    (tagExtensionFour_injective N i e)

lemma exists_extensionFour_grid_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N →
      ∀ (i e : Fin 3),
        (Nat.card (ExtensionFour N i e) : ℝ) ≤ C * (N : ℝ) ^ 5 := by
  obtain ⟨A, hA, hcircle⟩ := exists_radius_neighbor_cube_bound
  obtain ⟨B, hB, hisos⟩ := exists_isoscelesTriple_grid_bound
  let C : ℝ := 4 * B * A ^ ((1 : ℝ) / 3) * 5 ^ ((1 : ℝ) / 3)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro N hN i e
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hfiber (t : IsoscelesTriple N) :
      (Nat.card (ExtensionFiber N t i e) : ℝ) ≤
        (A * (N : ℝ) ^ 2) ^ ((1 : ℝ) / 3) := by
    have hcub := extensionFiber_cube_bound A hA.le hcircle N hN t i e
    have hroot :
        (Nat.card (ExtensionFiber N t i e) : ℝ) ≤
          (A * (N : ℝ) ^ 2) ^ ((3 : ℝ)⁻¹) := by
      rw [Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity)
        (by norm_num : (0 : ℝ) < 3)]
      simpa [Real.rpow_natCast] using hcub
    simpa [one_div] using hroot
  have htag :
      (Nat.card (TaggedExtensionFour N i e) : ℝ) ≤
        (Nat.card (IsoscelesTriple N) : ℝ) *
          (A * (N : ℝ) ^ 2) ^ ((1 : ℝ) / 3) := by
    rw [Nat.card_sigma]
    push_cast
    calc
      ∑ t : IsoscelesTriple N, (Nat.card (ExtensionFiber N t i e) : ℝ) ≤
          ∑ _t : IsoscelesTriple N,
            (A * (N : ℝ) ^ 2) ^ ((1 : ℝ) / 3) := by
        exact Finset.sum_le_sum fun t _ => hfiber t
      _ = (Nat.card (IsoscelesTriple N) : ℝ) *
          (A * (N : ℝ) ^ 2) ^ ((1 : ℝ) / 3) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp [Nat.card_eq_fintype_card]
  have hfactor :
      (A * (N : ℝ) ^ 2) ^ ((1 : ℝ) / 3) =
        A ^ ((1 : ℝ) / 3) * (N : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [Real.mul_rpow hA.le (sq_nonneg _)]
    rw [← Real.rpow_natCast_mul (by positivity) 2]
    congr 2
    norm_num
  have hq : ((4 * N + 1 : ℕ) : ℝ) ≤ 5 * (N : ℝ) := by
    norm_cast
    omega
  have hqpow : ((4 * N + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤
      (5 * (N : ℝ)) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow (by positivity) hq (by norm_num)
  have hlogRaw := Real.log_natCast_le_rpow_div (4 * N + 1)
    (show (0 : ℝ) < (1 : ℝ) / 3 by norm_num)
  have hlog : 1 + Real.log (4 * N + 1 : ℕ) ≤
      4 * (5 * (N : ℝ)) ^ ((1 : ℝ) / 3) := by
    have hNone : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hone : 1 ≤ (5 * (N : ℝ)) ^ ((1 : ℝ) / 3) :=
      Real.one_le_rpow (by nlinarith [hNone]) (by norm_num)
    have hlog' : Real.log (4 * N + 1 : ℕ) ≤
        3 * ((4 * N + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) := by
      convert hlogRaw using 1; ring
    nlinarith
  have hsplit :
      (5 * (N : ℝ)) ^ ((1 : ℝ) / 3) =
        5 ^ ((1 : ℝ) / 3) * (N : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [Real.mul_rpow (by norm_num) hNpos.le]
  have hfrac :
      (N : ℝ) ^ ((2 : ℝ) / 3) * (N : ℝ) ^ ((1 : ℝ) / 3) = N := by
    rw [← Real.rpow_add hNpos]
    norm_num
  calc
    (Nat.card (ExtensionFour N i e) : ℝ) ≤
        (Nat.card (TaggedExtensionFour N i e) : ℝ) := by
      exact_mod_cast extensionFour_card_le_tagged N i e
    _ ≤ (Nat.card (IsoscelesTriple N) : ℝ) *
          (A * (N : ℝ) ^ 2) ^ ((1 : ℝ) / 3) := htag
    _ ≤ (B * (N : ℝ) ^ 4 * (1 + Real.log (4 * N + 1 : ℕ))) *
          (A * (N : ℝ) ^ 2) ^ ((1 : ℝ) / 3) := by
      gcongr
      exact hisos N hN
    _ ≤ (B * (N : ℝ) ^ 4 *
          (4 * (5 * (N : ℝ)) ^ ((1 : ℝ) / 3))) *
          (A * (N : ℝ) ^ 2) ^ ((1 : ℝ) / 3) := by
      gcongr
    _ = C * (N : ℝ) ^ 5 := by
      rw [hfactor, hsplit]
      calc
        (B * (N : ℝ) ^ 4 *
              (4 * (5 ^ ((1 : ℝ) / 3) * (N : ℝ) ^ ((1 : ℝ) / 3))) *
            (A ^ ((1 : ℝ) / 3) * (N : ℝ) ^ ((2 : ℝ) / 3))) =
            (4 * B * A ^ ((1 : ℝ) / 3) * 5 ^ ((1 : ℝ) / 3)) *
              (N : ℝ) ^ 4 *
                ((N : ℝ) ^ ((2 : ℝ) / 3) *
                  (N : ℝ) ^ ((1 : ℝ) / 3)) := by ring
        _ = (4 * B * A ^ ((1 : ℝ) / 3) * 5 ^ ((1 : ℝ) / 3)) *
              (N : ℝ) ^ 4 * (N : ℝ) := by rw [hfrac]
        _ = C * (N : ℝ) ^ 5 := by
          dsimp [C]
          ring

noncomputable abbrev ExtensionFourAny (N : ℕ) :=
  {x : InjectiveGridFour N //
    intSqDist (x.1 0).1 (x.1 1).1 = intSqDist (x.1 0).1 (x.1 2).1 ∧
    ∃ i e : Fin 3,
      intSqDist (x.1 (fin3ToFin4 i)).1 (x.1 3).1 =
        intSqDist (x.1 (fin3ToFin4 (triangleEdgeStart e))).1
          (x.1 (fin3ToFin4 (triangleEdgeEnd e))).1}

noncomputable abbrev TaggedExtensionFourAny (N : ℕ) :=
  (i : Fin 3) × (e : Fin 3) × ExtensionFour N i e

noncomputable def tagExtensionFourAny (N : ℕ) :
    ExtensionFourAny N → TaggedExtensionFourAny N := fun x => by
  let i : Fin 3 := Classical.choose x.2.2
  let e : Fin 3 := Classical.choose (Classical.choose_spec x.2.2)
  have heq := Classical.choose_spec (Classical.choose_spec x.2.2)
  exact ⟨i, e, ⟨x.1, x.2.1, heq⟩⟩

lemma tagExtensionFourAny_injective (N : ℕ) :
    Function.Injective (tagExtensionFourAny N) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun z : TaggedExtensionFourAny N => z.2.2.1) hxy

lemma exists_extensionFourAny_grid_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N →
      (Nat.card (ExtensionFourAny N) : ℝ) ≤ C * (N : ℝ) ^ 5 := by
  obtain ⟨C₀, hC₀, hext⟩ := exists_extensionFour_grid_bound
  refine ⟨9 * C₀, by positivity, ?_⟩
  intro N hN
  have htagNat : Nat.card (ExtensionFourAny N) ≤
      Nat.card (TaggedExtensionFourAny N) :=
    Nat.card_le_card_of_injective (tagExtensionFourAny N)
      (tagExtensionFourAny_injective N)
  have htag : (Nat.card (TaggedExtensionFourAny N) : ℝ) ≤
      9 * (C₀ * (N : ℝ) ^ 5) := by
    rw [Nat.card_sigma]
    push_cast
    calc
      ∑ i : Fin 3, (Nat.card ((e : Fin 3) × ExtensionFour N i e) : ℝ) =
          ∑ i : Fin 3, ∑ e : Fin 3,
            (Nat.card (ExtensionFour N i e) : ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Nat.card_sigma]
        push_cast
        rfl
      _ ≤ ∑ _i : Fin 3, ∑ _e : Fin 3,
            C₀ * (N : ℝ) ^ 5 := by
        exact Finset.sum_le_sum fun i _ =>
          Finset.sum_le_sum fun e _ => hext N hN i e
      _ = 9 * (C₀ * (N : ℝ) ^ 5) := by
        norm_num
        ring
  calc
    (Nat.card (ExtensionFourAny N) : ℝ) ≤
        (Nat.card (TaggedExtensionFourAny N) : ℝ) := by exact_mod_cast htagNat
    _ ≤ 9 * (C₀ * (N : ℝ) ^ 5) := htag
    _ = (9 * C₀) * (N : ℝ) ^ 5 := by ring

/-! ## From bad four-sets to the classified patterns -/

noncomputable def finFourEquivOfCard {Q : Finset (ℤ × ℤ)}
    (hQ : Q.card = 4) : Fin 4 ≃ Q :=
  (finCongr (by simpa [Fintype.card_coe] using hQ.symm)).trans
    (Fintype.equivFin Q).symm

noncomputable def enumerateOtherBad (N : ℕ)
    (Q : {Q : Finset (ℤ × ℤ) // Q ∈ otherBadIntQuads (intGrid N)}) :
    InjectiveGridFour N := by
  have hmem := mem_otherBadIntQuads.mp Q.2
  let e : Fin 4 ≃ Q.1 := finFourEquivOfCard hmem.2.1
  refine ⟨fun i => ⟨(e i).1, hmem.1 (e i).2⟩, ?_⟩
  intro i j hij
  apply e.injective
  apply Subtype.ext
  exact congrArg (fun z : GridPoint N => z.1) hij

lemma enumerateOtherBad_range (N : ℕ)
    (Q : {Q : Finset (ℤ × ℤ) // Q ∈ otherBadIntQuads (intGrid N)}) :
    Finset.univ.image (fun i => ((enumerateOtherBad N Q).1 i).1) = Q.1 := by
  classical
  have hmem := mem_otherBadIntQuads.mp Q.2
  let e : Fin 4 ≃ Q.1 := finFourEquivOfCard hmem.2.1
  change Finset.univ.image (fun i => (e i).1) = Q.1
  ext z
  constructor
  · rintro hz
    rcases Finset.mem_image.mp hz with ⟨i, _hi, rfl⟩
    exact (e i).2
  · intro hz
    apply Finset.mem_image.mpr
    refine ⟨e.symm ⟨z, hz⟩, Finset.mem_univ _, ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply ⟨z, hz⟩)

lemma orderedQuadSet_enumerateOtherBad (N : ℕ)
    (Q : {Q : Finset (ℤ × ℤ) // Q ∈ otherBadIntQuads (intGrid N)}) :
    orderedQuadSet (fun i => ((enumerateOtherBad N Q).1 i).1) =
      Q.1.image intPoint := by
  unfold orderedQuadSet
  rw [enumerateOtherBad_range N Q]

noncomputable abbrev PatternTarget (N : ℕ) :=
  KiteFour N ⊕ OppositeFour N ⊕ ExtensionFourAny N

def patternPoints {N : ℕ} : PatternTarget N → Fin 4 → GridPoint N
  | Sum.inl x => x.1.1
  | Sum.inr (Sum.inl x) => x.1.1
  | Sum.inr (Sum.inr x) => x.1.1

noncomputable def patternSet {N : ℕ} (p : PatternTarget N) :
    Finset (ℤ × ℤ) :=
  Finset.univ.image fun i => (patternPoints p i).1

lemma four_list_nodup_of_injective {X : Type*} (f : Fin 4 → X)
    (hf : Function.Injective f) : [f 0, f 1, f 2, f 3].Nodup := by
  apply List.nodup_cons.mpr
  constructor
  · simp only [List.mem_cons, List.not_mem_nil, not_or,
      not_false_eq_true, and_true]
    exact ⟨hf.ne (by decide), hf.ne (by decide), hf.ne (by decide)⟩
  apply List.nodup_cons.mpr
  constructor
  · simp only [List.mem_cons, List.not_mem_nil, not_or,
      not_false_eq_true, and_true]
    exact ⟨hf.ne (by decide), hf.ne (by decide)⟩
  apply List.nodup_cons.mpr
  constructor
  · simpa using hf.ne (by decide : (2 : Fin 4) ≠ 3)
  · simp

lemma exists_patternTarget_of_otherBad (N : ℕ)
    (Q : {Q : Finset (ℤ × ℤ) // Q ∈ otherBadIntQuads (intGrid N)}) :
    ∃ p : PatternTarget N, patternSet p = Q.1 := by
  classical
  let x : InjectiveGridFour N := enumerateOtherBad N Q
  let xv : Fin 4 → ℤ × ℤ := fun j => (x.1 j).1
  have hxv : Function.Injective xv := by
    intro j k h
    exact x.2 (Subtype.ext h)
  have hmem := mem_otherBadIntQuads.mp Q.2
  have hquad : orderedQuadSet xv = Q.1.image intPoint := by
    exact orderedQuadSet_enumerateOtherBad N Q
  have hdist : distanceCount (orderedQuadSet xv) ≤ 4 := by
    rw [hquad]
    exact hmem.2.2.1
  obtain ⟨σ, hσ, hcases⟩ := ordered_distance_pattern_of_card_le_four hxv hdist
  let yfun : Fin 4 → GridPoint N := fun j => x.1 (σ j)
  have hyinj : Function.Injective yfun := x.2.comp hσ
  let y : InjectiveGridFour N := ⟨yfun, hyinj⟩
  let yv : Fin 4 → ℤ × ℤ := fun j => (y.1 j).1
  have hyv : Function.Injective yv := by
    intro j k h
    exact y.2 (Subtype.ext h)
  have hσsurj : Function.Surjective σ := Finite.injective_iff_surjective.mp hσ
  have hyRange : Finset.univ.image yv = Q.1 := by
    rw [← enumerateOtherBad_range N Q]
    ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨σ j, rfl⟩
    · rintro ⟨k, rfl⟩
      obtain ⟨j, rfl⟩ := hσsurj k
      exact ⟨j, rfl⟩
  have hymem (j : Fin 4) : yv j ∈ Q.1 := by
    rw [← hyRange]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hset (p : PatternTarget N) (hp : patternPoints p = y.1) :
      patternSet p = Q.1 := by
    unfold patternSet
    rw [hp]
    exact hyRange
  dsimp only at hcases
  rcases hcases with hequil | hopp | hkite | hext
  · exact (no_equilateral_integer_triangle
      (hyv.ne (by decide : (0 : Fin 4) ≠ 1)) hequil.1
      (hequil.1.trans hequil.2)).elim
  · by_cases hsum : yv 0 + yv 1 = yv 2 + yv 3
    · exfalso
      apply hmem.2.2.2
      let τ : Fin 4 → Fin 4 := ![0, 2, 3, 1]
      have hτ : Function.Injective τ := by decide
      have hnodup : [yv 0, yv 2, yv 3, yv 1].Nodup := by
        have h := four_list_nodup_of_injective (fun j => yv (τ j)) (hyv.comp hτ)
        simpa [τ] using h
      exact ⟨yv 0, hymem 0, yv 2, hymem 2, yv 3, hymem 3,
        yv 1, hymem 1, hnodup, hsum⟩
    · let p : PatternTarget N := Sum.inr (Sum.inl ⟨y, hopp.1, hopp.2, hsum⟩)
      refine ⟨p, hset p ?_⟩
      rfl
  · let p : PatternTarget N := Sum.inl ⟨y, hkite⟩
    refine ⟨p, hset p ?_⟩
    rfl
  · rcases hext with ⟨hleg, h03 | h03 | h03 | h13 | h13 | h13 | h23 | h23 | h23⟩
    · let p : PatternTarget N := Sum.inr (Sum.inr
          ⟨y, hleg, ⟨0, 0, by simpa [fin3ToFin4, triangleEdgeStart,
            triangleEdgeEnd] using h03⟩⟩)
      refine ⟨p, hset p ?_⟩
      rfl
    · let p : PatternTarget N := Sum.inr (Sum.inr
          ⟨y, hleg, ⟨0, 1, by simpa [fin3ToFin4, triangleEdgeStart,
            triangleEdgeEnd] using h03⟩⟩)
      refine ⟨p, hset p ?_⟩
      rfl
    · let p : PatternTarget N := Sum.inr (Sum.inr
          ⟨y, hleg, ⟨0, 2, by simpa [fin3ToFin4, triangleEdgeStart,
            triangleEdgeEnd] using h03⟩⟩)
      refine ⟨p, hset p ?_⟩
      rfl
    · let p : PatternTarget N := Sum.inr (Sum.inr
          ⟨y, hleg, ⟨1, 0, by simpa [fin3ToFin4, triangleEdgeStart,
            triangleEdgeEnd] using h13⟩⟩)
      refine ⟨p, hset p ?_⟩
      rfl
    · let p : PatternTarget N := Sum.inr (Sum.inr
          ⟨y, hleg, ⟨1, 1, by simpa [fin3ToFin4, triangleEdgeStart,
            triangleEdgeEnd] using h13⟩⟩)
      refine ⟨p, hset p ?_⟩
      rfl
    · let p : PatternTarget N := Sum.inr (Sum.inr
          ⟨y, hleg, ⟨1, 2, by simpa [fin3ToFin4, triangleEdgeStart,
            triangleEdgeEnd] using h13⟩⟩)
      refine ⟨p, hset p ?_⟩
      rfl
    · let p : PatternTarget N := Sum.inr (Sum.inr
          ⟨y, hleg, ⟨2, 0, by simpa [fin3ToFin4, triangleEdgeStart,
            triangleEdgeEnd] using h23⟩⟩)
      refine ⟨p, hset p ?_⟩
      rfl
    · let p : PatternTarget N := Sum.inr (Sum.inr
          ⟨y, hleg, ⟨2, 1, by simpa [fin3ToFin4, triangleEdgeStart,
            triangleEdgeEnd] using h23⟩⟩)
      refine ⟨p, hset p ?_⟩
      rfl
    · let p : PatternTarget N := Sum.inr (Sum.inr
          ⟨y, hleg, ⟨2, 2, by simpa [fin3ToFin4, triangleEdgeStart,
            triangleEdgeEnd] using h23⟩⟩)
      refine ⟨p, hset p ?_⟩
      rfl

noncomputable abbrev OtherBadSet (N : ℕ) :=
  {Q : Finset (ℤ × ℤ) // Q ∈ otherBadIntQuads (intGrid N)}

noncomputable abbrev ClassifiedOtherBad (N : ℕ) :=
  (p : PatternTarget N) ×
    {Q : OtherBadSet N // patternSet p = Q.1}

noncomputable def tagOtherBad (N : ℕ) :
    OtherBadSet N → ClassifiedOtherBad N := fun Q => by
  let p : PatternTarget N := Classical.choose (exists_patternTarget_of_otherBad N Q)
  have hp : patternSet p = Q.1 :=
    Classical.choose_spec (exists_patternTarget_of_otherBad N Q)
  exact ⟨p, ⟨Q, hp⟩⟩

lemma tagOtherBad_injective (N : ℕ) : Function.Injective (tagOtherBad N) := by
  intro Q R h
  exact congrArg (fun z : ClassifiedOtherBad N => z.2.1) h

def classifiedOtherBadToPattern {N : ℕ} : ClassifiedOtherBad N → PatternTarget N :=
  fun z => z.1

lemma classifiedOtherBadToPattern_injective (N : ℕ) :
    Function.Injective (classifiedOtherBadToPattern (N := N)) := by
  rintro ⟨p, Q, hQ⟩ ⟨q, R, hR⟩ hpq
  dsimp [classifiedOtherBadToPattern] at hpq
  subst q
  have hQR : Q = R := by
    apply Subtype.ext
    exact hQ.symm.trans hR
  subst R
  rfl

lemma card_OtherBadSet (N : ℕ) :
    Nat.card (OtherBadSet N) = (otherBadIntQuads (intGrid N)).card := by
  exact Nat.subtype_card _ (fun _ => Iff.rfl)

lemma otherBadIntQuads_card_le_patternTarget (N : ℕ) :
    (otherBadIntQuads (intGrid N)).card ≤ Nat.card (PatternTarget N) := by
  rw [← card_OtherBadSet]
  calc
    Nat.card (OtherBadSet N) ≤ Nat.card (ClassifiedOtherBad N) :=
      Nat.card_le_card_of_injective (tagOtherBad N) (tagOtherBad_injective N)
    _ ≤ Nat.card (PatternTarget N) :=
      Nat.card_le_card_of_injective classifiedOtherBadToPattern
        (classifiedOtherBadToPattern_injective N)

lemma exists_otherBadIntQuads_grid_real_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N →
      ((otherBadIntQuads (intGrid N)).card : ℝ) ≤ C * (N : ℝ) ^ 5 := by
  obtain ⟨C₁, hC₁, hline⟩ := exists_collinearFour_grid_bound
  obtain ⟨C₂, hC₂, hext⟩ := exists_extensionFourAny_grid_bound
  refine ⟨2 * C₁ + C₂, by positivity, ?_⟩
  intro N hN
  have hkite : (Nat.card (KiteFour N) : ℝ) ≤ C₁ * (N : ℝ) ^ 5 := by
    have hkite' : (Nat.card (KiteFour N) : ℝ) ≤
        Nat.card (CollinearFour (expandedPlaneGrid N)) := by
      exact_mod_cast card_KiteFour_le_collinear N
    exact hkite'.trans (hline N hN)
  have hopp : (Nat.card (OppositeFour N) : ℝ) ≤ C₁ * (N : ℝ) ^ 5 := by
    have hopp' : (Nat.card (OppositeFour N) : ℝ) ≤
        Nat.card (CollinearFour (expandedPlaneGrid N)) := by
      exact_mod_cast card_OppositeFour_le_collinear N
    exact hopp'.trans (hline N hN)
  have hpattern : (Nat.card (PatternTarget N) : ℝ) ≤
      (2 * C₁ + C₂) * (N : ℝ) ^ 5 := by
    rw [Nat.card_sum, Nat.card_sum]
    push_cast
    nlinarith [hkite, hopp, hext N hN]
  have hcount : ((otherBadIntQuads (intGrid N)).card : ℝ) ≤
      Nat.card (PatternTarget N) := by
    exact_mod_cast otherBadIntQuads_card_le_patternTarget N
  exact hcount.trans hpattern

lemma exists_otherBadIntQuads_grid_bound :
    ∃ K : ℕ, ∀ N : ℕ,
      (otherBadIntQuads (intGrid N)).card ≤ K * N ^ 5 := by
  obtain ⟨C, hC, hreal⟩ := exists_otherBadIntQuads_grid_real_bound
  refine ⟨Nat.ceil C, ?_⟩
  intro N
  by_cases hN : N = 0
  · subst N
    simp [otherBadIntQuads, intGrid, intRange]
  · have hNone : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
    have hceil : C ≤ (Nat.ceil C : ℝ) := Nat.le_ceil C
    have hbound : ((otherBadIntQuads (intGrid N)).card : ℝ) ≤
        (Nat.ceil C : ℝ) * (N : ℝ) ^ 5 :=
      (hreal N hNone).trans (mul_le_mul_of_nonneg_right hceil (by positivity))
    exact_mod_cast hbound

open scoped LSeries.notation NNReal

noncomputable def chiFourComplex : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

def oddNatEquiv : ℕ ≃ {n : ℕ // Odd n} where
  toFun k := ⟨2 * k + 1, ⟨k, by omega⟩⟩
  invFun n := n.1 / 2
  left_inv k := by
    change (2 * k + 1) / 2 = k
    rw [Nat.add_comm, Nat.add_mul_div_left 1 k (by decide)]
    norm_num
  right_inv n := by
    apply Subtype.ext
    rcases n.2 with ⟨k, hk⟩
    change 2 * (n.1 / 2) + 1 = n.1
    rw [hk]
    have hhalf : (2 * k + 1) / 2 = k := by
      rw [Nat.add_comm, Nat.add_mul_div_left 1 k (by decide)]
      norm_num
    rw [hhalf]

noncomputable def betaTerm (s : ℝ) (k : ℕ) : ℝ :=
  (2 * k + 1 : ℕ) ^ (-s)

lemma betaTerm_summable {s : ℝ} (hs : 1 < s) : Summable (betaTerm s) := by
  have hbase : Summable (fun n : ℕ => ((n : ℝ) ^ s)⁻¹) :=
    Real.summable_nat_rpow_inv.mpr hs
  have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro i j h
    have h' : 2 * i = 2 * j := Nat.add_right_cancel h
    exact Nat.eq_of_mul_eq_mul_left (by omega) h'
  have hcomp := hbase.comp_injective hinj
  change Summable (fun k : ℕ => (((2 * k + 1 : ℕ) : ℝ) ^ s)⁻¹) at hcomp
  change Summable (fun k : ℕ => ((2 * k + 1 : ℕ) : ℝ) ^ (-s))
  exact hcomp.congr fun k => by
    rw [Real.rpow_neg (by positivity)]

lemma betaTerm_antitone {s : ℝ} (hs : 0 ≤ s) : Antitone (betaTerm s) := by
  intro i j hij
  unfold betaTerm
  apply Real.rpow_le_rpow_of_nonpos
  · positivity
  · norm_cast
    omega
  · linarith

lemma beta_tsum_mem_Icc {s : ℝ} (hs : 1 < s) :
    (∑' k : ℕ, (-1 : ℝ) ^ k * betaTerm s k) ∈ Set.Icc (0 : ℝ) 1 := by
  have hf := betaTerm_summable hs
  have halt : Summable (fun k : ℕ => (-1 : ℝ) ^ k * betaTerm s k) :=
    hf.alternating
  have htend := halt.tendsto_sum_tsum_nat
  have hanti := betaTerm_antitone (by linarith)
  change 0 ≤ (∑' k : ℕ, (-1 : ℝ) ^ k * betaTerm s k) ∧
    (∑' k : ℕ, (-1 : ℝ) ^ k * betaTerm s k) ≤ 1
  constructor
  · simpa using hanti.alternating_series_le_tendsto htend 0
  · simpa [betaTerm] using hanti.tendsto_le_alternating_series htend 0

@[simp] lemma chiFourComplex_apply_nat (n : ℕ) :
    chiFourComplex n = ((ZMod.χ₄ n : ℤ) : ℂ) := by
  rfl

lemma chiFourComplex_eq_zero_of_not_odd {n : ℕ} (hn : ¬ Odd n) :
    chiFourComplex n = 0 := by
  have heven : Even n := Nat.not_odd_iff_even.mp hn
  have hmod : n % 2 = 0 := Nat.even_iff.mp heven
  rw [chiFourComplex_apply_nat, ZMod.χ₄_nat_eq_if_mod_four]
  simp [hmod]

lemma chiFourComplex_odd (k : ℕ) :
    chiFourComplex ((2 * k + 1 : ℕ) : ZMod 4) =
      (((-1 : ℝ) ^ k : ℝ) : ℂ) := by
  rw [chiFourComplex_apply_nat, ZMod.χ₄_eq_neg_one_pow (by omega)]
  have hhalf : (2 * k + 1) / 2 = k := by
    rw [Nat.add_comm, Nat.add_mul_div_left 1 k (by decide)]
    norm_num
  rw [hhalf]
  norm_num

lemma chiFour_LSeries_term_odd (s : ℝ) (k : ℕ) :
    LSeries.term (fun n => chiFourComplex n) (s : ℂ) (2 * k + 1) =
      (((-1 : ℝ) ^ k * betaTerm s k : ℝ) : ℂ) := by
  rw [LSeries.term_of_ne_zero (by omega), chiFourComplex_odd]
  change ((((-1 : ℝ) ^ k : ℝ) : ℂ) /
      ((((2 * k + 1 : ℕ) : ℝ) : ℂ) ^ ((s : ℝ) : ℂ))) =
        (((-1 : ℝ) ^ k * betaTerm s k : ℝ) : ℂ)
  rw [← Complex.ofReal_cpow (show (0 : ℝ) ≤ (2 * k + 1 : ℕ) by positivity) s]
  rw [← Complex.ofReal_div]
  congr 1
  unfold betaTerm
  rw [Real.rpow_neg (by positivity)]
  ring

lemma chiFour_LSeries_term_eq_zero_of_not_odd (s : ℝ) {n : ℕ}
    (hn : ¬ Odd n) :
    LSeries.term (fun m => chiFourComplex m) (s : ℂ) n = 0 := by
  rw [LSeries.term_def]
  split_ifs with hn0
  · rfl
  · rw [chiFourComplex_eq_zero_of_not_odd hn]
    simp

lemma chiFour_LSeries_eq_beta (s : ℝ) :
    LSeries (fun n => chiFourComplex n) (s : ℂ) =
      ((∑' k : ℕ, (-1 : ℝ) ^ k * betaTerm s k) : ℝ) := by
  unfold LSeries
  calc
    (∑' n : ℕ, LSeries.term (fun m => chiFourComplex m) (s : ℂ) n) =
        ∑' n : {n : ℕ // Odd n},
          LSeries.term (fun m => chiFourComplex m) (s : ℂ) n := by
      symm
      calc
        (∑' n : {n : ℕ // Odd n},
            LSeries.term (fun m => chiFourComplex m) (s : ℂ) n) =
            ∑' n : ℕ, ({n : ℕ | Odd n} : Set ℕ).indicator
              (LSeries.term (fun m => chiFourComplex m) (s : ℂ)) n :=
          tsum_subtype ({n : ℕ | Odd n} : Set ℕ)
            (LSeries.term (fun m => chiFourComplex m) (s : ℂ))
        _ = ∑' n : ℕ,
            LSeries.term (fun m => chiFourComplex m) (s : ℂ) n := by
          apply tsum_congr
          intro n
          by_cases hn : Odd n
          · simp [Set.indicator, hn]
          · simp only [Set.indicator, Set.mem_ofPred_eq, hn, if_false]
            exact (chiFour_LSeries_term_eq_zero_of_not_odd s hn).symm
    _ = ∑' k : ℕ,
        LSeries.term (fun m => chiFourComplex m) (s : ℂ)
          ((oddNatEquiv k : {n : ℕ // Odd n}) : ℕ) := by
      exact (oddNatEquiv.tsum_eq
        (fun n : {n : ℕ // Odd n} =>
          LSeries.term (fun m => chiFourComplex m) (s : ℂ) n)).symm
    _ = ∑' k : ℕ,
        (((-1 : ℝ) ^ k * betaTerm s k : ℝ) : ℂ) := by
      apply tsum_congr
      intro k
      exact chiFour_LSeries_term_odd s k
    _ = ((∑' k : ℕ, (-1 : ℝ) ^ k * betaTerm s k) : ℝ) := by
      exact (Complex.ofReal_tsum
        (fun k : ℕ => (-1 : ℝ) ^ k * betaTerm s k)).symm

lemma norm_chiFour_LSeries_le_one {s : ℝ} (hs : 1 < s) :
    ‖LSeries (fun n => chiFourComplex n) (s : ℂ)‖ ≤ 1 := by
  let b : ℝ := ∑' k : ℕ, (-1 : ℝ) ^ k * betaTerm s k
  have hb : b ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [b] using beta_tsum_mem_Icc hs
  have hL : LSeries (fun n => chiFourComplex n) (s : ℂ) = (b : ℂ) := by
    simpa [b] using chiFour_LSeries_eq_beta s
  rw [hL, Complex.norm_real, Real.norm_of_nonneg hb.1]
  exact hb.2

noncomputable def zetaRealTerm (s : ℝ) (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ (-s)

lemma zetaRealTerm_summable {s : ℝ} (hs : 1 < s) :
    Summable (zetaRealTerm s) := by
  have hbase : Summable (fun n : ℕ => ((n : ℝ) ^ s)⁻¹) :=
    Real.summable_nat_rpow_inv.mpr hs
  have hinj : Function.Injective (fun n : ℕ => n + 1) := by
    intro i j h
    exact Nat.add_right_cancel h
  have hcomp := hbase.comp_injective hinj
  change Summable (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) ^ s)⁻¹)) at hcomp
  change Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-s))
  exact hcomp.congr fun n => by rw [Real.rpow_neg (by positivity)]

lemma zetaReal_tsum_le {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, zetaRealTerm s n) ≤ 1 + 1 / (s - 1) := by
  let f : ℝ → ℝ := fun x => x ^ (-s)
  have hanti : AntitoneOn f (Set.Ici (1 : ℝ)) := by
    intro x hx y _hy hxy
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hx) hxy (by linarith)
  have hint : MeasureTheory.IntegrableOn f (Set.Ioi (1 : ℝ)) := by
    exact integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hnonneg : ∀ x ∈ Set.Ioi (1 : ℝ), 0 ≤ f x := by
    intro x _hx
    have hx1 : (1 : ℝ) < x := _hx
    exact Real.rpow_nonneg (by linarith : 0 ≤ x) _
  have htail := AntitoneOn.tsum_comp_add_le_integral (f := f) 1
    (by simpa using hanti) (by simpa using hint) (by simpa using hnonneg)
  have hintegral : (∫ x : ℝ in Set.Ioi ((1 : ℕ) : ℝ), f x) =
      1 / (s - 1) := by
    change (∫ x : ℝ in Set.Ioi ((1 : ℕ) : ℝ), x ^ (-s)) = 1 / (s - 1)
    rw [integral_Ioi_rpow_of_lt (by linarith)
      (by norm_num : (0 : ℝ) < ((1 : ℕ) : ℝ))]
    norm_num [Real.one_rpow]
    rw [show -s + 1 = -(s - 1) by ring, div_neg, neg_div, neg_neg]
    simp [div_eq_mul_inv]
  rw [hintegral] at htail
  have hsum := zetaRealTerm_summable hs
  rw [hsum.tsum_eq_zero_add]
  calc
    zetaRealTerm s 0 + (∑' n : ℕ, zetaRealTerm s (n + 1)) =
        1 + (∑' n : ℕ, f (n + 1 + 1 : ℕ)) := by
      congr 1; simp [zetaRealTerm]
    _ ≤ 1 + 1 / (s - 1) := by
      simpa [add_comm] using add_le_add_left htail 1

lemma riemannZeta_real_eq {s : ℝ} (hs : 1 < s) :
    riemannZeta (s : ℂ) = ((∑' n : ℕ, zetaRealTerm s n) : ℂ) := by
  calc
    riemannZeta (s : ℂ) =
        ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ (s : ℂ) :=
      zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs)
    _ = ∑' n : ℕ, (zetaRealTerm s n : ℂ) := by
      apply tsum_congr
      intro n
      have hcast : (n : ℂ) + 1 = ((((n + 1 : ℕ) : ℝ) : ℂ)) := by
        norm_num
      rw [hcast]
      change 1 / ((((n + 1 : ℕ) : ℝ) : ℂ) ^ ((s : ℝ) : ℂ)) =
        (zetaRealTerm s n : ℂ)
      rw [← Complex.ofReal_cpow (by positivity) s, ← Complex.ofReal_one,
        ← Complex.ofReal_div]
      congr 1
      unfold zetaRealTerm
      rw [Real.rpow_neg (by positivity)]
      ring
    _ = ((∑' n : ℕ, zetaRealTerm s n) : ℂ) := by rfl

lemma norm_riemannZeta_real_le {s : ℝ} (hs : 1 < s) :
    ‖riemannZeta (s : ℂ)‖ ≤ 1 + 1 / (s - 1) := by
  let z : ℝ := ∑' n : ℕ, zetaRealTerm s n
  have hz0 : 0 ≤ z := by
    dsimp [z]
    exact tsum_nonneg fun n => Real.rpow_nonneg (by positivity) _
  have hzeta : riemannZeta (s : ℂ) = (z : ℂ) := by
    dsimp [z]
    exact (riemannZeta_real_eq hs).trans
      (Complex.ofReal_tsum (zetaRealTerm s)).symm
  rw [hzeta, Complex.norm_real, Real.norm_of_nonneg hz0]
  simpa [z] using zetaReal_tsum_le hs

noncomputable def realZetaFactor (s : ℝ) (p : ℕ) : ℝ :=
  (1 - (p : ℝ) ^ (-s))⁻¹

noncomputable def complexZetaFactor (s : ℝ) (p : ℕ) : ℂ :=
  (1 - (p : ℂ) ^ (-(s : ℂ)))⁻¹

noncomputable def complexChiFactor (s : ℝ) (p : ℕ) : ℂ :=
  (1 - chiFourComplex p * (p : ℂ) ^ (-(s : ℂ)))⁻¹

lemma complex_nat_cpow_neg_real (s : ℝ) (p : ℕ) :
    (p : ℂ) ^ (-(s : ℂ)) = (((p : ℝ) ^ (-s) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg]
  exact (Complex.ofReal_cpow (Nat.cast_nonneg p) (-s)).symm

lemma norm_complexZetaFactor (s : ℝ) (p : ℕ) :
    ‖complexZetaFactor s p‖ = |realZetaFactor s p| := by
  rw [complexZetaFactor, complex_nat_cpow_neg_real]
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_inv,
    Complex.norm_real, Real.norm_eq_abs]
  rfl

lemma chiFourComplex_prime_of_mod_one {p : ℕ}
    (hmod : p % 4 = 1) : chiFourComplex p = 1 := by
  rw [chiFourComplex_apply_nat, ZMod.χ₄_nat_eq_if_mod_four]
  have hodd : p % 2 = 1 := by omega
  simp [hodd, hmod]

lemma chiFourComplex_prime_of_mod_three {p : ℕ}
    (hmod : p % 4 = 3) : chiFourComplex p = -1 := by
  rw [chiFourComplex_apply_nat, ZMod.χ₄_nat_eq_if_mod_four]
  have hodd : p % 2 = 1 := by omega
  simp [hodd, hmod]

lemma chiFourComplex_prime_two : chiFourComplex 2 = 0 := by
  change chiFourComplex ((2 : ℕ) : ZMod 4) = 0
  rw [chiFourComplex_apply_nat, ZMod.χ₄_nat_eq_if_mod_four]
  norm_num

lemma prime_mod_four_cases {p : ℕ} (hp : p.Prime) :
    p = 2 ∨ p % 4 = 1 ∨ p % 4 = 3 := by
  by_cases htwo : p = 2
  · exact Or.inl htwo
  right
  have hodd : Odd p := hp.odd_of_ne_two htwo
  have hmodlt : p % 4 < 4 := Nat.mod_lt _ (by omega)
  have hpmod2 : p % 2 = 1 := Nat.odd_iff.mp hodd
  have hmododd : p % 4 % 2 = 1 := by omega
  omega

lemma prime_rpow_neg_pos_le_half {s : ℝ} (hs : 1 ≤ s) {p : ℕ}
    (hp : p.Prime) :
    0 < (p : ℝ) ^ (-s) ∧ (p : ℝ) ^ (-s) ≤ 1 / 2 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpPow : (2 : ℝ) ≤ (p : ℝ) ^ s := by
    calc
      (2 : ℝ) ≤ p := hpTwo
      _ = (p : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (p : ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le hpOne hs
  constructor
  · exact Real.rpow_pos_of_pos hpR _
  · rw [Real.rpow_neg hpR.le]
    simpa only [one_div] using
      (inv_le_inv₀ (Real.rpow_pos_of_pos hpR s) (by norm_num : (0 : ℝ) < 2)).2 hpPow

lemma realZetaFactor_pos {s : ℝ} (hs : 1 ≤ s) {p : ℕ}
    (hp : p.Prime) : 0 < realZetaFactor s p := by
  have ha := (prime_rpow_neg_pos_le_half hs hp).2
  unfold realZetaFactor
  exact inv_pos.mpr (by linarith)

lemma realZetaFactor_one_le {s : ℝ} (hs : 1 ≤ s) {p : ℕ}
    (hp : p.Prime) : 1 ≤ realZetaFactor s p := by
  have ha := prime_rpow_neg_pos_le_half hs hp
  unfold realZetaFactor
  exact (one_le_inv₀ (by linarith)).2 (by linarith)

lemma realZetaFactor_le_two {s : ℝ} (hs : 1 ≤ s) {p : ℕ}
    (hp : p.Prime) : realZetaFactor s p ≤ 2 := by
  have ha := prime_rpow_neg_pos_le_half hs hp
  unfold realZetaFactor
  rw [inv_le_comm₀ (by linarith) (by norm_num : (0 : ℝ) < 2)]
  linarith

noncomputable def combinedFactor (s : ℝ) (p : ℕ) : ℝ :=
  ‖complexZetaFactor s p‖ * ‖complexChiFactor s p‖

lemma combinedFactor_of_mod_one {s : ℝ} (hs : 1 ≤ s) {p : ℕ}
    (hp : p.Prime) (hmod : p % 4 = 1) :
    combinedFactor s p = (realZetaFactor s p) ^ 2 := by
  have hpos := realZetaFactor_pos hs hp
  rw [combinedFactor, complexChiFactor,
    chiFourComplex_prime_of_mod_one hmod]
  simp only [one_mul]
  change ‖complexZetaFactor s p‖ * ‖complexZetaFactor s p‖ = _
  rw [norm_complexZetaFactor s p, abs_of_pos hpos]
  ring

lemma combinedFactor_two {s : ℝ} (hs : 1 ≤ s) :
    combinedFactor s 2 = realZetaFactor s 2 := by
  have hp : Nat.Prime 2 := Nat.prime_two
  have hpos := realZetaFactor_pos hs hp
  have hchi : chiFourComplex ((2 : ℕ) : ZMod 4) = 0 :=
    chiFourComplex_prime_two
  rw [combinedFactor, complexChiFactor, hchi]
  simp only [zero_mul, sub_zero, inv_one, norm_one, mul_one]
  rw [norm_complexZetaFactor s 2, abs_of_pos hpos]

lemma combinedFactor_of_mod_three {s : ℝ} (hs : 1 ≤ s) {p : ℕ}
    (hp : p.Prime) (hmod : p % 4 = 3) :
    combinedFactor s p = (1 - ((p : ℝ) ^ (-s)) ^ 2)⁻¹ := by
  let a : ℝ := (p : ℝ) ^ (-s)
  have ha := prime_rpow_neg_pos_le_half hs hp
  have hza : 0 < 1 - a := by dsimp [a]; linarith
  have hca : 0 < 1 + a := by dsimp [a]; linarith
  have hsq : 0 < 1 - a ^ 2 := by nlinarith
  rw [combinedFactor, complexChiFactor,
    chiFourComplex_prime_of_mod_three hmod,
    complex_nat_cpow_neg_real, norm_complexZetaFactor s p]
  change |realZetaFactor s p| * ‖(1 - (-1 : ℂ) * (a : ℂ))⁻¹‖ = _
  rw [abs_of_pos (realZetaFactor_pos hs hp)]
  rw [neg_one_mul, sub_neg_eq_add, ← Complex.ofReal_one,
    ← Complex.ofReal_add, ← Complex.ofReal_inv, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.mpr hca.le)]
  unfold realZetaFactor
  dsimp [a] at hza hca ⊢
  dsimp [a] at hsq
  field_simp [ne_of_gt hza, ne_of_gt hca, ne_of_gt hsq]
  ring

lemma combinedFactor_one_le {s : ℝ} (hs : 1 ≤ s) {p : ℕ}
    (hp : p.Prime) : 1 ≤ combinedFactor s p := by
  rcases prime_mod_four_cases hp with rfl | hmod | hmod
  · rw [combinedFactor_two hs]
    exact realZetaFactor_one_le hs Nat.prime_two
  · rw [combinedFactor_of_mod_one hs hp hmod]
    nlinarith [realZetaFactor_one_le hs hp]
  · rw [combinedFactor_of_mod_three hs hp hmod]
    have ha := prime_rpow_neg_pos_le_half hs hp
    exact (one_le_inv₀ (by nlinarith)).2 (by nlinarith)

lemma combinedFactor_hasProd {s : ℝ} (hs : 1 < s) :
    HasProd (fun p : Nat.Primes => combinedFactor s p)
      ‖riemannZeta (s : ℂ) * LSeries (fun n => chiFourComplex n) (s : ℂ)‖ := by
  have hz := riemannZeta_eulerProduct_hasProd (s := (s : ℂ)) (by simpa using hs)
  have hL := DirichletCharacter.LSeries_eulerProduct_hasProd
    chiFourComplex (s := (s : ℂ)) (by simpa using hs)
  have hmul := hz.mul hL
  have hnorm := hmul.norm
  simpa only [combinedFactor, complexZetaFactor, complexChiFactor, norm_mul] using hnorm

lemma combinedFactor_prod_le {s : ℝ} (hs : 1 < s) (N : ℕ) :
    (∏ p ∈ N.primesBelow, combinedFactor s p) ≤
      ‖riemannZeta (s : ℂ) * LSeries (fun n => chiFourComplex n) (s : ℂ)‖ := by
  let f : ℕ → ℝ≥0 := fun p =>
    ‖complexZetaFactor s p‖₊ * ‖complexChiFactor s p‖₊
  have hz := riemannZeta_eulerProduct_hasProd (s := (s : ℂ)) (by simpa using hs)
  have hL := DirichletCharacter.LSeries_eulerProduct_hasProd
    chiFourComplex (s := (s : ℂ)) (by simpa using hs)
  have hmul := hz.mul hL
  have hnnPrime : HasProd (fun p : Nat.Primes => f p)
      ‖riemannZeta (s : ℂ) * LSeries (fun n => chiFourComplex n) (s : ℂ)‖₊ := by
    have hcont : Continuous (nnnormHom.toMonoidHom : ℂ → ℝ≥0) := by
      change Continuous fun z : ℂ => ‖z‖₊
      exact (continuous_nnnorm : Continuous fun z : ℂ => ‖z‖₊)
    have hmap := hmul.map nnnormHom.toMonoidHom hcont
    change HasProd (fun p : Nat.Primes =>
        ‖complexZetaFactor s p * complexChiFactor s p‖₊)
      ‖riemannZeta (s : ℂ) *
        LSeries (fun n => chiFourComplex n) (s : ℂ)‖₊ at hmap
    simpa only [f, nnnorm_mul] using hmap
  have hnn : HasProd (fun n : ℕ => if n.Prime then f n else 1)
      ‖riemannZeta (s : ℂ) * LSeries (fun n => chiFourComplex n) (s : ℂ)‖₊ :=
    (Nat.Primes.hasProd_iff_hasProd_ite f).mp hnnPrime
  have hle : (∏ p ∈ N.primesBelow, f p) ≤
      ‖riemannZeta (s : ℂ) * LSeries (fun n => chiFourComplex n) (s : ℂ)‖₊ := by
    calc
      (∏ p ∈ N.primesBelow, f p) =
          ∏ p ∈ N.primesBelow, if p.Prime then f p else 1 := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [if_pos (Nat.prime_of_mem_primesBelow hp)]
      _ ≤ ‖riemannZeta (s : ℂ) *
          LSeries (fun n => chiFourComplex n) (s : ℂ)‖₊ := by
        apply prod_le_hasProd _ _ hnn
        intro p _hp
        by_cases hp : p.Prime
        · rw [if_pos hp]
          change (1 : ℝ) ≤ combinedFactor s p
          exact combinedFactor_one_le (le_of_lt hs) hp
        · simp [hp]
  have hle' : ((↑(∏ p ∈ N.primesBelow, f p) : ℝ) ≤
      (↑‖riemannZeta (s : ℂ) *
        LSeries (fun n => chiFourComplex n) (s : ℂ)‖₊ : ℝ)) :=
    NNReal.coe_le_coe.mpr hle
  simpa only [f, combinedFactor, NNReal.coe_prod, NNReal.coe_mul,
    coe_nnnorm] using hle'

lemma combinedFactor_prod_le_zeta {s : ℝ} (hs : 1 < s) (N : ℕ) :
    (∏ p ∈ N.primesBelow, combinedFactor s p) ≤ 1 + 1 / (s - 1) := by
  calc
    (∏ p ∈ N.primesBelow, combinedFactor s p) ≤
        ‖riemannZeta (s : ℂ) * LSeries (fun n => chiFourComplex n) (s : ℂ)‖ :=
      combinedFactor_prod_le hs N
    _ = ‖riemannZeta (s : ℂ)‖ *
        ‖LSeries (fun n => chiFourComplex n) (s : ℂ)‖ := norm_mul _ _
    _ ≤ (1 + 1 / (s - 1)) * 1 := by
      exact mul_le_mul (norm_riemannZeta_real_le hs)
        (norm_chiFour_LSeries_le_one hs) (norm_nonneg _) (by positivity)
    _ = 1 + 1 / (s - 1) := mul_one _

noncomputable def goodFactor (s : ℝ) (p : ℕ) : ℝ :=
  if p % 4 = 3 then 1 else realZetaFactor s p

lemma goodFactor_one_le {s : ℝ} (hs : 1 ≤ s) {p : ℕ} (hp : p.Prime) :
    1 ≤ goodFactor s p := by
  unfold goodFactor
  split_ifs
  · exact le_rfl
  · exact realZetaFactor_one_le hs hp

lemma goodFactor_two_le {s : ℝ} (hs : 1 ≤ s) :
    goodFactor s 2 ≤ 2 := by
  rw [goodFactor, if_neg (by norm_num)]
  exact realZetaFactor_le_two hs Nat.prime_two

lemma goodFactor_sq_le_combined {s : ℝ} (hs : 1 ≤ s) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    (goodFactor s p) ^ 2 ≤ combinedFactor s p := by
  rcases prime_mod_four_cases hp with htwo | hmod | hmod
  · exact (hp2 htwo).elim
  · rw [goodFactor, if_neg (by omega), combinedFactor_of_mod_one hs hp hmod]
  · rw [goodFactor, if_pos hmod]
    simpa using combinedFactor_one_le hs hp

lemma goodFactor_prod_sq_le_four_combined {s : ℝ} (hs : 1 ≤ s) (N : ℕ) :
    (∏ p ∈ N.primesBelow, goodFactor s p) ^ 2 ≤
      4 * ∏ p ∈ N.primesBelow, combinedFactor s p := by
  classical
  let S := N.primesBelow
  let R := S.erase 2
  have hgood0 (p : ℕ) (hp : p ∈ S) : 0 ≤ goodFactor s p :=
    (goodFactor_one_le hs (Nat.prime_of_mem_primesBelow hp)).trans' zero_le_one
  have hrest0 : 0 ≤ ∏ p ∈ R, goodFactor s p := by
    exact Finset.prod_nonneg fun p hp => hgood0 p (by
      dsimp [R] at hp
      exact Finset.mem_of_mem_erase hp)
  have hfull_le : (∏ p ∈ S, goodFactor s p) ≤
      2 * ∏ p ∈ R, goodFactor s p := by
    by_cases h2 : 2 ∈ S
    · rw [← Finset.mul_prod_erase _ _ h2]
      exact mul_le_mul_of_nonneg_right (goodFactor_two_le hs) hrest0
    · have hRS : R = S := Finset.erase_eq_of_notMem h2
      rw [hRS]
      nlinarith [show 0 ≤ ∏ p ∈ S, goodFactor s p from
        Finset.prod_nonneg fun p hp => hgood0 p hp]
  have hrest_sq : (∏ p ∈ R, goodFactor s p) ^ 2 ≤
      ∏ p ∈ R, combinedFactor s p := by
    rw [← Finset.prod_pow]
    exact Finset.prod_le_prod
      (fun p hp => by positivity)
      (fun p hp => by
        have hp' : p ∈ S := by
          dsimp [R] at hp
          exact Finset.mem_of_mem_erase hp
        exact goodFactor_sq_le_combined hs
          (Nat.prime_of_mem_primesBelow hp')
          (by
            dsimp [R] at hp
            exact Finset.ne_of_mem_erase hp))
  have hcombined_sub : (∏ p ∈ R, combinedFactor s p) ≤
      ∏ p ∈ S, combinedFactor s p := by
    by_cases h2 : 2 ∈ S
    · rw [← Finset.mul_prod_erase _ _ h2]
      exact le_mul_of_one_le_left
        (Finset.prod_nonneg fun p hp => by
          exact (combinedFactor_one_le hs
            (Nat.prime_of_mem_primesBelow (by
              dsimp [R] at hp
              exact Finset.mem_of_mem_erase hp))).trans' zero_le_one)
        (combinedFactor_one_le hs Nat.prime_two)
    · rw [show R = S from Finset.erase_eq_of_notMem h2]
  calc
    (∏ p ∈ N.primesBelow, goodFactor s p) ^ 2 =
        (∏ p ∈ S, goodFactor s p) ^ 2 := by rfl
    _ ≤ (2 * ∏ p ∈ R, goodFactor s p) ^ 2 :=
      pow_le_pow_left₀ (Finset.prod_nonneg fun p hp => hgood0 p hp) hfull_le 2
    _ = 4 * (∏ p ∈ R, goodFactor s p) ^ 2 := by ring
    _ ≤ 4 * ∏ p ∈ R, combinedFactor s p := by gcongr
    _ ≤ 4 * ∏ p ∈ S, combinedFactor s p := by gcongr
    _ = 4 * ∏ p ∈ N.primesBelow, combinedFactor s p := by rfl

lemma realZetaFactor_one_le_exp_mul {s : ℝ} (hs : 1 ≤ s) {p : ℕ}
    (hp : p.Prime) :
    realZetaFactor 1 p ≤
      Real.exp ((s - 1) * Real.log p / (p - 1 : ℕ)) *
        realZetaFactor s p := by
  let x : ℝ := (p : ℝ)⁻¹
  let y : ℝ := (p : ℝ) ^ (-s)
  let u : ℝ := (s - 1) * Real.log p
  let d : ℝ := u / (p - 1 : ℕ)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpOne : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hpOne
  have hu : 0 ≤ u := mul_nonneg (sub_nonneg.mpr hs) hlog.le
  have hx : 0 < x := by dsimp [x]; positivity
  have hxhalf : x ≤ 1 / 2 := by
    simpa [x, Real.rpow_neg_one] using
      (prime_rpow_neg_pos_le_half (s := 1) (by norm_num) hp).2
  have hy := prime_rpow_neg_pos_le_half hs hp
  have hpred : (0 : ℝ) < (p - 1 : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
  have hd : 0 ≤ d := div_nonneg hu hpred.le
  have hyexp : y = x * Real.exp (-u) := by
    dsimp [x, y, u]
    rw [show -s = (-1 : ℝ) + -(s - 1) by ring,
      Real.rpow_add hpR, Real.rpow_neg_one,
      Real.rpow_def_of_pos hpR]
    congr 1
    ring
  have hexp : 1 - Real.exp (-u) ≤ u := by
    linarith [Real.one_sub_le_exp_neg u]
  have hxy : x - y ≤ x * u := by
    rw [hyexp]
    calc
      x - x * Real.exp (-u) = x * (1 - Real.exp (-u)) := by ring
      _ ≤ x * u := mul_le_mul_of_nonneg_left hexp hx.le
  have hdu : d * (1 - x) = x * u := by
    dsimp [d, x]
    have hpne : (p : ℝ) ≠ 0 := ne_of_gt hpR
    have hpredEq : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hp.one_le]
      norm_num
    rw [hpredEq]
    have hp1ne : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hpOne)
    field_simp [hpne, hp1ne]
  have hcross : 1 - y ≤ (1 + d) * (1 - x) := by
    rw [add_mul, one_mul, hdu]
    linarith
  have hbase : realZetaFactor 1 p ≤ (1 + d) * realZetaFactor s p := by
    unfold realZetaFactor
    rw [Real.rpow_neg_one]
    change (1 - x)⁻¹ ≤ (1 + d) * (1 - y)⁻¹
    rw [← one_div, ← div_eq_mul_inv]
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    simpa using hcross
  calc
    realZetaFactor 1 p ≤ (1 + d) * realZetaFactor s p := hbase
    _ ≤ Real.exp d * realZetaFactor s p := by
      exact mul_le_mul_of_nonneg_right (by
        simpa [add_comm] using Real.add_one_le_exp d)
        (realZetaFactor_pos hs hp).le
    _ = Real.exp ((s - 1) * Real.log p / (p - 1 : ℕ)) *
        realZetaFactor s p := by rfl

lemma goodFactor_one_le_exp_mul {s : ℝ} (hs : 1 ≤ s) {p : ℕ}
    (hp : p.Prime) :
    goodFactor 1 p ≤
      Real.exp ((s - 1) * Real.log p / (p - 1 : ℕ)) *
        goodFactor s p := by
  by_cases hmod : p % 4 = 3
  · rw [goodFactor, if_pos hmod, goodFactor, if_pos hmod, mul_one]
    apply Real.one_le_exp
    exact div_nonneg
      (mul_nonneg (sub_nonneg.mpr hs)
        (Real.log_nonneg (by exact_mod_cast hp.one_le)))
      (by positivity)
  · rw [goodFactor, if_neg hmod, goodFactor, if_neg hmod]
    exact realZetaFactor_one_le_exp_mul hs hp

lemma goodFactor_one_prod_le_shift {s : ℝ} (hs : 1 ≤ s) (N : ℕ) :
    (∏ p ∈ (N + 1).primesBelow, goodFactor 1 p) ≤
      Real.exp ((s - 1) *
        BoundedGaps.Maynard.primeLogPredecessorSum N) *
        ∏ p ∈ (N + 1).primesBelow, goodFactor s p := by
  have hpoint (p : ℕ) (hp : p ∈ (N + 1).primesBelow) :=
    goodFactor_one_le_exp_mul hs (Nat.prime_of_mem_primesBelow hp)
  calc
    (∏ p ∈ (N + 1).primesBelow, goodFactor 1 p) ≤
        ∏ p ∈ (N + 1).primesBelow,
          (Real.exp ((s - 1) * Real.log p / (p - 1 : ℕ)) *
            goodFactor s p) := by
      exact Finset.prod_le_prod
        (fun p hp => by
          exact (goodFactor_one_le (by norm_num)
            (Nat.prime_of_mem_primesBelow hp)).trans' zero_le_one)
        hpoint
    _ = (∏ p ∈ (N + 1).primesBelow,
          Real.exp ((s - 1) * Real.log p / (p - 1 : ℕ))) *
        ∏ p ∈ (N + 1).primesBelow, goodFactor s p := by
      rw [Finset.prod_mul_distrib]
    _ = Real.exp (∑ p ∈ (N + 1).primesBelow,
          ((s - 1) * Real.log p / (p - 1 : ℕ))) *
        ∏ p ∈ (N + 1).primesBelow, goodFactor s p := by
      rw [Real.exp_sum]
    _ = Real.exp ((s - 1) *
          BoundedGaps.Maynard.primeLogPredecessorSum N) *
        ∏ p ∈ (N + 1).primesBelow, goodFactor s p := by
      congr 2
      rw [show (N + 1).primesBelow = Nat.primesLE N by rfl]
      unfold BoundedGaps.Maynard.primeLogPredecessorSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

lemma exists_goodFactor_one_prod_le_sqrt_log :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      (∏ p ∈ (N + 1).primesBelow, goodFactor 1 p) ≤
        C * Real.sqrt (Real.log (N : ℝ)) := by
  obtain ⟨C₀, hC₀⟩ :=
    BoundedGaps.Maynard.exists_uniform_abs_primeLogPredecessorSum_sub_log
  refine ⟨4 * Real.exp (1 + |C₀|), by positivity, ?_⟩
  intro N hN
  let ell : ℝ := Real.log (N : ℝ)
  let s : ℝ := 1 + 1 / ell
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL1 : 1 ≤ ell := by
    dsimp [ell]
    rw [Real.le_log_iff_exp_le hNpos]
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hN)
  have hLpos : 0 < ell := lt_of_lt_of_le zero_lt_one hL1
  have hs : 1 < s := by
    dsimp [s]
    have : 0 < 1 / ell := one_div_pos.mpr hLpos
    linarith
  have hmert :
      BoundedGaps.Maynard.primeLogPredecessorSum N ≤ ell + |C₀| := by
    have h := hC₀ N
    dsimp [ell]
    have hdiff := le_abs_self
      (BoundedGaps.Maynard.primeLogPredecessorSum N - Real.log (N : ℝ))
    have hCabs : C₀ ≤ |C₀| := le_abs_self C₀
    linarith
  have hexponent :
      (s - 1) * BoundedGaps.Maynard.primeLogPredecessorSum N ≤
        1 + |C₀| := by
    have habs : 0 ≤ |C₀| := abs_nonneg C₀
    dsimp [s]
    rw [add_sub_cancel_left]
    calc
      1 / ell * BoundedGaps.Maynard.primeLogPredecessorSum N =
          BoundedGaps.Maynard.primeLogPredecessorSum N / ell := by ring
      _ ≤ (1 + |C₀|) := by
        rw [div_le_iff₀ hLpos]
        nlinarith
  let P : ℝ := ∏ p ∈ (N + 1).primesBelow, goodFactor s p
  have hP0 : 0 ≤ P := by
    dsimp [P]
    exact Finset.prod_nonneg fun p hp =>
      (goodFactor_one_le (le_of_lt hs)
        (Nat.prime_of_mem_primesBelow hp)).trans' zero_le_one
  have hrecip : 1 / (s - 1) = ell := by
    dsimp [s]
    rw [add_sub_cancel_left]
    field_simp [ne_of_gt hLpos]
  have hPsq : P ^ 2 ≤ 4 * (1 + ell) := by
    calc
      P ^ 2 ≤ 4 * ∏ p ∈ (N + 1).primesBelow, combinedFactor s p := by
        simpa [P] using goodFactor_prod_sq_le_four_combined (le_of_lt hs) (N + 1)
      _ ≤ 4 * (1 + 1 / (s - 1)) := by
        gcongr
        exact combinedFactor_prod_le_zeta hs (N + 1)
      _ = 4 * (1 + ell) := by rw [hrecip]
  have hP : P ≤ 4 * Real.sqrt ell := by
    have hroot0 : 0 ≤ Real.sqrt (1 + ell) := Real.sqrt_nonneg _
    have hrootL0 : 0 ≤ Real.sqrt ell := Real.sqrt_nonneg _
    have hrootSq : (Real.sqrt (1 + ell)) ^ 2 = 1 + ell :=
      Real.sq_sqrt (by linarith)
    have hrootLSq : (Real.sqrt ell) ^ 2 = ell := Real.sq_sqrt hLpos.le
    have hPfirst : P ≤ 2 * Real.sqrt (1 + ell) := by
      nlinarith
    have hroot : Real.sqrt (1 + ell) ≤ 2 * Real.sqrt ell := by
      nlinarith
    linarith
  have hshift := goodFactor_one_prod_le_shift (le_of_lt hs) N
  calc
    (∏ p ∈ (N + 1).primesBelow, goodFactor 1 p) ≤
        Real.exp ((s - 1) *
          BoundedGaps.Maynard.primeLogPredecessorSum N) * P := by
      simpa [P] using hshift
    _ ≤ Real.exp (1 + |C₀|) * (4 * Real.sqrt ell) := by
      exact mul_le_mul (Real.exp_le_exp.mpr hexponent) hP hP0
        (Real.exp_pos _).le
    _ = (4 * Real.exp (1 + |C₀|)) *
        Real.sqrt (Real.log (N : ℝ)) := by
      dsimp [ell]
      ring

lemma realZetaFactor_prod_le_zeta {s : ℝ} (hs : 1 < s) (N : ℕ) :
    (∏ p ∈ N.primesBelow, realZetaFactor s p) ≤
      ‖riemannZeta (s : ℂ)‖ := by
  let f : ℕ → ℝ≥0 := fun p => ‖complexZetaFactor s p‖₊
  have hz := riemannZeta_eulerProduct_hasProd (s := (s : ℂ)) (by simpa using hs)
  have hnnPrime : HasProd (fun p : Nat.Primes => f p)
      ‖riemannZeta (s : ℂ)‖₊ := by
    have hcont : Continuous (nnnormHom.toMonoidHom : ℂ → ℝ≥0) := by
      change Continuous fun z : ℂ => ‖z‖₊
      exact (continuous_nnnorm : Continuous fun z : ℂ => ‖z‖₊)
    have hmap := hz.map nnnormHom.toMonoidHom hcont
    change HasProd (fun p : Nat.Primes => ‖complexZetaFactor s p‖₊)
      ‖riemannZeta (s : ℂ)‖₊ at hmap
    simpa only [f] using hmap
  have hnn : HasProd (fun n : ℕ => if n.Prime then f n else 1)
      ‖riemannZeta (s : ℂ)‖₊ :=
    (Nat.Primes.hasProd_iff_hasProd_ite f).mp hnnPrime
  have hle : (∏ p ∈ N.primesBelow, f p) ≤ ‖riemannZeta (s : ℂ)‖₊ := by
    calc
      (∏ p ∈ N.primesBelow, f p) =
          ∏ p ∈ N.primesBelow, if p.Prime then f p else 1 := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [if_pos (Nat.prime_of_mem_primesBelow hp)]
      _ ≤ ‖riemannZeta (s : ℂ)‖₊ := by
        apply prod_le_hasProd _ _ hnn
        intro p _hp
        by_cases hp : p.Prime
        · rw [if_pos hp]
          change (1 : ℝ) ≤ ‖complexZetaFactor s p‖
          rw [norm_complexZetaFactor s p,
            abs_of_pos (realZetaFactor_pos (le_of_lt hs) hp)]
          exact realZetaFactor_one_le (le_of_lt hs) hp
        · simp [hp]
  have hle' : ((↑(∏ p ∈ N.primesBelow, f p) : ℝ) ≤
      (↑‖riemannZeta (s : ℂ)‖₊ : ℝ)) := NNReal.coe_le_coe.mpr hle
  have hnormProd : (∏ p ∈ N.primesBelow, ‖complexZetaFactor s p‖) ≤
      ‖riemannZeta (s : ℂ)‖ := by
    simpa only [f, NNReal.coe_prod, coe_nnnorm] using hle'
  calc
    (∏ p ∈ N.primesBelow, realZetaFactor s p) =
        ∏ p ∈ N.primesBelow, ‖complexZetaFactor s p‖ := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [norm_complexZetaFactor s p,
        abs_of_pos (realZetaFactor_pos (le_of_lt hs)
          (Nat.prime_of_mem_primesBelow hp))]
    _ ≤ ‖riemannZeta (s : ℂ)‖ := hnormProd

noncomputable def badFactor (p : ℕ) : ℝ :=
  if p % 4 = 3 then (1 - ((p : ℝ)⁻¹) ^ 2)⁻¹ else 1

lemma badFactor_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ badFactor p := by
  unfold badFactor
  by_cases hmod : p % 4 = 3
  · rw [if_pos hmod]
    have ha := prime_rpow_neg_pos_le_half (s := 1) (by norm_num) hp
    have hprod : 0 ≤ (p : ℝ) ^ (-(1 : ℝ)) *
        (1 / 2 - (p : ℝ) ^ (-(1 : ℝ))) :=
      mul_nonneg ha.1.le (sub_nonneg.mpr ha.2)
    rw [show ((p : ℝ)⁻¹) = (p : ℝ) ^ (-(1 : ℝ)) by
      rw [Real.rpow_neg_one]]
    exact inv_nonneg.mpr (by nlinarith)
  · simp [hmod]

lemma badFactor_le_realZetaFactor_two {p : ℕ} (hp : p.Prime) :
    badFactor p ≤ realZetaFactor 2 p := by
  unfold badFactor
  by_cases hmod : p % 4 = 3
  · rw [if_pos hmod]
    unfold realZetaFactor
    rw [show ((p : ℝ) ^ (-(2 : ℝ))) = ((p : ℝ)⁻¹) ^ 2 by
      rw [Real.rpow_neg (by positivity), Real.rpow_two, inv_pow]]
  · rw [if_neg hmod]
    exact realZetaFactor_one_le (by norm_num) hp

lemma sumTwoSquares_eulerFactor_eq_bad_mul_good {p : ℕ} (hp : p.Prime) :
    (∑' j : ℕ,
        sumTwoSquaresWeight (p ^ j) / ((p ^ j : ℕ) : ℝ)) =
      badFactor p * goodFactor 1 p := by
  rw [sumTwoSquares_eulerFactor p hp]
  unfold badFactor goodFactor realZetaFactor
  by_cases hmod : p % 4 = 3
  · simp [hmod]
  · simp [hmod, Real.rpow_neg_one]

lemma badFactor_prod_le_two (N : ℕ) :
    (∏ p ∈ (N + 1).primesBelow, badFactor p) ≤ 2 := by
  calc
    (∏ p ∈ (N + 1).primesBelow, badFactor p) ≤
        ∏ p ∈ (N + 1).primesBelow, realZetaFactor 2 p := by
      exact Finset.prod_le_prod
        (fun p hp => by
          have hpPrime := Nat.prime_of_mem_primesBelow hp
          unfold badFactor
          split_ifs with hmod
          · have ha := prime_rpow_neg_pos_le_half
                (s := 1) (by norm_num) hpPrime
            have hprod : 0 ≤ (p : ℝ) ^ (-(1 : ℝ)) *
                (1 / 2 - (p : ℝ) ^ (-(1 : ℝ))) :=
              mul_nonneg ha.1.le (sub_nonneg.mpr ha.2)
            rw [show ((p : ℝ)⁻¹) = (p : ℝ) ^ (-(1 : ℝ)) by
              rw [Real.rpow_neg_one]]
            exact inv_nonneg.mpr (by nlinarith)
          · norm_num)
        (fun p hp => badFactor_le_realZetaFactor_two
          (Nat.prime_of_mem_primesBelow hp))
    _ ≤ ‖riemannZeta ((2 : ℝ) : ℂ)‖ :=
      realZetaFactor_prod_le_zeta (by norm_num) (N + 1)
    _ ≤ 2 := by
      convert norm_riemannZeta_real_le (s := (2 : ℝ)) (by norm_num) using 1;
        norm_num [div_eq_mul_inv]

lemma exists_sumTwoSquares_eulerProduct_le_sqrt_log :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      (∏ p ∈ (N + 1).primesBelow,
          ∑' j : ℕ,
            sumTwoSquaresWeight (p ^ j) / ((p ^ j : ℕ) : ℝ)) ≤
        C * Real.sqrt (Real.log (N : ℝ)) := by
  obtain ⟨C, hCpos, hC⟩ := exists_goodFactor_one_prod_le_sqrt_log
  refine ⟨2 * C, mul_pos (by norm_num) hCpos, ?_⟩
  intro N hN
  have hbad0 : 0 ≤ ∏ p ∈ (N + 1).primesBelow, badFactor p :=
    Finset.prod_nonneg fun p hp =>
      badFactor_nonneg (Nat.prime_of_mem_primesBelow hp)
  have hgood0 : 0 ≤ ∏ p ∈ (N + 1).primesBelow, goodFactor 1 p :=
    Finset.prod_nonneg fun p hp =>
      (goodFactor_one_le (by norm_num)
        (Nat.prime_of_mem_primesBelow hp)).trans' zero_le_one
  calc
    (∏ p ∈ (N + 1).primesBelow,
        ∑' j : ℕ,
          sumTwoSquaresWeight (p ^ j) / ((p ^ j : ℕ) : ℝ)) =
        (∏ p ∈ (N + 1).primesBelow, badFactor p) *
          ∏ p ∈ (N + 1).primesBelow, goodFactor 1 p := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      exact sumTwoSquares_eulerFactor_eq_bad_mul_good
        (Nat.prime_of_mem_primesBelow hp)
    _ ≤ 2 * (C * Real.sqrt (Real.log (N : ℝ))) :=
      mul_le_mul (badFactor_prod_le_two N) (hC N hN) hgood0 (by norm_num)
    _ = (2 * C) * Real.sqrt (Real.log (N : ℝ)) := by ring

lemma sumTwoSquaresWeight_sum_eq_card (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, sumTwoSquaresWeight n) =
      (((Finset.Icc 1 N).filter IsSumTwoSquares).card : ℝ) := by
  rw [Finset.cast_card, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : n ≠ 0 := by omega
  by_cases hrep : IsSumTwoSquares n <;>
    simp [sumTwoSquaresWeight, hn0, hrep]

lemma exists_sumTwoSquares_count_le :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      (((Finset.Icc 1 N).filter IsSumTwoSquares).card : ℝ) ≤
        C * (N : ℝ) / Real.sqrt (Real.log (N : ℝ)) := by
  obtain ⟨C, hCpos, hC⟩ := exists_sumTwoSquares_eulerProduct_le_sqrt_log
  let H : ℝ := HalberstamScratch.explicitMassConstant 1 1 + 1
  refine ⟨H * C, mul_pos (by
    dsimp [H]
    have := HalberstamScratch.explicitMassConstant_nonneg
      (lambda1 := (1 : ℝ)) (lambda2 := (1 : ℝ)) (by norm_num) (by norm_num)
    linarith) hCpos, ?_⟩
  intro N hN
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsqrt : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.mpr hlog
  have hsqrtSq : (Real.sqrt (Real.log (N : ℝ))) ^ 2 = Real.log (N : ℝ) :=
    Real.sq_sqrt hlog.le
  rw [← sumTwoSquaresWeight_sum_eq_card]
  calc
    (∑ n ∈ Finset.Icc 1 N, sumTwoSquaresWeight n) ≤
        H * (N : ℝ) / Real.log (N : ℝ) *
          ∏ p ∈ (N + 1).primesBelow,
            ∑' j : ℕ,
              sumTwoSquaresWeight (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
      simpa [H] using sumTwoSquaresWeight_mean_le_euler N (by omega)
    _ ≤ H * (N : ℝ) / Real.log (N : ℝ) *
        (C * Real.sqrt (Real.log (N : ℝ))) := by
      exact mul_le_mul_of_nonneg_left (hC N hN) (by
        exact mul_nonneg (mul_nonneg (by
          dsimp [H]
          have := HalberstamScratch.explicitMassConstant_nonneg
            (lambda1 := (1 : ℝ)) (lambda2 := (1 : ℝ))
            (by norm_num) (by norm_num)
          linarith) (Nat.cast_nonneg N)) (inv_nonneg.mpr hlog.le))
    _ = (H * C) * (N : ℝ) / Real.sqrt (Real.log (N : ℝ)) := by
      field_simp [ne_of_gt hlog, ne_of_gt hsqrt]
      rw [hsqrtSq]

/-! ## From lattice distances to sums of two squares -/

noncomputable def squaredDistanceNat (d : ℝ) : ℕ :=
  Nat.floor (d ^ 2)

lemma squaredDistanceNat_dist_intPoint (x y : ℤ × ℤ) :
    squaredDistanceNat (dist (intPoint x) (intPoint y)) =
      (intSqDist x y).toNat := by
  unfold squaredDistanceNat
  rw [dist_intPoint_sq]
  have hnonneg := intSqDist_nonneg x y
  have hcast : (intSqDist x y : ℝ) =
      (((intSqDist x y).toNat : ℕ) : ℝ) := by
    norm_cast
    exact (Int.toNat_of_nonneg hnonneg).symm
  rw [hcast, Nat.floor_natCast]

lemma intSqDist_toNat_isSumTwoSquares (x y : ℤ × ℤ) :
    IsSumTwoSquares (intSqDist x y).toNat := by
  refine ⟨(x.1 - y.1).natAbs, (x.2 - y.2).natAbs, ?_⟩
  apply Nat.cast_injective (R := ℤ)
  rw [Int.toNat_of_nonneg (intSqDist_nonneg x y)]
  simp only [Nat.cast_add, Nat.cast_pow, Int.natCast_natAbs]
  simp [intSqDist, sq_abs]

lemma intSqDist_grid_pos {x y : ℤ × ℤ}
    (hxy : x ≠ y) :
    0 < intSqDist x y := by
  exact lt_of_le_of_ne (intSqDist_nonneg x y)
    (Ne.symm ((intSqDist_eq_zero_iff x y).not.mpr hxy))

lemma intSqDist_grid_le {N : ℕ} {x y : ℤ × ℤ}
    (hx : x ∈ intGrid N) (hy : y ∈ intGrid N) :
    intSqDist x y ≤ (2 : ℤ) * (N : ℤ) ^ 2 := by
  rw [mem_intGrid] at hx hy
  have h1lo : -(N : ℤ) ≤ x.1 - y.1 := by omega
  have h1hi : x.1 - y.1 ≤ (N : ℤ) := by omega
  have h2lo : -(N : ℤ) ≤ x.2 - y.2 := by omega
  have h2hi : x.2 - y.2 ≤ (N : ℤ) := by omega
  have hs1 : (x.1 - y.1) ^ 2 ≤ (N : ℤ) ^ 2 := sq_le_sq' h1lo h1hi
  have hs2 : (x.2 - y.2) ^ 2 ≤ (N : ℤ) ^ 2 := sq_le_sq' h2lo h2hi
  dsimp [intSqDist]
  linarith

lemma squaredDistanceNat_mem_sumTwoSquares {N : ℕ} {d : ℝ}
    (hd : d ∈ distinctDistances (planeGrid N)) :
    squaredDistanceNat d ∈
      (Finset.Icc 1 (2 * N ^ 2)).filter IsSumTwoSquares := by
  rcases Finset.mem_image.mp hd with ⟨e, he, rfl⟩
  rcases Finset.mem_offDiag.mp he with ⟨he1, he2, hne⟩
  rcases Finset.mem_image.mp he1 with ⟨x, hx, hxe⟩
  rcases Finset.mem_image.mp he2 with ⟨y, hy, hye⟩
  have hxy : x ≠ y := by
    intro h
    apply hne
    rw [← hxe, ← hye, h]
  have hpos := intSqDist_grid_pos hxy
  have hle := intSqDist_grid_le hx hy
  have htoPos : 1 ≤ (intSqDist x y).toNat := by
    have : 0 < (intSqDist x y).toNat := by
      rw [Int.lt_toNat]
      exact hpos
    omega
  have htoLe : (intSqDist x y).toNat ≤ 2 * N ^ 2 := by
    rw [Int.toNat_le]
    exact_mod_cast hle
  rw [← hxe, ← hye, squaredDistanceNat_dist_intPoint]
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨htoPos, htoLe⟩,
      intSqDist_toNat_isSumTwoSquares x y⟩

lemma squaredDistanceNat_cast_sq {N : ℕ} {d : ℝ}
    (hd : d ∈ distinctDistances (planeGrid N)) :
    (squaredDistanceNat d : ℝ) = d ^ 2 := by
  rcases Finset.mem_image.mp hd with ⟨e, he, rfl⟩
  rcases Finset.mem_offDiag.mp he with ⟨he1, he2, _hne⟩
  rcases Finset.mem_image.mp he1 with ⟨x, hx, hxe⟩
  rcases Finset.mem_image.mp he2 with ⟨y, hy, hye⟩
  rw [← hxe, ← hye, squaredDistanceNat_dist_intPoint,
    dist_intPoint_sq]
  norm_cast
  exact Int.toNat_of_nonneg (intSqDist_nonneg x y)

lemma squaredDistanceNat_injOn_grid_distances (N : ℕ) :
    Set.InjOn squaredDistanceNat (distinctDistances (planeGrid N) : Set ℝ) := by
  intro d₁ hd₁ d₂ hd₂ h
  have hcast := congrArg (fun n : ℕ => (n : ℝ)) h
  rw [squaredDistanceNat_cast_sq hd₁,
    squaredDistanceNat_cast_sq hd₂] at hcast
  have hd₁0 : 0 ≤ d₁ := by
    rcases Finset.mem_image.mp hd₁ with ⟨e, he, rfl⟩
    exact dist_nonneg
  have hd₂0 : 0 ≤ d₂ := by
    rcases Finset.mem_image.mp hd₂ with ⟨e, he, rfl⟩
    exact dist_nonneg
  exact (sq_eq_sq₀ hd₁0 hd₂0).mp hcast

lemma distanceCount_planeGrid_le_sumTwoSquares (N : ℕ) :
    distanceCount (planeGrid N) ≤
      ((Finset.Icc 1 (2 * N ^ 2)).filter IsSumTwoSquares).card := by
  unfold distanceCount
  exact Finset.card_le_card_of_injOn squaredDistanceNat
    (fun _ hd => squaredDistanceNat_mem_sumTwoSquares hd)
    (squaredDistanceNat_injOn_grid_distances N)

lemma exists_distanceCount_planeGrid_le :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      (distanceCount (planeGrid N) : ℝ) ≤
        C * (N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ)) := by
  obtain ⟨C, hCpos, hC⟩ := exists_sumTwoSquares_count_le
  refine ⟨2 * C, mul_pos (by norm_num) hCpos, ?_⟩
  intro N hN
  let M : ℕ := 2 * N ^ 2
  have hM : 3 ≤ M := by
    dsimp [M]
    nlinarith
  have hcountNat := distanceCount_planeGrid_le_sumTwoSquares N
  have hcount : (distanceCount (planeGrid N) : ℝ) ≤
      (((Finset.Icc 1 M).filter IsSumTwoSquares).card : ℝ) := by
    exact_mod_cast hcountNat
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hNM : (N : ℝ) ≤ M := by
    exact_mod_cast (show N ≤ M by
      dsimp [M]
      nlinarith)
  have hlogle : Real.log (N : ℝ) ≤ Real.log (M : ℝ) :=
    Real.log_le_log hNpos hNM
  have hsqrtle : Real.sqrt (Real.log (N : ℝ)) ≤
      Real.sqrt (Real.log (M : ℝ)) := Real.sqrt_le_sqrt hlogle
  have hsqrtN : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.mpr hlogN
  have hMcast : (M : ℝ) = 2 * (N : ℝ) ^ 2 := by
    dsimp [M]
    norm_num [Nat.cast_mul, Nat.cast_pow]
  calc
    (distanceCount (planeGrid N) : ℝ) ≤
        (((Finset.Icc 1 M).filter IsSumTwoSquares).card : ℝ) := hcount
    _ ≤ C * (M : ℝ) / Real.sqrt (Real.log (M : ℝ)) := hC M hM
    _ ≤ C * (M : ℝ) / Real.sqrt (Real.log (N : ℝ)) := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg hCpos.le (Nat.cast_nonneg M)) hsqrtN hsqrtle
    _ = (2 * C) * (N : ℝ) ^ 2 /
        Real.sqrt (Real.log (N : ℝ)) := by
      rw [hMcast]
      ring

/-! ## Exact-size construction and the public counterexample -/

lemma exists_phi45_subset_of_card {K : ℕ}
    (hbad : ∀ N : ℕ,
      (otherBadIntQuads (intGrid N)).card ≤ K * N ^ 5)
    (n : ℕ) :
    ∃ A : Finset Plane,
      A.card = n ∧ HasPhi45 A ∧
        A ⊆ planeGrid (128 * (K + 1) * n) := by
  classical
  by_cases hn : n = 0
  · subst n
    refine ⟨∅, by simp, HasPhi45.of_card_lt_four (by simp), ?_⟩
    simp
  · let D : ℕ := 128 * (K + 1)
    let N : ℕ := D * n
    have hD : 0 < D := by
      dsimp [D]
      omega
    have hN : 1 ≤ N := by
      dsimp [N]
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hD.ne' hn)
    obtain ⟨S, hSgrid, hScard, hSphi⟩ :=
      exists_grid_subset_of_bad_bound hN (hbad N)
    have hnS : n ≤ S.card := by
      have hdiv : N / D = n := by
        dsimp [N]
        rw [Nat.mul_comm]
        exact Nat.mul_div_left n hD
      have hden : 128 * (K + 1) = D := by rfl
      rw [hden, hdiv] at hScard
      exact hScard
    obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hnS
    refine ⟨T.image intPoint, ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ intPoint_injective, hTcard]
    · exact hSphi.mono (Finset.image_subset_image hTS)
    · have hTgrid : T ⊆ intGrid N := hTS.trans hSgrid
      have himage : T.image intPoint ⊆ planeGrid N := by
        simpa [planeGrid] using Finset.image_subset_image hTgrid
      simpa [N, D, Nat.mul_assoc] using himage

/-- Tao's negative resolution of Erdős Problem 135: there are arbitrarily
large `Φ(4,5)` point sets whose number of distances is
`O(n² / sqrt(log n))`. -/
theorem not_erdos_135 :
    ∃ A : ℕ → Finset Plane,
      (∀ n : ℕ, (A n).card = n ∧ HasPhi45 (A n)) ∧
      (fun n : ℕ => (distanceCount (A n) : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ) ^ 2 /
          Real.sqrt (Real.log (n : ℝ))) := by
  obtain ⟨K, hK⟩ := exists_otherBadIntQuads_grid_bound
  let D : ℕ := 128 * (K + 1)
  have hD : 1 ≤ D := by
    dsimp [D]
    omega
  have hsets : ∀ n : ℕ, ∃ A : Finset Plane,
      A.card = n ∧ HasPhi45 A ∧ A ⊆ planeGrid (D * n) := by
    intro n
    simpa [D, Nat.mul_assoc] using exists_phi45_subset_of_card hK n
  let A : ℕ → Finset Plane := fun n => Classical.choose (hsets n)
  have hA (n : ℕ) :
      (A n).card = n ∧ HasPhi45 (A n) ∧ A n ⊆ planeGrid (D * n) :=
    Classical.choose_spec (hsets n)
  refine ⟨A, fun n => ⟨(hA n).1, (hA n).2.1⟩, ?_⟩
  obtain ⟨C, hCpos, hgrid⟩ := exists_distanceCount_planeGrid_le
  rw [Asymptotics.isBigO_iff]
  refine ⟨C * (D : ℝ) ^ 2, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 3] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hside : 3 ≤ D * n := by nlinarith
  have hspos : (0 : ℝ) < D * n := by exact_mod_cast (show 0 < D * n by omega)
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogs : 0 < Real.log ((D * n : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < D * n by omega))
  have hnside : (n : ℝ) ≤ (D * n : ℕ) := by
    exact_mod_cast (show n ≤ D * n by nlinarith)
  have hlogle : Real.log (n : ℝ) ≤ Real.log ((D * n : ℕ) : ℝ) :=
    Real.log_le_log hnpos hnside
  have hsqrtle : Real.sqrt (Real.log (n : ℝ)) ≤
      Real.sqrt (Real.log ((D * n : ℕ) : ℝ)) := Real.sqrt_le_sqrt hlogle
  have hsqrtn : 0 < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.mpr hlogn
  have hmono : (distanceCount (A n) : ℝ) ≤
      distanceCount (planeGrid (D * n)) := by
    exact_mod_cast distanceCount_mono (hA n).2.2
  rw [Real.norm_of_nonneg (Nat.cast_nonneg (distanceCount (A n))),
    Real.norm_of_nonneg (div_nonneg (sq_nonneg _)
      (Real.sqrt_nonneg _))]
  calc
    (distanceCount (A n) : ℝ) ≤
        (distanceCount (planeGrid (D * n)) : ℝ) := hmono
    _ ≤ C * ((D * n : ℕ) : ℝ) ^ 2 /
        Real.sqrt (Real.log ((D * n : ℕ) : ℝ)) := hgrid (D * n) hside
    _ ≤ C * ((D * n : ℕ) : ℝ) ^ 2 /
        Real.sqrt (Real.log (n : ℝ)) := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg hCpos.le (sq_nonneg _)) hsqrtn hsqrtle
    _ = (C * (D : ℝ) ^ 2) * ((n : ℝ) ^ 2 /
        Real.sqrt (Real.log (n : ℝ))) := by
      norm_num [Nat.cast_mul]
      ring

#print axioms not_erdos_135

end Erdos135

alias _root_.Erdos135.erdos_135 := _root_.Erdos135.not_erdos_135
