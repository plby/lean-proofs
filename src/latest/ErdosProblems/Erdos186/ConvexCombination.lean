/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.ConvexGeometry
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Capped convex combinations

This file proves the finite-dimensional separation lemma used in the proof of
Pham--Zakharov's Theorem 4.  If a finite set is not in `mu`-convex position,
then one of its points is the barycenter of a probability distribution on the
set in which no atom has mass greater than `(mu * |A|)⁻¹`.

The proof separates zero from the image of a capped standard simplex.  The
separating functional would expose a closed half-space through the chosen
point containing at most `mu * |A|` points, contradicting the choice of that
point.
-/

open scoped BigOperators
open Set

namespace Erdos186
namespace ConvexCombination

set_option autoImplicit false

/-- The standard simplex with an additional common upper bound on all its
coordinates. -/
def cappedSimplex (cap : ℝ) (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  stdSimplex ℝ ι ∩ {c | ∀ i, c i ≤ cap}

@[simp] theorem mem_cappedSimplex {cap : ℝ} {ι : Type*} [Fintype ι]
    {c : ι → ℝ} :
    c ∈ cappedSimplex cap ι ↔
      (∀ i, 0 ≤ c i) ∧ (∑ i, c i) = 1 ∧ ∀ i, c i ≤ cap := by
  simp [cappedSimplex, stdSimplex, and_assoc]

theorem convex_cappedSimplex (cap : ℝ) (ι : Type*) [Fintype ι] :
    Convex ℝ (cappedSimplex cap ι) := by
  rw [cappedSimplex]
  refine (convex_stdSimplex ℝ ι).inter ?_
  intro c hc d hd u v hu hv huv i
  dsimp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply] at hc hd ⊢
  calc
    u * c i + v * d i ≤ u * cap + v * cap :=
      add_le_add (mul_le_mul_of_nonneg_left (hc i) hu)
        (mul_le_mul_of_nonneg_left (hd i) hv)
    _ = cap := by rw [← add_mul, huv, one_mul]

theorem isClosed_coordinateCap (cap : ℝ) (ι : Type*) :
    IsClosed {c : ι → ℝ | ∀ i, c i ≤ cap} := by
  simp only [ofPred_forall]
  exact isClosed_iInter fun i ↦ isClosed_le (continuous_apply i) continuous_const

theorem isCompact_cappedSimplex (cap : ℝ) (ι : Type*) [Fintype ι] :
    IsCompact (cappedSimplex cap ι) := by
  rw [cappedSimplex]
  exact (isCompact_stdSimplex ℝ ι).inter_right (isClosed_coordinateCap cap ι)

/-- The linear map which sends weights to the corresponding weighted sum of
the vectors centered at `a`. -/
noncomputable def centeredMap {d : ℕ}
    (A : Finset (EuclideanSpace ℝ (Fin d))) (a : A) :
    (A → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
  ∑ x : A, (LinearMap.proj x).smulRight ((x : EuclideanSpace ℝ (Fin d)) - a)

@[simp] theorem centeredMap_apply {d : ℕ}
    (A : Finset (EuclideanSpace ℝ (Fin d))) (a : A) (c : A → ℝ) :
    centeredMap A a c =
      ∑ x : A, c x • ((x : EuclideanSpace ℝ (Fin d)) - a) := by
  classical
  simp [centeredMap]

theorem continuous_centeredMap {d : ℕ}
    (A : Finset (EuclideanSpace ℝ (Fin d))) (a : A) :
    Continuous (centeredMap A a) := by
  exact (centeredMap A a).continuous_of_finiteDimensional

/-- If `S` has more than `q` elements and `q > 0`, its uniform probability
measure has every atom at most `q⁻¹`.  It is extended by zero to the ambient
finite type. -/
private theorem uniform_mem_cappedSimplex
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) {q : ℝ} (hq : 0 < q) (hcard : q < S.card) :
    (fun i ↦ if i ∈ S then (S.card : ℝ)⁻¹ else 0) ∈
      cappedSimplex q⁻¹ ι := by
  rw [mem_cappedSimplex]
  have hScard : 0 < S.card := by
    exact_mod_cast hq.trans hcard
  have hScardR : (0 : ℝ) < S.card := by exact_mod_cast hScard
  refine ⟨?_, ?_, ?_⟩
  · intro i
    split_ifs
    · exact inv_nonneg.mpr hScardR.le
    · exact le_rfl
  · simp [hScard.ne']
  · intro i
    split_ifs
    · exact (inv_le_inv₀ hScardR hq).2 hcard.le
    · exact inv_nonneg.mpr hq.le

/--
**Capped convex-combination lemma (Pham--Zakharov, Theorem 4 separation
step).**  Failure of `mu`-convex position supplies a point of `A` which is a
convex combination of `A`, with each coefficient bounded by
`(mu * |A|)⁻¹`.

The equality is written in centered form, exactly as it is used in the
zonotope argument.
-/
theorem exists_capped_centered_combination_of_not_isDeltaConvexPosition
    {d : ℕ} {A : Finset (EuclideanSpace ℝ (Fin d))} {mu : ℝ}
    (hmu : 0 < mu)
    (hfail : ¬ ConvexGeometry.IsDeltaConvexPosition mu A) :
    ∃ a : A, ∃ c : A → ℝ,
      (∀ x, 0 ≤ c x ∧ c x ≤ (mu * A.card)⁻¹) ∧
      (∑ x, c x) = 1 ∧
      (∑ x, c x • ((x : EuclideanSpace ℝ (Fin d)) - a)) = 0 := by
  classical
  rw [ConvexGeometry.IsDeltaConvexPosition] at hfail
  push Not at hfail
  obtain ⟨a, ha, hhalf⟩ := hfail
  let aA : A := ⟨a, ha⟩
  let q : ℝ := mu * A.card
  have hAcard : 0 < A.card := Finset.card_pos.mpr ⟨a, ha⟩
  have hq : 0 < q := mul_pos hmu (by exact_mod_cast hAcard)
  let D : Set (A → ℝ) := cappedSimplex q⁻¹ A
  let T : Set (EuclideanSpace ℝ (Fin d)) := centeredMap A aA '' D
  have hDconvex : Convex ℝ D := convex_cappedSimplex q⁻¹ A
  have hDcompact : IsCompact D := isCompact_cappedSimplex q⁻¹ A
  have hTconvex : Convex ℝ T := hDconvex.linear_image (centeredMap A aA)
  have hTcompact : IsCompact T :=
    hDcompact.image (continuous_centeredMap A aA)
  have hzero : (0 : EuclideanSpace ℝ (Fin d)) ∈ T := by
    by_contra hz
    obtain ⟨ell, u, hzero_u, hsep⟩ :=
      geometric_hahn_banach_point_closed hTconvex hTcompact.isClosed hz
    have hsep_pos : ∀ c ∈ D, 0 < ell (centeredMap A aA c) := by
      intro c hc
      have hs := hsep (centeredMap A aA c) ⟨c, hc, rfl⟩
      simpa using hzero_u.trans hs
    let S : Finset A := Finset.univ.filter fun x ↦ ell (x - aA) ≤ 0
    have hScard : q < S.card := by
      let negEll : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := -ell
      have hbad := hhalf negEll (negEll a) (le_rfl)
      rw [ConvexGeometry.halfspaceCount_eq_card_filter] at hbad
      have hbad' : q < (A.filter fun x ↦ ell x ≤ ell a).card := by
        simpa [q, negEll] using hbad
      have hcardEq :
          S.card = (A.filter fun x ↦ ell x ≤ ell a).card := by
        refine Finset.card_bij (s := S) (t := A.filter fun x ↦ ell x ≤ ell a)
          (fun x _ ↦ (x : EuclideanSpace ℝ (Fin d))) ?_ ?_ ?_
        · intro x hx
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx
          exact Finset.mem_filter.mpr ⟨x.property, by simpa [aA, sub_nonpos] using hx⟩
        · intro x hx y hy hxy
          exact Subtype.ext hxy
        · intro x hx
          refine ⟨⟨x, (Finset.mem_filter.mp hx).1⟩, ?_, rfl⟩
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          simpa [aA, sub_nonpos] using (Finset.mem_filter.mp hx).2
      simpa only [hcardEq] using hbad'
    let c : A → ℝ := fun x ↦ if x ∈ S then (S.card : ℝ)⁻¹ else 0
    have hcD : c ∈ D := uniform_mem_cappedSimplex S hq hScard
    have hnonpos : ell (centeredMap A aA c) ≤ 0 := by
      rw [centeredMap_apply, map_sum]
      apply Finset.sum_nonpos
      intro x hx
      rw [map_smul]
      by_cases hxS : x ∈ S
      · have hxell : ell (x - aA) ≤ 0 := by
          simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hxS
        rw [show c x = (S.card : ℝ)⁻¹ by simp [c, hxS]]
        exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (Nat.cast_nonneg _)) hxell
      · simp [c, hxS]
    exact (not_le_of_gt (hsep_pos c hcD)) hnonpos
  rcases hzero with ⟨c, hcD, hc⟩
  refine ⟨aA, c, ?_, ?_, ?_⟩
  · intro x
    have hmem := (mem_cappedSimplex.mp hcD)
    constructor
    · exact hmem.1 x
    · change c x ≤ q⁻¹
      exact hmem.2.2 x
  · exact (mem_cappedSimplex.mp hcD).2.1
  · simpa [centeredMap_apply] using hc

end ConvexCombination
end Erdos186
