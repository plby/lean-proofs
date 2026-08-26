/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Translation of homogeneous polynomial coordinates in the affine plane.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.RationalConic

namespace Erdos477.Geometry

open Polynomial

variable {K : Type*} [Field K]

noncomputable def homogeneousPlaneTranslate (b : Fin 2 → K) (f : Fin 3 → K[X]) :
    Fin 3 → K[X] := ![f 0 + C (b 0) * f 2, f 1 + C (b 1) * f 2, f 2]

lemma degree_homogeneousPlaneTranslate (b : Fin 2 → K) (f : Fin 3 → K[X]) (D : ℕ)
    (hf : ∀ i, (f i).natDegree ≤ D) : ∀ i, (homogeneousPlaneTranslate b f i).natDegree ≤ D := by
  intro i
  fin_cases i
  · exact (natDegree_add_le _ _).trans (max_le (hf 0) ((natDegree_C_mul_le _ _).trans (hf 2)))
  · exact (natDegree_add_le _ _).trans (max_le (hf 1) ((natDegree_C_mul_le _ _).trans (hf 2)))
  · exact hf 2

lemma homogeneousPlaneTranslate_inverse (b : Fin 2 → K) (f : Fin 3 → K[X]) :
    homogeneousPlaneTranslate (-b) (homogeneousPlaneTranslate b f) = f := by
  funext i
  fin_cases i
  · change (f 0 + C (b 0) * f 2) + C (-(b 0)) * f 2 = f 0
    rw [map_neg]
    ring
  · change (f 1 + C (b 1) * f 2) + C (-(b 1)) * f 2 = f 1
    rw [map_neg]
    ring
  · rfl

lemma homogeneousPlaneTranslate_no_common_root (b : Fin 2 → K) (f : Fin 3 → K[X])
    (hf : ∀ z : K, ¬ ∀ i, (f i).eval z = 0) :
    ∀ z : K, ¬ ∀ i, (homogeneousPlaneTranslate b f i).eval z = 0 := by
  intro z hz
  have h2 : (f 2).eval z = 0 := hz 2
  apply hf z
  intro i
  fin_cases i
  · change (f 0).eval z = 0
    have h := hz 0
    change (f 0 + C (b 0) * f 2).eval z = 0 at h
    simpa only [eval_add, eval_mul, h2, mul_zero, add_zero] using h
  · change (f 1).eval z = 0
    have h := hz 1
    change (f 1 + C (b 1) * f 2).eval z = 0 at h
    simpa only [eval_add, eval_mul, h2, mul_zero, add_zero] using h
  · exact h2

lemma homogeneousPlaneTranslate_has_degree_two (b : Fin 2 → K) (f : Fin 3 → K[X])
    (hf : ∀ i, (f i).natDegree ≤ 2) (htwo : ∃ i, (f i).natDegree = 2) :
    ∃ i, (homogeneousPlaneTranslate b f i).natDegree = 2 := by
  by_contra! h
  have hlinear (i) : (homogeneousPlaneTranslate b f i).natDegree ≤ 1 := by
    have hbound := degree_homogeneousPlaneTranslate b f 2 hf i
    have hne := h i
    omega
  have hinverse := degree_homogeneousPlaneTranslate (-b) (homogeneousPlaneTranslate b f) 1 hlinear
  rw [homogeneousPlaneTranslate_inverse] at hinverse
  obtain ⟨i, hi⟩ := htwo
  have hbound := hinverse i
  omega

noncomputable def rationalPlaneCoordinates (f : Fin 3 → K[X]) : Fin 2 → RatFunc K :=
  ![algebraMap K[X] (RatFunc K) (f 0) / algebraMap K[X] (RatFunc K) (f 2),
    algebraMap K[X] (RatFunc K) (f 1) / algebraMap K[X] (RatFunc K) (f 2)]

lemma rationalPlaneCoordinates_translate (b : Fin 2 → K) (f : Fin 3 → K[X]) (hW : f 2 ≠ 0) :
    rationalPlaneCoordinates (homogeneousPlaneTranslate b f) =
      fun i => rationalPlaneCoordinates f i + RatFunc.C (b i) := by
  have hden : algebraMap K[X] (RatFunc K) (f 2) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hW
  ext i
  fin_cases i
  · change algebraMap K[X] (RatFunc K) (f 0 + C (b 0) * f 2) /
        algebraMap K[X] (RatFunc K) (f 2) =
      algebraMap K[X] (RatFunc K) (f 0) / algebraMap K[X] (RatFunc K) (f 2) + RatFunc.C (b 0)
    simp only [map_add, map_mul, RatFunc.algebraMap_C, add_div, mul_div_cancel_right₀ _ hden]
  · change algebraMap K[X] (RatFunc K) (f 1 + C (b 1) * f 2) /
        algebraMap K[X] (RatFunc K) (f 2) =
      algebraMap K[X] (RatFunc K) (f 1) / algebraMap K[X] (RatFunc K) (f 2) + RatFunc.C (b 1)
    simp only [map_add, map_mul, RatFunc.algebraMap_C, add_div, mul_div_cancel_right₀ _ hden]

lemma eval₂_homogeneousPlaneTranslate (b : Fin 2 → K) (f : Fin 3 → K[X]) (hW : f 2 ≠ 0)
    (P : MvPolynomial (Fin 2) K) :
    MvPolynomial.eval₂Hom RatFunc.C (rationalPlaneCoordinates (homogeneousPlaneTranslate b f)) P =
      MvPolynomial.eval₂Hom RatFunc.C (rationalPlaneCoordinates f) (planeTranslate b P) := by
  rw [rationalPlaneCoordinates_translate b f hW, eval₂_planeTranslate]

#print axioms eval₂_homogeneousPlaneTranslate
-- 'Erdos477.Geometry.eval₂_homogeneousPlaneTranslate' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
