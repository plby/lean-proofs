import Wikipedia.NoExoticSixSphere.SmoothDiskNormalComplement

/-!
# The actual normal thickening map and its core derivative

The map is `D(x) + C(x)v` on four disk coordinates and any finite number of
transverse coordinates. Its derivative at `v = 0` is the actual disk derivative together
with `C(x)`. When `C` spans the complement of the partial normal frame and the
disk derivative, the original partial frame is exactly its full normal space
along the core. No ambient handle embedding or attaching-face agreement is
asserted in this file.
-/

noncomputable section

open Function
open scoped ContDiff

namespace NoExoticSixSphere.DiskThickening

open GLOrthonormalization Stiefel

variable {N k q : ℕ} (D : Vector 4 → Vector N) (C : Vector 4 → Vector q →L[ℝ] Vector N)

def map (p : Vector 4 × Vector q) : Vector N := D p.1 + C p.1 p.2

theorem map_core (x : Vector 4) : map D C (x, 0) = D x := by simp [map]

theorem contDiffAt_map (x : Vector 4) (v : Vector q)
    (hD : ContDiffAt ℝ ∞ D x) (hC : ContDiffAt ℝ ∞ C x) :
    ContDiffAt ℝ ∞ (map D C) (x, v) :=
  (hD.comp (x, v) contDiffAt_fst).add
    ((hC.comp (x, v) contDiffAt_fst).clm_apply contDiffAt_snd)

theorem fderiv_map_core (x : Vector 4)
    (hD : ContDiffAt ℝ ∞ D x) (hC : ContDiffAt ℝ ∞ C x) :
    fderiv ℝ (map D C) (x, 0) = (fderiv ℝ D x).coprod (C x) := by
  have hfst : HasFDerivAt (Prod.fst : Vector 4 × Vector q → Vector 4)
      (ContinuousLinearMap.fst ℝ _ _) (x, 0) := hasFDerivAt_fst
  have hsnd : HasFDerivAt (Prod.snd : Vector 4 × Vector q → Vector q)
      (ContinuousLinearMap.snd ℝ _ _) (x, 0) := hasFDerivAt_snd
  have hD' := (hD.differentiableAt (by simp)).hasFDerivAt.comp (x, (0 : Vector q)) hfst
  have hC' := (hC.differentiableAt (by simp)).hasFDerivAt.comp (x, (0 : Vector q)) hfst
  have h := hD'.add (hC'.clm_apply hsnd)
  have hh := h.fderiv
  change fderiv ℝ (map D C) (x, 0) = _ at hh
  rw [hh]
  apply ContinuousLinearMap.ext
  intro p
  change fderiv ℝ D x p.1 + (C x p.2 + fderiv ℝ C x p.1 0) =
    fderiv ℝ D x p.1 + C x p.2
  rw [map_zero, add_zero]

theorem injective_fderiv_map_core (x : Vector 4)
    (hD : ContDiffAt ℝ ∞ D x) (hC : ContDiffAt ℝ ∞ C x)
    (hiD : Injective (fderiv ℝ D x)) (hiC : Injective (C x))
    (hCr : (C x).range ≤ (fderiv ℝ D x).rangeᗮ) :
    Injective (fderiv ℝ (map D C) (x, 0)) := by
  rw [fderiv_map_core D C x hD hC]
  change Injective ((fderiv ℝ D x).toLinearMap.coprod (C x).toLinearMap)
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_coprod_of_disjoint_range _ _
    ((fderiv ℝ D x).range.orthogonal_disjoint.mono_right hCr),
    LinearMap.ker_eq_bot.mpr hiD, LinearMap.ker_eq_bot.mpr hiC, Submodule.prod_bot]

theorem normal_range_core (T : Vector 4 → Vector k →L[ℝ] Vector N) (x : Vector 4)
    (hD : ContDiffAt ℝ ∞ D x) (hC : ContDiffAt ℝ ∞ C x)
    (hiD : Injective (fderiv ℝ D x)) (hiT : Injective (T x)) (hiC : Injective (C x))
    (hTr : (T x).range ≤ (fderiv ℝ D x).rangeᗮ)
    (hCr : (C x).range = (OperatorSum.operator (T x) (fderiv ℝ D x)).rangeᗮ)
    (hN : k + 4 + q = N) :
    (T x).range = (fderiv ℝ (map D C) (x, 0)).rangeᗮ := by
  have hCr' : (C x).range = (T x).rangeᗮ ⊓ (fderiv ℝ D x).rangeᗮ := by
    rw [hCr, OperatorSum.range_operator, Submodule.inf_orthogonal]
  have hCD : (C x).range ≤ (fderiv ℝ D x).rangeᗮ := hCr'.le.trans inf_le_right
  have hCT : (C x).range ≤ (T x).rangeᗮ := hCr'.le.trans inf_le_left
  have hTC : (T x).range ≤ (C x).rangeᗮ :=
    (T x).range.le_orthogonal_orthogonal.trans (Submodule.orthogonal_le hCT)
  have hle : (T x).range ≤ (fderiv ℝ (map D C) (x, 0)).rangeᗮ := by
    rw [fderiv_map_core D C x hD hC]
    change (T x).range ≤ ((fderiv ℝ D x).toLinearMap.coprod (C x).toLinearMap).rangeᗮ
    rw [LinearMap.range_coprod, ← Submodule.inf_orthogonal]
    exact le_inf hTr hTC
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [LinearMap.finrank_range_of_inj hiT, finrank_euclideanSpace_fin]
  have hd := (fderiv ℝ (map D C) (x, 0)).range.finrank_add_finrank_orthogonal
  rw [LinearMap.finrank_range_of_inj (injective_fderiv_map_core D C x hD hC hiD hiC hCD),
    Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin,
    finrank_euclideanSpace_fin] at hd
  omega

end NoExoticSixSphere.DiskThickening
