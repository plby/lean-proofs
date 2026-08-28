import Wikipedia.NoExoticSixSphere.CollaredDiskFrameCoordinates

/-!
# The actual collar derivative in radial source coordinates

Tangential columns are prescribed by the boundary sphere. The radial
column may have a spatial part and any nonzero height coefficient.
Together with the original normal columns this remains injective.
These formulas permit a collar homotopy without discarding its sign.
-/

noncomputable section

open Function

namespace NoExoticSixSphere.CollaredDiskFrame

open GLOrthonormalization SphereThreeTangentFrame

variable {N k : ℕ}

def radialColumn (v : Vector N) (c : ℝ) : Vector 1 →L[ℝ] (Vector N × ℝ) :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (v, c)).comp
    EuclideanTailCoordinates.scalar.symm.toContinuousLinearMap

def collarDerivative (s : Sphere 3) (T : Vector 3 →L[ℝ] Vector N)
    (v : Vector N) (c : ℝ) : Vector 4 →L[ℝ] (Vector N × ℝ) :=
  (((ContinuousLinearMap.inl ℝ (Vector N) ℝ).comp T).coprod (radialColumn v c)).comp
    ((EuclideanSpace.finAddEquivProd (n := 3) (m := 1)).toContinuousLinearMap.comp
      (radialCoordinates s).symm.toContinuousLinearMap)

theorem collarDerivative_apply (s : Sphere 3) (T : Vector 3 →L[ℝ] Vector N)
    (v : Vector N) (c : ℝ) (z : Vector 4) :
    collarDerivative s T v c z =
      (T (EuclideanSpace.finAddEquivProd (n := 3) (m := 1)
          ((radialCoordinates s).symm z)).1 +
        EuclideanTailCoordinates.scalar.symm
          (EuclideanSpace.finAddEquivProd (n := 3) (m := 1)
            ((radialCoordinates s).symm z)).2 • v,
        EuclideanTailCoordinates.scalar.symm
          (EuclideanSpace.finAddEquivProd (n := 3) (m := 1)
            ((radialCoordinates s).symm z)).2 * c) := by
  simp only [collarDerivative, radialColumn, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coprod_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
    Prod.smul_mk, Prod.mk_add_mk, zero_add, smul_eq_mul]
  rfl

theorem collarDerivative_radialCoordinates (s : Sphere 3) (T : Vector 3 →L[ℝ] Vector N)
    (v : Vector N) (c : ℝ) (z : Vector 4) :
    collarDerivative s T v c (radialCoordinates s z) =
      (T (EuclideanSpace.finAddEquivProd (n := 3) (m := 1) z).1 +
        EuclideanTailCoordinates.scalar.symm
          (EuclideanSpace.finAddEquivProd (n := 3) (m := 1) z).2 • v,
        EuclideanTailCoordinates.scalar.symm
          (EuclideanSpace.finAddEquivProd (n := 3) (m := 1) z).2 * c) := by
  rw [collarDerivative_apply, ContinuousLinearEquiv.symm_apply_apply]

theorem eq_collarDerivative_of_tangent_radial (s : Sphere 3)
    (T : Vector 3 →L[ℝ] Vector N) (D : Vector 4 →L[ℝ] (Vector N × ℝ))
    (v : Vector N) (c : ℝ)
    (hT : ∀ u, D (operator s.val u) = (T u, 0)) (hr : D s.val = (v, c)) :
    D = collarDerivative s T v c := by
  apply ContinuousLinearMap.ext
  intro z
  obtain ⟨w, rfl⟩ := (radialCoordinates s).surjective z
  rw [collarDerivative_radialCoordinates, radialCoordinates_apply, map_add, map_smul, hT, hr]
  simp only [Prod.smul_mk, Prod.mk_add_mk, zero_add, smul_eq_mul]

theorem collar_coprod_injective (s : Sphere 3) (a : Vector k →L[ℝ] Vector N)
    (T : Vector 3 →L[ℝ] Vector N) (v : Vector N) (c : ℝ)
    (ha : Injective a) (hT : Injective T) (hr : Disjoint a.range T.range) (hc : c ≠ 0) :
    Injective (((ContinuousLinearMap.inl ℝ (Vector N) ℝ).comp a).coprod
      (collarDerivative s T v c)) := by
  have haT : Injective (a.toLinearMap.coprod T.toLinearMap) := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_coprod_of_disjoint_range _ _ hr,
      LinearMap.ker_eq_bot.mpr ha, LinearMap.ker_eq_bot.mpr hT, Submodule.prod_bot]
  apply (injective_iff_map_eq_zero _).mpr
  rintro ⟨u, z⟩ h
  let w := EuclideanSpace.finAddEquivProd (n := 3) (m := 1) ((radialCoordinates s).symm z)
  have he : (a u + T w.1 + EuclideanTailCoordinates.scalar.symm w.2 • v,
      EuclideanTailCoordinates.scalar.symm w.2 * c) = (0, 0) := by
    change (a u, 0) + collarDerivative s T v c z = 0 at h
    rw [collarDerivative_apply] at h
    simpa only [w, Prod.mk_add_mk, Prod.zero_eq_mk, zero_add, add_assoc] using h
  have hz : EuclideanTailCoordinates.scalar.symm w.2 = 0 :=
    (mul_eq_zero.mp (congrArg Prod.snd he)).resolve_right hc
  have hsum : a u + T w.1 = 0 := by
    have hh := congrArg Prod.fst he
    change a u + T w.1 + EuclideanTailCoordinates.scalar.symm w.2 • v = 0 at hh
    simpa only [hz, zero_smul, add_zero] using hh
  have hu : (u, w.1) = (0, 0) := haT (hsum.trans (map_zero _).symm)
  have hw₂ : w.2 = 0 :=
    EuclideanTailCoordinates.scalar.symm.injective (hz.trans (map_zero _).symm)
  have hw : w = 0 := Prod.ext (congrArg Prod.snd hu) hw₂
  have hzz : z = 0 := by
    apply (radialCoordinates s).symm.injective
    apply (EuclideanSpace.finAddEquivProd (n := 3) (m := 1)).injective
    simpa only [map_zero] using hw
  have hu0 : u = 0 := congrArg (fun p : Vector k × Vector 3 ↦ p.1) hu
  exact Prod.ext hu0 hzz

theorem continuous_collarDerivative {X : Type*} [TopologicalSpace X]
    (s : X → Sphere 3) (T : X → Vector 3 →L[ℝ] Vector N)
    (v : X → Vector N) (c : X → ℝ)
    (hs : Continuous s) (hT : Continuous T) (hv : Continuous v) (hc : Continuous c) :
    Continuous (fun x ↦ collarDerivative (s x) (T x) (v x) (c x)) := by
  apply continuous_clm_apply.mpr
  intro z
  simp only [collarDerivative_apply]
  have hw : Continuous (fun x ↦ EuclideanSpace.finAddEquivProd (n := 3) (m := 1)
      ((radialCoordinates (s x)).symm z)) :=
    EuclideanSpace.finAddEquivProd.continuous.comp
      ((continuous_inverse_radialCoordinates.comp hs).clm_apply continuous_const)
  have hr : Continuous (fun x ↦ EuclideanTailCoordinates.scalar.symm
      (EuclideanSpace.finAddEquivProd (n := 3) (m := 1)
        ((radialCoordinates (s x)).symm z)).2) :=
    EuclideanTailCoordinates.scalar.symm.continuous.comp hw.snd
  exact ((hT.clm_apply hw.fst).add (hr.smul hv)).prodMk (hr.mul hc)

end NoExoticSixSphere.CollaredDiskFrame
