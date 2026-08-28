import Wikipedia.HopfProblem.MappingTorusHomologyMaps
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleCrossArcChains

/-!
# Actual interval strips for the cyclic mapping-torus covering

The two strips in each turn lie in the genuine open members of the
mapping-torus cover. Their four endpoint maps are the literal lower and
upper intersection sections, with the fibre changed by the indicated
iterate of the monodromy. In particular the return strip ends at the
next lower section. This fixes both the twist and the connecting sign.
-/

noncomputable section

open Set ContinuousMap

namespace Wikipedia.HopfProblem.MappingTorusHomology.Covering

open MappingTorus MappingTorus.HomologyCover
open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

variable {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)

/-- The lower intersection section in the `k`-th turn. -/
def lowerSection (k : ℕ) : C(X, ↥(U f ∩ V f)) where
  toFun x := (intersectionHomeomorph f).symm
    (Sum.inl (⟨(1 / 4 : ℝ), by norm_num⟩, (f ^ k) x))
  continuous_toFun := (intersectionHomeomorph f).symm.continuous.comp
    (continuous_inl.comp (continuous_const.prodMk (f ^ k).continuous))

/-- The upper intersection section in the same turn. -/
def upperSection (k : ℕ) : C(X, ↥(U f ∩ V f)) where
  toFun x := (intersectionHomeomorph f).symm
    (Sum.inr (⟨(3 / 4 : ℝ), by norm_num⟩, (f ^ k) x))
  continuous_toFun := (intersectionHomeomorph f).symm.continuous.comp
    (continuous_inr.comp (continuous_const.prodMk (f ^ k).continuous))

@[simp] theorem lowerSection_val (k : ℕ) (x : X) :
    (lowerSection f k x : Torus f) = mk f (1 / 4, (f ^ k) x) :=
  intersectionHomeomorph_symm_inl_coe f _

@[simp] theorem upperSection_val (k : ℕ) (x : X) :
    (upperSection f k x : Torus f) = mk f (3 / 4, (f ^ k) x) :=
  intersectionHomeomorph_symm_inr_coe f _

/-- The first positive half-turn stays in the actual first chart. -/
def uTime (t : unitInterval) : Ioo (0 : ℝ) 1 :=
  ⟨(1 / 4 : ℝ) + (t : ℝ) / 2, by
    constructor <;> linarith [t.property.1, t.property.2]⟩

theorem uTime_continuous : Continuous uTime :=
  (continuous_const.add (continuous_subtype_val.div_const 2)).subtype_mk _

def vTime (t : unitInterval) : Ioo (-(1 / 2 : ℝ)) (1 / 2) :=
  ⟨-(1 / 4 : ℝ) + (t : ℝ) / 2, by
    constructor <;> linarith [t.property.1, t.property.2]⟩

theorem vTime_continuous : Continuous vTime :=
  (continuous_const.add (continuous_subtype_val.div_const 2)).subtype_mk _

def uStrip (k : ℕ) : C(unitInterval × X, U f) where
  toFun p := (chartU f).symm (uTime p.1, (f ^ k) p.2)
  continuous_toFun := (chartU f).symm.continuous.comp
    ((uTime_continuous.comp continuous_fst).prodMk
        ((f ^ k).continuous.comp continuous_snd))

/-- The return half-turn uses the second chart and the next fibre iterate. -/
def vStrip (k : ℕ) : C(unitInterval × X, V f) where
  toFun p := (chartV f).symm (vTime p.1, (f ^ (k + 1)) p.2)
  continuous_toFun := (chartV f).symm.continuous.comp
    ((vTime_continuous.comp continuous_fst).prodMk
        ((f ^ (k + 1)).continuous.comp continuous_snd))

@[simp] theorem uStrip_val (k : ℕ) (p : unitInterval × X) :
    (uStrip f k p : Torus f) = mk f ((1 / 4 : ℝ) + (p.1 : ℝ) / 2, (f ^ k) p.2) :=
  chartU_symm_coe f _

@[simp] theorem vStrip_val (k : ℕ) (p : unitInterval × X) :
    (vStrip f k p : Torus f) =
      mk f (-(1 / 4 : ℝ) + (p.1 : ℝ) / 2, (f ^ (k + 1)) p.2) :=
  chartV_symm_coe f _

theorem uStrip_zero (k : ℕ) : (uStrip f k).comp (crossInsertLeft (0 : unitInterval)) =
    (intersectionToU f).comp (lowerSection f k) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change (uStrip f k (0, x) : Torus f) = (lowerSection f k x : Torus f)
  rw [uStrip_val, lowerSection_val]
  simp

theorem uStrip_one (k : ℕ) : (uStrip f k).comp (crossInsertLeft (1 : unitInterval)) =
    (intersectionToU f).comp (upperSection f k) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change (uStrip f k (1, x) : Torus f) = (upperSection f k x : Torus f)
  rw [uStrip_val, upperSection_val]
  norm_num

theorem vStrip_zero (k : ℕ) : (vStrip f k).comp (crossInsertLeft (0 : unitInterval)) =
    (intersectionToV f).comp (upperSection f k) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change (vStrip f k (0, x) : Torus f) = (upperSection f k x : Torus f)
  rw [vStrip_val, upperSection_val]
  have hpow : (f ^ (k + 1)) x = f ((f ^ k) x) := by
    rw [pow_succ', Homeomorph.mul_apply]
  rw [hpow]
  convert mk_sub_one f (3 / 4) ((f ^ k) x) using 1
  norm_num

theorem vStrip_one (k : ℕ) : (vStrip f k).comp (crossInsertLeft (1 : unitInterval)) =
    (intersectionToV f).comp (lowerSection f (k + 1)) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change (vStrip f k (1, x) : Torus f) = (lowerSection f (k + 1) x : Torus f)
  rw [vStrip_val, lowerSection_val]
  norm_num

/-- The lower section returns literally, not only up to homotopy, after
the specified finite order. -/
theorem lowerSection_period (m : ℕ) (hf : f ^ m = 1) :
    lowerSection f m = lowerSection f 0 := by
  apply ContinuousMap.ext
  intro x
  change (intersectionHomeomorph f).symm (Sum.inl (_, (f ^ m) x)) =
    (intersectionHomeomorph f).symm (Sum.inl (_, (f ^ 0) x))
  rw [hf, pow_zero]

theorem lowerSection_component (k : ℕ) :
    (intersectionHomotopyEquiv f).toFun.comp (lowerSection f k) =
      (⟨Sum.inl, continuous_inl⟩ : C(X, X ⊕ X)).comp
        ((f ^ k : X ≃ₜ X) : C(X, X)) := by
  apply ContinuousMap.ext
  intro x
  exact intersectionHomotopyEquiv_inl f _

theorem upperSection_component (k : ℕ) :
    (intersectionHomotopyEquiv f).toFun.comp (upperSection f k) =
      (⟨Sum.inr, continuous_inr⟩ : C(X, X ⊕ X)).comp
        ((f ^ k : X ≃ₜ X) : C(X, X)) := by
  apply ContinuousMap.ext
  intro x
  exact intersectionHomotopyEquiv_inr f _

/-- The lower section contributes to the first intersection coordinate. -/
theorem lowerSection_homology_coordinates (k n : ℕ) (a : SingularHomology X n) :
    intersectionHomologyEquiv f n (singularHomologyMap (lowerSection f k) n a) =
      (singularHomologyMap ((f ^ k : X ≃ₜ X) : C(X, X)) n a, 0) := by
  rw [intersectionHomologyEquiv_apply, ← LinearMap.comp_apply,
    ← singularHomologyMap_comp, lowerSection_component, singularHomologyMap_comp]
  exact sumHomologyEquiv_inl X X n _

/-- The upper section contributes to the second intersection coordinate. -/
theorem upperSection_homology_coordinates (k n : ℕ) (a : SingularHomology X n) :
    intersectionHomologyEquiv f n (singularHomologyMap (upperSection f k) n a) =
      (0, singularHomologyMap ((f ^ k : X ≃ₜ X) : C(X, X)) n a) := by
  rw [intersectionHomologyEquiv_apply, ← LinearMap.comp_apply,
    ← singularHomologyMap_comp, upperSection_component, singularHomologyMap_comp]
  exact sumHomologyEquiv_inr X X n _

end Wikipedia.HopfProblem.MappingTorusHomology.Covering
