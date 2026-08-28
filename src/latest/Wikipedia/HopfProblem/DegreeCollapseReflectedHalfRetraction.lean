import Wikipedia.HopfProblem.DegreeCollapseReflectedSeamDiffeomorph
import Wikipedia.HopfProblem.DegreeCollapsePointClassComponents

/-!
# The actual reflected double retracts onto its original nonnegative half

Absolute value in the time coordinate retains the reflected fiber. Its
restriction to the nonnegative half is literally the identity. Consequently
the original half inclusion is split injective on integral homology in
every degree; no Mayer--Vietoris injectivity premise is needed.
-/

noncomputable section

open Function Set ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

open NoExoticSixSphere SingularMayerVietoris PeriodTorusHigherHomology

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

theorem map_abs (t : ℝ) (x : Sphere m) : map d (|t|, x) = map d (t, x) := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_nonpos ht, map_reflected]

def reflection : Fiber d ≃ₜ Fiber d where
  toFun p := ⟨(-p.val.1, p.val.2), (map_reflected d _ _).trans p.property⟩
  invFun p := ⟨(-p.val.1, p.val.2), (map_reflected d _ _).trans p.property⟩
  left_inv _ := Subtype.ext (Prod.ext (neg_neg _) rfl)
  right_inv _ := Subtype.ext (Prod.ext (neg_neg _) rfl)
  continuous_toFun :=
    ((continuous_fst.comp continuous_subtype_val).neg.prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun :=
    ((continuous_fst.comp continuous_subtype_val).neg.prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _

def halfInclusion : C(NonnegativeHalf d, Fiber d) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def halfRetraction : C(Fiber d, NonnegativeHalf d) :=
  ⟨fun p ↦ ⟨⟨(|p.val.1|, p.val.2), (map_abs d _ _).trans p.property⟩, abs_nonneg _⟩,
    (((continuous_fst.comp continuous_subtype_val).abs.prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _).subtype_mk _⟩

theorem halfRetraction_inclusion (p : NonnegativeHalf d) :
    halfRetraction d (halfInclusion d p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (abs_of_nonneg p.property) rfl

theorem halfRetraction_comp_inclusion :
    (halfRetraction d).comp (halfInclusion d) = ContinuousMap.id (NonnegativeHalf d) :=
  ContinuousMap.ext (halfRetraction_inclusion d)

theorem halfInclusion_homology_leftInverse (k : ℕ) :
    LeftInverse (singularHomologyMap (halfRetraction d) k)
      (singularHomologyMap (halfInclusion d) k) := by
  intro a
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, halfRetraction_comp_inclusion,
    singularHomologyMap_id]
  rfl

theorem halfInclusion_homology_injective (k : ℕ) :
    Injective (singularHomologyMap (halfInclusion d) k) :=
  (halfInclusion_homology_leftInverse d k).injective

theorem half_homology_subsingleton (k : ℕ) [Subsingleton (SingularHomology (Fiber d) k)] :
    Subsingleton (SingularHomology (NonnegativeHalf d) k) :=
  (halfInclusion_homology_injective d k).subsingleton

end Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder
