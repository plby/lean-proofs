import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The actual cylinder homeomorphism of a compact ambient isotopy

A continuous family of bijections of a compact Hausdorff space induces a
homeomorphism of its unit-time cylinder. Thus the inverse is jointly continuous,
not merely separately continuous at each time. The homeomorphism preserves time.
-/

noncomputable section

open Function

namespace Wikipedia.SmoothSixDPoincare.AmbientIsotopy

variable {M : Type*} [TopologicalSpace M]

def cylinderMap (A : ℝ × M → M) (p : unitInterval × M) : unitInterval × M :=
  (p.1, A ((p.1 : ℝ), p.2))

theorem continuous_cylinderMap {A : ℝ × M → M} (hA : Continuous A) :
    Continuous (cylinderMap A) :=
  continuous_fst.prodMk (hA.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))

omit [TopologicalSpace M] in
theorem bijective_cylinderMap {A : ℝ × M → M}
    (hA : ∀ t, Bijective (fun x => A (t, x))) : Bijective (cylinderMap A) := by
  constructor
  · rintro ⟨t, x⟩ ⟨s, y⟩ hxy
    have hts : t = s := congrArg Prod.fst hxy
    subst s
    exact Prod.ext rfl ((hA t).1 (congrArg Prod.snd hxy))
  · rintro ⟨t, y⟩
    obtain ⟨x, hx⟩ := (hA t).2 y
    exact ⟨(t, x), Prod.ext rfl hx⟩

variable [CompactSpace M] [T2Space M]

/-- A genuine time-preserving cylinder homeomorphism, with jointly continuous inverse. -/
def cylinderHomeomorph (A : ℝ × M → M) (hA : Continuous A)
    (hbij : ∀ t, Bijective (fun x => A (t, x))) :
    (unitInterval × M) ≃ₜ (unitInterval × M) :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (cylinderMap A) (bijective_cylinderMap hbij))
    (continuous_cylinderMap hA)

theorem cylinderHomeomorph_apply (A : ℝ × M → M) (hA : Continuous A)
    (hbij : ∀ t, Bijective (fun x => A (t, x))) (p : unitInterval × M) :
    cylinderHomeomorph A hA hbij p = (p.1, A ((p.1 : ℝ), p.2)) := rfl

theorem cylinderHomeomorph_fst (A : ℝ × M → M) (hA : Continuous A)
    (hbij : ∀ t, Bijective (fun x => A (t, x))) (p : unitInterval × M) :
    (cylinderHomeomorph A hA hbij p).1 = p.1 := rfl

/-- The inverse homeomorphism also preserves the actual time coordinate. -/
theorem cylinderHomeomorph_symm_fst (A : ℝ × M → M) (hA : Continuous A)
    (hbij : ∀ t, Bijective (fun x => A (t, x))) (p : unitInterval × M) :
    ((cylinderHomeomorph A hA hbij).symm p).1 = p.1 := by
  calc
    ((cylinderHomeomorph A hA hbij).symm p).1 =
        (cylinderHomeomorph A hA hbij ((cylinderHomeomorph A hA hbij).symm p)).1 :=
      (cylinderHomeomorph_fst A hA hbij _).symm
    _ = p.1 := congrArg Prod.fst ((cylinderHomeomorph A hA hbij).apply_symm_apply p)

end Wikipedia.SmoothSixDPoincare.AmbientIsotopy
