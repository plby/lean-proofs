import StackExchange.Puzzling139335.LoopVariation.Geometric.Defs
import StackExchange.Puzzling139335.LoopVariation.Invariance

/-!
# Intrinsic cyclic variation of Jordan curves

The concrete supremum chosen for a Jordan curve is independent of the chosen
parametrization, starting point, orientation and parameter interval. Therefore
congruent Jordan curves have exactly equal truncated variation, including when
their ordinary perimeters are infinite.
-/

open Set

namespace Puzzling139335.LoopVariation

open ArcVariation

noncomputable section

/-- Every genuine Jordan-loop parametrization computes the set-level value. -/
theorem loopVariation_eq_of_parametrization {C : Set Schoenflies.Plane}
    (ε : ℝ) (hC : Schoenflies.IsJordanCurve C)
    {f : ℝ → Schoenflies.Plane} {a b : ℝ} (hab : a < b)
    (hfcont : ContinuousOn f (Icc a b)) (hfclose : f a = f b)
    (hfi : InjOn f (Ico a b)) (himage : f '' Icc a b = C) :
    loopVariation ε C = loopVariationOn ε f (Icc a b) := by
  rw [loopVariation, dif_pos hC]
  obtain ⟨hg, hgimage⟩ := Classical.choose_spec hC
  exact loopVariationOn_eq_of_loop_image_eq ε zero_lt_one hab
    hg.continuousOn hg.closes hg.injOn hfcont hfclose hfi (hgimage.trans himage.symm)

/-- An ambient isometry takes a Jordan curve to a Jordan curve. -/
theorem isJordanCurve_image_isometry {C : Set Schoenflies.Plane}
    (hC : Schoenflies.IsJordanCurve C)
    {e : Schoenflies.Plane → Schoenflies.Plane} (he : Isometry e) :
    Schoenflies.IsJordanCurve (e '' C) := by
  obtain ⟨f, hf, himage⟩ := hC
  refine ⟨e ∘ f, ⟨he.continuous.comp_continuousOn hf.continuousOn,
    congrArg e hf.closes, ?_⟩, ?_⟩
  · intro x hx y hy hxy
    exact hf.injOn hx hy (he.injective hxy)
  · rw [Set.image_comp, himage]

/-- Congruent Jordan curves have exactly equal cyclic truncated variation. -/
theorem loopVariation_image_isometry {C : Set Schoenflies.Plane} (ε : ℝ)
    (hC : Schoenflies.IsJordanCurve C)
    {e : Schoenflies.Plane → Schoenflies.Plane} (he : Isometry e) :
    loopVariation ε (e '' C) = loopVariation ε C := by
  obtain ⟨f, hf, himage⟩ := hC
  have hC : Schoenflies.IsJordanCurve C := ⟨f, hf, himage⟩
  have hecont : ContinuousOn (e ∘ f) (Icc (0 : ℝ) 1) :=
    he.continuous.comp_continuousOn hf.continuousOn
  have heinj : InjOn (e ∘ f) (Ico (0 : ℝ) 1) := by
    intro x hx y hy hxy
    exact hf.injOn hx hy (he.injective hxy)
  have heimage : (e ∘ f) '' Icc (0 : ℝ) 1 = e '' C := by
    rw [Set.image_comp, himage]
  rw [loopVariation_eq_of_parametrization ε (isJordanCurve_image_isometry hC he)
      zero_lt_one hecont (congrArg e hf.closes) heinj heimage,
    loopVariation_eq_of_parametrization ε hC zero_lt_one
      hf.continuousOn hf.closes hf.injOn himage]
  exact loopVariationOn_comp_isometry he ε f (Icc (0 : ℝ) 1)

end

end Puzzling139335.LoopVariation
