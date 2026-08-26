import ErdosProblems.Erdos1148.ForwardHaarTubeGeometry
import ErdosProblems.Erdos1148.ModularHaarLocalMass
import ErdosProblems.Erdos1148.BoundedFrameInjectivity

/-! # Uniform lower Haar mass of locally injective modular Bowen balls -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Measure
open scoped MatrixGroups ENNReal Pointwise

def modularForwardHaarBall (η S : ℝ) (g : SL(2, ℝ)) : Set ModularOrbitSpace :=
  (fun h : SL(2, ℝ) => modularMk (g * h)) '' forwardHaarTube η S

lemma modularForwardHaarBall_eq (η S : ℝ) (g : SL(2, ℝ)) :
    modularForwardHaarBall η S g = modularMk '' ((fun h : SL(2, ℝ) => g * h) '' forwardHaarTube η S) :=
  (Set.image_image _ _ _).symm

lemma isCompact_modularForwardHaarBall {η S : ℝ} (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 8)
    (hS : 0 ≤ S) (g : SL(2, ℝ)) : IsCompact (modularForwardHaarBall η S g) :=
  (isCompact_forwardHaarTube hη hηsmall hS).image
    (continuous_modularMk.comp (continuous_const.mul continuous_id))

lemma modularMk_mem_modularForwardHaarBall {η S : ℝ} (hη : 0 ≤ η) (g : SL(2, ℝ)) :
    modularMk g ∈ modularForwardHaarBall η S g :=
  ⟨1, one_mem_forwardHaarTube hη, by simp only [mul_one]⟩

lemma modularForwardHaarBall_integral_mul (η S : ℝ) (γ : SL(2, ℤ)) (g : SL(2, ℝ)) :
    modularForwardHaarBall η S ((γ : SL(2, ℝ)) * g) = modularForwardHaarBall η S g := by
  simp only [modularForwardHaarBall, mul_assoc, modularMk_integral_mul]

theorem modularForwardHaarBall_mass_lower_of_bounded {A η : ℝ}
    (hA : 0 ≤ A) (hη : 0 < η) (hηsmall : η ≤ 1 / 8) (hscale : 16 * A ^ 2 * η < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ (g : SL(2, ℝ)), (∀ i j : Fin 2, |g i j| ≤ A) →
      ∀ S : ℝ, 0 ≤ S → ENNReal.ofReal (c * Real.exp (-S)) ≤
        normalizedModularHaarMeasure (modularForwardHaarBall η S g) := by
  obtain ⟨c, hc, hvol⟩ := forwardHaarTube_mass_lower hη (by linarith)
  let a := ((modularHaarMeasure Set.univ)⁻¹).toReal
  have hnorm₀ : (modularHaarMeasure Set.univ)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)
  have hnormTop : (modularHaarMeasure Set.univ)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr (NeZero.ne _)
  have ha : 0 < a := ENNReal.toReal_pos hnorm₀ hnormTop
  have hae : ENNReal.ofReal a = (modularHaarMeasure Set.univ)⁻¹ := ENNReal.ofReal_toReal hnormTop
  refine ⟨a * c, mul_pos ha hc, ?_⟩
  intro g hg S hS
  let E := (fun h : SL(2, ℝ) => g * h) '' forwardHaarTube η S
  have hE : IsCompact E := (isCompact_forwardHaarTube hη.le hηsmall hS).image
    (continuous_const.mul continuous_id)
  have hinj : Set.InjOn modularMk E := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ huv
    have heq := modularMk_injective_on_small_right_neighborhood hA hη.le
      (by linarith) hscale g hg hu.1 hv.1 huv
    rw [heq]
  have hlocal := haar_mass_le_normalizedModularHaarMeasure_image hE.measurableSet
    (hE.image continuous_modularMk).measurableSet hinj
  have hmass : (Measure.haar (G := SL(2, ℝ))) E =
      (Measure.haar (G := SL(2, ℝ))) (forwardHaarTube η S) :=
    measure_smul (Measure.haar (G := SL(2, ℝ))) g _
  rw [hmass, ← modularForwardHaarBall_eq] at hlocal
  calc
    ENNReal.ofReal ((a * c) * Real.exp (-S)) =
        (modularHaarMeasure Set.univ)⁻¹ * ENNReal.ofReal (c * Real.exp (-S)) := by
      rw [mul_assoc, ENNReal.ofReal_mul ha.le, hae]
    _ ≤ (modularHaarMeasure Set.univ)⁻¹ *
        (Measure.haar (G := SL(2, ℝ))) (forwardHaarTube η S) := mul_le_mul_right (hvol S hS) _
    _ ≤ _ := hlocal

end Erdos1148.DukeArithmetic
