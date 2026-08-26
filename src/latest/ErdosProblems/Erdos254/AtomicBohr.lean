/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos254.AtomicMeasure

namespace Erdos254

open MeasureTheory Set
open scoped BigOperators Topology

/-- The Fourier coefficients of a measure supported on a finite set are sampled
from one continuous function on a finite-dimensional torus. -/
theorem finite_measure_torus_model (μ : Measure Circle) [IsFiniteMeasure μ]
    (F : Finset Circle) :
    ∃ (θ : UnitAddTorus (Fin F.card)) (P : C(UnitAddTorus (Fin F.card), ℂ)),
      P 0 = (μ.real (F : Set Circle) : ℂ) ∧
      ∀ n : ℕ, P (n • θ) = circleCoeff (μ.restrict (F : Set Circle)) n := by
  classical
  let e : Fin F.card ≃ F := F.equivFin.symm
  let θ : UnitAddTorus (Fin F.card) := fun i ↦
    (AddCircle.homeomorphCircle (T := 1) one_ne_zero).symm (e i : Circle)
  let P : C(UnitAddTorus (Fin F.card), ℂ) :=
    ⟨fun x ↦ ∑ i, (μ.real {(e i : Circle)} : ℂ) * (AddCircle.toCircle (x i) : ℂ), by
      apply continuous_finsetSum
      intro i _
      exact continuous_const.mul (continuous_subtype_val.comp
        (AddCircle.continuous_toCircle.comp (continuous_apply i)))⟩
  have hp (n : ℕ) : P (n • θ) = circleCoeff (μ.restrict (F : Set Circle)) n := by
    have hθ (i : Fin F.card) : AddCircle.toCircle ((n • θ) i) = (e i : Circle) ^ n := by
      change AddCircle.toCircle (n • θ i) = _
      rw [AddCircle.toCircle_nsmul]
      congr 1
      rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
      exact Homeomorph.apply_symm_apply _ _
    calc
      _ = ∑ i : Fin F.card, (μ.real {(e i : Circle)} : ℂ) * ((e i : Circle) : ℂ) ^ n := by
        change (∑ i : Fin F.card, (μ.real {(e i : Circle)} : ℂ) *
          (AddCircle.toCircle ((n • θ) i) : ℂ)) = _
        apply Finset.sum_congr rfl
        intro i _
        rw [hθ, Circle.coe_pow]
      _ = ∑ z ∈ F, (μ.real {z} : ℂ) * (z : ℂ) ^ n := by
        let g : Circle → ℂ := fun z ↦ (μ.real {z} : ℂ) * (z : ℂ) ^ n
        exact (e.sum_comp (fun z : F ↦ g z)).trans (Finset.sum_coe_sort F g)
      _ = _ := (circleCoeff_finset μ F n).symm
  refine ⟨θ, P, ?_, hp⟩
  have h := hp 0
  simpa [circleCoeff, Measure.real] using h

/-- A positive atom at `1` gives a Bohr neighborhood on which the atomic
Fourier contribution is uniformly positive. -/
theorem exists_bohr_atomic_lower (μ : Measure Circle) [IsFiniteMeasure μ]
    (ha : 0 < μ.real {1}) :
    ∃ (d : ℕ) (θ : UnitAddTorus (Fin d)) (U : Set (UnitAddTorus (Fin d))),
      IsOpen U ∧ 0 ∈ U ∧ ∀ n : ℕ, n • θ ∈ U →
        μ.real {1} / 2 < (circleCoeff (circleAtomicPart μ) n).re := by
  obtain ⟨F, hF, htail⟩ := exists_finite_small_tail μ (circleAtoms_countable μ)
    (show 0 < μ.real {1} / 8 by positivity)
  have hmem : (1 : Circle) ∈ circleAtoms μ := by
    intro h
    have : μ.real {1} = 0 := by simp [Measure.real, h]
    linarith
  have hmass : μ.real {1} ≤ μ.real (circleAtoms μ) :=
    measureReal_mono (singleton_subset_iff.mpr hmem)
  have htail' := htail
  rw [measureReal_sdiff hF F.measurableSet] at htail'
  obtain ⟨θ, P, hP0, hP⟩ := finite_measure_torus_model μ F
  let U : Set (UnitAddTorus (Fin F.card)) := {x | 3 * μ.real {1} / 4 < (P x).re}
  refine ⟨F.card, θ, U, isOpen_lt continuous_const (Complex.continuous_re.comp P.continuous),
    ?_, ?_⟩
  · change 3 * μ.real {1} / 4 < (P 0).re
    rw [hP0, Complex.ofReal_re]
    linarith
  · intro n hn
    change 3 * μ.real {1} / 4 < (P (n • θ)).re at hn
    rw [hP] at hn
    have herr := (norm_atomic_sub_finite_le μ F hF n).trans_lt htail
    have hre := Complex.re_le_norm
      (circleCoeff (μ.restrict (F : Set Circle)) n - circleCoeff (circleAtomicPart μ) n)
    rw [norm_sub_rev] at hre
    simp only [Complex.sub_re] at hre
    linarith

end Erdos254
