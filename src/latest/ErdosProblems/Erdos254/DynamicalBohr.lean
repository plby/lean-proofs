/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos254.SpectralBohr

namespace Erdos254

open MeasureTheory Set
open scoped Topology InnerProductSpace ENNReal

lemma ContainsPiecewiseBohr.mono {A B : Set ℕ} (hA : ContainsPiecewiseBohr A) (hAB : A ⊆ B) :
    ContainsPiecewiseBohr B := by
  obtain ⟨d, θ, U, J, hU, hJ, hne, hsub⟩ := hA
  exact ⟨d, θ, U, J, hU, hJ, hne, fun n hn hp ↦ hAB (hsub n hn hp)⟩

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) (T : X ≃ᵐ X)
  (hT : MeasurePreserving T μ μ)

/-- Composition by an invertible measure-preserving transformation is unitary
on complex `L²`. -/
noncomputable def koopmanUnitary : unitary (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
  Unitary.linearIsometryEquiv.symm
    (LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ ℂ T hT) (by
      intro g
      refine ⟨Lp.compMeasurePreserving T.symm (MeasurePreserving.symm T hT) g, ?_⟩
      change Lp.compMeasurePreserving T hT
        (Lp.compMeasurePreserving T.symm (MeasurePreserving.symm T hT) g) = g
      rw [← Lp.compMeasurePreserving_comp_apply g (MeasurePreserving.symm T hT) hT]
      simpa only [T.symm_comp_self] using (Lp.compMeasurePreserving_id_apply g)))

lemma koopmanUnitary_apply (v : Lp ℂ 2 μ) :
    (koopmanUnitary μ T hT : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) v =
      Lp.compMeasurePreserving T hT v := rfl

lemma koopmanUnitary_pow_apply (v : Lp ℂ 2 μ) (n : ℕ) :
    ((koopmanUnitary μ T hT : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) ^ n) v =
      Lp.compMeasurePreserving T^[n] (hT.iterate n) v := by
  have hfun : (koopmanUnitary μ T hT : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) =
      (Lp.compMeasurePreservingₗᵢ ℂ T hT).toContinuousLinearMap := rfl
  rw [hfun, pow_apply_eq_iterate]
  exact congrFun (Lp.compMeasurePreserving_iterate (E := ℂ) (p := 2) hT n) v

lemma koopmanUnitary_const [IsFiniteMeasure μ] :
    (koopmanUnitary μ T hT : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (Lp.const 2 μ (1 : ℂ)) =
      Lp.const 2 μ (1 : ℂ) := by
  rw [koopmanUnitary_apply, ← indicatorConstLp_univ]
  rw [Lp.indicatorConstLp_compMeasurePreserving]
  simp

lemma koopman_indicator_correlation [IsFiniteMeasure μ] {S : Set X}
    (hS : MeasurableSet S) (n : ℕ) :
    inner ℂ (indicatorConstLp 2 hS (measure_ne_top μ S) (1 : ℂ))
      (((koopmanUnitary μ T hT : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) ^ n)
        (indicatorConstLp 2 hS (measure_ne_top μ S) (1 : ℂ))) =
      (μ.real (S ∩ (T^[n]) ⁻¹' S) : ℂ) := by
  rw [koopmanUnitary_pow_apply, Lp.indicatorConstLp_compMeasurePreserving]
  exact L2.inner_indicatorConstLp_one_indicatorConstLp_one hS _

include hT in
/-- The return times of a positive-measure set contain a piecewise Bohr set.
This is the dynamical input in Følner's difference-set argument. -/
theorem return_times_piecewiseBohr [IsProbabilityMeasure μ] {S : Set X}
    (hS : MeasurableSet S) (hpos : 0 < μ.real S) :
    ContainsPiecewiseBohr {n : ℕ | μ (S ∩ (T^[n]) ⁻¹' S) ≠ 0} := by
  let v : Lp ℂ 2 μ := indicatorConstLp 2 hS (measure_ne_top μ S) (1 : ℂ)
  let w : Lp ℂ 2 μ := Lp.const 2 μ (1 : ℂ)
  have hwn : ‖w‖ = 1 := by simp [w, Lp.norm_const]
  have hwv : inner ℂ w v = (μ.real S : ℂ) := by
    rw [show w = indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) (1 : ℂ)
      from (indicatorConstLp_univ 2 μ (1 : ℂ)).symm]
    change inner ℂ (indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) (1 : ℂ))
      (indicatorConstLp 2 hS (measure_ne_top μ S) (1 : ℂ)) = _
    rw [L2.inner_indicatorConstLp_one_indicatorConstLp_one, univ_inter]
    rfl
  obtain ⟨ν, hfin, hmom, hatom⟩ := exists_unitary_spectral_measure_with_atom
    (koopmanUnitary μ T hT) v w (koopmanUnitary_const μ T hT) hwn
  have : IsFiniteMeasure ν := hfin
  have ha : 0 < ν.real {1} := by
    have hnorm : 0 < ‖inner ℂ w v‖ := by rw [hwv]; simpa using hpos.ne'
    exact (sq_pos_of_pos hnorm).trans_le hatom
  apply (spectral_piecewiseBohr ν ha).mono
  intro n hn hz
  apply hn
  change (∫ z : Circle, (z : ℂ) ^ n ∂ν) = 0
  rw [hmom]
  change inner ℂ (indicatorConstLp 2 hS (measure_ne_top μ S) (1 : ℂ))
    (((koopmanUnitary μ T hT : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) ^ n)
      (indicatorConstLp 2 hS (measure_ne_top μ S) (1 : ℂ))) = 0
  rw [koopman_indicator_correlation]
  simp [Measure.real, hz]

end Erdos254
