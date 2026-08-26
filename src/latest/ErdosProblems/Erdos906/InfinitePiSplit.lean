import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Integral.Prod

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory

namespace CofiniteDerivatives

section Split

variable {ι : Type*} [DecidableEq ι]
variable (X : ι → Type*) [∀ i, MeasurableSpace (X i)]

/-- Split a dependent product into one chosen coordinate and all remaining coordinates. -/
def piSplitAt (j : ι) :
    (∀ i, X i) ≃ᵐ X j × (∀ i : {i // i ≠ j}, X i) where
  toEquiv := Equiv.piSplitAt j X
  measurable_toFun :=
    (measurable_pi_apply j).prodMk <| measurable_pi_iff.2 fun _ ↦ measurable_pi_apply _
  measurable_invFun := measurable_pi_iff.2 fun i ↦ by
    by_cases hi : i = j
    · subst i
      simpa [Equiv.piSplitAt] using!
        (measurable_fst : Measurable (Prod.fst : X j × (∀ i : {i // i ≠ j}, X i) → X j))
    · simpa [Equiv.piSplitAt, hi] using!
        (measurable_pi_apply ⟨i, hi⟩).comp
          (measurable_snd : Measurable (Prod.snd :
            X j × (∀ i : {i // i ≠ j}, X i) → (∀ i : {i // i ≠ j}, X i)))

@[simp]
theorem piSplitAt_apply_fst (j : ι) (x : ∀ i, X i) :
    (piSplitAt X j x).1 = x j := rfl

@[simp]
theorem piSplitAt_apply_snd (j : ι) (x : ∀ i, X i) (i : {i // i ≠ j}) :
    (piSplitAt X j x).2 i = x i := rfl

end Split

section MeasureSplit

variable {ι : Type*}
variable (X : ι → Type*) [∀ i, MeasurableSpace (X i)]
variable (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- Under an infinite product measure, one coordinate is independent of the tuple of all the
remaining coordinates. -/
theorem indepFun_eval_restrict (j : ι) :
    IndepFun (fun x : ∀ i, X i ↦ x j)
      (fun x : (∀ i, X i) ↦ fun i : {i // i ≠ j} ↦ x i)
      (Measure.infinitePi μ) := by
  rw [IndepFun_iff_Indep]
  let m : ι → MeasurableSpace (∀ i, X i) := fun i ↦
    (inferInstance : MeasurableSpace (X i)).comap (fun x : ∀ i, X i ↦ x i)
  have h_indep :
      iIndep m (Measure.infinitePi μ) :=
    (iIndepFun_infinitePi (P := μ) (X := fun _ ↦ id) (fun _ ↦ measurable_id)).iIndep
  have h := indep_iSup_of_disjoint
    (m := m) (μ := Measure.infinitePi μ)
    (fun i ↦ (measurable_pi_apply i).comap_le) h_indep
    (S := ({j} : Set ι)) (T := {i | i ≠ j}) (by simp)
  have h_left : (⨆ i ∈ ({j} : Set ι), m i) = m j := by simp
  have h_right :
      (⨆ i ∈ {i | i ≠ j}, m i) =
        MeasurableSpace.comap
          (fun x : (∀ i, X i) ↦ fun i : {i // i ≠ j} ↦ x i) inferInstance := by
    rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    simp only [MeasurableSpace.comap_comp, Function.comp_def, Set.mem_ofPred_eq]
    exact iSup_subtype'
  rw [h_left, h_right] at h
  exact h

variable [DecidableEq ι]

/-- The coordinate split sends an infinite product measure to the binary product of the chosen
coordinate law and the infinite product of all remaining coordinate laws. -/
theorem infinitePi_map_piSplitAt (j : ι) :
    (Measure.infinitePi μ).map (piSplitAt X j) =
      (μ j).prod (Measure.infinitePi fun i : {i // i ≠ j} ↦ μ i) := by
  have h_eval : AEMeasurable (fun x : ∀ i, X i ↦ x j) (Measure.infinitePi μ) :=
    (measurable_pi_apply j).aemeasurable
  have h_restrict_meas : Measurable
      (fun x : (∀ i, X i) ↦ fun i : {i // i ≠ j} ↦ x i) := by
    rw [measurable_pi_iff]
    exact fun i ↦ measurable_pi_apply (X := X) i.1
  have h_restrict : AEMeasurable
      (fun x : (∀ i, X i) ↦ fun i : {i // i ≠ j} ↦ x i) (Measure.infinitePi μ) :=
    h_restrict_meas.aemeasurable
  change (Measure.infinitePi μ).map
    (fun x : ∀ i, X i ↦ (x j, fun i : {i // i ≠ j} ↦ x i)) = _
  rw [(indepFun_iff_map_prod_eq_prod_map_map h_eval h_restrict).1
    (indepFun_eval_restrict X μ j), Measure.infinitePi_map_eval]
  congr 1
  exact Measure.infinitePi_map_restrict' μ

/-- The measurable coordinate split is measure preserving for infinite product measures. -/
theorem measurePreserving_piSplitAt (j : ι) :
    MeasurePreserving (piSplitAt X j) (Measure.infinitePi μ)
      ((μ j).prod (Measure.infinitePi fun i : {i // i ≠ j} ↦ μ i)) where
  measurable := (piSplitAt X j).measurable
  map_eq := infinitePi_map_piSplitAt X μ j

end MeasureSplit

section SmallBall

variable {ι : Type*}
variable (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)]

/-- Fubini small-ball bound for an affine function of one coordinate. The remainder `H` is
defined on the complementary product, so its independence from coordinate `j` is encoded in its
type. -/
theorem infinitePi_affine_smallBall (j : ι) (a : ℂ)
  (H : ({i // i ≠ j} → ℂ) → ℂ) (hH : Measurable H)
  (ε : ℝ) (C : ENNReal)
    (hsmall : ∀ w : ℂ, μ j {z | ‖a * z + w‖ < ε} ≤ C) :
    Measure.infinitePi μ
    {ω : ι → ℂ | ‖a * ω j + H (fun i : {i // i ≠ j} ↦ ω i)‖ < ε} ≤ C := by
  classical
  let S : Set (ℂ × (∀ i : {i // i ≠ j}, ℂ)) :=
    {p | ‖a * p.1 + H p.2‖ < ε}
  have hS : MeasurableSet S := by
    exact measurableSet_lt
      ((measurable_const.mul measurable_fst).add (hH.comp measurable_snd)).norm
      measurable_const
  have hpre :
      {ω : ι → ℂ | ‖a * ω j + H (fun i : {i // i ≠ j} ↦ ω i)‖ < ε} =
        piSplitAt (fun _ : ι ↦ ℂ) j ⁻¹' S := rfl
  rw [hpre, ← Measure.map_apply (piSplitAt (fun _ : ι ↦ ℂ) j).measurable hS,
    infinitePi_map_piSplitAt (fun _ : ι ↦ ℂ) μ j, Measure.prod_apply_symm hS]
  apply lintegral_le_const
  exact ae_of_all _ fun y ↦ by simpa [S] using! hsmall (H y)

/-- Full-product form of `infinitePi_affine_smallBall`. The equality hypothesis says precisely
that `H` depends only on coordinates other than `j`. -/
theorem infinitePi_affine_smallBall_of_factor (j : ι) (a : ℂ)
  (H : (ι → ℂ) → ℂ) (H₀ : ({i // i ≠ j} → ℂ) → ℂ)
    (hH₀ : Measurable H₀)
    (hH : ∀ ω, H ω = H₀ (fun i : {i // i ≠ j} ↦ ω i))
    (ε : ℝ) (C : ENNReal)
    (hsmall : ∀ w : ℂ, μ j {z | ‖a * z + w‖ < ε} ≤ C) :
    Measure.infinitePi μ {ω : ι → ℂ | ‖a * ω j + H ω‖ < ε} ≤ C := by
  classical
  simpa only [hH] using! infinitePi_affine_smallBall μ j a H₀ hH₀ ε C hsmall

/-- Version with the selected coordinate law named separately as `ν`. -/
theorem infinitePi_affine_smallBall_of_law (j : ι) (ν : Measure ℂ) (hν : μ j = ν)
    (a : ℂ) (H : ({i // i ≠ j} → ℂ) → ℂ) (hH : Measurable H)
    (ε : ℝ) (C : ENNReal)
    (hsmall : ∀ w : ℂ, ν {z | ‖a * z + w‖ < ε} ≤ C) :
    Measure.infinitePi μ
        {ω : ι → ℂ | ‖a * ω j + H (fun i : {i // i ≠ j} ↦ ω i)‖ < ε} ≤ C := by
  classical
  apply infinitePi_affine_smallBall μ j a H hH ε C
  intro w
  simpa only [hν] using! hsmall w

end SmallBall

end CofiniteDerivatives
