import Wikipedia.SchoenfliesTheorem.Curve
import Mathlib.Topology.Instances.AddCircle.Real

/-!
# A simple loop as a circle embedding

The half-open interval parametrization of a simple loop descends to the
additive circle.  Agreement of the two endpoint values gives continuity, and
injectivity before the final endpoint gives injectivity on the quotient.
-/

open Set unitInterval Schoenflies

namespace Puzzling139335.CentralRotation.CrosscutPaths

/-- The circle map determined by the values of `f` on `[0, 1)`. -/
noncomputable def loopCircle (f : ℝ → Schoenflies.Plane) :
    AddCircle (1 : ℝ) → Schoenflies.Plane :=
  AddCircle.liftIco 1 0 f

/-- On the half-open fundamental interval, the circle map evaluates to the
original parametrization without any loop hypotheses. -/
theorem loopCircle_coe_Ico {f : ℝ → Schoenflies.Plane} {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) 1) :
    loopCircle f (t : AddCircle (1 : ℝ)) = f t :=
  AddCircle.liftIco_zero_coe_apply ht

@[simp] theorem loopCircle_zero (f : ℝ → Schoenflies.Plane) :
    loopCircle f 0 = f 0 := by
  simpa only [AddCircle.coe_zero] using
    loopCircle_coe_Ico (f := f) (t := 0) ⟨le_rfl, zero_lt_one⟩

/-- The endpoint agreement in `IsLoop` is exactly the condition needed to
make its circle map continuous at the identified endpoints. -/
theorem loopCircle_continuous {f : ℝ → Schoenflies.Plane} (hf : IsLoop f) :
    Continuous (loopCircle f) :=
  AddCircle.liftIco_zero_continuous hf.closes hf.continuousOn

/-- Injectivity on `[0, 1)` becomes injectivity on the additive circle. -/
theorem loopCircle_injective {f : ℝ → Schoenflies.Plane} (hf : IsLoop f) :
    Function.Injective (loopCircle f) := by
  have hfi : InjOn f (Ico 0 (0 + 1)) := by simpa only [zero_add] using hf.injOn
  exact hfi.injective.comp (AddCircle.equivIco (1 : ℝ) 0).injective

/-- The circle map agrees with the original loop on the entire closed unit
interval, including its final endpoint. -/
theorem loopCircle_coe {f : ℝ → Schoenflies.Plane} (hf : IsLoop f)
    {t : ℝ} (ht : t ∈ I) :
    loopCircle f (t : AddCircle (1 : ℝ)) = f t := by
  rcases lt_or_eq_of_le ht.2 with hlt | rfl
  · exact loopCircle_coe_Ico ⟨ht.1, hlt⟩
  · rw [AddCircle.coe_period, loopCircle_zero]
    exact hf.closes

/-- The quotient construction leaves the trace of a loop unchanged. -/
theorem range_loopCircle {f : ℝ → Schoenflies.Plane} (hf : IsLoop f) :
    range (loopCircle f) = f '' I := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(AddCircle.equivIco (1 : ℝ) 0 x : ℝ), ?_, rfl⟩
    have hx := (AddCircle.equivIco (1 : ℝ) 0 x).property
    exact ⟨hx.1, by simpa only [zero_add] using hx.2.le⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨(t : AddCircle (1 : ℝ)), loopCircle_coe hf ht⟩

/-- In the Hausdorff plane the circle map is a closed embedding, since its
domain is compact. -/
theorem loopCircle_isClosedEmbedding {f : ℝ → Schoenflies.Plane} (hf : IsLoop f) :
    Topology.IsClosedEmbedding (loopCircle f) :=
  (loopCircle_continuous hf).isClosedEmbedding (loopCircle_injective hf)

/-- The circle embedding associated to a simple loop, with both its evaluation
and its trace recorded. -/
theorem exists_circle_embedding {f : ℝ → Schoenflies.Plane} (hf : IsLoop f) :
    ∃ F : AddCircle (1 : ℝ) → Schoenflies.Plane,
      Continuous F ∧ Function.Injective F ∧
      (∀ t ∈ I, F (t : AddCircle (1 : ℝ)) = f t) ∧ range F = f '' I :=
  ⟨loopCircle f, loopCircle_continuous hf, loopCircle_injective hf,
    fun _ ht => loopCircle_coe hf ht, range_loopCircle hf⟩

end Puzzling139335.CentralRotation.CrosscutPaths
