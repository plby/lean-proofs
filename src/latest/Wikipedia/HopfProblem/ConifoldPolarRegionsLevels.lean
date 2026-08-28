import Wikipedia.HopfProblem.ConifoldPolarBasic
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Native Frobenius levels in the explicit polar coordinates

A fixed Frobenius level in the original determinant-one matrix group is
homeomorphic to a Euclidean two-sphere times the original unit normal
three-sphere.  At radius zero the first factor is the singleton sphere.
All subtypes retain their original subspace topologies.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ConifoldPolar

open ConifoldStandardBoundary

/-- The literal Frobenius level in the original determinant-one matrix group. -/
def frobeniusLevel (ρ : ℝ) : Set SpecialLinear :=
  {M | frobeniusSq M.val = 2 + 4 * ρ ^ 2}

theorem frobeniusSq_eq_iff_norm_forward_eq {ρ : ℝ} (hρ : 0 ≤ ρ)
    (M : SpecialLinear) :
    frobeniusSq M.val = 2 + 4 * ρ ^ 2 ↔ ‖(forward M).1‖ = ρ := by
  rw [frobeniusSq_eq]
  constructor
  · intro h
    apply (sq_eq_sq₀ (norm_nonneg _) hρ).mp
    linarith
  · intro h
    rw [h]

theorem forward_fst_mem_sphere {ρ : ℝ} (hρ : 0 ≤ ρ)
    (M : ↥(frobeniusLevel ρ)) : (forward M.val).1 ∈ Metric.sphere (0 : Base) ρ := by
  rw [Metric.mem_sphere, dist_zero_right]
  exact (frobeniusSq_eq_iff_norm_forward_eq hρ M.val).mp M.property

/-- Restrict the explicit polar coordinates to a literal Frobenius level. -/
def levelForward {ρ : ℝ} (hρ : 0 ≤ ρ) (M : ↥(frobeniusLevel ρ)) :
    ↥(Metric.sphere (0 : Base) ρ) × NormalSphere :=
  (⟨(forward M.val).1, forward_fst_mem_sphere hρ M⟩, (forward M.val).2)

/-- Restrict the original inverse matrix formula to a Euclidean sphere. -/
def levelInverse (ρ : ℝ) (q : ↥(Metric.sphere (0 : Base) ρ) × NormalSphere) :
    ↥(frobeniusLevel ρ) :=
  ⟨inverse (q.1.val, q.2), by
    change frobeniusSq (inverse (q.1.val, q.2)).val = 2 + 4 * ρ ^ 2
    rw [frobeniusSq_eq, forward_inverse]
    have hq : ‖q.1.val‖ = ρ := by
      simpa only [Metric.mem_sphere, dist_zero_right] using q.1.property
    simp only [hq]⟩

@[simp] theorem levelForward_fst_val {ρ : ℝ} (hρ : 0 ≤ ρ)
    (M : ↥(frobeniusLevel ρ)) :
    (levelForward hρ M).1.val = baseCoordinates (positivePart M.val.val) := rfl

@[simp] theorem levelForward_snd_val {ρ : ℝ} (hρ : 0 ≤ ρ)
    (M : ↥(frobeniusLevel ρ)) :
    (levelForward hρ M).2.val = normalCoordinates (unitaryPart M.val.val) := rfl

@[simp] theorem levelInverse_val_val (ρ : ℝ)
    (q : ↥(Metric.sphere (0 : Base) ρ) × NormalSphere) :
    (levelInverse ρ q).val.val = positiveMatrix q.1.val * unitaryMatrix q.2.val := rfl

@[simp] theorem levelInverse_levelForward {ρ : ℝ} (hρ : 0 ≤ ρ)
    (M : ↥(frobeniusLevel ρ)) : levelInverse ρ (levelForward hρ M) = M := by
  apply Subtype.ext
  exact inverse_forward M.val

@[simp] theorem levelForward_levelInverse {ρ : ℝ} (hρ : 0 ≤ ρ)
    (q : ↥(Metric.sphere (0 : Base) ρ) × NormalSphere) :
    levelForward hρ (levelInverse ρ q) = q := by
  have h := forward_inverse (q.1.val, q.2)
  have hfst := congrArg Prod.fst h
  have hsnd := congrArg Prod.snd h
  apply Prod.ext
  · apply Subtype.ext
    exact hfst
  · exact hsnd

theorem levelForward_continuous {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Continuous (levelForward hρ) := by
  have hf : Continuous (fun M : ↥(frobeniusLevel ρ) => forward M.val) :=
    forward_continuous.comp continuous_subtype_val
  exact (hf.fst.subtype_mk _).prodMk hf.snd

theorem levelInverse_continuous (ρ : ℝ) : Continuous (levelInverse ρ) := by
  have hq : Continuous
      (fun q : ↥(Metric.sphere (0 : Base) ρ) × NormalSphere => (q.1.val, q.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  exact (inverse_continuous.comp hq).subtype_mk _

/-- A native Frobenius level is the radius-`ρ` Euclidean sphere times the unit `S³`. -/
def levelHomeomorph (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ↥(frobeniusLevel ρ) ≃ₜ ↥(Metric.sphere (0 : Base) ρ) × NormalSphere where
  toFun := levelForward hρ
  invFun := levelInverse ρ
  left_inv := levelInverse_levelForward hρ
  right_inv := levelForward_levelInverse hρ
  continuous_toFun := levelForward_continuous hρ
  continuous_invFun := levelInverse_continuous ρ

@[simp] theorem levelHomeomorph_fst_val (ρ : ℝ) (hρ : 0 ≤ ρ)
    (M : ↥(frobeniusLevel ρ)) :
    (levelHomeomorph ρ hρ M).1.val = baseCoordinates (positivePart M.val.val) := rfl

@[simp] theorem levelHomeomorph_snd_val (ρ : ℝ) (hρ : 0 ≤ ρ)
    (M : ↥(frobeniusLevel ρ)) :
    (levelHomeomorph ρ hρ M).2.val = normalCoordinates (unitaryPart M.val.val) := rfl

@[simp] theorem levelHomeomorph_symm_val_val (ρ : ℝ) (hρ : 0 ≤ ρ)
    (q : ↥(Metric.sphere (0 : Base) ρ) × NormalSphere) :
    ((levelHomeomorph ρ hρ).symm q).val.val =
      positiveMatrix q.1.val * unitaryMatrix q.2.val := rfl

/-- Compactness of the native level follows from compactness of both Euclidean spheres. -/
theorem isCompact_frobeniusLevel (ρ : ℝ) (hρ : 0 ≤ ρ) :
    IsCompact (frobeniusLevel ρ) :=
  isCompact_iff_compactSpace.mpr (levelHomeomorph ρ hρ).symm.compactSpace

/-- The original right diagonal circle map restricts to every Frobenius level. -/
def levelCircleAction (ρ : ℝ) (u : ℂ) (hu : ‖u‖ = 1)
    (M : ↥(frobeniusLevel ρ)) : ↥(frobeniusLevel ρ) :=
  ⟨circleAction u hu M.val, by
    change frobeniusSq (rightCircle u M.val.val) = 2 + 4 * ρ ^ 2
    rw [frobeniusSq_rightCircle u hu]
    exact M.property⟩

@[simp] theorem levelCircleAction_val (ρ : ℝ) (u : ℂ) (hu : ‖u‖ = 1)
    (M : ↥(frobeniusLevel ρ)) :
    (levelCircleAction ρ u hu M).val = circleAction u hu M.val := rfl

@[simp] theorem levelCircleAction_val_val (ρ : ℝ) (u : ℂ) (hu : ‖u‖ = 1)
    (M : ↥(frobeniusLevel ρ)) :
    (levelCircleAction ρ u hu M).val.val = rightCircle u M.val.val := rfl

theorem levelForward_circleAction {ρ : ℝ} (hρ : 0 ≤ ρ) (u : ℂ) (hu : ‖u‖ = 1)
    (M : ↥(frobeniusLevel ρ)) :
    levelForward hρ (levelCircleAction ρ u hu M) =
      ((levelForward hρ M).1, sphereRotation u hu (levelForward hρ M).2) := by
  have h := forward_circleAction u hu M.val
  have hfst := congrArg Prod.fst h
  have hsnd := congrArg Prod.snd h
  apply Prod.ext
  · apply Subtype.ext
    exact hfst
  · exact hsnd

/-- On a native level the polar homeomorphism fixes the base and rotates the normal sphere. -/
theorem levelHomeomorph_circleAction (ρ : ℝ) (hρ : 0 ≤ ρ) (u : ℂ) (hu : ‖u‖ = 1)
    (M : ↥(frobeniusLevel ρ)) :
    levelHomeomorph ρ hρ (levelCircleAction ρ u hu M) =
      ((levelHomeomorph ρ hρ M).1, sphereRotation u hu (levelHomeomorph ρ hρ M).2) :=
  levelForward_circleAction hρ u hu M

end Wikipedia.HopfProblem.ConifoldPolar
