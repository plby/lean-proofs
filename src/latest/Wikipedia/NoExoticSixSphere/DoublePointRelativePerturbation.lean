import Wikipedia.NoExoticSixSphere.DoublePointLinearPerturbation
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Off-diagonal regularity while retaining both endpoint maps

A fixed smooth time cutoff vanishes outside the open unit interval and is
positive inside it. Multiplying the actual linear perturbation by this
cutoff leaves all exterior-time slices exactly unchanged. The nonzero
direction on interior distinct pairs still gives dense regular parameters.
-/

noncomputable section

open Set Function TopologicalSpace
open scoped ContDiff

namespace NoExoticSixSphere.RelativeDoublePointPerturbation

def cutoff (t : ℝ) : ℝ := expNegInvGlue t * expNegInvGlue (1 - t)

theorem contDiff_cutoff : ContDiff ℝ ∞ cutoff :=
  expNegInvGlue.contDiff.mul (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))

theorem cutoff_pos {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : 0 < cutoff t :=
  mul_pos (expNegInvGlue.pos_of_pos ht.1) (expNegInvGlue.pos_of_pos (sub_pos.mpr ht.2))

theorem cutoff_zero {t : ℝ} (ht : t ≤ 0 ∨ 1 ≤ t) : cutoff t = 0 := by
  rcases ht with ht | ht
  · rw [cutoff, expNegInvGlue.zero_of_nonpos ht, zero_mul]
  · rw [cutoff, expNegInvGlue.zero_of_nonpos (sub_nonpos.mpr ht), mul_zero]

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

def domain (E : Type) [NormedAddCommGroup E] : Opens (ℝ × (E × E)) :=
  ⟨{q | q.2.1 ≠ q.2.2 ∧ q.1 ∈ Ioo (0 : ℝ) 1},
    (DoublePointPerturbation.distinctDomain E).isOpen.inter
      (isOpen_Ioo.preimage continuous_fst)⟩

def perturb (f : ℝ → E → F) (A : E →L[ℝ] F) (t : ℝ) (x : E) : F :=
  f t x + cutoff t • A x

def direction (q : ℝ × (E × E)) : E :=
  cutoff q.1 • DoublePointPerturbation.direction q

def difference (f : ℝ → E → F) (A : E →L[ℝ] F) (q : ℝ × (E × E)) : F :=
  DoublePointPerturbation.baseDifference f q + A (direction q)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem perturb_eq_outside (f : ℝ → E → F) (A : E →L[ℝ] F) {t : ℝ}
    (ht : t ≤ 0 ∨ 1 ≤ t) (x : E) : perturb f A t x = f t x := by
  rw [perturb, cutoff_zero ht, zero_smul, add_zero]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem contDiff_perturb (f : ℝ → E → F) (hf : ContDiff ℝ ∞ (uncurry f))
    (A : E →L[ℝ] F) : ContDiff ℝ ∞ (uncurry (perturb f A)) :=
  hf.add ((contDiff_cutoff.comp contDiff_fst).smul (A.contDiff.comp contDiff_snd))

omit [FiniteDimensional ℝ E] in
theorem contDiff_direction : ContDiff ℝ ∞ (direction (E := E)) :=
  (contDiff_cutoff.comp contDiff_fst).smul DoublePointPerturbation.contDiff_direction

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem difference_eq (f : ℝ → E → F) (A : E →L[ℝ] F) (q : ℝ × (E × E)) :
    difference f A q = perturb f A q.1 q.2.1 - perturb f A q.1 q.2.2 := by
  simp only [difference, DoublePointPerturbation.baseDifference, direction,
    DoublePointPerturbation.direction, perturb, map_smul, map_sub, smul_sub]
  abel

theorem dense_regular_operators (f : ℝ → E → F) (hf : ContDiff ℝ ∞ (uncurry f)) :
    Dense {A : E →L[ℝ] F | ∀ q : ℝ × (E × E), q.2.1 ≠ q.2.2 →
      q.1 ∈ Ioo (0 : ℝ) 1 → difference f A q = 0 →
        Surjective (fderiv ℝ (difference f A) q)} := by
  have h := ParametricRegular.dense_affine_regular_operators_on
    (DoublePointPerturbation.baseDifference f) direction
    (DoublePointPerturbation.contDiff_baseDifference f hf) contDiff_direction (domain E)
    (fun q hq ↦ smul_ne_zero (cutoff_pos hq.2).ne' (sub_ne_zero.mpr hq.1))
  apply h.mono
  intro A hA q hq ht hz
  exact hA q ⟨hq, ht⟩ hz

theorem exists_small_regular_operator (f : ℝ → E → F)
    (hf : ContDiff ℝ ∞ (uncurry f)) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : E →L[ℝ] F, ‖A‖ < ε ∧
      (∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ x, perturb f A t x = f t x) ∧
      ∀ q : ℝ × (E × E), q.2.1 ≠ q.2.2 → q.1 ∈ Ioo (0 : ℝ) 1 →
        difference f A q = 0 → Surjective (fderiv ℝ (difference f A) q) := by
  obtain ⟨A, hA, hsmall⟩ := (dense_regular_operators f hf).exists_dist_lt 0 hε
  exact ⟨A, by simpa only [dist_zero_left] using hsmall,
    fun _ ht x ↦ perturb_eq_outside f A ht x, hA⟩

end NoExoticSixSphere.RelativeDoublePointPerturbation
