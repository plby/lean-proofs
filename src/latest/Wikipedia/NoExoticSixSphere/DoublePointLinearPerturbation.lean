import Wikipedia.NoExoticSixSphere.ParametricAffineEvaluation

/-!
# Small actual perturbations make the off-diagonal double-point equation regular

For a smooth Euclidean family, perturb each slice by the same small linear
map. On distinct source pairs the parameter derivative evaluates that linear
map at their nonzero difference, so the proved parametric theorem applies.
The conclusion concerns the derivative of the actual perturbed difference
map. Endpoint fixing and singularity normal forms are not asserted here.
-/

noncomputable section

open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.DoublePointPerturbation

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

def distinctDomain (E : Type) [NormedAddCommGroup E] : Opens (ℝ × (E × E)) :=
  ⟨{q | q.2.1 ≠ q.2.2},
    (isClosed_eq (continuous_fst.comp continuous_snd)
      (continuous_snd.comp continuous_snd)).isOpen_compl⟩

def perturb (f : ℝ → E → F) (A : E →L[ℝ] F) (t : ℝ) (x : E) : F := f t x + A x

def baseDifference (f : ℝ → E → F) (q : ℝ × (E × E)) : F :=
  f q.1 q.2.1 - f q.1 q.2.2

def direction (q : ℝ × (E × E)) : E := q.2.1 - q.2.2

def difference (f : ℝ → E → F) (A : E →L[ℝ] F) (q : ℝ × (E × E)) : F :=
  baseDifference f q + A (direction q)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem difference_eq (f : ℝ → E → F) (A : E →L[ℝ] F) (q : ℝ × (E × E)) :
    difference f A q = perturb f A q.1 q.2.1 - perturb f A q.1 q.2.2 := by
  simp only [difference, baseDifference, direction, perturb, map_sub]
  abel

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem contDiff_perturb (f : ℝ → E → F) (hf : ContDiff ℝ ∞ (uncurry f))
    (A : E →L[ℝ] F) : ContDiff ℝ ∞ (uncurry (perturb f A)) :=
  hf.add (A.contDiff.comp contDiff_snd)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem contDiff_baseDifference (f : ℝ → E → F) (hf : ContDiff ℝ ∞ (uncurry f)) :
    ContDiff ℝ ∞ (baseDifference f) :=
  (hf.comp (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd))).sub
    (hf.comp (contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)))

omit [FiniteDimensional ℝ E] in
theorem contDiff_direction : ContDiff ℝ ∞ (direction (E := E)) :=
  (contDiff_fst.comp contDiff_snd).sub (contDiff_snd.comp contDiff_snd)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem contDiff_difference (f : ℝ → E → F) (hf : ContDiff ℝ ∞ (uncurry f))
    (A : E →L[ℝ] F) : ContDiff ℝ ∞ (difference f A) :=
  (contDiff_baseDifference f hf).add (A.contDiff.comp contDiff_direction)

theorem dense_regular_operators (f : ℝ → E → F) (hf : ContDiff ℝ ∞ (uncurry f)) :
    Dense {A : E →L[ℝ] F | ∀ q : ℝ × (E × E), q.2.1 ≠ q.2.2 → difference f A q = 0 →
      Surjective (fderiv ℝ (difference f A) q)} :=
  ParametricRegular.dense_affine_regular_operators_on (baseDifference f) direction
    (contDiff_baseDifference f hf) contDiff_direction (distinctDomain E)
    (fun _ h ↦ sub_ne_zero.mpr h)

theorem exists_small_regular_operator (f : ℝ → E → F)
    (hf : ContDiff ℝ ∞ (uncurry f)) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : E →L[ℝ] F, ‖A‖ < ε ∧
      ∀ q : ℝ × (E × E), q.2.1 ≠ q.2.2 → difference f A q = 0 →
        Surjective (fderiv ℝ (difference f A) q) := by
  obtain ⟨A, hA, hsmall⟩ := (dense_regular_operators f hf).exists_dist_lt 0 hε
  exact ⟨A, by simpa only [dist_zero_left] using hsmall, hA⟩

end NoExoticSixSphere.DoublePointPerturbation
