import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Negative and positive Euclidean factors of a signed Morse chart

The actual coordinate space is split by its signs. The two factors have
Euclidean norms, and the signed sum is exactly the difference of their
squared norms. Empty factors are allowed, so this also covers extrema.
-/

noncomputable section

open Set

namespace Wikipedia.SmoothSixDPoincare.MorseHandle

variable {ι : Type*} [Fintype ι]

abbrev Negative (w : ι → ℝ) := {i // w i = -1}
abbrev Positive (w : ι → ℝ) := {i // w i ≠ -1}
abbrev NegativeSpace (w : ι → ℝ) := EuclideanSpace ℝ (Negative w)
abbrev PositiveSpace (w : ι → ℝ) := EuclideanSpace ℝ (Positive w)

open Classical in
/-- Coordinate restriction, followed by the Euclidean norm on each factor. -/
def splitLinearEquiv (w : ι → ℝ) :
    (ι → ℝ) ≃ₗ[ℝ] (NegativeSpace w × PositiveSpace w) := by
  let e : (ι → ℝ) ≃ₗ[ℝ] ((Negative w → ℝ) × (Positive w → ℝ)) :=
    { toEquiv := Equiv.piEquivPiSubtypeProd (fun i => w i = -1) (fun _ => ℝ)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact e.trans (LinearEquiv.prodCongr
    (WithLp.linearEquiv 2 ℝ (Negative w → ℝ)).symm
    (WithLp.linearEquiv 2 ℝ (Positive w → ℝ)).symm)

open Classical in
/-- The signed splitting is a genuine continuous linear equivalence. -/
def splitCoordinates (w : ι → ℝ) :
    (ι → ℝ) ≃L[ℝ] (NegativeSpace w × PositiveSpace w) :=
  (splitLinearEquiv w).toContinuousLinearEquiv

open Classical in
@[simp] theorem splitCoordinates_fst_apply (w : ι → ℝ) (z : ι → ℝ) (i : Negative w) :
    (splitCoordinates w z).1 i = z i.1 := rfl

open Classical in
@[simp] theorem splitCoordinates_snd_apply (w : ι → ℝ) (z : ι → ℝ) (i : Positive w) :
    (splitCoordinates w z).2 i = z i.1 := rfl

open Classical in
/-- The signed quadratic form is minus the negative norm squared plus the positive norm squared. -/
theorem signedSum_eq_norms (w : ι → ℝ) (hw : ∀ i, w i = -1 ∨ w i = 1) (z : ι → ℝ) :
    ∑ i, w i * (z i) ^ 2 =
      -‖(splitCoordinates w z).1‖ ^ 2 + ‖(splitCoordinates w z).2‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  have hneg : (∑ i : Negative w, w i.1 * (z i.1) ^ 2) =
      -∑ i : Negative w, (z i.1) ^ 2 := by
    calc
      _ = ∑ i : Negative w, -(z i.1) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [i.2, neg_one_mul]
      _ = _ := by rw [Finset.sum_neg_distrib]
  have hpos : (∑ i : Positive w, w i.1 * (z i.1) ^ 2) =
      ∑ i : Positive w, (z i.1) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [(hw i.1).resolve_left i.2, one_mul]
  calc
    ∑ i, w i * (z i) ^ 2 =
        (∑ i : Negative w, w i.1 * (z i.1) ^ 2) +
          ∑ i : Positive w, w i.1 * (z i.1) ^ 2 :=
      (Fintype.sum_subtype_add_sum_subtype (fun i => w i = -1)
        (fun i => w i * (z i) ^ 2)).symm
    _ = _ := by rw [hneg, hpos]; rfl

open Classical in
/-- The same quadratic identity in inverse product coordinates. -/
theorem signedSum_symm_eq_norms (w : ι → ℝ) (hw : ∀ i, w i = -1 ∨ w i = 1)
    (z : NegativeSpace w × PositiveSpace w) :
    ∑ i, w i * ((splitCoordinates w).symm z i) ^ 2 = -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    signedSum_eq_norms w hw ((splitCoordinates w).symm z)

end Wikipedia.SmoothSixDPoincare.MorseHandle
