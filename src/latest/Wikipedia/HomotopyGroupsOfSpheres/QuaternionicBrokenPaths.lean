import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicIntervalReplacement
import Wikipedia.NoExoticSixSphere.OrthogonalBrokenPaths

/-!
# Global replacement by finitely many exponential segments

Local corrections equal the identity off their time intervals. Their ordered
product therefore assembles a continuous homotopy, fixing both endpoint slices
and every stationary parameter, with the claimed exponential formula on each
subdivision interval.
-/

open Set unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Exponential.BrokenPaths

open NoExoticSixSphere.IntervalCoordinates

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
variable (H : C(I × X, symplecticSubgroup n)) (t : ℕ → I) (hmono : Monotone t)
  (hsmall : ∀ i, ∀ u ∈ Icc (t i) (t (i + 1)), ∀ x,
    (H (t i, x))⁻¹ * H (u, x) ∈ compatibleDomain n)

noncomputable def correctionAt (i : ℕ) : C(I × (I × X), symplecticSubgroup n) :=
  IntervalReplacement.correction H (t i) (t (i + 1)) (hmono i.le_succ) (hsmall i)

variable (N : ℕ)

noncomputable def deformation : C(I × (I × X), symplecticSubgroup n) where
  toFun q := ((List.range N).map (fun i ↦ correctionAt H t hmono hsmall i q)).prod * H q.2
  continuous_toFun :=
    (continuous_list_prod (List.range N) (fun i _ ↦
      (correctionAt H t hmono hsmall i).continuous)).mul (H.continuous.comp continuous_snd)

noncomputable def ending : C(I × X, symplecticSubgroup n) :=
  (deformation H t hmono hsmall N).comp ⟨fun p ↦ (1, p), continuous_const.prodMk continuous_id⟩

theorem deformation_eq_of_corrections_eq_one (r : I) (p : I × X)
    (hc : ∀ i < N, correctionAt H t hmono hsmall i (r, p) = 1) :
    deformation H t hmono hsmall N (r, p) = H p := by
  change ((List.range N).map (fun i ↦ correctionAt H t hmono hsmall i (r, p))).prod * H p = H p
  have hp : ((List.range N).map (fun i ↦ correctionAt H t hmono hsmall i (r, p))).prod = 1 := by
    apply List.prod_eq_one
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    exact hc i (List.mem_range.mp hi)
  rw [hp, one_mul]

theorem deformation_zero (p : I × X) : deformation H t hmono hsmall N (0, p) = H p := by
  apply deformation_eq_of_corrections_eq_one
  intro i _
  exact IntervalReplacement.correction_zero H (t i) (t (i + 1))
    (hmono i.le_succ) (hsmall i) p.1 p.2

theorem deformation_time_zero (r : I) (x : X) :
    deformation H t hmono hsmall N (r, (0, x)) = H (0, x) := by
  apply deformation_eq_of_corrections_eq_one
  intro i _
  exact IntervalReplacement.correction_before H (t i) (t (i + 1))
    (hmono i.le_succ) (hsmall i) r 0 x bot_le

theorem deformation_time_one (r : I) (x : X) :
    deformation H t hmono hsmall N (r, (1, x)) = H (1, x) := by
  apply deformation_eq_of_corrections_eq_one
  intro i _
  exact IntervalReplacement.correction_after H (t i) (t (i + 1))
    (hmono i.le_succ) (hsmall i) r 1 x le_top

theorem deformation_stationary (r v : I) (x : X) (hx : ∀ u, H (u, x) = H (0, x)) :
    deformation H t hmono hsmall N (r, (v, x)) = H (v, x) := by
  apply deformation_eq_of_corrections_eq_one
  intro i _
  exact IntervalReplacement.correction_stationary H (t i) (t (i + 1))
    (hmono i.le_succ) (hsmall i) r v x hx

noncomputable def homotopyRel (S : Set X)
    (hS : ∀ x ∈ S, ∀ u, H (u, x) = H (0, x)) :
    H.HomotopyRel (ending H t hmono hsmall N) {p | p.1 = 0 ∨ p.1 = 1 ∨ p.2 ∈ S} where
  toContinuousMap := deformation H t hmono hsmall N
  map_zero_left := deformation_zero H t hmono hsmall N
  map_one_left _ := rfl
  prop' r p hp := by
    rcases p with ⟨v, x⟩
    rcases hp with hv | hv | hx
    · change v = 0 at hv
      subst v
      exact deformation_time_zero H t hmono hsmall N r x
    · change v = 1 at hv
      subst v
      exact deformation_time_one H t hmono hsmall N r x
    · exact deformation_stationary H t hmono hsmall N r v x (hS x hx)

theorem ending_on_interval (i : ℕ) (hi : i < N) (v : I) (x : X)
    (hv : v ∈ Icc (t i) (t (i + 1))) :
    ending H t hmono hsmall N (v, x) =
      H (t i, x) * exp ((normalize (t i) (t (i + 1)) v : ℝ) •
        logarithmChart n ((H (t i, x))⁻¹ * H (t (i + 1), x))) := by
  have hother : ∀ j < N, j ≠ i → correctionAt H t hmono hsmall j (1, (v, x)) = 1 := by
    intro j _ hji
    rcases lt_or_gt_of_ne hji with hj | hj
    · exact IntervalReplacement.correction_after H (t j) (t (j + 1))
        (hmono j.le_succ) (hsmall j) 1 v x
        ((hmono (Nat.succ_le_of_lt hj)).trans hv.1)
    · exact IntervalReplacement.correction_before H (t j) (t (j + 1))
        (hmono j.le_succ) (hsmall j) 1 v x
        (hv.2.trans (hmono (Nat.succ_le_of_lt hj)))
  change ((List.range N).map (fun j ↦ correctionAt H t hmono hsmall j (1, (v, x)))).prod *
    H (v, x) = _
  rw [NoExoticSixSphere.OrthogonalExponential.BrokenPaths.list_range_prod_eq_single _ hi hother]
  exact IntervalReplacement.correction_one_mul H (t i) (t (i + 1))
    (hmono i.le_succ) (hsmall i) v x hv

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Exponential.BrokenPaths
