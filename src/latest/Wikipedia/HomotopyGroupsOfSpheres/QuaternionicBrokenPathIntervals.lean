import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBrokenPaths

/-! # A broken-path deformation agrees with its local replacement on each cell -/

open Set unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Exponential.BrokenPaths

open NoExoticSixSphere.IntervalCoordinates NoExoticSixSphere.OrthogonalPaths.ColumnLift

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

theorem deformation_on_interval (H : C(I × X, symplecticSubgroup n))
    (t : ℕ → I) (hmono : Monotone t)
    (hsmall : ∀ i, ∀ u ∈ Icc (t i) (t (i + 1)), ∀ x,
      (H (t i, x))⁻¹ * H (u, x) ∈ compatibleDomain n)
    (N i : ℕ) (hi : i < N) (r v : I) (x : X) (hv : v ∈ Icc (t i) (t (i + 1))) :
    deformation H t hmono hsmall N (r, (v, x)) =
      IntervalReplacement.lifted H (t i) (t (i + 1)) (hmono i.le_succ) (hsmall i) (r, (v, x)) := by
  have hother : ∀ j < N, j ≠ i → correctionAt H t hmono hsmall j (r, (v, x)) = 1 := by
    intro j _ hji
    rcases lt_or_gt_of_ne hji with hj | hj
    · exact IntervalReplacement.correction_after H (t j) (t (j + 1))
        (hmono j.le_succ) (hsmall j) r v x
        ((hmono (Nat.succ_le_of_lt hj)).trans hv.1)
    · exact IntervalReplacement.correction_before H (t j) (t (j + 1))
        (hmono j.le_succ) (hsmall j) r v x
        (hv.2.trans (hmono (Nat.succ_le_of_lt hj)))
  change ((List.range N).map (fun j ↦ correctionAt H t hmono hsmall j (r, (v, x)))).prod *
    H (v, x) = _
  rw [NoExoticSixSphere.OrthogonalExponential.BrokenPaths.list_range_prod_eq_single _ hi hother]
  change IntervalReplacement.correction H (t i) (t (i + 1))
    (hmono i.le_succ) (hsmall i) (r, (v, x)) * H (v, x) = _
  rw [IntervalReplacement.correction_apply, clip_of_ge hv.1, min_eq_left hv.2,
    mul_assoc, inv_mul_cancel, mul_one]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Exponential.BrokenPaths
