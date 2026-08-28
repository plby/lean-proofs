import Wikipedia.NoExoticSixSphere.OrthogonalIntervalReplacement

/-!
# Global replacement by finitely many exponential segments

Local corrections equal the identity off their time intervals. Their ordered
product therefore assembles a continuous homotopy, fixing both endpoint slices
and every stationary parameter, with the claimed exponential formula on each
subdivision interval.
-/

open Set unitInterval

namespace NoExoticSixSphere.OrthogonalExponential.BrokenPaths

open GLOrthonormalization CayleyTransform IntervalCoordinates

theorem list_range_prod_eq_single {G : Type*} [Monoid G] (f : ℕ → G)
    {N i : ℕ} (hi : i < N) (hother : ∀ j < N, j ≠ i → f j = 1) :
    ((List.range N).map f).prod = f i := by
  induction N with
  | zero => exact (Nat.not_lt_zero i hi).elim
  | succ N ih =>
    rw [List.prod_range_succ]
    by_cases heq : i = N
    · subst i
      have hp : ((List.range N).map f).prod = 1 := by
        apply List.prod_eq_one
        intro a ha
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
        have hjN := List.mem_range.mp hj
        exact hother j (hjN.trans N.lt_succ_self) (Nat.ne_of_lt hjN)
      rw [hp, one_mul]
    · have hiN : i < N := lt_of_le_of_ne (Nat.le_of_lt_succ hi) heq
      rw [ih hiN (fun j hj hji ↦ hother j (hj.trans N.lt_succ_self) hji),
        hother N N.lt_succ_self (Ne.symm heq), mul_one]

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
variable (H : C(I × X, OrthogonalOperators n)) (t : ℕ → I) (hmono : Monotone t)
  (hsmall : ∀ i, ∀ u ∈ Icc (t i) (t (i + 1)), ∀ x,
    (H (t i, x))⁻¹ * H (u, x) ∈ (logarithmChart n).source)

noncomputable def correctionAt (i : ℕ) : C(I × (I × X), OrthogonalOperators n) :=
  IntervalReplacement.correction H (t i) (t (i + 1)) (hmono i.le_succ) (hsmall i)

variable (N : ℕ)

noncomputable def deformation : C(I × (I × X), OrthogonalOperators n) where
  toFun q := ((List.range N).map (fun i ↦ correctionAt H t hmono hsmall i q)).prod * H q.2
  continuous_toFun :=
    (continuous_list_prod (List.range N) (fun i _ ↦
      (correctionAt H t hmono hsmall i).continuous)).mul (H.continuous.comp continuous_snd)

noncomputable def ending : C(I × X, OrthogonalOperators n) :=
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
  rw [list_range_prod_eq_single _ hi hother]
  exact IntervalReplacement.correction_one_mul H (t i) (t (i + 1))
    (hmono i.le_succ) (hsmall i) v x hv

end NoExoticSixSphere.OrthogonalExponential.BrokenPaths

namespace NoExoticSixSphere.OrthogonalExponential

open GLOrthonormalization CayleyTransform IntervalCoordinates

/-- Every compact path family can be replaced by finitely many actual exponential segments,
relative to both endpoint slices and any specified stationary parameters. -/
theorem exists_brokenExponentialHomotopy {n : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (H : C(I × X, OrthogonalOperators n)) (S : Set X)
    (hS : ∀ x ∈ S, ∀ u, H (u, x) = H (0, x)) :
    ∃ N : ℕ, ∃ t : ℕ → I, ∃ K : ℕ → C(X, SkewOperators n),
      ∃ G : C(I × X, OrthogonalOperators n),
        t 0 = 0 ∧ Monotone t ∧ t N = 1 ∧
        Nonempty (H.HomotopyRel G {p | p.1 = 0 ∨ p.1 = 1 ∨ p.2 ∈ S}) ∧
        ∀ i < N, ∀ u ∈ Icc (t i) (t (i + 1)), ∀ x,
          G (u, x) = H (t i, x) * exp ((normalize (t i) (t (i + 1)) u : ℝ) • K i x) := by
  obtain ⟨t, ht0, hmono, ⟨N, hN⟩, hsmall⟩ := exists_logarithmSubdivision H
  let K (i : ℕ) := logarithmicIncrement H (t i) (t (i + 1))
    (fun x ↦ hsmall i (t (i + 1)) ⟨hmono i.le_succ, le_rfl⟩ x)
  refine ⟨N, t, K, BrokenPaths.ending H t hmono hsmall N, ht0, hmono, hN N le_rfl,
    ⟨BrokenPaths.homotopyRel H t hmono hsmall N S hS⟩, ?_⟩
  intro i hi u hu x
  exact BrokenPaths.ending_on_interval H t hmono hsmall N i hi u x hu

end NoExoticSixSphere.OrthogonalExponential
