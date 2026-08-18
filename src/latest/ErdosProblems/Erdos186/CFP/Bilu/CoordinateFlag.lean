import ErdosProblems.Erdos186.CFP.Bilu.VolumeSections

namespace Erdos186.CFP.Bilu.VolumeSections

open MeasureTheory Set Module
open scoped ENNReal

/-- The base hyperplane of a coordinate cone, as a linear isometric embedding. -/
noncomputable def coneBaseEmbedding (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] ConeProduct n where
  toFun x := conePair 0 x
  map_add' x y := by
    apply (MeasurableEquiv.toLp 2
      (ℝ × EuclideanSpace ℝ (Fin n))).symm.injective
    simp [conePair]
  map_smul' c x := by
    apply (MeasurableEquiv.toLp 2
      (ℝ × EuclideanSpace ℝ (Fin n))).symm.injective
    simp [conePair]
  norm_map' x := by
    simp [conePair]

@[simp]
theorem coneBaseEmbedding_apply (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    coneBaseEmbedding n x = conePair 0 x := rfl

/-- Append one zero coordinate to a coordinate Euclidean vector. -/
noncomputable def coordinateSuccessorEmbedding (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)) :=
  (coneProductEquivSuccessor n).toLinearIsometry.comp (coneBaseEmbedding n)

@[simp]
theorem coordinateSuccessorEmbedding_apply (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    coordinateSuccessorEmbedding n x =
      coneProductEquivSuccessor n (conePair 0 x) := rfl

/-- Iterated standard zero-extension from `ℝ^(d+i)` to `ℝ^(d+k)`. -/
noncomputable def coordinateFlagEmbedding (d : ℕ) {i k : ℕ} (hi : i ≤ k) :
    EuclideanSpace ℝ (Fin (d + i)) →ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (d + k)) :=
  Nat.leRecOn (C := fun j ↦
      EuclideanSpace ℝ (Fin (d + i)) →ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin (d + j))) hi
    (fun {j} F ↦ (coordinateSuccessorEmbedding (d + j)).comp F)
    (LinearIsometryEquiv.refl ℝ
      (EuclideanSpace ℝ (Fin (d + i)))).toLinearIsometry

@[simp]
theorem coordinateFlagEmbedding_self (d i : ℕ) :
    coordinateFlagEmbedding d (Nat.le_refl i) =
      (LinearIsometryEquiv.refl ℝ
        (EuclideanSpace ℝ (Fin (d + i)))).toLinearIsometry := by
  exact Nat.leRecOn_self _

@[simp]
theorem coordinateFlagEmbedding_succ (d : ℕ) {i k : ℕ}
    (hi : i ≤ k) :
    coordinateFlagEmbedding d (Nat.le_succ_of_le hi) =
      (coordinateSuccessorEmbedding (d + k)).comp
        (coordinateFlagEmbedding d hi) := by
  exact Nat.leRecOn_succ hi _

/-- The standard cone identification, with the target dimension written
in the associativity convention used by an indexed flag. -/
noncomputable def coordinateConeSuccessor (d i : ℕ) :
    ConeProduct (d + i) →ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (d + (i + 1))) :=
  (coneProductEquivSuccessor (d + i)).toLinearIsometry

@[simp]
theorem coordinateConeSuccessor_base (d i : ℕ)
    (x : EuclideanSpace ℝ (Fin (d + i))) :
    coordinateConeSuccessor d i (conePair 0 x) =
      coordinateSuccessorEmbedding (d + i) x := by
  rfl

/-- Extending first from stage `i` to `i+1` and then to `k` agrees with
the direct standard zero-extension from `i` to `k`. -/
theorem coordinateFlagEmbedding_compat {d i k : ℕ} (hi : i < k)
    (x : EuclideanSpace ℝ (Fin (d + i))) :
    coordinateFlagEmbedding d (Nat.succ_le_of_lt hi)
        (coordinateSuccessorEmbedding (d + i) x) =
      coordinateFlagEmbedding d hi.le x := by
  let motive := fun (j : ℕ) (hj : i + 1 ≤ j) ↦
    ∀ y : EuclideanSpace ℝ (Fin (d + i)),
      coordinateFlagEmbedding d hj (coordinateSuccessorEmbedding (d + i) y) =
        coordinateFlagEmbedding d
          (Nat.le_trans (Nat.le_succ i) hj) y
  have hrec : ∀ {j} (hj : i + 1 ≤ j), motive j hj := by
    apply Nat.leRec (motive := motive)
    · intro y
      rw [coordinateFlagEmbedding_self,
        coordinateFlagEmbedding_succ d (Nat.le_refl i)]
      simp
    · intro j hj ih y
      rw [coordinateFlagEmbedding_succ d hj,
        coordinateFlagEmbedding_succ d
          (Nat.le_trans (Nat.le_succ i) hj)]
      exact congrArg (coordinateSuccessorEmbedding (d + j)) (ih y)
  exact hrec (Nat.succ_le_of_lt hi) x

/-- Canonical ambient coordinate flag into `ℝ^(d+k)`. -/
noncomputable def canonicalCoordinateFlagF (d k : ℕ) :
    (i : ℕ) → i ≤ k →
      EuclideanSpace ℝ (Fin (d + i)) →ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin (d + k)) :=
  fun _ hi ↦ coordinateFlagEmbedding d hi

/-- Canonical successor maps used by the coordinate cone chain. -/
noncomputable def canonicalCoordinateFlagG (d k : ℕ) :
    (i : ℕ) → i < k → ConeProduct (d + i) →ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (d + (i + 1))) :=
  fun i _ ↦ coordinateConeSuccessor d i

theorem canonicalCoordinateFlag_compat (d k : ℕ) :
    ∀ i (hi : i < k) x,
      canonicalCoordinateFlagF d k (i + 1) (Nat.succ_le_of_lt hi)
          (canonicalCoordinateFlagG d k i hi (conePair 0 x)) =
        canonicalCoordinateFlagF d k i hi.le x := by
  intro i hi x
  rw [canonicalCoordinateFlagG, coordinateConeSuccessor_base]
  exact coordinateFlagEmbedding_compat hi x

@[simp]
theorem canonicalCoordinateFlagF_terminal (d k : ℕ) :
    canonicalCoordinateFlagF d k k (Nat.le_refl k) =
      (LinearIsometryEquiv.refl ℝ
        (EuclideanSpace ℝ (Fin (d + k)))).toLinearIsometry := by
  exact coordinateFlagEmbedding_self d k

/-- Transport the canonical coordinate flag through a fixed terminal
linear isometric embedding. -/
noncomputable def transportedCoordinateFlagF {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (d k : ℕ) (u : EuclideanSpace ℝ (Fin (d + k)) →ₗᵢ[ℝ] X) :
    (i : ℕ) → i ≤ k →
      EuclideanSpace ℝ (Fin (d + i)) →ₗᵢ[ℝ] X :=
  fun i hi ↦ u.comp (canonicalCoordinateFlagF d k i hi)

theorem transportedCoordinateFlag_compat {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (d k : ℕ) (u : EuclideanSpace ℝ (Fin (d + k)) →ₗᵢ[ℝ] X) :
    ∀ i (hi : i < k) x,
      transportedCoordinateFlagF d k u (i + 1) (Nat.succ_le_of_lt hi)
          (canonicalCoordinateFlagG d k i hi (conePair 0 x)) =
        transportedCoordinateFlagF d k u i hi.le x := by
  intro i hi x
  exact congrArg u (canonicalCoordinateFlag_compat d k i hi x)

@[simp]
theorem transportedCoordinateFlagF_terminal {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (d k : ℕ) (u : EuclideanSpace ℝ (Fin (d + k)) →ₗᵢ[ℝ] X) :
    transportedCoordinateFlagF d k u k (Nat.le_refl k) = u := by
  ext x
  simp [transportedCoordinateFlagF, canonicalCoordinateFlagF]

/-- Exact section estimate for the canonical coordinate flag.  Unlike
`origin_centered_linear_section_bound_of_isometric_flag`, this interface
has no user-supplied flag maps or compatibility premise. -/
theorem origin_centered_coordinate_section_bound
    {d k : ℕ} {rho : ℝ}
    {B : Set (EuclideanSpace ℝ (Fin (d + k)))}
    (hrho : 0 < rho) (hB : MeasurableSet B) (hconv : Convex ℝ B)
    (hball : Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin (d + k))) rho ⊆ B) :
    ((d.factorial : ℝ≥0∞) * ENNReal.ofReal (rho ^ k)) *
        intrinsicVolume d
          ((canonicalCoordinateFlagF d k 0 (Nat.zero_le k)) ⁻¹' B) ≤
      ((d + k).factorial : ℝ≥0∞) * intrinsicVolume (d + k) B := by
  exact origin_centered_linear_section_bound_of_isometric_flag
    hrho hB hconv hball (canonicalCoordinateFlagF d k)
      (canonicalCoordinateFlagG d k) (canonicalCoordinateFlag_compat d k)

/-- Solved-for-section form of the canonical coordinate estimate.  This
is the coefficient shape used by the subsequent geometry synthesis. -/
theorem intrinsicVolume_canonical_section_le
    {d k : ℕ} {rho : ℝ}
    {B : Set (EuclideanSpace ℝ (Fin (d + k)))}
    (hrho : 0 < rho) (hB : MeasurableSet B) (hconv : Convex ℝ B)
    (hball : Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin (d + k))) rho ⊆ B) :
    intrinsicVolume d
        ((canonicalCoordinateFlagF d k 0 (Nat.zero_le k)) ⁻¹' B) ≤
      (((d.factorial : ℝ≥0∞) * ENNReal.ofReal (rho ^ k))⁻¹ *
        ((d + k).factorial : ℝ≥0∞)) * intrinsicVolume (d + k) B := by
  let a : ℝ≥0∞ := (d.factorial : ℝ≥0∞) * ENNReal.ofReal (rho ^ k)
  have ha0 : a ≠ 0 := by
    dsimp [a]
    positivity
  have hatop : a ≠ ∞ := by
    dsimp [a]
    finiteness
  have hcross := origin_centered_coordinate_section_bound
    hrho hB hconv hball
  calc
    intrinsicVolume d
        ((canonicalCoordinateFlagF d k 0 (Nat.zero_le k)) ⁻¹' B) =
        a⁻¹ * (a * intrinsicVolume d
          ((canonicalCoordinateFlagF d k 0 (Nat.zero_le k)) ⁻¹' B)) := by
      symm
      exact ENNReal.inv_mul_cancel_left ha0 hatop
    _ ≤ a⁻¹ * (((d + k).factorial : ℝ≥0∞) *
          intrinsicVolume (d + k) B) :=
      mul_le_mul_right hcross a⁻¹
    _ = (((d.factorial : ℝ≥0∞) * ENNReal.ofReal (rho ^ k))⁻¹ *
          ((d + k).factorial : ℝ≥0∞)) * intrinsicVolume (d + k) B := by
      dsimp [a]
      ac_rfl

/-- Ambient isometric-embedding form of the canonical coordinate-flag
estimate.  The pullback is along the transported initial coordinate plane. -/
theorem origin_centered_transported_coordinate_section_bound
    {d k : ℕ} {rho : ℝ} {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X]
    (u : EuclideanSpace ℝ (Fin (d + k)) →ₗᵢ[ℝ] X)
    {B : Set X} (hrho : 0 < rho) (hB : MeasurableSet B)
    (hconv : Convex ℝ B) (hball : Metric.closedBall (0 : X) rho ⊆ B) :
    ((d.factorial : ℝ≥0∞) * ENNReal.ofReal (rho ^ k)) *
        intrinsicVolume d
          ((transportedCoordinateFlagF d k u 0 (Nat.zero_le k)) ⁻¹' B) ≤
      ((d + k).factorial : ℝ≥0∞) * intrinsicVolume (d + k) B := by
  exact origin_centered_linear_section_bound_of_isometric_flag
    hrho hB hconv hball (transportedCoordinateFlagF d k u)
      (canonicalCoordinateFlagG d k)
      (transportedCoordinateFlag_compat d k u)

/-- Equivalence specialization of the transported coordinate flag. -/
theorem origin_centered_equiv_coordinate_section_bound
    {d k : ℕ} {rho : ℝ} {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X]
    (u : EuclideanSpace ℝ (Fin (d + k)) ≃ₗᵢ[ℝ] X)
    {B : Set X} (hrho : 0 < rho) (hB : MeasurableSet B)
    (hconv : Convex ℝ B) (hball : Metric.closedBall (0 : X) rho ⊆ B) :
    ((d.factorial : ℝ≥0∞) * ENNReal.ofReal (rho ^ k)) *
        intrinsicVolume d
          ((transportedCoordinateFlagF d k u.toLinearIsometry 0
            (Nat.zero_le k)) ⁻¹' B) ≤
      ((d + k).factorial : ℝ≥0∞) * intrinsicVolume (d + k) B :=
  origin_centered_transported_coordinate_section_bound
    u.toLinearIsometry hrho hB hconv hball

#print axioms canonicalCoordinateFlag_compat
#print axioms origin_centered_coordinate_section_bound
#print axioms intrinsicVolume_canonical_section_le

end Erdos186.CFP.Bilu.VolumeSections
