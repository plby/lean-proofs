/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Ford's order-statistics volume

This file introduces the ordered simplex and the quantity `Qₖ(u,v)` from
Section 4 of Kevin Ford's short paper *Integers with a divisor in (y,2y]*.
Coordinates are indexed by `Fin k`; thus coordinate `i` below is Ford's
`(i+1)`-st order statistic.
-/

namespace Erdos896.Ford

open MeasureTheory Set
open scoped Pointwise ENNReal

/-- The closed ordered simplex `a ≤ x₀ ≤ x₁ ≤ ... ≤ xₖ₋₁ ≤ b`. -/
def orderedSimplex (k : ℕ) (a b : ℝ) : Set (Fin k → ℝ) :=
  {x | (∀ i, a ≤ x i ∧ x i ≤ b) ∧ Monotone x}

/-- Ford's region `Sₖ(u,v)`: the ordered unit simplex subject to
`xᵢ ≥ (i+1-u)/v`. -/
def orderQSet (k : ℕ) (u v : ℝ) : Set (Fin k → ℝ) :=
  {x ∈ orderedSimplex k 0 1 |
    ∀ i, ((((i : Fin k) : ℕ) : ℝ) + 1 - u) / v ≤ x i}

/-- Ford's order-statistics probability.  The density of the increasing
rearrangement of `k` independent uniform random variables is `k!` on the
ordered simplex. -/
noncomputable def orderQ (k : ℕ) (u v : ℝ) : ℝ :=
  (k.factorial : ℝ) * (volume (orderQSet k u v)).toReal

theorem measurableSet_orderedSimplex (k : ℕ) (a b : ℝ) :
    MeasurableSet (orderedSimplex k a b) := by
  have hclosed : IsClosed (orderedSimplex k a b) := by
    change IsClosed
      ({x : Fin k → ℝ | ∀ i, a ≤ x i ∧ x i ≤ b} ∩
        {x : Fin k → ℝ | Monotone x})
    apply IsClosed.inter
    · rw [show {x : Fin k → ℝ | ∀ i, a ≤ x i ∧ x i ≤ b} =
          ⋂ i, {x | a ≤ x i ∧ x i ≤ b} by ext; simp]
      exact isClosed_iInter fun i ↦
        (isClosed_le continuous_const (continuous_apply i)).inter
          (isClosed_le (continuous_apply i) continuous_const)
    · rw [show {x : Fin k → ℝ | Monotone x} =
          ⋂ i, ⋂ j, ⋂ (_h : i ≤ j), {x | x i ≤ x j} by
            ext x
            simp only [mem_ofPred_eq, mem_iInter]
            exact Iff.rfl]
      exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun _ ↦
        isClosed_le (continuous_apply i) (continuous_apply j)
  exact hclosed.measurableSet

theorem measurableSet_orderQSet (k : ℕ) (u v : ℝ) :
    MeasurableSet (orderQSet k u v) := by
  apply (measurableSet_orderedSimplex k 0 1).inter
  have h : MeasurableSet
      (⋂ i, {x : Fin k → ℝ |
        ((((i : Fin k) : ℕ) : ℝ) + 1 - u) / v ≤ x i}) :=
    MeasurableSet.iInter fun i ↦
      measurableSet_le
        (show Measurable (fun _ : Fin k → ℝ ↦
          ((((i : Fin k) : ℕ) : ℝ) + 1 - u) / v) from measurable_const)
        (show Measurable (fun x : Fin k → ℝ ↦ x i) from measurable_pi_apply i)
  rw [show (fun x : Fin k → ℝ ↦
      ∀ i, ((((i : Fin k) : ℕ) : ℝ) + 1 - u) / v ≤ x i) =
      (fun x ↦ x ∈ ⋂ i, {y : Fin k → ℝ |
        ((((i : Fin k) : ℕ) : ℝ) + 1 - u) / v ≤ y i}) by
        funext x
        simp]
  exact h

/-! ## Exact volume of an ordered interval -/

/-- Permute the coordinates of a finite real tuple. -/
def permuteCoordinates {k : ℕ} (σ : Equiv.Perm (Fin k))
    (x : Fin k → ℝ) : Fin k → ℝ := x ∘ σ

/-- The chamber in the box `[a,b]^k` whose coordinates are ordered by `σ`. -/
def orderedChamber (k : ℕ) (a b : ℝ) (σ : Equiv.Perm (Fin k)) :
    Set (Fin k → ℝ) := permuteCoordinates σ ⁻¹' orderedSimplex k a b

theorem measurePreserving_permuteCoordinates {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    MeasurePreserving (permuteCoordinates σ)
      (volume : Measure (Fin k → ℝ)) volume := by
  change MeasurePreserving (fun x i ↦ x (σ i))
    (volume : Measure (Fin k → ℝ)) volume
  simpa [MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft, Equiv.piCongrLeft'] using
    (volume_measurePreserving_piCongrLeft (fun _ : Fin k ↦ ℝ) σ.symm)

theorem measurableSet_orderedChamber (k : ℕ) (a b : ℝ)
    (σ : Equiv.Perm (Fin k)) : MeasurableSet (orderedChamber k a b σ) :=
  (measurePreserving_permuteCoordinates σ).measurable
    (measurableSet_orderedSimplex k a b)

theorem volume_orderedChamber (k : ℕ) (a b : ℝ)
    (σ : Equiv.Perm (Fin k)) :
    volume (orderedChamber k a b σ) = volume (orderedSimplex k a b) := by
  exact (measurePreserving_permuteCoordinates σ).measure_preimage
    (measurableSet_orderedSimplex k a b).nullMeasurableSet

theorem iUnion_orderedChamber (k : ℕ) (a b : ℝ) :
    (⋃ σ : Equiv.Perm (Fin k), orderedChamber k a b σ) =
      Set.Icc (fun _ ↦ a) (fun _ ↦ b) := by
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨σ, hx⟩
    change (x ∘ σ) ∈ orderedSimplex k a b at hx
    exact ⟨fun i ↦ by simpa using (hx.1 (σ.symm i)).1,
      fun i ↦ by simpa using (hx.1 (σ.symm i)).2⟩
  · intro hx
    refine ⟨Tuple.sort x, ?_⟩
    change (x ∘ Tuple.sort x) ∈ orderedSimplex k a b
    exact ⟨fun i ↦ ⟨hx.1 _, hx.2 _⟩, Tuple.monotone_sort x⟩

/-- A coordinate diagonal in finite-dimensional real space has zero volume. -/
theorem volume_coordinateDiagonal_zero {k : ℕ} (p q : Fin k) (hpq : p ≠ q) :
    volume {x : Fin k → ℝ | x p = x q} = 0 := by
  let t : Matrix.TransvectionStruct (Fin k) ℝ := ⟨p, q, hpq, -1⟩
  have hpre : Matrix.toLin' t.toMatrix ⁻¹' {x : Fin k → ℝ | x p = 0} =
      {x : Fin k → ℝ | x p = x q} := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq, Matrix.toLin'_apply]
    simp only [t, Matrix.TransvectionStruct.toMatrix_mk, Matrix.transvection,
      Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq,
      Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    constructor <;> intro h <;> linarith
  rw [← hpre]
  calc
    volume (Matrix.toLin' t.toMatrix ⁻¹' {x : Fin k → ℝ | x p = 0}) =
        volume {x : Fin k → ℝ | x p = 0} :=
      (Real.volume_preserving_transvectionStruct t).measure_preimage
        (measurableSet_eq_fun (measurable_pi_apply p) measurable_const).nullMeasurableSet
    _ = 0 := by
      simpa only [MeasureTheory.volume_pi] using
        (Measure.pi_hyperplane (fun _ : Fin k ↦ (volume : Measure ℝ)) p 0)

theorem orderedChamber_aedisjoint {k : ℕ} {a b : ℝ}
    {σ τ : Equiv.Perm (Fin k)} (hστ : σ ≠ τ) :
    AEDisjoint volume (orderedChamber k a b σ) (orderedChamber k a b τ) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ τ i := by
    by_contra h
    push Not at h
    exact hστ (Equiv.ext h)
  unfold AEDisjoint
  apply measure_mono_null _ (volume_coordinateDiagonal_zero (σ i) (τ i) hi)
  rintro x ⟨hxσ, hxτ⟩
  change (x ∘ σ) ∈ orderedSimplex k a b at hxσ
  change (x ∘ τ) ∈ orderedSimplex k a b at hxτ
  exact congr_fun (Tuple.unique_monotone hxσ.2 hxτ.2) i

/-- Before division by the number of permutation chambers, the ordered
simplex fills its ambient box. -/
theorem factorial_mul_volume_orderedSimplex (k : ℕ) (a b : ℝ) :
    (k.factorial : ℝ≥0∞) * volume (orderedSimplex k a b) =
      ENNReal.ofReal (b - a) ^ k := by
  classical
  have hpair : Set.Pairwise
      (↑(Finset.univ : Finset (Equiv.Perm (Fin k))))
      (Function.onFun (AEDisjoint volume) (orderedChamber k a b)) := by
    intro σ _ τ _ hστ
    exact orderedChamber_aedisjoint hστ
  have hmeasure := measure_biUnion_finset₀ (μ := volume) hpair
    (fun σ _ ↦ (measurableSet_orderedChamber k a b σ).nullMeasurableSet)
  simp only [Finset.mem_univ, iUnion_true, volume_orderedChamber,
    Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul] at hmeasure
  rw [iUnion_orderedChamber, Real.volume_Icc_pi] at hmeasure
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hmeasure.symm

/-- Exact Lebesgue volume of the ordered interval simplex. -/
theorem volume_orderedSimplex (k : ℕ) {a b : ℝ} (hab : a ≤ b) :
    volume (orderedSimplex k a b) =
      ENNReal.ofReal ((b - a) ^ k / (k.factorial : ℝ)) := by
  rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr (Nat.factorial_pos k))]
  rw [ENNReal.ofReal_natCast]
  apply (ENNReal.eq_div_iff (by positivity) (by simp)).2
  rw [ENNReal.ofReal_pow (sub_nonneg.mpr hab)]
  exact factorial_mul_volume_orderedSimplex k a b

/-- Real-valued form of `volume_orderedSimplex`. -/
theorem volume_orderedSimplex_toReal (k : ℕ) {a b : ℝ} (hab : a ≤ b) :
    (volume (orderedSimplex k a b)).toReal =
      (b - a) ^ k / (k.factorial : ℝ) := by
  rw [volume_orderedSimplex k hab, ENNReal.toReal_ofReal]
  positivity

/-- Intersecting a coordinate-permutation-invariant set with any ordered
chamber gives the same volume. -/
theorem volume_inter_orderedChamber_eq {k : ℕ} {E : Set (Fin k → ℝ)}
    (hE : MeasurableSet E)
    (hinv : ∀ (σ : Equiv.Perm (Fin k)) (x : Fin k → ℝ),
      permuteCoordinates σ x ∈ E ↔ x ∈ E)
    (σ : Equiv.Perm (Fin k)) :
    volume (E ∩ orderedChamber k 0 1 σ) =
      volume (E ∩ orderedSimplex k 0 1) := by
  have hpre : permuteCoordinates σ ⁻¹' (E ∩ orderedSimplex k 0 1) =
      E ∩ orderedChamber k 0 1 σ := by
    ext x
    simp only [mem_preimage, mem_inter_iff, orderedChamber]
    exact and_congr (hinv σ x) Iff.rfl
  rw [← hpre]
  exact (measurePreserving_permuteCoordinates σ).measure_preimage
    (hE.inter (measurableSet_orderedSimplex k 0 1)).nullMeasurableSet

/-- Symmetry formula for a measurable permutation-invariant subset of the
unit cube: its volume is `k!` times the volume of its ordered part. -/
theorem volume_eq_factorial_mul_volume_inter_orderedSimplex
    (k : ℕ) {E : Set (Fin k → ℝ)}
    (hE : MeasurableSet E)
    (hsub : E ⊆ Set.Icc (fun _ ↦ (0 : ℝ)) (fun _ ↦ 1))
    (hinv : ∀ (σ : Equiv.Perm (Fin k)) (x : Fin k → ℝ),
      permuteCoordinates σ x ∈ E ↔ x ∈ E) :
    volume E = (k.factorial : ℝ≥0∞) *
      volume (E ∩ orderedSimplex k 0 1) := by
  classical
  have hunion :
      (⋃ σ : Equiv.Perm (Fin k), E ∩ orderedChamber k 0 1 σ) = E := by
    ext x
    simp only [mem_iUnion, mem_inter_iff]
    constructor
    · rintro ⟨σ, hxE, _⟩
      exact hxE
    · intro hxE
      have hxbox := hsub hxE
      have hxunion : x ∈ ⋃ σ : Equiv.Perm (Fin k), orderedChamber k 0 1 σ := by
        rw [iUnion_orderedChamber]
        exact hxbox
      simp only [mem_iUnion] at hxunion
      obtain ⟨σ, hxσ⟩ := hxunion
      exact ⟨σ, hxE, hxσ⟩
  have hpair : Set.Pairwise
      (↑(Finset.univ : Finset (Equiv.Perm (Fin k))))
      (Function.onFun (AEDisjoint volume)
        (fun σ ↦ E ∩ orderedChamber k 0 1 σ)) := by
    intro σ _ τ _ hστ
    exact (orderedChamber_aedisjoint hστ).mono inter_subset_right inter_subset_right
  have hmeasure := measure_biUnion_finset₀ (μ := volume) hpair
    (fun σ _ ↦ (hE.inter (measurableSet_orderedChamber k 0 1 σ)).nullMeasurableSet)
  simp only [Finset.mem_univ, iUnion_true, volume_inter_orderedChamber_eq hE hinv,
    Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul] at hmeasure
  rw [hunion] at hmeasure
  exact hmeasure

theorem orderQSet_subset_orderedSimplex (k : ℕ) (u v : ℝ) :
    orderQSet k u v ⊆ orderedSimplex k 0 1 := by
  exact fun _ hx ↦ hx.1

theorem orderQ_nonneg (k : ℕ) (u v : ℝ) : 0 ≤ orderQ k u v := by
  simp only [orderQ]
  positivity

/-- `Qₖ(u,v)` is at most one, since its region lies in one permutation
chamber of the unit cube. -/
theorem orderQ_le_one (k : ℕ) (u v : ℝ) : orderQ k u v ≤ 1 := by
  unfold orderQ
  calc
    (k.factorial : ℝ) * (volume (orderQSet k u v)).toReal ≤
        (k.factorial : ℝ) * (volume (orderedSimplex k 0 1)).toReal := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact ENNReal.toReal_mono
        (by rw [volume_orderedSimplex k (by norm_num)]; simp)
        (measure_mono (orderQSet_subset_orderedSimplex k u v))
    _ = 1 := by
      rw [volume_orderedSimplex k (by norm_num)]
      rw [ENNReal.toReal_ofReal]
      · norm_num
        field_simp
      · positivity

/-! ## Scaling the order-statistics region -/

/-- The homothetic copy of `Sₖ(u,v)` in an interval of length `t`. -/
def scaledOrderQSet (k : ℕ) (u v t : ℝ) : Set (Fin k → ℝ) :=
  t • orderQSet k u v

/-- Lebesgue volume under the homothety used in Ford's prefix blocks. -/
theorem volume_scaledOrderQSet (k : ℕ) (u v : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    volume (scaledOrderQSet k u v t) =
      ENNReal.ofReal (t ^ k) * volume (orderQSet k u v) := by
  unfold scaledOrderQSet
  rw [Measure.addHaar_smul_of_nonneg volume ht]
  simp

/-- Real-valued version of `volume_scaledOrderQSet`. -/
theorem volume_scaledOrderQSet_toReal (k : ℕ) (u v : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (volume (scaledOrderQSet k u v t)).toReal =
      t ^ k * (volume (orderQSet k u v)).toReal := by
  rw [volume_scaledOrderQSet k u v ht, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg ht k)]

/-- Recover the unnormalized volume from Ford's normalized `Qₖ`. -/
theorem volume_orderQSet_eq (k : ℕ) (u v : ℝ) :
    (volume (orderQSet k u v)).toReal = orderQ k u v / (k.factorial : ℝ) := by
  unfold orderQ
  field_simp

/-- The scaled volume directly in terms of `Qₖ(u,v)`. -/
theorem volume_scaledOrderQSet_eq (k : ℕ) (u v : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (volume (scaledOrderQSet k u v t)).toReal =
      t ^ k * orderQ k u v / (k.factorial : ℝ) := by
  rw [volume_scaledOrderQSet_toReal k u v ht, volume_orderQSet_eq]
  ring

end Erdos896.Ford
