import ErdosProblems.Erdos1166.Erdos1166PotentialKernelAnalytic

namespace Erdos1166.KilledGreen

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

open PotentialConvergence

def reverseBlock {n : ℕ} (η : Fin n → Direction) : Fin n → Direction :=
  fun i ↦ oppositeDirection (η i.rev)

@[simp] theorem reverseBlock_involutive {n : ℕ} (η : Fin n → Direction) :
    reverseBlock (reverseBlock η) = η := by
  funext i
  simp [reverseBlock]

def reverseBlockEquiv (n : ℕ) :
    (Fin n → Direction) ≃ (Fin n → Direction) :=
  (show Function.Involutive (@reverseBlock n) from reverseBlock_involutive).toPerm

theorem reverseBlockEquiv_apply {n : ℕ} (η : Fin n → Direction) :
    reverseBlockEquiv n η = reverseBlock η := rfl

private theorem reversePrefixSum {n : ℕ} (η : Fin n → Direction)
    (r : Fin (n + 1)) :
    let f : ℕ → Site := fun i ↦
      if hi : i < n then directionStep (η ⟨i, hi⟩) else 0
    (∑ i : Fin r, directionStep
        (reverseBlock η ⟨i, lt_of_lt_of_le i.isLt
          (Nat.le_of_lt_succ r.isLt)⟩)) =
      (∑ i ∈ Finset.range (n - r), f i) -
        ∑ i ∈ Finset.range n, f i := by
  dsimp only
  let f : ℕ → Site := fun i ↦
    if hi : i < n then directionStep (η ⟨i, hi⟩) else 0
  let fr : ℕ → Site := fun i ↦
    if hir : i < r then
      directionStep (reverseBlock η
        ⟨i, lt_of_lt_of_le hir (Nat.le_of_lt_succ r.isLt)⟩)
    else 0
  calc
    (∑ i : Fin r, directionStep
        (reverseBlock η ⟨i, lt_of_lt_of_le i.isLt
          (Nat.le_of_lt_succ r.isLt)⟩)) =
        ∑ i : Fin r, fr i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [fr]
    _ =
        ∑ i ∈ Finset.range r, -f (n - 1 - i) := by
      rw [Fin.sum_univ_eq_sum_range fr r]
      apply Finset.sum_congr rfl
      intro i hi
      have hir : i < r := Finset.mem_range.mp hi
      simp only [fr, dif_pos hir, reverseBlock, directionStep_opposite]
      dsimp only [f]
      rw [dif_pos (by omega : n - 1 - i < n)]
      have hrev :
          (⟨i, lt_of_lt_of_le hir
            (Nat.le_of_lt_succ r.isLt)⟩ : Fin n).rev =
            ⟨n - 1 - i, by omega⟩ := by
        apply Fin.ext
        dsimp only [Fin.rev, Fin.val_mk]
        omega
      rw [hrev]
    _ = -∑ j ∈ Finset.Ico (n - r) n, f j := by
      rw [Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_bij (fun i _ ↦ n - 1 - i)
      · intro i hi
        simp only [Finset.mem_range] at hi
        rw [Finset.mem_Ico]
        constructor <;> omega
      · intro i hi j hj hij
        simp only [Finset.mem_range] at hi hj
        omega
      · intro j hj
        rw [Finset.mem_Ico] at hj
        refine ⟨n - 1 - j, ?_, ?_⟩
        · rw [Finset.mem_range]
          omega
        · omega
      · intro i hi
        rfl
    _ = (∑ i ∈ Finset.range (n - r), f i) -
        ∑ i ∈ Finset.range n, f i := by
      rw [Finset.sum_Ico_eq_sub f (Nat.sub_le n r)]
      abel

theorem blockWalkFrom_reverseBlock {n : ℕ} (x : Site)
    (η : Fin n → Direction) (r : Fin (n + 1)) :
    blockWalkFrom (blockWalkFrom x η ⟨n, by omega⟩)
        (reverseBlock η) r =
      blockWalkFrom x η ⟨n - r, by omega⟩ := by
  unfold blockWalkFrom
  rw [reversePrefixSum]
  let f : ℕ → Site := fun i ↦
    if hi : i < n then directionStep (η ⟨i, hi⟩) else 0
  have hsum (q : Fin (n + 1)) :
      (∑ i : Fin q, directionStep
          (η ⟨i, lt_of_lt_of_le i.isLt
            (Nat.le_of_lt_succ q.isLt)⟩)) =
        ∑ i ∈ Finset.range q, f i := by
    rw [← Fin.sum_univ_eq_sum_range f q]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show f i = directionStep
        (η ⟨i, lt_of_lt_of_le i.isLt
          (Nat.le_of_lt_succ q.isLt)⟩) by
      dsimp only [f]
      rw [dif_pos (by omega)]]
  rw [hsum ⟨n, by omega⟩, hsum ⟨n - r, by omega⟩]
  abel

theorem reverseBlock_mem_blockKilledEndpoint
    {D : Set Site} {x y : Site} {n : ℕ} {η : Fin n → Direction}
    (h : η ∈ blockKilledEndpoint D x y n) :
    reverseBlock η ∈ blockKilledEndpoint D y x n := by
  have hend : blockWalkFrom x η ⟨n, by omega⟩ = y := h.2
  constructor
  · intro r
    rw [← hend, blockWalkFrom_reverseBlock]
    exact h.1 ⟨n - r, by omega⟩
  · rw [← hend, blockWalkFrom_reverseBlock]
    simp only [Nat.sub_self]
    unfold blockWalkFrom
    simp

theorem reverseBlock_mem_blockKilledEndpoint_iff
    {D : Set Site} {x y : Site} {n : ℕ} {η : Fin n → Direction} :
    reverseBlock η ∈ blockKilledEndpoint D y x n ↔
      η ∈ blockKilledEndpoint D x y n := by
  constructor
  · intro h
    have hr := reverseBlock_mem_blockKilledEndpoint h
    simpa using hr
  · exact reverseBlock_mem_blockKilledEndpoint

def reverseBlockMeasurableEquiv (n : ℕ) :
    (Fin n → Direction) ≃ᵐ (Fin n → Direction) where
  toEquiv := reverseBlockEquiv n
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

theorem reverseBlockMeasurableEquiv_apply {n : ℕ}
    (η : Fin n → Direction) :
    reverseBlockMeasurableEquiv n η = reverseBlock η := rfl

theorem reverseBlock_measurePreserving (n : ℕ) :
    MeasurePreserving (reverseBlockMeasurableEquiv n)
      (Measure.infinitePi fun _ : Fin n ↦ directionLaw)
      (Measure.infinitePi fun _ : Fin n ↦ directionLaw) := by
  refine ⟨(reverseBlockMeasurableEquiv n).measurable, ?_⟩
  apply Measure.ext_of_singleton
  intro η
  rw [Measure.map_apply (reverseBlockMeasurableEquiv n).measurable
    (measurableSet_singleton η)]
  have hpre : (reverseBlockMeasurableEquiv n) ⁻¹' {η} =
      {reverseBlock η} := by
    ext ξ
    simp only [Set.mem_preimage, Set.mem_singleton_iff,
      reverseBlockMeasurableEquiv_apply]
    constructor
    · intro h
      rw [← h]
      simp
    · intro h
      rw [h]
      simp
  rw [hpre]
  simp [directionLaw]

theorem finitePi_blockKilledEndpoint_comm
    (D : Set Site) (x y : Site) (n : ℕ) :
    (Measure.infinitePi fun _ : Fin n ↦ directionLaw)
        (blockKilledEndpoint D x y n) =
      (Measure.infinitePi fun _ : Fin n ↦ directionLaw)
        (blockKilledEndpoint D y x n) := by
  let μ := Measure.infinitePi fun _ : Fin n ↦ directionLaw
  let e := reverseBlockMeasurableEquiv n
  have hpre : e ⁻¹' blockKilledEndpoint D y x n =
      blockKilledEndpoint D x y n := by
    ext η
    exact reverseBlock_mem_blockKilledEndpoint_iff
  rw [← hpre]
  have hmap := congrArg
    (fun ν : Measure (Fin n → Direction) ↦
      ν (blockKilledEndpoint D y x n))
    (reverseBlock_measurePreserving n).map_eq
  rw [Measure.map_apply (reverseBlockMeasurableEquiv n).measurable
    (measurableSet_blockKilledEndpoint D y x n)] at hmap
  exact hmap

theorem killedWeight_comm (D : Set Site) (x y : Site) (n : ℕ) :
    killedWeight D x y n = killedWeight D y x n := by
  unfold killedWeight
  rw [← finitePi_blockKilledEndpoint_eq,
    ← finitePi_blockKilledEndpoint_eq]
  exact finitePi_blockKilledEndpoint_comm D x y n

theorem killedGreen_comm (D : Set Site) (x y : Site) :
    killedGreen D x y = killedGreen D y x := by
  unfold killedGreen
  apply tsum_congr
  intro n
  exact killedWeight_comm D x y n

theorem diskGreen_comm (R : ℕ) (x y : Site) :
    diskGreen R x y = diskGreen R y x :=
  killedGreen_comm _ _ _

theorem diskGreen_toReal_comm (R : ℕ) (x y : Site) :
    (diskGreen R x y).toReal = (diskGreen R y x).toReal := by
  rw [diskGreen_comm]

/-- The target-variable Dirichlet equation.  This is the self-adjoint
counterpart of `diskGreen_toReal_eq_indicator_add_step_average` and is the
minimal identity needed to pass from path reversal to a spectral treatment
of a Green column. -/
theorem diskGreen_toReal_eq_indicator_add_target_step_average
    (R : ℕ) (x y : Site) (hy : y ∈ squareDisk R) :
    (diskGreen R x y).toReal =
      (if x = y then 1 else 0) +
        (1 / 4 : ℝ) * ∑ d : Direction,
          (diskGreen R x (y + directionStep d)).toReal := by
  rw [diskGreen_toReal_comm R x y]
  have h := diskGreen_toReal_eq_indicator_add_step_average R y x hy
  rw [h]
  congr 1
  · by_cases hxy : x = y
    · simp [hxy]
    · simp [hxy, Ne.symm hxy]
  · apply congrArg ((1 / 4 : ℝ) * ·)
    apply Finset.sum_congr rfl
    intro d hd
    exact diskGreen_toReal_comm R (y + directionStep d) x

theorem diskGreen_start_edge_sub_eq_target_edge_sub
    (R : ℕ) (x z : Site) (d : Direction) :
    (diskGreen R (x + directionStep d) z).toReal -
        (diskGreen R x z).toReal =
      (diskGreen R z (x + directionStep d)).toReal -
        (diskGreen R z x).toReal := by
  rw [diskGreen_toReal_comm R (x + directionStep d) z,
    diskGreen_toReal_comm R x z]

/-- The unnormalised Dirichlet operator `I-P` for simple random walk.  When
functions are extended by zero off the square, its inverse kernel is exactly
`diskGreen`. -/
noncomputable def squareDirichletOperator (u : Site → ℝ) (y : Site) : ℝ :=
  u y - (1 / 4 : ℝ) * ∑ d : Direction, u (y + directionStep d)

/-- A square Green column is the exact fundamental solution of `I-P` in the
target variable.  This packages the resolvent equation needed before any
Fourier/eigenfunction expansion can be introduced. -/
theorem squareDirichletOperator_diskGreen
    (R : ℕ) (x y : Site) (hy : y ∈ squareDisk R) :
    squareDirichletOperator
        (fun z ↦ (diskGreen R x z).toReal) y =
      if x = y then 1 else 0 := by
  unfold squareDirichletOperator
  change (diskGreen R x y).toReal -
      (1 / 4 : ℝ) * ∑ d : Direction,
        (diskGreen R x (y + directionStep d)).toReal = _
  rw [diskGreen_toReal_eq_indicator_add_target_step_average R x y hy]
  ring

theorem diskGreen_toReal_eq_zero_of_target_not_mem
    {R : ℕ} {x y : Site} (hy : y ∉ squareDisk R) :
    (diskGreen R x y).toReal = 0 := by
  rw [diskGreen_toReal_comm]
  unfold diskGreen
  rw [killedGreen_eq_zero_of_start_not_mem hy]
  simp

end Erdos1166.KilledGreen
