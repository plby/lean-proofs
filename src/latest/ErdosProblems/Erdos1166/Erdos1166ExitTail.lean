/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166KilledGreen

namespace Erdos1166.ExitTail

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

open KilledGreen

/-!  A diffusive exit tail for the canonical planar walk.

The first diagonal coordinate of planar simple random walk is a one-dimensional
simple random walk.  The exact finite-prefix count below, together with the
central-binomial bound already proved in `Erdos1166Core`, gives a uniform
anti-concentration estimate.  A diagonal displacement larger than `4R` forces
exit from the square of radius `R`, independently of the starting point in the
square.  Independent blocks then give a geometric exit tail. -/

/-- Sign words whose sum is a prescribed integer. -/
def DiagonalBits (I : Type*) [Fintype I] (z : ℤ) :=
  {u : I → Bool // ∑ i, boolSign (u i) = z}

noncomputable instance (I : Type*) [Fintype I] [DecidableEq I] (z : ℤ) :
    Fintype (DiagonalBits I z) := by
  exact Fintype.ofInjective (fun u : DiagonalBits I z ↦ u.1)
    Subtype.coe_injective

/-- Once one sign word of sum `z` is fixed, all such words have the same
number of negative signs. -/
def diagonalBitsEquivBalanced {I : Type*} [Fintype I] [DecidableEq I]
    {z : ℤ} (u₀ : DiagonalBits I z) :
    DiagonalBits I z ≃ BalancedBits I (truePositions u₀.1).card where
  toFun u := ⟨u.1, by
    have hu₀ := u₀.2
    have hu := u.2
    rw [sum_boolSign_eq_card_sub_twice] at hu₀ hu
    omega⟩
  invFun u := ⟨u.1, by
    have hu₀ := u₀.2
    rw [sum_boolSign_eq_card_sub_twice]
    rw [u.2]
    rw [sum_boolSign_eq_card_sub_twice] at hu₀
    exact hu₀⟩
  left_inv u := by apply Subtype.ext; rfl
  right_inv u := by apply Subtype.ext; rfl

/-- At time `2j`, every atom of the first diagonal coordinate has at most the
central-binomial number of sign words. -/
theorem card_diagonalBits_le_centralBinom (j : ℕ) (z : ℤ) :
    Fintype.card (DiagonalBits (↑(Finset.range (2 * j))) z) ≤
      Nat.centralBinom j := by
  classical
  cases isEmpty_or_nonempty (DiagonalBits (↑(Finset.range (2 * j))) z) with
  | inl h => simp
  | inr h =>
      let u₀ : DiagonalBits (↑(Finset.range (2 * j))) z := Classical.choice h
      rw [Fintype.card_congr (diagonalBitsEquivBalanced u₀),
        card_balancedBits]
      simpa [Nat.centralBinom_eq_two_mul_choose] using
        Nat.choose_le_middle (truePositions u₀.1).card (2 * j)

/-- Prefixes whose first diagonal displacement is `z`. -/
def diagonalPrefixes (n : ℕ) (z : ℤ) : Finset (Prefix n) :=
  Finset.univ.filter fun w ↦ (finitePosition w).1 + (finitePosition w).2 = z

/-- The diagonal-bit bijection, retaining the unused independent bit word. -/
def diagonalPrefixEquiv (n : ℕ) (z : ℤ) :
    ↑(diagonalPrefixes n z) ≃
      DiagonalBits (↑(Finset.range n)) z ×
        ((↑(Finset.range n)) → Bool) where
  toFun w := by
    refine (⟨(prefixBitsEquiv n w.1).1, ?_⟩,
      (prefixBitsEquiv n w.1).2)
    change ∑ i, boolSign (directionBitsEquiv (w.1 i)).1 = z
    rw [diagonal_sum_one]
    exact (Finset.mem_filter.mp w.2).2
  invFun uv := by
    let w := (prefixBitsEquiv n).symm (uv.1.1, uv.2)
    refine ⟨w, ?_⟩
    change w ∈ Finset.univ.filter
      (fun w ↦ (finitePosition w).1 + (finitePosition w).2 = z)
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← diagonal_sum_one]
    have hw : prefixBitsEquiv n w = (uv.1.1, uv.2) :=
      (prefixBitsEquiv n).apply_symm_apply (uv.1.1, uv.2)
    have hw₁ := congrArg Prod.fst hw
    change (fun i ↦ (directionBitsEquiv (w i)).1) = uv.1.1 at hw₁
    have heach (i : ↑(Finset.range n)) :
        (directionBitsEquiv (w i)).1 = uv.1.1 i := congrFun hw₁ i
    simp_rw [heach]
    exact uv.1.2
  left_inv w := by
    apply Subtype.ext
    exact (prefixBitsEquiv n).symm_apply_apply w.1
  right_inv uv := by
    rcases uv with ⟨u, v⟩
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst ((prefixBitsEquiv n).apply_symm_apply (u.1, v))
    · change (prefixBitsEquiv n ((prefixBitsEquiv n).symm (u.1, v))).2 = v
      exact congrArg Prod.snd ((prefixBitsEquiv n).apply_symm_apply (u.1, v))

/-- Cardinal anti-concentration for the first diagonal coordinate. -/
theorem card_diagonalPrefixes_le (j : ℕ) (z : ℤ) :
    (diagonalPrefixes (2 * j) z).card ≤
      Nat.centralBinom j * 2 ^ (2 * j) := by
  classical
  rw [← Fintype.card_coe,
    Fintype.card_congr (diagonalPrefixEquiv (2 * j) z),
    Fintype.card_prod, Fintype.card_fun]
  simp only [Fintype.card_bool, Fintype.card_coe, Finset.card_range]
  exact Nat.mul_le_mul_right _ (card_diagonalBits_le_centralBinom j z)

/-- Exact finite-prefix expression for a diagonal-coordinate atom. -/
theorem increment_diagonal_prob_eq_card_div_pow (n : ℕ) (z : ℤ) :
    incrementLaw
        {ω | (simpleRandomWalk ω n).1 + (simpleRandomWalk ω n).2 = z} =
      ((diagonalPrefixes n z).card : ENNReal) / (4 : ENNReal) ^ n := by
  let A := diagonalPrefixes n z
  calc
    incrementLaw
        {ω | (simpleRandomWalk ω n).1 + (simpleRandomWalk ω n).2 = z} =
        (incrementLaw.map (Finset.range n).restrict) (A : Set (Prefix n)) := by
      rw [Measure.map_apply]
      · congr 1
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_preimage, Finset.mem_coe,
          A, diagonalPrefixes, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [finitePosition_restrict]
      · fun_prop
      · measurability
    _ = prefixLaw n (A : Set (Prefix n)) := by rw [increment_restrict_map]
    _ = ∑ w ∈ A, prefixLaw n {w} := by rw [sum_measure_singleton]
    _ = ∑ _w ∈ A, (4 : ENNReal)⁻¹ ^ n := by
      apply Finset.sum_congr rfl
      intro w _
      exact prefixLaw_singleton n w
    _ = (A.card : ENNReal) / (4 : ENNReal) ^ n := by
      simp [div_eq_mul_inv, ENNReal.inv_pow]
    _ = ((diagonalPrefixes n z).card : ENNReal) / (4 : ENNReal) ^ n := rfl

/-- A square-form consequence of the central-binomial estimate.  This form
avoids introducing real square roots into the exit argument. -/
theorem mul_centralBinom_le_four_pow_of_sq_le {M j : ℕ}
    (hM : M ^ 2 ≤ j + 1) :
    M * Nat.centralBinom j ≤ 4 ^ j := by
  apply (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).mp
  calc
    (M * Nat.centralBinom j) ^ 2 =
        M ^ 2 * Nat.centralBinom j ^ 2 := by ring
    _ ≤ (j + 1) * Nat.centralBinom j ^ 2 :=
      Nat.mul_le_mul_right _ hM
    _ ≤ 16 ^ j := succ_mul_centralBinom_sq_le_sixteen_pow j
    _ = (4 ^ j) ^ 2 := by
      rw [show (16 : ℕ) = 4 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
      congr 1
      omega

/-- Natural-number cancellation, stated in the `ENNReal` form used for
finite-prefix probabilities. -/
theorem ennreal_div_le_inv_of_nat {a b M : ℕ} (hM : 0 < M) (hb : 0 < b)
    (h : M * a ≤ b) :
    (a : ENNReal) / (b : ENNReal) ≤ (M : ENNReal)⁻¹ := by
  rw [ENNReal.div_le_iff (by exact_mod_cast hb.ne') (by simp)]
  have hcast : (M : ENNReal) * a ≤ b := by exact_mod_cast h
  calc
    (a : ENNReal) = (M : ENNReal)⁻¹ * ((M : ENNReal) * a) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel] <;> simp [hM.ne']
    _ ≤ (M : ENNReal)⁻¹ * b := by gcongr
    _ = (M : ENNReal)⁻¹ * (b : ENNReal) := rfl

/-- Uniform anti-concentration of a diagonal atom at even time. -/
theorem increment_diagonal_prob_le_inv {M j : ℕ} (z : ℤ)
    (hM : 0 < M) (hMsq : M ^ 2 ≤ j + 1) :
    incrementLaw
        {ω | (simpleRandomWalk ω (2 * j)).1 +
          (simpleRandomWalk ω (2 * j)).2 = z} ≤
      (M : ENNReal)⁻¹ := by
  rw [increment_diagonal_prob_eq_card_div_pow]
  have hnat : M * (diagonalPrefixes (2 * j) z).card ≤ 4 ^ (2 * j) := by
    calc
      M * (diagonalPrefixes (2 * j) z).card ≤
          M * (Nat.centralBinom j * 2 ^ (2 * j)) :=
        Nat.mul_le_mul_left _ (card_diagonalPrefixes_le j z)
      _ = (M * Nat.centralBinom j) * 2 ^ (2 * j) := by ring
      _ ≤ 4 ^ j * 2 ^ (2 * j) :=
        Nat.mul_le_mul_right _ (mul_centralBinom_le_four_pow_of_sq_le hMsq)
      _ = 4 ^ (2 * j) := by
        rw [show 2 ^ (2 * j) = 4 ^ j by rw [pow_mul]; norm_num]
        rw [← pow_add]
        congr 1
        omega
  simpa using ennreal_div_le_inv_of_nat hM (by positivity) hnat

/-- The possible diagonal displacements of a path that begins and ends in
the square of radius `R`. -/
noncomputable def diagonalWindow (R : ℕ) : Finset ℤ :=
  Finset.Icc (-4 * (R : ℤ)) (4 * (R : ℤ))

@[simp] theorem card_diagonalWindow (R : ℕ) :
    (diagonalWindow R).card = 8 * R + 1 := by
  simp [diagonalWindow]
  have h : 4 * (R : ℤ) + 1 + 4 * (R : ℤ) = ((8 * R + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [h]
  exact Int.toNat_natCast (8 * R + 1)

/-- Event that the first diagonal displacement lies in the square-compatible
window. -/
noncomputable def diagonalModerateEvent (R n : ℕ) : Set (ℕ → Direction) :=
  {ω | (simpleRandomWalk ω n).1 + (simpleRandomWalk ω n).2 ∈
    diagonalWindow R}

theorem measurableSet_diagonalModerateEvent (R n : ℕ) :
    MeasurableSet (diagonalModerateEvent R n) := by
  have hwalk : Measurable (fun ω : ℕ → Direction ↦ simpleRandomWalk ω n) :=
    (HLOZFoundation.measurable_simpleRandomWalk_time_iidHistory
      (j := n) (k := n) le_rfl).mono
        (ProbabilityTheory.iidHistory_le n) le_rfl
  have hdiag : Measurable (fun ω : ℕ → Direction ↦
      (simpleRandomWalk ω n).1 + (simpleRandomWalk ω n).2) :=
    hwalk.fst.add hwalk.snd
  exact (Set.to_countable (diagonalWindow R : Set ℤ)).measurableSet.preimage
    hdiag

theorem diagonalModerateEvent_eq_biUnion (R n : ℕ) :
    diagonalModerateEvent R n =
      ⋃ z ∈ diagonalWindow R,
        {ω | (simpleRandomWalk ω n).1 + (simpleRandomWalk ω n).2 = z} := by
  ext ω
  simp [diagonalModerateEvent]

/-- A moderate diagonal displacement has probability at most `1/4` at the
chosen diffusive time. -/
theorem diagonalModerateEvent_measure_le_quarter (R : ℕ) :
    incrementLaw
        (diagonalModerateEvent R
          (2 * (4 * (8 * R + 1)) ^ 2)) ≤
      (4 : ENNReal)⁻¹ := by
  let M := 4 * (8 * R + 1)
  let j := M ^ 2
  have hM : 0 < M := by dsimp [M]; positivity
  have hMsq : M ^ 2 ≤ j + 1 := by dsimp [j]; omega
  rw [show 2 * (4 * (8 * R + 1)) ^ 2 = 2 * j by rfl,
    diagonalModerateEvent_eq_biUnion]
  calc
    incrementLaw
        (⋃ z ∈ diagonalWindow R,
          {ω | (simpleRandomWalk ω (2 * j)).1 +
            (simpleRandomWalk ω (2 * j)).2 = z}) ≤
        ∑ z ∈ diagonalWindow R,
          incrementLaw
            {ω | (simpleRandomWalk ω (2 * j)).1 +
              (simpleRandomWalk ω (2 * j)).2 = z} :=
      measure_biUnion_finset_le (diagonalWindow R) _
    _ ≤ ∑ _z ∈ diagonalWindow R, (M : ENNReal)⁻¹ := by
      exact Finset.sum_le_sum fun z _ ↦
        increment_diagonal_prob_le_inv z hM hMsq
    _ = (4 : ENNReal)⁻¹ := by
      rw [Finset.sum_const, card_diagonalWindow]
      simp only [nsmul_eq_mul, Nat.cast_add,
        Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, M]
      rw [ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp))]
      rw [mul_comm (4 : ENNReal)⁻¹, ← mul_assoc,
        ENNReal.mul_inv_cancel (by positivity) (by finiteness), one_mul]

/-- The explicit diffusive block length used in the exit estimate. -/
def diffusiveExitBlockLength (R : ℕ) : ℕ :=
  2 * (4 * (8 * R + 1)) ^ 2

theorem diffusiveExitBlockLength_pos (R : ℕ) :
    0 < diffusiveExitBlockLength R := by
  dsimp [diffusiveExitBlockLength]
  positivity

/-- The block length is bounded by an explicit constant times the diffusive
scale `(R+1)^2`. -/
theorem diffusiveExitBlockLength_le (R : ℕ) :
    diffusiveExitBlockLength R ≤ 2048 * (R + 1) ^ 2 := by
  dsimp [diffusiveExitBlockLength]
  calc
    2 * (4 * (8 * R + 1)) ^ 2 ≤
        2 * (4 * (8 * (R + 1))) ^ 2 := by
      gcongr
      omega
    _ = 2048 * (R + 1) ^ 2 := by ring

/-- Displacement of a finite block. -/
def blockEndpoint {m : ℕ} (η : Fin m → Direction) : Site :=
  ∑ i, directionStep (η i)

/-- A block whose first diagonal displacement is compatible with beginning
and ending in the square of radius `R`. -/
noncomputable def blockDiagonalModerate (R m : ℕ) : Set (Fin m → Direction) :=
  {η | (blockEndpoint η).1 + (blockEndpoint η).2 ∈ diagonalWindow R}

theorem measurableSet_blockDiagonalModerate (R m : ℕ) :
    MeasurableSet (blockDiagonalModerate R m) :=
  MeasurableSet.of_discrete

theorem blockEndpoint_iidBlock_zero (m : ℕ) (ω : ℕ → Direction) :
    blockEndpoint (iidBlock (X := Direction) 0 m ω) =
      simpleRandomWalk ω m := by
  unfold blockEndpoint iidBlock simpleRandomWalk
  simp only [Nat.zero_add]
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ directionStep (ω i)) m]

theorem iidBlock_zero_preimage_blockDiagonalModerate (R m : ℕ) :
    iidBlock (X := Direction) 0 m ⁻¹' blockDiagonalModerate R m =
      diagonalModerateEvent R m := by
  ext ω
  simp only [Set.mem_preimage, blockDiagonalModerate, Set.mem_ofPred_eq,
    diagonalModerateEvent]
  rw [blockEndpoint_iidBlock_zero]

theorem finitePi_blockDiagonalModerate_eq (R m : ℕ) :
    (Measure.infinitePi fun _ : Fin m ↦ directionLaw)
        (blockDiagonalModerate R m) =
      incrementLaw (diagonalModerateEvent R m) := by
  rw [← iidBlock_map directionLaw 0 m]
  rw [Measure.map_apply (measurable_iidBlock 0 m)
    (measurableSet_blockDiagonalModerate R m)]
  exact congrArg incrementLaw
    (iidBlock_zero_preimage_blockDiagonalModerate R m)

theorem finitePi_diffusiveBlock_moderate_le_quarter (R : ℕ) :
    (Measure.infinitePi fun _ : Fin (diffusiveExitBlockLength R) ↦ directionLaw)
        (blockDiagonalModerate R (diffusiveExitBlockLength R)) ≤
      (4 : ENNReal)⁻¹ := by
  rw [finitePi_blockDiagonalModerate_eq]
  exact diagonalModerateEvent_measure_le_quarter R

/-- If a finite block begins and ends in the square, its diagonal displacement
lies in `[-4R,4R]`. -/
theorem blockEndpoint_mem_diagonalWindow_of_endpoints_mem
    {R m : ℕ} {z : Site} {η : Fin m → Direction}
    (hz : z ∈ squareDisk R)
    (hend : blockWalkFrom z η ⟨m, by omega⟩ ∈ squareDisk R) :
    (blockEndpoint η).1 + (blockEndpoint η).2 ∈ diagonalWindow R := by
  have hzx := (Finset.mem_Icc.mp (Finset.mem_product.mp hz).1)
  have hzy := (Finset.mem_Icc.mp (Finset.mem_product.mp hz).2)
  have hex := (Finset.mem_Icc.mp (Finset.mem_product.mp hend).1)
  have hey := (Finset.mem_Icc.mp (Finset.mem_product.mp hend).2)
  have hx : (blockWalkFrom z η ⟨m, by omega⟩).1 =
      z.1 + (blockEndpoint η).1 := by
    simp [blockWalkFrom, blockEndpoint]
  have hy : (blockWalkFrom z η ⟨m, by omega⟩).2 =
      z.2 + (blockEndpoint η).2 := by
    simp [blockWalkFrom, blockEndpoint]
  rw [hx] at hex
  rw [hy] at hey
  simp only [diagonalWindow, Finset.mem_Icc]
  constructor <;> omega

/-- Survival through the next diffusive block forces that independent block
to have moderate diagonal displacement. -/
theorem survival_succDiffusiveBlock_subset (R k : ℕ) (x : Site) :
    survivalEvent (squareDisk R : Set Site) x
        (k + diffusiveExitBlockLength R) ⊆
      survivalEvent (squareDisk R : Set Site) x k ∩
        iidBlock (X := Direction) k (diffusiveExitBlockLength R) ⁻¹'
          blockDiagonalModerate R (diffusiveExitBlockLength R) := by
  intro ω hω
  constructor
  · intro r hr
    exact hω r (by omega)
  · have hxk : walkFrom x ω k ∈ squareDisk R := hω k (by omega)
    have hend : blockWalkFrom (walkFrom x ω k)
        (iidBlock (X := Direction) k (diffusiveExitBlockLength R) ω)
        ⟨diffusiveExitBlockLength R, by omega⟩ ∈ squareDisk R := by
      rw [blockWalkFrom_iidBlock_eq_walkFrom]
      exact hω (k + diffusiveExitBlockLength R) le_rfl
    exact blockEndpoint_mem_diagonalWindow_of_endpoints_mem hxk hend

/-- One-block contraction of square survival probability. -/
theorem survivalWeight_succDiffusiveBlock_le (R k : ℕ) (x : Site) :
    survivalWeight (squareDisk R : Set Site) x
        (k + diffusiveExitBlockLength R) ≤
      survivalWeight (squareDisk R : Set Site) x k * (4 : ENNReal)⁻¹ := by
  calc
    survivalWeight (squareDisk R : Set Site) x
        (k + diffusiveExitBlockLength R) ≤
        incrementLaw
          (survivalEvent (squareDisk R : Set Site) x k ∩
            iidBlock (X := Direction) k (diffusiveExitBlockLength R) ⁻¹'
              blockDiagonalModerate R (diffusiveExitBlockLength R)) :=
      measure_mono (survival_succDiffusiveBlock_subset R k x)
    _ = survivalWeight (squareDisk R : Set Site) x k *
        (Measure.infinitePi fun _ : Fin (diffusiveExitBlockLength R) ↦ directionLaw)
          (blockDiagonalModerate R (diffusiveExitBlockLength R)) := by
      exact measure_inter_iidBlock_eq_mul directionLaw k (diffusiveExitBlockLength R)
        (measurableSet_survivalEvent_iidHistory _ _ k)
        (measurableSet_blockDiagonalModerate R (diffusiveExitBlockLength R))
    _ ≤ survivalWeight (squareDisk R : Set Site) x k * (4 : ENNReal)⁻¹ := by
      gcongr
      exact finitePi_diffusiveBlock_moderate_le_quarter R

/-- Geometric tail at integer multiples of the explicit diffusive block. -/
theorem survivalWeight_mulDiffusiveBlock_le (R q : ℕ) (x : Site) :
    survivalWeight (squareDisk R : Set Site) x
        (q * diffusiveExitBlockLength R) ≤
      ((4 : ENNReal)⁻¹) ^ q := by
  induction q with
  | zero =>
      simp only [zero_mul, pow_zero]
      exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ
  | succ q ih =>
      calc
        survivalWeight (squareDisk R : Set Site) x
            ((q + 1) * diffusiveExitBlockLength R) =
            survivalWeight (squareDisk R : Set Site) x
              (q * diffusiveExitBlockLength R + diffusiveExitBlockLength R) := by
                rw [Nat.add_mul]
                simp
        _ ≤ survivalWeight (squareDisk R : Set Site) x
              (q * diffusiveExitBlockLength R) * (4 : ENNReal)⁻¹ :=
          survivalWeight_succDiffusiveBlock_le R
            (q * diffusiveExitBlockLength R) x
        _ ≤ ((4 : ENNReal)⁻¹) ^ q * (4 : ENNReal)⁻¹ := by
          gcongr
        _ = ((4 : ENNReal)⁻¹) ^ (q + 1) := by rw [pow_succ]

/-- Geometric tail at an arbitrary deterministic time. -/
theorem survivalWeight_le_diffusiveBlockGeometric (R n : ℕ) (x : Site) :
    survivalWeight (squareDisk R : Set Site) x n ≤
      ((4 : ENNReal)⁻¹) ^ (n / diffusiveExitBlockLength R) := by
  calc
    survivalWeight (squareDisk R : Set Site) x n ≤
        survivalWeight (squareDisk R : Set Site) x
          ((n / diffusiveExitBlockLength R) * diffusiveExitBlockLength R) := by
      apply survivalWeight_antitone
      exact Nat.div_mul_le_self n (diffusiveExitBlockLength R)
    _ ≤ ((4 : ENNReal)⁻¹) ^ (n / diffusiveExitBlockLength R) :=
      survivalWeight_mulDiffusiveBlock_le R
        (n / diffusiveExitBlockLength R) x

/-- The same tail on the simpler displayed scale `2048 q (R+1)^2`. -/
theorem survivalWeight_mulDiffusiveScale_le (R q : ℕ) (x : Site) :
    survivalWeight (squareDisk R : Set Site) x
        (q * (2048 * (R + 1) ^ 2)) ≤
      ((4 : ENNReal)⁻¹) ^ q := by
  calc
    survivalWeight (squareDisk R : Set Site) x
        (q * (2048 * (R + 1) ^ 2)) ≤
        survivalWeight (squareDisk R : Set Site) x
          (q * diffusiveExitBlockLength R) := by
      apply survivalWeight_antitone
      exact Nat.mul_le_mul_left q (diffusiveExitBlockLength_le R)
    _ ≤ ((4 : ENNReal)⁻¹) ^ q :=
      survivalWeight_mulDiffusiveBlock_le R q x

/-- A natural-valued version of the first exit time.  On the null event of
never exiting, it is set to zero; the geometric tail below proves that this
exception has zero probability. -/
noncomputable def squareExitTimeNat (R : ℕ) (x : Site)
    (ω : ℕ → Direction) : ℕ := by
  classical
  exact if h : ∃ n, walkFrom x ω n ∉ squareDisk R then Nat.find h else 0

theorem ge_squareExitTimeNat_subset_survivalEvent (R q : ℕ) (x : Site) :
    {ω | q * diffusiveExitBlockLength R + 1 ≤ squareExitTimeNat R x ω} ⊆
      survivalEvent (squareDisk R : Set Site) x
        (q * diffusiveExitBlockLength R) := by
  intro ω hω r hr
  classical
  change q * diffusiveExitBlockLength R + 1 ≤ squareExitTimeNat R x ω at hω
  by_cases hex : ∃ n, walkFrom x ω n ∉ squareDisk R
  · have hτ : squareExitTimeNat R x ω = Nat.find hex := by
      simp [squareExitTimeNat, hex]
    rw [hτ] at hω
    by_contra hrout
    have hfirst : Nat.find hex ≤ r := Nat.find_min' hex hrout
    omega
  · have hτ : squareExitTimeNat R x ω = 0 := by
      simp [squareExitTimeNat, hex]
    rw [hτ] at hω
    omega

/-- Explicit exit-time tail in the form used in Appendix A: after `q`
diffusive blocks, the probability of not yet having exited is at most
`4^{-q}`. -/
theorem squareExitTimeNat_ge_measure_le (R q : ℕ) (x : Site) :
    incrementLaw
        {ω | q * diffusiveExitBlockLength R + 1 ≤
          squareExitTimeNat R x ω} ≤
      ((4 : ENNReal)⁻¹) ^ q := by
  calc
    incrementLaw
        {ω | q * diffusiveExitBlockLength R + 1 ≤
          squareExitTimeNat R x ω} ≤
        survivalWeight (squareDisk R : Set Site) x
          (q * diffusiveExitBlockLength R) :=
      measure_mono (ge_squareExitTimeNat_subset_survivalEvent R q x)
    _ ≤ ((4 : ENNReal)⁻¹) ^ q :=
      survivalWeight_mulDiffusiveBlock_le R q x

/-- Comparison form suitable for a prescribed Appendix-A time scale. -/
theorem squareExitTimeNat_ge_measure_le_of_blocks
    {R q N : ℕ} (x : Site)
    (hN : q * diffusiveExitBlockLength R + 1 ≤ N) :
    incrementLaw {ω | N ≤ squareExitTimeNat R x ω} ≤
      ((4 : ENNReal)⁻¹) ^ q := by
  calc
    incrementLaw {ω | N ≤ squareExitTimeNat R x ω} ≤
        incrementLaw
          {ω | q * diffusiveExitBlockLength R + 1 ≤
            squareExitTimeNat R x ω} := by
      apply measure_mono
      intro ω hω
      exact hN.trans hω
    _ ≤ ((4 : ENNReal)⁻¹) ^ q :=
      squareExitTimeNat_ge_measure_le R q x

/-- Explicit `q R^2`-scale exit tail (with the harmless lattice correction
`R+1` and the numerical constant `2048`). -/
theorem squareExitTimeNat_ge_diffusiveScale_measure_le
    (R q : ℕ) (x : Site) :
    incrementLaw
        {ω | q * (2048 * (R + 1) ^ 2) + 1 ≤ squareExitTimeNat R x ω} ≤
      ((4 : ENNReal)⁻¹) ^ q := by
  apply squareExitTimeNat_ge_measure_le_of_blocks (R := R) (q := q) x
  have h := Nat.mul_le_mul_left q (diffusiveExitBlockLength_le R)
  omega

end Erdos1166.ExitTail
