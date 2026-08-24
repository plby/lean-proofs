/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.ControlledNumericalEventually
import ErdosProblems.Erdos360.PrimePoolSharpOrdinary

/-!
# Uniform finite rooms for the sharp prime-pool numerics

The extracted cardinality varies in a fixed interval.  This file replaces
all occurrences of that cardinality by its two endpoints and proves the
rounding lemmas needed to recover the exact finite numerical record.
-/

namespace Erdos360

open scoped BigOperators

attribute [local instance] Classical.propDecidable

def sharpUniformPoolFloor (Q ell : ℕ) : ℕ := Q / (8 * ell)

def sharpUniformRemainderFloor (Q ell : ℕ) : ℕ :=
  sharpUniformPoolFloor Q ell / 8

def sharpUniformTargetCeiling (y ell : ℕ) : ℕ :=
  128 * y / ell + 1

def sharpDivisorTargetCeiling (y ell d : ℕ) : ℕ :=
  128 * y / (ell * d) + 1

def sharpUniformIncrementCeiling (y Q : ℕ) : ℕ :=
  65536 * y / Q

noncomputable def sharpUniformLogBudget (y Q ell : ℕ) : ℕ :=
  let h := Nat.log 2 (2 * y) + 1
  let p := sharpUniformPoolFloor Q ell
  h * (2 * h + (primePoolSharpGrowthThreshold y / (p / 128) + 1))

lemma poolSize_lower_of_uniform
    {Q z ell : ℕ} (hQz : Q ≤ z) :
    sharpUniformPoolFloor Q ell ≤ primeRandomPoolSize z ell := by
  exact Nat.div_le_div_right hQz

lemma pool_le_sixteen_mul_poolSize_of_room
    {z ell : ℕ} (hell : 0 < ell) (hroom : 64 * ell ≤ z) :
    z ≤ 16 * ell * primeRandomPoolSize z ell := by
  let m := primeRandomPoolSize z ell
  have hden : 0 < 8 * ell := by positivity
  have hm8 : 8 ≤ m := by
    dsimp [m, primeRandomPoolSize]
    apply (Nat.le_div_iff_mul_le hden).2
    simpa [mul_assoc, mul_comm, mul_left_comm] using hroom
  have hzlt : z < (m + 1) * (8 * ell) := by
    dsimp [m, primeRandomPoolSize]
    simpa [mul_comm] using Nat.lt_mul_div_succ z hden
  nlinarith

lemma poolSize_le_eight_mul_quarter_of_room
    {z ell : ℕ} (hell : 0 < ell) (hroom : 64 * ell ≤ z) :
    primeRandomPoolSize z ell ≤
      8 * (primeRandomPoolSize z ell / 4) := by
  let m := primeRandomPoolSize z ell
  have hm8 : 8 ≤ m := by
    have hden : 0 < 8 * ell := by positivity
    dsimp [m, primeRandomPoolSize]
    apply (Nat.le_div_iff_mul_le hden).2
    simpa [mul_assoc, mul_comm, mul_left_comm] using hroom
  have hlt := Nat.lt_mul_div_succ m (by norm_num : 0 < 4)
  omega

lemma primeRandomNzero_le_targetCeiling_mul_quarter
    {y z ell d : ℕ} (hell : 0 < ell) (hd : 0 < d)
    (hroom : 64 * ell ≤ z) :
    primeRandomNzero y z ell d ≤
      sharpDivisorTargetCeiling y ell d *
        (primeRandomPoolSize z ell / 4) := by
  let m := primeRandomPoolSize z ell
  let r := m / 4
  let B := ell * d
  have hB : 0 < B := by positivity
  have hz : z ≤ 128 * ell * r := by
    calc
      z ≤ 16 * ell * m :=
        pool_le_sixteen_mul_poolSize_of_room hell hroom
      _ ≤ 16 * ell * (8 * r) := Nat.mul_le_mul_left _
        (poolSize_le_eight_mul_quarter_of_room hell hroom)
      _ = 128 * ell * r := by ring
  have hnum : y * z ≤ ell * (128 * y * r) := by
    nlinarith
  have hcancel :
      y * z / (ell * B) ≤ (128 * y * r) / B := by
    calc
      y * z / (ell * B) ≤
          (ell * (128 * y * r)) / (ell * B) :=
        Nat.div_le_div_right hnum
      _ = (128 * y * r) / B := by
        exact Nat.mul_div_mul_left _ _ (by omega)
  have hround : (128 * y * r) / B ≤ (128 * y / B + 1) * r := by
    apply Nat.div_le_of_le_mul
    have hlt := Nat.lt_mul_div_succ (128 * y) hB
    nlinarith
  unfold primeRandomNzero sharpDivisorTargetCeiling
  simpa [B, r, m, pow_two, mul_assoc] using hcancel.trans hround

lemma primePoolSharpResidueTarget_le_divisor_uniform
    {y z ell d : ℕ} (hell : 0 < ell) (hd : 0 < d)
    (hroom : 64 * ell ≤ z) :
    primePoolSharpResidueTarget y z ell d ≤
      sharpDivisorTargetCeiling y ell d := by
  have hr : 0 < primeRandomPoolSize z ell / 4 := by
    have hm := poolSize_le_eight_mul_quarter_of_room hell hroom
    have hmpos : 0 < primeRandomPoolSize z ell := by
      have : 8 ≤ primeRandomPoolSize z ell := by
        have hden : 0 < 8 * ell := by positivity
        unfold primeRandomPoolSize
        apply (Nat.le_div_iff_mul_le hden).2
        simpa [mul_assoc, mul_comm, mul_left_comm] using hroom
      omega
    omega
  unfold primePoolSharpResidueTarget
  apply (ceilDiv_le_iff_le_mul hr).2
  simpa [mul_comm] using
    primeRandomNzero_le_targetCeiling_mul_quarter hell hd hroom

lemma primePoolSharpResidueTarget_le_uniform
    {y z ell d : ℕ} (hell : 0 < ell) (hd : 0 < d)
    (hroom : 64 * ell ≤ z) :
    primePoolSharpResidueTarget y z ell d ≤
      sharpUniformTargetCeiling y ell := by
  have hdiv : 128 * y / (ell * d) ≤ 128 * y / ell :=
    Nat.div_le_div_left (Nat.le_mul_of_pos_right ell hd) (by omega)
  exact (primePoolSharpResidueTarget_le_divisor_uniform hell hd hroom).trans
    (Nat.add_le_add_right hdiv 1)

lemma sharpRemainderFloor_lower
    {Q z ell : ℕ} (hQz : Q ≤ z) :
    sharpUniformRemainderFloor Q ell ≤
      primePoolSharpRemainderFloor z ell := by
  let m := primeRandomPoolSize z ell
  have hp : sharpUniformPoolFloor Q ell ≤ m :=
    poolSize_lower_of_uniform hQz
  have h8 : sharpUniformPoolFloor Q ell / 8 ≤ m / 8 :=
    Nat.div_le_div_right hp
  have h16le : m / 16 ≤ m / 8 :=
    Nat.div_le_div_left (by omega) (by omega)
  have htwice : 2 * (m / 8) ≤ m / 4 := by
    calc
      2 * (m / 8) ≤ (2 * m) / 8 := Nat.mul_div_le_mul_div_assoc 2 m 8
      _ = m / 4 := by omega
  dsimp [sharpUniformRemainderFloor, primePoolSharpRemainderFloor,
    primePoolSharpPhaseCount, m] at h8 ⊢
  omega

/-- Endpoint inequalities sufficient for every exact sharp numerical
record in the controlled extraction range. -/
structure CFPPrimePoolSharpUniformRooms
    (A C ratio : ℝ) (n sieveLevel sieveCutoff sieveQ : ℕ)
    (y U Q M ell : ℕ) : Prop where
  ell_pos : 0 < ell
  U_pos : 0 < U
  pool_room : 16 * U + 256 ≤ sharpUniformPoolFloor Q ell
  z_room : 64 * ell ≤ Q
  M_le_y : M ≤ y
  probability :
    (2 : ℝ) * (((2 * y : ℕ) : ℝ) + 1) *
      Real.exp (-(primeRandomPoolDiversity y ell : ℝ) / 24) < 1
  diversity_room : 128 * ell * U ≤ fourthRootCeil y
  increment_below :
    64 * sharpUniformIncrementCeiling y Q ≤
      primePoolSharpGrowthThreshold y
  growth_ambient :
    U * (4 * primePoolSharpGrowthThreshold y + 1) ≤ y
  growth_budget :
    sharpUniformLogBudget y Q ell ≤ sharpUniformPoolFloor Q ell / 16
  unsaturated_budget :
    sharpUniformTargetCeiling y ell ≤
      (65536 * y / M + 1) *
        (sharpUniformPoolFloor Q ell / 16 -
          sharpUniformLogBudget y Q ell)
  fiber_ambient :
    2000000000 * (128 * y / ell + U) ≤ y
  polynomial_reverse :
    2 ^ 712 * (4 * sharpUniformIncrementCeiling y Q) ^ 100 <
      (primePoolSharpGrowthThreshold y /
          (2 * sharpUniformIncrementCeiling y Q)) ^ 2 *
        sharpUniformRemainderFloor Q ell ^ 100
  A_ge_one : 1 ≤ A
  C_pos : 0 < C
  n_pos : 0 < n
  sieveCutoff_ge : 2 ≤ sieveCutoff
  sieveLevel_ge : 101 ≤ sieveLevel
  sieveQ_pos : 0 < sieveQ
  log_bound : Real.log A ≤ 2 * (sieveLevel - 100 : ℕ) / 99
  ratio_nonneg : 0 ≤ ratio
  ratio_bound : ∀ step : ℕ, 0 < step → step ≤ 2 * y →
    ((n * step : ℕ) : ℝ) / Nat.totient (n * step) ≤ ratio
  long_scale :
    (sieveQ * (sieveCutoff ^ sieveLevel) ^ 2) ^ 3 ≤
      sharpUniformRemainderFloor Q ell
  sieve_reverse :
    (((192 * 48 : ℕ) : ℝ) * sharpUniformIncrementCeiling y Q) *
        (((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (sieveLevel - 100)) *
            (C * ratio / Real.log (sieveCutoff : ℝ))) +
              1 / (sieveQ : ℝ)) <
      sharpUniformRemainderFloor Q ell

lemma sharpPolynomialReverse_of_uniform
    {G E e u R₀ R : ℕ} (he : 0 < e) (heE : e ≤ E) (hGu : G < u)
    (h64 : 64 * E ≤ G) (hR : R₀ ≤ R)
    (hpoly : 2 ^ 712 * (4 * E) ^ 100 <
      (G / (2 * E)) ^ 2 * R₀ ^ 100) :
    2 ^ 712 * u ^ 100 < (u / (2 * e)) ^ 102 * R ^ 100 := by
  let a := u / (2 * e)
  have hden : 2 * e ≤ 2 * E := Nat.mul_le_mul_left 2 heE
  have hquot : G / (2 * E) ≤ a := by
    apply Nat.div_le_div hGu.le hden
    positivity
  have hfour : 4 * e ≤ u := by omega
  have hua : u ≤ 4 * e * a := by
    have hlt := Nat.lt_mul_div_succ u (by positivity : 0 < 2 * e)
    have haTwo : 2 ≤ a := by
      dsimp [a]
      apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 * e)).2
      simpa [mul_assoc, mul_comm, mul_left_comm] using hfour
    calc
      u ≤ 2 * e * (a + 1) := hlt.le
      _ ≤ 2 * e * (2 * a) := Nat.mul_le_mul_left _ (by omega)
      _ = 4 * e * a := by ring
  have huEA : u ≤ 4 * E * a :=
    hua.trans (Nat.mul_le_mul_right a (Nat.mul_le_mul_left 4 heE))
  have haPos : 0 < a := by
    dsimp [a]
    apply Nat.div_pos
    · omega
    · positivity
  calc
    2 ^ 712 * u ^ 100 ≤ 2 ^ 712 * (4 * E * a) ^ 100 := by gcongr
    _ = (2 ^ 712 * (4 * E) ^ 100) * a ^ 100 := by
      rw [mul_pow]
      ring
    _ < ((G / (2 * E)) ^ 2 * R₀ ^ 100) * a ^ 100 :=
      Nat.mul_lt_mul_of_pos_right hpoly (Nat.pow_pos haPos)
    _ ≤ (a ^ 2 * R ^ 100) * a ^ 100 := by gcongr
    _ = a ^ 102 * R ^ 100 := by
      rw [show 102 = 2 + 100 by omega, pow_add]
      ring
/-- The endpoint room record gives the exact sharp numerical record at
every admissible divisor and extracted cardinality. -/
theorem CFPPrimePoolSharpUniformRooms.toSharpNumerics
    {A C ratio : ℝ} {n sieveLevel sieveCutoff sieveQ : ℕ}
    {y U Q M ell d z : ℕ}
    (h : CFPPrimePoolSharpUniformRooms A C ratio n sieveLevel sieveCutoff
      sieveQ y U Q M ell)
    (hd : 0 < d) (hdU : d ≤ U) (hQz : Q ≤ z) (hzM : z ≤ M) :
    CFPPrimePoolSharpNumerics A C ratio n sieveLevel sieveCutoff sieveQ
      y U z ell d := by
  let p := sharpUniformPoolFloor Q ell
  let m := primeRandomPoolSize z ell
  let k := primePoolSharpPhaseCount z ell
  let L := primePoolSharpLargeGain z ell
  let E := sharpUniformIncrementCeiling y Q
  let T := sharpUniformTargetCeiling y ell
  let Rf := sharpUniformRemainderFloor Q ell
  let budget := sharpUniformLogBudget y Q ell
  have hzroom : 64 * ell ≤ z := h.z_room.trans hQz
  have hQpos : 0 < Q := by
    have : 0 < 64 * ell := Nat.mul_pos (by norm_num) h.ell_pos
    exact this.trans_le h.z_room
  have hp : p ≤ m := poolSize_lower_of_uniform hQz
  have hpoolroom : 16 * U + 256 ≤ p := by
    simpa [p] using h.pool_room
  have hmroom : 16 * U + 256 ≤ m := h.pool_room.trans hp
  have hmpos : 0 < m := by omega
  have hkUpper : k ≤ m / 8 := by
    dsimp [k, primePoolSharpPhaseCount]
    exact Nat.div_le_div_left (by omega) (by omega)
  have hdoubleEighth : 2 * (m / 8) ≤ m / 4 := by
    calc
      2 * (m / 8) ≤ (2 * m) / 8 :=
        Nat.mul_div_le_mul_div_assoc 2 m 8
      _ = m / 4 := by omega
  have hphaseHalf : 2 * k ≤ m / 4 := by
    exact (Nat.mul_le_mul_left 2 hkUpper).trans hdoubleEighth
  have hUphase : U + 1 ≤ m / 16 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 16)).2
    omega
  have hcutroom : U + k < m / 4 := by
    have hsum : U + k < 2 * (m / 8) := by
      have hk16 : k = m / 16 := rfl
      have h16le8 : m / 16 ≤ m / 8 :=
        Nat.div_le_div_left (by omega) (by omega)
      omega
    exact hsum.trans_le hdoubleEighth
  have hsourceroom : 2 * U < m / 4 := by
    have : U < m / 8 := by omega
    omega
  have hLpos : 0 < L := by
    dsimp [L, primePoolSharpLargeGain]
    apply Nat.div_pos
    · omega
    · norm_num
  have hlarge16 : 16 * L ≤ m / 8 := by
    dsimp [L, primePoolSharpLargeGain]
    calc
      16 * (m / 128) ≤ (16 * m) / 128 :=
        Nat.mul_div_le_mul_div_assoc 16 m 128
      _ = m / 8 := by omega
  have hLroom : 16 * L + k ≤ m / 4 := by
    exact (Nat.add_le_add hlarge16 hkUpper).trans (by
      simpa [two_mul] using hdoubleEighth)
  have hzpos : 0 < z := by
    have : 0 < 64 * ell := Nat.mul_pos (by norm_num) h.ell_pos
    omega
  have hzy : z ≤ y := hzM.trans h.M_le_y
  have hDgt : 1 < primePoolSharpIncrement y z := by
    unfold primePoolSharpIncrement
    have hquot : 0 < 65536 * y / z :=
      Nat.div_pos (hzy.trans (Nat.le_mul_of_pos_left y (by norm_num))) hzpos
    omega
  have heUpper : primePoolSharpIncrement y z - 1 ≤ E := by
    unfold primePoolSharpIncrement
    dsimp [E, sharpUniformIncrementCeiling]
    have hdiv : 65536 * y / z ≤ 65536 * y / Q :=
      Nat.div_le_div_left hQz hQpos
    omega
  have htarget : primePoolSharpResidueTarget y z ell d ≤ T := by
    simpa [T] using
      primePoolSharpResidueTarget_le_uniform h.ell_pos hd hzroom
  have htargetDiv : primePoolSharpResidueTarget y z ell d ≤
      sharpDivisorTargetCeiling y ell d :=
    primePoolSharpResidueTarget_le_divisor_uniform h.ell_pos hd hzroom
  have hRf : Rf ≤ primePoolSharpRemainderFloor z ell := by
    simpa [Rf] using sharpRemainderFloor_lower hQz
  refine
    { probability := ?_
      diversity_pos := ?_
      half := ?_
      cutoff_room := ?_
      source_room := ?_
      diversity_room := ?_
      largeGain_pos := hLpos
      largeGain_room := ?_
      increment_gt_one := hDgt
      increment_below_threshold := ?_
      growth_ambient := ?_
      growth_budget := ?_
      unsaturated_budget := ?_
      fiber_ambient := ?_
      polynomial_reverse := ?_
      n_pos := h.n_pos
      sieveCutoff_ge := h.sieveCutoff_ge
      sieveLevel_ge := h.sieveLevel_ge
      sieveQ_pos := h.sieveQ_pos
      log_bound := h.log_bound
      ratio_nonneg := h.ratio_nonneg
      ratio_bound := ?_
      long_scale := ?_
      sieve_reverse := ?_
      sum := ?_ }
  · have hexp : 0 ≤
        Real.exp (-(primeRandomPoolDiversity y ell : ℝ) / 24) := by
      positivity
    calc
      (2 : ℝ) * (((2 * y / d : ℕ) : ℝ) + 1) *
          Real.exp (-(primeRandomPoolDiversity y ell : ℝ) / 24) ≤
        (2 : ℝ) * (((2 * y : ℕ) : ℝ) + 1) *
          Real.exp (-(primeRandomPoolDiversity y ell : ℝ) / 24) := by
        gcongr
        exact_mod_cast Nat.div_le_self (2 * y) d
      _ < 1 := h.probability
  · unfold primeRandomPoolDiversity
    apply Nat.div_pos
    · calc
        32 * ell ≤ 128 * ell * U := by
          nlinarith [h.U_pos, h.ell_pos]
        _ ≤ fourthRootCeil y := h.diversity_room
    · exact Nat.mul_pos (by norm_num) h.ell_pos
  · simpa [k, m] using hphaseHalf
  · simpa [k, m] using hcutroom
  · simpa [m] using hsourceroom
  · unfold primeRandomPoolDiversity
    have hdiv : U ≤ fourthRootCeil y / (128 * ell) := by
      apply (Nat.le_div_iff_mul_le
        (Nat.mul_pos (by norm_num) h.ell_pos)).2
      simpa [mul_assoc, mul_comm, mul_left_comm] using h.diversity_room
    simpa [Nat.div_div_eq_div_mul, mul_assoc, mul_comm, mul_left_comm] using hdiv.trans
      (Nat.le_add_right _ 1)
  · simpa [L, k, m] using hLroom
  · exact (Nat.mul_le_mul_left 64 heUpper).trans h.increment_below
  · intro t q htLower htUpper hq hqt hscaled
    have hmul : d * (q * (4 * primePoolSharpGrowthThreshold y + 1)) ≤ y := by
      calc
        d * (q * (4 * primePoolSharpGrowthThreshold y + 1)) =
            (d * q) * (4 * primePoolSharpGrowthThreshold y + 1) := by ring
        _ ≤ U * (4 * primePoolSharpGrowthThreshold y + 1) :=
          Nat.mul_le_mul_right _ hscaled
        _ ≤ y := h.growth_ambient
    have hqfactor : q * (4 * primePoolSharpGrowthThreshold y + 1) ≤
        y / d := (Nat.le_div_iff_mul_le hd).2 (by
          simpa [mul_assoc, mul_comm, mul_left_comm] using hmul)
    have hfactor : 4 * primePoolSharpGrowthThreshold y + 1 ≤ t / q := by
      apply (Nat.le_div_iff_mul_le hq).2
      have hydivt : y / d ≤ t := (Nat.le_add_right _ 1).trans htLower
      simpa [mul_comm] using hqfactor.trans hydivt
    omega
  · intro t htLower htUpper
    have ht2y : t ≤ 2 * y := htUpper.trans (Nat.div_le_self _ _)
    have hlog : Nat.log 2 t + 1 ≤ Nat.log 2 (2 * y) + 1 :=
      Nat.add_le_add_right (Nat.log_mono_right ht2y) 1
    have hLp : p / 128 ≤ L := by
      dsimp [p, L, primePoolSharpLargeGain]
      exact Nat.div_le_div_right hp
    have hp128 : 0 < p / 128 := by
      apply Nat.div_pos
      · omega
      · norm_num
    have hquot : primePoolSharpGrowthThreshold y / L ≤
        primePoolSharpGrowthThreshold y / (p / 128) :=
      Nat.div_le_div_left hLp hp128
    have hbudget :
        (Nat.log 2 t + 1) *
            (2 * (Nat.log 2 t + 1) +
              (primePoolSharpGrowthThreshold y / L + 1)) ≤ budget := by
      dsimp [budget, sharpUniformLogBudget]
      gcongr
    have hp16 : p / 16 ≤ k := by
      dsimp [p, k, primePoolSharpPhaseCount]
      exact Nat.div_le_div_right hp
    exact hbudget.trans (h.growth_budget.trans hp16)
  · intro t htLower htUpper
    have ht2y : t ≤ 2 * y := htUpper.trans (Nat.div_le_self _ _)
    have hlog : Nat.log 2 t + 1 ≤ Nat.log 2 (2 * y) + 1 :=
      Nat.add_le_add_right (Nat.log_mono_right ht2y) 1
    have hLp : p / 128 ≤ L := by
      dsimp [p, L, primePoolSharpLargeGain]
      exact Nat.div_le_div_right hp
    have hp128 : 0 < p / 128 := by
      apply Nat.div_pos
      · omega
      · norm_num
    have hquot : primePoolSharpGrowthThreshold y / L ≤
        primePoolSharpGrowthThreshold y / (p / 128) :=
      Nat.div_le_div_left hLp hp128
    have hbudget :
        (Nat.log 2 t + 1) *
            (2 * (Nat.log 2 t + 1) +
              (primePoolSharpGrowthThreshold y / L + 1)) ≤ budget := by
      dsimp [budget, sharpUniformLogBudget]
      gcongr
    have hp16 : p / 16 ≤ k := by
      dsimp [p, k, primePoolSharpPhaseCount]
      exact Nat.div_le_div_right hp
    have hremaining : p / 16 - budget ≤ k -
        (Nat.log 2 t + 1) *
          (2 * (Nat.log 2 t + 1) +
            (primePoolSharpGrowthThreshold y / L + 1)) :=
      by omega
    have hDlower : 65536 * y / M + 1 ≤ primePoolSharpIncrement y z := by
      unfold primePoolSharpIncrement
      exact Nat.add_le_add_right
        (Nat.div_le_div_left hzM hzpos (a := 65536 * y)) 1
    exact htarget.trans (h.unsaturated_budget.trans
      ((Nat.mul_le_mul hDlower hremaining).trans_eq (by rfl)))
  · intro t q u htLower htUpper hq hqt hscaled huQ hunsat
    have hqu : q * u < primePoolSharpResidueTarget y z ell d := by
      by_contra hnot
      have hle : primePoolSharpResidueTarget y z ell d ≤ q * u :=
        Nat.le_of_not_gt hnot
      have hceil : sourceAdaptiveCeilSaturation
          (primePoolSharpResidueTarget y z ell d) q ≤ u := by
        unfold sourceAdaptiveCeilSaturation
        exact (ceilDiv_le_iff_le_mul hq).2 hle
      omega
    have hdT : d * sharpDivisorTargetCeiling y ell d ≤
        128 * y / ell + U := by
      unfold sharpDivisorTargetCeiling
      have hdiv : d * (128 * y / (ell * d)) ≤ 128 * y / ell := by
        have hmul := Nat.mul_div_le (128 * y / ell) d
        simpa only [Nat.div_div_eq_div_mul, mul_comm] using hmul
      nlinarith
    have hduq : d * (q * u) < 128 * y / ell + U := by
      calc
        d * (q * u) < d * primePoolSharpResidueTarget y z ell d :=
          Nat.mul_lt_mul_of_pos_left hqu hd
        _ ≤ d * sharpDivisorTargetCeiling y ell d :=
          Nat.mul_le_mul_left d htargetDiv
        _ ≤ 128 * y / ell + U := hdT
    have hscaledY : d * (q * (2000000000 * u)) ≤ y := by
      calc
        d * (q * (2000000000 * u)) =
            2000000000 * (d * (q * u)) := by ring
        _ ≤ 2000000000 * (128 * y / ell + U) := by
          gcongr
        _ ≤ y := h.fiber_ambient
    have hqt' : q * (2000000000 * u) ≤ y / d :=
      (Nat.le_div_iff_mul_le hd).2 (by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hscaledY)
    apply (Nat.le_div_iff_mul_le hq).2
    have hydivt : y / d ≤ t := (Nat.le_add_right _ 1).trans htLower
    simpa [mul_assoc, mul_comm, mul_left_comm] using hqt'.trans hydivt
  · intro u huQ huT
    have hepos : 0 < primePoolSharpIncrement y z - 1 :=
      Nat.sub_pos_of_lt hDgt
    exact sharpPolynomialReverse_of_uniform hepos heUpper huQ
      h.increment_below hRf h.polynomial_reverse
  · intro step hstep hstepBound
    exact h.ratio_bound step hstep
      (hstepBound.trans (Nat.div_le_self _ _ |>.trans (by omega)))
  · exact h.long_scale.trans hRf
  · intro u huQ huT
    have hfactor : 0 ≤
        ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (sieveLevel - 100)) *
          (C * ratio / Real.log (sieveCutoff : ℝ))) +
            1 / (sieveQ : ℝ) := by
      have hs : 1 < sieveCutoff := one_lt_two.trans_le h.sieveCutoff_ge
      have hlog : 0 < Real.log (sieveCutoff : ℝ) :=
        Real.log_pos (by exact_mod_cast hs)
      have hA0 : 0 ≤ A := zero_le_one.trans h.A_ge_one
      have hC0 : 0 ≤ C := h.C_pos.le
      have heta : 0 ≤
          1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (sieveLevel - 100) := by
        positivity
      have hmain : 0 ≤ C * ratio / Real.log (sieveCutoff : ℝ) := by
        apply div_nonneg _ hlog.le
        exact mul_nonneg hC0 h.ratio_nonneg
      have hqR : (0 : ℝ) < sieveQ := by exact_mod_cast h.sieveQ_pos
      exact add_nonneg (mul_nonneg heta hmain) (one_div_nonneg.mpr hqR.le)
    have heReal : (primePoolSharpIncrement y z - 1 : ℕ) ≤ E := heUpper
    calc
      (((192 * 48 : ℕ) : ℝ) * (primePoolSharpIncrement y z - 1)) *
          ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (sieveLevel - 100)) *
            (C * ratio / Real.log (sieveCutoff : ℝ)) +
              1 / (sieveQ : ℝ)) ≤
        (((192 * 48 : ℕ) : ℝ) * E) *
          ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (sieveLevel - 100)) *
            (C * ratio / Real.log (sieveCutoff : ℝ)) +
              1 / (sieveQ : ℝ)) := by
        gcongr
        calc
          (primePoolSharpIncrement y z : ℝ) - 1 =
              ((primePoolSharpIncrement y z - 1 : ℕ) : ℝ) := by
            simpa using (Nat.cast_sub hDgt.le).symm
          _ ≤ (E : ℝ) := by exact_mod_cast heReal
      _ < Rf := h.sieve_reverse
      _ ≤ primePoolSharpRemainderFloor z ell := by exact_mod_cast hRf
  · exact primeRandomPoolSize_mul_range_le_diameter h.ell_pos hd

end Erdos360
