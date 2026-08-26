import ErdosProblems.Erdos394.EulerProductLinear

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Least root times and geometric tail summation
-/

open Nat Finset

namespace Erdos394

/-- A monotone sequence telescopes through its successive natural
increments. -/
theorem initial_add_sum_successive_sub
    (T : ℕ → ℕ) (hT : Monotone T) (r : ℕ) :
    T 0 + ∑ i ∈ Finset.range r, (T (i + 1) - T i) = T r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ih]
      have hstep : T r ≤ T (r + 1) := hT (Nat.le_succ r)
      omega

/-- Geometric-layer pointwise tail decomposition for a bounded natural
variable. -/
theorem le_initial_add_tail_layers
    (T : ℕ → ℕ) (hT : Monotone T) (r n : ℕ) (hn : n ≤ T r) :
    n ≤ T 0 + ∑ i ∈ Finset.range r,
      (T (i + 1) - T i) * (if T i < n then 1 else 0) := by
  induction r with
  | zero => simpa using hn
  | succ r ih =>
      by_cases hprev : n ≤ T r
      · rw [Finset.sum_range_succ]
        have hi := ih hprev
        omega
      · have hri : T r < n := by omega
        have hall : ∀ i ∈ Finset.range (r + 1), T i < n := by
          intro i hi
          have hir : i ≤ r := by
            have := Finset.mem_range.mp hi
            omega
          exact (hT hir).trans_lt hri
        calc
          n ≤ T (r + 1) := hn
          _ = T 0 + ∑ i ∈ Finset.range (r + 1),
              (T (i + 1) - T i) :=
            (initial_add_sum_successive_sub T hT (r + 1)).symm
          _ = T 0 + ∑ i ∈ Finset.range (r + 1),
              (T (i + 1) - T i) *
                (if T i < n then 1 else 0) := by
            apply congrArg (T 0 + ·)
            apply Finset.sum_congr rfl
            intro i hi
            simp [hall i hi]

/-- Summed form of the geometric-layer tail decomposition. -/
theorem sum_le_initial_add_tail_layers
    {α : Type*} [DecidableEq α] (H : Finset α) (N : α → ℕ)
    (T : ℕ → ℕ) (hT : Monotone T) (r : ℕ)
    (hbound : ∀ h ∈ H, N h ≤ T r) :
    (∑ h ∈ H, N h) ≤
      H.card * T 0 + ∑ i ∈ Finset.range r,
        (T (i + 1) - T i) *
          (H.filter (fun h ↦ T i < N h)).card := by
  calc
    (∑ h ∈ H, N h) ≤ ∑ h ∈ H,
        (T 0 + ∑ i ∈ Finset.range r,
          (T (i + 1) - T i) * (if T i < N h then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro h hh
      exact le_initial_add_tail_layers T hT r (N h) (hbound h hh)
    _ = H.card * T 0 + ∑ i ∈ Finset.range r,
        (T (i + 1) - T i) *
          (H.filter (fun h ↦ T i < N h)).card := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.mul_sum, Finset.card_filter]

/-- `K`-adic threshold `ceil(q K^i / K^r)` used to sum the least-hit
tail in exactly `r=|P|` layers. -/
def rootBoxGeometricThreshold
    (P : Finset ℕ) (K i : ℕ) : ℕ :=
  (primeProduct P * K ^ i) ⌈/⌉ (K ^ P.card)

/-- The geometric thresholds are monotone. -/
theorem rootBoxGeometricThreshold_monotone
    (P : Finset ℕ) (K : ℕ) (hK : 0 < K) :
    Monotone (rootBoxGeometricThreshold P K) := by
  intro i j hij
  unfold rootBoxGeometricThreshold
  have hR : 0 < K ^ P.card := pow_pos hK _
  apply (gc_mul_ceilDiv hR).monotone_l
  exact Nat.mul_le_mul_left (primeProduct P) (Nat.pow_le_pow_right hK hij)

/-- The final threshold is exactly the full modulus. -/
theorem rootBoxGeometricThreshold_card
    (P : Finset ℕ) (K : ℕ) (hK : 0 < K) :
    rootBoxGeometricThreshold P K P.card = primeProduct P := by
  unfold rootBoxGeometricThreshold
  have hR : 0 < K ^ P.card := pow_pos hK _
  simpa [nsmul_eq_mul, Nat.mul_comm] using
    (smul_ceilDiv (α := ℕ) (β := ℕ) hR (primeProduct P))

/-- Every threshold up to the final layer lies below the modulus. -/
theorem rootBoxGeometricThreshold_le_primeProduct
    (P : Finset ℕ) (K i : ℕ) (hK : 0 < K) (hi : i ≤ P.card) :
    rootBoxGeometricThreshold P K i ≤ primeProduct P := by
  unfold rootBoxGeometricThreshold
  have hR : 0 < K ^ P.card := pow_pos hK _
  apply (ceilDiv_le_iff_le_mul hR).mpr
  have hpow := Nat.pow_le_pow_right hK hi
  nlinarith

/-- Elementary real upper bound for a ceiling quotient. -/
theorem natCast_ceilDiv_le_div_add_one
    (n d : ℕ) (hd : 0 < d) :
    ((n ⌈/⌉ d : ℕ) : ℝ) ≤ (n : ℝ) / (d : ℝ) + 1 := by
  have hnat : n ⌈/⌉ d ≤ n / d + 1 := by
    apply (ceilDiv_le_iff_le_mul hd).mpr
    have hlt : n < (n / d + 1) * d := by
      simpa [Nat.mul_comm] using Nat.lt_mul_div_succ n hd
    exact le_of_lt (by simpa [Nat.mul_comm] using hlt)
  calc
    ((n ⌈/⌉ d : ℕ) : ℝ) ≤ ((n / d + 1 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    _ = ((n / d : ℕ) : ℝ) + 1 := by push_cast; ring
    _ ≤ (n : ℝ) / (d : ℝ) + 1 := by
      gcongr
      exact Nat.cast_div_le

/-- A threshold increment has the expected geometric real upper bound. -/
theorem rootBoxGeometricThreshold_sub_le
    (P : Finset ℕ) (K i : ℕ) (hK : 0 < K) :
    ((rootBoxGeometricThreshold P K (i + 1) -
        rootBoxGeometricThreshold P K i : ℕ) : ℝ) ≤
      (primeProduct P : ℝ) * ((K ^ (i + 1) : ℕ) : ℝ) /
          ((K ^ P.card : ℕ) : ℝ) + 1 := by
  have hsub : rootBoxGeometricThreshold P K (i + 1) -
      rootBoxGeometricThreshold P K i ≤
      rootBoxGeometricThreshold P K (i + 1) := Nat.sub_le _ _
  calc
    ((rootBoxGeometricThreshold P K (i + 1) -
        rootBoxGeometricThreshold P K i : ℕ) : ℝ) ≤
      (rootBoxGeometricThreshold P K (i + 1) : ℝ) := by exact_mod_cast hsub
    _ ≤ (primeProduct P * K ^ (i + 1) : ℕ) /
          (K ^ P.card : ℕ) + 1 := by
      exact natCast_ceilDiv_le_div_add_one
        (primeProduct P * K ^ (i + 1)) (K ^ P.card) (pow_pos hK _)
    _ = (primeProduct P : ℝ) * ((K ^ (i + 1) : ℕ) : ℝ) /
          ((K ^ P.card : ℕ) : ℝ) + 1 := by push_cast; rfl

/-- Every geometric threshold is positive. -/
theorem rootBoxGeometricThreshold_pos
    (P : Finset ℕ) (K i : ℕ) (hK : 0 < K)
    (hprime : ∀ p ∈ P, p.Prime) :
    0 < rootBoxGeometricThreshold P K i := by
  have hR : 0 < K ^ P.card := pow_pos hK _
  have hunit : primeProduct P * K ^ i ≤
      K ^ P.card * rootBoxGeometricThreshold P K i :=
    (gc_mul_ceilDiv hR).le_u_l (primeProduct P * K ^ i)
  have hq : 0 < primeProduct P := by
    unfold primeProduct
    exact Finset.prod_pos fun p hp ↦ (hprime p hp).pos
  have hnum : 0 < primeProduct P * K ^ i :=
    Nat.mul_pos hq (pow_pos hK _)
  by_contra hz
  have : rootBoxGeometricThreshold P K i = 0 := by omega
  rw [this, Nat.mul_zero] at hunit
  omega

/-- At the `i`th threshold the continuous first-moment parameter is at least
`K^i`. -/
theorem pow_le_rootBoxMainParameter_threshold
    (P : Finset ℕ) (K i : ℕ) (hK : 0 < K)
    (hprime : ∀ p ∈ P, p.Prime) :
    ((K ^ i : ℕ) : ℝ) ≤
      rootBoxMainParameter P K (rootBoxGeometricThreshold P K i) := by
  have hR : 0 < K ^ P.card := pow_pos hK _
  have hunit : primeProduct P * K ^ i ≤
      K ^ P.card * rootBoxGeometricThreshold P K i := by
    exact (gc_mul_ceilDiv hR).le_u_l (primeProduct P * K ^ i)
  have hq : (0 : ℝ) < primeProduct P := by
    exact_mod_cast (show 0 < primeProduct P by
      unfold primeProduct
      exact Finset.prod_pos fun p hp ↦ (hprime p hp).pos)
  unfold rootBoxMainParameter
  apply (le_div_iff₀ hq).mpr
  have hunitR :
      (primeProduct P : ℝ) * ((K ^ i : ℕ) : ℝ) ≤
        ((K ^ P.card : ℕ) : ℝ) *
          (rootBoxGeometricThreshold P K i : ℝ) := by
    exact_mod_cast hunit
  simpa [mul_comm] using hunitR

/-- The explicit no-hit bound at a geometric threshold, with its
`K^{-i}` dependence made visible. -/
theorem normalized_noHit_geometricThreshold_le
    (P : Finset ℕ) (K Z i : ℕ) (hK : 1 < K) (hZ : 1 ≤ Z)
    (hP : 0 < P.card) (hprime : ∀ p ∈ P, p.Prime)
    (hKp : ∀ p ∈ P, K < p) (hK2p : ∀ p ∈ P, K * K < p)
    (hlarge : ∀ p ∈ P, Z ^ (K * K) ≤ p)
    (hZp : ∀ p ∈ P, Z ≤ p) (hZ2p : ∀ p ∈ P, Z * Z ≤ p)
    (hareaSize : ∀ p ∈ P,
      2 * P.card * K ^ P.card ≤ p - 1)
    (hratSize : ∀ p ∈ P, 4 * P.card * K ≤ p - 1)
    (hZsize : 8 * P.card * (K * K - 1) ≤ Z) :
    ((rootBoxTupleNoHitSet P K (rootBoxGeometricThreshold P K i) hprime).card : ℝ) /
        (primeUnitCount P : ℝ) ≤
      1 / ((K ^ P.card : ℕ) : ℝ) +
      (((80 : ℝ) * ((K * K - 1 : ℕ) : ℝ) + 160 * (K : ℝ)) + 2) /
        ((K ^ i : ℕ) : ℝ) +
      88 / (((K ^ i : ℕ) : ℝ) ^ 2) := by
  let C : ℝ := ((80 : ℝ) * ((K * K - 1 : ℕ) : ℝ) +
    160 * (K : ℝ)) + 2
  have htail := normalized_rootBoxTupleNoHitSet_le_of_sizes
    P K (rootBoxGeometricThreshold P K i) Z hK
    (rootBoxGeometricThreshold_pos P K i (by omega) hprime) hZ hP
    hprime hKp hK2p hlarge hZp hZ2p hareaSize hratSize hZsize
  have hmu := pow_le_rootBoxMainParameter_threshold P K i (by omega) hprime
  have hpow : (0 : ℝ) < ((K ^ i : ℕ) : ℝ) := by positivity
  have hmuPos : 0 < rootBoxMainParameter P K
      (rootBoxGeometricThreshold P K i) := hpow.trans_le hmu
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hdivC : C / rootBoxMainParameter P K
      (rootBoxGeometricThreshold P K i) ≤ C / ((K ^ i : ℕ) : ℝ) :=
    div_le_div_of_nonneg_left hC hpow hmu
  have hsquare : (((K ^ i : ℕ) : ℝ) ^ 2) ≤
      (rootBoxMainParameter P K
        (rootBoxGeometricThreshold P K i)) ^ 2 := by nlinarith
  have hdiv88 : 88 / (rootBoxMainParameter P K
      (rootBoxGeometricThreshold P K i)) ^ 2 ≤
      88 / (((K ^ i : ℕ) : ℝ) ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hpow) hsquare
  dsimp [C] at hdivC ⊢
  exact htail.trans (by gcongr)

/-- One geometric shell contributes only a constant multiple of `q/R`
to the least-hit mean. -/
theorem geometric_layer_product_le
    (K R q s C d prob : ℝ)
    (hK : 0 ≤ K) (hR : 1 ≤ R) (hqR : R ≤ q)
    (hs : 1 ≤ s) (hKs : K * s ≤ R) (hC : 0 ≤ C)
    (hd : 0 ≤ d) (hprob : 0 ≤ prob)
    (hdle : d ≤ q * K * s / R + 1)
    (hple : prob ≤ 1 / R + C / s + 88 / s ^ 2) :
    d * prob ≤ (2 + (C + 88) * (K + 1)) * (q / R) := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hq0 : 0 ≤ q := (le_trans (by norm_num : (0 : ℝ) ≤ 1) hR).trans hqR
  let A := q / R
  have hA : 1 ≤ A := by
    dsimp [A]
    apply (le_div_iff₀ hRpos).mpr
    simpa [one_mul] using hqR
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hdle' : d ≤ A * K * s + 1 := by
    dsimp [A]
    convert hdle using 1 <;> ring
  have harea : d * (1 / R) ≤ 2 * A := by
    calc
      d * (1 / R) ≤ (A * K * s + 1) * (1 / R) := by
        gcongr
      _ = (A * K * s + 1) / R := by ring
      _ ≤ 2 * A := by
        apply (div_le_iff₀ hRpos).mpr
        have hAKs : A * (K * s) ≤ A * R :=
          mul_le_mul_of_nonneg_left hKs hA0
        have hOne : 1 ≤ A * R := by
          have hh := mul_le_mul hA hR (by norm_num : (0 : ℝ) ≤ 1) hA0
          nlinarith
        nlinarith
  have hCterm : d * (C / s) ≤ C * (K + 1) * A := by
    calc
      d * (C / s) ≤ (A * K * s + 1) * (C / s) := by
        gcongr
      _ = ((A * K * s + 1) * C) / s := by ring
      _ ≤ C * (K + 1) * A := by
        apply (div_le_iff₀ hspos).mpr
        have hAs : 1 ≤ A * s := by
          have hh := mul_le_mul hA hs (by norm_num : (0 : ℝ) ≤ 1) hA0
          nlinarith
        have hins : A * K * s + 1 ≤ (K + 1) * A * s := by
          nlinarith
        have hh := mul_le_mul_of_nonneg_right hins hC
        simpa [mul_assoc, mul_left_comm, mul_comm] using hh
  have h88term : d * (88 / s ^ 2) ≤ 88 * (K + 1) * A := by
    have hs2 : 1 ≤ s ^ 2 := by nlinarith [sq_nonneg (s - 1)]
    have hs2pos : 0 < s ^ 2 := sq_pos_of_pos hspos
    calc
      d * (88 / s ^ 2) ≤ (A * K * s + 1) * (88 / s ^ 2) := by
        gcongr
      _ = ((A * K * s + 1) * 88) / s ^ 2 := by ring
      _ ≤ 88 * (K + 1) * A := by
        apply (div_le_iff₀ hs2pos).mpr
        have hsle : s ≤ s ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hs) hspos.le]
        have hAs2 : 1 ≤ A * s ^ 2 := by
          have hh := mul_le_mul_of_nonneg_right hA (sq_nonneg s)
          nlinarith
        have hins : A * K * s + 1 ≤ (K + 1) * A * s ^ 2 := by
          have hfirst : A * K * s ≤ A * K * s ^ 2 := by
            exact mul_le_mul_of_nonneg_left hsle (mul_nonneg hA0 hK)
          nlinarith
        nlinarith
  have hmul : d * prob ≤
      d * (1 / R + C / s + 88 / s ^ 2) :=
    mul_le_mul_of_nonneg_left hple hd
  dsimp [A] at harea hCterm h88term ⊢
  calc
    d * prob ≤ d * (1 / R + C / s + 88 / s ^ 2) := hmul
    _ = d * (1 / R) + d * (C / s) + d * (88 / s ^ 2) := by ring
    _ ≤ 2 * (q / R) + C * (K + 1) * (q / R) +
        88 * (K + 1) * (q / R) := by gcongr
    _ = (2 + (C + 88) * (K + 1)) * (q / R) := by ring

/-- Positive hit times through the full modulus. -/
noncomputable def rootBoxTupleHitTimes
    (P : Finset ℕ) (K : ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (h : RootBoxMultiplierTuple P) : Finset ℕ := by
  classical
  exact (Icc 1 (primeProduct P)).filter (fun j ↦
    h ∈ rootBoxGlobalHitSet P K j hprime)

/-- Time `q=∏P` is always a hit when the block contains its zero label. -/
theorem primeProduct_mem_rootBoxTupleHitTimes
    (P : Finset ℕ) (K : ℕ) (hK : 0 < K)
    (hprime : ∀ p ∈ P, p.Prime) (h : RootBoxMultiplierTuple P) :
    primeProduct P ∈ rootBoxTupleHitTimes P K hprime h := by
  classical
  have hqpos : 0 < primeProduct P := by
    unfold primeProduct
    exact Finset.prod_pos fun p hp ↦ (hprime p hp).pos
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_Icc.mpr ⟨hqpos, le_rfl⟩
  · apply (mem_rootBoxGlobalHitSet_iff P K (primeProduct P) hprime h).mpr
    intro p
    unfold localBlockHit
    refine ⟨0, Finset.mem_range.mpr hK, ?_⟩
    have hpq : p.val ∣ primeProduct P :=
      (primeProduct_dvd_iff_all_dvd P hprime (primeProduct P)).mp
        (dvd_refl (primeProduct P)) p.val p.property
    have hqz : (primeProduct P : ZMod p.val) = 0 :=
      (ZMod.natCast_eq_zero_iff (primeProduct P) p.val).mpr hpq
    simp [hqz]

/-- The full-modulus hit-time set is nonempty. -/
theorem rootBoxTupleHitTimes_nonempty
    (P : Finset ℕ) (K : ℕ) (hK : 0 < K)
    (hprime : ∀ p ∈ P, p.Prime) (h : RootBoxMultiplierTuple P) :
    (rootBoxTupleHitTimes P K hprime h).Nonempty :=
  ⟨primeProduct P,
    primeProduct_mem_rootBoxTupleHitTimes P K hK hprime h⟩

/-- Least positive block-root time for one independent CRT multiplier tuple. -/
noncomputable def rootBoxTupleLeastHit
    (P : Finset ℕ) (K : ℕ) (hK : 0 < K)
    (hprime : ∀ p ∈ P, p.Prime) (h : RootBoxMultiplierTuple P) : ℕ :=
  (rootBoxTupleHitTimes P K hprime h).min'
    (rootBoxTupleHitTimes_nonempty P K hK hprime h)

/-- The least time belongs to the hit-time set. -/
theorem rootBoxTupleLeastHit_mem
    (P : Finset ℕ) (K : ℕ) (hK : 0 < K)
    (hprime : ∀ p ∈ P, p.Prime) (h : RootBoxMultiplierTuple P) :
    rootBoxTupleLeastHit P K hK hprime h ∈
      rootBoxTupleHitTimes P K hprime h :=
  Finset.min'_mem _ _

/-- The least time is positive and no larger than the modulus. -/
theorem rootBoxTupleLeastHit_bounds
    (P : Finset ℕ) (K : ℕ) (hK : 0 < K)
    (hprime : ∀ p ∈ P, p.Prime) (h : RootBoxMultiplierTuple P) :
    1 ≤ rootBoxTupleLeastHit P K hK hprime h ∧
      rootBoxTupleLeastHit P K hK hprime h ≤ primeProduct P := by
  have hm := rootBoxTupleLeastHit_mem P K hK hprime h
  exact (Finset.mem_filter.mp hm).1 |> Finset.mem_Icc.mp

/-- A tuple has no hit through `Y≤q` exactly when its least hit exceeds `Y`. -/
theorem rootBoxTupleHitNumber_eq_zero_iff_lt_least
    (P : Finset ℕ) (K Y : ℕ) (hK : 0 < K)
    (hprime : ∀ p ∈ P, p.Prime) (hYq : Y ≤ primeProduct P)
    (h : RootBoxMultiplierTuple P) :
    rootBoxTupleHitNumber P K Y hprime h = 0 ↔
      Y < rootBoxTupleLeastHit P K hK hprime h := by
  classical
  let m := rootBoxTupleLeastHit P K hK hprime h
  constructor
  · intro hzero
    by_contra hnot
    have hmY : m ≤ Y := by omega
    have hmmem := rootBoxTupleLeastHit_mem P K hK hprime h
    have hmI := Finset.mem_Icc.mp (Finset.mem_filter.mp hmmem).1
    have hmhit := (Finset.mem_filter.mp hmmem).2
    have hmSmall : m ∈ (Icc 1 Y).filter (fun j ↦
        h ∈ rootBoxGlobalHitSet P K j hprime) :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hmI.1, hmY⟩, hmhit⟩
    unfold rootBoxTupleHitNumber at hzero
    have : ((Icc 1 Y).filter (fun j ↦
        h ∈ rootBoxGlobalHitSet P K j hprime)).Nonempty := ⟨m, hmSmall⟩
    rw [Finset.card_eq_zero] at hzero
    exact this.ne_empty hzero
  · intro hYm
    unfold rootBoxTupleHitNumber
    rw [Finset.card_eq_zero]
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hne
    obtain ⟨j, hj⟩ := hne
    have hjI := Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1
    have hjhit := (Finset.mem_filter.mp hj).2
    have hjFull : j ∈ rootBoxTupleHitTimes P K hprime h := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Icc.mpr ⟨hjI.1, hjI.2.trans hYq⟩, hjhit⟩
    have hmj : rootBoxTupleLeastHit P K hK hprime h ≤ j :=
      Finset.min'_le _ _ hjFull
    omega

/-- The least-hit upper-tail set is exactly the no-hit set. -/
theorem filter_leastHit_gt_eq_noHitSet
    (P : Finset ℕ) (K Y : ℕ) (hK : 0 < K)
    (hprime : ∀ p ∈ P, p.Prime) (hYq : Y ≤ primeProduct P) :
    (rootBoxMultiplierUniverse P hprime).filter (fun h ↦
      Y < rootBoxTupleLeastHit P K hK hprime h) =
      rootBoxTupleNoHitSet P K Y hprime := by
  classical
  unfold rootBoxTupleNoHitSet
  apply Finset.filter_congr
  intro h hh
  exact (rootBoxTupleHitNumber_eq_zero_iff_lt_least
    P K Y hK hprime hYq h).symm

/-- Complete finite mean estimate: under the explicit large-prime
hypotheses, the average least root is `O_K((r+1)q/K^r)`. -/
theorem normalized_sum_rootBoxTupleLeastHit_le
    (P : Finset ℕ) (K Z : ℕ) (hK : 1 < K)
    (hZ : 1 ≤ Z) (hP : 0 < P.card)
    (hprime : ∀ p ∈ P, p.Prime)
    (hKp : ∀ p ∈ P, K < p) (hK2p : ∀ p ∈ P, K * K < p)
    (hlarge : ∀ p ∈ P, Z ^ (K * K) ≤ p)
    (hZp : ∀ p ∈ P, Z ≤ p) (hZ2p : ∀ p ∈ P, Z * Z ≤ p)
    (hareaSize : ∀ p ∈ P,
      2 * P.card * K ^ P.card ≤ p - 1)
    (hratSize : ∀ p ∈ P, 4 * P.card * K ≤ p - 1)
    (hZsize : 8 * P.card * (K * K - 1) ≤ Z)
    (hRq : K ^ P.card ≤ primeProduct P) :
    (∑ h ∈ rootBoxMultiplierUniverse P hprime,
        (rootBoxTupleLeastHit P K (by omega) hprime h : ℝ)) /
        (primeUnitCount P : ℝ) ≤
      (2 + (P.card : ℝ) *
        (2 + ((((80 : ℝ) * ((K * K - 1 : ℕ) : ℝ) +
          160 * (K : ℝ)) + 2) + 88) * ((K : ℝ) + 1))) *
        ((primeProduct P : ℝ) / ((K ^ P.card : ℕ) : ℝ)) := by
  classical
  let H := rootBoxMultiplierUniverse P hprime
  let N : RootBoxMultiplierTuple P → ℕ :=
    rootBoxTupleLeastHit P K (by omega) hprime
  let T : ℕ → ℕ := rootBoxGeometricThreshold P K
  let r := P.card
  let q := primeProduct P
  let R := K ^ P.card
  let C : ℝ := ((80 : ℝ) * ((K * K - 1 : ℕ) : ℝ) +
    160 * (K : ℝ)) + 2
  let D : ℝ := 2 + (C + 88) * ((K : ℝ) + 1)
  have hTmono : Monotone T :=
    rootBoxGeometricThreshold_monotone P K (by omega)
  have hTlast : T r = q := by
    exact rootBoxGeometricThreshold_card P K (by omega)
  have hNbound : ∀ h ∈ H, N h ≤ T r := by
    intro h hh
    rw [hTlast]
    exact (rootBoxTupleLeastHit_bounds P K (by omega) hprime h).2
  have hsumNat := sum_le_initial_add_tail_layers H N T hTmono r hNbound
  have hsumR : (∑ h ∈ H, (N h : ℝ)) ≤
      (H.card : ℝ) * (T 0 : ℝ) +
        ∑ i ∈ Finset.range r,
          ((T (i + 1) - T i : ℕ) : ℝ) *
            (((H.filter (fun h ↦ T i < N h)).card : ℝ)) := by
    exact_mod_cast hsumNat
  have hphiNat : 0 < primeUnitCount P := by
    unfold primeUnitCount
    exact Finset.prod_pos fun p hp ↦ by
      have hp2 := (hprime p hp).two_le
      omega
  have hHcard : H.card = primeUnitCount P :=
    card_rootBoxMultiplierUniverse P hprime
  have hphi : (0 : ℝ) < primeUnitCount P := by exact_mod_cast hphiNat
  have hmeanRaw :
      (∑ h ∈ H, (N h : ℝ)) / (primeUnitCount P : ℝ) ≤
        (T 0 : ℝ) + ∑ i ∈ Finset.range r,
          ((T (i + 1) - T i : ℕ) : ℝ) *
            (((H.filter (fun h ↦ T i < N h)).card : ℝ) /
              (primeUnitCount P : ℝ)) := by
    rw [← hHcard]
    have hHposNat : 0 < H.card := by rw [hHcard]; exact hphiNat
    have hHpos : (0 : ℝ) < H.card := by exact_mod_cast hHposNat
    have hdiv := (div_le_div_iff_of_pos_right hHpos).mpr hsumR
    calc
      (∑ h ∈ H, (N h : ℝ)) / (H.card : ℝ) ≤
          ((H.card : ℝ) * (T 0 : ℝ) +
            ∑ i ∈ Finset.range r,
              ((T (i + 1) - T i : ℕ) : ℝ) *
                ((H.filter (fun h ↦ T i < N h)).card : ℝ)) /
              (H.card : ℝ) := hdiv
      _ = (T 0 : ℝ) + ∑ i ∈ Finset.range r,
          ((T (i + 1) - T i : ℕ) : ℝ) *
            (((H.filter (fun h ↦ T i < N h)).card : ℝ) /
              (H.card : ℝ)) := by
        rw [add_div, Finset.sum_div]
        congr 1
        · field_simp
        · apply Finset.sum_congr rfl
          intro i hi
          ring
  have hqR : (1 : ℝ) ≤ (q : ℝ) / (R : ℝ) := by
    have hRpos : (0 : ℝ) < R := by
      dsimp [R]
      positivity
    apply (le_div_iff₀ hRpos).mpr
    have hRqR : (R : ℝ) ≤ (q : ℝ) := by
      dsimp [R, q]
      exact_mod_cast hRq
    simpa using hRqR
  have hbase : (T 0 : ℝ) ≤ 2 * ((q : ℝ) / (R : ℝ)) := by
    have hu := natCast_ceilDiv_le_div_add_one q R (by
      dsimp [R]
      exact pow_pos (by omega) _)
    have hu' : (T 0 : ℝ) ≤ (q : ℝ) / (R : ℝ) + 1 := by
      simpa [T, q, R, rootBoxGeometricThreshold] using hu
    calc
      (T 0 : ℝ) ≤ (q : ℝ) / (R : ℝ) + 1 := hu'
      _ ≤ 2 * ((q : ℝ) / (R : ℝ)) := by nlinarith
  have hlayer : ∀ i ∈ Finset.range r,
      ((T (i + 1) - T i : ℕ) : ℝ) *
          (((H.filter (fun h ↦ T i < N h)).card : ℝ) /
            (primeUnitCount P : ℝ)) ≤
        D * ((q : ℝ) / (R : ℝ)) := by
    intro i hi
    have hir : i < r := Finset.mem_range.mp hi
    have hi1r : i + 1 ≤ P.card := by dsimp [r] at hir; omega
    have hTiQ : T i ≤ primeProduct P := by
      exact rootBoxGeometricThreshold_le_primeProduct P K i (by omega)
        (by dsimp [r] at hir; omega)
    have hfilter : H.filter (fun h ↦ T i < N h) =
        rootBoxTupleNoHitSet P K (T i) hprime := by
      dsimp [H, N, T]
      exact filter_leastHit_gt_eq_noHitSet P K
        (rootBoxGeometricThreshold P K i) (by omega) hprime hTiQ
    have htail := normalized_noHit_geometricThreshold_le
      P K Z i hK hZ hP hprime hKp hK2p hlarge hZp hZ2p
      hareaSize hratSize hZsize
    have hple :
        (((H.filter (fun h ↦ T i < N h)).card : ℝ) /
            (primeUnitCount P : ℝ)) ≤
          1 / (R : ℝ) + C / ((K ^ i : ℕ) : ℝ) +
            88 / (((K ^ i : ℕ) : ℝ) ^ 2) := by
      rw [hfilter]
      simpa [R, C] using htail
    have hdle := rootBoxGeometricThreshold_sub_le P K i (by omega)
    have hKsNat : K * K ^ i ≤ R := by
      have hh := Nat.pow_le_pow_right (by omega : 0 < K) hi1r
      simpa [R, pow_succ, Nat.mul_comm] using hh
    have hKs : (K : ℝ) * ((K ^ i : ℕ) : ℝ) ≤ (R : ℝ) := by
      exact_mod_cast hKsNat
    have hRone : (1 : ℝ) ≤ R := by
      exact_mod_cast (show 1 ≤ R by
        have : 0 < R := by dsimp [R]; positivity
        omega)
    have hsone : (1 : ℝ) ≤ ((K ^ i : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ K ^ i by
        have : 0 < K ^ i := pow_pos (by omega) _
        omega)
    have hd0 : (0 : ℝ) ≤ ((T (i + 1) - T i : ℕ) : ℝ) := by positivity
    have hp0 : (0 : ℝ) ≤
        ((H.filter (fun h ↦ T i < N h)).card : ℝ) /
          (primeUnitCount P : ℝ) := by positivity
    have hqRcast : (R : ℝ) ≤ (q : ℝ) := by exact_mod_cast hRq
    have hl := geometric_layer_product_le
      (K : ℝ) (R : ℝ) (q : ℝ) ((K ^ i : ℕ) : ℝ) C
      ((T (i + 1) - T i : ℕ) : ℝ)
      (((H.filter (fun h ↦ T i < N h)).card : ℝ) /
        (primeUnitCount P : ℝ))
      (by positivity) hRone hqRcast hsone hKs (by dsimp [C]; positivity)
      hd0 hp0 (by
        norm_num only [Nat.cast_pow] at hdle
        simpa [q, R, T, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hdle) hple
    simpa [D] using hl
  calc
    (∑ h ∈ rootBoxMultiplierUniverse P hprime,
        (rootBoxTupleLeastHit P K (by omega) hprime h : ℝ)) /
        (primeUnitCount P : ℝ) =
      (∑ h ∈ H, (N h : ℝ)) / (primeUnitCount P : ℝ) := by rfl
    _ ≤ (T 0 : ℝ) + ∑ i ∈ Finset.range r,
          ((T (i + 1) - T i : ℕ) : ℝ) *
            (((H.filter (fun h ↦ T i < N h)).card : ℝ) /
              (primeUnitCount P : ℝ)) := hmeanRaw
    _ ≤ 2 * ((q : ℝ) / (R : ℝ)) +
        ∑ _i ∈ Finset.range r, D * ((q : ℝ) / (R : ℝ)) := by
      apply add_le_add hbase
      apply Finset.sum_le_sum
      intro i hi
      exact hlayer i hi
    _ = (2 + (r : ℝ) * D) * ((q : ℝ) / (R : ℝ)) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    _ = (2 + (P.card : ℝ) *
        (2 + ((((80 : ℝ) * ((K * K - 1 : ℕ) : ℝ) +
          160 * (K : ℝ)) + 2) + 88) * ((K : ℝ) + 1))) *
        ((primeProduct P : ℝ) / ((K ^ P.card : ℕ) : ℝ)) := by
      rfl


end Erdos394
