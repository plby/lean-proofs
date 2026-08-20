import ErdosProblems.Erdos525.Endpoint

open scoped BigOperators Topology ComplexConjugate RealInnerProductSpace

namespace Erdos525

open Classical Filter Finset Set MeasureTheory

/-!  Deterministic covers used for the nonsmooth (major-arc) part of the
minimum-modulus argument.  The endpoint cover is graded by powers of `n`;
the interior cover is the elementary rational-arc cover obtained directly
from the negation of `IsSmooth`. -/

noncomputable def badArcCoarseWidth (n : ℕ) : ℝ :=
  rigidityPower n (-1 / 4)

noncomputable def endpointShellLower (n ℓ : ℕ) : ℝ :=
  rigidityPower n (((ℓ : ℝ) - 48) / 128)

noncomputable def endpointShellStep (n ℓ : ℕ) : ℝ :=
  endpointShellLower n ℓ * rigidityPower n (-1 / 16)

noncomputable def endpointShellUpper (n ℓ : ℕ) : ℝ :=
  rigidityPower n (((ℓ : ℝ) - 47) / 128)

noncomputable def endpointShellCount (n ℓ : ℕ) : ℕ :=
  Nat.floor ((endpointShellUpper n ℓ - endpointShellLower n ℓ) /
    endpointShellStep n ℓ) + 1

noncomputable def endpointShellPoint (n ℓ b : ℕ) : ℝ :=
  endpointShellLower n ℓ + b * endpointShellStep n ℓ

noncomputable def endpointCover (n : ℕ) : Finset ℝ :=
  (Finset.range 49).biUnion fun ℓ ↦
    (Finset.range (endpointShellCount n ℓ)).image
      (endpointShellPoint n ℓ)

lemma endpointShellLower_pos {n : ℕ} (hn : 0 < n) (ℓ : ℕ) :
    0 < endpointShellLower n ℓ := by
  unfold endpointShellLower
  exact rigidityPower_pos hn _

lemma endpointShellStep_pos {n : ℕ} (hn : 0 < n) (ℓ : ℕ) :
    0 < endpointShellStep n ℓ := by
  unfold endpointShellStep
  exact mul_pos (endpointShellLower_pos hn ℓ) (rigidityPower_pos hn _)

lemma endpointShellUpper_eq_next (n ℓ : ℕ) :
    endpointShellUpper n ℓ = endpointShellLower n (ℓ + 1) := by
  unfold endpointShellUpper endpointShellLower
  congr 2
  push_cast
  ring

lemma mem_endpointCover_of_mem_shell
    {n ℓ : ℕ} (hℓ : ℓ < 49) {t : ℝ}
    (htl : endpointShellLower n ℓ ≤ t)
    (htu : t < endpointShellUpper n ℓ)
    (hn : 0 < n) :
    ∃ b < endpointShellCount n ℓ,
      endpointShellPoint n ℓ b ≤ t ∧
        t - endpointShellPoint n ℓ b < endpointShellStep n ℓ ∧
        endpointShellLower n ℓ ≤ endpointShellPoint n ℓ b := by
  let x : ℝ := (t - endpointShellLower n ℓ) / endpointShellStep n ℓ
  let b : ℕ := Nat.floor x
  have hstep := endpointShellStep_pos hn ℓ
  have hx0 : 0 ≤ x := div_nonneg (sub_nonneg.mpr htl) hstep.le
  have hbLower : (b : ℝ) ≤ x := Nat.floor_le hx0
  have hbUpper : x < b + 1 := Nat.lt_floor_add_one x
  have hbCount : b < endpointShellCount n ℓ := by
    unfold endpointShellCount
    have hxBound : x <
        (endpointShellUpper n ℓ - endpointShellLower n ℓ) /
          endpointShellStep n ℓ := by
      dsimp [x]
      exact div_lt_div_of_pos_right (sub_lt_sub_right htu _) hstep
    have hfloorBound : b ≤ Nat.floor
        ((endpointShellUpper n ℓ - endpointShellLower n ℓ) /
          endpointShellStep n ℓ) := by
      apply Nat.floor_mono
      exact hxBound.le
    omega
  refine ⟨b, hbCount, ?_, ?_, ?_⟩
  · dsimp [endpointShellPoint, x, b] at *
    rw [le_div_iff₀ hstep] at hbLower
    linarith
  · dsimp [endpointShellPoint, x, b] at *
    rw [div_lt_iff₀ hstep] at hbUpper
    linarith
  · dsimp [endpointShellPoint]
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hstep.le)

lemma exists_endpoint_shell_of_range
    {n : ℕ} (hn : 1 ≤ n) {t : ℝ}
    (hlower : endpointExclusionRadius n ≤ t)
    (hupper : t < endpointShellUpper n 48) :
    ∃ ℓ < 49,
      endpointShellLower n ℓ ≤ t ∧ t < endpointShellUpper n ℓ := by
  have hbase : endpointShellLower n 0 = endpointExclusionRadius n := by
    unfold endpointShellLower endpointExclusionRadius
    congr 1
    norm_num
  by_contra hnot
  push Not at hnot
  have hall : ∀ ℓ ≤ 49, endpointShellLower n ℓ ≤ t := by
    intro ℓ hℓ
    induction ℓ with
    | zero => simpa [hbase] using hlower
    | succ k ih =>
        rw [← endpointShellUpper_eq_next]
        exact hnot k (by omega) (ih (by omega))
  have hlast : endpointShellUpper n 48 ≤ t := by
    rw [endpointShellUpper_eq_next]
    exact hall 49 le_rfl
  exact (not_lt_of_ge hlast) hupper

lemma exists_endpointCover_point
    {n : ℕ} (hn : 0 < n) {t : ℝ}
    (hlower : endpointExclusionRadius n ≤ t)
    (hupper : t < endpointShellUpper n 48) :
    ∃ ℓ < 49, ∃ b < endpointShellCount n ℓ,
      endpointShellPoint n ℓ b ≤ t ∧
        t - endpointShellPoint n ℓ b < endpointShellStep n ℓ ∧
        endpointShellLower n ℓ ≤ endpointShellPoint n ℓ b := by
  rcases exists_endpoint_shell_of_range hn hlower hupper with
    ⟨ℓ, hℓ, htl, htu⟩
  rcases mem_endpointCover_of_mem_shell hℓ htl htu hn with
    ⟨b, hb, hqt, hdist, hql⟩
  exact ⟨ℓ, hℓ, b, hb, hqt, hdist, hql⟩

lemma endpointShellUpper_div_step_eq
    {n : ℕ} (hn : 0 < n) (ℓ : ℕ) :
    endpointShellUpper n ℓ / endpointShellStep n ℓ =
      rigidityPower n (9 / 128) := by
  unfold endpointShellUpper endpointShellStep endpointShellLower
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold rigidityPower
  rw [div_mul_eq_div_mul_one_div, div_eq_mul_inv]
  simp only [one_div]
  rw [← Real.rpow_neg hnR.le, ← Real.rpow_neg hnR.le]
  rw [← Real.rpow_add hnR, ← Real.rpow_add hnR]
  congr 2
  push_cast
  ring

lemma endpointShellCount_cast_le
    {n : ℕ} (hn : 0 < n) (ℓ : ℕ) :
    (endpointShellCount n ℓ : ℝ) ≤
      2 * rigidityPower n (9 / 128) := by
  have hstep := endpointShellStep_pos hn ℓ
  have hlower := (endpointShellLower_pos hn ℓ).le
  have hratio0 : 0 ≤
      (endpointShellUpper n ℓ - endpointShellLower n ℓ) /
        endpointShellStep n ℓ := by
    apply div_nonneg
    · apply sub_nonneg.mpr
      rw [endpointShellUpper_eq_next]
      unfold endpointShellLower
      apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast (show 1 ≤ n by omega)
      · push_cast
        linarith
    · exact hstep.le
  have hfloor := Nat.floor_le hratio0
  have hratio :
      (endpointShellUpper n ℓ - endpointShellLower n ℓ) /
          endpointShellStep n ℓ ≤
        endpointShellUpper n ℓ / endpointShellStep n ℓ := by
    exact div_le_div_of_nonneg_right
      (sub_le_self _ hlower) hstep.le
  have hone : 1 ≤ rigidityPower n (9 / 128) := by
    unfold rigidityPower
    exact Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega))
      (by norm_num)
  unfold endpointShellCount
  push_cast
  calc
    (Nat.floor ((endpointShellUpper n ℓ - endpointShellLower n ℓ) /
          endpointShellStep n ℓ) : ℝ) + 1 ≤
        (endpointShellUpper n ℓ - endpointShellLower n ℓ) /
          endpointShellStep n ℓ + 1 := by
      simpa [add_comm] using add_le_add_right hfloor 1
    _ ≤ endpointShellUpper n ℓ / endpointShellStep n ℓ + 1 :=
      by simpa [add_comm] using add_le_add_right hratio 1
    _ = rigidityPower n (9 / 128) + 1 := by
      rw [endpointShellUpper_div_step_eq hn]
    _ ≤ 2 * rigidityPower n (9 / 128) := by linarith

lemma endpointCover_card_cast_le
    {n : ℕ} (hn : 0 < n) :
    ((endpointCover n).card : ℝ) ≤
      98 * rigidityPower n (9 / 128) := by
  have hcardNat : (endpointCover n).card ≤
      ∑ ℓ ∈ Finset.range 49, endpointShellCount n ℓ := by
    unfold endpointCover
    calc
      ((Finset.range 49).biUnion fun ℓ ↦
          (Finset.range (endpointShellCount n ℓ)).image
            (endpointShellPoint n ℓ)).card ≤
          ∑ ℓ ∈ Finset.range 49,
            ((Finset.range (endpointShellCount n ℓ)).image
              (endpointShellPoint n ℓ)).card :=
        Finset.card_biUnion_le (M := ℝ)
      _ ≤ ∑ ℓ ∈ Finset.range 49, endpointShellCount n ℓ := by
        apply Finset.sum_le_sum
        intro ℓ hℓ
        simpa using (Finset.card_image_le
          (s := Finset.range (endpointShellCount n ℓ))
          (f := endpointShellPoint n ℓ))
  have hcardR : ((endpointCover n).card : ℝ) ≤
      ∑ ℓ ∈ Finset.range 49, (endpointShellCount n ℓ : ℝ) := by
    exact_mod_cast hcardNat
  calc
    ((endpointCover n).card : ℝ) ≤
        ∑ ℓ ∈ Finset.range 49, (endpointShellCount n ℓ : ℝ) := hcardR
    _ ≤ ∑ _ℓ ∈ Finset.range 49,
        2 * rigidityPower n (9 / 128) := by
      apply Finset.sum_le_sum
      intro ℓ _hℓ
      exact endpointShellCount_cast_le hn ℓ
    _ = 98 * rigidityPower n (9 / 128) := by
      simp
      ring

lemma endpointShellCounts_sum_cast_le
    {n : ℕ} (hn : 0 < n) :
    (∑ ℓ ∈ Finset.range 49, (endpointShellCount n ℓ : ℝ)) ≤
      98 * rigidityPower n (9 / 128) := by
  calc
    (∑ ℓ ∈ Finset.range 49, (endpointShellCount n ℓ : ℝ)) ≤
        ∑ _ℓ ∈ Finset.range 49,
          2 * rigidityPower n (9 / 128) := by
      apply Finset.sum_le_sum
      intro ℓ _hℓ
      exact endpointShellCount_cast_le hn ℓ
    _ = 98 * rigidityPower n (9 / 128) := by
      simp
      ring

noncomputable def interiorArcDenominatorCount (n : ℕ) : ℕ :=
  Nat.floor (4 * rigiditySmoothScale n) + 1

noncomputable def interiorArcGridCount (n : ℕ) : ℕ :=
  Nat.floor ((8 * Real.pi * rigiditySmoothScale n) /
    badArcCoarseWidth n) + 1

noncomputable def interiorArcPoint
    (n p : ℕ) (z : ℤ) (b : ℕ) : ℝ :=
  Real.pi * n * z / p - 4 * Real.pi * rigiditySmoothScale n +
    b * badArcCoarseWidth n

noncomputable def interiorArcCover (n : ℕ) : Finset ℝ :=
  (Finset.Icc 1 (interiorArcDenominatorCount n)).biUnion fun p ↦
    (Finset.Icc (-((interiorArcDenominatorCount n : ℕ) : ℤ) - 1)
      ((interiorArcDenominatorCount n : ℕ) + 1)).biUnion fun z ↦
        (Finset.range (interiorArcGridCount n)).image
          (interiorArcPoint n p z)

lemma badArcCoarseWidth_pos {n : ℕ} (hn : 0 < n) :
    0 < badArcCoarseWidth n := by
  unfold badArcCoarseWidth
  exact rigidityPower_pos hn _

lemma nonsmooth_has_nearby_interiorArcPoint
    {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi * n))
    (hbad : ¬IsSmooth n (4 * rigiditySmoothScale n) t) :
    ∃ q ∈ interiorArcCover n,
      q ≤ t ∧ t - q < badArcCoarseWidth n := by
  rw [IsSmooth] at hbad
  push Not at hbad
  rcases hbad with ⟨p, hp1, hpP, hpdist⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp1
  let y : ℝ := p * t / (Real.pi * n)
  rcases exists_int_add_centeredModOne y with ⟨z, hz⟩
  have hsub : y - (z : ℝ) = centeredModOne y := by
    calc
      y - (z : ℝ) = ((z : ℝ) + centeredModOne y) - z :=
        congrArg (fun w : ℝ ↦ w - z) hz
      _ = centeredModOne y := by ring
  have herror : |y - z| = distanceToInteger y := by
    calc
      |y - z| = |centeredModOne y| := by rw [hsub]
      _ = distanceToInteger y := abs_centeredModOne_eq_distanceToInteger y
  have hy0 : 0 ≤ y := by
    dsimp [y]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg p) ht.1)
      (mul_pos Real.pi_pos hnR).le
  have hyp : y ≤ p := by
    dsimp [y]
    rw [div_le_iff₀ (mul_pos Real.pi_pos hnR)]
    nlinarith [ht.2, Real.pi_pos]
  have hdistHalf : distanceToInteger y ≤ 1 / 2 :=
    distanceToInteger_le_half y
  have hzLowerR : (-1 : ℝ) ≤ z := by
    have habs : |y - z| ≤ 1 / 2 := herror.trans_le hdistHalf
    rw [abs_le] at habs
    linarith
  have hzUpperR : (z : ℝ) ≤ p + 1 := by
    have habs : |y - z| ≤ 1 / 2 := herror.trans_le hdistHalf
    rw [abs_le] at habs
    linarith
  have hpCount : p ≤ interiorArcDenominatorCount n := by
    simpa [interiorArcDenominatorCount] using hpP
  have hzMem : z ∈ Finset.Icc
      (-((interiorArcDenominatorCount n : ℕ) : ℤ) - 1)
      ((interiorArcDenominatorCount n : ℕ) + 1) := by
    rw [Finset.mem_Icc]
    constructor
    · have hzLower : (-1 : ℤ) ≤ z := by exact_mod_cast hzLowerR
      omega
    · have hzUpper : z ≤ (p : ℤ) + 1 := by exact_mod_cast hzUpperR
      exact hzUpper.trans (by exact_mod_cast Nat.add_le_add_right hpCount 1)
  let c : ℝ := Real.pi * n * z / p
  have hclose : |t - c| ≤ 4 * Real.pi * rigiditySmoothScale n := by
    have hid : t - c = (Real.pi * n / p) * (y - z) := by
      dsimp [c, y]
      field_simp [hpR.ne', hnR.ne', Real.pi_ne_zero]
    rw [hid, abs_mul, abs_of_pos (div_pos (mul_pos Real.pi_pos hnR) hpR)]
    have hdist : distanceToInteger y ≤
        4 * rigiditySmoothScale n / n := by simpa [y] using hpdist
    rw [herror]
    calc
      Real.pi * n / p * distanceToInteger y ≤
          Real.pi * n / p * (4 * rigiditySmoothScale n / n) := by
        gcongr
      _ = 4 * Real.pi * rigiditySmoothScale n / p := by
        field_simp [hnR.ne']
      _ ≤ 4 * Real.pi * rigiditySmoothScale n := by
        rw [div_le_iff₀ hpR]
        have hA : 0 ≤ 4 * Real.pi * rigiditySmoothScale n := by
          exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
            (by unfold rigiditySmoothScale; exact rigidityPower_nonneg n _)
        have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hp1
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hpOne hA
  let x : ℝ :=
    (t - (c - 4 * Real.pi * rigiditySmoothScale n)) /
      badArcCoarseWidth n
  let b : ℕ := Nat.floor x
  have hwidth := badArcCoarseWidth_pos hn
  have hx0 : 0 ≤ x := by
    apply div_nonneg
    · rw [abs_le] at hclose
      linarith
    · exact hwidth.le
  have hxUpper : x ≤
      (8 * Real.pi * rigiditySmoothScale n) / badArcCoarseWidth n := by
    apply (div_le_div_iff_of_pos_right hwidth).2
    rw [abs_le] at hclose
    linarith
  have hbLower : (b : ℝ) ≤ x := Nat.floor_le hx0
  have hbUpperNat : b < interiorArcGridCount n := by
    have hfloor : b ≤ Nat.floor
        ((8 * Real.pi * rigiditySmoothScale n) / badArcCoarseWidth n) := by
      exact Nat.floor_mono hxUpper
    unfold interiorArcGridCount
    omega
  have hbOne : x < b + 1 := Nat.lt_floor_add_one x
  let q : ℝ := interiorArcPoint n p z b
  refine ⟨q, ?_, ?_, ?_⟩
  · unfold interiorArcCover
    apply Finset.mem_biUnion.mpr
    refine ⟨p, Finset.mem_Icc.mpr ⟨hp1, hpCount⟩, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨z, hzMem, ?_⟩
    exact Finset.mem_image.mpr ⟨b, Finset.mem_range.mpr hbUpperNat, rfl⟩
  · dsimp [q, interiorArcPoint, c, x, b] at *
    rw [le_div_iff₀ hwidth] at hbLower
    linarith
  · dsimp [q, interiorArcPoint, c, x, b] at *
    rw [div_lt_iff₀ hwidth] at hbOne
    linarith

lemma rigiditySmoothScale_div_badArcCoarseWidth
    {n : ℕ} (hn : 0 < n) :
    rigiditySmoothScale n / badArcCoarseWidth n =
      rigidityPower n (5 / 16) := by
  unfold rigiditySmoothScale rigiditySmoothExponent badArcCoarseWidth
    rigidityPower
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_eq_mul_inv, ← Real.rpow_neg hnR.le, ← Real.rpow_add hnR]
  congr 2
  norm_num

lemma interiorArcDenominatorCount_cast_le
    {n : ℕ} (hn : 0 < n) :
    (interiorArcDenominatorCount n : ℝ) ≤
      5 * rigidityPower n (1 / 16) := by
  have hK : 1 ≤ rigiditySmoothScale n := by
    unfold rigiditySmoothScale rigiditySmoothExponent rigidityPower
    exact Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega))
      (by norm_num)
  have hK0 : 0 ≤ rigiditySmoothScale n := by
    unfold rigiditySmoothScale
    exact rigidityPower_nonneg n _
  have hfloor : ((Nat.floor (4 * rigiditySmoothScale n) : ℕ) : ℝ) ≤
      4 * rigiditySmoothScale n :=
    Nat.floor_le (mul_nonneg (by norm_num) hK0)
  unfold interiorArcDenominatorCount
  push_cast
  calc
    (Nat.floor (4 * rigiditySmoothScale n) : ℝ) + 1 ≤
        4 * rigiditySmoothScale n + 1 := by
      simpa [add_comm] using add_le_add_right hfloor 1
    _ ≤ 5 * rigiditySmoothScale n := by linarith
    _ = 5 * rigidityPower n (1 / 16) := by
      unfold rigiditySmoothScale rigiditySmoothExponent
      rfl

lemma interiorArcIntegerCount_cast_le
    {n : ℕ} (hn : 0 < n) :
    ((Finset.Icc (-((interiorArcDenominatorCount n : ℕ) : ℤ) - 1)
      ((interiorArcDenominatorCount n : ℕ) + 1)).card : ℝ) ≤
        13 * rigidityPower n (1 / 16) := by
  let P := interiorArcDenominatorCount n
  have hcard : (Finset.Icc (-((P : ℕ) : ℤ) - 1)
      ((P : ℕ) + 1)).card = 2 * P + 3 := by
    rw [Int.card_Icc]
    omega
  rw [hcard]
  push_cast
  have hP := interiorArcDenominatorCount_cast_le hn
  have hpow : 1 ≤ rigidityPower n (1 / 16) := by
    unfold rigidityPower
    exact Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega))
      (by norm_num)
  dsimp [P] at *
  nlinarith

lemma interiorArcGridCount_cast_le
    {n : ℕ} (hn : 0 < n) :
    (interiorArcGridCount n : ℝ) ≤
      33 * rigidityPower n (5 / 16) := by
  have hwidth := badArcCoarseWidth_pos hn
  have hratio0 : 0 ≤
      (8 * Real.pi * rigiditySmoothScale n) / badArcCoarseWidth n := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
        (by unfold rigiditySmoothScale; exact rigidityPower_nonneg n _))
      (badArcCoarseWidth_pos hn).le
  have hfloor := Nat.floor_le hratio0
  have hratio :
      (8 * Real.pi * rigiditySmoothScale n) / badArcCoarseWidth n ≤
        32 * rigidityPower n (5 / 16) := by
    rw [mul_div_assoc, rigiditySmoothScale_div_badArcCoarseWidth hn]
    exact mul_le_mul_of_nonneg_right
      (by nlinarith [Real.pi_le_four]) (rigidityPower_nonneg n _)
  have hpow : 1 ≤ rigidityPower n (5 / 16) := by
    unfold rigidityPower
    exact Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega))
      (by norm_num)
  unfold interiorArcGridCount
  push_cast
  calc
    (Nat.floor ((8 * Real.pi * rigiditySmoothScale n) /
          badArcCoarseWidth n) : ℝ) + 1 ≤
        (8 * Real.pi * rigiditySmoothScale n) / badArcCoarseWidth n + 1 := by
      simpa [add_comm] using add_le_add_right hfloor 1
    _ ≤ 32 * rigidityPower n (5 / 16) + 1 :=
      by simpa [add_comm] using add_le_add_right hratio 1
    _ ≤ 33 * rigidityPower n (5 / 16) := by linarith

lemma interiorArcCover_card_cast_le
    {n : ℕ} (hn : 0 < n) :
    ((interiorArcCover n).card : ℝ) ≤
      2145 * rigidityPower n (7 / 16) := by
  let P := interiorArcDenominatorCount n
  let Z : Finset ℤ := Finset.Icc (-((P : ℕ) : ℤ) - 1) ((P : ℕ) + 1)
  let B := interiorArcGridCount n
  have hcardNat : (interiorArcCover n).card ≤ P * (Z.card * B) := by
    unfold interiorArcCover
    calc
      ((Finset.Icc 1 P).biUnion fun p ↦
          Z.biUnion fun z ↦
            (Finset.range B).image (interiorArcPoint n p z)).card ≤
          ∑ p ∈ Finset.Icc 1 P,
            (Z.biUnion fun z ↦
              (Finset.range B).image (interiorArcPoint n p z)).card :=
        Finset.card_biUnion_le (M := ℝ)
      _ ≤ ∑ _p ∈ Finset.Icc 1 P, Z.card * B := by
        apply Finset.sum_le_sum
        intro p _hp
        calc
          (Z.biUnion fun z ↦
              (Finset.range B).image (interiorArcPoint n p z)).card ≤
              ∑ z ∈ Z,
                ((Finset.range B).image (interiorArcPoint n p z)).card :=
            Finset.card_biUnion_le (M := ℝ)
          _ ≤ ∑ _z ∈ Z, B := by
            apply Finset.sum_le_sum
            intro z _hz
            simpa using (Finset.card_image_le
              (s := Finset.range B) (f := interiorArcPoint n p z))
          _ = Z.card * B := by simp
      _ = (Finset.Icc 1 P).card * (Z.card * B) := by simp
      _ ≤ P * (Z.card * B) := by
        gcongr
        simp
  have hcardR : ((interiorArcCover n).card : ℝ) ≤
      (P : ℝ) * ((Z.card : ℝ) * (B : ℝ)) := by
    exact_mod_cast hcardNat
  have hP := interiorArcDenominatorCount_cast_le hn
  have hZ := interiorArcIntegerCount_cast_le hn
  have hB := interiorArcGridCount_cast_le hn
  have hp0 : 0 ≤ (P : ℝ) := by positivity
  have hz0 : 0 ≤ (Z.card : ℝ) := by positivity
  have hb0 : 0 ≤ (B : ℝ) := by positivity
  have hpowOne0 : 0 ≤ rigidityPower n (1 / 16) :=
    rigidityPower_nonneg n _
  have hpowFive0 : 0 ≤ rigidityPower n (5 / 16) :=
    rigidityPower_nonneg n _
  calc
    ((interiorArcCover n).card : ℝ) ≤
        (P : ℝ) * ((Z.card : ℝ) * (B : ℝ)) := hcardR
    _ ≤ (5 * rigidityPower n (1 / 16)) *
        ((13 * rigidityPower n (1 / 16)) *
          (33 * rigidityPower n (5 / 16))) := by
      exact mul_le_mul hP
        (mul_le_mul hZ hB hb0
          (mul_nonneg (by norm_num) hpowOne0))
        (mul_nonneg hz0 hb0)
        (mul_nonneg (by norm_num) hpowOne0)
    _ = 2145 * rigidityPower n (7 / 16) := by
      have hpowers : rigidityPower n (1 / 16) *
          rigidityPower n (1 / 16) * rigidityPower n (5 / 16) =
            rigidityPower n (7 / 16) := by
        rw [← rigidityPower_add hn, ← rigidityPower_add hn]
        congr 2 <;> norm_num
      rw [← hpowers]
      ring

lemma eventually_global_velocity_le_two_growing :
    ∀ᶠ n : ℕ in atTop, ∀ e : SignVector (2 * n),
      ¬HasHighMeshAcceleration n e →
      ¬HasHighMeshVelocity n (growingVelocityCutoff n) e →
      ∀ t ∈ Set.Ico (-(Real.pi * n)) (Real.pi * n),
        ‖rescaledCenteredVelocity n e t‖ ≤ 2 * growingVelocityCutoff n := by
  have herr : ∀ᶠ n : ℕ in atTop,
      2 * globalAccelerationBound n * localMeshHalfWidth n < 1 := by
    have h := (globalAccelerationBound_mul_halfWidth_tendsto_zero.const_mul 2)
    have h' : Tendsto (fun n : ℕ ↦
        2 * globalAccelerationBound n * localMeshHalfWidth n)
        atTop (𝓝 0) := by
      convert h using 1 <;> ring
    exact h'.eventually (Iio_mem_nhds (by norm_num))
  have hcut : ∀ᶠ n : ℕ in atTop, 1 < growingVelocityCutoff n :=
    growingVelocityCutoff_tendsto_atTop.eventually (eventually_gt_atTop 1)
  filter_upwards [Nat.eventually_pos, herr, hcut] with n hn herrN hcutN
  intro e hacc hvel t ht
  rcases exists_localMeshPoint_within_step n hn t ht with
    ⟨a, hdiff0, hdiff⟩
  have ha : ‖rescaledCenteredVelocity n e (localMeshPoint n a)‖ <
      growingVelocityCutoff n := by
    exact lt_of_not_ge fun hge ↦ hvel ⟨a, hge⟩
  have hx : localMeshPoint n a ∈
      Set.Icc (-(Real.pi * n)) (Real.pi * n) := by
    have hx' := localMeshPoint_mem_Ico n hn a
    exact ⟨hx'.1, hx'.2.le⟩
  have ht' : t ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n) :=
    ⟨ht.1, ht.2.le⟩
  have hsub := norm_rescaledCenteredVelocity_sub_le_of_not_high
    n hn e hacc (localMeshPoint n a) t hx ht'
  have hsub' : ‖rescaledCenteredVelocity n e t -
        rescaledCenteredVelocity n e (localMeshPoint n a)‖ < 1 := by
    calc
      _ ≤ globalAccelerationBound n * |t - localMeshPoint n a| := hsub
      _ < globalAccelerationBound n * (2 * localMeshHalfWidth n) := by
        have hC : 0 ≤ globalAccelerationBound n := by
          unfold globalAccelerationBound accelerationCutoff
          exact add_nonneg (rigidityPower_nonneg n _)
            (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
              (by unfold localMeshHalfWidth; positivity))
        rw [abs_of_nonneg hdiff0]
        exact mul_lt_mul_of_pos_left hdiff (hC.lt_of_ne' (by
          intro hzero
          have := rigidityPower_pos hn (1 / 8)
          unfold globalAccelerationBound accelerationCutoff at hzero
          nlinarith [Real.sqrt_nonneg (2 * n + 1 : ℝ),
            show 0 ≤ localMeshHalfWidth n by unfold localMeshHalfWidth; positivity]))
      _ = 2 * globalAccelerationBound n * localMeshHalfWidth n := by ring
      _ < 1 := herrN
  have htri : ‖rescaledCenteredVelocity n e t‖ ≤
      ‖rescaledCenteredVelocity n e (localMeshPoint n a)‖ +
        ‖rescaledCenteredVelocity n e t -
          rescaledCenteredVelocity n e (localMeshPoint n a)‖ := by
    have hid : rescaledCenteredVelocity n e t =
        rescaledCenteredVelocity n e (localMeshPoint n a) +
          (rescaledCenteredVelocity n e t -
            rescaledCenteredVelocity n e (localMeshPoint n a)) := by abel
    calc
      ‖rescaledCenteredVelocity n e t‖ =
          ‖rescaledCenteredVelocity n e (localMeshPoint n a) +
            (rescaledCenteredVelocity n e t -
              rescaledCenteredVelocity n e (localMeshPoint n a))‖ :=
        congrArg norm hid
      _ ≤ _ := norm_add_le _ _
  exact (calc
    ‖rescaledCenteredVelocity n e t‖ ≤ _ := htri
    _ < growingVelocityCutoff n + 1 := add_lt_add ha hsub'
    _ < 2 * growingVelocityCutoff n := by linarith).le

lemma norm_rescaledCenteredEval_sub_le_of_global_velocity
    (n : ℕ) (e : SignVector (2 * n)) (T x y : ℝ)
    (hxy : x ≤ y)
    (hvel : ∀ s ∈ Set.Icc x y,
      ‖rescaledCenteredVelocity n e s‖ ≤ T) :
    ‖rescaledCenteredEval n e y - rescaledCenteredEval n e x‖ ≤
      T * (y - x) := by
  exact norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s _hs ↦ (hasDerivAt_rescaledCenteredEval n e s).hasDerivWithinAt)
    (fun s hs ↦ hvel s ⟨hs.1, hs.2.le⟩)
    y (Set.right_mem_Icc.mpr hxy)

lemma small_value_transfers_to_left_cover_point
    {n : ℕ} (hn : 0 < n) (e : SignVector (2 * n))
    (hacc : ¬HasHighMeshAcceleration n e)
    (hmesh : ¬HasHighMeshVelocity n (growingVelocityCutoff n) e)
    (hglobal : ∀ s ∈ Set.Ico (-(Real.pi * n)) (Real.pi * n),
      ‖rescaledCenteredVelocity n e s‖ ≤ 2 * growingVelocityCutoff n)
    (u t q step : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi * n))
    (hq0 : 0 ≤ q) (hqt : q ≤ t) (htop : t < Real.pi * n)
    (hdist : t - q < step) (hstep : 0 ≤ step)
    (hsmall : ‖rescaledCenteredEval n e t‖ ≤ u / n) :
    ‖rescaledCenteredEval n e q‖ ≤
      u / n + 2 * growingVelocityCutoff n * step := by
  have hsegment : ∀ s ∈ Set.Icc q t,
      s ∈ Set.Ico (-(Real.pi * n)) (Real.pi * n) := by
    intro s hs
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hp : 0 < Real.pi * (n : ℝ) := mul_pos Real.pi_pos hnR
    exact ⟨(le_of_lt (neg_lt_zero.mpr hp)).trans (hq0.trans hs.1),
      hs.2.trans_lt htop⟩
  have hdiff := norm_rescaledCenteredEval_sub_le_of_global_velocity
    n e (2 * growingVelocityCutoff n) q t hqt
      (fun s hs ↦ hglobal s (hsegment s hs))
  have htri : ‖rescaledCenteredEval n e q‖ ≤
      ‖rescaledCenteredEval n e t‖ +
        ‖rescaledCenteredEval n e t - rescaledCenteredEval n e q‖ := by
    have hid : rescaledCenteredEval n e q = rescaledCenteredEval n e t -
        (rescaledCenteredEval n e t - rescaledCenteredEval n e q) := by abel
    calc
      ‖rescaledCenteredEval n e q‖ =
          ‖rescaledCenteredEval n e t -
            (rescaledCenteredEval n e t - rescaledCenteredEval n e q)‖ :=
        congrArg norm hid
      _ ≤ _ := norm_sub_le _ _
  have hT : 0 ≤ 2 * growingVelocityCutoff n := by
    exact mul_nonneg (by norm_num) (growingVelocityCutoff_nonneg n)
  calc
    ‖rescaledCenteredEval n e q‖ ≤ _ := htri
    _ ≤ u / n + (2 * growingVelocityCutoff n) * (t - q) :=
      add_le_add hsmall hdiff
    _ ≤ u / n + 2 * growingVelocityCutoff n * step := by
      simpa using add_le_add_left
        (mul_le_mul_of_nonneg_left hdist.le hT) (u / n)

lemma small_value_transfers_to_right_cover_point
    {n : ℕ} (hn : 0 < n) (e : SignVector (2 * n))
    (hacc : ¬HasHighMeshAcceleration n e)
    (hmesh : ¬HasHighMeshVelocity n (growingVelocityCutoff n) e)
    (hglobal : ∀ s ∈ Set.Ico (-(Real.pi * n)) (Real.pi * n),
      ‖rescaledCenteredVelocity n e s‖ ≤ 2 * growingVelocityCutoff n)
    (u t q step : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi * n))
    (htq : t ≤ q) (hqtop : q < Real.pi * n)
    (hdist : q - t < step) (hstep : 0 ≤ step)
    (hsmall : ‖rescaledCenteredEval n e t‖ ≤ u / n) :
    ‖rescaledCenteredEval n e q‖ ≤
      u / n + 2 * growingVelocityCutoff n * step := by
  have hsegment : ∀ s ∈ Set.Icc t q,
      s ∈ Set.Ico (-(Real.pi * n)) (Real.pi * n) := by
    intro s hs
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hp : 0 < Real.pi * (n : ℝ) := mul_pos Real.pi_pos hnR
    exact ⟨(le_of_lt (neg_lt_zero.mpr hp)).trans (ht.1.trans hs.1),
      hs.2.trans_lt hqtop⟩
  have hdiff := norm_rescaledCenteredEval_sub_le_of_global_velocity
    n e (2 * growingVelocityCutoff n) t q htq
      (fun s hs ↦ hglobal s (hsegment s hs))
  have htri : ‖rescaledCenteredEval n e q‖ ≤
      ‖rescaledCenteredEval n e t‖ +
        ‖rescaledCenteredEval n e q - rescaledCenteredEval n e t‖ := by
    have hid : rescaledCenteredEval n e q = rescaledCenteredEval n e t +
        (rescaledCenteredEval n e q - rescaledCenteredEval n e t) := by abel
    calc
      ‖rescaledCenteredEval n e q‖ =
          ‖rescaledCenteredEval n e t +
            (rescaledCenteredEval n e q - rescaledCenteredEval n e t)‖ :=
        congrArg norm hid
      _ ≤ _ := norm_add_le _ _
  have hT : 0 ≤ 2 * growingVelocityCutoff n := by
    exact mul_nonneg (by norm_num) (growingVelocityCutoff_nonneg n)
  calc
    ‖rescaledCenteredEval n e q‖ ≤ _ := htri
    _ ≤ u / n + (2 * growingVelocityCutoff n) * (q - t) :=
      add_le_add hsmall hdiff
    _ ≤ u / n + 2 * growingVelocityCutoff n * step := by
      simpa using add_le_add_left
        (mul_le_mul_of_nonneg_left hdist.le hT) (u / n)

end Erdos525
