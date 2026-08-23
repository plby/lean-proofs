import Mathlib

open scoped NumberField NNReal ENNReal BigOperators
open NumberField NumberField.mixedEmbedding

noncomputable section

namespace Erdos841.BoundedUnits

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
open scoped Classical


def placeHalf (x : NumberField.RingOfIntegers K) (w : InfinitePlace K) : ℝ≥0 :=
  ⟨w (x : K) / 2, by positivity⟩

noncomputable def boundedRadius (w₁ : InfinitePlace K)
    (x : NumberField.RingOfIntegers K) (C R : ℝ≥0) :
    InfinitePlace K → ℝ≥0 := fun w =>
  if w = w₁ then C * R else placeHalf x w

lemma prod_boundedRadius (w₁ : InfinitePlace K)
    (x : NumberField.RingOfIntegers K) (C R : ℝ≥0) :
    ∏ w, (boundedRadius w₁ x C R w) ^ InfinitePlace.mult w =
      C * R *
        (∏ w ∈ Finset.univ.erase w₁, placeHalf x w) := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ
    (fun w => (boundedRadius w₁ x C R w) ^ InfinitePlace.mult w)
    (Finset.mem_univ w₁)]
  simp only [boundedRadius, if_pos, NumberField.IsTotallyReal.mult_eq, pow_one]
  congr 1
  apply Finset.prod_congr rfl
  intro w hw
  rw [if_neg (Finset.ne_of_mem_erase hw)]

lemma prod_other_radius_lower
    (w₁ : InfinitePlace K)
    (x : NumberField.RingOfIntegers K) (hx : x ≠ 0)
    (R : ℝ≥0) (hR : (w₁ (x : K) : ℝ) ≤ R) :
    (1 : ℝ) ≤
      (R : ℝ) * (2 : ℝ) ^ (Finset.univ.erase w₁).card *
        (∏ w ∈ Finset.univ.erase w₁, (w (x : K) / 2)) := by
  classical
  have hxK : (x : K) ≠ 0 := NumberField.RingOfIntegers.coe_ne_zero_iff.mpr hx
  have hnormZ : Algebra.norm ℤ x ≠ 0 := by
    rw [Algebra.norm_ne_zero_iff]
    exact hx
  have hnormNat : 1 ≤ Int.natAbs (Algebra.norm ℤ x) :=
    Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hnormZ)
  have hnormQ : (1 : ℚ) ≤ |Algebra.norm ℚ (x : K)| := by
    have heqQ : ((Algebra.norm ℤ x : ℤ) : ℚ) =
        Algebra.norm ℚ (x : K) := Algebra.coe_norm_int x
    rw [← heqQ, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hnormZ
  have hnorm : (1 : ℝ) ≤ ((|Algebra.norm ℚ (x : K)| : ℚ) : ℝ) := by
    exact_mod_cast hnormQ
  have hprod : (1 : ℝ) ≤ ∏ w : InfinitePlace K, w (x : K) := by
    rw [← NumberField.InfinitePlace.prod_eq_abs_norm (x : K)] at hnorm
    simpa [NumberField.IsTotallyReal.mult_eq] using hnorm
  have hprodErase : (1 : ℝ) ≤
      (w₁ (x : K)) * ∏ w ∈ Finset.univ.erase w₁, w (x : K) := by
    rw [Finset.mul_prod_erase Finset.univ (fun w : InfinitePlace K => w (x : K))
      (Finset.mem_univ w₁)]
    exact hprod
  have hotherNonneg : 0 ≤ ∏ w ∈ Finset.univ.erase w₁, w (x : K) := by positivity
  have hRprod : (1 : ℝ) ≤
      (R : ℝ) * ∏ w ∈ Finset.univ.erase w₁, w (x : K) :=
    hprodErase.trans (mul_le_mul_of_nonneg_right hR hotherNonneg)
  calc
    (1 : ℝ) ≤ (R : ℝ) * ∏ w ∈ Finset.univ.erase w₁, w (x : K) := hRprod
    _ = (R : ℝ) * (2 : ℝ) ^ (Finset.univ.erase w₁).card *
        (∏ w ∈ Finset.univ.erase w₁, (w (x : K) / 2)) := by
      rw [Finset.prod_div_distrib, Finset.prod_const]
      have htwo : (2 : ℝ) ^ (Finset.univ.erase w₁).card ≠ 0 := by positivity
      field_simp

noncomputable def boundedStepFactor (w₁ : InfinitePlace K) (B : ℕ) : ℝ≥0 :=
  (B : ℝ≥0) * 2 ^ (Finset.univ.erase w₁).card

lemma one_le_boundedStepFactor (w₁ : InfinitePlace K) {B : ℕ} (hBnat : 1 ≤ B) :
    (1 : ℝ≥0) ≤ boundedStepFactor w₁ B := by
  dsimp [boundedStepFactor]
  exact one_le_mul (by exact_mod_cast hBnat) (one_le_pow₀ one_le_two)

theorem exists_bounded_next
    (w₁ : InfinitePlace K) {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B)
    (x : NumberField.RingOfIntegers K) (hx : x ≠ 0)
    (R : ℝ≥0) (hR : ∀ w : InfinitePlace K, w (x : K) ≤ R) :
    ∃ y : NumberField.RingOfIntegers K, y ≠ 0 ∧
      (∀ w, w ≠ w₁ → w (y : K) < w (x : K)) ∧
      Int.natAbs (Algebra.norm ℤ y) ≤ B ∧
      (∀ w : InfinitePlace K,
        w (y : K) < (boundedStepFactor w₁ B) * R) := by
  classical
  have hBnat : 1 ≤ B := by
    by_contra h
    have hB0 : B = 0 := by omega
    subst B
    simp at hB
  have hxK : (x : K) ≠ 0 :=
    NumberField.RingOfIntegers.coe_ne_zero_iff.mpr hx
  let f : InfinitePlace K → ℝ≥0 := fun w => placeHalf x w
  have hf : ∀ w, w ≠ w₁ → f w ≠ 0 := by
    intro w _hw
    intro hz
    have hzR : (f w : ℝ) = 0 := congrArg ((↑) : ℝ≥0 → ℝ) hz
    change w (x : K) / 2 = 0 at hzR
    have hwpos : 0 < w (x : K) := InfinitePlace.pos_iff.mpr hxK
    linarith
  obtain ⟨g, hgother, hgprod⟩ :=
    mixedEmbedding.adjust_f K (B : ℝ≥0) hf
  have hvolume : mixedEmbedding.minkowskiBound K 1 <
      MeasureTheory.volume (mixedEmbedding.convexBodyLT K g) := by
    rw [mixedEmbedding.convexBodyLT_volume, hgprod]
    exact hB
  obtain ⟨y, hy0, hy⟩ :=
    mixedEmbedding.exists_ne_zero_mem_ringOfIntegers_lt K hvolume
  have hynorm : Int.natAbs (Algebra.norm ℤ y) ≤ B := by
    rw [← Nat.cast_le (α := ℚ), Nat.cast_natAbs, Int.cast_abs,
      Algebra.coe_norm_int]
    rw [← Rat.cast_le (K := ℝ), Rat.cast_natCast]
    calc
      |Algebra.norm ℚ (y : K)| =
          ∏ w : InfinitePlace K, w (y : K) ^ InfinitePlace.mult w :=
        (NumberField.InfinitePlace.prod_eq_abs_norm (y : K)).symm
      _ ≤ ∏ w : InfinitePlace K, (g w : ℝ) ^ InfinitePlace.mult w := by
        gcongr with w
        exact (hy w).le
      _ = (B : ℝ) := by
        simpa using congrArg ((↑) : ℝ≥0 → ℝ) hgprod
  have hdecrease : ∀ w, w ≠ w₁ → w (y : K) < w (x : K) := by
    intro w hw
    calc
      w (y : K) < g w := hy w
      _ = w (x : K) / 2 := by
        rw [hgother w hw]
        rfl
      _ < w (x : K) := by
        exact div_lt_self (InfinitePlace.pos_iff.mpr
          (NumberField.RingOfIntegers.coe_ne_zero_iff.mpr hx)) (by norm_num)
  have hPpos : 0 <
      ∏ w ∈ Finset.univ.erase w₁, (f w : ℝ) := by
    apply Finset.prod_pos
    intro w _hw
    change 0 < w (x : K) / 2
    exact div_pos (InfinitePlace.pos_iff.mpr hxK) (by norm_num)
  have hgprodR : (g w₁ : ℝ) *
      (∏ w ∈ Finset.univ.erase w₁, (f w : ℝ)) = (B : ℝ) := by
    have hsplit := congrArg ((↑) : ℝ≥0 → ℝ) hgprod
    rw [← Finset.mul_prod_erase Finset.univ
      (fun w => g w ^ InfinitePlace.mult w) (Finset.mem_univ w₁)] at hsplit
    simp only [NumberField.IsTotallyReal.mult_eq, pow_one] at hsplit
    simp only [NNReal.coe_mul, NNReal.coe_prod, NNReal.coe_natCast] at hsplit
    have hprodEq :
        (∏ w ∈ Finset.univ.erase w₁, (g w : ℝ)) =
          ∏ w ∈ Finset.univ.erase w₁, (f w : ℝ) := by
      apply Finset.prod_congr rfl
      intro w hw
      exact congrArg ((↑) : ℝ≥0 → ℝ)
        (hgother w (Finset.ne_of_mem_erase hw))
    rw [hprodEq] at hsplit
    exact hsplit
  have hlow : (1 : ℝ) ≤
      (R : ℝ) * (2 : ℝ) ^ (Finset.univ.erase w₁).card *
        (∏ w ∈ Finset.univ.erase w₁, (f w : ℝ)) := by
    change (1 : ℝ) ≤
      (R : ℝ) * (2 : ℝ) ^ (Finset.univ.erase w₁).card *
        (∏ w ∈ Finset.univ.erase w₁, (w (x : K) / 2))
    exact prod_other_radius_lower w₁ x hx R (hR w₁)
  have hinvP :
      (∏ w ∈ Finset.univ.erase w₁, (f w : ℝ))⁻¹ ≤
        (R : ℝ) * (2 : ℝ) ^ (Finset.univ.erase w₁).card := by
    rw [inv_eq_one_div, div_le_iff₀ hPpos]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hlow
  have hgw₁ : (g w₁ : ℝ) ≤
      (boundedStepFactor w₁ B : ℝ) * R := by
    have hgeq : (g w₁ : ℝ) =
        (B : ℝ) * (∏ w ∈ Finset.univ.erase w₁, (f w : ℝ))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hPpos.ne']
      exact hgprodR
    rw [hgeq]
    dsimp [boundedStepFactor]
    push_cast
    have hBnonneg : (0 : ℝ) ≤ B := by positivity
    exact (mul_le_mul_of_nonneg_left hinvP hBnonneg).trans_eq (by ring)
  refine ⟨y, hy0, hdecrease, hynorm, ?_⟩
  intro w
  by_cases hw : w = w₁
  · subst w
    exact (hy w₁).trans_le hgw₁
  · calc
      w (y : K) < w (x : K) := hdecrease w hw
      _ ≤ R := hR w
      _ ≤ (boundedStepFactor w₁ B : ℝ) * R := by
        nth_rw 1 [← one_mul (R : ℝ)]
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast one_le_boundedStepFactor w₁ hBnat)
          (by positivity)

def placeVector (x : NumberField.RingOfIntegers K) : InfinitePlace K → ℝ :=
  fun w => w (x : K)

noncomputable def placeNorm (x : NumberField.RingOfIntegers K) : ℝ≥0 :=
  ‖placeVector x‖₊

lemma place_le_placeNorm (x : NumberField.RingOfIntegers K) (w : InfinitePlace K) :
    w (x : K) ≤ placeNorm x := by
  change (placeVector x w : ℝ) ≤ ‖placeVector x‖
  exact (le_abs_self _).trans (norm_le_pi_norm (placeVector x) w)

lemma placeNorm_one : placeNorm (1 : NumberField.RingOfIntegers K) = 1 := by
  apply NNReal.eq
  change ‖placeVector (1 : NumberField.RingOfIntegers K)‖ = 1
  have hv : placeVector (1 : NumberField.RingOfIntegers K) =
      (fun _w : InfinitePlace K => (1 : ℝ)) := by
    funext w
    simp [placeVector]
  rw [hv, pi_norm_const]
  norm_num

def BoundedNextPred
    (w₁ : InfinitePlace K) (B : ℕ)
    (x : {x : NumberField.RingOfIntegers K // x ≠ 0})
    (y : NumberField.RingOfIntegers K) : Prop :=
  y ≠ 0 ∧
    (∀ w : InfinitePlace K, w ≠ w₁ → w (y : K) < w (x.1 : K)) ∧
    Int.natAbs (Algebra.norm ℤ y) ≤ B ∧
    ∀ w : InfinitePlace K,
      w (y : K) < boundedStepFactor w₁ B * placeNorm x.1

noncomputable def boundedNextDataOf
    (w₁ : InfinitePlace K) {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B)
    (x : {x : NumberField.RingOfIntegers K // x ≠ 0}) :
    {y : NumberField.RingOfIntegers K // BoundedNextPred w₁ B x y} :=
  Classical.choice <| by
    obtain ⟨y, hy0, hydec, hynorm, hyplace⟩ :=
      exists_bounded_next w₁ hB x.1 x.prop (placeNorm x.1)
        (place_le_placeNorm x.1)
    exact ⟨⟨y, hy0, hydec, hynorm, hyplace⟩⟩

noncomputable def boundedNext
    (w₁ : InfinitePlace K) {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B)
    (x : {x : NumberField.RingOfIntegers K // x ≠ 0}) :
    NumberField.RingOfIntegers K :=
  (boundedNextDataOf w₁ hB x).1

lemma boundedNext_ne_zero
    (w₁ : InfinitePlace K) {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B)
    (x : {x : NumberField.RingOfIntegers K // x ≠ 0}) :
    boundedNext w₁ hB x ≠ 0 :=
  (boundedNextDataOf w₁ hB x).2.1

lemma boundedNext_decreasing
    (w₁ : InfinitePlace K) {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B)
    (x : {x : NumberField.RingOfIntegers K // x ≠ 0})
    (w : InfinitePlace K) (hw : w ≠ w₁) :
    w (boundedNext w₁ hB x : K) < w (x.1 : K) :=
  (boundedNextDataOf w₁ hB x).2.2.1 w hw

lemma boundedNext_norm_le
    (w₁ : InfinitePlace K) {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B)
    (x : {x : NumberField.RingOfIntegers K // x ≠ 0}) :
    Int.natAbs (Algebra.norm ℤ (boundedNext w₁ hB x)) ≤ B :=
  (boundedNextDataOf w₁ hB x).2.2.2.1

lemma boundedNext_placeNorm_le
    (w₁ : InfinitePlace K) {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B)
    (x : {x : NumberField.RingOfIntegers K // x ≠ 0}) :
    placeNorm (boundedNext w₁ hB x) ≤
      boundedStepFactor w₁ B * placeNorm x.1 := by
  let y := boundedNext w₁ hB x
  have hy := (boundedNextDataOf w₁ hB x).2.2.2.2
  change ‖placeVector y‖₊ ≤ boundedStepFactor w₁ B * placeNorm x.1
  rw [Pi.nnnorm_def]
  apply Finset.sup_le
  intro w _hw
  change ‖w (y : K)‖₊ ≤ boundedStepFactor w₁ B * placeNorm x.1
  rw [Real.nnnorm_of_nonneg (apply_nonneg w (y : K))]
  exact_mod_cast (hy w).le

noncomputable def boundedSeq
    (w₁ : InfinitePlace K) {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B) :
    ℕ → {x : NumberField.RingOfIntegers K // x ≠ 0}
  | 0 => ⟨1, by simp⟩
  | n + 1 =>
      ⟨boundedNext w₁ hB (boundedSeq w₁ hB n),
        boundedNext_ne_zero w₁ hB (boundedSeq w₁ hB n)⟩

lemma boundedSeq_succ
    (w₁ : InfinitePlace K) {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B) (n : ℕ) :
    (boundedSeq w₁ hB (n + 1) : NumberField.RingOfIntegers K) =
      boundedNext w₁ hB (boundedSeq w₁ hB n) := rfl

lemma boundedSeq_placeNorm_le
    (w₁ : InfinitePlace K) {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B) (n : ℕ) :
    placeNorm (boundedSeq w₁ hB n).1 ≤ (boundedStepFactor w₁ B) ^ n := by
  induction n with
  | zero => simp [boundedSeq, placeNorm_one]
  | succ n ih =>
      rw [boundedSeq_succ]
      calc
        placeNorm (boundedNext w₁ hB (boundedSeq w₁ hB n)) ≤
            boundedStepFactor w₁ B * placeNorm (boundedSeq w₁ hB n).1 :=
          boundedNext_placeNorm_le w₁ hB (boundedSeq w₁ hB n)
        _ ≤ boundedStepFactor w₁ B * (boundedStepFactor w₁ B) ^ n := by
          exact mul_le_mul_of_nonneg_left ih (by positivity)
        _ = (boundedStepFactor w₁ B) ^ (n + 1) := by
          rw [pow_succ']

lemma boundedSeq_place_le
    (w₁ : InfinitePlace K) {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B) (n : ℕ)
    (w : InfinitePlace K) :
    w ((boundedSeq w₁ hB n).1 : K) ≤ (boundedStepFactor w₁ B : ℝ) ^ n := by
  exact (place_le_placeNorm (boundedSeq w₁ hB n).1 w).trans
    (by exact_mod_cast boundedSeq_placeNorm_le w₁ hB n)

lemma boundedSeq_norm_le
    (w₁ : InfinitePlace K) {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B) (n : ℕ) :
    Int.natAbs (Algebra.norm ℤ (boundedSeq w₁ hB n :
      NumberField.RingOfIntegers K)) ≤ B := by
  cases n with
  | zero =>
      have hBnat : 1 ≤ B := by
        by_contra h
        have : B = 0 := by omega
        subst B
        simp at hB
      simpa [boundedSeq] using hBnat
  | succ n =>
      exact boundedNext_norm_le w₁ hB (boundedSeq w₁ hB n)

lemma boundedSeq_decreasing
    (w₁ : InfinitePlace K) {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B)
    {n m : ℕ} (hnm : n < m) (w : InfinitePlace K) (hw : w ≠ w₁) :
    w ((boundedSeq w₁ hB m).1 : K) < w ((boundedSeq w₁ hB n).1 : K) := by
  induction m with
  | zero => omega
  | succ m ih =>
      rcases eq_or_lt_of_le (Nat.le_of_lt_succ hnm) with rfl | hnm'
      · exact boundedNext_decreasing w₁ hB (boundedSeq w₁ hB n) w hw
      · exact (boundedNext_decreasing w₁ hB (boundedSeq w₁ hB m) w hw).trans
          (ih hnm')

theorem exists_boundedSeq_collision
    (w₁ : InfinitePlace K) {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B) :
    ∃ n m : ℕ,
      n < m ∧
      m ≤ (Ideal.finite_setOfPred_absNorm_le
        (S := NumberField.RingOfIntegers K) B).toFinset.card ∧
      Ideal.span ({(boundedSeq w₁ hB n).1} : Set
          (NumberField.RingOfIntegers K)) =
        Ideal.span ({(boundedSeq w₁ hB m).1} : Set
          (NumberField.RingOfIntegers K)) := by
  classical
  let t : Finset (Ideal (NumberField.RingOfIntegers K)) :=
    (Ideal.finite_setOfPred_absNorm_le
      (S := NumberField.RingOfIntegers K) B).toFinset
  let s : Finset ℕ := Finset.range (t.card + 1)
  let f : ℕ → Ideal (NumberField.RingOfIntegers K) := fun n =>
    Ideal.span ({(boundedSeq w₁ hB n).1} : Set
      (NumberField.RingOfIntegers K))
  have hmaps : Set.MapsTo f s t := by
    intro n hn
    rw [Finset.mem_coe]
    change f n ∈ (Ideal.finite_setOfPred_absNorm_le
      (S := NumberField.RingOfIntegers K) B).toFinset
    rw [Set.Finite.mem_toFinset]
    change Ideal.absNorm (f n) ≤ B
    dsimp [f]
    rw [Ideal.absNorm_span_singleton]
    exact boundedSeq_norm_le w₁ hB n
  have hcard : t.card < s.card := by simp [s]
  obtain ⟨n, hn, m, hm, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  have hnle : n ≤ t.card := by simpa [s] using hn
  have hmle : m ≤ t.card := by simpa [s] using hm
  rcases lt_or_gt_of_ne hne with hnm | hmn
  · exact ⟨n, m, hnm, by simpa [t] using hmle, heq⟩
  · exact ⟨m, n, hmn, by simpa [t] using hnle, heq.symm⟩

lemma boundedSeq_place_inv_le
    (w₁ : InfinitePlace K) {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B)
    (n : ℕ) (w₀ : InfinitePlace K) :
    (w₀ ((boundedSeq w₁ hB n).1 : K))⁻¹ ≤
      (boundedStepFactor w₁ B : ℝ) ^
        (n * (Finset.univ.erase w₀).card) := by
  classical
  let x : NumberField.RingOfIntegers K := (boundedSeq w₁ hB n).1
  have hx : x ≠ 0 := (boundedSeq w₁ hB n).2
  have hxK : (x : K) ≠ 0 :=
    NumberField.RingOfIntegers.coe_ne_zero_iff.mpr hx
  have hnormQ : (1 : ℝ) ≤ ((|Algebra.norm ℚ (x : K)| : ℚ) : ℝ) := by
    have hnormZ : Algebra.norm ℤ x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
    have heqQ : ((Algebra.norm ℤ x : ℤ) : ℚ) =
        Algebra.norm ℚ (x : K) := Algebra.coe_norm_int x
    have hq : (1 : ℚ) ≤ |Algebra.norm ℚ (x : K)| := by
      rw [← heqQ, ← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hnormZ
    exact_mod_cast hq
  have hprod : (1 : ℝ) ≤ ∏ w : InfinitePlace K, w (x : K) := by
    rw [← NumberField.InfinitePlace.prod_eq_abs_norm (x : K)] at hnormQ
    simpa [NumberField.IsTotallyReal.mult_eq] using hnormQ
  have hsplit : (1 : ℝ) ≤
      w₀ (x : K) * ∏ w ∈ Finset.univ.erase w₀, w (x : K) := by
    rw [Finset.mul_prod_erase Finset.univ
      (fun w : InfinitePlace K => w (x : K)) (Finset.mem_univ w₀)]
    exact hprod
  have hother :
      ∏ w ∈ Finset.univ.erase w₀, w (x : K) ≤
        (boundedStepFactor w₁ B : ℝ) ^
          (n * (Finset.univ.erase w₀).card) := by
    calc
      ∏ w ∈ Finset.univ.erase w₀, w (x : K) ≤
          ∏ _w ∈ Finset.univ.erase w₀,
            (boundedStepFactor w₁ B : ℝ) ^ n := by
        gcongr with w hw
        exact boundedSeq_place_le w₁ hB n w
      _ = ((boundedStepFactor w₁ B : ℝ) ^ n) ^
          (Finset.univ.erase w₀).card := by simp
      _ = (boundedStepFactor w₁ B : ℝ) ^
          (n * (Finset.univ.erase w₀).card) := by rw [pow_mul]
  have hnonneg : 0 ≤ w₀ (x : K) := apply_nonneg w₀ (x : K)
  have hone : (1 : ℝ) ≤ w₀ (x : K) *
      (boundedStepFactor w₁ B : ℝ) ^
        (n * (Finset.univ.erase w₀).card) :=
    hsplit.trans (mul_le_mul_of_nonneg_left hother hnonneg)
  rw [inv_eq_one_div]
  exact (div_le_iff₀ (InfinitePlace.pos_iff.mpr hxK)).mpr
    (by simpa [mul_comm] using hone)

noncomputable def boundedIdealCount (B : ℕ) : ℕ :=
  (Ideal.finite_setOfPred_absNorm_le
    (S := NumberField.RingOfIntegers K) B).toFinset.card

lemma boundedStepFactor_one_le
    (w₁ : InfinitePlace K) {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B) :
    (1 : ℝ) ≤ boundedStepFactor w₁ B := by
  have hBnat : 1 ≤ B := by
    by_contra h
    have hB0 : B = 0 := by omega
    subst B
    simp at hB
  exact_mod_cast one_le_boundedStepFactor w₁ hBnat

lemma infinitePlace_erase_card_add_one (w : InfinitePlace K) :
    (Finset.univ.erase w).card + 1 = Fintype.card (InfinitePlace K) := by
  classical
  rw [Finset.card_erase_of_mem (Finset.mem_univ w)]
  simp only [Finset.card_univ]
  have hc : 1 ≤ Fintype.card (InfinitePlace K) :=
    Fintype.card_pos_iff.mpr inferInstance
  omega

theorem exists_bounded_unit_place
    (w₁ : InfinitePlace K) {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B) :
    ∃ u : (NumberField.RingOfIntegers K)ˣ,
      (∀ w : InfinitePlace K, w ≠ w₁ → Real.log (w u) < 0) ∧
      ∀ w : InfinitePlace K,
        w u ≤ (boundedStepFactor w₁ B : ℝ) ^
            (boundedIdealCount (K := K) B * Fintype.card (InfinitePlace K)) ∧
        w (u⁻¹) ≤ (boundedStepFactor w₁ B : ℝ) ^
            (boundedIdealCount (K := K) B * Fintype.card (InfinitePlace K)) := by
  classical
  obtain ⟨n, m, hnm, hm, hspan⟩ := exists_boundedSeq_collision w₁ hB
  let N : ℕ := boundedIdealCount (K := K) B
  have hmN : m ≤ N := by simpa [N, boundedIdealCount] using hm
  have hnN : n ≤ N := (Nat.le_of_lt hnm).trans hmN
  have hu := Ideal.span_singleton_eq_span_singleton.mp hspan
  have hratio_eq : ∀ w : InfinitePlace K,
      w hu.choose = w ((boundedSeq w₁ hB m).1 : K) *
        (w ((boundedSeq w₁ hB n).1 : K))⁻¹ := by
    intro w
    calc
      w hu.choose = w ((algebraMap (NumberField.RingOfIntegers K) K
          (boundedSeq w₁ hB m).1) *
          (algebraMap (NumberField.RingOfIntegers K) K
            (boundedSeq w₁ hB n).1)⁻¹) := by
        rw [← congr_arg (algebraMap (NumberField.RingOfIntegers K) K) hu.choose_spec,
          mul_comm, map_mul (algebraMap (NumberField.RingOfIntegers K) K), ← mul_assoc,
          inv_mul_cancel₀ (NumberField.RingOfIntegers.coe_ne_zero_iff.mpr
            (boundedSeq w₁ hB n).2), one_mul]
      _ = w ((boundedSeq w₁ hB m).1 : K) *
          (w ((boundedSeq w₁ hB n).1 : K))⁻¹ := by
        rw [map_mul, map_inv₀]
  have hratioInv : ∀ w : InfinitePlace K,
      w (hu.choose⁻¹) = w ((boundedSeq w₁ hB n).1 : K) *
        (w ((boundedSeq w₁ hB m).1 : K))⁻¹ := by
    intro w
    calc
      w (hu.choose⁻¹) = (w hu.choose)⁻¹ := map_inv₀ w _
      _ = w ((boundedSeq w₁ hB n).1 : K) *
          (w ((boundedSeq w₁ hB m).1 : K))⁻¹ := by
        rw [hratio_eq w, mul_inv_rev, inv_inv]
  have hExp : ∀ (a b : ℕ), a ≤ N → b ≤ N →
      ∀ w : InfinitePlace K,
      a + b * (Finset.univ.erase w).card ≤
        N * Fintype.card (InfinitePlace K) := by
    intro a b ha hb w
    have hsum : a + b * (Finset.univ.erase w).card ≤
        N + N * (Finset.univ.erase w).card :=
      Nat.add_le_add ha (Nat.mul_le_mul_right _ hb)
    calc
      a + b * (Finset.univ.erase w).card ≤
          N + N * (Finset.univ.erase w).card := hsum
      _ = N * ((Finset.univ.erase w).card + 1) := by
        simp only [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ = N * Fintype.card (InfinitePlace K) := by
        rw [infinitePlace_erase_card_add_one]
  have hplace : ∀ w : InfinitePlace K,
      w hu.choose ≤ (boundedStepFactor w₁ B : ℝ) ^
          (N * Fintype.card (InfinitePlace K)) := by
    intro w
    rw [hratio_eq w]
    calc
      w ((boundedSeq w₁ hB m).1 : K) *
          (w ((boundedSeq w₁ hB n).1 : K))⁻¹ ≤
          (boundedStepFactor w₁ B : ℝ) ^ m *
            (boundedStepFactor w₁ B : ℝ) ^
              (n * (Finset.univ.erase w).card) := by
        gcongr
        · exact boundedSeq_place_le w₁ hB m w
        · exact boundedSeq_place_inv_le w₁ hB n w
      _ = (boundedStepFactor w₁ B : ℝ) ^
          (m + n * (Finset.univ.erase w).card) := by rw [← pow_add]
      _ ≤ (boundedStepFactor w₁ B : ℝ) ^
          (N * Fintype.card (InfinitePlace K)) := by
        exact pow_le_pow_right₀ (boundedStepFactor_one_le w₁ hB)
          (hExp m n hmN hnN w)
  have hplaceInv : ∀ w : InfinitePlace K,
      w (hu.choose⁻¹) ≤ (boundedStepFactor w₁ B : ℝ) ^
          (N * Fintype.card (InfinitePlace K)) := by
    intro w
    rw [hratioInv w]
    calc
      w ((boundedSeq w₁ hB n).1 : K) *
          (w ((boundedSeq w₁ hB m).1 : K))⁻¹ ≤
          (boundedStepFactor w₁ B : ℝ) ^ n *
            (boundedStepFactor w₁ B : ℝ) ^
              (m * (Finset.univ.erase w).card) := by
        gcongr
        · exact boundedSeq_place_le w₁ hB n w
        · exact boundedSeq_place_inv_le w₁ hB m w
      _ = (boundedStepFactor w₁ B : ℝ) ^
          (n + m * (Finset.univ.erase w).card) := by rw [← pow_add]
      _ ≤ (boundedStepFactor w₁ B : ℝ) ^
          (N * Fintype.card (InfinitePlace K)) := by
        exact pow_le_pow_right₀ (boundedStepFactor_one_le w₁ hB)
          (hExp n m hnN hmN w)
  refine ⟨hu.choose, ?_, ?_⟩
  · intro w hw
    refine Real.log_neg (NumberField.Units.pos_at_place hu.choose w) ?_
    rw [hratio_eq w, mul_inv_lt_iff₀'
      (InfinitePlace.pos_iff.mpr
        (NumberField.RingOfIntegers.coe_ne_zero_iff.mpr
          (boundedSeq w₁ hB n).2)), mul_one]
    exact boundedSeq_decreasing w₁ hB hnm w hw
  · intro w
    change w hu.choose ≤ (boundedStepFactor w₁ B : ℝ) ^
        (N * Fintype.card (InfinitePlace K)) ∧
      w (hu.choose⁻¹) ≤ (boundedStepFactor w₁ B : ℝ) ^
        (N * Fintype.card (InfinitePlace K))
    exact ⟨hplace w, hplaceInv w⟩

noncomputable def boundedUnitLogBound
    (w₁ : InfinitePlace K) (B : ℕ) : ℝ :=
  (boundedIdealCount (K := K) B * Fintype.card (InfinitePlace K) : ℕ) *
    Real.log (boundedStepFactor w₁ B : ℝ)

theorem exists_bounded_unit_log
    (w₁ : InfinitePlace K) {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B) :
    ∃ u : (NumberField.RingOfIntegers K)ˣ,
      (∀ w : InfinitePlace K, w ≠ w₁ → Real.log (w u) < 0) ∧
      ∀ w : InfinitePlace K,
        |Real.log (w u)| ≤ boundedUnitLogBound w₁ B := by
  obtain ⟨u, hdec, hplace⟩ := exists_bounded_unit_place w₁ hB
  refine ⟨u, hdec, ?_⟩
  intro w
  have hxpos : 0 < w u := NumberField.Units.pos_at_place u w
  have hupper := Real.log_le_log hxpos (hplace w).1
  have hinv : (w u)⁻¹ ≤ (boundedStepFactor w₁ B : ℝ) ^
      (boundedIdealCount (K := K) B * Fintype.card (InfinitePlace K)) := by
    rw [← map_inv₀]
    exact (hplace w).2
  have hlower := Real.log_le_log (inv_pos.mpr hxpos) hinv
  rw [Real.log_pow] at hupper hlower
  rw [Real.log_inv] at hlower
  exact abs_le.mpr ⟨by
      simpa [boundedUnitLogBound] using (neg_le_neg hlower),
    by simpa [boundedUnitLogBound] using hupper⟩

open Module Matrix NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped Classical

noncomputable def boundedPlaceUnit
    (w : {w : InfinitePlace K // w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
    {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B) :
    (NumberField.RingOfIntegers K)ˣ :=
  (exists_bounded_unit_log w.1 hB).choose

lemma boundedPlaceUnit_log_neg
    (w : {w : InfinitePlace K // w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
    {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B)
    (z : InfinitePlace K) (hz : z ≠ w.1) :
    Real.log (z (boundedPlaceUnit w hB)) < 0 :=
  (exists_bounded_unit_log w.1 hB).choose_spec.1 z hz

lemma boundedPlaceUnit_log_abs_le
    (w : {w : InfinitePlace K // w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
    {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B)
    (z : InfinitePlace K) :
    |Real.log (z (boundedPlaceUnit w hB))| ≤ boundedUnitLogBound w.1 B :=
  (exists_bounded_unit_log w.1 hB).choose_spec.2 z

noncomputable def boundedFundSystem {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B) :
    Fin (NumberField.Units.rank K) → (NumberField.RingOfIntegers K)ˣ :=
  fun i ↦ boundedPlaceUnit (NumberField.Units.equivFinRank K i) hB

set_option backward.isDefEq.respectTransparency.types false in
theorem boundedFundSystem_isMaxRank {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B) :
    NumberField.Units.IsMaxRank (boundedFundSystem hB) := by
  classical
  let e := NumberField.Units.equivFinRank K
  let B₀ := Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀}
  let v := fun w : {w : InfinitePlace K // w ≠ w₀} ↦
    NumberField.Units.logEmbedding K (Additive.ofMul (boundedPlaceUnit w hB))
  have hdet : B₀.det v ≠ 0 := by
    rw [Basis.det_apply]
    refine det_ne_zero_of_sum_col_lt_diag (fun w ↦ ?_)
    simp_rw [Real.norm_eq_abs, B₀, Basis.coePiBasisFun.toMatrix_eq_transpose,
      Matrix.transpose_apply]
    rw [← sub_pos, Finset.sum_congr rfl (fun x hx ↦ abs_of_neg ?_),
      Finset.sum_neg_distrib, sub_neg_eq_add,
      Finset.sum_erase_eq_sub (Finset.mem_univ _), ← add_comm_sub]
    · refine add_pos_of_nonneg_of_pos ?_ ?_
      · rw [sub_nonneg]
        exact le_abs_self _
      · rw [sum_logEmbedding_component (boundedPlaceUnit w hB)]
        refine mul_pos_of_neg_of_neg ?_
          (boundedPlaceUnit_log_neg w hB w₀ w.prop.symm)
        rw [InfinitePlace.mult]
        split_ifs <;> norm_num
    · refine mul_neg_of_pos_of_neg ?_ (boundedPlaceUnit_log_neg w hB x ?_)
      · rw [InfinitePlace.mult]
        split_ifs <;> norm_num
      · exact Subtype.ext_iff.not.mp (Finset.ne_of_mem_erase hx)
  have hli : LinearIndependent ℝ v :=
    ((Basis.is_basis_iff_det B₀).mpr
      ((isUnit_iff_ne_zero).mpr hdet)).1
  have hli' : LinearIndependent ℝ (v ∘ e) :=
    (linearIndependent_equiv e).mpr hli
  simpa [NumberField.Units.IsMaxRank, boundedFundSystem, v, e,
    Function.comp_def] using hli'

lemma erase_infinitePlace_card_eq_rank (w : InfinitePlace K) :
    (Finset.univ.erase w).card = NumberField.Units.rank K := by
  classical
  rw [Finset.card_erase_of_mem (Finset.mem_univ w), NumberField.Units.rank,
    Finset.card_univ]

noncomputable def commonBoundedStepFactor (B : ℕ) : ℝ≥0 :=
  (B : ℝ≥0) * 2 ^ NumberField.Units.rank K

lemma boundedStepFactor_eq_common (w : InfinitePlace K) (B : ℕ) :
    boundedStepFactor w B = commonBoundedStepFactor (K := K) B := by
  unfold boundedStepFactor commonBoundedStepFactor
  rw [erase_infinitePlace_card_eq_rank]

noncomputable def commonBoundedUnitLogBound (B : ℕ) : ℝ :=
  (boundedIdealCount (K := K) B * Fintype.card (InfinitePlace K) : ℕ) *
    Real.log (commonBoundedStepFactor (K := K) B : ℝ)

lemma boundedUnitLogBound_eq_common (w : InfinitePlace K) (B : ℕ) :
    boundedUnitLogBound w B = commonBoundedUnitLogBound (K := K) B := by
  simp only [boundedUnitLogBound, commonBoundedUnitLogBound,
    boundedStepFactor_eq_common]

lemma boundedFundSystem_log_abs_le {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B)
    (i : Fin (NumberField.Units.rank K)) (w : InfinitePlace K) :
    |Real.log (w (boundedFundSystem hB i))| ≤
      commonBoundedUnitLogBound (K := K) B := by
  simpa only [boundedFundSystem, boundedUnitLogBound_eq_common] using
    boundedPlaceUnit_log_abs_le (NumberField.Units.equivFinRank K i) hB w

/-- A quantitative Cramer-rule estimate for coordinates in a real basis.
The background basis is the coordinate basis of the finite product. -/
lemma basisCoordinate_mul_det_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → (ι → ℝ)) (hv : LinearIndependent ℝ v)
    (hsp : ⊤ ≤ Submodule.span ℝ (Set.range v))
    (C : ℝ) (hC : ∀ i j, |v i j| ≤ C)
    (x : ι → ℝ) (i : ι) :
    |(Basis.mk hv hsp).repr x i| * |(Pi.basisFun ℝ ι).det v| ≤
      (Fintype.card ι).factorial * (max C ‖x‖) ^ Fintype.card ι := by
  have hcr := Module.Basis.det_smul_mk_coord_eq_det_update
    (Pi.basisFun ℝ ι) hv hsp i
  have heq := LinearMap.congr_fun hcr x
  simp only [LinearMap.smul_apply, smul_eq_mul] at heq
  change (Pi.basisFun ℝ ι).det v * (Basis.mk hv hsp).repr x i =
    (Pi.basisFun ℝ ι).det (Function.update v i x) at heq
  have hdet : |(Pi.basisFun ℝ ι).det (Function.update v i x)| ≤
      (Fintype.card ι).factorial * (max C ‖x‖) ^ Fintype.card ι := by
    rw [Pi.basisFun_det_apply]
    have hd := Matrix.det_le (A := Matrix.of (Function.update v i x))
      (abv := AbsoluteValue.abs) (x := max C ‖x‖) (fun a b ↦ ?_)
    · simpa [nsmul_eq_mul] using hd
    · simp only [Matrix.of_apply, AbsoluteValue.abs_apply]
      by_cases hai : a = i
      · subst a
        rw [Function.update_self]
        simpa [Real.norm_eq_abs] using
          ((norm_le_pi_norm x b).trans (le_max_right _ _))
      · rw [Function.update_of_ne hai]
        exact (hC a b).trans (le_max_left _ _)
  rw [← abs_mul, mul_comm, heq]
  exact hdet

/-- The coordinates in the explicitly bounded fundamental system satisfy
a determinant-normalized estimate with no hidden field-dependent constant. -/
theorem boundedFundSystem_coordinate_mul_regulator_le {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B)
    (x : NumberField.Units.dirichletUnitTheorem.logSpace K)
    (i : Fin (NumberField.Units.rank K)) :
    |(NumberField.Units.basisOfIsMaxRank (boundedFundSystem_isMaxRank hB)).repr x i| *
        NumberField.Units.regOfFamily (boundedFundSystem hB) ≤
      (NumberField.Units.rank K).factorial *
        (max (commonBoundedUnitLogBound (K := K) B) ‖x‖) ^
          NumberField.Units.rank K := by
  classical
  let e := NumberField.Units.equivFinRank K
  let u := boundedFundSystem hB
  let b := (NumberField.Units.basisOfIsMaxRank
    (boundedFundSystem_isMaxRank hB)).reindex e
  let v : {w : InfinitePlace K // w ≠ NumberField.Units.dirichletUnitTheorem.w₀} →
      NumberField.Units.dirichletUnitTheorem.logSpace K :=
    fun w ↦ NumberField.Units.logEmbedding K (Additive.ofMul (u (e.symm w)))
  have hv : LinearIndependent ℝ v := by
    exact (linearIndependent_equiv e.symm).mpr (boundedFundSystem_isMaxRank hB)
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range v) := by
    exact (hv.span_eq_top_of_card_eq_finrank' (by
      rw [Module.finrank_pi])).ge
  have hcoord := basisCoordinate_mul_det_le v hv hsp
    (commonBoundedUnitLogBound (K := K) B) (fun a z ↦ by
      simpa [v, u, NumberField.IsTotallyReal.mult_eq] using
        boundedFundSystem_log_abs_le hB (e.symm a) z.1) x (e i)
  have hbasis : (Basis.mk hv hsp).repr x (e i) =
      (NumberField.Units.basisOfIsMaxRank (boundedFundSystem_isMaxRank hB)).repr x i := by
    have hmk : Basis.mk hv hsp = b := by
      ext j
      simp [b, v, u, e]
    rw [hmk]
    simp [b]
  rw [hbasis] at hcoord
  have hdet : |(Pi.basisFun ℝ
      {w : InfinitePlace K // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}).det v| =
      NumberField.Units.regOfFamily (boundedFundSystem hB) := by
    rw [Pi.basisFun_det_apply]
    rw [NumberField.Units.regOfFamily_eq_det (boundedFundSystem hB)
      NumberField.Units.dirichletUnitTheorem.w₀ e.symm]
    congr 2
  rw [hdet] at hcoord
  simpa [NumberField.Units.rank] using hcoord

set_option backward.isDefEq.respectTransparency.types false in
theorem regOf_boundedFundSystem_le {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B) :
    NumberField.Units.regOfFamily (boundedFundSystem hB) ≤
      (NumberField.Units.rank K).factorial *
        (commonBoundedUnitLogBound (K := K) B) ^ NumberField.Units.rank K := by
  classical
  let e : {w : InfinitePlace K // w ≠ w₀} ≃ Fin (NumberField.Units.rank K) :=
    (NumberField.Units.equivFinRank K).symm
  rw [NumberField.Units.regOfFamily_eq_det (boundedFundSystem hB) w₀ e]
  have hdet := Matrix.det_le
    (A := Matrix.of fun i w : {w : InfinitePlace K // w ≠ w₀} ↦
      (InfinitePlace.mult w.val : ℝ) *
        Real.log (w.val (boundedFundSystem hB (e i) : K)))
    (abv := AbsoluteValue.abs)
    (x := commonBoundedUnitLogBound (K := K) B) (fun i w ↦ ?_)
  · simpa [NumberField.Units.rank, nsmul_eq_mul] using hdet
  · simp only [Matrix.of_apply, AbsoluteValue.abs_apply]
    rw [NumberField.IsTotallyReal.mult_eq, Nat.cast_one, one_mul]
    exact boundedFundSystem_log_abs_le hB (e i) w.1

lemma commonBoundedUnitLogBound_nonneg {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B) :
    0 ≤ commonBoundedUnitLogBound (K := K) B := by
  unfold commonBoundedUnitLogBound
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Real.log_nonneg
  have hBnat : 1 ≤ B := by
    by_contra h
    have hB0 : B = 0 := by omega
    subst B
    simp at hB
  unfold commonBoundedStepFactor
  exact_mod_cast mul_le_mul (show (1 : ℝ≥0) ≤ B by exact_mod_cast hBnat)
    (one_le_pow₀ (show (1 : ℝ≥0) ≤ 2 by norm_num)) (by norm_num) (by norm_num)

noncomputable def boundedUnitRegulatorUpper (B : ℕ) : ℝ :=
  (NumberField.Units.rank K).factorial *
    (commonBoundedUnitLogBound (K := K) B) ^ NumberField.Units.rank K

noncomputable def boundedUnitIndexUpper (ε : ℝ) (B : ℕ) : ℕ :=
  ⌈boundedUnitRegulatorUpper (K := K) B /
    ε ^ NumberField.Units.rank K⌉₊

def boundedUnitSubgroup {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B) :
    Subgroup (NumberField.RingOfIntegers K)ˣ :=
  Subgroup.closure (Set.range (boundedFundSystem hB)) ⊔
    NumberField.Units.torsion K

lemma boundedUnitSubgroup_finiteIndex {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B) :
    (boundedUnitSubgroup hB).FiniteIndex := by
  apply (NumberField.Units.finiteIndex_iff_sup_torsion_finiteIndex _).mp
  exact NumberField.Units.isMaxRank_iff_closure_finiteIndex.mp
    (boundedFundSystem_isMaxRank hB)

lemma boundedUnitSubgroup_index_ne_zero {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B) :
    (boundedUnitSubgroup hB).index ≠ 0 := by
  letI : (boundedUnitSubgroup hB).FiniteIndex := boundedUnitSubgroup_finiteIndex hB
  exact Subgroup.FiniteIndex.index_ne_zero

theorem boundedUnitSubgroup_index_le {B : ℕ} {ε : ℝ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B)
    (hε : 0 < ε)
    (hreg : ε ^ NumberField.Units.rank K ≤
      NumberField.Units.regulator K) :
    (boundedUnitSubgroup hB).index ≤
      boundedUnitIndexUpper (K := K) ε B := by
  have hregpos : 0 < NumberField.Units.regulator K :=
    NumberField.Units.regulator_pos K
  have hεpow : 0 < ε ^ NumberField.Units.rank K := pow_pos hε _
  have hupperNonneg : 0 ≤ boundedUnitRegulatorUpper (K := K) B := by
    unfold boundedUnitRegulatorUpper
    exact mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (commonBoundedUnitLogBound_nonneg hB) _)
  have hreal : ((boundedUnitSubgroup hB).index : ℝ) ≤
      boundedUnitRegulatorUpper (K := K) B /
        ε ^ NumberField.Units.rank K := by
    calc
      ((boundedUnitSubgroup hB).index : ℝ) =
          NumberField.Units.regOfFamily (boundedFundSystem hB) /
            NumberField.Units.regulator K := by
        symm
        simpa only [boundedUnitSubgroup] using
          NumberField.Units.regOfFamily_div_regulator (boundedFundSystem hB)
      _ ≤ boundedUnitRegulatorUpper (K := K) B /
            NumberField.Units.regulator K := by
        apply div_le_div_of_nonneg_right _ hregpos.le
        simpa only [boundedUnitRegulatorUpper] using
          regOf_boundedFundSystem_le hB
      _ ≤ boundedUnitRegulatorUpper (K := K) B /
            ε ^ NumberField.Units.rank K := by
        exact div_le_div_of_nonneg_left hupperNonneg hεpow hreg
  exact (Nat.cast_le (α := ℝ)).mp
    (hreal.trans (Nat.le_ceil _))

/-- Cramer's rule together with a regulator lower bound gives an
explicit coordinate bound in the bounded fundamental system. -/
theorem boundedFundSystem_coordinate_le_of_regulator_lower {B : ℕ} {ε : ℝ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B)
    (hε : 0 < ε)
    (hreg : ε ^ NumberField.Units.rank K ≤
      NumberField.Units.regulator K)
    (x : NumberField.Units.dirichletUnitTheorem.logSpace K)
    (i : Fin (NumberField.Units.rank K)) :
    |(NumberField.Units.basisOfIsMaxRank (boundedFundSystem_isMaxRank hB)).repr x i| ≤
      ((NumberField.Units.rank K).factorial *
        (max (commonBoundedUnitLogBound (K := K) B) ‖x‖) ^
          NumberField.Units.rank K) /
        ε ^ NumberField.Units.rank K := by
  have hregpos : 0 < NumberField.Units.regulator K :=
    NumberField.Units.regulator_pos K
  have hindex : 1 ≤ (boundedUnitSubgroup hB).index :=
    Nat.one_le_iff_ne_zero.mpr (boundedUnitSubgroup_index_ne_zero hB)
  have hfamily : NumberField.Units.regulator K ≤
      NumberField.Units.regOfFamily (boundedFundSystem hB) := by
    have hq : (1 : ℝ) ≤
        NumberField.Units.regOfFamily (boundedFundSystem hB) /
          NumberField.Units.regulator K := by
      rw [NumberField.Units.regOfFamily_div_regulator]
      exact_mod_cast hindex
    simpa using (le_div_iff₀ hregpos).mp hq
  have hεfamily : ε ^ NumberField.Units.rank K ≤
      NumberField.Units.regOfFamily (boundedFundSystem hB) :=
    hreg.trans hfamily
  have hcoord := boundedFundSystem_coordinate_mul_regulator_le hB x i
  have hmul :
      |(NumberField.Units.basisOfIsMaxRank
        (boundedFundSystem_isMaxRank hB)).repr x i| *
          ε ^ NumberField.Units.rank K ≤
        (NumberField.Units.rank K).factorial *
          (max (commonBoundedUnitLogBound (K := K) B) ‖x‖) ^
            NumberField.Units.rank K :=
    (mul_le_mul_of_nonneg_left hεfamily (abs_nonneg _)).trans hcoord
  exact (le_div_iff₀ (pow_pos hε _)).2 hmul

/-- The logarithmic embedding turns a finitely supported product of
integer powers into the corresponding real linear combination. -/
lemma logEmbedding_finsupp_prod
    (u : Fin (NumberField.Units.rank K) → (NumberField.RingOfIntegers K)ˣ)
    (a : Fin (NumberField.Units.rank K) →₀ ℤ) :
    NumberField.Units.logEmbedding K
        (Additive.ofMul (a.prod (fun i z ↦ u i ^ z))) =
      a.sum (fun i z ↦ (z : ℝ) •
        NumberField.Units.logEmbedding K (Additive.ofMul (u i))) := by
  change NumberField.Units.logEmbedding K
      (Additive.ofMul (∏ i ∈ a.support, u i ^ a i)) =
    ∑ i ∈ a.support, (a i : ℝ) •
      NumberField.Units.logEmbedding K (Additive.ofMul (u i))
  rw [ofMul_prod, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ofMul_zpow, map_zsmul]
  ext w
  simp

theorem boundedUnit_pow_decomposition {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B)
    (q : (NumberField.RingOfIntegers K)ˣ) :
    ∃ (ζ : NumberField.Units.torsion K)
        (a : Fin (NumberField.Units.rank K) →₀ ℤ),
      q ^ (boundedUnitSubgroup hB).index =
        ζ.1 * a.prod (fun i z ↦ boundedFundSystem hB i ^ z) := by
  have hmem : q ^ (boundedUnitSubgroup hB).index ∈ boundedUnitSubgroup hB :=
    Subgroup.pow_index_mem (boundedUnitSubgroup hB) q
  rw [boundedUnitSubgroup, Subgroup.mem_sup] at hmem
  obtain ⟨y, hy, z, hz, hyz⟩ := hmem
  obtain ⟨a, ha⟩ :=
    Subgroup.exists_finsupp_of_mem_closure_range (boundedFundSystem hB) y hy
  refine ⟨⟨z, hz⟩, a, ?_⟩
  change q ^ (Subgroup.closure (Set.range (boundedFundSystem hB)) ⊔
      NumberField.Units.torsion K).index =
    z * a.prod (fun i z ↦ boundedFundSystem hB i ^ z)
  rw [← hyz, ha]
  exact mul_comm _ _

/-- For any displayed bounded-unit decomposition, its integer exponents
are exactly the real coordinates of the powered unit's logarithmic
embedding in the bounded fundamental system. -/
lemma boundedUnit_decomposition_log_coordinates {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B)
    (q : (NumberField.RingOfIntegers K)ˣ)
    (ζ : NumberField.Units.torsion K)
    (a : Fin (NumberField.Units.rank K) →₀ ℤ)
    (ha : q ^ (boundedUnitSubgroup hB).index =
      ζ.1 * a.prod (fun i z ↦ boundedFundSystem hB i ^ z)) :
    ∀ i,
      ((a i : ℤ) : ℝ) =
        (NumberField.Units.basisOfIsMaxRank
          (boundedFundSystem_isMaxRank hB)).repr
            (NumberField.Units.logEmbedding K
              (Additive.ofMul (q ^ (boundedUnitSubgroup hB).index))) i := by
  intro i
  let b := NumberField.Units.basisOfIsMaxRank
    (boundedFundSystem_isMaxRank hB)
  have hlog := congrArg
    (fun z : (NumberField.RingOfIntegers K)ˣ ↦
      NumberField.Units.logEmbedding K (Additive.ofMul z)) ha
  have hζ : NumberField.Units.logEmbedding K (Additive.ofMul ζ.1) = 0 :=
    NumberField.Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff.mpr ζ.2
  simp only [ofMul_mul, map_add, hζ, zero_add,
    logEmbedding_finsupp_prod] at hlog
  have hre := congrArg (fun x ↦ b.repr x i) hlog
  have hb : ∀ c, NumberField.Units.logEmbedding K
      (Additive.ofMul (boundedFundSystem hB c)) = b c := by
    intro c
    exact (NumberField.Units.basisOfIsMaxRank_apply
      (boundedFundSystem_isMaxRank hB) c).symm
  simp_rw [hb] at hre
  simp [Finsupp.sum, map_sum] at hre
  have hsum : (∑ c ∈ a.support, (Finsupp.single c (a c : ℝ)) i) =
      (a i : ℝ) := by
    by_cases hi : i ∈ a.support
    · rw [Finset.sum_eq_single i]
      · simp
      · intro c hc hci
        simp [hci]
      · intro hni
        exact (hni hi).elim
    · have hai : a i = 0 := by simpa [Finsupp.mem_support_iff] using hi
      rw [hai, Int.cast_zero]
      apply Finset.sum_eq_zero
      intro c hc
      have hci : c ≠ i := by
        intro h
        subst c
        exact hi hc
      simp [hci]
  rw [hsum] at hre
  simpa [ofMul_pow, map_nsmul] using hre.symm

/-- The integer exponents in the finite-index decomposition are exactly
the real coordinates of the powered unit's logarithmic embedding in the
bounded fundamental system. -/
lemma boundedUnit_pow_decomposition_log_coordinates {B : ℕ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B)
    (q : (NumberField.RingOfIntegers K)ˣ) :
    ∃ (a : Fin (NumberField.Units.rank K) →₀ ℤ),
      ∀ i,
        ((a i : ℤ) : ℝ) =
          (NumberField.Units.basisOfIsMaxRank
            (boundedFundSystem_isMaxRank hB)).repr
              (NumberField.Units.logEmbedding K
                (Additive.ofMul (q ^ (boundedUnitSubgroup hB).index))) i := by
  obtain ⟨ζ, a, ha⟩ := boundedUnit_pow_decomposition hB q
  exact ⟨a, boundedUnit_decomposition_log_coordinates hB q ζ a ha⟩

/-- The exponent vector in the finite-index decomposition has a fully
explicit bound in terms of the regulator lower bound and the logarithmic
size of the powered unit. -/
theorem boundedUnit_pow_decomposition_exponent_le {B : ℕ} {ε : ℝ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B)
    (hε : 0 < ε)
    (hreg : ε ^ NumberField.Units.rank K ≤
      NumberField.Units.regulator K)
    (q : (NumberField.RingOfIntegers K)ˣ) :
    ∃ (a : Fin (NumberField.Units.rank K) →₀ ℤ),
      ∀ i,
        |((a i : ℤ) : ℝ)| ≤
          ((NumberField.Units.rank K).factorial *
            (max (commonBoundedUnitLogBound (K := K) B)
              ‖NumberField.Units.logEmbedding K
                (Additive.ofMul (q ^ (boundedUnitSubgroup hB).index))‖) ^
              NumberField.Units.rank K) /
            ε ^ NumberField.Units.rank K := by
  obtain ⟨a, ha⟩ := boundedUnit_pow_decomposition_log_coordinates hB q
  refine ⟨a, fun i ↦ ?_⟩
  rw [ha i]
  exact boundedFundSystem_coordinate_le_of_regulator_lower hB hε hreg _ i

/-- Taking a natural power scales the sup norm of the logarithmic
embedding by that natural number. -/
lemma logEmbedding_pow_norm
    (q : (NumberField.RingOfIntegers K)ˣ) (n : ℕ) :
    ‖(fun w => NumberField.Units.logEmbedding K
      (Additive.ofMul (q ^ n)) w)‖ =
      (n : ℝ) * ‖(fun w => NumberField.Units.logEmbedding K
        (Additive.ofMul q) w)‖ := by
  rw [ofMul_pow, map_nsmul]
  have hfun :
      (fun w => (n • NumberField.Units.logEmbedding K
        (Additive.ofMul q)) w) =
        (n : ℝ) • (fun w => NumberField.Units.logEmbedding K
          (Additive.ofMul q) w) := by
    ext w
    simp [nsmul_eq_mul]
  rw [hfun, norm_smul_of_nonneg (Nat.cast_nonneg n)]

/-- The preceding exponent bound can be written entirely in terms of the
unpowered unit: the only extra factor is the explicit subgroup index. -/
theorem boundedUnit_pow_decomposition_exponent_le_unpowered {B : ℕ} {ε : ℝ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B)
    (hε : 0 < ε)
    (hreg : ε ^ NumberField.Units.rank K ≤
      NumberField.Units.regulator K)
    (q : (NumberField.RingOfIntegers K)ˣ) :
    ∃ (a : Fin (NumberField.Units.rank K) →₀ ℤ),
      ∀ i,
        |((a i : ℤ) : ℝ)| ≤
          ((NumberField.Units.rank K).factorial *
            (max (commonBoundedUnitLogBound (K := K) B)
              (((boundedUnitSubgroup hB).index : ℝ) *
                ‖NumberField.Units.logEmbedding K
                  (Additive.ofMul q)‖)) ^
              NumberField.Units.rank K) /
            ε ^ NumberField.Units.rank K := by
  obtain ⟨a, ha⟩ :=
    boundedUnit_pow_decomposition_exponent_le hB hε hreg q
  refine ⟨a, fun i ↦ ?_⟩
  simpa only [logEmbedding_pow_norm] using ha i

/-- The bounded generators, torsion factor, decomposition identity, and
explicit exponent estimates can be chosen simultaneously. -/
theorem boundedUnit_pow_decomposition_with_exponent_le_unpowered
    {B : ℕ} {ε : ℝ}
    (hB : mixedEmbedding.minkowskiBound K 1 <
      (mixedEmbedding.convexBodyLTFactor K) * B)
    (hε : 0 < ε)
    (hreg : ε ^ NumberField.Units.rank K ≤
      NumberField.Units.regulator K)
    (q : (NumberField.RingOfIntegers K)ˣ) :
    ∃ (ζ : NumberField.Units.torsion K)
        (a : Fin (NumberField.Units.rank K) →₀ ℤ),
      q ^ (boundedUnitSubgroup hB).index =
          ζ.1 * a.prod (fun i z ↦ boundedFundSystem hB i ^ z) ∧
        ∀ i,
          |((a i : ℤ) : ℝ)| ≤
            ((NumberField.Units.rank K).factorial *
              (max (commonBoundedUnitLogBound (K := K) B)
                (((boundedUnitSubgroup hB).index : ℝ) *
                  ‖NumberField.Units.logEmbedding K
                    (Additive.ofMul q)‖)) ^
                NumberField.Units.rank K) /
              ε ^ NumberField.Units.rank K := by
  obtain ⟨ζ, a, ha⟩ := boundedUnit_pow_decomposition hB q
  refine ⟨ζ, a, ha, fun i ↦ ?_⟩
  rw [boundedUnit_decomposition_log_coordinates hB q ζ a ha i]
  have hcoord := boundedFundSystem_coordinate_le_of_regulator_lower
    hB hε hreg
    (NumberField.Units.logEmbedding K
      (Additive.ofMul (q ^ (boundedUnitSubgroup hB).index))) i
  simpa only [logEmbedding_pow_norm] using hcoord

end Erdos841.BoundedUnits
