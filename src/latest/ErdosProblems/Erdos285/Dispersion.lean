import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.ZMod.ValMinAbs

/-!
# Martin's modular-inverse dispersion lemma

This file formalizes the modular inverse dispersion estimate used in Greg
Martin's proof of Erdős Problem 285.  The formulation follows Lemma 10 of the
published version of *Denser Egyptian fractions* (Lemma 11 in the arXiv
version).  The distance to the nearest integer is represented by the absolute
value of `ZMod.valMinAbs`.
-/

namespace Erdos285.Dispersion

open Filter Finset Real
open scoped BigOperators Topology

noncomputable section

/-- `m` is a product of exactly `k` distinct primes, none dividing `n`. -/
def IsKPrimeProductAway (k n m : ℕ) : Prop :=
  ∃ P : Finset ℕ, P.card = k ∧
    (∀ p ∈ P, p.Prime ∧ ¬ p ∣ n) ∧ m = P.prod id

/-- Martin's distance `‖h m̅/n‖`, where `m̅` denotes the inverse modulo `n`. -/
def centeredInverse (n h m : ℕ) : ℤ :=
  ((h : ZMod n) * (m : ZMod n)⁻¹).valMinAbs

/-- Martin's distance `‖h m̅/n‖`, where `m̅` denotes the inverse modulo `n`. -/
def inverseDistance (n h m : ℕ) : ℝ :=
  (centeredInverse n h m).natAbs / n

/-- The right-hand side in Martin's inverse-dispersion inequality. -/
def dispersionThreshold (n k : ℕ) (B C : ℝ) : ℝ :=
  C * Real.log (Real.log n) ^ k / (200 * B * Real.log n ^ k)

lemma factorial_card_le_prod_of_one_le (s : Finset ℕ)
    (hs : ∀ x ∈ s, 1 ≤ x) :
    Nat.factorial s.card ≤ ∏ x ∈ s, x := by
  let f : Fin s.card ↪o ℕ := s.orderEmbOfFin rfl
  have hidx : ∀ i : ℕ, ∀ hi : i < s.card, i + 1 ≤ f ⟨i, hi⟩ := by
    intro i hi
    induction i with
    | zero =>
        have hmem : f ⟨0, hi⟩ ∈ s := by simp [f]
        simpa [f] using hs (f ⟨0, hi⟩) hmem
    | succ i ih =>
        have hi' : i < s.card := Nat.lt_of_succ_lt hi
        have hprev : i + 1 ≤ f ⟨i, hi'⟩ := ih hi'
        have hlt : f ⟨i, hi'⟩ < f ⟨i + 1, hi⟩ :=
          f.strictMono (Nat.lt_succ_self i)
        exact le_trans (Nat.succ_le_succ hprev) (Nat.succ_le_of_lt hlt)
  have hprod : (∏ i : Fin s.card, (i.1 + 1)) ≤ ∏ i : Fin s.card, f i := by
    exact Finset.prod_le_prod' fun i _ ↦ hidx i.1 i.2
  have hleft : (∏ i : Fin s.card, (i.1 + 1)) = Nat.factorial s.card := by
    calc
      (∏ i : Fin s.card, (i.1 + 1)) = ∏ i ∈ Finset.range s.card, (i + 1) := by
        simpa using (Fin.prod_univ_eq_prod_range (fun i : ℕ ↦ i + 1) s.card)
      _ = Nat.factorial s.card := Finset.prod_range_add_one_eq_factorial s.card
  have hright : (∏ i : Fin s.card, f i) = ∏ x ∈ s, x := by
    calc
      (∏ i : Fin s.card, f i) =
          ∏ x ∈ Finset.map (s.orderEmbOfFin rfl).toEmbedding Finset.univ, x := by
        symm
        simpa [f] using
          (Finset.prod_map (s := Finset.univ)
            (e := (s.orderEmbOfFin rfl).toEmbedding) (f := fun x : ℕ ↦ x))
      _ = ∏ x ∈ s, x := by rw [Finset.map_orderEmbOfFin_univ (s := s) (h := rfl)]
  exact hleft ▸ hright ▸ hprod

lemma factorial_card_primeFactors_le (m : ℕ) (hm : m ≠ 0) :
    Nat.factorial m.primeFactors.card ≤ m := by
  refine (factorial_card_le_prod_of_one_le m.primeFactors ?_).trans ?_
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).one_le
  · exact Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.prod_primeFactors_dvd m)

/-- The elementary maximal-order estimate for the number of distinct prime
factors, in precisely the uniform form used by Martin. -/
lemma eventually_primeFactors_card_lt_four_log_div_loglog :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 0 < m → m < n ^ 2 →
      (m.primeFactors.card : ℝ) <
        4 * Real.log n / Real.log (Real.log n) := by
  have hloglog : Tendsto (fun n : ℕ ↦ Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hloglog.eventually (eventually_gt_atTop (16 : ℝ))] with n hn
  intro m hm hm_lt
  let r := m.primeFactors.card
  have hn2 : 2 ≤ n := by
    by_contra h
    have hnle : n ≤ 1 := by omega
    interval_cases n <;> norm_num at hn
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn2
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos hnR
  have hll_pos : 0 < Real.log (Real.log (n : ℝ)) := lt_trans (by norm_num) hn
  by_contra hbound
  have hr_lower : 4 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) ≤ (r : ℝ) :=
    le_of_not_gt hbound
  have hr_pos : 0 < (r : ℝ) := lt_of_lt_of_le (by positivity) hr_lower
  have hlogll_le_half :
      Real.log (Real.log (Real.log (n : ℝ))) ≤
        Real.log (Real.log (n : ℝ)) / 2 := by
    let u := Real.log (Real.log (n : ℝ))
    have hu : 16 ≤ u := hn.le
    have hlogu : Real.log u ≤ u ^ ((1 : ℝ) / 2) / ((1 : ℝ) / 2) :=
      Real.log_le_rpow_div (by positivity) (by norm_num)
    have hsqrt : u ^ ((1 : ℝ) / 2) = Real.sqrt u := by
      rw [Real.sqrt_eq_rpow]
    have hsqrt_le : Real.sqrt u ≤ u / 4 := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · have hu0 : 0 ≤ u := le_trans (by norm_num) hu
        nlinarith [sq_sqrt hu0]
    dsimp [u] at hlogu hsqrt hsqrt_le ⊢
    rw [hsqrt] at hlogu
    nlinarith
  have hlogr_lower :
      Real.log (Real.log (n : ℝ)) / 2 + 1 < Real.log (r : ℝ) := by
    have hfour_pos : (0 : ℝ) < 4 := by norm_num
    have hquot_pos : 0 < Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) :=
      div_pos hlogn_pos hll_pos
    have hlog_mono :
        Real.log (4 * (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))) ≤
          Real.log (r : ℝ) :=
      Real.log_le_log (mul_pos hfour_pos hquot_pos) (by
        simpa [mul_div_assoc] using hr_lower)
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hquot_pos),
      Real.log_div (ne_of_gt hlogn_pos) (ne_of_gt hll_pos)] at hlog_mono
    have hlogfour : (1 : ℝ) < Real.log 4 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      exact (Real.exp_one_lt_d9).trans_le (by norm_num)
    linarith
  have hstirling :
      (r : ℝ) * Real.log r - r ≤ Real.log (Nat.factorial r : ℝ) := by
    have hr_nat : 0 < r := by exact_mod_cast hr_pos
    have h := Stirling.le_log_factorial_stirling hr_nat.ne'
    have hlogr_nonneg : 0 ≤ Real.log (r : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hr_nat)
    have hlogtwopi_nonneg : 0 ≤ Real.log (2 * Real.pi) :=
      Real.log_nonneg (by nlinarith [Real.pi_gt_three])
    nlinarith
  have hfact_le : Nat.factorial r ≤ m := factorial_card_primeFactors_le m hm.ne'
  have hlogfact_lt : Real.log (Nat.factorial r : ℝ) < 2 * Real.log n := by
    have hcast_fact : (Nat.factorial r : ℝ) ≤ m := by exact_mod_cast hfact_le
    have hcast_m : (m : ℝ) < (n : ℝ) ^ 2 := by exact_mod_cast hm_lt
    have hposfact : (0 : ℝ) < Nat.factorial r := by positivity
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hnpowR : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    calc
      Real.log (Nat.factorial r : ℝ) ≤ Real.log (m : ℝ) :=
        Real.log_le_log hposfact hcast_fact
      _ < Real.log ((n : ℝ) ^ 2) := Real.strictMonoOn_log hmR hnpowR hcast_m
      _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num
  have hmain : 2 * Real.log (n : ℝ) < (r : ℝ) * Real.log r - r := by
    have hdiff : Real.log (Real.log (n : ℝ)) / 2 < Real.log (r : ℝ) - 1 := by
      linarith
    have := mul_lt_mul_of_pos_left hdiff hr_pos
    have hcancel :
        (r : ℝ) * (Real.log (Real.log (n : ℝ)) / 2) ≥
          2 * Real.log (n : ℝ) := by
      have := mul_le_mul_of_nonneg_right hr_lower (le_of_lt (half_pos hll_pos))
      field_simp [hll_pos.ne'] at this ⊢
      nlinarith
    nlinarith
  linarith

lemma primeFactors_eq_of_isKPrimeProductAway {k n m : ℕ}
    (hm : IsKPrimeProductAway k n m) :
    ∃ P : Finset ℕ, P.card = k ∧ m.primeFactors = P ∧
      (∀ p ∈ P, p.Prime ∧ ¬ p ∣ n) := by
  obtain ⟨P, hPk, hP, rfl⟩ := hm
  refine ⟨P, hPk, Nat.primeFactors_prod (fun p hp ↦ (hP p hp).1), hP⟩

lemma isKPrimeProductAway_pos {k n m : ℕ} (hm : IsKPrimeProductAway k n m) :
    0 < m := by
  obtain ⟨P, -, hP, rfl⟩ := hm
  exact Finset.prod_pos fun p hp ↦ (hP p hp).1.pos

lemma isKPrimeProductAway_coprime {k n m : ℕ} (hm : IsKPrimeProductAway k n m) :
    Nat.Coprime m n := by
  obtain ⟨P, -, hP, rfl⟩ := hm
  rw [Nat.coprime_prod_left_iff]
  intro p hp
  exact (hP p hp).1.coprime_iff_not_dvd.mpr (hP p hp).2

lemma isKPrimeProductAway_primeFactors_card {k n m : ℕ}
    (hm : IsKPrimeProductAway k n m) : m.primeFactors.card = k := by
  obtain ⟨P, hPk, hprime, -⟩ := primeFactors_eq_of_isKPrimeProductAway hm
  rw [hprime, hPk]

/-- The integer `s_m = (m r_m - h)/n` in Martin's proof. -/
def quotientIndex (n h m : ℕ) : ℤ :=
  ((m : ℤ) * centeredInverse n h m - h) / n

lemma centeredInverse_mul_sub_dvd {n h m : ℕ} (hn : n ≠ 0)
    (hcop : Nat.Coprime m n) :
    (n : ℤ) ∣ (m : ℤ) * centeredInverse n h m - h := by
  let _ : NeZero n := ⟨hn⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, centeredInverse,
    ZMod.coe_valMinAbs]
  have hu : IsUnit (m : ZMod n) := (ZMod.isUnit_iff_coprime m n).mpr hcop
  calc
    (m : ZMod n) * ((h : ZMod n) * (m : ZMod n)⁻¹) - h =
        (h : ZMod n) * ((m : ZMod n) * (m : ZMod n)⁻¹) - h := by ring
    _ = 0 := by rw [ZMod.mul_inv_of_unit (m : ZMod n) hu, mul_one, sub_self]

lemma quotientIndex_spec {n h m : ℕ} (hn : n ≠ 0)
    (hcop : Nat.Coprime m n) :
    (n : ℤ) * quotientIndex n h m =
      (m : ℤ) * centeredInverse n h m - h := by
  rw [quotientIndex, mul_comm]
  exact Int.ediv_mul_cancel (centeredInverse_mul_sub_dvd hn hcop)

lemma centeredInverse_ne_zero {n h m : ℕ} (hn : n ≠ 0)
    (hhpos : 0 < h) (hhlt : h < n) (hcop : Nat.Coprime m n) :
    centeredInverse n h m ≠ 0 := by
  let _ : NeZero n := ⟨hn⟩
  simp only [centeredInverse, ne_eq, ZMod.valMinAbs_eq_zero]
  have hh : (h : ZMod n) ≠ 0 := by
    intro hzero
    have hdvd : n ∣ h := (ZMod.natCast_eq_zero_iff h n).mp hzero
    have := Nat.le_of_dvd hhpos hdvd
    omega
  have hu : IsUnit (m : ZMod n) := (ZMod.isUnit_iff_coprime m n).mpr hcop
  intro hz
  have hz' := congrArg (fun x : ZMod n ↦ x * (m : ZMod n)) hz
  rw [zero_mul, mul_assoc, ZMod.inv_mul_of_unit (m : ZMod n) hu, mul_one] at hz'
  exact hh hz'

lemma card_le_card_image_mul_of_fiber_bound {A B : Type*}
    [DecidableEq A] [DecidableEq B] (S : Finset A) (f : A → B) (D : ℕ)
    (hfiber : ∀ b ∈ S.image f, (S.filter fun a ↦ f a = b).card ≤ D) :
    S.card ≤ (S.image f).card * D := by
  rw [Finset.card_eq_sum_card_fiberwise (t := S.image f) (f := f) (by
    intro a ha
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨a, Finset.mem_coe.mp ha, rfl⟩))]
  calc
    ∑ b ∈ S.image f, (S.filter fun a ↦ f a = b).card
        ≤ ∑ _b ∈ S.image f, D := Finset.sum_le_sum fun b hb ↦ hfiber b hb
    _ = (S.image f).card * D := by simp

lemma four_pow_lt_twenty_mul_factorial (k : ℕ) :
    4 ^ k < 20 * Nat.factorial k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      by_cases hk : k < 3
      · interval_cases k <;> norm_num [Nat.factorial]
      · have hk4 : 4 ≤ k + 1 := by omega
        rw [pow_succ, Nat.factorial_succ]
        calc
          4 ^ k * 4 < (20 * Nat.factorial k) * 4 :=
            Nat.mul_lt_mul_of_pos_right ih (by norm_num)
          _ ≤ 20 * ((k + 1) * Nat.factorial k) := by
            nlinarith [Nat.factorial_pos k]

lemma four_pow_div_factorial_lt_twenty (k : ℕ) :
    (4 : ℝ) ^ k / Nat.factorial k < 20 := by
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < Nat.factorial k)]
  exact_mod_cast four_pow_lt_twenty_mul_factorial k

/-- A fiber of Martin's integer `s_m` injects into the `k`-element subsets
of the prime divisors of `|nz+h|`. -/
lemma quotientIndex_fiber_card_le_choose
    {k n h : ℕ} (hn : n ≠ 0) (hhpos : 0 < h) (hhlt : h < n)
    (M : Finset ℕ) (hM : ∀ m ∈ M, IsKPrimeProductAway k n m) (z : ℤ) :
    ((M.filter fun m ↦ quotientIndex n h m = z).card : ℕ) ≤
      (n * z + h).natAbs.primeFactors.card.choose k := by
  let F := M.filter fun m ↦ quotientIndex n h m = z
  let q := (n * z + h).natAbs
  have hinj : Set.InjOn Nat.primeFactors F := by
    intro a ha b hb hab
    have haM : a ∈ M := (Finset.mem_filter.mp ha).1
    have hbM : b ∈ M := (Finset.mem_filter.mp hb).1
    obtain ⟨Pa, -, hPa, haeq⟩ := hM a haM
    obtain ⟨Pb, -, hPb, hbeq⟩ := hM b hbM
    have hpfa : a.primeFactors = Pa := by
      rw [haeq]
      exact Nat.primeFactors_prod fun p hp ↦ (hPa p hp).1
    have hpfb : b.primeFactors = Pb := by
      rw [hbeq]
      exact Nat.primeFactors_prod fun p hp ↦ (hPb p hp).1
    have hPP : Pa = Pb := hpfa.symm.trans (hab.trans hpfb)
    rw [haeq, hbeq, hPP]
  have hsub : F.image Nat.primeFactors ⊆ q.primeFactors.powersetCard k := by
    intro P hP
    obtain ⟨m, hmF, rfl⟩ := Finset.mem_image.mp hP
    have hmM : m ∈ M := (Finset.mem_filter.mp hmF).1
    have hmz : quotientIndex n h m = z := (Finset.mem_filter.mp hmF).2
    have hmprop := hM m hmM
    have hmpos := isKPrimeProductAway_pos hmprop
    have hmcop := isKPrimeProductAway_coprime hmprop
    have hrne := centeredInverse_ne_zero hn hhpos hhlt hmcop
    have hspec := quotientIndex_spec (n := n) (h := h) (m := m) hn hmcop
    rw [hmz] at hspec
    have heq : (n : ℤ) * z + h = (m : ℤ) * centeredInverse n h m := by
      linarith
    have hqeq : q = m * (centeredInverse n h m).natAbs := by
      dsimp [q]
      rw [heq, Int.natAbs_mul, Int.natAbs_natCast]
    have hqne : q ≠ 0 := by
      rw [hqeq]
      exact Nat.mul_ne_zero hmpos.ne' (Int.natAbs_ne_zero.mpr hrne)
    rw [Finset.mem_powersetCard]
    constructor
    · apply Nat.primeFactors_mono
      · rw [hqeq]
        exact dvd_mul_right m _
      · exact hqne
    · exact isKPrimeProductAway_primeFactors_card hmprop
  calc
    F.card = (F.image Nat.primeFactors).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (q.primeFactors.powersetCard k).card := Finset.card_le_card hsub
    _ = q.primeFactors.card.choose k := Finset.card_powersetCard k q.primeFactors

lemma choose_primeFactors_lt_twenty_ratio_pow
    {k n q : ℕ} (hk : 0 < k)
    (hlog : 0 < Real.log (n : ℝ))
    (hloglog : 0 < Real.log (Real.log (n : ℝ)))
    (homega : ∀ m : ℕ, 0 < m → m < n ^ 2 →
      (m.primeFactors.card : ℝ) <
        4 * Real.log n / Real.log (Real.log n))
    (hqpos : 0 < q) (hqlt : q < n ^ 2) :
    (q.primeFactors.card.choose k : ℝ) <
      20 * (Real.log n / Real.log (Real.log n)) ^ k := by
  let L := Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))
  have hL : 0 < L := div_pos hlog hloglog
  have hw := homega q hqpos hqlt
  have hpow : (q.primeFactors.card : ℝ) ^ k < (4 * L) ^ k := by
    apply pow_lt_pow_left₀
    · simpa [L, mul_div_assoc] using hw
    · positivity
    · exact hk.ne'
  calc
    (q.primeFactors.card.choose k : ℝ)
        ≤ (q.primeFactors.card : ℝ) ^ k / Nat.factorial k :=
      Nat.choose_le_pow_div k q.primeFactors.card
    _ < (4 * L) ^ k / Nat.factorial k :=
      div_lt_div_of_pos_right hpow (by positivity)
    _ = ((4 : ℝ) ^ k / Nat.factorial k) * L ^ k := by
      rw [mul_pow]
      ring
    _ < 20 * L ^ k :=
      mul_lt_mul_of_pos_right (four_pow_div_factorial_lt_twenty k) (pow_pos hL k)
    _ = 20 * (Real.log n / Real.log (Real.log n)) ^ k := rfl

/-- **Martin's modular-inverse dispersion lemma** (published Lemma 10).

For all sufficiently large moduli `n`, if `M` has more than `C` elements,
each below `B` and each a product of `k` distinct primes avoiding `n`, then
for every nonzero residue `h`, at least `C / 2` of their inverse residues are
farther from zero than Martin's stated threshold. -/
theorem martin_inverse_dispersion (k : ℕ) (hk : 0 < k) :
    ∀ᶠ n : ℕ in atTop, ∀ (B C : ℝ) (M : Finset ℕ),
      0 < B → 0 < C →
      200 * (Real.log n / Real.log (Real.log n)) ^ k < C →
      C < n → C < M.card →
      (∀ m ∈ M, (m : ℝ) < B ∧ IsKPrimeProductAway k n m) →
      ∀ h : ℕ, 0 < h → h < n →
        C / 2 ≤
          ((M.filter fun m ↦
            dispersionThreshold n k B C < inverseDistance n h m).card : ℝ) := by
  have hllTop : Tendsto (fun n : ℕ ↦ Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_primeFactors_card_lt_four_log_div_loglog,
    hllTop.eventually (eventually_gt_atTop (16 : ℝ))] with n homega hnll
  intro B C M hB hCpos hC hCn hCM hM h hhpos hhlt
  have hnpos : 0 < n := lt_trans hhpos hhlt
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hlog : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    have hn2 : 2 ≤ n := by omega
    exact_mod_cast hn2
  have hll : 0 < Real.log (Real.log (n : ℝ)) := lt_trans (by norm_num) hnll
  let L := Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))
  let X := C / (100 * L ^ k)
  let T := dispersionThreshold n k B C
  have hL : 0 < L := div_pos hlog hll
  have hLpow : 0 < L ^ k := pow_pos hL k
  have hC' : 200 * L ^ k < C := by simpa [L] using hC
  have hX : 2 < X := by
    change 2 < C / (100 * L ^ k)
    rw [lt_div_iff₀ (mul_pos (by norm_num) hLpow)]
    nlinarith
  have hlog_lt : Real.log (Real.log (n : ℝ)) < Real.log (n : ℝ) := by
    have hlog_ne_one : Real.log (n : ℝ) ≠ 1 := by
      intro heq
      rw [heq, Real.log_one] at hnll
      norm_num at hnll
    have := Real.log_lt_sub_one_of_pos hlog hlog_ne_one
    linarith
  have hLone : 1 < L := by
    change 1 < Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))
    rw [lt_div_iff₀ hll]
    simpa using hlog_lt
  have hden : 1 < 100 * L ^ k := by
    have hpowone : 1 ≤ L ^ k := one_le_pow₀ hLone.le
    nlinarith
  have hXltC : X < C := by
    simpa [X] using (div_lt_self hCpos hden)
  have hXltn : X < (n : ℝ) := hXltC.trans hCn
  have hTeq : T = X / (2 * B) := by
    dsimp [T, X, L, dispersionThreshold]
    rw [div_pow]
    field_simp [hB.ne', hlog.ne', hll.ne']
    norm_num
  let bad := M.filter fun m ↦ inverseDistance n h m ≤ T
  let good := M.filter fun m ↦ T < inverseDistance n h m
  by_contra hgoal
  have hgoodlt : (good.card : ℝ) < C / 2 := by
    have : ¬ C / 2 ≤ (good.card : ℝ) := by
      simpa [good, T] using hgoal
    exact lt_of_not_ge this
  have hpartition : bad.card + good.card = M.card := by
    have hp := Finset.card_filter_add_card_filter_not
      (s := M) (p := fun m ↦ inverseDistance n h m ≤ T)
    have hcomp :
        (M.filter fun m ↦ ¬ inverseDistance n h m ≤ T) = good := by
      ext m
      simp [good]
    simpa [bad, hcomp] using hp
  have hbadlarge : C / 2 < (bad.card : ℝ) := by
    have hpartR : (bad.card : ℝ) + good.card = M.card := by exact_mod_cast hpartition
    nlinarith
  have hbad_nonempty : bad.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he] at hbadlarge
    simp at hbadlarge
    linarith
  have hquotient_bound : ∀ m ∈ bad, |(quotientIndex n h m : ℝ)| < X := by
    intro m hmbad
    have hmM : m ∈ M := (Finset.mem_filter.mp hmbad).1
    have hmdist : inverseDistance n h m ≤ T := (Finset.mem_filter.mp hmbad).2
    have hmB := (hM m hmM).1
    have hmprop := (hM m hmM).2
    have hmpos := isKPrimeProductAway_pos hmprop
    have hmcop := isKPrimeProductAway_coprime hmprop
    have hrne := centeredInverse_ne_zero hnpos.ne' hhpos hhlt hmcop
    let R : ℝ := (centeredInverse n h m).natAbs
    have hRpos : 0 < R := by
      dsimp [R]
      exact_mod_cast Int.natAbs_pos.mpr hrne
    have hRle : R ≤ (n : ℝ) * T := by
      have := hmdist
      rw [inverseDistance, div_le_iff₀ hnR] at this
      simpa [R, mul_comm] using this
    have hmR : (m : ℝ) * R < (n : ℝ) * X / 2 := by
      calc
        (m : ℝ) * R < B * R := mul_lt_mul_of_pos_right hmB hRpos
        _ ≤ B * ((n : ℝ) * T) := mul_le_mul_of_nonneg_left hRle hB.le
        _ = (n : ℝ) * X / 2 := by rw [hTeq]; field_simp [hB.ne']
    have hspec := quotientIndex_spec (n := n) (h := h) (m := m) hnpos.ne' hmcop
    have hspecR :
        (n : ℝ) * (quotientIndex n h m : ℝ) =
          (m : ℝ) * (centeredInverse n h m : ℝ) - h := by
      exact_mod_cast hspec
    have habs : |(centeredInverse n h m : ℝ)| = R := by
      dsimp [R]
      rw [Nat.cast_natAbs, Int.cast_abs]
    have hrupper : (centeredInverse n h m : ℝ) ≤ R := by
      rw [← habs]
      exact le_abs_self _
    have hrlower : -R ≤ (centeredInverse n h m : ℝ) := by
      rw [← habs]
      exact neg_abs_le _
    have hhR : (h : ℝ) < n := by exact_mod_cast hhlt
    have hsupper : (quotientIndex n h m : ℝ) < X := by
      have hmposR : (0 : ℝ) ≤ m := by positivity
      nlinarith
    have hslower : -X < (quotientIndex n h m : ℝ) := by
      have hmposR : (0 : ℝ) ≤ m := by positivity
      nlinarith
    rw [abs_lt]
    exact ⟨hslower, hsupper⟩
  let Zs := bad.image (quotientIndex n h)
  let A : ℤ := ⌊X⌋
  have hA0 : 0 ≤ A := by
    change 0 ≤ ⌊X⌋
    rw [Int.floor_nonneg]
    linarith
  have hZsubset : Zs ⊆ Finset.Icc (-A) A := by
    intro z hz
    obtain ⟨m, hmbad, rfl⟩ := Finset.mem_image.mp hz
    have hs := hquotient_bound m hmbad
    rw [abs_lt] at hs
    rw [Finset.mem_Icc]
    constructor
    · by_contra hnot
      have hzInt : (quotientIndex n h m : ℤ) ≤ -A - 1 := by omega
      have hfloorlt : X < (A : ℝ) + 1 := by simpa [A] using Int.lt_floor_add_one X
      have hzReal : (quotientIndex n h m : ℝ) ≤ (-A - 1 : ℤ) := by exact_mod_cast hzInt
      push_cast at hzReal
      linarith
    · by_contra hnot
      have hzInt : A + 1 ≤ (quotientIndex n h m : ℤ) := by omega
      have hfloorle : (A : ℝ) ≤ X := by simpa [A] using Int.floor_le X
      have hzReal : ((A + 1 : ℤ) : ℝ) ≤ quotientIndex n h m := by exact_mod_cast hzInt
      push_cast at hzReal
      have hfloorlt : X < (A : ℝ) + 1 := by simpa [A] using Int.lt_floor_add_one X
      linarith
  have hZcard : (Zs.card : ℝ) < (5 / 2 : ℝ) * X := by
    have hcardle := Finset.card_le_card hZsubset
    have hcardInt := Int.card_Icc_of_le (-A) A (by omega)
    have hcardReal : ((Finset.Icc (-A) A).card : ℝ) = 2 * (A : ℝ) + 1 := by
      have hcardInt' : ((Finset.Icc (-A) A).card : ℤ) = 2 * A + 1 := by
        linarith
      exact_mod_cast hcardInt'
    have hfloorle : (A : ℝ) ≤ X := by simpa [A] using Int.floor_le X
    have hZle : (Zs.card : ℝ) ≤ 2 * (A : ℝ) + 1 := by
      rw [← hcardReal]
      exact_mod_cast hcardle
    nlinarith
  have hZnonempty : Zs.Nonempty := hbad_nonempty.image _
  have hfiber : ∀ z ∈ Zs,
      (((bad.filter fun m ↦ quotientIndex n h m = z).card : ℕ) : ℝ) <
        20 * L ^ k := by
    intro z hz
    obtain ⟨m, hmbad, hmz⟩ := Finset.mem_image.mp hz
    have hmM : m ∈ M := (Finset.mem_filter.mp hmbad).1
    have hmprop := (hM m hmM).2
    have hmpos := isKPrimeProductAway_pos hmprop
    have hmcop := isKPrimeProductAway_coprime hmprop
    have hrne := centeredInverse_ne_zero hnpos.ne' hhpos hhlt hmcop
    let q := (n * z + h).natAbs
    have hspec := quotientIndex_spec (n := n) (h := h) (m := m) hnpos.ne' hmcop
    rw [hmz] at hspec
    have heq : (n : ℤ) * z + h = (m : ℤ) * centeredInverse n h m := by linarith
    have hqeq : q = m * (centeredInverse n h m).natAbs := by
      dsimp [q]
      rw [heq, Int.natAbs_mul, Int.natAbs_natCast]
    have hqpos : 0 < q := by
      rw [hqeq]
      exact Nat.mul_pos hmpos (Int.natAbs_pos.mpr hrne)
    have hq_lt : q < n ^ 2 := by
      have hqm : (q : ℝ) = (m : ℝ) * (centeredInverse n h m).natAbs := by
        exact_mod_cast hqeq
      have hmB := (hM m hmM).1
      have hmdist : inverseDistance n h m ≤ T := (Finset.mem_filter.mp hmbad).2
      have hRle : ((centeredInverse n h m).natAbs : ℝ) ≤ (n : ℝ) * T := by
        rw [inverseDistance, div_le_iff₀ hnR] at hmdist
        simpa [mul_comm] using hmdist
      have hRpos : (0 : ℝ) < (centeredInverse n h m).natAbs := by
        exact_mod_cast Int.natAbs_pos.mpr hrne
      have hqbound : (q : ℝ) < (n : ℝ) * X / 2 := by
        rw [hqm]
        calc
          (m : ℝ) * (centeredInverse n h m).natAbs <
              B * (centeredInverse n h m).natAbs :=
            mul_lt_mul_of_pos_right hmB hRpos
          _ ≤ B * ((n : ℝ) * T) := mul_le_mul_of_nonneg_left hRle hB.le
          _ = (n : ℝ) * X / 2 := by rw [hTeq]; field_simp [hB.ne']
      have hnpow : (n : ℝ) * X / 2 < (n : ℝ) ^ 2 := by
        nlinarith
      exact_mod_cast hqbound.trans hnpow
    have hbadM : ∀ a ∈ bad, IsKPrimeProductAway k n a := by
      intro a ha
      exact (hM a (Finset.mem_filter.mp ha).1).2
    have hcardchoose := quotientIndex_fiber_card_le_choose hnpos.ne' hhpos hhlt bad hbadM z
    have hchoose := choose_primeFactors_lt_twenty_ratio_pow hk hlog hll homega hqpos hq_lt
    have hcardchooseR :
        ((bad.filter fun m ↦ quotientIndex n h m = z).card : ℝ) ≤
          (q.primeFactors.card.choose k : ℝ) := by
      exact_mod_cast hcardchoose
    exact lt_of_le_of_lt hcardchooseR (by simpa [L, q] using hchoose)
  have hdecomp :
      (bad.card : ℝ) =
        ∑ z ∈ Zs, ((bad.filter fun m ↦ quotientIndex n h m = z).card : ℝ) := by
    have hnat := Finset.card_eq_sum_card_fiberwise
      (s := bad) (t := Zs) (f := quotientIndex n h) (by
        intro m hm
        exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨m, Finset.mem_coe.mp hm, rfl⟩))
    exact_mod_cast hnat
  have hbadupp : (bad.card : ℝ) < (Zs.card : ℝ) * (20 * L ^ k) := by
    rw [hdecomp]
    calc
      ∑ z ∈ Zs, ((bad.filter fun m ↦ quotientIndex n h m = z).card : ℝ)
          < ∑ _z ∈ Zs, 20 * L ^ k := by
        exact Finset.sum_lt_sum_of_nonempty hZnonempty hfiber
      _ = (Zs.card : ℝ) * (20 * L ^ k) := by simp
  have hfinal : (bad.card : ℝ) < C / 2 := by
    calc
      (bad.card : ℝ) < (Zs.card : ℝ) * (20 * L ^ k) := hbadupp
      _ < ((5 / 2 : ℝ) * X) * (20 * L ^ k) :=
        mul_lt_mul_of_pos_right hZcard (mul_pos (by norm_num) hLpow)
      _ = C / 2 := by
        dsimp [X]
        field_simp [hLpow.ne']
        ring
  linarith

end

end Erdos285.Dispersion

#print axioms Erdos285.Dispersion.martin_inverse_dispersion
