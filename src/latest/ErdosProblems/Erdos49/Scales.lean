import ErdosProblems.Erdos49.Assembly
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Integer scales for Erdős Problem 49

We use ceilings of the continuous scales from Tao's proof.  The large
constant in `scaleR` is harmless and gives ample room for the deliberately
coarse eighth-power Rankin product bound.
-/

open Filter Set Topology

namespace Erdos49

noncomputable section

def scaleH (N : ℕ) : ℕ := ⌈Real.log (N : ℝ)⌉₊

def scaleT (N : ℕ) : ℝ := Real.log (Real.log (N : ℝ))

def scaleL (N : ℕ) : ℕ := ⌈Real.exp (20 * scaleT N)⌉₊

def scaleD (N : ℕ) : ℕ := ⌈Real.exp (scaleT N ^ 4)⌉₊

def scaleR (N : ℕ) : ℕ :=
  ⌈Real.exp (Real.log (N : ℝ) / (1000 * scaleT N))⌉₊

def scaleQ (N : ℕ) : ℕ :=
  (4 * scaleD N ^ 2 + 1) * scaleL N

def scaleW (N : ℕ) : ℕ := N / scaleQ N

def scalePairY (N : ℕ) : ℕ := scaleR N / scaleL N

def scaleTripleY (N : ℕ) : ℕ := scaleR N / scaleL N ^ 2

lemma natCast_div_lower {a b : ℕ} (hb : 0 < b) :
    (a : ℝ) / b - 1 < (a / b : ℕ) := by
  have hlt : a < (a / b + 1) * b := by
    calc
      a = b * (a / b) + a % b := (Nat.div_add_mod a b).symm
      _ < b * (a / b) + b := Nat.add_lt_add_left (Nat.mod_lt a hb) _
      _ = (a / b + 1) * b := by ring
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  apply (sub_lt_iff_lt_add).2
  apply (div_lt_iff₀ hbR).2
  exact_mod_cast (by simpa [add_mul] using hlt)

lemma natCast_div_half_lower {a b : ℕ} (hb : 0 < b)
    (hlarge : (2 : ℝ) ≤ (a : ℝ) / b) :
    (a : ℝ) / (2 * b) ≤ (a / b : ℕ) := by
  have h := natCast_div_lower (a := a) hb
  have : (a : ℝ) / (2 * b) ≤ (a : ℝ) / b - 1 := by
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    rw [show (a : ℝ) / (2 * b) = ((a : ℝ) / b) / 2 by ring]
    linarith
  exact this.trans h.le

lemma scale_log_tendsto :
    Tendsto scaleT atTop atTop := by
  unfold scaleT
  exact Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- One dominance inequality supplies all subsequent scale separations. -/
lemma eventually_scale_core :
    ∀ᶠ N : ℕ in atTop,
      10 ≤ scaleT N ∧
      100000 * (1 + scaleT N) ^ 6 ≤ Real.log (N : ℝ) := by
  let t : ℕ → ℝ := scaleT
  have ht : Tendsto t atTop atTop := scale_log_tendsto
  have hdecay := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 6).comp ht
  have hsmall : ∀ᶠ N : ℕ in atTop,
      6400000 * (t N ^ 6 * Real.exp (-t N)) ≤ 1 := by
    have hlim := hdecay.const_mul 6400000
    have hnorm : ∀ᶠ N : ℕ in atTop,
        6400000 * (t N ^ 6 * Real.exp (-t N)) < 1 :=
      (tendsto_order.1 hlim).2 1 (by norm_num)
    filter_upwards [hnorm, eventually_ge_atTop 0] with N hN hN0
    have hnonneg : 0 ≤ 6400000 * (t N ^ 6 * Real.exp (-t N)) := by positivity
    exact hN.le
  filter_upwards [ht.eventually_ge_atTop 10, hsmall,
    eventually_ge_atTop 3] with N ht10 hsmall hN3
  constructor
  · exact ht10
  have htpos : 0 < t N := by linarith
  have hone : 1 + t N ≤ 2 * t N := by linarith
  have hpow : (1 + t N) ^ 6 ≤ 64 * t N ^ 6 := by
    calc
      (1 + t N) ^ 6 ≤ (2 * t N) ^ 6 := pow_le_pow_left₀ (by positivity) hone 6
      _ = 64 * t N ^ 6 := by ring
  have hexp : Real.exp (t N) = Real.log (N : ℝ) := by
    dsimp only [t, scaleT]
    rw [Real.exp_log]
    exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  rw [← hexp]
  apply (div_le_one (Real.exp_pos (t N))).mp
  rw [show (100000 : ℝ) * (1 + t N) ^ 6 / Real.exp (t N) =
      100000 * (1 + t N) ^ 6 * Real.exp (-t N) by
    rw [Real.exp_neg]
    ring]
  calc
    100000 * (1 + t N) ^ 6 * Real.exp (-t N) ≤
        6400000 * (t N ^ 6 * Real.exp (-t N)) := by
      nlinarith [mul_le_mul_of_nonneg_right hpow (Real.exp_pos (-t N)).le]
    _ ≤ 1 := hsmall

structure ScaleFacts (N : ℕ) : Prop where
  t_ge : 10 ≤ scaleT N
  core_bound :
    100000 * (1 + scaleT N) ^ 6 ≤ Real.log (N : ℝ)
  N_pos : 0 < N
  H_two : 2 ≤ scaleH N
  L_pos : 0 < scaleL N
  D_one : 1 ≤ scaleD N
  L_bounds :
    Real.exp (20 * scaleT N) ≤ (scaleL N : ℝ) ∧
      (scaleL N : ℝ) ≤ 2 * Real.exp (20 * scaleT N)
  D_bounds :
    Real.exp (scaleT N ^ 4) ≤ (scaleD N : ℝ) ∧
      (scaleD N : ℝ) ≤ 2 * Real.exp (scaleT N ^ 4)
  R_bounds :
    Real.exp (Real.log (N : ℝ) / (1000 * scaleT N)) ≤ (scaleR N : ℝ) ∧
      (scaleR N : ℝ) ≤
        2 * Real.exp (Real.log (N : ℝ) / (1000 * scaleT N))
  Q_bound :
    (scaleQ N : ℝ) ≤
      40 * Real.exp (2 * scaleT N ^ 4 + 20 * scaleT N)
  W_three : 3 ≤ scaleW N
  W_cast_lower :
    (N : ℝ) / (2 * scaleQ N) ≤ (scaleW N : ℝ)
  W_scale :
    (4 * scaleD N ^ 2 + 1) * scaleW N * scaleL N ≤ N
  logW_lower : Real.log (N : ℝ) / 2 ≤ Real.log (scaleW N : ℝ)
  logW_sharp :
    Real.log (N : ℝ) -
      (7 + 2 * scaleT N ^ 4 + 20 * scaleT N) ≤
        Real.log (scaleW N : ℝ)
  separation :
    scaleL N < scaleR N ∧ scaleD N < scaleR N ∧
      8 * scaleD N ^ 2 ≤ scaleR N
  secondary_scale : secondaryT (scaleH N) ^ 3 ≤ scaleL N
  logR_upper :
    Real.log (scaleR N : ℝ) ≤
      Real.log (N : ℝ) / (500 * scaleT N)
  pair_log_lower :
    Real.log (N : ℝ) / (2000 * scaleT N) ≤
      Real.log (scalePairY N : ℝ)
  triple_log_lower :
    Real.log (N : ℝ) / (2000 * scaleT N) ≤
      Real.log (scaleTripleY N : ℝ)
  tripleY_cast_lower :
    Real.exp (Real.log (N : ℝ) / (2000 * scaleT N)) ≤
      (scaleTripleY N : ℝ)
  pairY_three : 3 ≤ scalePairY N
  tripleY_three : 3 ≤ scaleTripleY N

lemma nat_div_three_of_exp_bound {N Q : ℕ} {h : ℝ}
    (hQ : 0 < Q) (hexph : Real.exp h = (N : ℝ))
    (hNQexp : (2 : ℝ) * Q ≤ Real.exp (h / 2))
    (h6 : (6 : ℝ) ≤ Real.exp (h / 2)) :
    3 ≤ N / Q := by
  have hcast : (N : ℝ) / (2 * Q) ≤ (N / Q : ℕ) := by
    have hratio : (2 : ℝ) ≤ (N : ℝ) / Q := by
      apply (le_div_iff₀ (by exact_mod_cast hQ)).2
      calc
        (2 : ℝ) * Q ≤ Real.exp (h / 2) := hNQexp
        _ ≤ Real.exp h := Real.exp_le_exp.mpr (by
          have he : Real.exp 0 ≤ Real.exp (h / 2) := by
            rw [Real.exp_zero]
            linarith
          have := Real.exp_le_exp.mp he
          linarith)
        _ = N := hexph
    exact natCast_div_half_lower hQ hratio
  have hhuge : (3 : ℝ) ≤ (N : ℝ) / (2 * Q) := by
    calc
      (3 : ℝ) ≤ Real.exp (h / 2) / 2 := by linarith
      _ ≤ Real.exp (h / 2) := by nlinarith [Real.exp_pos (h / 2)]
      _ = Real.exp h / Real.exp (h / 2) := by
        apply (eq_div_iff (Real.exp_ne_zero _)).2
        rw [← Real.exp_add]
        congr 1 <;> ring
      _ ≤ Real.exp h / (2 * Q) :=
        div_le_div_of_nonneg_left (Real.exp_pos h).le (by positivity) hNQexp
      _ = (N : ℝ) / (2 * Q) := by rw [hexph]
  exact_mod_cast hhuge.trans hcast

structure ScalePolynomialFacts (N : ℕ) : Prop where
  N_pos : 0 < N
  h_pos : 0 < Real.log (N : ℝ)
  h_ge_two : (2 : ℝ) ≤ Real.log (N : ℝ)
  B_small :
    7 + 2 * scaleT N ^ 4 + 20 * scaleT N ≤ Real.log (N : ℝ) / 2
  ratio_large :
    40 * scaleT N + 3 ≤ Real.log (N : ℝ) / (2000 * scaleT N)
  ratio_D :
    2 * scaleT N ^ 4 + 5 ≤ Real.log (N : ℝ) / (1000 * scaleT N)

lemma scalePolynomialFacts_of_core {N : ℕ}
    (hcore : 10 ≤ scaleT N ∧
      100000 * (1 + scaleT N) ^ 6 ≤ Real.log (N : ℝ)) :
    ScalePolynomialFacts N := by
  let t := scaleT N
  let h := Real.log (N : ℝ)
  have ht : 10 ≤ t := hcore.1
  have ht0 : 0 ≤ t := by linarith
  have hdom : 100000 * (1 + t) ^ 6 ≤ h := hcore.2
  have hpos : 0 < h := lt_of_lt_of_le (by positivity) hdom
  have htpow : t ^ 6 ≤ (1 + t) ^ 6 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 6
  have ht4pow : t ^ 4 ≤ (1 + t) ^ 6 := by
    calc
      t ^ 4 ≤ (1 + t) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
      _ ≤ (1 + t) ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have htlin : t ≤ (1 + t) ^ 6 := by
    calc
      t ≤ 1 + t := by linarith
      _ = (1 + t) ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ (1 + t) ^ (6 : ℕ) := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hone : (1 : ℝ) ≤ (1 + t) ^ 6 := by
    simpa using (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + t)
      (show 0 ≤ 6 by omega))
  have hBsmall : 7 + 2 * t ^ 4 + 20 * t ≤ h / 2 := by
    have hpoly : 2 * t ^ 4 + 20 * t + 7 ≤ 29 * (1 + t) ^ 6 := by
      nlinarith [ht4pow, htlin, hone]
    nlinarith
  have htwo : (2 : ℝ) ≤ h := by nlinarith [hdom, hone]
  have hh : 100000 * t ^ 6 ≤ h := hdom.trans' (by nlinarith [htpow])
  have hratioLarge : 40 * t + 3 ≤ h / (2000 * t) := by
    apply (le_div_iff₀ (by positivity : 0 < 2000 * t)).2
    have ht6ge : t ^ 2 ≤ t ^ 6 :=
      pow_le_pow_right₀ (by linarith) (by norm_num)
    have haux : (2000 * t) * (40 * t + 3) ≤ 100000 * t ^ 6 := by
      nlinarith [ht6ge]
    simpa [mul_comm] using haux.trans hh
  have hratioD : 2 * t ^ 4 + 5 ≤ h / (1000 * t) := by
    apply (le_div_iff₀ (by positivity : 0 < 1000 * t)).2
    have ht5 : t ^ 5 ≤ t ^ 6 :=
      pow_le_pow_right₀ (by linarith) (by norm_num)
    have haux : (1000 * t) * (2 * t ^ 4 + 5) ≤ 100000 * t ^ 6 := by
      nlinarith
    simpa [mul_comm] using haux.trans hh
  refine ⟨?_, hpos, by simpa [h] using htwo, ?_, ?_, ?_⟩
  · have hN1R : (1 : ℝ) < N :=
      (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ N)).mp (by simpa [h] using hpos)
    exact_mod_cast (show (0 : ℕ) < N by exact_mod_cast hN1R.le)
  · simpa [t, h] using hBsmall
  · simpa [t, h] using hratioLarge
  · simpa [t, h] using hratioD

structure ScaleCeilingFacts (N : ℕ) : Prop where
  L_pos : 0 < scaleL N
  D_pos : 0 < scaleD N
  Q_pos : 0 < scaleQ N
  L_bounds : Real.exp (20 * scaleT N) ≤ (scaleL N : ℝ) ∧
    (scaleL N : ℝ) ≤ 2 * Real.exp (20 * scaleT N)
  D_bounds : Real.exp (scaleT N ^ 4) ≤ (scaleD N : ℝ) ∧
    (scaleD N : ℝ) ≤ 2 * Real.exp (scaleT N ^ 4)
  R_bounds :
    Real.exp (Real.log (N : ℝ) / (1000 * scaleT N)) ≤ (scaleR N : ℝ) ∧
    (scaleR N : ℝ) ≤
      2 * Real.exp (Real.log (N : ℝ) / (1000 * scaleT N))
  Q_bound : (scaleQ N : ℝ) ≤
    40 * Real.exp (2 * scaleT N ^ 4 + 20 * scaleT N)

lemma scaleCeilingFacts_of_core {N : ℕ}
    (hcore : 10 ≤ scaleT N ∧
      100000 * (1 + scaleT N) ^ 6 ≤ Real.log (N : ℝ)) :
    ScaleCeilingFacts N := by
  let t := scaleT N
  let h := Real.log (N : ℝ)
  have ht : 10 ≤ t := hcore.1
  have hpos : 0 < h := lt_of_lt_of_le (by positivity) hcore.2
  have hLlow : Real.exp (20 * t) ≤ (scaleL N : ℝ) := Nat.le_ceil _
  have hLup : (scaleL N : ℝ) ≤ 2 * Real.exp (20 * t) := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ Real.exp (20 * t) by positivity)
    have he : 1 ≤ Real.exp (20 * t) := Real.one_le_exp (by positivity)
    exact hc.le.trans (by linarith)
  have hDlow : Real.exp (t ^ 4) ≤ (scaleD N : ℝ) := Nat.le_ceil _
  have hDup : (scaleD N : ℝ) ≤ 2 * Real.exp (t ^ 4) := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ Real.exp (t ^ 4) by positivity)
    have he : 1 ≤ Real.exp (t ^ 4) := Real.one_le_exp (by positivity)
    exact hc.le.trans (by linarith)
  have hLpos : 0 < scaleL N := by
    exact_mod_cast (Real.exp_pos (20 * t)).trans_le hLlow
  have hDpos : 0 < scaleD N := by
    exact_mod_cast (Real.exp_pos (t ^ 4)).trans_le hDlow
  let r := h / (1000 * t)
  have hrpos : 0 < r := by positivity
  have hRlow : Real.exp r ≤ (scaleR N : ℝ) := Nat.le_ceil _
  have hRup : (scaleR N : ℝ) ≤ 2 * Real.exp r := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ Real.exp r by positivity)
    have he : 1 ≤ Real.exp r := Real.one_le_exp hrpos.le
    exact hc.le.trans (by linarith)
  have hDsq : (scaleD N : ℝ) ^ 2 ≤ 4 * Real.exp (2 * t ^ 4) := by
    calc
      (scaleD N : ℝ) ^ 2 ≤ (2 * Real.exp (t ^ 4)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hDup 2
      _ = 4 * Real.exp (2 * t ^ 4) := by
        rw [show (2 : ℝ) * t ^ 4 = t ^ 4 + t ^ 4 by ring, Real.exp_add]
        ring
  have hQpos : 0 < scaleQ N := by
    unfold scaleQ
    exact Nat.mul_pos (by positivity) hLpos
  have hQbound : (scaleQ N : ℝ) ≤
      40 * Real.exp (2 * t ^ 4 + 20 * t) := by
    unfold scaleQ
    push_cast
    have he4 : 1 ≤ Real.exp (2 * t ^ 4) := Real.one_le_exp (by positivity)
    have hfactor : 4 * (scaleD N : ℝ) ^ 2 + 1 ≤
        16 * Real.exp (2 * t ^ 4) + 1 := by nlinarith [hDsq]
    calc
      (4 * (scaleD N : ℝ) ^ 2 + 1) * scaleL N ≤
          (16 * Real.exp (2 * t ^ 4) + 1) *
            (2 * Real.exp (20 * t)) :=
        mul_le_mul hfactor hLup (by positivity) (by positivity)
      _ ≤ (20 * Real.exp (2 * t ^ 4)) *
            (2 * Real.exp (20 * t)) := by gcongr <;> nlinarith
      _ = 40 * Real.exp (2 * t ^ 4 + 20 * t) := by
        rw [Real.exp_add]
        ring
  exact
    { L_pos := hLpos
      D_pos := hDpos
      Q_pos := hQpos
      L_bounds := by simpa [t] using And.intro hLlow hLup
      D_bounds := by simpa [t] using And.intro hDlow hDup
      R_bounds := by simpa [r, h, t] using And.intro hRlow hRup
      Q_bound := by simpa [t] using hQbound }

lemma triple_cutoff_data {N : ℕ} {h t : ℝ}
    (hh : 0 < h) (ht : 0 < t) (hL : 0 < scaleL N)
    (hratio : 2 * Real.exp (h / (2000 * t)) ≤
      (scaleR N : ℝ) / (scaleL N : ℝ) ^ 2)
    (hratioLarge : 40 * t + 3 ≤ h / (2000 * t))
    (hexp3 : (8 : ℝ) ≤ Real.exp 3) :
    Real.exp (h / (2000 * t)) ≤ (scaleTripleY N : ℝ) ∧
    h / (2000 * t) ≤ Real.log (scaleTripleY N : ℝ) ∧
    3 ≤ scaleTripleY N := by
  have hcast : Real.exp (h / (2000 * t)) ≤
      (scaleTripleY N : ℝ) := by
    have hLnat : 0 < scaleL N ^ 2 := pow_pos hL 2
    have hdiv := natCast_div_lower (a := scaleR N) hLnat
    unfold scaleTripleY
    have htarget : 1 ≤ Real.exp (h / (2000 * t)) :=
      Real.one_le_exp (by positivity)
    have hratio' : 2 * Real.exp (h / (2000 * t)) ≤
        (scaleR N : ℝ) / (scaleL N ^ 2 : ℕ) := by
      simpa only [Nat.cast_pow] using hratio
    linarith
  have hlog : h / (2000 * t) ≤ Real.log (scaleTripleY N : ℝ) := by
    calc
      h / (2000 * t) = Real.log (Real.exp (h / (2000 * t))) := by
        rw [Real.log_exp]
      _ ≤ Real.log (scaleTripleY N : ℝ) :=
        Real.log_le_log (Real.exp_pos _) hcast
  have hthree : 3 ≤ scaleTripleY N := by
    have hthreeR : (3 : ℝ) ≤ Real.exp (h / (2000 * t)) := by
      calc
        (3 : ℝ) ≤ Real.exp 3 := by nlinarith [hexp3]
        _ ≤ Real.exp (h / (2000 * t)) := Real.exp_le_exp.mpr (by
          nlinarith [hratioLarge])
    exact_mod_cast hthreeR.trans hcast
  exact ⟨hcast, hlog, hthree⟩

lemma eight_scaleD_sq_le_scaleR {N : ℕ} {t r : ℝ}
    (hDup : (scaleD N : ℝ) ≤ 2 * Real.exp (t ^ 4))
    (hratioD : 2 * t ^ 4 + 5 ≤ r)
    (hRlow : Real.exp r ≤ (scaleR N : ℝ)) :
    8 * scaleD N ^ 2 ≤ scaleR N := by
  have hDsq : (scaleD N : ℝ) ^ 2 ≤ 4 * Real.exp (2 * t ^ 4) := by
    calc
      (scaleD N : ℝ) ^ 2 ≤ (2 * Real.exp (t ^ 4)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hDup 2
      _ = 4 * Real.exp (2 * t ^ 4) := by
        rw [show (2 : ℝ) * t ^ 4 = t ^ 4 + t ^ 4 by ring, Real.exp_add]
        ring
  have h32 : (32 : ℝ) ≤ Real.exp 5 := by
    calc
      (32 : ℝ) = 2 ^ (5 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (5 : ℕ) := by gcongr; exact Real.exp_one_gt_two.le
      _ = Real.exp 5 := by rw [← Real.exp_nat_mul]; norm_num
  have hreal : ((8 * scaleD N ^ 2 : ℕ) : ℝ) ≤ (scaleR N : ℝ) := by
    push_cast
    calc
      8 * (scaleD N : ℝ) ^ 2 ≤ 32 * Real.exp (2 * t ^ 4) := by nlinarith
      _ ≤ Real.exp 5 * Real.exp (2 * t ^ 4) := by gcongr
      _ = Real.exp (2 * t ^ 4 + 5) := by
        rw [← Real.exp_add]
        congr 1 <;> ring
      _ ≤ Real.exp r := Real.exp_le_exp.mpr hratioD
      _ ≤ scaleR N := hRlow
  exact_mod_cast hreal

lemma secondary_scale_of_bounds {N : ℕ} {h t : ℝ}
    (hh : 0 < h) (ht : 10 ≤ t)
    (hHup : (scaleH N : ℝ) ≤ 2 * h)
    (hexpt : Real.exp t = h)
    (hLlow : Real.exp (20 * t) ≤ (scaleL N : ℝ)) :
    secondaryT (scaleH N) ^ 3 ≤ scaleL N := by
  have hh10 : (2 : ℝ) ^ 18 ≤ h ^ 2 := by
    have he10 : (2 : ℝ) ^ 10 ≤ Real.exp t := by
      calc
        (2 : ℝ) ^ 10 ≤ Real.exp 1 ^ 10 := by gcongr; exact Real.exp_one_gt_two.le
        _ = Real.exp 10 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ Real.exp t := Real.exp_le_exp.mpr ht
    rw [hexpt] at he10
    nlinarith [sq_nonneg ((2 : ℝ) ^ 9),
      mul_self_le_mul_self (by positivity) he10]
  have hreal : ((secondaryT (scaleH N) ^ 3 : ℕ) : ℝ) ≤ scaleL N := by
    simp only [secondaryT, Nat.cast_pow]
    calc
      ((scaleH N : ℝ) ^ 6) ^ 3 = (scaleH N : ℝ) ^ 18 := by ring
      _ ≤ (2 * h) ^ 18 := pow_le_pow_left₀ (by positivity) hHup 18
      _ = 2 ^ 18 * h ^ 18 := by ring
      _ ≤ h ^ 2 * h ^ 18 :=
        mul_le_mul_of_nonneg_right hh10 (pow_nonneg hh.le 18)
      _ = h ^ 20 := by ring
      _ = Real.exp (20 * t) := by
        rw [← hexpt, ← Real.exp_nat_mul]
        norm_num
      _ ≤ scaleL N := hLlow
  exact_mod_cast hreal

lemma log_scaleR_upper_of_bounds {N : ℕ} {h t r : ℝ}
    (ht : 0 < t) (hr : r = h / (1000 * t))
    (hratioD : 2 * t ^ 4 + 5 ≤ h / (1000 * t))
    (hRlow : Real.exp r ≤ (scaleR N : ℝ))
    (hRup : (scaleR N : ℝ) ≤ 2 * Real.exp r) :
    Real.log (scaleR N : ℝ) ≤ h / (500 * t) := by
  have hrpos : 0 < r := by rw [hr]; nlinarith [hratioD, sq_nonneg (t ^ 2)]
  have hRpos : (0 : ℝ) < scaleR N := (Real.exp_pos r).trans_le hRlow
  have hrlog : Real.log (scaleR N : ℝ) ≤ Real.log 2 + r := by
    calc
      Real.log (scaleR N : ℝ) ≤ Real.log (2 * Real.exp r) := by
        exact Real.log_le_log hRpos hRup
      _ = Real.log 2 + r := by
        rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
  have hlog2r : Real.log 2 ≤ r := by
    have hlog2' :=
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have hlog2 : Real.log 2 ≤ 1 := by norm_num at hlog2' ⊢; exact hlog2'
    rw [hr]
    nlinarith [hratioD, sq_nonneg (t ^ 2)]
  rw [hr] at hrlog hlog2r
  rw [show h / (500 * t) = 2 * (h / (1000 * t)) by ring]
  linarith

theorem eventually_scaleFacts : ∀ᶠ N : ℕ in atTop, ScaleFacts N := by
  filter_upwards [eventually_scale_core] with N hcore
  let t := scaleT N
  let h := Real.log (N : ℝ)
  have hp := scalePolynomialFacts_of_core hcore
  have hc := scaleCeilingFacts_of_core hcore
  have ht : 10 ≤ t := hcore.1
  have ht0 : 0 ≤ t := by linarith
  have htpos : 0 < t := by linarith
  have hdom : 100000 * (1 + t) ^ 6 ≤ h := hcore.2
  have hpos : 0 < h := by simpa [h] using hp.h_pos
  have hNpos : 0 < N := hp.N_pos
  have hexph : Real.exp h = (N : ℝ) := by
    rw [Real.exp_log]
    positivity
  have hexpt : Real.exp t = h := by
    dsimp only [t, scaleT, h]
    rw [Real.exp_log hpos]
  have hBsmall : 7 + 2 * t ^ 4 + 20 * t ≤ h / 2 := by
    simpa [t, h] using hp.B_small
  have hratioLarge : 40 * t + 3 ≤ h / (2000 * t) := by
    simpa [t, h] using hp.ratio_large
  have hratioD : 2 * t ^ 4 + 5 ≤ h / (1000 * t) := by
    simpa [t, h] using hp.ratio_D
  have hexp7 : (80 : ℝ) ≤ Real.exp 7 := by
    calc
      (80 : ℝ) ≤ 2 ^ (7 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (7 : ℕ) := by
        gcongr
        exact Real.exp_one_gt_two.le
      _ = Real.exp 7 := by
        rw [← Real.exp_nat_mul]
        norm_num
  have hexp3 : (8 : ℝ) ≤ Real.exp 3 := by
    calc
      (8 : ℝ) = 2 ^ (3 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (3 : ℕ) := by
        gcongr
        exact Real.exp_one_gt_two.le
      _ = Real.exp 3 := by
        rw [← Real.exp_nat_mul]
        norm_num
  have hLlow : Real.exp (20 * t) ≤ (scaleL N : ℝ) := by
    simpa [t] using hc.L_bounds.1
  have hLup : (scaleL N : ℝ) ≤ 2 * Real.exp (20 * t) := by
    simpa [t] using hc.L_bounds.2
  have hDlow : Real.exp (t ^ 4) ≤ (scaleD N : ℝ) := by
    simpa [t] using hc.D_bounds.1
  have hDup : (scaleD N : ℝ) ≤ 2 * Real.exp (t ^ 4) := by
    simpa [t] using hc.D_bounds.2
  have hLnatpos : 0 < scaleL N := hc.L_pos
  have hDnatpos : 0 < scaleD N := hc.D_pos
  have hLsq : (scaleL N : ℝ) ^ 2 ≤ 4 * Real.exp (40 * t) := by
    calc
      (scaleL N : ℝ) ^ 2 ≤ (2 * Real.exp (20 * t)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hLup 2
      _ = 4 * Real.exp (40 * t) := by
        rw [show (40 : ℝ) * t = 20 * t + 20 * t by ring, Real.exp_add]
        ring
  let r := h / (1000 * t)
  have hrpos : 0 < r := by positivity
  have hRlow : Real.exp r ≤ (scaleR N : ℝ) := by
    simpa [r, h, t] using hc.R_bounds.1
  have hRup : (scaleR N : ℝ) ≤ 2 * Real.exp r := by
    simpa [r, h, t] using hc.R_bounds.2
  have hQpos : 0 < scaleQ N := hc.Q_pos
  have hQbound : (scaleQ N : ℝ) ≤
      40 * Real.exp (2 * t ^ 4 + 20 * t) := by simpa [t] using hc.Q_bound
  have hNQexp : (2 : ℝ) * scaleQ N ≤ Real.exp (h / 2) := by
    calc
      (2 : ℝ) * scaleQ N ≤
          80 * Real.exp (2 * t ^ 4 + 20 * t) := by nlinarith [hQbound]
      _ ≤ Real.exp 7 * Real.exp (2 * t ^ 4 + 20 * t) := by gcongr
      _ = Real.exp (7 + 2 * t ^ 4 + 20 * t) := by
        rw [← Real.exp_add]
        congr 1 <;> ring
      _ ≤ Real.exp (h / 2) := Real.exp_le_exp.mpr hBsmall
  have hNQ : (2 : ℝ) ≤ (N : ℝ) / scaleQ N := by
    apply (le_div_iff₀ (by exact_mod_cast hQpos)).2
    calc
      (2 : ℝ) * scaleQ N ≤ Real.exp (h / 2) := hNQexp
      _ ≤ Real.exp h := Real.exp_le_exp.mpr (by linarith [hpos])
      _ = N := hexph
  have hWcast : (N : ℝ) / (2 * scaleQ N) ≤ (scaleW N : ℝ) := by
    exact natCast_div_half_lower hQpos hNQ
  have hWthree : 3 ≤ scaleW N := by
    have h6 : (6 : ℝ) ≤ Real.exp (h / 2) := by
      have hthree : (3 : ℝ) ≤ h / 2 := by
        have ht4nonneg : 0 ≤ t ^ 4 := by positivity
        nlinarith [hBsmall]
      calc
        (6 : ℝ) ≤ Real.exp 3 := by nlinarith [hexp3]
        _ ≤ Real.exp (h / 2) := Real.exp_le_exp.mpr hthree
    simpa [scaleW] using nat_div_three_of_exp_bound hQpos hexph hNQexp h6
  have hlogQ : Real.log (2 * (scaleQ N : ℝ)) ≤
      7 + 2 * t ^ 4 + 20 * t := by
    calc
      Real.log (2 * (scaleQ N : ℝ)) ≤
          Real.log (Real.exp (7 + 2 * t ^ 4 + 20 * t)) := by
        apply Real.log_le_log (by positivity)
        calc
          (2 : ℝ) * scaleQ N ≤ 80 * Real.exp (2 * t ^ 4 + 20 * t) :=
            by nlinarith [hQbound]
          _ ≤ Real.exp 7 * Real.exp (2 * t ^ 4 + 20 * t) := by gcongr
          _ = Real.exp (7 + 2 * t ^ 4 + 20 * t) := by
            rw [← Real.exp_add]
            congr 1 <;> ring
      _ = 7 + 2 * t ^ 4 + 20 * t := Real.log_exp _
  have hlogW : h / 2 ≤ Real.log (scaleW N : ℝ) := by
    have hWposR : (0 : ℝ) < scaleW N := by exact_mod_cast (by omega : 0 < scaleW N)
    calc
      h / 2 ≤ h - Real.log (2 * (scaleQ N : ℝ)) := by linarith
      _ = Real.log ((N : ℝ) / (2 * scaleQ N)) := by
        rw [Real.log_div (by positivity : (N : ℝ) ≠ 0) (by positivity)]
      _ ≤ Real.log (scaleW N : ℝ) := by
        apply Real.log_le_log
        · positivity
        · exact hWcast
  have hlogWsharp : h - (7 + 2 * t ^ 4 + 20 * t) ≤
      Real.log (scaleW N : ℝ) := by
    calc
      h - (7 + 2 * t ^ 4 + 20 * t) ≤
          h - Real.log (2 * (scaleQ N : ℝ)) := by linarith
      _ = Real.log ((N : ℝ) / (2 * scaleQ N)) := by
        rw [Real.log_div (by positivity : (N : ℝ) ≠ 0) (by positivity)]
      _ ≤ Real.log (scaleW N : ℝ) := Real.log_le_log (by positivity) hWcast
  have hratioTriple :
      2 * Real.exp (h / (2000 * t)) ≤
        (scaleR N : ℝ) / (scaleL N : ℝ) ^ 2 := by
    have hdenpos : 0 < (scaleL N : ℝ) ^ 2 := by exact_mod_cast pow_pos hLnatpos 2
    apply (le_div_iff₀ hdenpos).2
    calc
      2 * Real.exp (h / (2000 * t)) * (scaleL N : ℝ) ^ 2 ≤
          8 * Real.exp (h / (2000 * t) + 40 * t) := by
        rw [Real.exp_add]
        calc
          2 * Real.exp (h / (2000 * t)) * (scaleL N : ℝ) ^ 2 ≤
              2 * Real.exp (h / (2000 * t)) *
                (4 * Real.exp (40 * t)) :=
            mul_le_mul_of_nonneg_left hLsq (by positivity)
          _ = 8 * (Real.exp (h / (2000 * t)) * Real.exp (40 * t)) := by ring
      _ ≤ Real.exp (h / (1000 * t)) := by
        calc
          8 * Real.exp (h / (2000 * t) + 40 * t) ≤
              Real.exp 3 * Real.exp (h / (2000 * t) + 40 * t) := by gcongr
          _ = Real.exp (3 + h / (2000 * t) + 40 * t) := by
            rw [← Real.exp_add]
            congr 1 <;> ring
          _ ≤ Real.exp (h / (1000 * t)) := by
            apply Real.exp_le_exp.mpr
            have := hratioLarge
            ring_nf at this ⊢
            linarith
      _ ≤ scaleR N := hRlow
  obtain ⟨htripleCast, htripleLog, htripleThree⟩ :=
    triple_cutoff_data hpos htpos hLnatpos hratioTriple hratioLarge hexp3
  have hLone : 1 ≤ scaleL N := hLnatpos
  have hYmono : scaleTripleY N ≤ scalePairY N := by
    unfold scaleTripleY scalePairY
    have hLL : scaleL N ≤ scaleL N ^ 2 := by nlinarith [hLnatpos]
    exact Nat.div_le_div_left hLL hLnatpos
  have hpairLog : h / (2000 * t) ≤ Real.log (scalePairY N : ℝ) := by
    apply htripleLog.trans
    apply Real.log_le_log
    · exact_mod_cast (by omega : 0 < scaleTripleY N)
    · exact_mod_cast hYmono
  have hpairThree : 3 ≤ scalePairY N := htripleThree.trans hYmono
  have h8D : 8 * scaleD N ^ 2 ≤ scaleR N :=
    eight_scaleD_sq_le_scaleR hDup (by simpa [r] using hratioD) hRlow
  have hDR : scaleD N < scaleR N := by
    have hDone : 1 ≤ scaleD N := hDnatpos
    nlinarith
  have hLR : scaleL N < scaleR N := by
    have hdivPos : 0 < scaleTripleY N := by omega
    have hmul : scaleTripleY N * scaleL N ^ 2 ≤ scaleR N := by
      simpa [scaleTripleY] using
        (Nat.div_mul_le_self (scaleR N) (scaleL N ^ 2))
    have hLsq : scaleL N < scaleL N ^ 2 * scaleTripleY N := by
      nlinarith [hLnatpos]
    exact hLsq.trans_le (by simpa [mul_comm] using hmul)
  have hh2 : (2 : ℝ) ≤ h := by simpa [h] using hp.h_ge_two
  have hHup : (scaleH N : ℝ) ≤ 2 * h := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ h by linarith)
    exact hc.le.trans (by linarith [hh2])
  have hHtwo : 2 ≤ scaleH N := by
    exact_mod_cast hh2.trans (Nat.le_ceil h)
  have hsecondary : secondaryT (scaleH N) ^ 3 ≤ scaleL N :=
    secondary_scale_of_bounds hpos ht hHup hexpt hLlow
  have hlogR : Real.log (scaleR N : ℝ) ≤ h / (500 * t) :=
    log_scaleR_upper_of_bounds htpos (by rfl) hratioD hRlow hRup
  refine
    { t_ge := ht
      core_bound := by simpa [t, h] using hdom
      N_pos := hNpos
      H_two := hHtwo
      L_pos := hLnatpos
      D_one := hDnatpos
      L_bounds := ⟨hLlow, hLup⟩
      D_bounds := ⟨hDlow, hDup⟩
      R_bounds := ⟨hRlow, hRup⟩
      Q_bound := hQbound
      W_three := hWthree
      W_cast_lower := hWcast
      W_scale := by
        calc
          (4 * scaleD N ^ 2 + 1) * scaleW N * scaleL N =
              scaleW N * scaleQ N := by unfold scaleQ; ring
          _ = (N / scaleQ N) * scaleQ N := by rfl
          _ ≤ N := Nat.div_mul_le_self _ _
      logW_lower := hlogW
      logW_sharp := hlogWsharp
      separation := ⟨hLR, hDR, h8D⟩
      secondary_scale := hsecondary
      logR_upper := hlogR
      pair_log_lower := hpairLog
      triple_log_lower := htripleLog
      tripleY_cast_lower := htripleCast
      pairY_three := hpairThree
      tripleY_three := htripleThree }

#print axioms eventually_scaleFacts

end

end Erdos49
