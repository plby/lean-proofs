import Arxiv.Arxiv2411_18291.LogNibbleParameters

/-! # Face drift and average loss with the logarithmic route's constant error -/

noncomputable section

namespace Arxiv2411_18291

def logNibbleFaceUpper (a n F p : ℝ) : ℝ := p * F + 2 * a * n

def logNibbleFaceUpperComparison (k : ℕ) (a g n F : ℝ) (i : ℕ) : ℝ :=
  logNibbleFaceUpper a n F (removalDensity k g i)

theorem logNibbleFaceUpperComparison_increment (k : ℕ) (a g n F : ℝ) (i : ℕ) :
    logNibbleFaceUpperComparison k a g n F (i + 1) -
      logNibbleFaceUpperComparison k a g n F i = -(k : ℝ) * F / g := by
  simp only [logNibbleFaceUpperComparison, logNibbleFaceUpper, removalDensity_succ]
  ring

theorem logNibbleFaceUpper_le_density {a n F p : ℝ}
    (hn : 0 ≤ n) (hp : 0 ≤ p) (hFn : F ≤ n) (hap : a ≤ p) :
    logNibbleFaceUpper a n F p ≤ 3 * p * n := by
  have hF := mul_le_mul_of_nonneg_left hFn hp
  have ha := mul_le_mul_of_nonneg_right hap hn
  unfold logNibbleFaceUpper
  nlinarith only [hF, ha]

theorem LogNibbleParameters.face_upper_drift {k : ℕ} {a g D p₀ L : ℝ}
    (P : LogNibbleParameters k a g D p₀ L) {p n F d h : ℝ}
    (hp : p₀ ≤ p) (hp1 : p ≤ 1) (hn : 0 ≤ n) (hF : 0 ≤ F) (hFn : F ≤ n)
    (hdn : d ≤ n)
    (hh : |h - nibbleCliqueMain k g D p| ≤ logNibbleCliqueError k a g D p)
    (hcritical : logNibbleFaceUpper a n F p - a * n ≤ d) :
    -(d * (nibbleDegreeMain k D p - logNibbleDegreeError k a D p) / h) +
      (k : ℝ) * F / g ≤ 0 := by
  have hk : 0 < k := by have h := P.rank; omega
  have hp0 := P.floor_pos.trans_le hp
  have Q := P.point_conditions hp hp1
  have hv := (Q.count_bounds hk P.degree_pos.le P.graph_pos.le hp0.le).1
  have hh₀ := nibbleCliqueMain_pos hk P.graph_pos P.degree_pos hp0
  have hhpos : 0 < h := by
    have hlo := (abs_le.mp hh).1
    linarith only [hlo, hv, hh₀]
  have hcrit : p * F + a * n ≤ d := by
    unfold logNibbleFaceUpper at hcritical
    nlinarith only [hcritical]
  have hyp : p * F ≤ F := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp1 hF
  have hloss := log_nibble_face_loss_lower hk Q P.error_pos.le P.graph_pos P.degree_pos
    hp0 hp1 hhpos hn (mul_nonneg hp0.le hF) (hyp.trans hFn) hdn hcrit hh
  have heq : nibbleDegreeMain k D p / nibbleCliqueMain k g D p * (p * F) =
      (k : ℝ) * F / g := by
    rw [nibbleDegreeMain_clique_ratio hk P.graph_pos.ne' P.degree_pos.ne' hp0.ne']
    field_simp
  rw [heq] at hloss
  linarith only [hloss]

theorem LogNibbleParameters.face_average_loss_le {k : ℕ} {a g D p₀ L : ℝ}
    (P : LogNibbleParameters k a g D p₀ L) {p n F d h : ℝ}
    (hp : p₀ ≤ p) (hp1 : p ≤ 1) (hn : 0 ≤ n) (hFn : F ≤ n) (hd : 0 ≤ d)
    (hhalf : nibbleCliqueMain k g D p / 2 ≤ h)
    (hface : d ≤ logNibbleFaceUpper a n F p) :
    d * (nibbleDegreeMain k D p + logNibbleDegreeError k a D p) / h ≤
      12 * k * n / g := by
  have hk : 0 < k := by have h := P.rank; omega
  have hp0 := P.floor_pos.trans_le hp
  have hm := nibbleDegreeMain_pos (k := k) P.degree_pos hp0
  have hum := ((P.point_conditions hp hp1).degree_bounds P.degree_pos.le).1
  have hh₀ := nibbleCliqueMain_pos hk P.graph_pos P.degree_pos hp0
  have hh : 0 < h := (half_pos hh₀).trans_le hhalf
  let C := 3 * p * n
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hdC : d ≤ C := hface.trans
    (logNibbleFaceUpper_le_density hn hp0.le hFn (P.error_le_floor.trans hp))
  have hdegree : nibbleDegreeMain k D p + logNibbleDegreeError k a D p ≤
      2 * nibbleDegreeMain k D p := by linarith only [hum, hm]
  have hN : d * (nibbleDegreeMain k D p + logNibbleDegreeError k a D p) ≤
      C * (2 * nibbleDegreeMain k D p) :=
    (mul_le_mul_of_nonneg_left hdegree hd).trans
      (mul_le_mul_of_nonneg_right hdC (mul_nonneg (by norm_num) hm.le))
  have hN' := mul_le_mul_of_nonneg_right hN hh₀.le
  have hh' := mul_le_mul_of_nonneg_left hhalf (mul_nonneg hC hm.le)
  calc
    _ ≤ 4 * C * nibbleDegreeMain k D p / nibbleCliqueMain k g D p := by
      apply (div_le_div_iff₀ hh hh₀).mpr
      nlinarith only [hN', hh']
    _ = 4 * C * (nibbleDegreeMain k D p / nibbleCliqueMain k g D p) := by ring
    _ = _ := by
      rw [nibbleDegreeMain_clique_ratio hk P.graph_pos.ne' P.degree_pos.ne' hp0.ne']
      dsimp only [C]
      field_simp
      ring

end Arxiv2411_18291
