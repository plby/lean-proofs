import Arxiv.Arxiv2411_18291.NibbleComparisonParameters

/-! # Additional scalar conditions for clique-count critical intervals -/

namespace Arxiv2411_18291

structure NibbleCountConditions (k : ℕ) (a g D p₀ L : ℝ) : Prop where
  variance_bound : 128 * a ≤ (k : ℝ) * p₀ ^ (k - 2)
  step_bound : 1 ≤ a ^ 3 * g
  overlap_bound : L ≤ a ^ 3 * D

theorem nibbleCliqueError_ge_twice_width {k : ℕ} (hk : 0 < k) {a g D p : ℝ}
    (ha : 0 ≤ a) (hg : 0 ≤ g) (hD : 0 ≤ D) (hp : 0 < p) (hp1 : p ≤ 1) :
    2 * (a ^ 3 * D * g) ≤ nibbleCliqueError k a g D p := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hc : (2 : ℝ) ≤ 16 * (k : ℝ) ^ 2 := by nlinarith only [hk']
  have hw : 0 ≤ a ^ 3 * D * g := by positivity
  have hp2 : p ^ 2 ≤ 1 := pow_le_one₀ hp.le hp1
  have heq : nibbleCliqueError k a g D p = 16 * (k : ℝ) ^ 2 * (a ^ 3 * D * g) / p ^ 2 := by
    unfold nibbleCliqueError
    ring
  rw [heq]
  apply (le_div_iff₀ (pow_pos hp 2)).mpr
  have h₁ := mul_le_mul_of_nonneg_left hp2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hw)
  have h₂ := mul_le_mul_of_nonneg_right hc hw
  nlinarith only [h₁, h₂]

namespace NibbleCountConditions

variable {k : ℕ} {a g D p₀ L : ℝ}
variable (P : NibbleComparisonParameters k a g D p₀ L) (Q : NibbleCountConditions k a g D p₀ L)

include P Q

theorem variance_at {p : ℝ} (hp : p₀ ≤ p) : 128 * a ≤ (k : ℝ) * p ^ (k - 2) :=
  Q.variance_bound.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ P.floor_pos.le hp (k - 2)) (Nat.cast_nonneg _))

theorem overlap_margin {p : ℝ} (hp : p₀ ≤ p) (hp1 : p ≤ 1) :
    (p * g) * L ≤ nibbleCliqueError k a g D p - a ^ 3 * D * g := by
  have hk : 0 < k := by have h := P.rank; omega
  have hp0 := P.floor_pos.trans_le hp
  have hv := nibbleCliqueError_ge_twice_width hk P.error_pos.le P.graph_pos.le
    P.degree_pos.le hp0 hp1
  have hw : 0 ≤ a ^ 3 * D * g :=
    mul_nonneg (mul_nonneg (pow_nonneg P.error_pos.le _) P.degree_pos.le) P.graph_pos.le
  have hEL : (p * g) * L ≤ a ^ 3 * D * g := by
    calc
      _ ≤ (p * g) * (a ^ 3 * D) :=
        mul_le_mul_of_nonneg_left Q.overlap_bound (mul_nonneg hp0.le P.graph_pos.le)
      _ = p * (a ^ 3 * D * g) := by ring
      _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hp1 hw
  linarith only [hv, hEL]

theorem variance_margin {p : ℝ} (hp : p₀ ≤ p) (hp1 : p ≤ 1) :
    2 * (p * g) ^ 2 * nibbleDegreeError k a D p ^ 2 ≤
      (k : ℝ) ^ 2 * (nibbleCliqueError k a g D p - a ^ 3 * D * g) *
        nibbleCliqueMain k g D p := by
  have hk : 0 < k := by have h := P.rank; omega
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hp0 := P.floor_pos.trans_le hp
  have hvar := Q.variance_at P hp
  have h64 : 64 * a ≤ (k : ℝ) * p ^ (k - 2) := by
    have ha := P.error_pos
    linarith only [hvar, ha]
  let F := 16 * (k : ℝ) ^ 2 * a ^ 3 * D ^ 2 * g ^ 2
  have hF : 0 ≤ F := by
    have ha := P.error_pos
    dsimp only [F]
    positivity
  have hmul := mul_le_mul_of_nonneg_left h64 hF
  have hexp : k - 2 + 2 = k := by have h := P.rank; omega
  have hpow : p ^ k = p ^ (k - 2) * p ^ 2 := by rw [← pow_add, hexp]
  have hleft : 4 * (p * g) ^ 2 * nibbleDegreeError k a D p ^ 2 = F * (64 * a) := by
    unfold nibbleDegreeError nibbleEdgeScale
    dsimp only [F]
    field_simp
    ring
  have hright : (k : ℝ) ^ 2 * nibbleCliqueError k a g D p * nibbleCliqueMain k g D p =
      F * ((k : ℝ) * p ^ (k - 2)) := by
    unfold nibbleCliqueError nibbleCliqueMain
    rw [hpow]
    dsimp only [F]
    field_simp
  have hfour : 4 * (p * g) ^ 2 * nibbleDegreeError k a D p ^ 2 ≤
      (k : ℝ) ^ 2 * nibbleCliqueError k a g D p * nibbleCliqueMain k g D p := by
    rw [hleft, hright]
    exact hmul
  have hv := nibbleCliqueError_ge_twice_width hk P.error_pos.le P.graph_pos.le
    P.degree_pos.le hp0 hp1
  have hvprod := mul_le_mul_of_nonneg_right hv
    (mul_nonneg (sq_nonneg (k : ℝ)) (nibbleCliqueMain_pos hk P.graph_pos P.degree_pos hp0).le)
  nlinarith only [hfour, hvprod]

end NibbleCountConditions

end Arxiv2411_18291
