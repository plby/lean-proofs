import ErdosProblems.Erdos1188.SparseCutoffPolynomial

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Explicit sparse lower bound at every sufficiently large cutoff
-/

namespace Erdos1188

/-- The pre-subtraction quotient in the all-cutoff interpolation. -/
def sparseAllCutoffQuotient (D x : ℕ) : ℕ :=
  Nat.sqrt (x / D) / (Nat.log 2 (x + 1) + 1) ^ 2

/-- Dimension selected from an arbitrary cutoff, with `D` any fixed
coefficient dominating the construction's seed coefficient. -/
def sparseAllCutoffIndex (D x : ℕ) : ℕ :=
  sparseAllCutoffQuotient D x - 1

/-- By construction, the explicit parametric cutoff at the selected dimension
fits under `x`. -/
theorem sparsePrimeCutoff_selected_le (D x : ℕ)
    (hD : sparseSeedProduct * (256 ^ 3 * 2048 * 2049) ≤ D)
    (hm : sparseSeed ≤ sparseAllCutoffIndex D x) :
    sparsePrimeCutoff (sparseAllCutoffIndex D x) ≤ x := by
  let R := Nat.log 2 (x + 1) + 1
  let t := Nat.sqrt (x / D)
  let q := sparseAllCutoffQuotient D x
  let m := sparseAllCutoffIndex D x
  have hDpos : 0 < D := by
    have hc : 0 < sparseSeedProduct * (256 ^ 3 * 2048 * 2049) :=
      Nat.mul_pos sparseSeedProduct_pos (by norm_num)
    omega
  have hR : 0 < R := by simp [R]
  have hqdef : q = t / R ^ 2 := by rfl
  have hmdef : m = q - 1 := by rfl
  have hqpos : 0 < q := by
    change sparseSeed ≤ m at hm
    rw [hmdef] at hm
    unfold sparseSeed at hm
    omega
  have hm1 : m + 1 = q := by omega
  have hqt : q * R ^ 2 ≤ t := by
    rw [hqdef]
    exact Nat.div_mul_le_self _ _
  have htdiv : t ^ 2 ≤ x / D := by
    simpa [t, pow_two] using Nat.sqrt_le (x / D)
  have hDx : D * (x / D) ≤ x := Nat.mul_div_le x D
  have hqx : q ≤ x := by
    have hqt' : q ≤ t := by
      calc
        q = q * 1 := by omega
        _ ≤ q * R ^ 2 := Nat.mul_le_mul_left q (by nlinarith)
        _ ≤ t := hqt
    exact hqt'.trans ((Nat.sqrt_le_self _).trans (Nat.div_le_self _ _))
  have hmx : m + 1 ≤ x + 1 := by omega
  have hrR : sparseLog m ≤ R := by
    unfold sparseLog R
    exact Nat.add_le_add_right (Nat.log_mono_right hmx) 1
  have ha : (m + 1) * (sparseLog m) ^ 2 ≤ t := by
    calc
      (m + 1) * (sparseLog m) ^ 2 = q * (sparseLog m) ^ 2 := by rw [hm1]
      _ ≤ q * R ^ 2 := Nat.mul_le_mul_left q (Nat.pow_le_pow_left hrR 2)
      _ ≤ t := hqt
  have hsq : ((m + 1) * (sparseLog m) ^ 2) ^ 2 ≤ t ^ 2 :=
    Nat.pow_le_pow_left ha 2
  have hpoly := sparsePrimeCutoff_le_polynomial_log m
  calc
    sparsePrimeCutoff m ≤
        (sparseSeedProduct * (256 ^ 3 * 2048 * 2049)) *
          (m + 1) ^ 2 * (sparseLog m) ^ 4 := hpoly
    _ ≤ D * (m + 1) ^ 2 * (sparseLog m) ^ 4 := by gcongr
    _ = D * (((m + 1) * (sparseLog m) ^ 2) ^ 2) := by ring
    _ ≤ D * t ^ 2 := Nat.mul_le_mul_left D hsq
    _ ≤ D * (x / D) := Nat.mul_le_mul_left D htdiv
    _ ≤ x := hDx

/-- Explicit lower bound for every cutoff whose selected sparse dimension is
large enough. -/
theorem explicit_sparse_all_cutoff_lower (D x : ℕ)
    (hD : sparseSeedProduct * (256 ^ 3 * 2048 * 2049) ≤ D)
    (hm : sparseSeed ≤ sparseAllCutoffIndex D x) :
    2 ^ ((sparseAllCutoffIndex D x - sparseSeed) *
        (sparseAllCutoffIndex D x - sparseSeed - 1) / 2) ≤ coveringCount x := by
  exact (explicit_sparse_quadratic_parametric_lower
      (sparseAllCutoffIndex D x) hm).trans
    (coveringCount_mono (sparsePrimeCutoff_selected_le D x hD hm))

set_option maxRecDepth 100000 in
/-- A simpler direct all-cutoff form: the exponent is quadratic in the
explicit quotient `sqrt(x/D)/(log_2(x+1)+1)^2`. -/
theorem explicit_sparse_quotient_lower (D x : ℕ)
    (hD : sparseSeedProduct * (256 ^ 3 * 2048 * 2049) ≤ D)
    (hq : 2 * (sparseSeed + 1) ≤ sparseAllCutoffQuotient D x) :
    2 ^ ((sparseAllCutoffQuotient D x / 2).choose 2) ≤ coveringCount x := by
  set q := sparseAllCutoffQuotient D x with hqdef
  set m := sparseAllCutoffIndex D x with hmraw
  change 2 * (sparseSeed + 1) ≤ q at hq
  have hqpos : 0 < q := by omega
  have hmdef : m = q - 1 := by
    rw [hmraw, hqdef]
    rfl
  have hseedq : sparseSeed + 1 ≤ q := by
    exact (Nat.le_mul_of_pos_left (sparseSeed + 1) (by decide : 0 < 2)).trans hq
  have hm : sparseSeed ≤ m := by
    rw [hmdef]
    exact Nat.le_sub_of_add_le hseedq
  have hhalf : q / 2 ≤ m - sparseSeed := by
    rw [hmdef, Nat.sub_sub]
    have hseedhalf : sparseSeed + 1 ≤ q / 2 := by
      rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
      simpa [Nat.mul_comm] using hq
    have hdiv : q / 2 * 2 ≤ q := Nat.div_mul_le_self _ _
    apply Nat.le_sub_of_add_le
    calc
      q / 2 + (1 + sparseSeed) ≤ q / 2 + q / 2 := by
        gcongr
        simpa [Nat.add_comm] using hseedhalf
      _ = q / 2 * 2 := by ring
      _ ≤ q := hdiv
  have hchoose : (q / 2).choose 2 ≤ (m - sparseSeed).choose 2 :=
    Nat.choose_le_choose 2 hhalf
  have hparam := explicit_sparse_quadratic_parametric_lower m hm
  rw [← Nat.choose_two_right] at hparam
  have hcut0 := sparsePrimeCutoff_selected_le D x hD (by simpa [hmraw] using hm)
  have hcut : sparsePrimeCutoff m ≤ x := by simpa [hmraw] using hcut0
  exact (Nat.pow_le_pow_right (by decide) hchoose).trans
    (hparam.trans (coveringCount_mono hcut))

end Erdos1188
