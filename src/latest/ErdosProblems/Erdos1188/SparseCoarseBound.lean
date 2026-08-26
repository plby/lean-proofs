import ErdosProblems.Erdos1188.SparseFinalEstimate

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A simpler coarse exponent extracted from the sparse all-cutoff bound
-/

namespace Erdos1188

/-- A denominator convenient for stating the sparse lower exponent without
nested integer square roots or binomial coefficients. -/
def sparseCoarseDenominator (D x : ℕ) : ℕ :=
  2048 * D * (Nat.log 2 (x + 1) + 1) ^ 4

/-- Once the interpolation quotient is nontrivial, its binomial exponent
absorbs `x` divided by a fixed constant and four binary logarithms. -/
theorem sparse_coarseExponent_le_choose (D x : ℕ) (hD : 0 < D)
    (hq : 8 ≤ sparseAllCutoffQuotient D x) :
    x / sparseCoarseDenominator D x ≤
      (sparseAllCutoffQuotient D x / 2).choose 2 := by
  let R := Nat.log 2 (x + 1) + 1
  let y := x / D
  let t := Nat.sqrt y
  let q := sparseAllCutoffQuotient D x
  let n := q / 2
  let e := n.choose 2
  have hR : 0 < R := by simp [R]
  have hR2 : 0 < R ^ 2 := pow_pos hR _
  have hqdef : q = t / R ^ 2 := by rfl
  have hndef : n = q / 2 := by rfl
  have hedef : e = n.choose 2 := by rfl
  have hqt : q * R ^ 2 ≤ t := by
    rw [hqdef]
    exact Nat.div_mul_le_self _ _
  have htpos : 0 < t := by
    have hqpos : 0 < q := by omega
    nlinarith
  have htupper : t < (q + 1) * R ^ 2 := by
    have hm := Nat.mod_lt t hR2
    have heq := Nat.div_add_mod t (R ^ 2)
    rw [← hqdef] at heq
    nlinarith
  have htq : t ≤ 2 * q * R ^ 2 := by
    have hqone : q + 1 ≤ 2 * q := by omega
    exact (Nat.le_of_lt htupper).trans (Nat.mul_le_mul_right (R ^ 2) hqone)
  have hypos : 0 < y := by
    have hyt := Nat.sqrt_le y
    nlinarith
  have hysq : y ≤ 4 * t ^ 2 := by
    have hylt := Nat.lt_succ_sqrt' y
    have htone : t + 1 ≤ 2 * t := by omega
    have hs : (t + 1) ^ 2 ≤ (2 * t) ^ 2 := Nat.pow_le_pow_left htone 2
    nlinarith
  have hxdiv : x < D * (y + 1) := by
    have hm := Nat.mod_lt x hD
    have heq := Nat.div_add_mod x D
    change D * y + x % D = x at heq
    nlinarith
  have hxy : x ≤ 2 * D * y := by
    have hyone : y + 1 ≤ 2 * y := by omega
    have htmp : D * (y + 1) ≤ 2 * D * y := by nlinarith
    exact (Nat.le_of_lt hxdiv).trans htmp
  have hxq : x ≤ 32 * D * R ^ 4 * q ^ 2 := by
    have htq2 : t ^ 2 ≤ (2 * q * R ^ 2) ^ 2 := Nat.pow_le_pow_left htq 2
    calc
      x ≤ 2 * D * y := hxy
      _ ≤ 2 * D * (4 * t ^ 2) := Nat.mul_le_mul_left (2 * D) hysq
      _ ≤ 2 * D * (4 * (2 * q * R ^ 2) ^ 2) := by gcongr
      _ = 32 * D * R ^ 4 * q ^ 2 := by ring
  have hn : 4 ≤ n := by
    rw [hndef]
    omega
  have hqn : q ≤ 3 * n := by
    have hdiv := Nat.div_add_mod q 2
    have hmod := Nat.mod_lt q (by decide : 0 < 2)
    rw [← hndef] at hdiv
    omega
  have heq : 2 * e = n * (n - 1) := by
    rw [hedef, Nat.choose_two_right]
    have heven : 2 ∣ n * (n - 1) := (Nat.even_mul_pred_self n).two_dvd
    omega
  have hnchoose : n ^ 2 ≤ 4 * e := by
    have hnlin : n ≤ 2 * (n - 1) := by omega
    nlinarith
  have hqchoose : q ^ 2 ≤ 36 * e := by
    have hs : q ^ 2 ≤ (3 * n) ^ 2 := Nat.pow_le_pow_left hqn 2
    nlinarith
  have hxchoose : x ≤ sparseCoarseDenominator D x * e := by
    unfold sparseCoarseDenominator
    change x ≤ 2048 * D * R ^ 4 * e
    calc
      x ≤ 32 * D * R ^ 4 * q ^ 2 := hxq
      _ ≤ 32 * D * R ^ 4 * (36 * e) := Nat.mul_le_mul_left _ hqchoose
      _ ≤ 2048 * D * R ^ 4 * e := by nlinarith
  have hden : 0 < sparseCoarseDenominator D x := by
    unfold sparseCoarseDenominator
    positivity
  change x / sparseCoarseDenominator D x ≤ e
  exact Nat.div_le_of_le_mul hxchoose

/-- A pointwise power-of-two lower bound with exponent
`x / (2048 D (log₂(x+1)+1)^4)`. -/
theorem explicit_sparse_coarse_lower (D x : ℕ)
    (hD : sparseSeedProduct * (256 ^ 3 * 2048 * 2049) ≤ D)
    (hq : 2 * (sparseSeed + 1) ≤ sparseAllCutoffQuotient D x) :
    2 ^ (x / sparseCoarseDenominator D x) ≤ coveringCount x := by
  have hDpos : 0 < D := by
    have hc : 0 < sparseSeedProduct * (256 ^ 3 * 2048 * 2049) :=
      Nat.mul_pos sparseSeedProduct_pos (by norm_num)
    omega
  have hseed8 : 8 ≤ 2 * (sparseSeed + 1) := by
    unfold sparseSeed
    norm_num
  have hq8 : 8 ≤ sparseAllCutoffQuotient D x := hseed8.trans hq
  exact (Nat.pow_le_pow_right (by decide)
      (sparse_coarseExponent_le_choose D x hDpos hq8)).trans
    (explicit_sparse_quotient_lower D x hD hq)

end Erdos1188
