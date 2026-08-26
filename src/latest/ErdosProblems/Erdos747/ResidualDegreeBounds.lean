import ErdosProblems.Erdos747.ResidualCountBounds

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Explicit aggregate-degree losses after removing one triple -/

def residualDegreeTolerance (n : ℕ) (B q g : ℝ) : ℝ :=
  2 * q + 6 * g + 12 * (B + 1) / n

lemma residualDegreeTolerance_tendsto_zero
    (B : ℝ) (q g : ℕ → ℝ)
    (hq : Tendsto q atTop (𝓝 0)) (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun n ↦ residualDegreeTolerance n B (q n) (g n)) atTop (𝓝 0) := by
  have hlast : Tendsto (fun n : ℕ ↦ 12 * (B + 1) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  simpa only [residualDegreeTolerance, mul_zero, add_zero] using
    ((hq.const_mul 2).add (hg.const_mul 6)).add hlast

lemma degreeAggregateRegular_reindexGraphAway_explicit
    {n M cap : ℕ} {H : Finset (Edge n)} {Z : Edge n} {B q eta g : ℝ}
    (hn : 2 ≤ n) (hH : H ∈ sample n M) (hZ : Z ∈ allEdges n)
    (hB : 0 ≤ B) (hq : 0 ≤ q) (heta : 0 ≤ eta) (hg : 0 ≤ g)
    (hmean : 1 ≤ (M : ℝ) / n) (hsize : 6 * (B + 1) ≤ n)
    (hcap : (cap : ℝ) / ((M : ℝ) / n) ≤ g)
    (hcodeg : ∀ u v : Vertex n, u ≠ v → vertexCodegree H u v ≤ cap)
    (hreg : DegreeAggregateRegular n M q eta B H)
    (hq' : residualDegreeTolerance n B q g ≤ 1) :
    DegreeAggregateRegular (n - 1) (reindexGraphAway H Z hZ).card
        (residualDegreeTolerance n B q g) (2 * eta) (2 * B) (reindexGraphAway H Z hZ) ∧
      (cap : ℝ) / (((reindexGraphAway H Z hZ).card : ℝ) / ((n - 1 : ℕ) : ℝ)) ≤ 2 * g ∧
      ((M : ℝ) / n) / 2 ≤ ((reindexGraphAway H Z hZ).card : ℝ) / ((n - 1 : ℕ) : ℝ) ∧
      ((reindexGraphAway H Z hZ).card : ℝ) / ((n - 1 : ℕ) : ℝ) ≤
        (1 + 2 / (n : ℝ)) * ((M : ℝ) / n) := by
  let mu : ℝ := (M : ℝ) / n
  let J := reindexGraphAway H Z hZ
  let mu' : ℝ := (J.card : ℝ) / ((n - 1 : ℕ) : ℝ)
  let zeta : ℝ := 3 * (B + 1) / n
  let q' := residualDegreeTolerance n B q g
  let D : ℕ := ⌈B * mu⌉₊
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hk : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
  have hmu : 0 < mu := lt_of_lt_of_le zero_lt_one hmean
  have hmuId : mu * n = M := div_mul_cancel₀ _ hnR.ne'
  have hzeta : 0 ≤ zeta := by dsimp only [zeta]; positivity
  have hzetaHalf : zeta ≤ 1 / 2 := by
    dsimp only [zeta]
    apply (div_le_iff₀ hnR).mpr
    linarith only [hsize]
  have hD : (D : ℝ) ≤ (B + 1) * mu := by
    have hceil : (D : ℝ) < B * mu + 1 := Nat.ceil_lt_add_one (by positivity)
    nlinarith only [hceil, hmean]
  have hdegree : ∀ v : Vertex n, vertexDegree H v ≤ D := by
    intro v
    have h := (hreg.2 v).trans (Nat.le_ceil (B * mu))
    exact_mod_cast h
  have hHcard := (mem_sample.mp hH).2
  have hJnat := card_reindexGraphAway_lower hZ hHcard (fun v hv ↦ hdegree v)
  have hJlower : (M : ℝ) ≤ J.card + 3 * (D : ℝ) := by
    exact_mod_cast (show M ≤ J.card + 3 * D by dsimp only [J]; omega)
  have hJupper : (J.card : ℝ) ≤ M := by
    have hc : J.card ≤ M := by
      rw [show J = reindexGraphAway H Z hZ by rfl, card_reindexGraphAway]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHcard
    exact_mod_cast hc
  have hlower : (1 - zeta) * mu ≤ mu' := by
    have hnum : (1 - zeta) * mu * n ≤ J.card := by
      dsimp only [zeta]
      have heq : (1 - 3 * (B + 1) / (n : ℝ)) * mu * n =
          mu * n - 3 * (B + 1) * mu := by field_simp
      rw [heq]
      nlinarith only [hD, hJlower, hmuId]
    calc
      _ ≤ (J.card : ℝ) / n := (le_div_iff₀ hnR).mpr hnum
      _ ≤ (J.card : ℝ) / ((n - 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hk (by exact_mod_cast Nat.sub_le n 1)
  have hupper : mu' ≤ (1 + 2 / (n : ℝ)) * mu := by
    calc
      _ ≤ (M : ℝ) / ((n - 1 : ℕ) : ℝ) := div_le_div_of_nonneg_right hJupper hk.le
      _ = mu * ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) := by dsimp only [mu]; field_simp
      _ ≤ mu * (1 + 2 / (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hmu.le
        rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
        have hpred : (0 : ℝ) < (n : ℝ) - 1 := by linarith only [hn2]
        apply (div_le_iff₀ hpred).mpr
        apply (mul_le_mul_iff_right₀ hnR).mp
        field_simp [hnR.ne']
        nlinarith only [hn2]
      _ = _ := by ring
  have hhalf : mu / 2 ≤ mu' := by
    nlinarith only [hlower, mul_nonneg (sub_nonneg.mpr hzetaHalf) hmu.le]
  have hmu' : 0 < mu' := (half_pos hmu).trans_le hhalf
  have hqform : q' = 2 * q + 6 * g + 4 * zeta := by
    dsimp only [q', residualDegreeTolerance, zeta]
    ring
  have hq0' : 0 ≤ q' := by rw [hqform]; positivity
  have htwo : 2 / (n : ℝ) ≤ 4 * zeta := by
    dsimp only [zeta]
    have h := div_le_div_of_nonneg_right
      (show (2 : ℝ) ≤ 12 * (B + 1) by linarith only [hB]) hnR.le
    exact h.trans_eq (by ring)
  have hstepLower : q + 3 * g + 2 / (n : ℝ) ≤ q' := by
    linarith only [hqform, hq, hg, htwo]
  have hstepUpper : q + 2 * zeta ≤ q' := by
    linarith only [hqform, hq, hg, hzeta]
  have hcapMu : (cap : ℝ) ≤ g * mu := (div_le_iff₀ hmu).mp hcap
  have hregular : DegreeAggregateRegular (n - 1) J.card q' (2 * eta) (2 * B) J := by
    apply degreeAggregateRegular_reindexGraphAway (n := n) (M := M) (codegCap := cap)
      (H := H) (Z := Z) hZ hHcard q eta B q' (2 * eta) (2 * B) hcodeg hreg
    · have hscalar : (1 - q') * (1 + 2 / (n : ℝ)) ≤ 1 - q - 3 * g := by
        nlinarith only [hstepLower, mul_nonneg hq0' (show 0 ≤ 2 / (n : ℝ) by positivity)]
      have hscaled := mul_le_mul_of_nonneg_right hscalar hmu.le
      have hfirst := mul_le_mul_of_nonneg_left hupper (sub_nonneg.mpr hq')
      change (1 - q') * mu' ≤ (1 - q) * mu - 3 * cap
      nlinarith only [hscaled, hfirst, hcapMu]
    · have hscalar : 1 + q ≤ (1 + q') * (1 - zeta) := by
        nlinarith only [hstepUpper, mul_nonneg (sub_nonneg.mpr hq') hzeta]
      have hscaled := mul_le_mul_of_nonneg_right hscalar hmu.le
      have hlast := mul_le_mul_of_nonneg_left hlower (show 0 ≤ 1 + q' by linarith only [hq0'])
      change (1 + q) * mu ≤ (1 + q') * mu'
      nlinarith only [hscaled, hlast]
    · rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      nlinarith only [mul_nonneg heta (show 0 ≤ (n : ℝ) - 2 by linarith only [hn2])]
    · change B * mu ≤ (2 * B) * mu'
      nlinarith only [mul_le_mul_of_nonneg_left hhalf hB]
  refine ⟨hregular, ?_, hhalf, hupper⟩
  change (cap : ℝ) / mu' ≤ 2 * g
  calc
    _ ≤ (cap : ℝ) / (mu / 2) := div_le_div_of_nonneg_left (by positivity) (half_pos hmu) hhalf
    _ = 2 * ((cap : ℝ) / mu) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcap (by norm_num)

end

end Erdos747
