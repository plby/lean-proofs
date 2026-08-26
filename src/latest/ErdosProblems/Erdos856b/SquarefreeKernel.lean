import ErdosProblems.Erdos856b.Selections
import ErdosProblems.Erdos856b.PrimeBuckets
import ErdosProblems.Erdos856b.EulerBound

/-! # Logarithmic growth of the squarefree harmonic kernel -/

namespace Erdos856b

open Real Filter
open scoped BigOperators Topology

noncomputable def squarefreeKernel (z : ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ (Finset.Icc 1 N).filter Squarefree, omegaWeight z q

theorem squarefreeKernel_le_omegaSum {z : ℝ} (hz : 0 ≤ z) (N : ℕ) :
    squarefreeKernel z N ≤ omegaSum z N :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun q _ _ => omegaWeight_nonneg hz q)

theorem one_le_squarefreeKernel {z : ℝ} (hz : 0 ≤ z) {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ squarefreeKernel z N := by
  have h := Finset.single_le_sum (f := omegaWeight z)
    (s := (Finset.Icc 1 N).filter Squarefree) (fun q _ => omegaWeight_nonneg hz q)
    (by simp [hN] : 1 ∈ (Finset.Icc 1 N).filter Squarefree)
  simpa only [omegaWeight_one, squarefreeKernel] using h

theorem selectionSupport_card {t : ℕ} {P : Fin t → Finset ℕ}
    {F : Finset (Finset (Fin t))} (hdis : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (q : Selections P F) : (selectionSupport q).card = q.1.val.card := by
  rw [selectionSupport, Finset.card_image_of_injective _ (selectedValue_injective hdis q)]
  simp

theorem realization_omegaWeight {t : ℕ} {P : Fin t → Finset ℕ}
    {F : Finset (Finset (Fin t))} (ht : 0 < t)
    (hdis : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hp : ∀ i p, p ∈ P i → p.Prime) (z : ℝ) :
    (∑ q ∈ realization P F, omegaWeight z q) =
      ∑ s ∈ F, z ^ s.card * ∏ i ∈ s, ∑ p ∈ P i, (p : ℝ)⁻¹ := by
  classical
  rw [realization, Finset.sum_image]
  · rw [Fintype.sum_sigma]
    simp only [omegaWeight]
    simp_rw [selectionNumber_primeFactors hdis hp, selectionSupport_card hdis]
    simp only [selectionNumber, Nat.cast_prod, div_eq_mul_inv, ← Finset.prod_inv_distrib]
    rw [← Finset.sum_coe_sort F]
    apply Finset.sum_congr rfl
    intro s _
    rw [← Finset.mul_sum]
    congr 1
    rw [← Fintype.prod_sum (fun (i : s.val) (p : P i.val) => (p.val : ℝ)⁻¹)]
    calc
      (∏ i : s.val, ∑ p : P i.val, (p.val : ℝ)⁻¹) =
          ∏ i : s.val, ∑ p ∈ P i.val, (p : ℝ)⁻¹ := by
        apply Finset.prod_congr rfl
        intro i _
        exact Finset.sum_coe_sort (P i.val) (fun p => (p : ℝ)⁻¹)
      _ = ∏ i ∈ s.val, ∑ p ∈ P i, (p : ℝ)⁻¹ :=
        Finset.prod_coe_sort s.val (fun i => ∑ p ∈ P i, (p : ℝ)⁻¹)
  · intro q _ q' _ h
    exact selectionNumber_injective ht hdis hp h

theorem full_weight_le_kernel_of_prime_buckets {t : ℕ} {P : Fin t → Finset ℕ}
    (ht : 0 < t) (hdis : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hp : ∀ i p, p ∈ P i → p.Prime) {X : ℝ} (hX : 1 ≤ X)
    (hP : ∀ i p, p ∈ P i → (p : ℝ) ≤ X) {N : ℕ} (hN : X ^ t ≤ N)
    {z s : ℝ} (hz : 0 ≤ z) (hs : 0 ≤ s)
    (hweight : ∀ i, s ≤ ∑ p ∈ P i, (p : ℝ)⁻¹) :
    (1 + z * s) ^ t ≤ squarefreeKernel z N := by
  let F := (Finset.univ : Finset (Fin t)).powerset
  have hsubset : realization P F ⊆ (Finset.Icc 1 N).filter Squarefree := by
    intro q hq
    exact Finset.mem_filter.mpr
      ⟨realization_subset_interval hdis hp hX hP hN hq, realization_squarefree hdis hp q hq⟩
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun q _ _ => omegaWeight_nonneg hz q)
  rw [realization_omegaWeight ht hdis hp z] at hsum
  apply le_trans _ hsum
  have heq : (∑ I ∈ F, z ^ I.card * ∏ i ∈ I, ∑ p ∈ P i, (p : ℝ)⁻¹) =
      ∏ i : Fin t, (1 + z * ∑ p ∈ P i, (p : ℝ)⁻¹) := by
    rw [Finset.prod_one_add]
    apply Finset.sum_congr rfl
    intro I _
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  rw [heq]
  have hprod : (∏ _i : Fin t, (1 + z * s)) ≤
      ∏ i : Fin t, (1 + z * ∑ p ∈ P i, (p : ℝ)⁻¹) := by
    apply Finset.prod_le_prod
    · intro i _
      positivity
    · intro i _
      simpa only [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left (hweight i) hz) 1
  simpa using hprod

theorem eventually_kernel_lower_param {a s : ℝ} (ha : 0 < a) (hs : 0 < s)
    (has : a * s < 1) {z : ℝ} (hz : 0 ≤ z) :
    ∀ᶠ N : ℕ in atTop, (1 + z * s) ^ bucketCount a N ≤ squarefreeKernel z N := by
  let δ := (1 - a * s) / (2 * a)
  have hδ : 0 < δ := div_pos (by linarith) (by positivity)
  have hsmall : a * (s + δ) < 1 := by
    dsimp [δ]
    have ha0 := ha.ne'
    field_simp
    nlinarith
  filter_upwards [eventually_prime_buckets ha hs hδ hsmall] with N hN
  obtain ⟨ht, hX, hsize, P, hdis, hP, hw⟩ := hN
  exact full_weight_le_kernel_of_prime_buckets ht hdis (fun i p hp => (hP i p hp).1)
    hX (fun i p hp => (hP i p hp).2) hsize hz hs.le hw

theorem kernel_lower_param {a s : ℝ} (ha : 0 < a) (hs : 0 < s) (has : a * s < 1)
    {z : ℝ} (hz : 0 ≤ z) {b : ℝ} (hb : b < a * log (1 + z * s)) :
    ∀ᶠ N : ℕ in atTop, b < log (squarefreeKernel z N) / logScale N := by
  have hlim := (tendsto_bucketCount_div ha).mul_const (log (1 + z * s))
  have hlarge := hlim.eventually (lt_mem_nhds hb)
  filter_upwards [hlarge, eventually_kernel_lower_param ha hs has hz,
    tendsto_logScale.eventually_gt_atTop 0] with N hN hbound hL
  have hbase : 0 < 1 + z * s := by positivity
  have hlog := log_le_log (pow_pos hbase _) hbound
  rw [log_pow] at hlog
  apply hN.trans_le
  have h := div_le_div_of_nonneg_right hlog hL.le
  convert h using 1
  ring

theorem kernel_lower_bound {z : ℝ} (hz : 0 < z) {b : ℝ} (hb : b < z) :
    ∀ᶠ N : ℕ in atTop, b < log (squarefreeKernel z N) / logScale N := by
  obtain ⟨c, hc, hcz⟩ := exists_between (max_lt hz hb : max 0 b < z)
  have hc0 : 0 < c := (le_max_left _ _).trans_lt hc
  have hbc : b < c := (le_max_right _ _).trans_lt hc
  let s := (z - c) / (c * z)
  have hs : 0 < s := div_pos (sub_pos.mpr hcz) (mul_pos hc0 hz)
  have hsz : c * z * s = z - c := by dsimp [s]; field_simp
  have hlog : c * s < log (1 + z * s) := by
    have h := le_log_one_add_of_nonneg (mul_nonneg hz.le hs.le)
    apply lt_of_lt_of_le _ h
    apply (lt_div_iff₀ (by positivity : 0 < z * s + 2)).mpr
    have hgap : c * (z * s + 2) < 2 * z := by nlinarith
    nlinarith [mul_lt_mul_of_pos_right hgap hs]
  have hlogpos : 0 < log (1 + z * s) := (mul_pos hc0 hs).trans hlog
  have hinterval : c / log (1 + z * s) < 1 / s := by
    apply (div_lt_div_iff₀ hlogpos hs).mpr
    simpa using hlog
  obtain ⟨a, ha, has⟩ := exists_between hinterval
  have ha0 : 0 < a := (div_pos hc0 hlogpos).trans ha
  apply kernel_lower_param ha0 hs ((lt_div_iff₀ hs).mp has) hz.le
  exact hbc.trans ((div_lt_iff₀ hlogpos).mp ha)

theorem tendsto_primeHarmonic_nat_div :
    Tendsto (fun N : ℕ => primeHarmonic N / logScale N) atTop (𝓝 1) :=
  tendsto_primeHarmonic_div_log_log.comp tendsto_natCast_atTop_atTop

theorem tendsto_euler_log_bound (z : ℝ) :
    Tendsto (fun N : ℕ => z * (primeHarmonic N + 1) / logScale N) atTop (𝓝 z) := by
  have h := (tendsto_primeHarmonic_nat_div.add
    ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop tendsto_logScale)).const_mul z
  simp only [add_zero, mul_one] at h
  convert h using 1
  ext N
  ring

/-- The logarithmic form of Lemma 2.3 needed for the weighted upper transference. -/
theorem tendsto_log_squarefreeKernel_div {z : ℝ} (hz : 0 < z) :
    Tendsto (fun N => log (squarefreeKernel z N) / logScale N) atTop (𝓝 z) := by
  apply tendsto_order.mpr
  constructor
  · exact fun b hb => kernel_lower_bound hz hb
  · intro b hb
    have hlarge := (tendsto_euler_log_bound z).eventually (gt_mem_nhds hb)
    filter_upwards [hlarge, eventually_ge_atTop (1 : ℕ),
      tendsto_logScale.eventually_gt_atTop 0] with N hN hN1 hL
    have hpos : 0 < squarefreeKernel z N :=
      zero_lt_one.trans_le (one_le_squarefreeKernel hz.le hN1)
    have hbound := log_le_log hpos
      ((squarefreeKernel_le_omegaSum hz.le N).trans (omegaSum_le_exp hz.le N))
    rw [log_exp] at hbound
    exact (div_le_div_of_nonneg_right hbound hL.le).trans_lt hN

end Erdos856b
