import ErdosProblems.Erdos856b.PressureRepresentation

/-! # Complementation and the sunflower pressure -/

namespace Erdos856b

open Real Filter
open scoped BigOperators Topology FinsetFamily

/-- No `k` distinct members have identical pairwise intersections. -/
def InterFree {α : Type*} [DecidableEq α] (k : ℕ) (F : Finset (Finset α)) : Prop :=
  ∀ a : Fin k → Finset α, Function.Injective a → (∀ i, a i ∈ F) →
    ¬ ∃ u : Finset α, ∀ i j, i ≠ j → a i ∩ a j = u

theorem UnionFree.compls {α : Type*} [Fintype α] [DecidableEq α]
    {k : ℕ} {F : Finset (Finset α)} (hF : UnionFree k F) : InterFree k Fᶜˢ := by
  intro a hinj hmem hbad
  obtain ⟨u, hu⟩ := hbad
  apply hF (fun i => (a i)ᶜ) (compl_injective.comp hinj)
    (fun i => Finset.mem_compls.mp (hmem i))
  refine ⟨uᶜ, ?_⟩
  intro i j hij
  simpa only [Finset.compl_inter] using congrArg (fun s : Finset α => sᶜ) (hu i j hij)

theorem InterFree.compls {α : Type*} [Fintype α] [DecidableEq α]
    {k : ℕ} {F : Finset (Finset α)} (hF : InterFree k F) : UnionFree k Fᶜˢ := by
  intro a hinj hmem hbad
  obtain ⟨u, hu⟩ := hbad
  apply hF (fun i => (a i)ᶜ) (compl_injective.comp hinj)
    (fun i => Finset.mem_compls.mp (hmem i))
  refine ⟨uᶜ, ?_⟩
  intro i j hij
  simpa only [Finset.compl_union] using congrArg (fun s : Finset α => sᶜ) (hu i j hij)

theorem partitionWeight_compls {n : ℕ} (F : Finset (Finset (Fin n)))
    {z : ℝ} (hz : 0 < z) :
    partitionWeight Fᶜˢ z = z ^ n * partitionWeight F (1 / z) := by
  simp only [partitionWeight, Finset.compls, Finset.sum_map, Function.Embedding.coeFn_mk]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have hcard : s.card + sᶜ.card = n := by simp
  have hpow : z ^ n = z ^ s.card * z ^ sᶜ.card := by rw [← pow_add, hcard]
  rw [hpow, one_div_pow]
  field_simp

noncomputable def allInterFreeFamilies (k n : ℕ) : Finset (Finset (Finset (Fin n))) := by
  classical
  exact insert ∅ (Finset.univ.filter (InterFree k))

/-- The maximum sunflower-free partition function from the writeup. -/
noncomputable def W (k n : ℕ) (z : ℝ) : ℝ :=
  (allInterFreeFamilies k n).sup' (by
    classical
    simp [allInterFreeFamilies]) (fun F => partitionWeight F z)

theorem partitionWeight_le_W {k n : ℕ} {F : Finset (Finset (Fin n))}
    (hF : InterFree k F) (z : ℝ) : partitionWeight F z ≤ W k n z := by
  classical
  unfold W
  exact Finset.le_sup' (s := allInterFreeFamilies k n) (fun G => partitionWeight G z)
    (b := F) (by simp [allInterFreeFamilies, hF])

theorem C_attained {k : ℕ} (hk : 3 ≤ k) (n : ℕ) (z : ℝ) :
    ∃ F : Finset (Finset (Fin n)), UnionFree k F ∧ partitionWeight F z = C k n z := by
  classical
  obtain ⟨F, hF, heq⟩ := Finset.exists_mem_eq_sup'
    (show (allUnionFreeFamilies k n).Nonempty by simp [allUnionFreeFamilies])
    (fun F => partitionWeight F z)
  refine ⟨F, ?_, heq.symm⟩
  simp only [allUnionFreeFamilies, Finset.mem_insert, Finset.mem_filter,
    Finset.mem_univ, true_and] at hF
  rcases hF with rfl | hF
  · exact unionFree_empty (by omega)
  · exact hF

theorem W_attained {k : ℕ} (hk : 3 ≤ k) (n : ℕ) (z : ℝ) :
    ∃ F : Finset (Finset (Fin n)), InterFree k F ∧ partitionWeight F z = W k n z := by
  classical
  obtain ⟨F, hF, heq⟩ := Finset.exists_mem_eq_sup'
    (show (allInterFreeFamilies k n).Nonempty by simp [allInterFreeFamilies])
    (fun F => partitionWeight F z)
  refine ⟨F, ?_, heq.symm⟩
  simp only [allInterFreeFamilies, Finset.mem_insert, Finset.mem_filter,
    Finset.mem_univ, true_and] at hF
  rcases hF with rfl | hF
  · simpa using (unionFree_empty (α := Fin n) (by omega : 0 < k)).compls
  · exact hF

/-- The finite complement identity, with actual sunflower and cosunflower maxima. -/
theorem W_eq_dual_C {k : ℕ} (hk : 3 ≤ k) (n : ℕ) {z : ℝ} (hz : 0 < z) :
    W k n z = z ^ n * C k n (1 / z) := by
  apply le_antisymm
  · obtain ⟨F, hF, hmax⟩ := W_attained hk n z
    rw [← hmax, ← Finset.compls_compls F, partitionWeight_compls _ hz]
    exact mul_le_mul_of_nonneg_left (partitionWeight_le_C hF.compls _) (pow_nonneg hz.le _)
  · obtain ⟨F, hF, hmax⟩ := C_attained hk n (1 / z)
    rw [← hmax, ← partitionWeight_compls F hz]
    exact partitionWeight_le_W hF.compls z

theorem W_pos {k n : ℕ} (hk : 3 ≤ k) {z : ℝ} (hz : 0 < z) : 0 < W k n z := by
  rw [W_eq_dual_C hk n hz]
  exact mul_pos (pow_pos hz _) (C_pos hk (one_div_pos.mpr hz))

theorem tendsto_log_W_div {k : ℕ} (hk : 3 ≤ k) {z : ℝ} (hz : 0 < z) :
    Tendsto (fun n : ℕ => log (W k n z) / n) atTop
      (𝓝 (log z + logPressure k (1 / z))) := by
  have h := (tendsto_const_nhds (x := log z)).add
    (tendsto_log_C_div hk (one_div_pos.mpr hz))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  rw [W_eq_dual_C hk n hz, log_mul (pow_ne_zero _ hz.ne')
    (C_pos hk (one_div_pos.mpr hz)).ne', log_pow]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp

/-- Existence of the sunflower pressure and its complement duality. -/
theorem tendsto_W_root {k : ℕ} (hk : 3 ≤ k) {z : ℝ} (hz : 0 < z) :
    Tendsto (fun n : ℕ => W k n z ^ (1 / (n : ℝ))) atTop
      (𝓝 (sunflowerPressure k z)) := by
  change Tendsto _ _ (𝓝 (z * exp (logPressure k (1 / z))))
  have h := Real.continuous_exp.continuousAt.tendsto.comp (tendsto_log_W_div hk hz)
  rw [exp_add, exp_log hz] at h
  convert h using 1
  ext n
  rw [rpow_def_of_pos (W_pos hk hz)]
  congr 1
  ring

theorem cosPressure_duality (k : ℕ) {z : ℝ} (hz : 0 < z) :
    cosPressure k z = z * sunflowerPressure k (1 / z) := by
  dsimp [sunflowerPressure]
  rw [one_div_one_div]
  field_simp

end Erdos856b
