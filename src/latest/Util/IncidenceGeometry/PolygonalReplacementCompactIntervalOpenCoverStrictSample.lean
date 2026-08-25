import Util.IncidenceGeometry.Basic
import Mathlib.Topology.UnitInterval

open Classical
noncomputable section

lemma PolygonalReplacementCompactIntervalOpenCoverStrictSample
    {ι : Type*} {a b : ℝ} (hab : a < b)
    {c : ι → Set (Set.Icc a b)}
    (hc_open : ∀ i, IsOpen (c i))
    (hc_cover : Set.univ ⊆ ⋃ i, c i) :
    ∃ m : ℕ, ∃ params : Fin (m + 1) → Set.Icc a b,
      0 < m ∧
        params 0 = (⟨a, ⟨le_rfl, hab.le⟩⟩ : Set.Icc a b) ∧
        params (Fin.last m) = (⟨b, ⟨hab.le, le_rfl⟩⟩ : Set.Icc a b) ∧
        (∀ n : Fin m, params (Fin.castSucc n) < params (Fin.succ n)) ∧
        (∀ n : Fin m, ∃ i, Set.Icc (params (Fin.castSucc n))
          (params (Fin.succ n)) ⊆ c i) := by
  classical
  obtain ⟨δ, hδ_pos, hδ_cover⟩ :=
    lebesgue_number_lemma_of_metric (s := (Set.univ : Set (Set.Icc a b)))
      isCompact_univ hc_open hc_cover
  let ε : ℝ := δ / 2
  have hε_pos : 0 < ε := half_pos hδ_pos
  have hε_nonneg : 0 ≤ ε := hε_pos.le
  let t : ℕ → Set.Icc a b := Set.Icc.addNSMul hab.le ε
  have ht_zero : t 0 = (⟨a, ⟨le_rfl, hab.le⟩⟩ : Set.Icc a b) := by
    apply Subtype.ext
    simpa [t] using Set.Icc.addNSMul_zero (h := hab.le) (δ := ε)
  obtain ⟨m0, hm0⟩ := Set.Icc.addNSMul_eq_right (h := hab.le) hε_pos
  have hhit : ∃ m, t m = (⟨b, ⟨hab.le, le_rfl⟩⟩ : Set.Icc a b) :=
    ⟨m0, by
      apply Subtype.ext
      simpa [t] using hm0 m0 le_rfl⟩
  let m : ℕ := Nat.find hhit
  have hm_hit : t m = (⟨b, ⟨hab.le, le_rfl⟩⟩ : Set.Icc a b) :=
    Nat.find_spec hhit
  have hm_pos : 0 < m := by
    by_contra hm_not
    have hm_eq_zero : m = 0 := Nat.eq_zero_of_not_pos hm_not
    have hleft_eq_right :
        (⟨a, ⟨le_rfl, hab.le⟩⟩ : Set.Icc a b) =
          (⟨b, ⟨hab.le, le_rfl⟩⟩ : Set.Icc a b) := by
      simpa [hm_eq_zero, ht_zero] using hm_hit
    have : a = b := congrArg Subtype.val hleft_eq_right
    exact (ne_of_lt hab) this
  have hnot_hit_before :
      ∀ n, n < m →
        t n ≠ (⟨b, ⟨hab.le, le_rfl⟩⟩ : Set.Icc a b) := by
    intro n hn htn
    exact Nat.find_min hhit hn htn
  have ht_strict_step : ∀ n, n < m → t n < t (n + 1) := by
    intro n hn
    have htn_ne := hnot_hit_before n hn
    have hnot_le : ¬ b ≤ a + n • ε := by
      intro hb_le
      apply htn_ne
      simpa [t, Set.Icc.addNSMul] using
        ((Set.projIcc_eq_right hab).2 hb_le :
          Set.projIcc a b hab.le (a + n • ε) =
            (⟨b, ⟨hab.le, le_rfl⟩⟩ : Set.Icc a b))
    have hx_lt_b : a + n • ε < b := lt_of_not_ge hnot_le
    have hx_ge_a : a ≤ a + n • ε := by
      exact le_add_of_nonneg_right (nsmul_nonneg hε_nonneg n)
    have ht_n_val : (t n : ℝ) = a + n • ε := by
      dsimp [t, Set.Icc.addNSMul]
      rw [Set.coe_projIcc, min_eq_right hx_lt_b.le, max_eq_right hx_ge_a]
    have hx_succ_ge_a : a ≤ a + (n + 1) • ε := by
      exact le_add_of_nonneg_right (nsmul_nonneg hε_nonneg (n + 1))
    have hsucc_val :
        (t (n + 1) : ℝ) =
          min b (a + (n + 1) • ε) := by
      dsimp [t, Set.Icc.addNSMul]
      rw [Set.coe_projIcc, max_eq_right (le_min hab.le hx_succ_ge_a)]
    rw [← Subtype.coe_lt_coe, ht_n_val, hsucc_val]
    apply lt_min
    · exact hx_lt_b
    · have : a + n • ε < a + (n + 1) • ε := by
        rw [add_lt_add_iff_left]
        norm_num [nsmul_eq_mul]
        nlinarith [hε_pos]
      exact this
  let params : Fin (m + 1) → Set.Icc a b := fun k => t k.1
  refine ⟨m, params, hm_pos, ?_, ?_, ?_, ?_⟩
  · simp [params, ht_zero]
  · simp [params, hm_hit]
  · intro n
    exact ht_strict_step n.1 n.2
  · intro n
    obtain ⟨i, hsub⟩ := hδ_cover (t n.1) trivial
    refine ⟨i, ?_⟩
    intro x hx
    exact hsub ((Set.Icc.abs_sub_addNSMul_le hab.le hε_nonneg n.1 hx).trans_lt
      (half_lt_self hδ_pos))
