import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMinimumPolygonSpace

/-!
# A common finite partition for the entire minimum locus

The norm of every quaternionic complex structure is at most one. A sufficiently
fine uniform partition therefore keeps every minimum exponential increment
in the logarithm target at once, while retaining compact sublevels below any
prescribed energy bound. The minimum-locus homeomorphism has no remaining
small-logarithm existence premise.
-/

open Set Metric

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.UniformTimePartition
open VertexSpace Exponential

variable {n m : ℕ}

private theorem norm_real_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (c : ℝ) (v : V) : ‖c • v‖ = |c| * ‖v‖ := by
  simpa only [Real.norm_eq_abs] using norm_smul c v

theorem complexStructure_step_mem_logarithmTarget (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    {r E : ℝ} (hr0 : 0 ≤ r) (hE : Real.pi ^ 2 ≤ E)
    (hr : closedBall (0 : SkewSpace n) r ⊆ compatibleTarget n)
    (hmesh : ∀ i : Fin (m + 1), E * (τ i.succ - τ i.castSucc) ≤ r ^ 2)
    (J : ComplexStructures.Space n) (i : Fin (m + 1)) :
    (τ i.succ - τ i.castSucc) • (Real.pi • J.1) ∈ compatibleTarget n := by
  let δ := τ i.succ - τ i.castSucc
  have hδ : 0 ≤ δ := (sub_pos.mpr (hτ (show i.castSucc < i.succ by simp))).le
  have hδone : δ ≤ 1 := by
    have hl := hτ.monotone (Fin.zero_le i.castSucc)
    have hu := hτ.monotone (Fin.le_last i.succ)
    rw [hzero] at hl
    rw [hone] at hu
    dsimp only [δ]
    linarith
  have hprod : 0 ≤ δ * Real.pi := mul_nonneg hδ Real.pi_pos.le
  have hsquare : (δ * Real.pi) ^ 2 ≤ r ^ 2 := by
    calc
      (δ * Real.pi) ^ 2 = (Real.pi ^ 2 * δ) * δ := by ring
      _ ≤ Real.pi ^ 2 * δ := mul_le_of_le_one_right (mul_nonneg (sq_nonneg _) hδ) hδone
      _ ≤ E * δ := mul_le_mul_of_nonneg_right hE hδ
      _ ≤ r ^ 2 := hmesh i
  have hbound : δ * Real.pi ≤ r := (sq_le_sq₀ hprod hr0).mp hsquare
  apply hr
  rw [mem_closedBall,
    dist_zero_right ((τ i.succ - τ i.castSucc) • (Real.pi • J.val)),
    smul_smul, norm_real_smul (V := SkewSpace n),
    abs_of_nonneg hprod]
  exact (mul_le_of_le_one_right hprod (ComplexStructures.norm_le_one J)).trans hbound

/-- Every sufficiently fine uniform partition has the common controls for
compact short sublevels and all minimum exponential increments. -/
theorem exists_eventual_minimumPolygon_control (n : ℕ) (E : ℝ) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      (∀ a b : symplecticSubgroup n, ∀ C : ℝ, C ≤ E →
        IsCompact (energySublevel a b (time m) C) ∧
        energySublevel a b (time m) C ⊆ shortDomain a b m) ∧
      (∀ a b : symplecticSubgroup n,
        IsCompact (energySublevel a b (time m) (((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2))) ∧
      ∀ J : ComplexStructures.Space n, ∀ i : Fin (m + 1),
        (time m i.succ - time m i.castSucc) •
          (Real.pi • J.1) ∈ compatibleTarget n := by
  obtain ⟨r, hr0, hrπ, hr⟩ := exists_compatible_radius n
  let B := max E ((((4 * n + 4 : ℕ) : ℝ) + 1) * Real.pi ^ 2)
  have hEB : E ≤ B := le_max_left _ _
  have hπB : Real.pi ^ 2 ≤ B := by
    have hb := le_max_right E ((((4 * n + 4 : ℕ) : ℝ) + 1) * Real.pi ^ 2)
    have hn : 0 ≤ ((4 * n + 4 : ℕ) : ℝ) := Nat.cast_nonneg (4 * n + 4)
    dsimp only [B]
    nlinarith [sq_nonneg Real.pi]
  have hminB : ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 ≤ B := by
    have hb := le_max_right E ((((4 * n + 4 : ℕ) : ℝ) + 1) * Real.pi ^ 2)
    dsimp only [B]
    nlinarith [sq_nonneg Real.pi]
  obtain ⟨N, hN⟩ := exists_nat_gt (B / r ^ 2)
  refine ⟨N, ?_⟩
  intro m hNm
  have hm := small_energy_step_of_large B hr0 m
    (hN.trans_le (by exact_mod_cast hNm))
  let τ := time m
  have hτ := strictMono_time m
  have hzero := time_zero m
  have hone := time_last m
  have hmesh {C : ℝ} (hC : C ≤ B) (i : Fin (m + 1)) :
      C * (τ i.succ - τ i.castSucc) ≤ r ^ 2 :=
    (mul_le_mul_of_nonneg_right hC
      (sub_nonneg.mpr (hτ (show i.castSucc < i.succ by simp)).le)).trans (hm i).le
  refine ⟨?_, ?_, ?_⟩
  · intro a b C hC
    exact ⟨isCompact_energySublevel a b τ hτ hr0.le hr (hmesh (hC.trans hEB)),
      energySublevel_subset_shortDomain a b τ hτ hr0.le hrπ hr (hmesh (hC.trans hEB))⟩
  · intro a b
    exact isCompact_energySublevel a b τ hτ hr0.le hr (hmesh hminB)
  · exact complexStructure_step_mem_logarithmTarget τ hτ hzero hone
      hr0.le hπB hr (hmesh le_rfl)

/-- Common partition controls for compact short sublevels and all minimum
exponential increments. The minimum sublevel is compact even when `E` is smaller. -/
theorem exists_minimumPolygon_partition_control (n : ℕ) (E : ℝ) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧
      (∀ a b : symplecticSubgroup n, ∀ C : ℝ, C ≤ E →
        IsCompact (energySublevel a b (time m) C) ∧
        energySublevel a b (time m) C ⊆ shortDomain a b m) ∧
      (∀ a b : symplecticSubgroup n,
        IsCompact (energySublevel a b (time m) (((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2))) ∧
      ∀ J : ComplexStructures.Space n, ∀ i : Fin (m + 1),
        (time m i.succ - time m i.castSucc) •
          (Real.pi • J.1) ∈ compatibleTarget n := by
  obtain ⟨N₀, hN₀⟩ := exists_eventual_minimumPolygon_control n E
  exact ⟨max N N₀, le_max_left _ _, hN₀ _ (le_max_right _ _)⟩

/-- For any energy bound there are arbitrarily fine partitions with both
compact short sublevels and the actual minimum-locus homeomorphism. -/
theorem exists_minimumPolygon_partition (n : ℕ) (E : ℝ) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧
      (∀ a b : symplecticSubgroup n, ∀ C : ℝ, C ≤ E →
        IsCompact (energySublevel a b (time m) C) ∧
        energySublevel a b (time m) C ⊆ shortDomain a b m) ∧
      ∀ a b : symplecticSubgroup n,
        (a⁻¹ * b).val.val.val = -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) →
        Nonempty (ComplexStructures.Space n ≃ₜ
          minimumSet a b (time m)) := by
  obtain ⟨m, hNm, hlevels, hmin, hsmall⟩ := exists_minimumPolygon_partition_control n E N
  refine ⟨m, hNm, hlevels, ?_⟩
  intro a b hanti
  exact ⟨complexStructureMinimumHomeomorph a b (time m)
    (strictMono_time m) (time_zero m)
    (time_last m) hanti hsmall (hmin a b)⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon
