import ErdosProblems.Erdos1148.RefinedMovingLocalCover
import ErdosProblems.Erdos1148.BoundedFrameLiftGrid
import ErdosProblems.Erdos1148.ModularHighCuspVisits

/-! # A global refined cusp-visit cover with polynomial initial-height dependence -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_refined_global_cusp_cover {η ε : ℝ}
    (hηpos : 0 < η) (hη : η ≤ 1 / 2) (hε : 0 < ε) :
    ∃ H₀ : ℝ, 1 < H₀ ∧ ∀ H : ℝ, H₀ ≤ H → ∃ C : ℝ, 0 < C ∧
      ∀ Y : ℝ, 1 ≤ Y → ∀ (n : ℕ) (A : ℝ),
      ∃ (N : ℕ) (B : Fin N → Set ModularOrbitSpace),
        (N : ℝ) ≤ C * (Y + 1) ^ 11 * Real.exp ((1 + ε) * n - A / 2) ∧
        (∀ i, IsCompact (B i)) ∧ (∀ i, MeasurableSet (B i)) ∧
        modularBufferedHighCuspVisits H Y n A ⊆ ⋃ i, B i ∧
        ∀ i, B i ×ˢ B i ⊆ modularForwardBowenPairs (32 * η) ((n : ℝ) + 4 * Real.log H) := by
  obtain ⟨H₀, hH₀, hcover⟩ := exists_refined_moving_local_lift_cover hηpos hη hε
  refine ⟨H₀, hH₀, ?_⟩
  intro H hH
  have hH1 : 1 < H := hH₀.trans_le hH
  have hHpos : 0 < H := by linarith
  obtain ⟨C, hC, hlocal⟩ := hcover H hH
  let G := (4 / η + 1) ^ 4 * (5 * (H + 1)) ^ 8
  have hG : 0 < G := by dsimp only [G]; positivity
  refine ⟨G * C, mul_pos hG hC, ?_⟩
  intro Y hY n A
  let Z := 2 * (Y * H + 2)
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  obtain ⟨N₀, E, hN₀, hEunion, hEclose⟩ := exists_bounded_frame_lift_grid hZ hηpos
  have hgrid : (N₀ : ℝ) ≤ G * (Y + 1) ^ 8 := by
    have hbase : Z + 1 ≤ (5 * (H + 1)) * (Y + 1) := by dsimp only [Z]; nlinarith
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ Z + 1) hbase 8
    apply hN₀.trans
    calc
      _ ≤ (4 / η + 1) ^ 4 * (((5 * (H + 1)) * (Y + 1)) ^ 8) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by dsimp only [G]; rw [mul_pow]; ring
  let F : Fin N₀ → Set SL(2, ℝ) := fun i => highCuspVisitsWithInitialHeight H Y n A (E i)
  have hF (i : Fin N₀) : LiftCoverBound η ((n : ℝ) + 4 * Real.log H) (F i)
      (C * (Y + 1) ^ 3 * Real.exp ((1 + ε) * n - A / 2)) :=
    hlocal Y hY n (E i) A (hEclose i)
  have hc := LiftCoverBound.iUnion F hF
  have hcost : (Fintype.card (Fin N₀) : ℝ) *
      (C * (Y + 1) ^ 3 * Real.exp ((1 + ε) * n - A / 2)) ≤
      (G * C) * (Y + 1) ^ 11 * Real.exp ((1 + ε) * n - A / 2) := by
    simp only [Fintype.card_fin]
    calc
      _ ≤ (G * (Y + 1) ^ 8) * (C * (Y + 1) ^ 3 * Real.exp ((1 + ε) * n - A / 2)) :=
        mul_le_mul_of_nonneg_right hgrid (by positivity)
      _ = _ := by ring
  have hT : 0 ≤ (n : ℝ) + 4 * Real.log H := by
    have hlog := (Real.log_pos hH1).le
    positivity
  obtain ⟨N, B, hN, hcompact, hmeas, hcov, hpair⟩ :=
    (hc.mono_bound hcost).measurable_modular_cover hηpos.le hη hT
  refine ⟨N, B, hN, hcompact, hmeas, ?_, hpair⟩
  intro x hx
  apply hcov
  have hx' : modularRightTranslate (diagonalFlow (2 * Real.log H)) x ∉ modularCusp Y ∧
      A ≤ ((modularCuspVisitTimes H n
        (modularRightTranslate (diagonalFlow (2 * Real.log H)) x)).card : ℝ) := hx
  have hxnot := not_mem_cusp_before_log_buffer hH1.le x hx'.1
  obtain ⟨g, hmk, hg⟩ := exists_bounded_lift_of_not_cusp (by positivity : 0 < Y * H) x hxnot
  have hg' : g ∈ boundedEntryFrames Z := hg
  rw [← hEunion] at hg'
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg'
  refine ⟨g, Set.mem_iUnion.mpr ⟨i, hi, ?_⟩, hmk⟩
  change modularRightTranslate (diagonalFlow (2 * Real.log H)) (modularMk g) ∉ modularCusp Y ∧
    A ≤ ((modularCuspVisitTimes H n
      (modularRightTranslate (diagonalFlow (2 * Real.log H)) (modularMk g))).card : ℝ)
  rwa [hmk]

end Erdos1148.DukeArithmetic
