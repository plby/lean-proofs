import StackExchange.Puzzling139335.HalfTurnRemainder.Variation.Defs
import StackExchange.Puzzling139335.LoopVariation.Cuts.GeometricPartition

/-!
# Variation bounds for the actual finite interface partitions

The ordered-loop witnesses retained by the geometric construction compute the
intrinsic sums on the interface family. Thus each boundary's loop variation
lies between its actual arc sum and that sum plus one penalty per arc.
-/

open Set

namespace Puzzling139335.HalfTurnRemainder

open LoopVariation

noncomputable section

/-- Exact geometric loop parameters, rather than a presumed perimeter bound,
give the finite-resolution estimate for every boundary of the dissection. -/
theorem boundaryArcSum_bounds {d : SquareDissection} (F : ExactBoundaryArcFamily d)
    (hparams : F.HasLoopParameters) {ε : ℝ} (hε : 0 < ε) (i : ExtendedPieceIndex) :
    boundaryArcSum F ε i ≤ loopVariation ε (frontier (d.extendedPiece i)) ∧
      loopVariation ε (frontier (d.extendedPiece i)) ≤
        boundaryArcSum F ε i + (F.n i : ℝ) * ε := by
  obtain ⟨f, hf, himage, hn, t, ht, ht0, ht1, hhalf, hArc, _, _⟩ := hparams i
  have hn2 : 2 ≤ F.n i := by
    by_contra hnot
    have hn1 : F.n i = 1 := by omega
    obtain ⟨j, hj⟩ := hhalf
    have hjends : j = 0 ∨ j = Fin.last (F.n i) := by
      by_cases hj0 : j.val = 0
      · exact Or.inl (Fin.ext hj0)
      · right
        apply Fin.ext
        change j.val = F.n i
        have hjlt := j.isLt
        omega
    rcases hjends with rfl | rfl
    · rw [ht0] at hj
      norm_num at hj
    · rw [ht1] at hj
      norm_num at hj
  let T : ℕ → ℝ := fun k => if hk : k ≤ F.n i then t ⟨k, Nat.lt_succ_of_le hk⟩ else 1
  have hT (k : ℕ) (hk : k ≤ F.n i) :
      T k = t ⟨k, Nat.lt_succ_of_le hk⟩ := by
    simp only [T, dif_pos hk]
  have hTmono : StrictMonoOn T (Icc 0 (F.n i)) := by
    intro j hj k hk hjk
    rw [hT j hj.2, hT k hk.2]
    exact ht hjk
  have hT0 : T 0 = 0 := by
    rw [hT 0 (Nat.zero_le _)]
    exact ht0
  have hT1 : T (F.n i) = 1 := by
    rw [hT (F.n i) le_rfl]
    exact ht1
  have hsum : boundaryArcSum F ε i =
      ∑ k ∈ Finset.range (F.n i), arcVariation ε (f '' Icc (T k) (T (k + 1))) := by
    calc
      boundaryArcSum F ε i =
          ∑ k : Fin (F.n i), arcVariation ε (f '' Icc (T k.val) (T (k.val + 1))) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hArc k, hT k.val (Nat.le_of_lt k.isLt),
          hT (k.val + 1) (Nat.succ_le_of_lt k.isLt)]
        rfl
      _ = _ := Fin.sum_univ_eq_sum_range
        (fun k => arcVariation ε (f '' Icc (T k) (T (k + 1)))) (F.n i)
  rw [hsum]
  exact loopVariation_partition_bounds hf himage hn2 hTmono hT0 hT1 hε

/-- Actual congruence of closed pieces gives equality of their intrinsic
boundary variations, including for nonrectifiable Jordan boundaries. -/
theorem piece_boundary_variation_eq (d : SquareDissection) (ε : ℝ) (i j : Fin 4) :
    loopVariation ε (frontier (d.piece i)) = loopVariation ε (frontier (d.piece j)) := by
  obtain ⟨e, he⟩ := d.congruent i j
  have hfront : e '' frontier (d.piece i) = frontier (d.piece j) :=
    (e.toHomeomorph.image_frontier _).trans (congrArg frontier he)
  rw [← hfront, loopVariation_image_isometry ε (d.jordan i).frontier_isJordanCurve e.isometry]

end

end Puzzling139335.HalfTurnRemainder
