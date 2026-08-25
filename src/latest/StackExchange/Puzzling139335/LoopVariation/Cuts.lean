import StackExchange.Puzzling139335.LoopVariation.Cuts.ArcPartition
import StackExchange.Puzzling139335.LoopVariation.Finiteness

/-!
# Finite arc decompositions of cyclic truncated variation

An ordered partition into `m` arcs has total arc variation at most the cyclic
variation.  The reverse inequality loses at most `m * ε`: one penalty for each
of the `m - 1` interior cuts, and one for opening the loop at its basepoint.
All scores and suprema are the concrete definitions in the imported modules.
-/

open Set

namespace Puzzling139335.LoopVariation

open ArcVariation

noncomputable section

variable {α X : Type*} [LinearOrder α] [PseudoMetricSpace X]

/-- A finite closed parameter partition has a cyclic-variation error between
zero and `m * ε`, assuming only boundedness of the concrete arc scores. -/
theorem loop_partition_estimates {ε : ℝ} {f : α → X} {t : ℕ → α} {m : ℕ}
    (hm : 0 < m) (hε : 0 ≤ ε) (ht : MonotoneOn t (Icc 0 m))
    (hclose : f (t 0) = f (t m))
    (hb : BddAbove (scoresOn ε f (Icc (t 0) (t m)))) :
    cutSum ε f t m ≤ loopVariationOn ε f (Icc (t 0) (t m)) ∧
      loopVariationOn ε f (Icc (t 0) (t m)) ≤
        cutSum ε f t m + (m : ℝ) * ε := by
  have hends : t 0 ≤ t m :=
    ht ⟨le_rfl, Nat.zero_le m⟩ ⟨Nat.zero_le m, le_rfl⟩ (Nat.zero_le m)
  have hcyclic : BddAbove (cycleScoresOn ε f (Icc (t 0) (t m))) := by
    refine ⟨variationOn ε f (Icc (t 0) (t m)) + ε, ?_⟩
    rintro _ ⟨xs, hxs, rfl⟩
    exact cycleScore_le_variationOn_add hε hends hclose hb hxs
  have harc := arc_partition_estimates hm hε ht hb
  have hlo := variationOn_le_loopVariationOn hcyclic
  have hhi := loopVariationOn_le_variationOn_add hε hends hclose hb
  have hcount : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel (show 1 ≤ m by omega)
  have herror : ((m - 1 : ℕ) : ℝ) * ε + ε = (m : ℝ) * ε := by
    calc
      ((m - 1 : ℕ) : ℝ) * ε + ε = (((m - 1 : ℕ) : ℝ) + 1) * ε := by ring
      _ = (m : ℝ) * ε := by rw [hcount]
  constructor
  · exact harc.1.trans hlo
  · calc
      loopVariationOn ε f (Icc (t 0) (t m)) ≤
          variationOn ε f (Icc (t 0) (t m)) + ε := hhi
      _ ≤ (cutSum ε f t m + ((m - 1 : ℕ) : ℝ) * ε) + ε := by
          linarith [harc.2]
      _ = cutSum ε f t m + (m : ℝ) * ε := by rw [add_assoc, herror]

end

noncomputable section

variable {X : Type*} [PseudoMetricSpace X]

/-- For a continuous closed curve, compactness supplies the boundedness needed
for the finite cyclic partition estimates. -/
theorem loop_partition_estimates_of_continuousOn
    {ε : ℝ} {f : ℝ → X} {t : ℕ → ℝ} {m : ℕ}
    (hm : 0 < m) (hε : 0 < ε) (ht : MonotoneOn t (Icc 0 m))
    (hf : ContinuousOn f (Icc (t 0) (t m))) (hclose : f (t 0) = f (t m)) :
    cutSum ε f t m ≤ loopVariationOn ε f (Icc (t 0) (t m)) ∧
      loopVariationOn ε f (Icc (t 0) (t m)) ≤
        cutSum ε f t m + (m : ℝ) * ε := by
  have hends : t 0 ≤ t m :=
    ht ⟨le_rfl, Nat.zero_le m⟩ ⟨Nat.zero_le m, le_rfl⟩ (Nat.zero_le m)
  exact loop_partition_estimates hm hε.le ht hclose
    (bddAbove_scoresOn_Icc hends hf hε)

/-- Two complementary arcs of a closed parameter interval have total variation
within `2 * ε` below its cyclic variation. -/
theorem loopVariationOn_two_arc_bounds {f : ℝ → X} {a b c ε : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) (hf : ContinuousOn f (Icc a b))
    (hclose : f a = f b) (hε : 0 < ε) :
    variationOn ε f (Icc a c) + variationOn ε f (Icc c b) ≤
        loopVariationOn ε f (Icc a b) ∧
      loopVariationOn ε f (Icc a b) ≤
        variationOn ε f (Icc a c) + variationOn ε f (Icc c b) + 2 * ε := by
  have harc := variationOn_Icc_concatenation_of_continuousOn hac hcb hf hε
  have hloop := loopVariationOn_Icc_bounds (hac.trans hcb) hf hclose hε
  constructor
  · exact harc.1.trans hloop.1
  · linarith [harc.2, hloop.2]

end

end Puzzling139335.LoopVariation
