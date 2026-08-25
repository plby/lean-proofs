import ErdosProblems.Erdos157.MaskDecay
import ErdosProblems.Erdos157.UniformProducts
import ErdosProblems.Erdos157.CandidateEncoding

/-! One infinite choice of masks works for every sufficiently large level. -/

namespace Erdos157.Elementary

open Filter

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

theorem exists_eventually_good_masks :
    ∃ τ : MaskChoice K, ∀ᶠ k in atTop,
      ∀ z : MaskTarget K k, MaskTargetHit K (fun i => τ i) z := by
  classical
  let X (i : ℕ) := TagField i → LogDigit K i
  letI (i : ℕ) : MeasurableSpace (X i) := ⊤
  letI (i : ℕ) : DiscreteMeasurableSpace (X i) := ⟨fun _ => trivial⟩
  let μ := UniformProducts.productMeasure X
  let bad (k : ℕ) : Set (∀ i, X i) := {τ | MaskLevelFailure K k (fun i => τ i)}
  have hbad : ∀ᶠ k in atTop, μ.real (bad k) ≤ Real.exp (-(k : ℝ)) := by
    filter_upwards [eventually_maskLevelFailure_density K] with k hk
    have heq := UniformProducts.prefix_density X k (MaskLevelFailure K k)
    exact heq.trans_le hk
  obtain ⟨τ, hτ⟩ := exists_eventually_avoiding_events μ bad (fun k => Real.exp (-(k : ℝ)))
    Real.summable_exp_neg_nat hbad
  refine ⟨τ, hτ.mono ?_⟩
  intro k hk z
  by_contra hz
  exact hk ⟨z, hz⟩

end Erdos157.Elementary
