import Wikipedia.HopfProblem.DegreeCollapseFiniteIndexDisorder
import Mathlib.Data.Finset.Max

/-!
# Finite descent of one distinguished critical value

If two selected values are not consecutive, the immediate predecessor of
the upper one still lies above the lower one. Swapping that predecessor
with the upper point strictly decreases the number of values below the
distinguished point. This is a natural-valued termination measure.
-/

noncomputable section

open Function

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement

variable {X : Type*} [Fintype X]

theorem exists_consecutive_below_of_intermediate {h : X → ℝ} {p q : X}
    (hintermediate : ∃ x, h p < h x ∧ h x < h q) :
    ∃ r, h p < h r ∧ h r < h q ∧ ∀ x, ¬(h r < h x ∧ h x < h q) := by
  classical
  obtain ⟨w, hpw, hwq⟩ := hintermediate
  let K := Finset.univ.filter (fun x => h x < h q)
  have hw : w ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwq⟩
  obtain ⟨r, hr, hmax⟩ := K.exists_max_image h ⟨w, hw⟩
  refine ⟨r, hpw.trans_le (hmax w hw), (Finset.mem_filter.mp hr).2, ?_⟩
  intro x hx
  exact (not_lt_of_ge (hmax x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.2⟩))) hx.1

def beforeValueRank (h : X → ℝ) (q : X) : ℕ := upperValueRank (fun x => -h x) q

open Classical in
theorem beforeValueRank_exchange_lt {h g : X → ℝ} (hi : Injective h) {p q : X}
    (hpq : h p < h q) (hconsecutive : ∀ x, ¬(h p < h x ∧ h x < h q))
    (hgp : g p = h q) (hgq : g q = h p)
    (hothers : ∀ x, x ≠ p → x ≠ q → g x = h x) :
    beforeValueRank g q < beforeValueRank h q := by
  classical
  have hform : (fun x => -g x) = (fun x => -h x) ∘ Equiv.swap p q := by
    funext x
    by_cases hxp : x = p
    · subst x
      simp only [Function.comp_apply, Equiv.swap_apply_left, hgp]
    by_cases hxq : x = q
    · subst x
      simp only [Function.comp_apply, Equiv.swap_apply_right, hgq]
    simp only [Function.comp_apply, Equiv.swap_apply_def, if_neg hxp, if_neg hxq,
      hothers x hxp hxq]
  have hnew : beforeValueRank g q = beforeValueRank h p := by
    unfold beforeValueRank
    rw [hform, upperValueRank_comp_equiv, Equiv.swap_apply_right]
  have hneg : Injective (fun x => -h x) := fun x y hxy => hi (neg_injective hxy)
  have hgap : beforeValueRank h q = beforeValueRank h p + 1 := by
    apply upperValueRank_consecutive hneg (neg_lt_neg hpq)
    intro x hx
    exact hconsecutive x ⟨neg_lt_neg_iff.mp hx.2, neg_lt_neg_iff.mp hx.1⟩
  omega

end Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement
