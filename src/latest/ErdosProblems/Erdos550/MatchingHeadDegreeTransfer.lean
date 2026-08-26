import Mathlib
import ErdosProblems.Erdos550.MatchingCoverageBounds

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Transfer of head degree to the maximal-matching cluster union

After the maximum matching leaves fewer than `B` non-head clusters uncovered,
at most `B+2` clusters lie outside its endpoint set.  Since every cluster
contributes at most its size to a head degree, deleting those clusters costs at
most `(B+2)s`.  This is the combinatorial content of the paper's passage to
`D_X,D_Y`.
-/

open Finset

namespace Erdos550

/-- Removing a set of at most `B` indices loses at most `B*s` from a
nonnegative sum whose summands are bounded by `s`. -/
lemma sum_on_large_subset_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Finset ι) (f : ι → ℝ) (s : ℝ)
    (hfs : ∀ i, f i ≤ s) (hs0 : 0 ≤ s) (B : ℕ)
    (hcompl : (Finset.univ \ E).card ≤ B) :
    (∑ i, f i) - B * s ≤ ∑ i ∈ E, f i := by
  have hout : ∑ i ∈ Finset.univ \ E, f i ≤ B * s := by
    calc
      _ ≤ ∑ _i ∈ Finset.univ \ E, s := Finset.sum_le_sum (fun i _ => hfs i)
      _ = ((Finset.univ \ E).card : ℝ) * s := by simp
      _ ≤ B * s := mul_le_mul_of_nonneg_right (by exact_mod_cast hcompl) hs0
  rw [← Finset.sum_sdiff (Finset.subset_univ E)]
  linarith

/-- Application to the endpoint images of the paper's maximal matching. -/
lemma matching_endpoint_sum_lower
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (X Y : ι) (cL cR : κ → ι) (U : Finset ι)
    (hU : ∀ a, a ∈ U ↔ a ≠ X ∧ a ≠ Y ∧
      a ∉ Finset.univ.image cL ∧ a ∉ Finset.univ.image cR)
    (B : ℕ) (hsmall : U.card < B)
    (f : ι → ℝ) (s : ℝ) (hfs : ∀ i, f i ≤ s)
    (hs0 : 0 ≤ s) :
    (∑ i, f i) - (B + 2) * s ≤
      ∑ i ∈ (Finset.univ.image cL ∪ Finset.univ.image cR), f i := by
  convert! sum_on_large_subset_lower
      (Finset.univ.image cL ∪ Finset.univ.image cR) f s hfs hs0 (B + 2)
      (Nat.le_of_lt (card_compl_matching_endpoints_lt_add_two
        X Y cL cR U B hU hsmall)) using 1 <;> norm_num

/-- If the full normalized head degree is at least `base+80ηN`, maximal-matching
coverage and the paper's `(ηℓ+2)s ≤ 2ηN` estimate leave at least
`base+78ηN` toward matching endpoints. -/
lemma matching_head_degree_lower
    (base η N full matched outside : ℝ)
    (hfull : base + 80 * η * N ≤ full)
    (hsplit : full ≤ matched + outside)
    (hout : outside ≤ 2 * η * N) :
    base + 78 * η * N ≤ matched := by
  linarith

end Erdos550
