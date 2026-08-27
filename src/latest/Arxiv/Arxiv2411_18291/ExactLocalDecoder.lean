import Arxiv.Arxiv2411_18291.DecoderCoefficient

/-! # The local decoder as a function of the root-clique intersection -/

open Finset
open scoped BigOperators

namespace Arxiv2411_18291

variable {V : Type*} [DecidableEq V] {q r : ℕ}

theorem localDecoder_eq_coefficient (e : Block V r) (Q : Block V q) :
    localDecoder q e Q = decoderCoefficient q r (e.val \ Q.val).card := by
  unfold localDecoder
  rw [← sum_filter]
  have hfilter : e.val.powerset.filter (fun I => Disjoint I Q.val) =
      (e.val \ Q.val).powerset := by
    ext I
    simp [subset_sdiff]
  rw [hfilter, sum_powerset_apply_card (decoderWeight q r)]
  simp only [decoderCoefficient, nsmul_eq_mul]

theorem localDecoder_eq (hqr : r < q) (e : Block V r) (Q : Block V q) :
    localDecoder q e Q =
      (-1 : ℤ) ^ (e.val \ Q.val).card *
        ((q - r).ascFactorial (e.val \ Q.val).card : ℤ) *
          ((r - (e.val \ Q.val).card).factorial : ℤ) := by
  rw [localDecoder_eq_coefficient]
  exact decoderCoefficient_eq q r _ hqr (by
    simpa only [e.property] using card_le_card (sdiff_subset : e.val \ Q.val ⊆ e.val))

theorem abs_localDecoder_eq (hqr : r < q) (e : Block V r) (Q : Block V q) :
    |localDecoder q e Q| =
      ((q - r).ascFactorial (e.val \ Q.val).card *
        (r - (e.val \ Q.val).card).factorial : ℕ) := by
  rw [localDecoder_eq hqr]
  simp [abs_mul, abs_pow]

end Arxiv2411_18291
