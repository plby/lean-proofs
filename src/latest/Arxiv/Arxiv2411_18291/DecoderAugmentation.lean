import Arxiv.Arxiv2411_18291.CliqueSupportBounds
import Arxiv.Arxiv2411_18291.SparseLocalDecoders
import Arxiv.Arxiv2411_18291.ColourProbabilityNumerics

/-!
# Augmenting a sparse family with local decoders

For any fixed loss in the density exponent, a bounded clique family can
be enlarged to decode every multiple of the decoder modulus supported
on its original edge support. All choices are uniform over the input
vectors that will later be decoded.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem eventually_augment_with_local_decoders (q r : ℕ) (hq : r + 1 ≤ q)
    {C s t : ℝ} (ht : 0 < t) (hts : t < s) (hs1 : s < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ F : Finset (Block (Fin n) q),
      IsCliqueFamilyBounded r F (C * (n : ℝ) ^ (-s)) →
      ∃ D : Finset (Block (Fin n) q), F ⊆ D ∧
        IsCliqueFamilyBounded r D ((n : ℝ) ^ (-t)) ∧
        ∀ J : Block (Fin n) (r + 1) → ℤ,
          (∀ e, e ∉ cliqueSupport (r + 1) F → J e = 0) →
          (∀ e, (((r + 1).factorial * q.choose (r + 1) : ℕ) : ℤ) ∣ J e) → GeneratedBy D J := by
  let η := (s + t) / 2
  let K : ℝ := q.choose (r + 1) *
    (1 + 4 * (r + 1).factorial * (q + (r + 1)).choose (r + 1))
  have hη : 0 < η := by dsimp only [η]; linarith only [ht, hts]
  have hη1 : η < 1 := by dsimp only [η]; linarith only [hts, hs1]
  have htη : t < η := by dsimp only [η]; linarith only [hts]
  have hηs : η < s := by dsimp only [η]; linarith only [hts]
  filter_upwards [eventually_const_mul_rpow_le C hηs,
    eventually_exists_bounded_local_decoder_family hq hη hη1,
    eventually_const_mul_rpow_le (1 + K) htη] with n hsmall hdecode hsum
  intro F hF
  have hFη := hF.mono hsmall
  obtain ⟨D₀, hD₀, _, hD₀b⟩ := hdecode (cliqueSupport (r + 1) F) hFη.support_graphBounded
  refine ⟨F ∪ D₀, subset_union_left, ?_, fun J hs hd => ?_⟩
  · have hu : IsCliqueFamilyBounded r (F ∪ D₀) ((1 + K) * (n : ℝ) ^ (-η)) := by
      simpa only [add_mul, one_mul, K] using hFη.union hD₀b
    exact hu.mono hsum
  · exact (hD₀.generates_multiples J hs hd).mono subset_union_right

end Arxiv2411_18291
