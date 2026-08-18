/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Reduction.Normalization
import ErdosProblems.Erdos186.PZ.Reduction.Estimates

/-!
# The initial normalized-box estimate

After translating the original input box by its lower corner, the comparison
GAP contains both zero and the selected CFP core and has volume exactly the
cardinality of the original box.  Lemma 6 therefore gives the initial
high-rank saving without any hidden centering assumption.
-/

namespace Erdos186.PZ.Reduction

noncomputable section

variable {ℓ s D k loss : ℕ}
  {A : Finset (LatticePoint ℓ)}

/-- The normalized CFP core and zero lie in the standard GAP presentation of
the normalized original box. -/
theorem initialCore_subset_normalizedBoxGAP
    (B : CFP.IntegerBox ℓ) (hA : A.Nonempty) (hAB : A ⊆ B.carrier)
    (W : CFP.EnhancedCFPWitness (normalizeSet B A) s D k loss) :
    insert 0 W.core ⊆
      (CFP.IntegerBox.toGAP (normalizedBox B)
        (normalized_nonempty B (hA.mono hAB))).carrier := by
  rw [CFP.IntegerBox.toGAP_carrier]
  intro x hx
  rw [Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · exact zero_mem_normalized B (hA.mono hAB)
  · exact normalizeSet_subset_normalized B hAB (W.core_subset hx)

/-- Exact initial high-rank estimate in Lemma 10.  The comparison volume is
literally `|B|`, and normalization costs no cardinality factor. -/
theorem initial_dimensionIncrease
    (B : CFP.IntegerBox ℓ) (hA : A.Nonempty) (hAB : A ⊆ B.carrier)
    (W : CFP.EnhancedCFPWitness (normalizeSet B A) s D k loss)
    (hrank : ℓ ≤ W.rank) :
    k ^ (W.rank - ℓ) * W.progression.volume ≤
      2 ^ W.rank * (2 * W.scaleDen) ^ ℓ * B.carrier.card := by
  let hB : B.carrier.Nonempty := hA.mono hAB
  let hNB : (normalizedBox B).carrier.Nonempty := normalized_nonempty B hB
  let Q := CFP.IntegerBox.toGAP (normalizedBox B) hNB
  calc
    k ^ (W.rank - ℓ) * W.progression.volume ≤
        2 ^ W.rank * (2 * W.scaleDen) ^ ℓ * Q.volume :=
      Estimates.cfpWitness_dimensionIncrease W Q
        (initialCore_subset_normalizedBoxGAP B hA hAB W) hrank
    _ = 2 ^ W.rank * (2 * W.scaleDen) ^ ℓ * B.carrier.card := by
      rw [CFP.IntegerBox.toGAP_volume]
      exact congrArg (fun n : ℕ ↦
        2 ^ W.rank * (2 * W.scaleDen) ^ ℓ * n) (card_normalized B)

end

end Erdos186.PZ.Reduction
