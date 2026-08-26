import ErdosProblems.Erdos336.FourierFourFifthsAlmost
import ErdosProblems.Erdos336.StableHighPowerCertificateV3

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped BigOperators Pointwise

variable {N : ℕ} [NeZero N]

noncomputable def lowOrderFrequencies (N : ℕ) [NeZero N] (q : ℕ) :
    Finset (ZMod N) :=
  Finset.univ.filter fun k => addOrderOf k ≤ q

lemma lowOrderFrequencies_subset_factorial_torsion (q : ℕ) :
    lowOrderFrequencies N q ⊆
      (Finset.univ.filter fun k : ZMod N => q.factorial • k = 0) := by
  intro k hk
  simp only [lowOrderFrequencies, Finset.mem_filter, Finset.mem_univ,
    true_and] at hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← addOrderOf_dvd_iff_nsmul_eq_zero]
  exact Nat.dvd_factorial (addOrderOf_pos k) hk

lemma card_lowOrderFrequencies_le_factorial (q : ℕ) :
    (lowOrderFrequencies N q).card ≤ q.factorial := by
  calc
    (lowOrderFrequencies N q).card ≤
        (Finset.univ.filter fun k : ZMod N => q.factorial • k = 0).card :=
      Finset.card_le_card (lowOrderFrequencies_subset_factorial_torsion q)
    _ ≤ q.factorial :=
      IsAddCyclic.card_nsmul_eq_zero_le (Nat.factorial_pos q)

lemma norm_cyclicFinsetFourier_le_card
    (A : Finset (ZMod N)) (k : ZMod N) :
    ‖cyclicFinsetFourier A k‖ ≤ A.card := by
  calc
    ‖cyclicFinsetFourier A k‖ ≤ (fourierPositiveHalf A k).card :=
      norm_fourier_le_card_positiveHalf A k
    _ ≤ A.card := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

end Erdos336
