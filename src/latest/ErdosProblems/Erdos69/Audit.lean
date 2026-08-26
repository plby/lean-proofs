import ErdosProblems.Erdos69

/-! # Dependency audit for the exact theorem and its main ingredients

Every declaration below depends only on Lean's standard axioms
`propext`, `Classical.choice`, and `Quot.sound`.
-/

#check Erdos69.irrational_omega_series
#print axioms Erdos69.irrational_omega_series
#print axioms Erdos69.Elementary.irrational_binaryOmegaSum
#print axioms Erdos69.Elementary.summable_omegaCount_div_two_pow
#print axioms Erdos69.Elementary.binaryOmegaSum_eq_tsum_from_two
#print axioms Erdos69.Elementary.tendsto_fullCharacteristic_norm
#print axioms Erdos69.Elementary.tendsto_full_sub_one_norm_of_rational

#print axioms Erdos69.Elementary.patternSignedSum_vanish
#print axioms Erdos69.Elementary.FiniteLaw.affine_fourier_transfer
#print axioms Erdos69.Elementary.FiniteLaw.categorical_product_fourier_le
#print axioms Erdos69.Elementary.FiniteLaw.rational_signed_tail_phase_le
#print axioms Erdos69.Elementary.exists_primeReciprocal_error_constant
#print axioms Erdos69.Elementary.arithmeticTail_truncation_error
#print axioms Erdos69.Elementary.log_constructionUpperBound_le
#print axioms Erdos69.Elementary.tendsto_coefficientMassBound_affine
#print axioms Erdos69.Elementary.tendsto_scale_tail
#print axioms Erdos69.Elementary.tendsto_independent_decay
