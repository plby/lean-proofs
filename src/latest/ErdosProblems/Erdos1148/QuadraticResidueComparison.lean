import ErdosProblems.Erdos1148.QuadraticIdealCoefficient
import ErdosProblems.Erdos1148.CoprimeConvolutionAsymptotic

/-! # Comparing the quadratic residue with a restricted Dirichlet convolution -/

namespace Erdos1148.DukeArithmetic

open NumberField Ideal Finset Filter Topology

lemma ideal_norm_count_sum_Ioc_le {K : Type*} [Field K] [NumberField K] (X : ℕ) :
    (∑ n ∈ Ioc 0 X, Nat.card {I : Ideal (𝓞 K) // absNorm I = n}) ≤
      Nat.card {I : Ideal (𝓞 K) // absNorm I ≤ X} := by
  rw [← Finset.card_preimage_eq_sum_card_image_eq
    (fun n _ => finite_setOfPred_absNorm_eq n)]
  have : Finite {I : Ideal (𝓞 K) // absNorm I ≤ X} := finite_setOfPred_absNorm_le X
  exact Nat.card_le_card_of_injective
    (fun I => ⟨I.val, (Finset.mem_Ioc.mp I.prop).2⟩)
    (fun I J h => Subtype.ext
      (congrArg (fun L : {I : Ideal (𝓞 K) // absNorm I ≤ X} => L.val) h))

theorem quadratic_residue_ge_principalMean_mul_LValue (a : ℕ) [NeZero a]
    [hns : Fact (¬IsSquare (a : ℤ))] {t : ℤ × ℤ × ℤ} (ht : discr t = (a : ℤ)) :
    principalCharacterMean (4 * a) * realDirichletValue (quadraticDirichletCharacter a) 1 ≤
      NumberField.dedekindZeta_residue (QuadraticDiscrAlgebra (a : ℤ)) := by
  have hnsNat : ¬IsSquare a := by
    rintro ⟨b, hb⟩
    apply hns.out
    exact ⟨(b : ℤ), by exact_mod_cast hb⟩
  have hL := coprime_convolution_sum_div_sq_tendsto (quadraticDirichletCharacter a)
    (quadraticDirichletCharacter_ne_one a hnsNat)
  have hN : Tendsto (fun N : ℕ => (N : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop
  have hR := (NumberField.Ideal.tendsto_norm_le_div_atTop
    (QuadraticDiscrAlgebra (a : ℤ))).comp hN
  apply le_of_tendsto_of_tendsto hL hR
  filter_upwards [] with N
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have hsum := sum_le_sum (fun n (_ : n ∈ Ioc 0 (N * N)) => quadratic_convolution_le_ideal_count a ht n)
  have hcount := ideal_norm_count_sum_Ioc_le (K := QuadraticDiscrAlgebra (a : ℤ)) (N * N)
  have hsum' : (∑ n ∈ Ioc 0 (N * N), realCoprimeZetaConvolution (quadraticDirichletCharacter a) n) ≤
      (Nat.card {I : Ideal (𝓞 (QuadraticDiscrAlgebra (a : ℤ))) // absNorm I ≤ N * N} : ℝ) :=
    hsum.trans (by exact_mod_cast hcount)
  simpa only [pow_two, ← Nat.cast_mul, Nat.cast_le] using hsum'

end Erdos1148.DukeArithmetic
