import Util.Bernays.GenusSlices
import Util.Bernays.SmoothDecomposition
import Util.Bernays.CoprimeIdealDecomposition

/-!
# Class slices and their common negligible exceptional set
-/

open Filter Topology
open scoped Classical

namespace Bernays

noncomputable def classSliceValues {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ClassGroup (QuadraticAlgebra ℤ d b) → ℕ → ℕ → Finset ℕ :=
  letI := quadraticOrderIsDomain hD
  fun C m N => (Finset.Icc 1 N).filter fun n =>
    n.Coprime (discriminantLevel (b ^ 2 + 4 * d)) ∧
      ∃ I : InvertibleIdeal (QuadraticAlgebra ℤ d b),
        (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = m * n ∧ I.idealClass = C

theorem classSliceValues_subset_genusSliceValues {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (C : ClassGroup (QuadraticAlgebra ℤ d b)) (m : ℕ),
      m ∈ Nat.factoredNumbers (discriminantLevel (b ^ 2 + 4 * d)).primeFactors →
      ∀ N : ℕ, classSliceValues hD C m N ⊆ genusSliceValues hD C m N := by
  let := quadraticOrderIsDomain hD
  intro C m hm N n hn
  obtain ⟨hnN, hnc, I, hIn, hIC⟩ := Finset.mem_filter.mp hn
  obtain ⟨J, K, hJK, hJ, hK⟩ := exists_coprime_norm_factors hD I m n
    (factored_coprime_of_coprime_level hm hnc) hIn
  have hKF : IsCoprime (K : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) :=
    K.coprime_scalar_of_cardQuot_coprime _ (hK.symm ▸ hnc)
  have hclass : K.idealClass = C * J.idealClass⁻¹ := by
    rw [← hIC, ← hJK, InvertibleIdeal.idealClass_mul]
    rw [mul_comm J.idealClass K.idealClass, mul_assoc, mul_inv_cancel, mul_one]
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hnN,
      by simpa only [hK] using local_of_goodIdeal_norm hD K hKF⟩, hnc⟩
  · apply (mem_remainderGenusSet hD C m (genusValue hD n)).mpr
    refine ⟨J, hJ, ?_⟩
    rw [← hclass, ← genusValue_goodIdeal_norm hD K hKF, hK]

theorem genusSlice_sdiff_classSlice_subset_exceptional {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (C : ClassGroup (QuadraticAlgebra ℤ d b)) (m N : ℕ),
      genusSliceValues hD C m N \ classSliceValues hD C m N ⊆ squareExceptionalValues hD
        (Nat.card (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b)))) N := by
  let := quadraticOrderIsDomain hD
  intro C m N n hn
  obtain ⟨hng, hnot⟩ := Finset.mem_sdiff.mp hn
  obtain ⟨hngood, hngen⟩ := Finset.mem_filter.mp hng
  obtain ⟨hnlocal, hnc⟩ := Finset.mem_filter.mp hngood
  obtain ⟨hnN, hnpar⟩ := Finset.mem_filter.mp hnlocal
  have hn₀ : 0 < n := (Finset.mem_Icc.mp hnN).1
  obtain ⟨J, hJ, hJgen⟩ := (mem_remainderGenusSet hD C m (genusValue hD n)).mp hngen
  obtain ⟨K, hK⟩ := exists_ideal_norm_of_local hD n hn₀ hnc hnpar
  have hKF : IsCoprime (K : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) :=
    K.coprime_scalar_of_cardQuot_coprime _ (hK.symm ▸ hnc)
  have hgen : genusMap K.idealClass = genusMap (C * J.idealClass⁻¹) := by
    rw [← genusValue_goodIdeal_norm hD K hKF, hK]
    exact hJgen.symm
  have hmiss (L : InvertibleIdeal (QuadraticAlgebra ℤ d b))
      (hL : (L : Ideal (QuadraticAlgebra ℤ d b)).cardQuot =
        (K : Ideal (QuadraticAlgebra ℤ d b)).cardQuot) : L.idealClass ≠ C * J.idealClass⁻¹ := by
    intro hLC
    apply hnot
    apply Finset.mem_filter.mpr
    refine ⟨hnN, hnc, J * L, ?_, ?_⟩
    · rw [InvertibleIdeal.cardQuot_mul, hJ, hL, hK]
    · rw [InvertibleIdeal.idealClass_mul, hLC]
      rw [mul_left_comm, mul_inv_cancel, mul_one]
  have hex := missing_same_genus_mem_exceptional hD K hKF (C * J.idealClass⁻¹) hgen hmiss N
    (hK.symm ▸ hnlocal)
  simpa only [hK] using hex

theorem classSlice_genus_count_error_limit {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (C : ClassGroup (QuadraticAlgebra ℤ d b)) (m : ℕ),
      m ∈ Nat.factoredNumbers (discriminantLevel (b ^ 2 + 4 * d)).primeFactors →
      Tendsto (fun N : ℕ =>
        (((genusSliceValues hD C m N).card : ℝ) - (classSliceValues hD C m N).card) / scale N)
        atTop (𝓝 0) := by
  let := quadraticOrderIsDomain hD
  intro C m hm
  let k := Nat.card (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b)))
  have heq (N : ℕ) : ((genusSliceValues hD C m N).card : ℝ) - (classSliceValues hD C m N).card =
      ((genusSliceValues hD C m N \ classSliceValues hD C m N).card : ℝ) := by
    have h := Finset.card_sdiff_add_card_eq_card (classSliceValues_subset_genusSliceValues hD C m hm N)
    have h' : ((genusSliceValues hD C m N \ classSliceValues hD C m N).card : ℝ) +
        (classSliceValues hD C m N).card = (genusSliceValues hD C m N).card := by exact_mod_cast h
    linarith
  apply squeeze_zero _ _ (squareExceptionalValues_div_scale_tendsto_zero hD k)
  · intro N
    rw [heq N]
    exact div_nonneg (Nat.cast_nonneg _) (div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
  · intro N
    rw [heq N]
    apply div_le_div_of_nonneg_right _ (div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
    exact_mod_cast Finset.card_le_card (genusSlice_sdiff_classSlice_subset_exceptional hD C m N)

theorem classSliceValues_card_limit {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (C : ClassGroup (QuadraticAlgebra ℤ d b)) (m : ℕ),
      m ∈ Nat.factoredNumbers (discriminantLevel (b ^ 2 + 4 * d)).primeFactors →
      Tendsto (fun N : ℕ => ((classSliceValues hD C m N).card : ℝ) / scale N)
        atTop (𝓝 (goodClassConstant hD * (normGenusSet hD m).card)) := by
  let := quadraticOrderIsDomain hD
  intro C m hm
  have h := (genusSliceValues_card_limit hD C m).sub (classSlice_genus_count_error_limit hD C m hm)
  rw [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  change ((genusSliceValues hD C m N).card : ℝ) / scale N -
    (((genusSliceValues hD C m N).card : ℝ) - (classSliceValues hD C m N).card) / scale N = _
  ring

end Bernays
