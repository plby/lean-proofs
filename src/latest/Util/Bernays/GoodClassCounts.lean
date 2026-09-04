import Util.Bernays.GenusNorms
import Util.Bernays.SquareExceptionalUnion

/-!
# Class counts differ from genus counts by a negligible exceptional set
-/

open Filter Topology
open scoped Classical

namespace Bernays

noncomputable def goodClassValues {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ClassGroup (QuadraticAlgebra ℤ d b) → ℕ → Finset ℕ :=
  letI := quadraticOrderIsDomain hD
  fun C N => (Finset.Icc 1 N).filter fun n =>
    n.Coprime (discriminantLevel (b ^ 2 + 4 * d)) ∧
      ∃ I : InvertibleIdeal (QuadraticAlgebra ℤ d b),
        (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = n ∧ I.idealClass = C

noncomputable def genusValues {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    GenusGroup (QuadraticAlgebra ℤ d b) → ℕ → Finset ℕ :=
  letI := quadraticOrderIsDomain hD
  fun g N => (localValues (fun p : ℕ => discriminantCharacter (b ^ 2 + 4 * d) hD.ne p = -1) N).filter
    fun n => n.Coprime (discriminantLevel (b ^ 2 + 4 * d)) ∧ genusValue hD n = g

theorem goodClassValues_subset_genusValues {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ C : ClassGroup (QuadraticAlgebra ℤ d b), ∀ N : ℕ,
      goodClassValues hD C N ⊆ genusValues hD (genusMap C) N := by
  let := quadraticOrderIsDomain hD
  intro C N n hn
  obtain ⟨hnN, hnc, I, hIn, hIc⟩ := Finset.mem_filter.mp hn
  have hIF : IsCoprime (I : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) :=
    I.coprime_scalar_of_cardQuot_coprime _ (hIn.symm ▸ hnc)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨hnN, ?_⟩, hnc, ?_⟩
  · simpa only [hIn] using local_of_goodIdeal_norm hD I hIF
  · simpa only [hIn, hIc] using genusValue_goodIdeal_norm hD I hIF

theorem genusValues_sdiff_class_subset_exceptional {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ C : ClassGroup (QuadraticAlgebra ℤ d b), ∀ N : ℕ,
      genusValues hD (genusMap C) N \ goodClassValues hD C N ⊆ squareExceptionalValues hD
        (Nat.card (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b)))) N := by
  let := quadraticOrderIsDomain hD
  intro C N n hn
  obtain ⟨hng, hnot⟩ := Finset.mem_sdiff.mp hn
  obtain ⟨hnlocal, hnc, hngen⟩ := Finset.mem_filter.mp hng
  have hnpos : 0 < n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hnlocal).1).1
  obtain ⟨I, hIn⟩ := exists_ideal_norm_of_local hD n hnpos hnc (Finset.mem_filter.mp hnlocal).2
  have hIF : IsCoprime (I : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) :=
    I.coprime_scalar_of_cardQuot_coprime _ (hIn.symm ▸ hnc)
  have hIC : genusMap I.idealClass = genusMap C := by
    rw [← genusValue_goodIdeal_norm hD I hIF, hIn]
    exact hngen
  have hmiss (J : InvertibleIdeal (QuadraticAlgebra ℤ d b))
      (hJn : (J : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot) :
      J.idealClass ≠ C := by
    intro hJc
    exact hnot (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hnlocal).1, hnc, J, hJn.trans hIn, hJc⟩)
  simpa only [hIn] using missing_same_genus_mem_exceptional hD I hIF C hIC hmiss N (hIn.symm ▸ hnlocal)

theorem goodClass_genus_count_error_limit {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ C : ClassGroup (QuadraticAlgebra ℤ d b),
      Tendsto (fun N : ℕ =>
        (((genusValues hD (genusMap C) N).card : ℝ) - (goodClassValues hD C N).card) / scale N)
        atTop (𝓝 0) := by
  let := quadraticOrderIsDomain hD
  intro C
  let k := Nat.card (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b)))
  have heq (N : ℕ) : ((genusValues hD (genusMap C) N).card : ℝ) - (goodClassValues hD C N).card =
      ((genusValues hD (genusMap C) N \ goodClassValues hD C N).card : ℝ) := by
    have h := Finset.card_sdiff_add_card_eq_card (goodClassValues_subset_genusValues hD C N)
    have h' : ((genusValues hD (genusMap C) N \ goodClassValues hD C N).card : ℝ) +
        (goodClassValues hD C N).card = (genusValues hD (genusMap C) N).card := by exact_mod_cast h
    linarith
  apply squeeze_zero _ _ (squareExceptionalValues_div_scale_tendsto_zero hD k)
  · intro N
    rw [heq N]
    exact div_nonneg (Nat.cast_nonneg _) (div_nonneg (Nat.cast_nonneg N) (Real.sqrt_nonneg _))
  · intro N
    rw [heq N]
    apply div_le_div_of_nonneg_right _ (div_nonneg (Nat.cast_nonneg N) (Real.sqrt_nonneg _))
    exact_mod_cast Finset.card_le_card (genusValues_sdiff_class_subset_exceptional hD C N)

end Bernays
