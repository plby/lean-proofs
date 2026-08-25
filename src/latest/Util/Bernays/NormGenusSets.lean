import Util.Bernays.GoodClassAsymptotic

/-!
# The finite genus sets of ideals of a prescribed norm
-/

open scoped Classical

namespace Bernays

noncomputable def normGenusSet {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) (m : ℕ) :
    letI := quadraticOrderIsDomain hD
    Finset (GenusGroup (QuadraticAlgebra ℤ d b)) := by
  letI := quadraticOrderIsDomain hD
  letI := quadraticOrderClassGroupFintype hD
  letI : Fintype (GenusGroup (QuadraticAlgebra ℤ d b)) := Fintype.ofFinite _
  exact Finset.univ.filter fun g => ∃ J : InvertibleIdeal (QuadraticAlgebra ℤ d b),
    (J : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = m ∧ genusMap J.idealClass = g

theorem mem_normGenusSet {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) (m : ℕ) :
    letI := quadraticOrderIsDomain hD
    ∀ g : GenusGroup (QuadraticAlgebra ℤ d b),
      g ∈ normGenusSet hD m ↔ ∃ J : InvertibleIdeal (QuadraticAlgebra ℤ d b),
        (J : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = m ∧ genusMap J.idealClass = g := by
  letI := quadraticOrderIsDomain hD
  intro g
  simp only [normGenusSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem normGenusSet_one {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    normGenusSet hD 1 = {1} := by
  letI := quadraticOrderIsDomain hD
  ext g
  rw [mem_normGenusSet, Finset.mem_singleton]
  constructor
  · rintro ⟨J, hJ, hg⟩
    have hJ₁ : J = 1 := InvertibleIdeal.ext (Submodule.cardQuot_eq_one_iff.mp hJ)
    simpa only [hJ₁, InvertibleIdeal.idealClass_one, map_one] using hg.symm
  · intro hg
    refine ⟨1, ?_, ?_⟩
    · exact Submodule.cardQuot_top _ _
    · simp only [InvertibleIdeal.idealClass_one, map_one, hg]

noncomputable def remainderGenusSet {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ClassGroup (QuadraticAlgebra ℤ d b) → ℕ → Finset (GenusGroup (QuadraticAlgebra ℤ d b)) :=
  letI := quadraticOrderIsDomain hD
  fun C m => (normGenusSet hD m).image (fun g => genusMap C * g⁻¹)

theorem remainderGenusSet_card {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ C : ClassGroup (QuadraticAlgebra ℤ d b), ∀ m : ℕ,
      (remainderGenusSet hD C m).card = (normGenusSet hD m).card := by
  letI := quadraticOrderIsDomain hD
  intro C m
  apply Finset.card_image_of_injective
  intro g h heq
  exact inv_injective (mul_left_cancel heq)

theorem mem_remainderGenusSet {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (C : ClassGroup (QuadraticAlgebra ℤ d b)) (m : ℕ) (g : GenusGroup (QuadraticAlgebra ℤ d b)),
      g ∈ remainderGenusSet hD C m ↔ ∃ J : InvertibleIdeal (QuadraticAlgebra ℤ d b),
        (J : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = m ∧
          genusMap (C * J.idealClass⁻¹) = g := by
  letI := quadraticOrderIsDomain hD
  intro C m g
  rw [remainderGenusSet, Finset.mem_image]
  constructor
  · rintro ⟨h, hh, heq⟩
    obtain ⟨J, hJ, hgen⟩ := (mem_normGenusSet hD m h).mp hh
    refine ⟨J, hJ, ?_⟩
    rw [map_mul, map_inv, hgen]
    exact heq
  · rintro ⟨J, hJ, heq⟩
    refine ⟨genusMap J.idealClass, (mem_normGenusSet hD m _).mpr ⟨J, hJ, rfl⟩, ?_⟩
    simpa only [map_mul, map_inv] using heq

end Bernays
