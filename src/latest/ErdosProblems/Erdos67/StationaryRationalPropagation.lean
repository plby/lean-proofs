import ErdosProblems.Erdos67.StationaryRationalUniformity

/-!
# Propagation of rational atom masses to larger denominators

If a prime divides the order of a rational frequency, every root under that
prime dilation has the multiplied order. Uniformity within each order and
the finite size of a dilation fiber give the square-factor mass inequality.
-/

open scoped BigOperators
open Finset MeasureTheory

namespace Erdos67.StationaryModel

theorem exists_primitiveFrequency_of_order (q : ℕ+) (θ : FrequencyCircle)
    (hθ : addOrderOf θ = q.val) : ∃ a : (ZMod q.val)ˣ, primitiveFrequency q a = θ := by
  obtain ⟨m, _, hg, he⟩ := (AddCircle.addOrderOf_eq_pos_iff (p := (1 : ℝ)) q.pos).mp hθ
  refine ⟨ZMod.unitOfCoprime m hg, ?_⟩
  simpa only [primitiveFrequency, ZMod.coe_unitOfCoprime, ZMod.toAddCircle_natCast,
    mul_one] using he

theorem prime_root_order_of_dvd {η θ : FrequencyCircle} {q p : ℕ}
    (hq : 0 < q) (hp : p.Prime) (hpq : p ∣ q)
    (hη : addOrderOf η = q) (hθ : p • θ = η) : addOrderOf θ = p * q := by
  rcases prime_root_order_cases hq hp hη hθ with he | he
  · have ht : IsOfFinAddOrder θ := by
      apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
      exact ⟨q, hq, he ▸ addOrderOf_nsmul_eq_zero θ⟩
    have hh := IsOfFinAddOrder.addOrderOf_nsmul θ p ht
    rw [hθ, hη, he, Nat.gcd_eq_right hpq] at hh
    exact False.elim ((Nat.div_lt_self hq hp.one_lt).ne hh.symm)
  · exact he

theorem exists_finset_dilation_fiber (d : ℕ+) (η : FrequencyCircle) :
    ∃ s : Finset FrequencyCircle, (s : Set FrequencyCircle) = {θ | d.val • θ = η} ∧
      s.card ≤ d.val := by
  classical
  by_cases he : ∃ ξ : FrequencyCircle, d.val • ξ = η
  · obtain ⟨ξ, hξ⟩ := he
    have hK := AddCircle.finite_torsion (1 : ℝ) d.pos
    have hc := AddCircle.card_torsion_le_of_isSMulRegular (1 : ℝ) d.val d.pos.ne'
      (IsSMulRegular.of_right_eq_zero_of_smul (fun _ ↦ by simp [d.pos.ne']))
    rw [hK.encard_eq_coe_toFinset_card] at hc
    have hcard : hK.toFinset.card ≤ d.val := by exact_mod_cast hc
    refine ⟨hK.toFinset.image (fun θ ↦ θ + ξ), ?_, (card_image_le.trans hcard)⟩
    ext θ
    simp only [coe_image, Set.mem_image, hK.coe_toFinset, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [nsmul_add, hx, zero_add, hξ]
    · intro hθ
      refine ⟨θ - ξ, ?_, sub_add_cancel θ ξ⟩
      rw [nsmul_sub, hθ, hξ, sub_self]
  · refine ⟨∅, ?_, by simp⟩
    ext θ
    simp only [coe_empty, Set.mem_empty_iff_false, Set.mem_ofPred_eq, false_iff]
    exact fun hθ ↦ he ⟨θ, hθ⟩

noncomputable def rationalAtomMass (σ : ProbabilityMeasure FrequencyCircle) (q : ℕ+) : ℝ :=
  (σ : Measure FrequencyCircle).real {primitiveFrequency q 1}

theorem atom_mass_eq_of_order (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (hCD : ∀ (d : ℕ+) (F : C((ℤ → Bool), ℝ)),
      (∫ ω, F ω.1 ∂(Q : Measure Configuration)) =
        (d.val : ℝ) * ∫ ω, conditionalDilationTest d F ω ∂(Q : Measure Configuration))
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ)
    (q : ℕ+) (θ : FrequencyCircle) (hθ : addOrderOf θ = q.val) :
    (σ : Measure FrequencyCircle).real {θ} = rationalAtomMass σ q := by
  obtain ⟨a, rfl⟩ := exists_primitiveFrequency_of_order q θ hθ
  exact primitive_atom_masses_equal Q hQ hCD σ hσ q a 1

theorem rational_atom_mass_le_prime_square (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (hCD : ∀ (d : ℕ+) (F : C((ℤ → Bool), ℝ)),
      (∫ ω, F ω.1 ∂(Q : Measure Configuration)) =
        (d.val : ℝ) * ∫ ω, conditionalDilationTest d F ω ∂(Q : Measure Configuration))
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ)
    (q : ℕ+) (p : ℕ) (hp : p.Prime) (hpq : p ∣ q.val) :
    rationalAtomMass σ q ≤ (p : ℝ) ^ 2 * rationalAtomMass σ (⟨p, hp.pos⟩ * q) := by
  classical
  let η := primitiveFrequency q 1
  let d : ℕ+ := ⟨p, hp.pos⟩
  obtain ⟨s, hs, hc⟩ := exists_finset_dilation_fiber d η
  have hm (θ : FrequencyCircle) (hθ : θ ∈ s) :
      (σ : Measure FrequencyCircle).real {θ} = rationalAtomMass σ (d * q) := by
    apply atom_mass_eq_of_order Q hQ hCD σ hσ (d * q) θ
    have hroot : p • θ = η := by
      have ht : θ ∈ (s : Set FrequencyCircle) := hθ
      rw [hs] at ht
      exact ht
    exact prime_root_order_of_dvd q.pos hp hpq (primitiveFrequency_order q 1) hroot
  have hf : (σ : Measure FrequencyCircle).real {θ | p • θ = η} ≤
      (p : ℝ) * rationalAtomMass σ (d * q) := by
    change (σ : Measure FrequencyCircle).real {θ | d.val • θ = η} ≤ _
    rw [← hs, ← sum_measureReal_singleton]
    calc
      _ = (s.card : ℝ) * rationalAtomMass σ (d * q) := by
        rw [sum_congr rfl hm, sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) measureReal_nonneg
  have ht := spectral_atom_transport Q hQ hCD σ hσ η d
  calc
    rationalAtomMass σ q ≤ (p : ℝ) * (σ : Measure FrequencyCircle).real
        {θ | p • θ = η} := ht
    _ ≤ (p : ℝ) * ((p : ℝ) * rationalAtomMass σ (d * q)) :=
      mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg _)
    _ = _ := by ring

end Erdos67.StationaryModel
