import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.Fintype

/-! # A unit-density bound from the number of maximal ideals -/

namespace Erdos1148.DukeArithmetic

lemma isUnit_of_avoids_maximal {R : Type*} [CommRing R] (x : R)
    (hx : ∀ m : MaximalSpectrum R, x ∉ m.asIdeal) : IsUnit x := by
  by_contra hunit
  obtain ⟨M, hM, hxM⟩ := Ideal.exists_le_maximal (Ideal.span {x})
    (fun h => hunit (Ideal.span_singleton_eq_top.mp h))
  exact hx ⟨M, hM⟩ (hxM (Ideal.subset_span (Set.mem_singleton x)))

theorem finite_ring_card_le_pow_maximal_mul_units (R : Type*) [CommRing R] [Finite R] :
    Nat.card R ≤ 2 ^ Nat.card (MaximalSpectrum R) * Nat.card Rˣ := by
  classical
  let := Fintype.ofFinite R
  let := Fintype.ofFinite (MaximalSpectrum R)
  have hcop : Pairwise (fun m n : MaximalSpectrum R => IsCoprime m.asIdeal n.asIdeal) := by
    intro m n hmn
    exact Ideal.isCoprime_of_isMaximal (fun h => hmn (MaximalSpectrum.ext h))
  have hex : ∀ s : Finset (MaximalSpectrum R), ∃ r : R,
      ∀ m : MaximalSpectrum R, Ideal.Quotient.mk m.asIdeal r = if m ∈ s then 1 else 0 := by
    intro s
    exact Ideal.pi_quotient_surjective hcop (fun m => if m ∈ s then 1 else 0)
  choose r hr using hex
  let F : Finset (MaximalSpectrum R) × Rˣ → R := fun z => (z.2 : R) - r z.1
  have hF : Function.Surjective F := by
    intro x
    let s : Finset (MaximalSpectrum R) := Finset.univ.filter (fun m => x ∈ m.asIdeal)
    have hu : IsUnit (x + r s) := by
      apply isUnit_of_avoids_maximal
      intro m hm
      have heq := Ideal.Quotient.eq_zero_iff_mem.mpr hm
      rw [map_add, hr] at heq
      by_cases hx : x ∈ m.asIdeal
      · have hs : m ∈ s := by simp [s, hx]
        rw [if_pos hs, Ideal.Quotient.eq_zero_iff_mem.mpr hx, zero_add] at heq
        exact one_ne_zero heq
      · have hs : m ∉ s := by simp [s, hx]
        rw [if_neg hs, add_zero] at heq
        exact hx (Ideal.Quotient.eq_zero_iff_mem.mp heq)
    obtain ⟨u, hu⟩ := hu
    refine ⟨(s, u), ?_⟩
    change (u : R) - r s = x
    rw [hu, add_sub_cancel_right]
  have hcard := Nat.card_le_card_of_surjective F hF
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_finset] using hcard

end Erdos1148.DukeArithmetic
