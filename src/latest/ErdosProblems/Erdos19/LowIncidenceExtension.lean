import ErdosProblems.Erdos19.LowIncidenceColoring
import ErdosProblems.Erdos19.MediumExtension

/-! # Low-incidence extension when old palette edges have much larger rank -/

namespace Erdos19.SetHypergraph

open Finset

attribute [local instance] Classical.propDecidable

theorem eventually_color_low_incidence_around_large_palette (R s a : ℕ)
    (hR : 0 < R) (hs : 2 ≤ s) (ha : 0 < a) :
    ∃ ell N : ℕ, 2 ≤ ell ∧ ∀ n : ℕ, N ≤ n →
      ∀ L M : SetHypergraph (Fin n), L.IsLinear → M.IsLinear →
      ∀ color : L.EdgeColoring (Fin n), ∀ palette : Finset (Fin n),
        (∀ e : L, color e ∈ palette → ell * R ≤ e.1.ncard) →
        (∀ e : M, e.1.ncard ≤ R) →
        (∀ v, (M.incidentEdges v).ncard ≤ n - n / s) →
        16 * a * (∑ e : M, e.1.ncard) ≤ n ^ 2 →
        n - n / (2 * s) ≤ palette.card →
        ∃ c : M.EdgeColoring palette,
          (∀ e : M, ∀ f : L, (e.1 ∩ f.1).Nonempty → (c e).1 ≠ color f) ∧
          (∀ x, (M.coveredVertices {e | c e = x}).ncard ≤ n / a) := by
  classical
  obtain ⟨delta, hdelta, N, hN⟩ := eventually_low_incidence_covered_lists R s a hR hs ha
  obtain ⟨k, hk⟩ := exists_nat_ge (max 1 (1 / delta))
  have hkpos : 1 ≤ k := by exact_mod_cast ((le_max_left _ _).trans hk)
  have hdk : 1 ≤ delta * (k : ℝ) := by
    have h := (div_le_iff₀ hdelta).mp ((le_max_right _ _).trans hk)
    nlinarith only [h]
  let ell := k + 2
  have hlarge : 2 ≤ ell * R := by dsimp only [ell]; nlinarith only [hR]
  have hden : k * R ≤ ell * R - 1 := by
    have h : k * R + 1 ≤ ell * R := by dsimp only [ell]; nlinarith only [hR]
    omega
  refine ⟨ell, N, by dsimp only [ell]; omega, ?_⟩
  intro n hn L M hL hM color palette hmin hmax hdegree htotal hpalette
  let F : M → Finset palette := fun e ↦ L.forbiddenReservedColors color e.1 palette
  have hF : ∀ e, ((F e).card : ℝ) ≤ delta * n := by
    intro e
    have hcount := L.forbiddenReservedColors_card_le hL color e.1 palette
      (ell * R) hlarge hmin
    simp only [Fintype.card_fin] at hcount
    have hsize := Nat.mul_le_mul_right ((n - 1) / (ell * R - 1)) (hmax e)
    have hcard : (F e).card ≤ R * ((n - 1) / (ell * R - 1)) := hcount.trans hsize
    have hq := Nat.mul_div_le (n - 1) (ell * R - 1)
    have hqscale := Nat.mul_le_mul_right ((n - 1) / (ell * R - 1)) hden
    have hcardscale := Nat.mul_le_mul_left k hcard
    have hscaled : k * (F e).card ≤ n := by
      have hnsub := Nat.sub_le n 1
      nlinarith only [hq, hqscale, hcardscale, hnsub]
    have hscaledR : (k : ℝ) * (F e).card ≤ n := by exact_mod_cast hscaled
    have hmul := mul_le_mul_of_nonneg_left hscaledR hdelta.le
    have hunit := mul_le_mul_of_nonneg_right hdk (Nat.cast_nonneg (F e).card)
    nlinarith only [hmul, hunit]
  obtain ⟨c, hc, hcover⟩ := hN n hn M hM hmax hdegree htotal palette F hF
    (by simpa only [Fintype.card_coe] using hpalette)
  refine ⟨c, ?_, hcover⟩
  intro e f hinter heq
  exact hc e (mem_filter.mpr ⟨mem_univ _, f, heq.symm, hinter⟩)

#print axioms eventually_color_low_incidence_around_large_palette

end Erdos19.SetHypergraph
