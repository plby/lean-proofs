import ErdosProblems.Erdos19.ReservedColorConflicts

/-! # A fixed rank separation makes inherited forbidden lists sparse -/

namespace Erdos19.SetHypergraph

theorem exists_rank_separation_for_forbidden_colors (R : ℕ) (hR : 0 < R)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ ell : ℕ, 2 ≤ ell ∧ ∀ n : ℕ, ∀ L : SetHypergraph (Fin n), L.IsLinear →
      ∀ m : ℕ, ∀ color : L.EdgeColoring (Fin m), ∀ palette : Finset (Fin m),
        (∀ e : L, color e ∈ palette → ell * R ≤ e.1.ncard) →
        ∀ S : Set (Fin n), S.ncard ≤ R →
          ((L.forbiddenReservedColors color S palette).card : ℝ) ≤ delta * n := by
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
  refine ⟨ell, by dsimp only [ell]; omega, ?_⟩
  intro n L hL m color palette hmin S hS
  let F := L.forbiddenReservedColors color S palette
  have hcount := L.forbiddenReservedColors_card_le hL color S palette (ell * R) hlarge hmin
  simp only [Fintype.card_fin] at hcount
  have hsize := Nat.mul_le_mul_right ((n - 1) / (ell * R - 1)) hS
  have hcard : F.card ≤ R * ((n - 1) / (ell * R - 1)) := hcount.trans hsize
  have hq := Nat.mul_div_le (n - 1) (ell * R - 1)
  have hqscale := Nat.mul_le_mul_right ((n - 1) / (ell * R - 1)) hden
  have hcardscale := Nat.mul_le_mul_left k hcard
  have hscaled : k * F.card ≤ n := by
    have hnsub := Nat.sub_le n 1
    nlinarith only [hq, hqscale, hcardscale, hnsub]
  have hscaledR : (k : ℝ) * F.card ≤ n := by exact_mod_cast hscaled
  have hmul := mul_le_mul_of_nonneg_left hscaledR hdelta.le
  have hunit := mul_le_mul_of_nonneg_right hdk (Nat.cast_nonneg F.card)
  change (F.card : ℝ) ≤ delta * n
  nlinarith only [hmul, hunit]

#print axioms exists_rank_separation_for_forbidden_colors

end Erdos19.SetHypergraph
