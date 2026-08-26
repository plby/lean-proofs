import ErdosProblems.Erdos556.ProfileApproximationParameters
import ErdosProblems.Erdos556.ProfileSaturation
import ErdosProblems.Erdos556.CubeStability

/-! Uniform stability for the profiles of a forbidden-cycle colouring. -/

namespace Erdos556

open SimpleGraph Finset

theorem exists_stable_three_colour_decomposition (η : ℝ) (hη : 0 < η) :
    ∃ n₀ : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (c : ThreeColouring V) (n : ℕ), n₀ ≤ n → Odd n →
      Fintype.card V = 4 * n - 3 → (∀ i, ¬ cycleGraph n ⊑ c.graph i) →
      ∃ E D : ℝ, ∃ h : ThreeColourDecomposition c E D, ∃ v : CubeProfile → ℝ,
        IsCubeWeight v ∧ IsCubeTiling v ∧
        (∀ p, |h.profileWeight n p - v p| < η) ∧
        (Nat.card h.potentialMissing.edgeSet : ℝ) ≤ η * (n : ℝ) ^ 2 := by
  let α : ℝ := η / 1000
  have hα : 0 < α := div_pos hη (by norm_num)
  have hαη : α < η := by dsimp only [α]; linarith
  obtain ⟨δ₀, hδ₀, hstable⟩ := exists_cube_stability_and_energy_tolerance α hα
  let δ : ℝ := min δ₀ α
  have hδ : 0 < δ := lt_min hδ₀ hα
  obtain ⟨ε, hε, hεδ, n₁, happrox⟩ := exists_profile_approximation_parameters δ hδ
  have hεα : ε ≤ α := hεδ.trans (min_le_right _ _)
  obtain ⟨n₂, hdecomp⟩ := exists_three_colour_decomposition ε hε
  obtain ⟨m, hm⟩ := exists_nat_ge (4 / α)
  refine ⟨max 8 (max m (max n₁ n₂)), ?_⟩
  intro V _ _ c n hn hodd hN hno
  have hn8 : 8 ≤ n := (le_max_left _ _).trans hn
  have hmnat : m ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn₁ : n₁ ≤ n := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hn₂ : n₂ ≤ n := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hNleN : Fintype.card V ≤ 4 * n := by omega
  have hnN : n ≤ Fintype.card V := by omega
  obtain ⟨h⟩ := hdecomp c n hn₂ hodd hnN hNleN hno
  have hw := (happrox c n hn₁ hN hno h).mono (min_le_left δ₀ α)
  obtain ⟨v, hv, ht, hclose, henergy⟩ := hstable _ hw
  refine ⟨_, _, h, v, hv, ht, fun p => (hclose p).trans hαη, ?_⟩
  have hNnonneg : (0 : ℝ) ≤ Fintype.card V := by positivity
  have hNle : (Fintype.card V : ℝ) ≤ 4 * n := by exact_mod_cast hNleN
  have hNsq : (Fintype.card V : ℝ) ^ 2 ≤ 16 * (n : ℝ) ^ 2 := by nlinarith
  have hαn : 4 ≤ α * n := by
    have hmn : (m : ℝ) ≤ n := by exact_mod_cast hmnat
    have hh := (div_le_iff₀ hα).mp (hm.trans hmn)
    nlinarith
  have hNsmall : (Fintype.card V : ℝ) ≤ α * (n : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hαn hnpos.le]
  have hEsmall : ε * (Fintype.card V : ℝ) ^ 2 ≤ 16 * α * (n : ℝ) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hNsq hε.le
    have hh' := mul_le_mul_of_nonneg_right hεα (sq_nonneg (n : ℝ))
    nlinarith
  have hW := h.free_coordinate_mass_le
  have hWscaled := mul_le_mul_of_nonneg_left hW
    (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * ε) hNnonneg)
  have he := (abs_lt.mp henergy).1
  have hescaled := mul_le_mul_of_nonneg_right (le_of_lt he) (sq_nonneg (n : ℝ))
  have hb := h.potentialMissing_bound n hnpos.ne'
  have hαeq : 1000 * α = η := by dsimp only [α]; ring
  have hαeqsq : 1000 * α * (n : ℝ) ^ 2 = η * (n : ℝ) ^ 2 := by rw [hαeq]
  nlinarith [mul_nonneg hα.le (sq_nonneg (n : ℝ))]

#print axioms exists_stable_three_colour_decomposition

end Erdos556
