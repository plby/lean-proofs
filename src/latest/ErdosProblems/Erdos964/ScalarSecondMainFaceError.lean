import ErdosProblems.Erdos964.ScalarPrimeKernelLimit
import ErdosProblems.Erdos964.AffinePrimeSliceMass
import ErdosProblems.Erdos964.ScalarSliceFaceError
import ErdosProblems.Erdos964.ScalarSupportThresholds

/-!
# Uniform kernel replacement in the second main term on the actual scale
-/

namespace Erdos964

open BoundedGaps.Maynard Filter

noncomputable def scalarSecondMainAtScale (M m c K : ℕ) (η β : ℝ) (t : ℕ) : ℝ :=
  scalarCandidateSecondMain M (modulusCutoff β t) (scalarSmallPrimeSupport η K t)
    ((Finset.Ioc (K * t) ((K * t) ^ 2)).filter Nat.Prime)
    (m * t ^ 2 + c - 1) (m * (2 * t ^ 2) + c - 1)

theorem exists_scalar_second_main_face_error (M m c K : ℕ) (hM : 0 < M)
    (h2M : 2 ∣ M) (h3M : 3 ∣ M) (hm : 1 ≤ m) (hc : 1 ≤ c)
    (hK : 1 ≤ K) (hKsize : 2 * m + c ≤ K ^ 2)
    (η β : ℝ) (hη : 0 < η) (hβ : 0 < β) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℕ, 2 ≤ T₀ ∧ ∀ t : ℕ, T₀ ≤ t →
      |scalarSecondMainAtScale M m c K η β t / (Real.log (modulusCutoff β t)) ^ 4 -
        (scalarSieveEulerConstant M * coprimeHarmonicDensity M ^ 4) *
          scalarSliceFaceSum η β m c K t| ≤
        ε * D * (((t ^ 2 : ℕ) : ℝ) / Real.log t) := by
  refine ⟨2 * ((m : ℝ) + 1) / η, by positivity, ?_⟩
  intro ε hε
  obtain ⟨R₀, P₀, hR₀, hP₀, hkernel⟩ :=
    exists_scalar_second_main_uniform_face_error M hM h2M h3M ε hε
  obtain ⟨T₁, hT₁, hmass⟩ := exists_affine_primeSlice_total_mass_bound m c hm hc η hη
  obtain ⟨T₂, hT₂, hlarge⟩ := exists_scalarSmallPrimeSupport_ge P₀ η hη
  obtain ⟨T₃, hT₃, hcop⟩ := exists_scalarSmallPrimeSupport_coprime M hM η hη
  have hevent : ∀ᶠ t : ℕ in atTop, 2 ≤ t ∧
      |scalarSecondMainAtScale M m c K η β t / (Real.log (modulusCutoff β t)) ^ 4 -
        (scalarSieveEulerConstant M * coprimeHarmonicDensity M ^ 4) *
          scalarSliceFaceSum η β m c K t| ≤
        ε * (2 * ((m : ℝ) + 1) / η) * (((t ^ 2 : ℕ) : ℝ) / Real.log t) := by
    filter_upwards [eventually_ge_atTop T₁, eventually_ge_atTop T₂, eventually_ge_atTop T₃,
      (tendsto_scalar_power_radius β hβ).eventually (eventually_ge_atTop R₀)] with t ht₁ ht₂ ht₃ hR
    have ht2 : 2 ≤ t := hT₁.trans ht₁
    refine ⟨ht2, ?_⟩
    let P := scalarSmallPrimeSupport η K t
    let Q := (Finset.Ioc (K * t) ((K * t) ^ 2)).filter Nat.Prime
    let x := m * t ^ 2 + c - 1
    let z := m * (2 * t ^ 2) + c - 1
    have hP (p : ℕ) (hp : p ∈ P) : P₀ ≤ p ∧ p.Prime ∧ p.Coprime M :=
      ⟨hlarge t ht₂ K hK p hp, (scalarSmallPrimeSupport_spec η K t p hp).1,
        hcop t ht₃ K hK p hp⟩
    have h := hkernel (modulusCutoff β t) x z P Q hR hP
    have hends := scalar_affine_interval_bounds m c K t hm hc ht2 hKsize
    have hm := hmass t (K * t) ((K * t) ^ 2) P ht₁
      (fun p hp => by
        have hs := scalarSmallPrimeSupport_spec η K t p hp
        exact ⟨hs.1, hs.2.1.trans (Nat.div_le_self _ _),
          scalarSmallPrimeSupport_log_lower η K t p hη.le hK (by omega) hp⟩)
      (fun p hp => ⟨(scalarSmallPrimeSupport_mul_scale_le_square η K t p hp).trans hends.1,
        hends.2.2.trans (Nat.le_mul_of_pos_left _ (scalarSmallPrimeSupport_spec η K t p hp).1.pos)⟩)
    change |scalarSecondMainAtScale M m c K η β t / (Real.log (modulusCutoff β t)) ^ 4 -
      (scalarSieveEulerConstant M * coprimeHarmonicDensity M ^ 4) *
        scalarSliceFaceSum η β m c K t| ≤ ε * (∑ p ∈ P, ((primeSlice Q p x z).card : ℝ)) at h
    calc
      _ ≤ ε * ((2 * ((m : ℝ) + 1) / η) * ((t : ℝ) ^ 2 / Real.log t)) :=
        h.trans (mul_le_mul_of_nonneg_left hm hε.le)
      _ = _ := by push_cast; ring
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hevent
  refine ⟨max T₀ 2, le_max_right _ _, ?_⟩
  intro t ht
  exact (hT₀ t ((le_max_left _ _).trans ht)).2

end Erdos964
