import ErdosProblems.Erdos964.ScalarPrimeFaceSum
import ErdosProblems.Erdos964.AffinePrimeSlicePNT
import ErdosProblems.Erdos964.PrimeReciprocalMass
import ErdosProblems.Erdos964.ScalarFaceBound

/-!
# Summing the prime-counting error against the scalar face
-/

namespace Erdos964

open BoundedGaps.Maynard Filter

noncomputable def scalarSliceFaceSum (η β : ℝ) (m c K t : ℕ) : ℝ :=
  ∑ p ∈ scalarSmallPrimeSupport η K t,
    (primeSlice ((Finset.Ioc (K * t) ((K * t) ^ 2)).filter Nat.Prime) p
      (m * t ^ 2 + c - 1) (m * (2 * t ^ 2) + c - 1)).card *
        scalarSieveFace (Real.log p / Real.log (modulusCutoff β t))

theorem exists_scalar_slice_face_error (m c K : ℕ) (hm : 1 ≤ m) (hc : 1 ≤ c)
    (hK : 1 ≤ K) (hKsize : 2 * m + c ≤ K ^ 2)
    (η β : ℝ) (hη : 0 < η) (hβ : 0 < β) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℕ, 2 ≤ T₀ ∧ ∀ t : ℕ, T₀ ≤ t →
      |scalarSliceFaceSum η β m c K t -
        (m : ℝ) * (t ^ 2 : ℕ) * scalarPrimeFaceSum η β K t| ≤
        ε * G * (((t ^ 2 : ℕ) : ℝ) / Real.log t) := by
  obtain ⟨G, hG, hface⟩ := exists_scalarSieveFace_bound
  refine ⟨2 * G / η, by positivity, ?_⟩
  intro ε hε
  obtain ⟨Y₀, hY₀, hPNT⟩ := exists_affine_primeSlice_error m c hm hc ε hε
  obtain ⟨T₁, hT₁, hmass⟩ := exists_primeReciprocalMass_uniform_bound η hη
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp
    ((tendsto_log_scalar_power_radius β hβ).eventually (eventually_gt_atTop 0))
  refine ⟨max T₁ (max T₂ ⌈Y₀⌉₊), hT₁.trans (le_max_left _ _), ?_⟩
  intro t ht
  have ht₁ : T₁ ≤ t := (le_max_left _ _).trans ht
  have ht₂ : T₂ ≤ t := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have htY : ⌈Y₀⌉₊ ≤ t := (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  have ht2 : 2 ≤ t := hT₁.trans ht₁
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hlogt : 0 < Real.log t := Real.log_pos (by exact_mod_cast (show 1 < t by omega))
  have hlogR := hT₂ t ht₂
  let P := scalarSmallPrimeSupport η K t
  let Q := (Finset.Ioc (K * t) ((K * t) ^ 2)).filter Nat.Prime
  let x := m * t ^ 2 + c - 1
  let z := m * (2 * t ^ 2) + c - 1
  let H : ℕ → ℝ := fun p => scalarSieveFace (Real.log p / Real.log (modulusCutoff β t))
  let Y : ℕ → ℝ := fun p => ((t ^ 2 : ℕ) : ℝ) / p
  have hends := scalar_affine_interval_bounds m c K t hm hc ht2 hKsize
  have hpoint (p : ℕ) (hp : p ∈ P) :
      |((primeSlice Q p x z).card - (m : ℝ) * Y p / Real.log (Y p)) * H p| ≤
        (ε * G * (((t ^ 2 : ℕ) : ℝ) / Real.log t)) * (1 / (p : ℝ)) := by
    have hspec := scalarSmallPrimeSupport_spec η K t p hp
    have hpt : p ≤ t := hspec.2.1.trans (Nat.div_le_self _ _)
    have hpR : (0 : ℝ) < p := by exact_mod_cast hspec.1.pos
    have hptR : (p : ℝ) ≤ t := by exact_mod_cast hpt
    have hYt : (t : ℝ) ≤ Y p := by
      apply (le_div_iff₀ hpR).mpr
      push_cast
      nlinarith
    have hY : Y₀ ≤ Y p := (Nat.le_ceil Y₀).trans
      ((show (⌈Y₀⌉₊ : ℝ) ≤ t by exact_mod_cast htY).trans hYt)
    have hlogY : Real.log t ≤ Real.log (Y p) := Real.log_le_log htR hYt
    have hlo := (scalarSmallPrimeSupport_mul_scale_le_square η K t p hp).trans hends.1
    have hhi : m * (2 * t ^ 2) + c - 1 ≤ p * ((K * t) ^ 2) :=
      hends.2.2.trans (Nat.le_mul_of_pos_left _ hspec.1.pos)
    have he := hPNT (t ^ 2) p (K * t) ((K * t) ^ 2) (by nlinarith)
      hspec.1.pos hY hlo hhi
    have hH : |H p| ≤ G := hface _
      (div_nonneg (Real.log_natCast_nonneg _) hlogR.le)
    have hYpos : 0 < Y p := htR.trans_le hYt
    have hLY : 0 < Real.log (Y p) := hlogt.trans_le hlogY
    rw [abs_mul]
    calc
      _ ≤ (ε * (Y p / Real.log (Y p))) * G :=
        mul_le_mul he hH (abs_nonneg _) (by positivity)
      _ ≤ (ε * (Y p / Real.log t)) * G := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left hYpos.le hlogt hlogY) hε.le) hG
      _ = _ := by dsimp only [Y]; ring
  have hid : scalarSliceFaceSum η β m c K t -
      (m : ℝ) * (t ^ 2 : ℕ) * scalarPrimeFaceSum η β K t =
      ∑ p ∈ P, ((primeSlice Q p x z).card - (m : ℝ) * Y p / Real.log (Y p)) * H p := by
    unfold scalarSliceFaceSum scalarPrimeFaceSum
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    dsimp only [Q, x, z, H, Y]
    ring
  rw [hid]
  calc
    _ ≤ ∑ p ∈ P,
        |((primeSlice Q p x z).card - (m : ℝ) * Y p / Real.log (Y p)) * H p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ P, (ε * G * (((t ^ 2 : ℕ) : ℝ) / Real.log t)) * (1 / (p : ℝ)) :=
      Finset.sum_le_sum hpoint
    _ = (ε * G * (((t ^ 2 : ℕ) : ℝ) / Real.log t)) * (∑ p ∈ P, (1 : ℝ) / p) := by
      rw [Finset.mul_sum]
    _ ≤ (ε * G * (((t ^ 2 : ℕ) : ℝ) / Real.log t)) * (2 / η) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply hmass t P ht₁
      intro p hp
      have hs := scalarSmallPrimeSupport_spec η K t p hp
      exact ⟨hs.1, hs.2.1.trans (Nat.div_le_self _ _),
        scalarSmallPrimeSupport_log_lower η K t p hη.le hK (by omega) hp⟩
    _ = _ := by ring

end Erdos964
