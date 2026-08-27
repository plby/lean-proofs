import Arxiv.Arxiv2411_18291.RainbowIntegralLift
import Arxiv.Arxiv2411_18291.AvoidingRainbowGeneratingSystem
import Arxiv.Arxiv2411_18291.DecoderFocusingAssembly
import Arxiv.Arxiv2411_18291.DecoderCorrection

/-!
# Sparse integral generators before flattening

The finite exchange system constructs a sparse family that generates every
integral boundary supported on a sparse reserve. Its clique multiplicities
are not yet bounded by two; that is the separate flattening step.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {U W : Type*} [Fintype U] [Fintype W] [DecidableEq W] {q r : ℕ}

theorem eventually_exists_sparse_integral_generators_with_exchange
    (F₀ : Block U (r + 1)) (hU : Fintype.card U = q)
    {S : ExchangeSystem W q (r + 1)} {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    {P₀ : Block W q} {e₀ : Block W (r + 1)} (hpair : IsEliminationPair S P₀ e₀)
    (hqr : r + 1 < q) (h : ℕ) (hqh : q.choose (r + 1) ≤ h) (hSh : S.graph.card ≤ h)
    {α ρ η : ℝ} (hα : 0 < α) (hαh : α * h ≤ 1 / 12)
    (hρ : 2 * α * q.choose (r + 1) ≤ ρ) (hρ1 : ρ < 1)
    (hη : 0 < η) (hηα : η < 7 * α / 10) :
    ∀ᶠ n : ℕ in atTop, ∀ B : Hypergraph (Fin n) (r + 1),
      IsGraphBounded B ((n : ℝ) ^ (-ρ)) →
      ∃ D : Finset (Block (Fin n) q), IsCliqueFamilyBounded r D ((n : ℝ) ^ (-η)) ∧
        ∀ J : Block (Fin n) (r + 1) → ℤ, (∀ e, e ∉ B → J e = 0) →
          IntegrallyDecomposable q J → GeneratedBy D J := by
  classical
  let N := (r + 1).factorial * q.choose (r + 1)
  let t := 2 * q.choose (r + 1)
  have hk : 1 ≤ q.choose (r + 1) := Nat.choose_pos hqr.le
  have hkR : (1 : ℝ) ≤ q.choose (r + 1) := by exact_mod_cast hk
  have hN : 1 < N := by
    have h := (decoder_multiplier_bounds hqr).1
    change (2 : ℤ) ≤ (N : ℤ) at h
    exact_mod_cast (show (1 : ℤ) < N by omega)
  let : Fact (1 < N) := ⟨hN⟩
  have ht : 1 ≤ t := by dsimp only [t]; omega
  have hpred : ((q.choose (r + 1) - 1 : ℕ) : ℝ) ≤ h := by
    exact_mod_cast (Nat.sub_le (q.choose (r + 1)) 1).trans hqh
  have hgap : α * ((q.choose (r + 1) - 1 : ℕ) : ℝ) < 1 :=
    (mul_le_mul_of_nonneg_left hpred hα.le).trans_lt (by linarith only [hαh])
  have hα1 : 7 * α / 10 < 1 := by nlinarith only [hα, hρ, hρ1, hkR]
  obtain ⟨u, L, hsystem⟩ := eventually_exists_avoiding_rainbow_generating_system F₀ hU hA
    hpair hqr h N t (by omega) hqh hSh hα hαh
  let C : ℝ := (((t + 1) * u + L * S.farCliques.card + 1 : ℕ) : ℝ) * 2 ^ q
  filter_upwards [hsystem,
    eventually_integral_coloured_generated_rainbow (I := Fin (t + 1) × Fin u) hA hqr
      hpair.negative_mem (le_refl t) (b := 1 / 4) (by norm_num) hgap,
    eventually_good_reference_density_lower (r + 1) (α := α) (δ := 1 / 10)
      (τ := α / 10) (by norm_num) (by positivity),
    eventually_exists_decoder_focusing_augmentation (I := Fin (t + 1) × Fin u) q r hqr.le
      (C := C) hα hρ hρ1 hη hηα hα1] with n hnSystem hnRainbow hnDensity hnAugment
  intro B hB
  obtain ⟨K, _, hd, M, _, hloss, σ, τ, hE, hτ, hspan⟩ := hnSystem
  have hbound : IsCliqueFamilyBounded r (permutedUnion τ M.generators)
      (C * (n : ℝ) ^ (-(7 * α / 10))) := by
    simpa only [C, mul_assoc] using hτ
  have hcount (e : Block (Fin n) (r + 1)) := (hE.toRainbowExtensionProperties.punctured e).le
  simp only [Fintype.card_fin] at hcount
  obtain ⟨D, hsub, hD, hdecode, hfocus⟩ := hnAugment K M.good hd M.good_subset hloss
    σ hcount B hB (permutedUnion τ M.generators) hbound
  refine ⟨D, hD, fun J hs hJ => ?_⟩
  obtain ⟨J', hdiff, hs', hJ'⟩ := hfocus J hs hJ
  have hcolour := hnRainbow M.good (hnDensity K M.good hd M.good_subset hloss) σ hE J' hJ' hs'
  have hlift := hE.integral_lift ht N (permutedUnion τ M.generators) D hsub hspan
    hdecode J' hs' hcolour
  simpa only [sub_add_cancel] using hdiff.add hlift

end Arxiv2411_18291
