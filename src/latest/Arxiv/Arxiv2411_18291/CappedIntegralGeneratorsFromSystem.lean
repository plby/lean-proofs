import Arxiv.Arxiv2411_18291.CappedDecoderFocusing
import Arxiv.Arxiv2411_18291.RelaxedRainbowIntegralGeneration
import Arxiv.Arxiv2411_18291.RainbowIntegralLift
import Arxiv.Arxiv2411_18291.DecoderCorrection

/-! # Integral lifting preserves the input edge cap up to an additive constant

All integral generation is constructed from the modular span and the
extension properties. The only coefficient hypothesis is the displayed
numerical growth bound; the input need not generate integral vectors.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_integral_generators_from_system_with_cap_paper_threshold
    {I W : Type*} [Finite I] [Fintype W] [DecidableEq W] {q r n t H : ℕ}
    {S : ExchangeSystem W q (r + 1)} {A : Finset (Block W q)} {P : Block W q}
    (hA : IsExchangeFamily S A) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hqh : q.choose (r + 1) ≤ H)
    (hH : H ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (hP : P ∈ S.negative)
    (ht : 2 * q.choose (r + 1) ≤ t)
    {C M : ℝ} (hgrowth : C + 1 ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 20))
    (K G : Hypergraph (Fin n) (r + 1))
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) * K.card)
    (σ : I → Equiv.Perm (Fin n)) (hE : RainbowAvoidingExtensionProperties S P σ G t)
    (F₀ : Finset (Block (Fin n) q))
    (hF₀ : IsCliqueFamilyBounded r F₀
      (C * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))))
    (hM : ∀ e : Block (Fin n) (r + 1),
      ((F₀.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ M)
    (hmod : ∀ Q : Block (Fin n) q,
      IsRainbow (fun i => mapGraph (σ i).toEmbedding G) (cliqueEdges (r + 1) Q) →
      modularCliqueVector ((r + 1).factorial * q.choose (r + 1)) (r + 1) Q ∈
        generatedSubgroup
          (modularCliqueVector ((r + 1).factorial * q.choose (r + 1)) (r + 1)) F₀)
    (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-paperRho q (r + 1)))) :
    ∃ D : Finset (Block (Fin n) q), F₀ ⊆ D ∧
      IsCliqueFamilyBounded r D ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) / 2) ∧
      (∀ e : Block (Fin n) (r + 1),
        ((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ M + 1 + q.choose (r + 1)) ∧
      ∀ J : Block (Fin n) (r + 1) → ℤ, (∀ e, e ∉ B → J e = 0) →
        IntegrallyDecomposable q J → GeneratedBy D J := by
  let : Fintype I := Fintype.ofFinite I
  let N := (r + 1).factorial * q.choose (r + 1)
  have hN : 1 < N := by
    have hh := (decoder_multiplier_bounds hqr).1
    change (2 : ℤ) ≤ (N : ℤ) at hh
    exact_mod_cast (show (1 : ℤ) < N by omega)
  let : Fact (1 < N) := ⟨hN⟩
  have hk : 1 ≤ q.choose (r + 1) := Nat.choose_pos hqr.le
  have htpos : 1 ≤ t := by omega
  have hcount (e : Block (Fin n) (r + 1)) := (hE.toRainbowExtensionProperties.punctured e).le
  simp only [Fintype.card_fin] at hcount
  obtain ⟨D, hsub, hD, hcap, hdecode, hfocus⟩ :=
    exists_decoder_focusing_augmentation_with_cap_paper_threshold hqr hn hqh hH hgrowth
      K G hd hGK hloss σ hcount B hB F₀ hF₀ hM
  refine ⟨D, hsub, hD, hcap, fun J hs hJ => ?_⟩
  obtain ⟨J', hdiff, hs', hJ'⟩ := hfocus J hs hJ
  have hcolour := integral_coloured_generated_rainbow_relaxed_paper_threshold
    hA hqr hn hqh hH hP ht K G hd hGK hloss σ hE J' hJ' hs'
  have hlift := hE.integral_lift htpos N F₀ D hsub hmod hdecode J' hs' hcolour
  simpa only [sub_add_cancel] using hdiff.add hlift

end Arxiv2411_18291
