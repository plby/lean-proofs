import Arxiv.Arxiv2411_18291.FiniteDecoderFocusing
import Arxiv.Arxiv2411_18291.FiniteRainbowIntegralGeneration
import Arxiv.Arxiv2411_18291.RainbowIntegralLift
import Arxiv.Arxiv2411_18291.DecoderCorrection

/-!
# Finite integral generators from an actual rainbow generating system

The input is the coloured modular construction, its explicit density
coefficient, and its extension properties. All focusing, bridge, decoding,
and integral lifting steps are carried out at the paper's size threshold,
using half the final degree budget so the source graph can be retained.
No integral-generation conclusion is assumed of the input family.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_integral_generators_from_system_paper_threshold
    {I W : Type*} [Finite I] [Fintype W] [DecidableEq W] {q r n t : ℕ}
    {S : ExchangeSystem W q (r + 1)} {A : Finset (Block W q)} {P : Block W q}
    (hA : IsExchangeFamily S A) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hP : P ∈ S.negative)
    (ht : 2 * q.choose (r + 1) ≤ t)
    {C : ℝ} (hC : 0 ≤ C) (hCb : C + 1 ≤ (4 * q : ℝ) ^ (6 * q))
    (K G : Hypergraph (Fin n) (r + 1))
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card)
    (σ : I → Equiv.Perm (Fin n)) (hE : RainbowAvoidingExtensionProperties S P σ G t)
    (F₀ : Finset (Block (Fin n) q))
    (hF₀ : IsCliqueFamilyBounded r F₀
      (C * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))))
    (hmod : ∀ Q : Block (Fin n) q,
      IsRainbow (fun i => mapGraph (σ i).toEmbedding G) (cliqueEdges (r + 1) Q) →
      modularCliqueVector ((r + 1).factorial * q.choose (r + 1)) (r + 1) Q ∈
        generatedSubgroup
          (modularCliqueVector ((r + 1).factorial * q.choose (r + 1)) (r + 1)) F₀)
    (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-paperRho q (r + 1)))) :
    ∃ D : Finset (Block (Fin n) q), F₀ ⊆ D ∧
      IsCliqueFamilyBounded r D ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) / 2) ∧
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
  obtain ⟨D, hsub, hD, hdecode, hfocus⟩ :=
    exists_decoder_focusing_augmentation_paper_threshold hqr hn hC hCb
      K G hd hGK hloss σ hcount B hB F₀ hF₀
  refine ⟨D, hsub, hD, fun J hs hJ => ?_⟩
  obtain ⟨J', hdiff, hs', hJ'⟩ := hfocus J hs hJ
  have hcolour := integral_coloured_generated_rainbow_paper_threshold hA hqr hn hP ht
    K G hd hGK hloss σ hE J' hJ' hs'
  have hlift := hE.integral_lift htpos N F₀ D hsub hmod hdecode J' hs' hcolour
  simpa only [sub_add_cancel] using hdiff.add hlift

/-- Finite integral generation with any fixed input coefficient. -/
theorem exists_integral_generators_from_system_explicit
    {I W : Type*} [Finite I] [Fintype W] [DecidableEq W] {q r n t : ℕ}
    {S : ExchangeSystem W q (r + 1)} {A : Finset (Block W q)} {P : Block W q}
    (hA : IsExchangeFamily S A) (hqr : r + 1 < q)
    {C : ℝ} (hn : finiteGeneratorAssemblyThreshold q r C ≤ n)
    (hP : P ∈ S.negative) (ht : 2 * q.choose (r + 1) ≤ t)
    (K G : Hypergraph (Fin n) (r + 1))
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card)
    (σ : I → Equiv.Perm (Fin n)) (hE : RainbowAvoidingExtensionProperties S P σ G t)
    (F₀ : Finset (Block (Fin n) q))
    (hF₀ : IsCliqueFamilyBounded r F₀
      (C * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))))
    (hmod : ∀ Q : Block (Fin n) q,
      IsRainbow (fun i => mapGraph (σ i).toEmbedding G) (cliqueEdges (r + 1) Q) →
      modularCliqueVector ((r + 1).factorial * q.choose (r + 1)) (r + 1) Q ∈
        generatedSubgroup
          (modularCliqueVector ((r + 1).factorial * q.choose (r + 1)) (r + 1)) F₀)
    (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-paperRho q (r + 1)))) :
    ∃ D : Finset (Block (Fin n) q), F₀ ⊆ D ∧
      IsCliqueFamilyBounded r D ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5))) ∧
      ∀ J : Block (Fin n) (r + 1) → ℤ, (∀ e, e ∉ B → J e = 0) →
        IntegrallyDecomposable q J → GeneratedBy D J := by
  let : Fintype I := Fintype.ofFinite I
  have hnPaper : paperSizeThreshold q (r + 1) ≤ n := (le_max_left _ _).trans hn
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
  obtain ⟨D, hsub, hD, hdecode, hfocus⟩ :=
    exists_decoder_focusing_augmentation_explicit hqr hn
      K G hd hGK hloss σ hcount B hB F₀ hF₀
  refine ⟨D, hsub, hD, fun J hs hJ => ?_⟩
  obtain ⟨J', hdiff, hs', hJ'⟩ := hfocus J hs hJ
  have hcolour := integral_coloured_generated_rainbow_paper_threshold hA hqr hnPaper hP ht
    K G hd hGK hloss σ hE J' hJ' hs'
  have hlift := hE.integral_lift htpos N F₀ D hsub hmod hdecode J' hs' hcolour
  simpa only [sub_add_cancel] using hdiff.add hlift

end Arxiv2411_18291
