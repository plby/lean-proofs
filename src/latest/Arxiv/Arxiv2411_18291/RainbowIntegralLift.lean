import Arxiv.Arxiv2411_18291.RainbowGeneratorSupport

/-!
# Converting rainbow generation to the sparse integer span

Modular generators cover the colour graph. Consequently the difference
between a supported integer vector and its modular representation is a
modulus multiple on the decoder support, where it can be corrected.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {I W V : Type*} [Fintype I] [Fintype W] [DecidableEq W]
variable [Fintype V] [DecidableEq V] {q r t : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {P : Block W q}
variable {σ : I → Equiv.Perm V} {G : Hypergraph V (r + 1)}

theorem RainbowAvoidingExtensionProperties.integral_lift
    (hE : RainbowAvoidingExtensionProperties S P σ G t) (ht : 1 ≤ t)
    (N : ℕ) [Nontrivial (ZMod N)] (D F : Finset (Block V q)) (hDF : D ⊆ F)
    (hmod : ∀ Q : Block V q,
      IsRainbow (fun i => mapGraph (σ i).toEmbedding G) (cliqueEdges (r + 1) Q) →
      modularCliqueVector N (r + 1) Q ∈ generatedSubgroup (modularCliqueVector N (r + 1)) D)
    (hdecode : ∀ J : Block V (r + 1) → ℤ,
      (∀ e, e ∉ cliqueSupport (r + 1) D → J e = 0) →
      (∀ e, (N : ℤ) ∣ J e) → GeneratedBy F J)
    (J : Block V (r + 1) → ℤ) (hs : ∀ e, e ∉ permutedUnion σ G → J e = 0)
    (hJ : GeneratedBy (rainbowCliqueFamily (fun i => mapGraph (σ i).toEmbedding G) q) J) :
    GeneratedBy F J := by
  have hsupport := hE.colour_subset_generator_support ht N D hmod
  have hprojection := hJ.modular_mem N
    (fun Q hQ => hmod Q ((mem_rainbowCliqueFamily _ _).mp hQ))
  exact generatedBy_of_modular_membership N D F (cliqueSupport (r + 1) D)
    hDF Subset.rfl hdecode J (fun e he => hs e (fun heG => he (hsupport heG))) hprojection

end Arxiv2411_18291
