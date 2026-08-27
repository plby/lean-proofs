import Arxiv.Arxiv2411_18291.DecoderAugmentation
import Arxiv.Arxiv2411_18291.SparseColouredFocusing

/-!
# Assembling the generators, focusing cliques, and local decoders

The enlarged family contains the original generators, focuses every signed
input vector onto the colour graph, and decodes every modulus multiple on
the generator support. Any fixed loss from the `0.7*α` density exponent
absorbs all constants from this assembly.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {I : Type*} [Fintype I]

theorem eventually_exists_decoder_focusing_augmentation (q r : ℕ) (hq : r + 1 ≤ q)
    {C α ρ η : ℝ} (hα : 0 < α) (hρ : 2 * α * q.choose (r + 1) ≤ ρ) (hρ1 : ρ < 1)
    (hη : 0 < η) (hηα : η < 7 * α / 10) (hα1 : 7 * α / 10 < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ K G : Hypergraph (Fin n) (r + 1),
      |density K - (n : ℝ) ^ (-α)| ≤
        (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-α) →
      G ⊆ K → ((K \ G).card : ℝ) ≤ (n : ℝ) ^ (-(α / 10)) * K.card →
      ∀ σ : I → Equiv.Perm (Fin n),
      (∀ e : Block (Fin n) (r + 1),
        ((3 / 8 : ℝ) * density G ^ (q.choose (r + 1) - 1) *
          (n : ℝ) ^ (q - (r + 1))) / (q - (r + 1)).factorial ≤
            (rainbowPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) e q).card) →
      ∀ B : Hypergraph (Fin n) (r + 1), IsGraphBounded B ((n : ℝ) ^ (-ρ)) →
      ∀ F₀ : Finset (Block (Fin n) q),
        IsCliqueFamilyBounded r F₀ (C * (n : ℝ) ^ (-(7 * α / 10))) →
      ∃ D : Finset (Block (Fin n) q), F₀ ⊆ D ∧
        IsCliqueFamilyBounded r D ((n : ℝ) ^ (-η)) ∧
        (∀ J : Block (Fin n) (r + 1) → ℤ,
          (∀ e, e ∉ cliqueSupport (r + 1) F₀ → J e = 0) →
          (∀ e, (((r + 1).factorial * q.choose (r + 1) : ℕ) : ℤ) ∣ J e) → GeneratedBy D J) ∧
        ∀ J : Block (Fin n) (r + 1) → ℤ, (∀ e, e ∉ B → J e = 0) →
          IntegrallyDecomposable q J →
          ∃ J' : Block (Fin n) (r + 1) → ℤ, GeneratedBy D (J - J') ∧
            (∀ e, e ∉ permutedUnion σ G → J' e = 0) ∧ IntegrallyDecomposable q J' := by
  filter_upwards [eventually_exists_sparse_coloured_focusing (I := I) q r hq hα hρ hρ1,
    eventually_augment_with_local_decoders q r hq (C := C + 1) hη hηα hα1]
      with n hfocus hdecode
  intro K G hd hGK hloss σ hcount B hB F₀ hF₀
  obtain ⟨F, hF, hfocusF⟩ := hfocus K G hd hGK hloss σ hcount B hB
  have hsum : IsCliqueFamilyBounded r (F₀ ∪ F) ((C + 1) * (n : ℝ) ^ (-(7 * α / 10))) := by
    simpa only [add_mul, one_mul] using hF₀.union hF
  obtain ⟨D, hsub, hD, hdecodeD⟩ := hdecode (F₀ ∪ F) hsum
  have hsupport : cliqueSupport (r + 1) F₀ ⊆ cliqueSupport (r + 1) (F₀ ∪ F) := by
    intro e he
    obtain ⟨Q, hQ, heQ⟩ := mem_biUnion.mp he
    exact mem_biUnion.mpr ⟨Q, mem_union_left _ hQ, heQ⟩
  refine ⟨D, subset_union_left.trans hsub, hD, ?_, ?_⟩
  · intro J hs hdiv
    exact hdecodeD J (fun e he => hs e (fun he₀ => he (hsupport he₀))) hdiv
  · intro J hs hInt
    obtain ⟨J', hJ', hs', hInt'⟩ := hfocusF J hs hInt
    exact ⟨J', hJ'.mono (subset_union_right.trans hsub), hs', hInt'⟩

end Arxiv2411_18291
