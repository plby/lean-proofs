import Arxiv.Arxiv2411_18291.RootedCliquePlacement
import Arxiv.Arxiv2411_18291.CliqueRefinement
import Arxiv.Arxiv2411_18291.CliqueFamilyBoundedness
import Arxiv.Arxiv2411_18291.IntegralSpan

/-!
# Sparse simultaneous local decoders

This implements Step 2 of the absorber construction for any sparse input
graph. The placed `(q+r)`-sets have disjoint edge sets, and all their
`q`-subsets form a sparse family with edge multiplicity at most `choose(q,r)`.
Every input edge has an explicit integral decoder supported on this family,
with multiplier `r!*choose(q,r)` and coefficient bound `2^q*r!`.
-/

open Finset Filter

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

structure IsLocalDecoderFamily (B : Hypergraph V (r + 1))
    (D : Finset (Block V q)) : Prop where
  multiplicity : ∀ e : Block V (r + 1),
    (D.filter fun Q => e.val ⊆ Q.val).card ≤ q.choose (r + 1)
  decodes : ∀ e ∈ B, ∃ Ψ : Block V q → ℤ,
    boundary (r + 1) Ψ =
      (fun e' => if e' = e then (((r + 1).factorial * q.choose (r + 1) : ℕ) : ℤ) else 0) ∧
    (∀ Q, Q ∉ D → Ψ Q = 0) ∧
    ∀ Q, |Ψ Q| ≤ (2 ^ q * (r + 1).factorial : ℕ)

theorem IsLocalDecoderFamily.generates_multiples {B : Hypergraph V (r + 1)}
    {D : Finset (Block V q)} (hD : IsLocalDecoderFamily B D)
    (J : Block V (r + 1) → ℤ) (hsupport : ∀ e, e ∉ B → J e = 0)
    (hdiv : ∀ e, (((r + 1).factorial * q.choose (r + 1) : ℕ) : ℤ) ∣ J e) :
    GeneratedBy D J := by
  apply generatedBy_of_edge_decoders B _ _ J hsupport hdiv
  intro e he
  obtain ⟨Ψ, hΨ, hs, _⟩ := hD.decodes e he
  exact ⟨Ψ, hΨ, hs⟩

theorem IsCliqueCover.localDecoderFamily (hqr : r + 1 ≤ q)
    {R B : Hypergraph V (r + 1)} {Z : B → Block V (q + (r + 1))}
    (hZ : IsCliqueCover R (fun e : B => e.val) Z) :
    IsLocalDecoderFamily B (cliqueRefinement q (univ.image Z)) := by
  constructor
  · intro e
    simpa only [Nat.add_sub_cancel_right, Nat.choose_symm hqr] using
      hZ.decomposition.refinement_multiplicity_le hqr e
  · intro e he
    obtain ⟨Ψ, hΨ, hs, hb⟩ := local_decoder_on (Z ⟨e, he⟩).val (Z ⟨e, he⟩).property
      hqr e (hZ.punctured ⟨e, he⟩).1
    refine ⟨Ψ, hΨ, ?_, hb⟩
    intro Q hQ
    apply hs Q
    intro hQZ
    apply hQ
    exact (mem_cliqueRefinement _ Q).mpr
      ⟨Z ⟨e, he⟩, mem_image.mpr ⟨⟨e, he⟩, mem_univ _, rfl⟩, hQZ⟩

omit [Fintype V] [DecidableEq V] in
theorem eventually_exists_sparse_local_decoders (hqr : r + 1 ≤ q) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ B : Hypergraph (Fin n) (r + 1),
      IsGraphBounded B ((n : ℝ) ^ (-ρ)) →
      ∃ Z : B → Block (Fin n) (q + (r + 1)), ∃ D : Finset (Block (Fin n) q),
        IsCliqueCover (complete (Fin n) (r + 1) \ B) (fun e : B => e.val) Z ∧
        D = cliqueRefinement q (univ.image Z) ∧ IsLocalDecoderFamily B D ∧
        IsGraphBounded (cliqueSupport (r + 1) D)
          ((1 + 4 * (r + 1).factorial * (q + (r + 1)).choose (r + 1)) *
            (n : ℝ) ^ (-ρ)) := by
  filter_upwards [eventually_exists_clique_placement (Nat.le_add_left (r + 1) q) hρ hρ1]
    with n hplace
  intro B hB
  obtain ⟨Z, hZ, hb⟩ := hplace B hB
  exact ⟨Z, cliqueRefinement q (univ.image Z), hZ, rfl, hZ.localDecoderFamily hqr,
    hb.subgraph hZ.decomposition.refinement_support_subset⟩

omit [Fintype V] [DecidableEq V] in
theorem eventually_exists_bounded_local_decoder_family (hqr : r + 1 ≤ q) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    let C : ℝ := 1 + 4 * (r + 1).factorial * (q + (r + 1)).choose (r + 1)
    ∀ᶠ n : ℕ in atTop, ∀ B : Hypergraph (Fin n) (r + 1),
      IsGraphBounded B ((n : ℝ) ^ (-ρ)) →
      ∃ D : Finset (Block (Fin n) q), IsLocalDecoderFamily B D ∧
        IsGraphBounded (cliqueSupport (r + 1) D) (C * (n : ℝ) ^ (-ρ)) ∧
        IsCliqueFamilyBounded r D (q.choose (r + 1) * C * (n : ℝ) ^ (-ρ)) := by
  dsimp only
  filter_upwards [eventually_exists_sparse_local_decoders hqr hρ hρ1] with n hn
  intro B hB
  obtain ⟨_, D, _, _, hD, hb⟩ := hn B hB
  refine ⟨D, hD, hb, ?_⟩
  have hmulti := hb.cliqueFamilyBounded D (Nat.choose_pos hqr) hD.multiplicity (Subset.refl _)
  simpa only [mul_assoc] using hmulti

end Arxiv2411_18291
