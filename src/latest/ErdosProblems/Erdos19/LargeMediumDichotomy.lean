import ErdosProblems.Erdos19.LargeEdgeDichotomy
import ErdosProblems.Erdos19.LargeMediumSaving
import ErdosProblems.Erdos19.LargeMediumProjective

/-! # The assembled large-and-medium coloring dichotomy

The projective coverage parameter is chosen first. After the saving constant
is fixed, the saving-branch coverage parameter and the medium-class parameter
remain arbitrary. The large threshold can exceed any prescribed multiple of
the medium threshold, avoiding a circular constant hierarchy.
-/

namespace Erdos19.SetHypergraph

open Finset

attribute [local instance] Classical.propDecidable

def mediumMinimumSize (a b : ℕ) : ℕ := 16 * a * (16 * b ^ 4) + 1

theorem eventually_large_medium_dichotomy (t : ℕ) (ht : 1024 ≤ t) (B₀ : ℕ) :
    ∃ b : ℕ, 8 * t ≤ b ∧ B₀ ≤ b ∧ ∀ a u ell : ℕ, 0 < a → 0 < u →
      ∃ R N : ℕ, ell * mediumMinimumSize a b ≤ R ∧ mediumMinimumSize a b < R ∧
        ∀ n : ℕ, N ≤ n → ∀ H : SetHypergraph (Fin n), H.IsLinear →
          (∀ e : H, mediumMinimumSize a b ≤ e.1.ncard) →
          (∃ color : H.EdgeColoring (Fin (n - n / (4 * b ^ 4))),
            ∃ palette : Finset (Fin (n - n / (4 * b ^ 4))),
              palette.card = n / (4 * b ^ 4) ∧
              H.HasControlledMediumPalette color palette R (16 * (n / u)) (n / a)) ∨
          (∃ color : H.EdgeColoring (Fin n), ∃ palette : Finset (Fin n),
            palette.card = n / (4 * b ^ 4) ∧
            H.HasControlledMediumPalette color palette R (16 * (n / t))
              (16 * (n / t) + n / a) ∧
            (∀ x, (H.coveredVertices {e | color.color e = x}).ncard ≤
              16 * (n / t) + n / a) ∧
            ∃ W : Finset H, ∃ r : ℕ,
              projectiveScale n - projectiveScale n / t ≤ r ∧
              (∀ e ∈ W, r ≤ e.1.ncard ∧ e.1.ncard ≤ r + r / b) ∧
              (b - 10) * n ^ 2 ≤ b * (∑ e ∈ W, e.1.ncard * (e.1.ncard - 1))) := by
  obtain ⟨b, hbt, hbB₀, N₀, _, hN₀⟩ :=
    eventually_large_edge_saving_or_projective_core_parametric t ht B₀
  refine ⟨b, hbt, hbB₀, ?_⟩
  intro a u ell ha hu
  have hbpos : 0 < b := by omega
  have hb4 : 0 < b ^ 4 := pow_pos hbpos _
  have ht2 : 0 < t ^ 2 := pow_pos (by omega) _
  let r₁ := mediumMinimumSize a b
  let R := max (ell * r₁) (max (r₁ + 1)
    (max (t ^ 2 * (4 * b ^ 4) + 1) (u ^ 2 * (2 * b ^ 4) + 1)))
  have hRell : ell * r₁ ≤ R := le_max_left _ _
  have hRr₁ : r₁ + 1 ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hRproj : t ^ 2 * (4 * b ^ 4) + 1 ≤ R :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hRsave : u ^ 2 * (2 * b ^ 4) + 1 ≤ R :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hRb : b ^ 4 ≤ R := by nlinarith only [hRproj, ht2, hb4]
  obtain ⟨Nsave, hNsave⟩ := eventually_medium_coloring_of_large_edge_saving R b a u
    hbpos ha hu hRsave
  obtain ⟨Nproj, hNproj⟩ := eventually_medium_coloring_of_projective_core R b a t ht hbt ha hRproj
  let N := max N₀ (max Nsave Nproj)
  refine ⟨R, N, hRell, by omega, ?_⟩
  intro n hn H hlinear hmin
  have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
  have hnsave : Nsave ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hnproj : Nproj ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  let L := H.rankAtLeast R
  have hL := H.rankAtLeast_linear hlinear R
  have hLmin (e : L) : b ^ 4 ≤ e.1.ncard := hRb.trans e.2.2
  rcases hN₀ n hn₀ L hL hLmin with hsave |
    ⟨S, W, r, hS, hWS, _, hdense, hpeel, hprojective, hminS, hmaxW, hvolume⟩
  · left
    exact hNsave n hnsave H hlinear hmin hsave
  · right
    have hcoremin : ∀ e ∈ S, projectiveScale n - projectiveScale n / t ≤ e.1.ncard :=
      fun e he ↦ hprojective.trans (hminS e he)
    obtain ⟨color, palette, hcard, hcontrol, hcover⟩ :=
      hNproj n hnproj H hlinear hmin S hS hdense hpeel hcoremin
    let W' := W.map (H.rankAtLeastEmbedding R)
    have hW' (e : H) (he : e ∈ W') : r ≤ e.1.ncard ∧ e.1.ncard ≤ r + r / b := by
      obtain ⟨f, hf, rfl⟩ := mem_map.mp he
      exact ⟨hminS f (hWS hf), hmaxW f hf⟩
    have hweight : (∑ e ∈ W', e.1.ncard * (e.1.ncard - 1)) =
        ∑ e ∈ W, e.1.ncard * (e.1.ncard - 1) := by
      rw [show W' = W.map (H.rankAtLeastEmbedding R) from rfl, Finset.sum_map]
      rfl
    refine ⟨color, palette, hcard, hcontrol, hcover, W', r, hprojective, hW', ?_⟩
    rw [hweight]
    exact hvolume

#print axioms eventually_large_medium_dichotomy

end Erdos19.SetHypergraph
