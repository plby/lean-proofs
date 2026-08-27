import Arxiv.Arxiv2411_18291.VariableNearCancellationPairs
import Arxiv.Arxiv2411_18291.NearMatching

/-! # Selecting near cancellations with variable capacities

Nonnegative boundary at the old graph supplies a matching covering every
selected negative near clique. Each positive near clique is used at most once.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {q r : ℕ} {S : ExchangeSystem W q (r + 1)} {D : Finset (Block V q)}
variable {B : Hypergraph V (r + 1)} {C : Block V q → ℕ} {θ : ℝ}

structure VariableNearMatching (F : VariableSplittingFamily S D B C θ)
    (P N : Finset (Block V q)) where
  partner : ↥(N ∩ F.negativeNear) ↪ ↥(P ∩ F.positiveNear)
  common : ∀ Q, (cliqueEdges (r + 1) Q.val ∩
    cliqueEdges (r + 1) (partner Q).val).Nonempty

variable {F : VariableSplittingFamily S D B C θ} {P N : Finset (Block V q)}

def VariableNearMatching.index
    (M : VariableNearMatching F P N) (Q : ↥(N ∩ F.negativeNear)) : F.NearPairs :=
  ⟨(⟨Q.val, (mem_inter.mp Q.property).2⟩,
    ⟨(M.partner Q).val, (mem_inter.mp (M.partner Q).property).2⟩), M.common Q⟩

def VariableNearMatching.selected (M : VariableNearMatching F P N) : Finset F.NearPairs :=
  univ.image M.index

theorem VariableNearMatching.index_negative
    (M : VariableNearMatching F P N) (Q : ↥(N ∩ F.negativeNear)) :
    F.pairNegative (M.index Q) = Q.val := rfl

theorem VariableNearMatching.index_positive
    (M : VariableNearMatching F P N) (Q : ↥(N ∩ F.negativeNear)) :
    F.pairPositive (M.index Q) = (M.partner Q).val := rfl

theorem VariableNearMatching.negative_injective (M : VariableNearMatching F P N) :
    Set.InjOn F.pairNegative M.selected := by
  intro i hi j hj hij
  obtain ⟨x, _, hx⟩ := mem_image.mp hi
  obtain ⟨y, _, hy⟩ := mem_image.mp hj
  have hxy : x.val = y.val := by
    rw [← M.index_negative x, ← M.index_negative y, hx, hy]
    exact hij
  exact hx.symm.trans ((congrArg M.index (Subtype.ext hxy)).trans hy)

theorem VariableNearMatching.positive_injective (M : VariableNearMatching F P N) :
    Set.InjOn F.pairPositive M.selected := by
  intro i hi j hj hij
  obtain ⟨x, _, hx⟩ := mem_image.mp hi
  obtain ⟨y, _, hy⟩ := mem_image.mp hj
  have hxy : (M.partner x).val = (M.partner y).val := by
    rw [← M.index_positive x, ← M.index_positive y, hx, hy]
    exact hij
  exact hx.symm.trans ((congrArg M.index (M.partner.injective (Subtype.ext hxy))).trans hy)

theorem VariableNearMatching.selected_negative (M : VariableNearMatching F P N) :
    M.selected.image F.pairNegative = N ∩ F.negativeNear := by
  rw [selected, image_image]
  change (univ.image fun Q : ↥(N ∩ F.negativeNear) => Q.val) = N ∩ F.negativeNear
  ext Q
  simp only [mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨R, rfl⟩
    exact R.property
  · intro hQ
    exact ⟨⟨Q, hQ⟩, rfl⟩

theorem VariableNearMatching.selected_positive_subset (M : VariableNearMatching F P N) :
    M.selected.image F.pairPositive ⊆ P ∩ F.positiveNear := by
  intro Q hQ
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hQ
  obtain ⟨x, _, rfl⟩ := mem_image.mp hi
  exact (M.partner x).property

theorem VariableSplittingFamily.exists_nearMatching (F : VariableSplittingFamily S D B C θ)
    {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    (P N : Finset (Block V q)) (hP : P ⊆ F.positiveCliques) (hN : N ⊆ F.negativeCliques)
    (hnonneg : ∀ e ∈ B, 0 ≤ boundary (r + 1) (indicator P - indicator N) e) :
    Nonempty (VariableNearMatching F P N) := by
  have hn (e : Block V (r + 1)) (he : e ∈ B) :
      (N ∩ F.negativeNear).filter (fun Q => e.val ⊆ Q.val) =
        N.filter (fun Q => e.val ⊆ Q.val) := by
    ext Q
    simp only [mem_filter, mem_inter]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · intro h
      exact ⟨⟨h.1, mem_filter.mpr ⟨hN h.1, ⟨e, mem_inter.mpr
        ⟨(mem_cliqueEdges _ _).mpr h.2, he⟩⟩⟩⟩, h.2⟩
  have hp (e : Block V (r + 1)) (he : e ∈ B) :
      (P ∩ F.positiveNear).filter (fun Q => e.val ⊆ Q.val) =
        P.filter (fun Q => e.val ⊆ Q.val) := by
    ext Q
    simp only [mem_filter, mem_inter]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · intro h
      exact ⟨⟨h.1, mem_filter.mpr ⟨hP h.1, ⟨e, mem_inter.mpr
        ⟨(mem_cliqueEdges _ _).mpr h.2, he⟩⟩⟩⟩, h.2⟩
  obtain ⟨f, hf⟩ := exists_singleton_inter_matching B (N ∩ F.negativeNear)
    (P ∩ F.positiveNear)
    (fun _ h => F.negativeNear_inter hA (mem_inter.mp h).2)
    (fun _ h => F.positiveNear_inter hA (mem_inter.mp h).2) (by
      intro e he
      rw [hn e he, hp e he]
      have h := hnonneg e he
      rw [boundary_sub, Pi.sub_apply, boundary_indicator, boundary_indicator] at h
      exact_mod_cast sub_nonneg.mp h)
  exact ⟨⟨f, hf⟩⟩

end Arxiv2411_18291
