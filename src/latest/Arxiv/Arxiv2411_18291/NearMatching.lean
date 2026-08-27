import Arxiv.Arxiv2411_18291.FiniteFiberMatching
import Arxiv.Arxiv2411_18291.NearCancellationPairs

/-!
# Choosing the near cancellations for a signed representation

Each near clique has one edge in the original graph. Nonnegative boundary
there supplies at least as many positive cliques as negative cliques at
each edge. Matching these fibers cancels every negative near clique and
uses each positive near clique at most once.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem exists_singleton_inter_matching (B : Hypergraph V r) (N P : Finset (Block V q))
    (hN : ∀ Q ∈ N, ∃ e ∈ B, cliqueEdges r Q ∩ B = {e})
    (hP : ∀ Q ∈ P, ∃ e ∈ B, cliqueEdges r Q ∩ B = {e})
    (hcount : ∀ e ∈ B, (N.filter fun Q => e.val ⊆ Q.val).card ≤
      (P.filter fun Q => e.val ⊆ Q.val).card) :
    ∃ f : N ↪ P, ∀ Q, (cliqueEdges r Q.val ∩ cliqueEdges r (f Q).val).Nonempty := by
  let color (K : Finset (Block V q))
      (hK : ∀ Q ∈ K, ∃ e ∈ B, cliqueEdges r Q ∩ B = {e}) (Q : K) : B :=
    ⟨(hK Q.val Q.property).choose, (hK Q.val Q.property).choose_spec.1⟩
  have hcolor (K : Finset (Block V q))
      (hK : ∀ Q ∈ K, ∃ e ∈ B, cliqueEdges r Q ∩ B = {e}) (Q : K) :
      cliqueEdges r Q.val ∩ B = {(color K hK Q).val} :=
    (hK Q.val Q.property).choose_spec.2
  have hfiber (K : Finset (Block V q))
      (hK : ∀ Q ∈ K, ∃ e ∈ B, cliqueEdges r Q ∩ B = {e}) (e : B) :
      (univ.filter fun Q : K => color K hK Q = e).card =
        (K.filter fun Q => e.val.val ⊆ Q.val).card := by
    rw [← card_filter_subtype K (fun Q => e.val.val ⊆ Q.val)]
    congr 1
    apply filter_congr
    intro Q _
    have hm : e.val ∈ cliqueEdges r Q.val ∩ B ↔ e.val.val ⊆ Q.val.val := by
      simp only [mem_inter, mem_cliqueEdges, e.property, and_true]
    rw [hcolor K hK Q, mem_singleton] at hm
    exact (Subtype.ext_iff.trans eq_comm).trans hm
  obtain ⟨f, hf⟩ := exists_color_preserving_embedding (color N hN) (color P hP) (by
    intro e
    rw [hfiber N hN e, hfiber P hP e]
    exact hcount e.val e.property)
  refine ⟨f, ?_⟩
  intro Q
  let e := (color N hN Q).val
  have heN : e ∈ cliqueEdges r Q.val ∩ B := by
    rw [hcolor N hN Q]
    exact mem_singleton_self _
  have heP : e ∈ cliqueEdges r (f Q).val ∩ B := by
    rw [hcolor P hP (f Q), hf Q]
    exact mem_singleton_self _
  exact ⟨e, mem_inter.mpr ⟨(mem_inter.mp heN).1, (mem_inter.mp heP).1⟩⟩

variable {W : Type*} [Fintype W] [DecidableEq W] {C : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {D : Finset (Block V q)}
variable {B : Hypergraph V (r + 1)} {θ : ℝ}

structure NearMatching (F : SplittingFamily S D B C θ) (P N : Finset (Block V q)) where
  partner : ↥(N ∩ F.negativeNear) ↪ ↥(P ∩ F.positiveNear)
  common : ∀ Q, (cliqueEdges (r + 1) Q.val ∩
    cliqueEdges (r + 1) (partner Q).val).Nonempty

variable {F : SplittingFamily S D B C θ} {P N : Finset (Block V q)}

def NearMatching.index (M : NearMatching F P N) (Q : ↥(N ∩ F.negativeNear)) : F.NearPairs :=
  ⟨(⟨Q.val, (mem_inter.mp Q.property).2⟩,
    ⟨(M.partner Q).val, (mem_inter.mp (M.partner Q).property).2⟩), M.common Q⟩

def NearMatching.selected (M : NearMatching F P N) : Finset F.NearPairs :=
  univ.image M.index

theorem NearMatching.index_negative (M : NearMatching F P N) (Q : ↥(N ∩ F.negativeNear)) :
    F.pairNegative (M.index Q) = Q.val := rfl

theorem NearMatching.index_positive (M : NearMatching F P N) (Q : ↥(N ∩ F.negativeNear)) :
    F.pairPositive (M.index Q) = (M.partner Q).val := rfl

theorem NearMatching.negative_injective (M : NearMatching F P N) :
    Set.InjOn F.pairNegative M.selected := by
  intro i hi j hj hij
  obtain ⟨x, _, hx⟩ := mem_image.mp hi
  obtain ⟨y, _, hy⟩ := mem_image.mp hj
  have hxy : x.val = y.val := by
    rw [← M.index_negative x, ← M.index_negative y, hx, hy]
    exact hij
  exact hx.symm.trans ((congrArg M.index (Subtype.ext hxy)).trans hy)

theorem NearMatching.positive_injective (M : NearMatching F P N) :
    Set.InjOn F.pairPositive M.selected := by
  intro i hi j hj hij
  obtain ⟨x, _, hx⟩ := mem_image.mp hi
  obtain ⟨y, _, hy⟩ := mem_image.mp hj
  have hxy : (M.partner x).val = (M.partner y).val := by
    rw [← M.index_positive x, ← M.index_positive y, hx, hy]
    exact hij
  exact hx.symm.trans ((congrArg M.index (M.partner.injective (Subtype.ext hxy))).trans hy)

theorem NearMatching.selected_negative (M : NearMatching F P N) :
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

theorem NearMatching.selected_positive_subset (M : NearMatching F P N) :
    M.selected.image F.pairPositive ⊆ P ∩ F.positiveNear := by
  intro Q hQ
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hQ
  obtain ⟨x, _, rfl⟩ := mem_image.mp hi
  exact (M.partner x).property

theorem SplittingFamily.exists_nearMatching (F : SplittingFamily S D B C θ)
    {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    (P N : Finset (Block V q)) (hP : P ⊆ F.positiveCliques) (hN : N ⊆ F.negativeCliques)
    (hnonneg : ∀ e ∈ B, 0 ≤ boundary (r + 1) (indicator P - indicator N) e) :
    Nonempty (NearMatching F P N) := by
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
