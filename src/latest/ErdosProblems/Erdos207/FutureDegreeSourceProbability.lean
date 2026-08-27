/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FutureTypicalityCaps
import ErdosProblems.Erdos207.LocalInnerDegreeLoss
import ErdosProblems.Erdos207.FiniteJointConditioning

/-! # Actual link sampling controls every future degree test, with the prior bad event retained -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem FiniteLaw.jointBind_probability_le_bad_prior
    {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ω] [DecidableEq Ξ]
    (L : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ) (Good : Ω → Prop) (Event : Ω → Ξ → Prop)
    (error : ℝ≥0) (hbound : ∀ ω, 0 < L.mass ω → Good ω → (K ω).probability (Event ω) ≤ error) :
    (L.jointBind K).probability (fun z ↦ Event z.1 z.2) ≤ L.probability (fun ω ↦ ¬ Good ω) + error := by
  have hgood := L.jointBind_probability_and_le_on_support K Good Event error hbound
  have hsplit : (L.jointBind K).probability (fun z ↦ Event z.1 z.2) ≤
      (L.jointBind K).probability (fun z ↦ ¬ Good z.1 ∨ (Good z.1 ∧ Event z.1 z.2)) := by
    apply FiniteLaw.probability_mono
    intro z hz
    by_cases hg : Good z.1
    · exact Or.inr ⟨hg, hz⟩
    · exact Or.inl hg
  apply (hsplit.trans ((L.jointBind K).probability_or_le _ _)).trans
  rw [L.probability_jointBind_fst K (fun ω ↦ ¬ Good ω)]
  exact add_le_add le_rfl (hgood.trans (mul_le_of_le_one_right zero_le (L.probability_le_one Good)))

theorem FiniteLaw.jointBind_not_localFutureDegreeCaps_le
    {Ω O V : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Ω) (linkLaw : Ω → FiniteLaw (TripleSystemOn V))
    (W : Vortex V ell) (next : Fin (ell+1)) (hnonempty : ∀ i, (W.U i).Nonempty)
    (links : Ω → O → BipartiteLink V) (A P : Ω → TripleSystemOn V) (G : Ω → SimpleGraph V)
    (Good : Ω → Prop) (sigma p eta epsilon error priorError : ℝ≥0) (M s h : ℕ)
    (hp : 0 < p) (heta : 0 < eta) (hepsilon : 0 < epsilon)
    (hprior : L.probability (fun ω ↦ ¬ Good ω) ≤ priorError)
    (hgeom : ∀ ω, 0 < L.mass ω → Good ω →
      TrianglesMeetAtMostOne (W.U next) (P ω) ∧ IsSimultaneousLinkFamily (links ω) (A ω) ∧
        ∀ o, (links ω o).center ∉ W.U next)
    (hsub : ∀ ω, 0 < L.mass ω → Good ω → (linkLaw ω).SupportedOn fun T ↦ T ⊆ A ω)
    (hjoint : ∀ ω, 0 < L.mass ω → ∀ Q : TripleSystemOn V,
      (linkLaw ω).probability (fun T ↦ Q ⊆ T) ≤ sigma ^ Q.card)
    (hfan : ∀ ω, 0 < L.mass ω → Good ω → ∀ e : Sym2 V,
      e.toFinset ⊆ W.U next → (linkInnerEdgeFan (A ω) e).card ≤ M)
    (hsize : ∀ a ∈ futureLevelPairs next,
      (2*s : ℝ≥0) ≤ epsilon*p^h*eta^(h^2)*(W.U a.2).card)
    (hscalar : (2*(M : ℝ≥0)*sigma/(epsilon*p^h*eta^(h^2)))^s ≤ error) :
    (L.jointBind linkLaw).probability (fun z ↦ ¬ LocalFutureDegreeCaps W next
      (G z.1) (P z.1 ∪ z.2) p eta epsilon h) ≤
      priorError + (ell*(ell+1) : ℕ)*Fintype.card V*error := by
  apply le_trans (L.jointBind_probability_le_bad_prior linkLaw Good
    (fun ω T ↦ ¬ LocalFutureDegreeCaps W next (G ω) (P ω ∪ T) p eta epsilon h) _ ?_)
    (add_le_add hprior le_rfl)
  intro ω hω hGood
  obtain ⟨hP, hA, hout⟩ := hgeom ω hω hGood
  apply (linkLaw ω).probability_not_localFutureDegreeCaps_le W next (fun _ ↦ G ω)
    (fun T ↦ P ω ∪ T) p eta epsilon error h
  intro a ha v hv
  have hd := (mem_futureLevelPairs_iff next a).mp ha
  have hnext : next ≤ a.1.castSucc := Fin.mk_le_mk.mpr hd.1
  have hStar : a.1.castSucc ≤ a.2 := by
    rcases hd.2 with h | h
    · rw [h]
    · rw [h]
      exact Fin.castSucc_le_succ _
  have hS : W.U a.2 ⊆ W.U next := W.antitone _ _ (hnext.trans hStar)
  have hvU := W.antitone _ _ hnext hv
  have hn : (0 : ℝ≥0) < (W.U a.2).card := by exact_mod_cast card_pos.mpr (hnonempty a.2)
  have hR : 0 < epsilon*p^h*eta^(h^2)*(W.U a.2).card := by positivity
  have hf : ∀ e ∈ sourceQuasiSpokes (W.U a.2) v, (linkInnerEdgeFan (A ω) e).card ≤ M := by
    intro e he
    obtain ⟨w, hw, rfl⟩ := mem_image.mp he
    apply hfan ω hω hGood
    simpa only [Sym2.toFinset_mk_eq, insert_subset_iff, singleton_subset_iff] using And.intro hvU (hS hw)
  have hb := (linkLaw ω).probability_local_removed_neighbors_real_ge_le id (links ω) (W.U next)
    hout (A ω) hA (hsub ω hω hGood) sigma (hjoint ω hω) (G ω) (P ω) hP
    (W.U a.2) v hvU hS M hf s (epsilon*p^h*eta^(h^2)*(W.U a.2).card) hR (hsize a ha)
  rw [normalized_local_inner_degree_ratio (W.U a.2).card M sigma epsilon p eta h hn] at hb
  exact (FiniteLaw.probability_mono _ (fun _ hlarge ↦ hlarge.le)).trans (hb.trans hscalar)

end

end Erdos207
