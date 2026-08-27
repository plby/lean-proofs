/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AvailableLinkFamily
import ErdosProblems.Erdos207.FutureDegreeSourceProbability

/-! # Future-degree failure for the actual reservoir/cover joint kernel -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem FiniteLaw.jointBind_not_localFutureDegreeCaps_le_selected
    {Ω Ξ O V : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Ξ] [DecidableEq Ξ]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Ω) (kernel : Ω → FiniteLaw Ξ) (selected : Ω → Ξ → TripleSystemOn V)
    (W : Vortex V ell) (next : Fin (ell + 1)) (hnonempty : ∀ i, (W.U i).Nonempty)
    (links : Ω → O → BipartiteLink V) (A P : Ω → TripleSystemOn V) (G : Ω → SimpleGraph V)
    (Good : Ω → Prop) (sigma p eta epsilon error priorError : ℝ≥0) (M s h : ℕ)
    (hp : 0 < p) (heta : 0 < eta) (hepsilon : 0 < epsilon)
    (hprior : L.probability (fun omega ↦ ¬ Good omega) ≤ priorError)
    (hgeom : ∀ omega, 0 < L.mass omega → Good omega →
      TrianglesMeetAtMostOne (W.U next) (P omega) ∧ IsSimultaneousLinkFamily (links omega) (A omega) ∧
        ∀ o, (links omega o).center ∉ W.U next)
    (hsub : ∀ omega, 0 < L.mass omega → Good omega →
      (kernel omega).SupportedOn fun sample ↦ selected omega sample ⊆ A omega)
    (hjoint : ∀ omega, 0 < L.mass omega → ∀ Q : TripleSystemOn V,
      (kernel omega).probability (fun sample ↦ Q ⊆ selected omega sample) ≤ sigma ^ Q.card)
    (hfan : ∀ omega, 0 < L.mass omega → Good omega → ∀ e : Sym2 V,
      e.toFinset ⊆ W.U next → (linkInnerEdgeFan (A omega) e).card ≤ M)
    (hsize : ∀ a ∈ futureLevelPairs next,
      (2 * s : ℝ≥0) ≤ epsilon * p ^ h * eta ^ (h ^ 2) * (W.U a.2).card)
    (hscalar : (2 * (M : ℝ≥0) * sigma / (epsilon * p ^ h * eta ^ (h ^ 2))) ^ s ≤ error) :
    (L.jointBind kernel).probability (fun z ↦ ¬ LocalFutureDegreeCaps W next
      (G z.1) (P z.1 ∪ selected z.1 z.2) p eta epsilon h) ≤
        priorError + (ell * (ell + 1) : ℕ) * Fintype.card V * error := by
  let projected := fun omega ↦ (kernel omega).map (selected omega)
  have hs : ∀ omega, 0 < L.mass omega → Good omega →
      (projected omega).SupportedOn fun T ↦ T ⊆ A omega := by
    intro omega hm hg
    exact (hsub omega hm hg).map (selected omega) (fun _ hh ↦ hh)
  have hj : ∀ omega, 0 < L.mass omega → ∀ Q : TripleSystemOn V,
      (projected omega).probability (fun T ↦ Q ⊆ T) ≤ sigma ^ Q.card := by
    intro omega hm Q
    simpa only [projected, FiniteLaw.probability_map] using hjoint omega hm Q
  have hb := L.jointBind_not_localFutureDegreeCaps_le projected W next hnonempty links A P G
    Good sigma p eta epsilon error priorError M s h hp heta hepsilon hprior hgeom hs hj hfan hsize hscalar
  simpa only [projected, FiniteLaw.probability_jointBind, FiniteLaw.probability_map] using hb

theorem FiniteLaw.rawLinkJoint_futureDegree_failure_le
    {Ω O V : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype O] [DecidableEq O]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Ω) (kernel : Ω → FiniteLaw (TripleSystemOn V × TripleSystemOn V))
    (W : Vortex V ell) (next : Fin (ell + 1)) (hnonempty : ∀ i, (W.U i).Nonempty)
    (F : ForbiddenFamilyOn V) (links : Ω → O → BipartiteLink V)
    (A past R : Ω → TripleSystemOn V) (G : Ω → SimpleGraph V)
    (Good : Ω → Prop) (sigma p eta epsilon error priorError : ℝ≥0) (overlap s h : ℕ)
    (hp : 0 < p) (heta : 0 < eta) (hepsilon : 0 < epsilon)
    (hprior : L.probability (fun omega ↦ ¬ Good omega) ≤ priorError)
    (hstruct : ∀ omega, 0 < L.mass omega → (kernel omega).SupportedOn
      (IsSampledLinkJointOutcome F (A omega) (past omega) (links omega)))
    (hpoint : ∀ omega, 0 < L.mass omega → ∀ Q : TripleSystemOn V,
      (kernel omega).probability (fun result ↦ Q ⊆ result.1) ≤ sigma ^ Q.card)
    (hR : ∀ omega, 0 < L.mass omega → Good omega → TrianglesMeetAtMostOne (W.U next) (R omega))
    (hout : ∀ omega, 0 < L.mass omega → Good omega → ∀ o, (links omega o).center ∉ W.U next)
    (hoverlap : ∀ omega, 0 < L.mass omega → Good omega →
      ∀ x : SimultaneousLinkPair O V (links omega),
        (otherLinkCoordinates (links omega)
          (fun o ↦ linkAvailableRelation (links omega o) (A omega)) x).card ≤ overlap)
    (hsize : ∀ a ∈ futureLevelPairs next,
      (2 * s : ℝ≥0) ≤ epsilon * p ^ h * eta ^ (h ^ 2) * (W.U a.2).card)
    (hscalar : (2 * (overlap + 1 : ℝ≥0) * sigma / (epsilon * p ^ h * eta ^ (h ^ 2))) ^ s ≤ error) :
    (L.jointBind kernel).probability (fun z ↦ ¬ LocalFutureDegreeCaps W next
      (G z.1) (R z.1 ∪ z.2.2) p eta epsilon h) ≤
        priorError + (ell * (ell + 1) : ℕ) * Fintype.card V * error := by
  apply L.jointBind_not_localFutureDegreeCaps_le_selected kernel (fun _ result ↦ result.2)
    W next hnonempty links (fun omega ↦ availableLinkFamily (links omega) (A omega)) R G
    Good sigma p eta epsilon error priorError (overlap + 1) s h hp heta hepsilon hprior
  · intro omega hm hg
    exact ⟨hR omega hm hg, availableLinkFamily_isFamily _ _, hout omega hm hg⟩
  · intro omega hm _ result hr
    exact (hstruct omega hm result hr).selected_subset_availableLinkFamily
  · intro omega hm
    exact (kernel omega).sampledLinkJoint_selected_probability_le (hstruct omega hm) sigma (hpoint omega hm)
  · intro omega hm hg e he
    exact availableLinkFamily_innerFan_le_overlap_add_one (links omega) (A omega) (W.U next)
      (hout omega hm hg) overlap (hoverlap omega hm hg) e he
  · exact hsize
  · simpa only [Nat.cast_add, Nat.cast_one] using hscalar

end

end Erdos207
