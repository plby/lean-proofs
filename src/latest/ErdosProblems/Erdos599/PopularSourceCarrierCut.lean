/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.PopularSwitching

/-!
# Reserving an entire source carrier away from a popular cut

For disjoint source-indexed carriers which are internally reachable from
their source, the sources whose carriers meet a non-strongly-popular set
have nonstationary indices.  The proof chooses an actual finite path to
one contact in each such carrier.  These paths form a genuine disjoint
warp into the cut, not merely a joined family with uncontrolled overlaps.
-/

noncomputable section

namespace Erdos599.Popular

open Set DirectedPath Stationary

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Disjoint carriers with concrete internal finite paths from their
designated source to each of their vertices. -/
structure SourceCarrierFamily (Gamma : DWeb V) where
  carrier : Gamma.source → Set V
  disjoint : Pairwise (fun x y ↦ Disjoint (carrier x) (carrier y))
  internally_reachable : ∀ (x : Gamma.source) (v : V), v ∈ carrier x →
    ∃ p : FinitePath Gamma.graph,
      p.start = x.1 ∧ p.finish = v ∧ p.support ⊆ carrier x

namespace SourceCarrierFamily

/-- The source indices of exactly the carriers touching the given cut. -/
def cutContactIndices (F : SourceCarrierFamily Gamma)
    (U : KappaIndexed Gamma kappa) (C : Set V) : Set (Below kappa) :=
  {a | ∃ x : Gamma.source, U.f x = a ∧ (F.carrier x ∩ C).Nonempty}

/-- Choosing one internally reachable cut contact from each touching
carrier produces a finite-path warp with exactly these initial indices. -/
theorem exists_cutContactWarp (F : SourceCarrierFamily Gamma)
    (U : KappaIndexed Gamma kappa) (C : Set V) :
    ∃ W : XSWarp Gamma C,
      initialIndicesOf U W.paths W.starts_in_source =
        F.cutContactIndices U C := by
  classical
  let I := {x : Gamma.source // (F.carrier x ∩ C).Nonempty}
  have hpath : ∀ i : I, ∃ p : FinitePath Gamma.graph,
      p.start = i.1.1 ∧ p.finish ∈ C ∧ p.support ⊆ F.carrier i.1 := by
    intro i
    obtain ⟨v, hvF, hvC⟩ := i.2
    obtain ⟨p, hpStart, hpFinish, hpSupport⟩ :=
      F.internally_reachable i.1 v hvF
    exact ⟨p, hpStart, hpFinish ▸ hvC, hpSupport⟩
  choose path hstart hfinish hsupport using hpath
  let W : XSWarp Gamma C := {
    paths := Set.range path
    disjoint := by
      rintro p ⟨i, rfl⟩ q ⟨j, rfl⟩ hpq
      have hij : i.1 ≠ j.1 := by
        intro h
        have : i = j := Subtype.ext h
        exact hpq (congrArg path this)
      exact (F.disjoint hij).mono (hsupport i) (hsupport j)
    starts_in_source := by
      rintro p ⟨i, rfl⟩
      rw [hstart i]
      exact i.1.2
    ends_in_target := by
      rintro p ⟨i, rfl⟩
      exact hfinish i }
  refine ⟨W, ?_⟩
  ext a
  constructor
  · rintro ⟨p, hp, hpa⟩
    obtain ⟨i, rfl⟩ := hp
    have hs : (⟨(path i).start, W.starts_in_source ⟨i, rfl⟩⟩ :
        Gamma.source) = i.1 := Subtype.ext (hstart i)
    exact ⟨i.1, (congrArg U.f hs).symm.trans hpa, i.2⟩
  · rintro ⟨x, hxa, hxC⟩
    let i : I := ⟨x, hxC⟩
    have hp : path i ∈ W.paths := ⟨i, rfl⟩
    refine ⟨path i, hp, ?_⟩
    have hs : (⟨(path i).start, W.starts_in_source hp⟩ :
        Gamma.source) = x := Subtype.ext (hstart i)
    exact (congrArg U.f hs).trans hxa

/-- A non-strongly-popular cut cannot touch a stationary collection of
pairwise disjoint, internally source-reachable carriers. -/
theorem cutContactIndices_nonstationary (F : SourceCarrierFamily Gamma)
    (U : KappaIndexed Gamma kappa) (C : Set V)
    (hC : ¬ IsStronglyPopular U C) :
    ¬ IsStationaryBelow kappa (F.cutContactIndices U C) := by
  obtain ⟨W, hW⟩ := F.exists_cutContactWarp U C
  rw [← hW]
  exact PopularSwitching.initialIndices_nonstationary_of_warp_to_subset
    U W Set.Subset.rfl hC

/-- Reserve a source whose entire carrier avoids the cut and whose index
also avoids any previously excluded nonstationary set. -/
theorem exists_source_disjoint_cut_avoiding
    (F : SourceCarrierFamily Gamma) (U : KappaIndexed Gamma kappa)
    (C : Set V) (hC : ¬ IsStronglyPopular U C)
    (N : Set (Below kappa)) (hN : ¬ IsStationaryBelow kappa N) :
    ∃ x : Gamma.source, U.f x ∉ N ∧ Disjoint (F.carrier x) C := by
  have hcut := F.cutContactIndices_nonstationary U C hC
  have hfirst := PopularSwitching.stationary_diff_of_stationary_of_nonstationary
    U.regular U.uncountable U.f_range_stationary hN
  have hsecond := PopularSwitching.stationary_diff_of_stationary_of_nonstationary
    U.regular U.uncountable hfirst hcut
  obtain ⟨a, ⟨⟨x, hxa⟩, haN⟩, haCut⟩ := hsecond.nonempty
  refine ⟨x, hxa ▸ haN, Set.disjoint_left.mpr ?_⟩
  intro v hvF hvC
  exact haCut ⟨x, hxa, v, hvF, hvC⟩

end SourceCarrierFamily

#print axioms SourceCarrierFamily.exists_cutContactWarp
#print axioms SourceCarrierFamily.cutContactIndices_nonstationary
#print axioms SourceCarrierFamily.exists_source_disjoint_cut_avoiding

end Erdos599.Popular
