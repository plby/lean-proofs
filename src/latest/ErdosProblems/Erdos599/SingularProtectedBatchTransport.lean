/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularSafeBatch

/-!
# Transporting protected singular request batches

A protected batch is constructed in a source restriction of a web.  This
module first forgets that restricted distinguished source, retaining all
path-family data in the original web.  It then specializes the construction
to a quotient after a frozen deletion and transports the family back to the
ordinary quotient.  The latter transport preserves target links and proves
that the ambient lift avoids the deleted carrier.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularProtectedBatchTransport

open SingularContinuation SingularExtension SingularPendingReentry
  SingularSafeBatch

universe u

variable {V : Type u}

/-- Forget the distinguished restricted source used to construct a protected
batch.  The graph of `protectedRequestWeb` is definitionally the graph of the
underlying web. -/
def forgetProtectedBatchFamily
    {H : DWeb V} {current reserve : Set V} {mu : Cardinal.{u}}
    (B : ProtectedBatch H current reserve mu) : Set H.DPath :=
  B.paths

/-- Transport from deletion-then-quotient to quotient-then-deletion preserves
the optional terminal coordinate. -/
@[simp] theorem terminal?_liftDeleteQuotientPathToQuotientDelete
    (G : DWeb V) (C Q : Set V)
    (p : ((G.delete Q).quotient C).DPath) :
    ((G.quotient C).delete Q).terminal?
        (G.liftDeleteQuotientPathToQuotientDelete C Q p) =
      ((G.delete Q).quotient C).terminal? p := by
  rcases p with p | r <;> rfl

/-- The composite transport used by `deletedQuotientFamily` preserves the
terminal frontier exactly.  This is the terminal-coordinate counterpart of
`deletedQuotientFamily_initialSet`. -/
theorem deletedQuotientFamily_terminalFrontier
    (G : DWeb V) (C Q : Set V)
    (U : Set ((G.delete Q).quotient C).DPath) :
    (G.quotient C).terminalFrontier
        (deletedQuotientFamily G C Q U) =
      ((G.delete Q).quotient C).terminalFrontier U := by
  rw [deletedQuotientFamily,
    (G.quotient C).terminalFrontier_liftDeleteFamily]
  ext x
  constructor
  · rintro ⟨p, ⟨q, hqU, rfl⟩, hpx⟩
    exact ⟨q, hqU, by simpa using hpx⟩
  · rintro ⟨q, hqU, hqx⟩
    exact ⟨G.liftDeleteQuotientPathToQuotientDelete C Q q,
      ⟨q, hqU, rfl⟩, by simpa using hqx⟩

/-- All path-family data of a protected batch survives forgetting its
restricted source.  The last two conjuncts are the exact source and cardinal
coordinates of the reserved initials at the new stop-over. -/
theorem protectedBatch_ambientPayload
    {H : DWeb V} {current reserve : Set V} {mu : Cardinal.{u}}
    (B : ProtectedBatch H current reserve mu) :
    let U := forgetProtectedBatchFamily B
    H.IsWarp U ∧
      H.HasFiniteCharacter U ∧
      H.initialSet U = current ∪ reserve ∧
      LinksToTarget H U current ∧
      B.reserveFrontier ⊆
        ((protectedRequestWeb H current reserve).quotient
          B.boundary).source ∧
      #B.reserveFrontier = #reserve := by
  dsimp only [forgetProtectedBatchFamily]
  exact ⟨B.separating.linkage.isWarp,
    B.separating.linkage.finiteCharacter,
    B.initialSet_eq,
    B.links_current,
    B.reserveFrontier_subset_quotientSource,
    B.mk_reserveFrontier_eq⟩

/-- Ambient payload of a full-source batch.  Unlike a `ProtectedBatch`, its
exact initial set is the entire ambient source, so a future reserve need not
be supplied when the batch is chosen.  The payload makes no post-deletion
safety claim. -/
theorem fullSourceBatch_ambientPayload
    {H : DWeb V} {current : Set V} {mu : Cardinal.{u}}
    (B : FullSourceBatch H current mu) :
    H.IsWarp B.paths ∧
      H.HasFiniteCharacter B.paths ∧
      H.initialSet B.paths = H.source ∧
      LinksToTarget H B.paths current ∧
      (H.quotient B.boundary).IsUnhindered := by
  exact ⟨B.separating.linkage.isWarp,
    B.separating.linkage.finiteCharacter,
    B.initialSet_eq,
    B.links_current,
    B.quotient_unhindered⟩

/-- Transport a protected batch constructed in `(G - Q) / C` into `G / C`.
Besides preserving its full initial set and current target links, the
transport proves that lifting the resulting quotient family to `G` cannot
meet the frozen set `Q`. -/
theorem deletedProtectedBatch_quotientPayload
    {G : DWeb V} {C Q current reserve : Set V} {mu : Cardinal.{u}}
    (B : ProtectedBatch ((G.delete Q).quotient C) current reserve mu)
    (hcurrent : current ⊆ ((G.delete Q).quotient C).source)
    (hreserve : reserve ⊆ ((G.delete Q).quotient C).source) :
    let U₀ := forgetProtectedBatchFamily B
    let R := deletedQuotientFamily G C Q U₀
    (G.quotient C).IsWarp R ∧
      (G.quotient C).HasFiniteCharacter R ∧
      (G.quotient C).initialSet R = current ∪ reserve ∧
      LinksToTarget (G.quotient C) R current ∧
      Disjoint (G.vertexSet (liftedQuotientFamily G C R)) Q ∧
      B.reserveFrontier ⊆
        ((protectedRequestWeb ((G.delete Q).quotient C) current reserve).quotient
          B.boundary).source ∧
      #B.reserveFrontier = #reserve := by
  dsimp only
  obtain ⟨hwarp, hfinite, hinitial, hlinks, hfrontier, hcard⟩ :=
    protectedBatch_ambientPayload B
  have hstart :
      ((G.delete Q).quotient C).initialSet
          (forgetProtectedBatchFamily B) ⊆
        ((G.delete Q).quotient C).source := by
    rw [hinitial]
    exact Set.union_subset hcurrent hreserve
  refine ⟨deletedQuotientFamily_isWarp hwarp,
    deletedQuotientFamily_hasFiniteCharacter hfinite,
    ?_, linksToTarget_deletedQuotientFamily hlinks,
    lift_deletedQuotientFamily_vertexSet_disjoint hstart,
    hfrontier, hcard⟩
  rw [deletedQuotientFamily_initialSet]
  exact hinitial

/-- Transport a full-source batch from `(G - Q) / C` to `G / C`.  Its
transported initial set is the whole source of the genuinely deleted
quotient, its current target links survive, and its ambient lift avoids the
frozen carrier. -/
theorem deletedFullSourceBatch_quotientPayload
    {G : DWeb V} {C Q current : Set V} {mu : Cardinal.{u}}
    (B : FullSourceBatch ((G.delete Q).quotient C) current mu) :
    let R := deletedQuotientFamily G C Q B.paths
    (G.quotient C).IsWarp R ∧
      (G.quotient C).HasFiniteCharacter R ∧
      (G.quotient C).initialSet R =
        ((G.delete Q).quotient C).source ∧
      LinksToTarget (G.quotient C) R current ∧
      Disjoint (G.vertexSet (liftedQuotientFamily G C R)) Q := by
  dsimp only
  obtain ⟨hwarp, hfinite, hinitial, hlinks, _hresidual⟩ :=
    fullSourceBatch_ambientPayload B
  have hstart :
      ((G.delete Q).quotient C).initialSet B.paths ⊆
        ((G.delete Q).quotient C).source := by
    rw [hinitial]
  exact ⟨deletedQuotientFamily_isWarp hwarp,
    deletedQuotientFamily_hasFiniteCharacter hfinite,
    deletedQuotientFamily_initialSet G C Q B.paths |>.trans hinitial,
    linksToTarget_deletedQuotientFamily hlinks,
    lift_deletedQuotientFamily_vertexSet_disjoint hstart⟩

end SingularProtectedBatchTransport
end CardinalInduction
end Erdos599
