/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularProgressiveExchangeAmbient
import ErdosProblems.Erdos599.HindranceGrounding

/-!
# A source-subweb linkage need not be safely deletable in the ambient web

Restricting the distinguished source to a small set and applying the lower
cardinal induction hypothesis does produce a linkage of that set to the
target.  It does not make an arbitrary such linkage safe in the ambient web.

The finite crossing web already used to audit the singular successor gives
the exact obstruction.  Its ambient source is `{d,b}` and it is normalized
and unhindered.  In the source subweb on `{d}`, the path `d-x-t1` is a full
source--target linkage.  Deleting its carrier, however, strands the surviving
source `b`: its two possible exits toward a target use either `x` or `t1`.

Thus a hindrance in the post-linkage deletion cannot in general be lifted by
simply adjoining the chosen source-subweb linkage.  An ambiently safe batch
requires an additional joint-selection argument; it does not follow from
lower-cardinal linkability alone by this transport.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularSourceSubwebSafetyCounterexample

open DirectedPath
open SingularSafeBatchCounterexample
open SingularSafeBatchCounterexample.Vertex

/-- The bad full linkage in the one-source subweb. -/
def badPaths : Set web.DPath := {(.inl dxt1 : web.DPath)}

@[simp] theorem badPaths_vertexSet :
    web.vertexSet badPaths = ({d, x, t1} : Set Vertex) := by
  ext v
  constructor
  · rintro ⟨p, hp, hvp⟩
    have hp' : p = (.inl dxt1 : web.DPath) := by
      simpa only [badPaths, Set.mem_singleton_iff] using hp
    subst p
    change v ∈ dxt1.support at hvp
    simpa only [support_dxt1] using hvp
  · intro hv
    refine ⟨.inl dxt1, by simp [badPaths], ?_⟩
    change v ∈ dxt1.support
    simpa only [support_dxt1] using hv

/-- The crossing path is a legitimate linkage from the restricted source
`{d}` to the original target. -/
theorem badPaths_linkage :
    IsLinkageBetween web ({d} : Set Vertex) web.target badPaths := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    have hp' : p = (.inl dxt1 : web.DPath) := by
      simpa only [badPaths, Set.mem_singleton_iff] using hp
    have hq' : q = (.inl dxt1 : web.DPath) := by
      simpa only [badPaths, Set.mem_singleton_iff] using hq
    exact (hpq (hp'.trans hq'.symm)).elim
  · intro p hp
    have hp' : p = (.inl dxt1 : web.DPath) := by
      simpa only [badPaths, Set.mem_singleton_iff] using hp
    subst p
    exact ⟨dxt1, rfl⟩
  · ext v
    constructor
    · rintro ⟨p, hp, hpv⟩
      have hp' : p = (.inl dxt1 : web.DPath) := by
        simpa only [badPaths, Set.mem_singleton_iff] using hp
      subst p
      change d = v at hpv
      simpa [hpv]
    · intro hv
      have hvd : v = d := by simpa using hv
      subst v
      exact ⟨.inl dxt1, by simp [badPaths], rfl⟩
  · rintro v ⟨p, hp, hpv⟩
    have hp' : p = (.inl dxt1 : web.DPath) := by
      simpa only [badPaths, Set.mem_singleton_iff] using hp
    subst p
    have hv : dxt1.finish = v := by
      change (some dxt1.finish : Option Vertex) = some v at hpv
      exact Option.some.inj hpv
    subst v
    simp [web]
  · intro p hp
    have hp' : p = (.inl dxt1 : web.DPath) := by
      simpa only [badPaths, Set.mem_singleton_iff] using hp
    subst p
    refine ⟨dxt1, rfl, ?_, ?_⟩
    · change dxt1.support ∩ (({d} : Set Vertex) ∪ web.target) =
        {dxt1.start, dxt1.finish}
      rw [support_dxt1]
      ext v
      cases v <;> simp [web, dxt1]
    · change dxt1.support ∩ ({d} : Set Vertex) = {dxt1.start}
      rw [support_dxt1]
      ext v
      cases v <;> simp [dxt1]

/-- In the residual web, every vertex reachable from `b` stays in the small
set `{b,y,q}`. -/
private def bResidualReach : Set Vertex := {b, y, q}

private theorem bResidualReach_step {u v : Vertex}
    (hu : u ∈ bResidualReach)
    (huv : (web.delete (web.vertexSet badPaths)).graph.Adj u v) :
    v ∈ bResidualReach := by
  have huvWeb : web.graph.Adj u v := huv.1
  have hvAvoid : v ∉ web.vertexSet badPaths := huv.2.2
  rw [badPaths_vertexSet] at hvAvoid
  change graph.Adj u v at huvWeb
  simp only [graph_adj] at huvWeb
  rcases huvWeb with huvWeb | huvWeb | huvWeb | huvWeb | huvWeb |
      huvWeb | huvWeb | huvWeb | huvWeb
  all_goals rcases huvWeb with ⟨rfl, rfl⟩ <;>
    simp [bResidualReach] at hu hvAvoid ⊢

private theorem walk_preserves_bResidualReach {u v : Vertex}
    (p : Walk (web.delete (web.vertexSet badPaths)).graph u v)
    (hu : u ∈ bResidualReach) : v ∈ bResidualReach := by
  induction p with
  | nil => exact hu
  | @cons a b c hab p ih =>
      exact ih (bResidualReach_step hu hab)

/-- The surviving source `b` cannot reach any surviving target after the
bad path carrier is deleted. -/
theorem b_not_reachable_after_badPaths :
    b ∉ (web.delete (web.vertexSet badPaths)).reachableToTarget := by
  rintro ⟨p, hp⟩
  have hstart : p.start = b := hp.1
  have hreach : p.finish ∈ bResidualReach := by
    exact walk_preserves_bResidualReach p.walk
      (by simpa only [hstart, bResidualReach] using (Set.mem_insert b {y, q}))
  have htarget : p.finish ∈ web.target \ web.vertexSet badPaths := hp.2
  have htargetWeb : p.finish ∈ web.target := htarget.1
  have hdisjoint : Disjoint bResidualReach web.target := by
    apply Set.disjoint_left.2
    intro v hvReach hvTarget
    cases v <;> simp [bResidualReach, web] at hvReach hvTarget
  exact Set.disjoint_left.1 hdisjoint hreach htargetWeb

/-- The bad source-subweb linkage is not an ambient safe batch. -/
theorem delete_badPaths_isHindered :
    (web.delete (web.vertexSet badPaths)).IsHindered := by
  apply (web.delete (web.vertexSet badPaths)).exists_hindrance_of_source_not_subset_reachableToTarget
  apply Set.not_subset.mpr
  refine ⟨b, ?_, b_not_reachable_after_badPaths⟩
  change b ∈ web.source \ web.vertexSet badPaths
  refine ⟨by simp [web], ?_⟩
  rw [badPaths_vertexSet]
  simp

/-- Exact failure of the proposed source-subweb transport: the ambient web
is normalized and unhindered, and the restricted-source linkage is genuine,
but deleting its carrier produces a hindrance. -/
theorem sourceSubweb_linkage_not_ambiently_safe :
    web.IsNormalized ∧ web.IsUnhindered ∧
      IsLinkageBetween (web.sourceSubweb ({d} : Set Vertex))
        (web.sourceSubweb ({d} : Set Vertex)).source
        (web.sourceSubweb ({d} : Set Vertex)).target badPaths ∧
      (web.delete (web.vertexSet badPaths)).IsHindered := by
  refine ⟨web_normalized,
    SingularProgressiveExchangeAmbient.web_unhindered, ?_,
    delete_badPaths_isHindered⟩
  refine ⟨badPaths_linkage.1, badPaths_linkage.2.1, ?_,
    badPaths_linkage.2.2.2.1, badPaths_linkage.2.2.2.2⟩
  change web.initialSet badPaths = ({d} : Set Vertex)
  exact badPaths_linkage.2.2.1

#print axioms sourceSubweb_linkage_not_ambiently_safe

end SingularSourceSubwebSafetyCounterexample
end CardinalInduction
end Erdos599
