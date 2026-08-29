/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.JoinedFamilyOwnerThinning

/-!
# Disjoint countable regions cannot capture stationary source indices

Every source in one region reaches its assigned cut endpoint inside that
region. Countable-fiber thinning would turn stationary captured indices
into a genuine stationary source--cut warp. No injectivity of the source
index function is needed.
-/

noncomputable section

namespace Erdos599.Popular

open Set Cardinal DirectedPath Stationary

universe u v

variable {V : Type u} {J : Type v} {Gamma : DWeb V} {C : Set V} {kappa : Cardinal.{u}}

structure CountableCutRegions (Gamma : DWeb V) (C : Set V) (J : Type v) where
  region : J → Set V
  countable : ∀ j, (region j).Countable
  disjoint : Pairwise (fun i j ↦ Disjoint (region i) (region j))
  endpoint : J → V
  endpoint_mem : ∀ j, endpoint j ∈ C
  source_reaches : ∀ (j : J) (x : Gamma.source), x.1 ∈ region j →
    ∃ p : FinitePath Gamma.graph, p.start = x.1 ∧ p.finish = endpoint j ∧ p.support ⊆ region j

namespace CountableCutRegions

variable (R : CountableCutRegions Gamma C J)

def capturedIndices (U : KappaIndexed Gamma kappa) : Set (Below kappa) :=
  {a | ∃ j : J, ∃ x : Gamma.source, x.1 ∈ R.region j ∧ U.f x = a}

theorem capturedIndices_nonstationary (U : KappaIndexed Gamma kappa)
    (hC : ¬ IsStronglyPopular U C) : ¬ IsStationaryBelow kappa (R.capturedIndices U) := by
  classical
  let A := R.capturedIndices U
  intro hA
  have hchoose (a : A) : ∃ j : J, ∃ x : Gamma.source, x.1 ∈ R.region j ∧ U.f x = a.1 := a.2
  choose owner source hsource hindex using hchoose
  obtain ⟨a0, ha0⟩ := hA.nonempty
  let totalOwner (a : Below kappa) : J := if ha : a ∈ A then owner ⟨a, ha⟩ else owner ⟨a0, ha0⟩
  have htotal (a : A) : totalOwner a.1 = owner a := by simp only [totalOwner, dif_pos a.2]
  have hfiber (j : J) : (A ∩ totalOwner ⁻¹' {j}).Countable := by
    have hSources : ({x : Gamma.source | x.1 ∈ R.region j} : Set Gamma.source).Countable :=
      (R.countable j).preimage Subtype.val_injective
    apply (hSources.image U.f).mono
    rintro a ⟨ha, hj⟩
    let b : A := ⟨a, ha⟩
    have hoj : owner b = j := (htotal b).symm.trans hj
    exact ⟨source b, hoj ▸ hsource b, hindex b⟩
  obtain ⟨B, hBA, hB, hOwners⟩ :=
    exists_stationary_subset_injOn_of_countable_fibers U.regular U.uncountable hA totalOwner hfiber
  let old (b : B) : A := ⟨b.1, hBA b.2⟩
  have hDifferent {a b : B} (hab : a ≠ b) : owner (old a) ≠ owner (old b) := by
    intro h
    apply hab
    apply Subtype.ext
    apply hOwners a.2 b.2
    exact (htotal (old a)).trans (h.trans (htotal (old b)).symm)
  have hpath (b : B) : ∃ p : FinitePath Gamma.graph,
      p.start = (source (old b)).1 ∧ p.finish = R.endpoint (owner (old b)) ∧
        p.support ⊆ R.region (owner (old b)) :=
    R.source_reaches _ _ (hsource (old b))
  choose path hstart hfinish hsupport using hpath
  let W : XSWarp Gamma C := {
    paths := Set.range path
    disjoint := by
      rintro p ⟨a, rfl⟩ q ⟨b, rfl⟩ hpq
      have hab : a ≠ b := fun h ↦ hpq (congrArg path h)
      exact (R.disjoint (hDifferent hab)).mono (hsupport a) (hsupport b)
    starts_in_source := by
      rintro p ⟨b, rfl⟩
      rw [hstart b]
      exact (source (old b)).2
    ends_in_target := by
      rintro p ⟨b, rfl⟩
      rw [hfinish b]
      exact R.endpoint_mem _ }
  apply hC
  refine ⟨W, hB.mono ?_⟩
  intro a ha
  let b : B := ⟨a, ha⟩
  have hp : path b ∈ W.paths := ⟨b, rfl⟩
  refine ⟨path b, hp, ?_⟩
  have hx : (⟨(path b).start, W.starts_in_source hp⟩ : Gamma.source) = source (old b) :=
    Subtype.ext (hstart b)
  exact (congrArg U.f hx).trans (hindex (old b))

#print axioms capturedIndices_nonstationary

end CountableCutRegions
end Erdos599.Popular
