/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularRetargetedRow
import ErdosProblems.Erdos599.SingularClosedTargetRows

/-!
# Full rows which also preserve the fixed complementary domain

`SingularRetargetedRow.exists_jointBoundedTargetLinkage` gives more than a
linkage for the bounded set currently exposed by the singular construction:
the same linkage also covers every source outside the distinguished set
`A₀`.  This file fills the remaining sources with trivial paths and records
the resulting full-source row.

Consequently, every bounded approximating row can be chosen so that it links
both the current bounded request and the whole fixed complementary domain.
This removes the fixed-complement paths from the row-to-row compatibility
problem.  It deliberately does not claim that two such independently chosen
rows are forward compatible.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularJointFullRow

open SingularExtension SingularRetargetedRow SingularClosedTargetRows

universe u

variable {V : Type u}

/-- Shrinking the designated source set preserves a source-faithful target
link certificate. -/
theorem linksToTarget_mono_sources
    {G : DWeb V} {W : Set G.DPath} {S T : Set V}
    (hTS : T ⊆ S) (hW : LinksToTarget G W S) :
    LinksToTarget G W T := by
  intro a ha
  obtain ⟨p, hpW, q, rfl, hpure, hsuffix⟩ := hW a (hTS ha)
  refine ⟨Sum.inl q, hpW, q, rfl, ?_, hsuffix⟩
  apply Set.Subset.antisymm
  · rintro x ⟨hxq, hxT⟩
    have hxS : x ∈ q.support ∩ S := ⟨hxq, hTS hxT⟩
    have hxa : x = a := Set.mem_singleton_iff.1 (hpure ▸ hxS)
    exact hxa ▸ Set.mem_singleton a
  · intro x hx
    have hxa : x = a := Set.mem_singleton_iff.1 hx
    subst x
    have haS : a ∈ ({a} : Set V) := Set.mem_singleton a
    have haq : a ∈ q.support := (hpure.symm ▸ haS).1
    exact ⟨haq, ha⟩

/-- A warp is closed under its own competitor operation: two members which
meet must be the same member, so their initial vertices agree. -/
theorem competitorClosure_self_subset
    (G : DWeb V) {W : Set G.DPath} (hW : G.IsWarp W) (S : Set V) :
    G.competitorClosure W S ⊆ S := by
  rintro b ⟨a, ha, p, hpW, hpa, q, hqW, hqb, hpq⟩
  have hpqEq : p = q := by
    by_contra hne
    exact Set.not_disjoint_iff.1 hpq |>.elim fun x hx ↦
      Set.disjoint_left.1 (hW hpW hqW hne) hx.1 hx.2
  rw [hpqEq, hqb] at hpa
  exact hpa ▸ ha

/-- Two full-source rows whose union is still a warp are necessarily the
same family.  At each source, their two members meet at their common initial
vertex, so the warp condition identifies them. -/
theorem eq_of_union_isWarp_of_initialSet_eq_source
    (G : DWeb V) {W Q : Set G.DPath}
    (hWinitial : G.initialSet W = G.source)
    (hQinitial : G.initialSet Q = G.source)
    (hunion : G.IsWarp (W ∪ Q)) :
    W = Q := by
  apply Set.Subset.antisymm
  · intro p hpW
    have hpSource : p.initial ∈ G.source := by
      rw [← hWinitial]
      exact ⟨p, hpW, rfl⟩
    have hpQinitial : p.initial ∈ G.initialSet Q := by
      rwa [hQinitial]
    obtain ⟨q, hqQ, hqp⟩ := hpQinitial
    by_contra hpQ
    have hpq : p ≠ q := by
      intro heq
      exact hpQ (heq ▸ hqQ)
    exact Set.disjoint_left.1
      (hunion (Or.inl hpW) (Or.inr hqQ) hpq)
      p.initial_mem_support (hqp ▸ q.initial_mem_support)
  · intro q hqQ
    have hqSource : q.initial ∈ G.source := by
      rw [← hQinitial]
      exact ⟨q, hqQ, rfl⟩
    have hqWinitial : q.initial ∈ G.initialSet W := by
      rwa [hWinitial]
    obtain ⟨p, hpW, hpq⟩ := hqWinitial
    by_contra hqW
    have hpqNe : p ≠ q := by
      intro heq
      exact hqW (heq ▸ hpW)
    exact Set.disjoint_left.1
      (hunion (Or.inl hpW) (Or.inr hqQ) hpqNe)
      (hpq ▸ p.initial_mem_support) q.initial_mem_support

/-- Fill every source outside the initial set of a target linkage by its
trivial path. -/
def fillTargetLinkage (G : DWeb V) (D : Set V) (P : Set G.DPath) :
    Set G.DPath :=
  P ∪ G.trivialPath '' (G.source \ D)

/-- A target linkage on an arbitrary source subset extends to a full-source
finite-character warp, while retaining the original target segments. -/
theorem fillTargetLinkage_spec
    {G : DWeb V} (hNorm : G.IsNormalized)
    {D : Set V} (hD : D ⊆ G.source) {P : Set G.DPath}
    (hP : IsLinkageBetween G D G.target P) :
    G.IsWarp (fillTargetLinkage G D P) ∧
      G.HasFiniteCharacter (fillTargetLinkage G D P) ∧
      G.initialSet (fillTargetLinkage G D P) = G.source ∧
      LinksToTarget G (fillTargetLinkage G D P) D := by
  let R : Set G.DPath := G.trivialPath '' (G.source \ D)
  have hcross : ∀ p ∈ P, ∀ q ∈ R, p ≠ q →
      Disjoint p.support q.support := by
    intro p hp q hq _hpq
    obtain ⟨x, hx, rfl⟩ := hq
    rw [G.support_trivialPath]
    apply Set.disjoint_singleton_right.2
    intro hxp
    have hxInitial : x = p.initial :=
      hNorm.eq_initial_of_mem_path p hxp hx.1
    have hpInitial : p.initial ∈ D := by
      rw [← hP.initialSet_eq]
      exact ⟨p, hp, rfl⟩
    exact hx.2 (hxInitial.symm ▸ hpInitial)
  have hwarp : G.IsWarp (P ∪ R) := by
    apply Set.PairwiseDisjoint.union hP.isWarp
      (G.isWarp_trivialPaths (G.source \ D))
    exact hcross
  have hRfinite : G.HasFiniteCharacter R := by
    rintro p ⟨x, _hx, rfl⟩
    exact ⟨DirectedPath.FinitePath.trivial G.graph x, rfl⟩
  have hfinite : G.HasFiniteCharacter (P ∪ R) :=
    SingularContinuation.finiteCharacter_union G hP.finiteCharacter hRfinite
  have hinitial : G.initialSet (P ∪ R) = G.source := by
    change G.initialSet
      (P ∪ (G.trivialPath '' (G.source \ D))) = G.source
    rw [G.initialSet_union, G.initialSet_trivialPaths, hP.initialSet_eq,
      Set.union_comm, Set.sdiff_union_of_subset hD]
  have hlinksP : LinksToTarget G P D :=
    linksToTarget_of_linkageToTarget hP
  have hlinks : LinksToTarget G (P ∪ R) D := by
    intro a ha
    obtain ⟨p, hp, hpa⟩ := hlinksP a ha
    exact ⟨p, Or.inl hp, hpa⟩
  exact ⟨hwarp, hfinite, hinitial, hlinks⟩

/-- A full row whose completed target paths cover the entire fixed
complement and the bounded currently requested set. -/
structure JointFullRow (G : DWeb V) (A₀ B : Set V) where
  paths : Set G.DPath
  isWarp : G.IsWarp paths
  finiteCharacter : G.HasFiniteCharacter paths
  initialSet : G.initialSet paths = G.source
  linksJoint : LinksToTarget G paths ((G.source \ A₀) ∪ B)

namespace JointFullRow

variable {G : DWeb V} {A₀ B : Set V}

theorem links_complement (R : JointFullRow G A₀ B) :
    LinksToTarget G R.paths (G.source \ A₀) := by
  apply linksToTarget_mono_sources _ R.linksJoint
  exact Set.subset_union_left

theorem links_bounded (R : JointFullRow G A₀ B) :
    LinksToTarget G R.paths B := by
  apply linksToTarget_mono_sources _ R.linksJoint
  exact Set.subset_union_right

/-- Forgetting the complementary guarantee gives an ordinary simultaneous
target-row stage. -/
def toTargetRowStage (R : JointFullRow G A₀ B) :
    TargetRowStage G PUnit where
  sources _ := B
  paths _ := R.paths
  isWarp _ := R.isWarp
  finiteCharacter _ := R.finiteCharacter
  initialSet _ := R.initialSet
  links _ := R.links_bounded

end JointFullRow

/-- The retargeted lower-induction construction always supplies a joint
full row for a bounded request. -/
theorem exists_jointFullRow
    {kappa rho : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hrho : rho < kappa)
    {G : DWeb V} (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {A₀ B : Set V} (hA₀ : A₀ ⊆ G.source) (hB : B ⊆ A₀)
    (hBcard : #B = rho)
    {fixed : Set G.DPath}
    (hfixed : IsLinkageBetween G (G.source \ A₀) G.target fixed) :
    Nonempty (JointFullRow G A₀ B) := by
  obtain ⟨L, hL⟩ := exists_jointBoundedTargetLinkage
    hlower hrho hG hNorm hA₀ hB hBcard hfixed
  have hD : (G.source \ A₀) ∪ B ⊆ G.source := by
    rintro x (hx | hx)
    · exact hx.1
    · exact hA₀ (hB hx)
  obtain ⟨hwarp, hfinite, hinitial, hlinks⟩ :=
    fillTargetLinkage_spec hNorm hD hL
  exact ⟨⟨fillTargetLinkage G ((G.source \ A₀) ∪ B) L,
    hwarp, hfinite, hinitial, hlinks⟩⟩

/-- Strict-cardinality form of `exists_jointFullRow`. -/
theorem exists_jointFullRow_of_mk_lt
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    {G : DWeb V} (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {A₀ B : Set V} (hA₀ : A₀ ⊆ G.source) (hB : B ⊆ A₀)
    (hBcard : #B < kappa)
    {fixed : Set G.DPath}
    (hfixed : IsLinkageBetween G (G.source \ A₀) G.target fixed) :
    Nonempty (JointFullRow G A₀ B) := by
  exact exists_jointFullRow hlower hBcard hG hNorm
    hA₀ hB rfl hfixed

/-! ## The simultaneous cofinal family -/

/-- Joint full rows for all members of the singular cofinal scale.  Each
row links the fixed complementary domain in addition to its own layer. -/
structure JointLayerRows
    (G : DWeb V) (A₀ : Set V) (kappa : Cardinal.{u})
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    (hcard : #A₀ = kappa) where
  row : (i : SingularMatrix.Index kappa) →
    JointFullRow G A₀
      (SingularMatrix.sourceLayer A₀ kappa hcard
        huncountable hsingular i)

namespace JointLayerRows

variable {G : DWeb V} {A₀ : Set V} {kappa : Cardinal.{u}}
variable {huncountable : aleph0 < kappa} {hsingular : kappa.IsSingular}
variable {hcard : #A₀ = kappa}

/-- Forget the additional complementary links and retain the ordinary
simultaneous target-row stage on the canonical source layers. -/
def toTargetRowStage
    (R : JointLayerRows G A₀ kappa huncountable hsingular hcard) :
    TargetRowStage G (SingularMatrix.Index kappa) where
  sources i := SingularMatrix.sourceLayer A₀ kappa hcard
    huncountable hsingular i
  paths i := (R.row i).paths
  isWarp i := (R.row i).isWarp
  finiteCharacter i := (R.row i).finiteCharacter
  initialSet i := (R.row i).initialSet
  links i := (R.row i).links_bounded

theorem links_complement
    (R : JointLayerRows G A₀ kappa huncountable hsingular hcard)
    (i : SingularMatrix.Index kappa) :
    LinksToTarget G (R.row i).paths (G.source \ A₀) :=
  (R.row i).links_complement

/-- The apparent global-warp master criterion admits no genuinely varying
rows: every two scale columns must already be literally equal. -/
theorem rows_eq_of_globalWarp
    (R : JointLayerRows G A₀ kappa huncountable hsingular hcard)
    {fixed : Set G.DPath}
    (hglobal : G.IsWarp (fixed ∪ ⋃ i, (R.row i).paths))
    (i j : SingularMatrix.Index kappa) :
    (R.row i).paths = (R.row j).paths := by
  apply eq_of_union_isWarp_of_initialSet_eq_source G
    (R.row i).initialSet (R.row j).initialSet
  intro p hp q hq hpq
  rcases hp with hpi | hpj <;> rcases hq with hqi | hqj
  · exact hglobal
      (Or.inr (Set.mem_iUnion.2 ⟨i, hpi⟩))
      (Or.inr (Set.mem_iUnion.2 ⟨i, hqi⟩)) hpq
  · exact hglobal
      (Or.inr (Set.mem_iUnion.2 ⟨i, hpi⟩))
      (Or.inr (Set.mem_iUnion.2 ⟨j, hqj⟩)) hpq
  · exact hglobal
      (Or.inr (Set.mem_iUnion.2 ⟨j, hpj⟩))
      (Or.inr (Set.mem_iUnion.2 ⟨i, hqi⟩)) hpq
  · exact hglobal
      (Or.inr (Set.mem_iUnion.2 ⟨j, hpj⟩))
      (Or.inr (Set.mem_iUnion.2 ⟨j, hqj⟩)) hpq

/-- If the fixed linkage and all simultaneous rows were already one warp,
then no competitor closure is needed and the rows can be repeated
reflexively.  This is the strongest literal "master columns" criterion. -/
noncomputable def toClosedRows_of_globalWarp
    (R : JointLayerRows G A₀ kappa huncountable hsingular hcard)
    (fixed : Set G.DPath)
    (hglobal : G.IsWarp (fixed ∪ ⋃ i, (R.row i).paths)) :
    ClosedRows G fixed A₀ kappa huncountable hsingular hcard where
  sources i := SingularMatrix.sourceLayer A₀ kappa hcard
    huncountable hsingular i
  paths i := (R.row i).paths
  seed _ := Set.Subset.rfl
  isWarp i := (R.row i).isWarp
  finiteCharacter i := (R.row i).finiteCharacter
  initialSet i := (R.row i).initialSet
  links i := (R.row i).links_bounded
  closed _ := competitorClosure_self_subset G hglobal _

/-- A globally compatible family of the unconditional joint rows completes
the singular extension.  The premise is geometric, not cardinal: it says
that rows from distinct scale indices are mutually vertex-disjoint. -/
theorem isLinkable_of_globalWarp
    (R : JointLayerRows G A₀ kappa huncountable hsingular hcard)
    (hA₀ : A₀ ⊆ G.source) {fixed : Set G.DPath}
    (hfixed : IsLinkageBetween G (G.source \ A₀) G.target fixed)
    (hglobal : G.IsWarp (fixed ∪ ⋃ i, (R.row i).paths)) :
    IsLinkable G := by
  exact SingularExtension.isLinkable_of_targetRows
    (R.toClosedRows_of_globalWarp fixed hglobal).toTargetRows hA₀ hfixed

end JointLayerRows

/-- Lower induction constructs all cofinal joint rows simultaneously by
ordinary choice.  No compatibility between different choices is asserted. -/
theorem exists_jointLayerRows
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hkappa : aleph0 < kappa) (hsingular : kappa.IsSingular)
    {G : DWeb V} (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {A₀ : Set V} (hA₀ : A₀ ⊆ G.source) (hcard : #A₀ = kappa)
    {fixed : Set G.DPath}
    (hfixed : IsLinkageBetween G (G.source \ A₀) G.target fixed) :
    Nonempty (JointLayerRows G A₀ kappa hkappa hsingular hcard) := by
  have hexists : ∀ i : SingularMatrix.Index kappa,
      Nonempty (JointFullRow G A₀
        (SingularMatrix.sourceLayer A₀ kappa hcard hkappa hsingular i)) := by
    intro i
    apply exists_jointFullRow hlower
      (SingularMatrix.scale_below kappa hkappa hsingular i)
      hG hNorm hA₀
    · exact SingularMatrix.sourceLayer_subset A₀ kappa hcard
        hkappa hsingular i
    · exact SingularMatrix.sourceLayer_card A₀ kappa hcard
        hkappa hsingular i
    · exact hfixed
  exact ⟨⟨fun i ↦ Classical.choice (hexists i)⟩⟩

#print axioms fillTargetLinkage_spec
#print axioms eq_of_union_isWarp_of_initialSet_eq_source
#print axioms exists_jointFullRow
#print axioms exists_jointFullRow_of_mk_lt
#print axioms exists_jointLayerRows
#print axioms JointLayerRows.rows_eq_of_globalWarp
#print axioms JointLayerRows.isLinkable_of_globalWarp

end SingularJointFullRow
end CardinalInduction
end Erdos599
