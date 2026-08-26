import ErdosProblems.Erdos593.Graph.FiniteOutdegreeColoring
import ErdosProblems.Erdos593.TripleSystem.ObligatoryDisjointUnion
import ErdosProblems.Erdos593.TripleSystem.OnePointAmalgamation
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Equiv.Fin.Basic

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Rooted abundance and obligatory one-point amalgamation

This file formalizes Section 4 of the manuscript.  It defines rooted copies and
the abundance set `R_m(F,r;H)`, constructs the uniformly finite blocking sets
at bad roots, and uses the finite-outdegree compactness lemma to prove that the
abundance restriction of an uncountably chromatic host is still uncountably
chromatic.  The final theorem combines an abundant rooted copy with an
obligatory copy of the other factor.
-/

namespace Erdos593

open scoped Cardinal

universe u v

namespace TripleSystem

variable {V W X : Type u} {E D A : Type v}

/-- A canonical countably infinite colour type living in the ambient vertex
universe. -/
abbrev CountableColor := ULift.{u} ℕ

/-- An embedding of a rooted triple system whose root has a prescribed image. -/
structure RootedEmbedding (F : TripleSystem V E) (r : V)
    (H : TripleSystem W D) (root : W) where
  /-- The underlying non-induced triple-system embedding. -/
  embedding : F.Embedding H
  /-- The selected source root is sent to the prescribed host root. -/
  map_root : embedding.vertex r = root

namespace RootedEmbedding

variable {F : TripleSystem V E} {r : V} {H : TripleSystem W D} {root : W}

/-- Regard an ordinary embedding as rooted at the image of a selected vertex. -/
def atImage (f : F.Embedding H) (r : V) : RootedEmbedding F r H (f.vertex r) where
  embedding := f
  map_root := rfl

/-- Composition of a rooted embedding with an ordinary embedding. -/
def trans {Y : Type u} {B : Type v} {K : TripleSystem Y B}
    (f : RootedEmbedding F r H root) (g : H.Embedding K) :
    RootedEmbedding F r K (g.vertex root) where
  embedding := f.embedding.trans g
  map_root := congrArg g.vertex f.map_root

/-- The host vertices in a rooted copy other than its root. -/
def offRootFinset [Fintype V] [DecidableEq V] [DecidableEq W]
    (f : RootedEmbedding F r H root) : Finset W :=
  (Finset.univ.erase r).image f.embedding.vertex

@[simp]
theorem mem_offRootFinset [Fintype V] [DecidableEq V] [DecidableEq W]
    (f : RootedEmbedding F r H root) (x : W) :
    x ∈ f.offRootFinset ↔ ∃ y : V, y ≠ r ∧ f.embedding.vertex y = x := by
  simp [offRootFinset]

theorem card_offRootFinset [Fintype V] [DecidableEq V] [DecidableEq W]
    (f : RootedEmbedding F r H root) :
    f.offRootFinset.card = Fintype.card V - 1 := by
  rw [offRootFinset, Finset.card_image_of_injective _ f.embedding.vertex.injective]
  exact Finset.card_erase_of_mem (Finset.mem_univ r)

@[simp]
theorem root_not_mem_offRootFinset [Fintype V] [DecidableEq V] [DecidableEq W]
    (f : RootedEmbedding F r H root) : root ∉ f.offRootFinset := by
  rw [mem_offRootFinset]
  rintro ⟨y, hyr, hy⟩
  apply hyr
  apply f.embedding.vertex.injective
  exact hy.trans f.map_root.symm

end RootedEmbedding

/-- Two rooted embeddings with exactly one cross-image collision combine into
an embedding of the canonical one-point amalgamation. -/
def RootedEmbedding.amalgam
    {F₀ : TripleSystem V E} {F₁ : TripleSystem X A}
    {H : TripleSystem W D} {r₀ : V} {r₁ : X} {root : W}
    (f₀ : RootedEmbedding F₀ r₀ H root)
    (f₁ : RootedEmbedding F₁ r₁ H root)
    (hcross : ∀ x y,
      f₀.embedding.vertex x = f₁.embedding.vertex y ↔ x = r₀ ∧ y = r₁) :
    (OnePointAmalgamation.amalgam F₀ F₁ r₀ r₁).Embedding H where
  vertex :=
    { toFun := OnePointAmalgamation.lift r₀ r₁
        f₀.embedding.vertex f₁.embedding.vertex (f₀.map_root.trans f₁.map_root.symm)
      inj' := OnePointAmalgamation.lift_injective r₀ r₁
        f₀.embedding.vertex f₁.embedding.vertex
        (f₀.map_root.trans f₁.map_root.symm)
        f₀.embedding.vertex.injective f₁.embedding.vertex.injective hcross }
  edge := Sum.elim f₀.embedding.edge f₁.embedding.edge
  map_edge := by
    intro e
    cases e with
    | inl e =>
        change (OnePointAmalgamation.lift r₀ r₁
          f₀.embedding.vertex f₁.embedding.vertex
            (f₀.map_root.trans f₁.map_root.symm) ''
            (OnePointAmalgamation.left r₀ r₁ '' F₀.edgeSet e)) =
          H.edgeSet (f₀.embedding.edge e)
        rw [Set.image_image]
        change f₀.embedding.vertex '' F₀.edgeSet e = _
        exact f₀.embedding.map_edge e
    | inr e =>
        change (OnePointAmalgamation.lift r₀ r₁
          f₀.embedding.vertex f₁.embedding.vertex
            (f₀.map_root.trans f₁.map_root.symm) ''
            (OnePointAmalgamation.right r₀ r₁ '' F₁.edgeSet e)) =
          H.edgeSet (f₁.embedding.edge e)
        rw [Set.image_image]
        change f₁.embedding.vertex '' F₁.edgeSet e = _
        exact f₁.embedding.map_edge e

/-- `m` rooted copies with pairwise disjoint off-root vertex sets. -/
structure RootedPacking (F : TripleSystem V E) (r : V)
    (H : TripleSystem W D) (root : W) (m : ℕ) [Fintype V]
    [DecidableEq V] [DecidableEq W] where
  /-- The indexed rooted copies. -/
  copy : Fin m → RootedEmbedding F r H root
  /-- Different copies are disjoint after deleting the common root. -/
  offRoot_disjoint : ∀ ⦃i j : Fin m⦄, i ≠ j →
    Disjoint (copy i).offRootFinset (copy j).offRootFinset

namespace RootedPacking

variable {F : TripleSystem V E} {r : V} {H : TripleSystem W D} {root : W}
variable [Fintype V] [DecidableEq V] [DecidableEq W]

/-- The empty rooted packing. -/
def zero : RootedPacking F r H root 0 where
  copy := Fin.elim0
  offRoot_disjoint := by intro i; exact Fin.elim0 i

/-- Add a rooted copy disjoint from all members of a rooted packing. -/
def snoc {m : ℕ} (p : RootedPacking F r H root m)
    (g : RootedEmbedding F r H root)
    (hdisj : ∀ i, Disjoint (p.copy i).offRootFinset g.offRootFinset) :
    RootedPacking F r H root (m + 1) where
  copy i := Sum.elim p.copy (fun _ : Fin 1 => g) (finSumFinEquiv.symm i)
  offRoot_disjoint := by
    intro i j hij
    generalize hi : finSumFinEquiv.symm i = si
    generalize hj : finSumFinEquiv.symm j = sj
    cases si with
    | inl a =>
        cases sj with
        | inl b =>
            apply p.offRoot_disjoint
            intro hab
            apply hij
            apply finSumFinEquiv.symm.injective
            simp [hi, hj, hab]
        | inr b =>
            simpa [hi, hj] using! hdisj a
    | inr a =>
        cases sj with
        | inl b =>
            simpa [hi, hj] using! (hdisj b).symm
        | inr b =>
            exfalso
            apply hij
            apply finSumFinEquiv.symm.injective
            have hab : a = b := Subsingleton.elim _ _
            simp [hi, hj, hab]

end RootedPacking

/-- A vertex supports `m` pairwise off-root-disjoint rooted copies. -/
def SupportsRootedCopies [Fintype V] [DecidableEq V] [DecidableEq W]
    (F : TripleSystem V E) (r : V) (H : TripleSystem W D)
    (m : ℕ) (root : W) : Prop :=
  Nonempty (RootedPacking F r H root m)

/-- The rooted-abundance set `R_m(F,r;H)` from Definition 4.2. -/
def rootedAbundance [Fintype V] [DecidableEq V] [DecidableEq W]
    (F : TripleSystem V E) (r : V) (H : TripleSystem W D) (m : ℕ) : Set W :=
  {root | SupportsRootedCopies F r H m root}

@[simp]
theorem supportsRootedCopies_zero [Fintype V] [DecidableEq V] [DecidableEq W]
    (F : TripleSystem V E) (r : V) (H : TripleSystem W D) (root : W) :
    SupportsRootedCopies F r H 0 root :=
  ⟨RootedPacking.zero⟩

/-- Pigeonhole principle in the form needed at the final amalgamation step:
fewer than `m` vertices cannot meet all `m` pairwise-disjoint pieces. -/
theorem exists_disjoint_piece_of_card_lt
    [DecidableEq W] {m : ℕ} (pieces : Fin m → Finset W)
    (hpair : ∀ ⦃i j⦄, i ≠ j → Disjoint (pieces i) (pieces j))
    (t : Finset W) (hcard : t.card < m) :
    ∃ i, Disjoint (pieces i) t := by
  classical
  by_contra h
  push Not at h
  have hmeet : ∀ i, ∃ x, x ∈ pieces i ∧ x ∈ t := by
    intro i
    exact Finset.not_disjoint_iff.mp (h i)
  let point : Fin m → W := fun i => Classical.choose (hmeet i)
  have hpoint_piece (i : Fin m) : point i ∈ pieces i :=
    (Classical.choose_spec (hmeet i)).1
  have hpoint_t (i : Fin m) : point i ∈ t :=
    (Classical.choose_spec (hmeet i)).2
  let pointInT : Fin m → t := fun i => ⟨point i, hpoint_t i⟩
  have hinj : Function.Injective pointInT := by
    intro i j hij
    by_contra hij'
    have hdisj := hpair hij'
    apply (Finset.disjoint_left.mp hdisj (hpoint_piece i))
    have hp : point i = point j := congrArg Subtype.val hij
    simpa [hp] using! hpoint_piece j
  have hle : m ≤ t.card := by
    simpa using! Fintype.card_le_of_injective pointInT hinj
  omega

section CountableColoring

variable (H : TripleSystem W D)

/-- A countable chromatic-cardinal bound can be represented by an actual
natural-number colouring. -/
theorem exists_natColoring_of_chromaticCardinal_le_aleph0
    (hH : H.chromaticCardinal ≤ ℵ₀) :
    ∃ c : W → CountableColor.{u}, H.IsProperColoring c := by
  apply (H.chromaticCardinal_le_mk_iff (C := CountableColor.{u})).mp
  simpa [CountableColor] using! hH

/-- An actual natural-number colouring gives the corresponding cardinal
bound. -/
theorem chromaticCardinal_le_aleph0_of_natColoring
    (hH : ∃ c : W → CountableColor.{u}, H.IsProperColoring c) :
    H.chromaticCardinal ≤ ℵ₀ := by
  have hle : H.chromaticCardinal ≤ #CountableColor.{u} :=
    (H.chromaticCardinal_le_mk_iff (C := CountableColor.{u})).mpr hH
  simpa [CountableColor] using! hle

/-- Colour two complementary vertex restrictions and tag the side.  No edge
crossing the partition is monochromatic because the two tags differ. -/
theorem exists_properColoring_sum_vertexRestrictions
    (S : Set W) {C₀ C₁ : Type u}
    (c₀ : S → C₀) (hc₀ : (H.vertexRestriction S).IsProperColoring c₀)
    (c₁ : (Sᶜ : Set W) → C₁)
    (hc₁ : (H.vertexRestriction (Sᶜ : Set W)).IsProperColoring c₁) :
    ∃ c : W → C₀ ⊕ C₁, H.IsProperColoring c := by
  classical
  let c : W → C₀ ⊕ C₁ := fun x =>
    if hx : x ∈ S then Sum.inl (c₀ ⟨x, hx⟩) else Sum.inr (c₁ ⟨x, hx⟩)
  refine ⟨c, ?_⟩
  intro e
  by_cases hin : ∃ x : W, H.Inc x e ∧ x ∈ S
  · obtain ⟨x, hxe, hxS⟩ := hin
    by_cases hout : ∃ y : W, H.Inc y e ∧ y ∉ S
    · obtain ⟨y, hye, hyS⟩ := hout
      refine ⟨x, hxe, y, hye, ?_⟩
      simp [c, hxS, hyS]
    · push Not at hout
      let d : H.RestrictedEdge S := ⟨e, fun z hze => hout z hze⟩
      obtain ⟨x₀, hx₀, y₀, hy₀, hxy⟩ := hc₀ d
      refine ⟨x₀.1, hx₀, y₀.1, hy₀, ?_⟩
      rw [show c x₀.1 = Sum.inl (c₀ x₀) by simp [c, x₀.2],
        show c y₀.1 = Sum.inl (c₀ y₀) by simp [c, y₀.2]]
      exact Sum.inl_injective.ne hxy
  · push Not at hin
    let d : H.RestrictedEdge (Sᶜ : Set W) := ⟨e, fun z hze => hin z hze⟩
    obtain ⟨x₁, hx₁, y₁, hy₁, hxy⟩ := hc₁ d
    refine ⟨x₁.1, hx₁, y₁.1, hy₁, ?_⟩
    have hxS : x₁.1 ∉ S := x₁.2
    have hyS : y₁.1 ∉ S := y₁.2
    rw [show c x₁.1 = Sum.inr (c₁ x₁) by simp [c, hxS],
      show c y₁.1 = Sum.inr (c₁ y₁) by simp [c, hyS]]
    exact Sum.inr_injective.ne hxy

end CountableColoring

section Blocking

variable [Fintype V] [DecidableEq V] [DecidableEq W]
variable (F : TripleSystem V E) (r : V) (H : TripleSystem W D)

/-- The greatest size below `m` of a rooted packing at `root`.  It is used only
at bad roots, where no packing of size `m` exists. -/
noncomputable def maximalRootedPackingSize (m : ℕ) (root : W) : ℕ :=
  by
    classical
    exact Nat.findGreatest (fun k => SupportsRootedCopies F r H k root) (m - 1)

theorem maximalRootedPackingSize_le (m : ℕ) (root : W) :
    maximalRootedPackingSize (F := F) (r := r) (H := H) m root ≤ m - 1 :=
  by
    classical
    unfold maximalRootedPackingSize
    exact Nat.findGreatest_le _

theorem supportsRootedCopies_maximalSize (m : ℕ) (root : W) :
    SupportsRootedCopies F r H
      (maximalRootedPackingSize (F := F) (r := r) (H := H) m root) root := by
  classical
  unfold maximalRootedPackingSize
  exact Nat.findGreatest_spec
    (P := fun k => SupportsRootedCopies F r H k root)
    (m := 0) (n := m - 1) (Nat.zero_le _)
    (supportsRootedCopies_zero F r H root)

/-- A chosen maximum rooted packing below `m`. -/
noncomputable def maximalRootedPacking (m : ℕ) (root : W) :
    RootedPacking F r H root
      (maximalRootedPackingSize (F := F) (r := r) (H := H) m root) :=
  Classical.choice (supportsRootedCopies_maximalSize F r H m root)

/-- The union of the off-root parts of a chosen maximum packing. -/
noncomputable def rootedBlockingFinset (m : ℕ) (root : W) : Finset W :=
  Finset.univ.biUnion fun i : Fin
      (maximalRootedPackingSize (F := F) (r := r) (H := H) m root) =>
    ((maximalRootedPacking (F := F) (r := r) (H := H) m root).copy i).offRootFinset

theorem root_not_mem_rootedBlockingFinset (m : ℕ) (root : W) :
    root ∉ rootedBlockingFinset (F := F) (r := r) (H := H) m root := by
  classical
  simp only [rootedBlockingFinset, Finset.mem_biUnion]
  rintro ⟨i, _hi, hroot⟩
  exact ((maximalRootedPacking (F := F) (r := r) (H := H) m root).copy i).root_not_mem_offRootFinset hroot

/-- Uniform size bound on the blocking set from the manuscript. -/
theorem rootedBlockingFinset_card_le (m : ℕ) (root : W) :
    (rootedBlockingFinset (F := F) (r := r) (H := H) m root).card ≤
      (m - 1) * (Fintype.card V - 1) := by
  classical
  calc
    (rootedBlockingFinset (F := F) (r := r) (H := H) m root).card ≤
        ∑ i : Fin (maximalRootedPackingSize (F := F) (r := r) (H := H) m root),
          (((maximalRootedPacking (F := F) (r := r) (H := H) m root).copy i).offRootFinset.card) := by
      simpa [rootedBlockingFinset] using!
        (Finset.card_biUnion_le (s :=
          (Finset.univ : Finset (Fin (maximalRootedPackingSize
            (F := F) (r := r) (H := H) m root))))
          (t := fun i => ((maximalRootedPacking
            (F := F) (r := r) (H := H) m root).copy i).offRootFinset))
    _ = maximalRootedPackingSize (F := F) (r := r) (H := H) m root *
        (Fintype.card V - 1) := by
      simp [RootedEmbedding.card_offRootFinset]
    _ ≤ (m - 1) * (Fintype.card V - 1) := by
      gcongr
      exact maximalRootedPackingSize_le (F := F) (r := r) (H := H) m root

/-- At a bad root, the chosen blocking set meets every rooted copy. -/
theorem rootedBlockingFinset_hits (m : ℕ) (hm : 0 < m) (root : W)
    (hbad : ¬SupportsRootedCopies F r H m root)
    (g : RootedEmbedding F r H root) :
    ∃ x, x ∈ g.offRootFinset ∧
      x ∈ rootedBlockingFinset (F := F) (r := r) (H := H) m root := by
  classical
  rw [← Finset.not_disjoint_iff]
  intro hdisj
  let p := maximalRootedPacking (F := F) (r := r) (H := H) m root
  have hpieces : ∀ i, Disjoint (p.copy i).offRootFinset g.offRootFinset := by
    intro i
    apply Finset.disjoint_left.mpr
    intro x hxi hxg
    apply (Finset.disjoint_left.mp hdisj hxg)
    simp only [rootedBlockingFinset, Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ i, hxi⟩
  have hnext : SupportsRootedCopies F r H
      (maximalRootedPackingSize (F := F) (r := r) (H := H) m root + 1) root :=
    ⟨p.snoc g hpieces⟩
  have hklt : maximalRootedPackingSize (F := F) (r := r) (H := H) m root < m := by
    have hk := maximalRootedPackingSize_le (F := F) (r := r) (H := H) m root
    omega
  by_cases heq : maximalRootedPackingSize (F := F) (r := r) (H := H) m root + 1 = m
  · exact hbad (heq ▸ hnext)
  · have hnext_lt : maximalRootedPackingSize (F := F) (r := r) (H := H) m root + 1 < m := by omega
    have hbound : maximalRootedPackingSize (F := F) (r := r) (H := H) m root + 1 ≤ m - 1 := by omega
    exact (Nat.findGreatest_is_greatest
      (P := fun k => SupportsRootedCopies F r H k root)
      (Nat.lt_succ_self _) hbound) hnext

end Blocking

section RootedAbundance

variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq W]
variable (F : TripleSystem V E) (r : V)

set_option linter.unusedSectionVars false in
/-- **Rooted-abundance lemma (manuscript Lemma 4.3).**  For a finite
obligatory rooted triple system, the vertices supporting any prescribed
positive finite number of pairwise off-root-disjoint copies still induce an
uncountably chromatic subsystem.  Edge finiteness is retained explicitly to
match the manuscript's finite-source hypothesis, although the blocking bound
itself uses only vertex finiteness. -/
theorem IsObligatory.rootedAbundance
    (hF : F.IsObligatory) (m : ℕ) (hm : 0 < m)
    (H : TripleSystem W D) (hH : ℵ₀ < H.chromaticCardinal) :
    ℵ₀ < (H.vertexRestriction
      (Erdos593.TripleSystem.rootedAbundance F r H m)).chromaticCardinal := by
  classical
  let R : Set W := Erdos593.TripleSystem.rootedAbundance F r H m
  let B : Set W := Rᶜ
  let bound : ℕ := (m - 1) * (Fintype.card V - 1)
  let targets : W → Finset W := fun x =>
    if hx : x ∈ B then
      rootedBlockingFinset (F := F) (r := r) (H := H) m x
    else ∅
  have htargets_card (x : W) : (targets x).card ≤ bound := by
    by_cases hx : x ∈ B
    · simpa [targets, hx, bound] using!
        rootedBlockingFinset_card_le (F := F) (r := r) (H := H) m x
    · simp [targets, hx, bound]
  obtain ⟨aux, haux⟩ :=
    FiniteOutdegreeColoring.exists_coloring targets bound htargets_card
  let ColorClass (i : Fin (2 * bound + 1)) : Set W :=
    {x | x ∈ B ∧ aux x = i}
  have hclass_free (i : Fin (2 * bound + 1)) :
      ¬F.Appears (H.vertexRestriction (ColorClass i)) := by
    rintro ⟨f⟩
    let root : W := (f.vertex r).1
    have hroot_class : root ∈ ColorClass i := (f.vertex r).2
    have hroot_bad : ¬SupportsRootedCopies F r H m root := by
      have hnotR : root ∉ R := hroot_class.1
      simpa [R, Erdos593.TripleSystem.rootedAbundance] using! hnotR
    let fr : RootedEmbedding F r H root :=
      (RootedEmbedding.atImage f r).trans
        (H.vertexRestrictionEmbedding (ColorClass i))
    obtain ⟨x, hxoff, hxblock⟩ :=
      rootedBlockingFinset_hits (F := F) (r := r) (H := H)
        m hm root hroot_bad fr
    obtain ⟨y, hyr, hyx⟩ := (RootedEmbedding.mem_offRootFinset fr x).mp hxoff
    have hxclass : x ∈ ColorClass i := by
      have hyclass : (f.vertex y).1 ∈ ColorClass i := (f.vertex y).2
      simpa [fr, RootedEmbedding.trans, RootedEmbedding.atImage] using! hyx ▸ hyclass
    have hroot_target : x ∈ targets root := by
      simp [targets, hroot_class.1, hxblock]
    have hxr : x ≠ root := by
      intro hxr
      apply fr.root_not_mem_offRootFinset
      simpa [hxr] using! hxoff
    have hne := haux hxr.symm (Or.inl hroot_target)
    exact hne (hroot_class.2.trans hxclass.2.symm)
  have hclass_count (i : Fin (2 * bound + 1)) :
      (H.vertexRestriction (ColorClass i)).chromaticCardinal ≤ ℵ₀ := by
    by_contra hnot
    have hunc : ℵ₀ < (H.vertexRestriction (ColorClass i)).chromaticCardinal :=
      lt_of_not_ge hnot
    exact hclass_free i
      (hF (ColorClass i) (H.RestrictedEdge (ColorClass i))
        (H.vertexRestriction (ColorClass i)) hunc)
  have hclass_coloring (i : Fin (2 * bound + 1)) :
      ∃ c : ColorClass i → CountableColor.{u},
        (H.vertexRestriction (ColorClass i)).IsProperColoring c :=
    (H.vertexRestriction (ColorClass i)).exists_natColoring_of_chromaticCardinal_le_aleph0
      (hclass_count i)
  let inner : ∀ i : Fin (2 * bound + 1), ColorClass i → CountableColor.{u} :=
    fun i => Classical.choose (hclass_coloring i)
  have hinner (i : Fin (2 * bound + 1)) :
      (H.vertexRestriction (ColorClass i)).IsProperColoring (inner i) :=
    Classical.choose_spec (hclass_coloring i)
  let innerFull (i : Fin (2 * bound + 1)) (x : W) : CountableColor.{u} :=
    if hx : x ∈ ColorClass i then inner i ⟨x, hx⟩ else default
  let cB : B → CountableColor.{u} := fun x =>
    ⟨Nat.pair (aux x.1).val (innerFull (aux x.1) x.1).down⟩
  have hcB : (H.vertexRestriction B).IsProperColoring cB := by
    intro d
    by_cases hdiff : ∃ x : B, (H.vertexRestriction B).Inc x d ∧
        ∃ y : B, (H.vertexRestriction B).Inc y d ∧ aux x.1 ≠ aux y.1
    · obtain ⟨x, hx, y, hy, hxy⟩ := hdiff
      refine ⟨x, hx, y, hy, ?_⟩
      intro hc
      have hp := congrArg ULift.down hc
      have hfirst := (Nat.pair_eq_pair.mp hp).1
      exact hxy (Fin.ext hfirst)
    · push Not at hdiff
      have hne : ((H.vertexRestriction B).edgeSet d).ncard ≠ 0 := by
        rw [(H.vertexRestriction B).edgeSet_ncard d]
        decide
      obtain ⟨x₀, hx₀⟩ := Set.nonempty_of_ncard_ne_zero hne
      let i : Fin (2 * bound + 1) := aux x₀.1
      have hall (z : B) (hz : (H.vertexRestriction B).Inc z d) : aux z.1 = i := by
        exact (hdiff x₀ hx₀ z hz).symm
      let dclass : H.RestrictedEdge (ColorClass i) :=
        ⟨d.1, fun z hz => by
          have hzB : z ∈ B := d.2 hz
          have hzi : aux z = i := hall ⟨z, hzB⟩ hz
          exact ⟨hzB, hzi⟩⟩
      obtain ⟨x, hx, y, hy, hxy⟩ := hinner i dclass
      let xB : B := ⟨x.1, x.2.1⟩
      let yB : B := ⟨y.1, y.2.1⟩
      refine ⟨xB, hx, yB, hy, ?_⟩
      have hcx : cB xB =
          ⟨Nat.pair i.val (inner i x).down⟩ := by
        change (⟨Nat.pair (aux x.1).val
          (innerFull (aux x.1) x.1).down⟩ : CountableColor.{u}) = _
        rw [x.2.2]
        simp [innerFull, x.2]
      have hcy : cB yB =
          ⟨Nat.pair i.val (inner i y).down⟩ := by
        change (⟨Nat.pair (aux y.1).val
          (innerFull (aux y.1) y.1).down⟩ : CountableColor.{u}) = _
        rw [y.2.2]
        simp [innerFull, y.2]
      rw [hcx, hcy]
      intro hc
      have hp := congrArg ULift.down hc
      exact hxy (ULift.down_injective ((Nat.pair_eq_pair.mp hp).2))
  have hBcount : (H.vertexRestriction B).chromaticCardinal ≤ ℵ₀ :=
    (H.vertexRestriction B).chromaticCardinal_le_aleph0_of_natColoring ⟨cB, hcB⟩
  by_contra hRnot
  have hRnot' : ¬ℵ₀ < (H.vertexRestriction R).chromaticCardinal := by
    simpa [R] using! hRnot
  have hRcount : (H.vertexRestriction R).chromaticCardinal ≤ ℵ₀ :=
    le_of_not_gt hRnot'
  obtain ⟨cR, hcR⟩ :=
    (H.vertexRestriction R).exists_natColoring_of_chromaticCardinal_le_aleph0 hRcount
  obtain ⟨cB₀, hcB₀⟩ :=
    (H.vertexRestriction B).exists_natColoring_of_chromaticCardinal_le_aleph0 hBcount
  obtain ⟨cSum, hcSum⟩ :=
    H.exists_properColoring_sum_vertexRestrictions R cR hcR cB₀ hcB₀
  let encode : CountableColor.{u} ⊕ CountableColor.{u} → CountableColor.{u}
    | .inl a => ⟨Nat.pair 0 a.down⟩
    | .inr b => ⟨Nat.pair 1 b.down⟩
  have hencode : Function.Injective encode := by
    intro a b hab
    cases a with
    | inl a =>
        cases b with
        | inl b =>
            simp only [encode] at hab
            congr
            apply ULift.down_injective
            exact (Nat.pair_eq_pair.mp (congrArg ULift.down hab)).2
        | inr b =>
            simp only [encode] at hab
            have := (Nat.pair_eq_pair.mp (congrArg ULift.down hab)).1
            omega
    | inr a =>
        cases b with
        | inl b =>
            simp only [encode] at hab
            have := (Nat.pair_eq_pair.mp (congrArg ULift.down hab)).1
            omega
        | inr b =>
            simp only [encode] at hab
            congr
            apply ULift.down_injective
            exact (Nat.pair_eq_pair.mp (congrArg ULift.down hab)).2
  let c : W → CountableColor.{u} := encode ∘ cSum
  have hc : H.IsProperColoring c := by
    intro e
    obtain ⟨x, hx, y, hy, hxy⟩ := hcSum e
    exact ⟨x, hx, y, hy, hencode.ne hxy⟩
  have hHcount : H.chromaticCardinal ≤ ℵ₀ :=
    H.chromaticCardinal_le_aleph0_of_natColoring ⟨c, hc⟩
  exact hH.2 hHcount

end RootedAbundance

section ObligatoryAmalgamation

variable {F₀ : TripleSystem V E} {F₁ : TripleSystem X A}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype A]
variable [DecidableEq V] [DecidableEq X]

set_option linter.unusedSectionVars false in
/-- **One-point-amalgamation closure (manuscript Proposition 4.4).**  This
includes singleton-factor cases: rooted abundance is valid there as well, and
the corresponding off-root set is empty.  The finite-edge assumptions state
the manuscript's scope explicitly even though the construction only counts
factor vertices. -/
theorem IsObligatory.onePointAmalgamation
    (h₀ : F₀.IsObligatory) (h₁ : F₁.IsObligatory) (r₀ : V) (r₁ : X) :
    (OnePointAmalgamation.amalgam F₀ F₁ r₀ r₁).IsObligatory := by
  classical
  intro W D _ H hH
  let m := Fintype.card X
  have hm : 0 < m := by
    exact Fintype.card_pos_iff.mpr ⟨r₁⟩
  let R : Set W := Erdos593.TripleSystem.rootedAbundance F₀ r₀ H m
  have hR : ℵ₀ < (H.vertexRestriction R).chromaticCardinal := by
    simpa [R] using!
      IsObligatory.rootedAbundance (F := F₀) (r := r₀) h₀ m hm H hH
  obtain ⟨g₁⟩ := h₁ R (H.RestrictedEdge R) (H.vertexRestriction R) hR
  let root : W := (g₁.vertex r₁).1
  let f₁ : RootedEmbedding F₁ r₁ H root :=
    (RootedEmbedding.atImage g₁ r₁).trans (H.vertexRestrictionEmbedding R)
  have hrootR : root ∈ R := (g₁.vertex r₁).2
  have hsupp : SupportsRootedCopies F₀ r₀ H m root := by
    change SupportsRootedCopies F₀ r₀ H m root at hrootR
    exact hrootR
  obtain ⟨p⟩ := hsupp
  have htcard : f₁.offRootFinset.card < m := by
    rw [f₁.card_offRootFinset]
    simp [m, hm]
  obtain ⟨i, hdisj⟩ := exists_disjoint_piece_of_card_lt
    (fun i => (p.copy i).offRootFinset) p.offRoot_disjoint
    f₁.offRootFinset htcard
  refine ⟨RootedEmbedding.amalgam (p.copy i) f₁ ?_⟩
  intro x y
  constructor
  · intro hxy
    have hx : x = r₀ := by
      by_contra hxr
      have hxmem : (p.copy i).embedding.vertex x ∈
          (p.copy i).offRootFinset :=
        ((p.copy i).mem_offRootFinset _).2 ⟨x, hxr, rfl⟩
      by_cases hyr : y = r₁
      · subst y
        have hxeqroot : (p.copy i).embedding.vertex x = root :=
          hxy.trans f₁.map_root
        exact (p.copy i).root_not_mem_offRootFinset
          (by simpa only [hxeqroot] using! hxmem)
      · have hymem : f₁.embedding.vertex y ∈ f₁.offRootFinset :=
          (f₁.mem_offRootFinset _).2 ⟨y, hyr, rfl⟩
        exact (Finset.disjoint_left.mp hdisj hxmem) (hxy ▸ hymem)
    have hy : y = r₁ := by
      apply f₁.embedding.vertex.injective
      calc
        f₁.embedding.vertex y = (p.copy i).embedding.vertex x := hxy.symm
        _ = (p.copy i).embedding.vertex r₀ := congrArg _ hx
        _ = root := (p.copy i).map_root
        _ = f₁.embedding.vertex r₁ := f₁.map_root.symm
    exact ⟨hx, hy⟩
  · rintro ⟨rfl, rfl⟩
    exact (p.copy i).map_root.trans f₁.map_root.symm

end ObligatoryAmalgamation

end TripleSystem

end Erdos593
