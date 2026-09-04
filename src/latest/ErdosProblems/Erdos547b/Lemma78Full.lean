/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Fact72
import ErdosProblems.Erdos547b.Lemma78
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.Clique

open scoped SimpleGraph BigOperators

noncomputable section

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.Zhao78Hard

open Finset Fintype SimpleGraph

/-- The Hall calculation used in the many-leaves branch of Zhao's Lemma 7.8.

Every individual leaf has at least `|W| - l` available images.  For a set of
more than `l` leaves, the second hypothesis says that their candidate sets
cover the whole available reservoir.  When `2l <= |W|`, these are exactly the
two ranges needed for Hall's condition. -/
theorem exists_injective_choice_of_large_common_reservoir
    {ι β : Type*} [DecidableEq β]
    (W : Finset ι) (available : Finset β) (candidate : ι → Finset β) (l : ℕ)
    (hdouble : 2 * l ≤ #W)
    (hcandidate : ∀ w ∈ W, candidate w ⊆ available)
    (hsmall : ∀ w ∈ W, #W - l ≤ #(candidate w))
    (hlarge : ∀ S : Finset ι, S ⊆ W → l < #S → available ⊆ S.biUnion candidate)
    (hcapacity : #W ≤ #available) :
    ∃ image : W → β, Function.Injective image ∧
      ∀ w : W, image w ∈ candidate w := by
  classical
  rw [← Finset.all_card_le_biUnion_card_iff_exists_injective]
  intro S
  by_cases hS : S.Nonempty
  · obtain ⟨w, hwS⟩ := hS
    by_cases hcard : #S ≤ #W - l
    · calc
        #S ≤ #W - l := hcard
        _ ≤ #(candidate (w : W)) := hsmall w (w.property)
        _ ≤ #(S.biUnion fun w : W ↦ candidate w) := by
          apply card_le_card
          exact subset_biUnion_of_mem (fun w : W ↦ candidate w) hwS
    · have hSW : S.image Subtype.val ⊆ W := by
        intro x hx
        obtain ⟨w, hwS', rfl⟩ := mem_image.mp hx
        exact w.property
      have hScard : #(S.image Subtype.val) = #S :=
        card_image_iff.mpr fun _ _ _ _ h ↦ Subtype.ext h
      have hlS : l < #(S.image Subtype.val) := by
        rw [hScard]
        have hWl : l ≤ #W - l := by omega
        omega
      have havail : available ⊆
          (S.image Subtype.val).biUnion candidate :=
        hlarge (S.image Subtype.val) hSW hlS
      calc
        #S ≤ #W := by simpa using S.card_le_univ
        _ ≤ #available := hcapacity
        _ ≤ #((S.image Subtype.val).biUnion candidate) := card_le_card havail
        _ = #(S.biUnion fun w : W ↦ candidate w) := by
          congr 1
          ext x
          simp
  · simp only [not_nonempty_iff_eq_empty] at hS
    simp [hS]

/-- A convenient version of the preceding Hall lemma in which the large-set
condition is supplied by a bound on the number of leaves missing each
available vertex. -/
theorem exists_injective_choice_of_miss_bound
    {ι β : Type*} [DecidableEq ι] [DecidableEq β]
    (W : Finset ι) (available : Finset β) (candidate : ι → Finset β) (l : ℕ)
    (hdouble : 2 * l ≤ #W)
    (hcandidate : ∀ w ∈ W, candidate w ⊆ available)
    (hsmall : ∀ w ∈ W, #W - l ≤ #(candidate w))
    (hmiss : ∀ x ∈ available, #(W.filter fun w ↦ x ∉ candidate w) ≤ l)
    (hcapacity : #W ≤ #available) :
    ∃ image : W → β, Function.Injective image ∧
      ∀ w : W, image w ∈ candidate w := by
  apply exists_injective_choice_of_large_common_reservoir W available candidate l
    hdouble hcandidate hsmall
  · intro S hSW hlS x hx
    rw [mem_biUnion]
    by_contra hnone
    push_neg at hnone
    have hsub : S ⊆ W.filter fun w ↦ x ∉ candidate w := by
      intro w hw
      exact mem_filter.mpr ⟨hSW hw, hnone w hw⟩
    have := (card_le_card hsub).trans (hmiss x hx)
    omega
  · exact hcapacity

/-- Finite-type wrapper avoiding the extra subtype introduced by indexing a
Hall family with `univ`. -/
theorem exists_injective_choice_fintype_of_miss_bound
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]
    (available : Finset β) (candidate : ι → Finset β) (l : ℕ)
    (hdouble : 2 * l ≤ Fintype.card ι)
    (hcandidate : ∀ w, candidate w ⊆ available)
    (hsmall : ∀ w, Fintype.card ι - l ≤ #(candidate w))
    (hmiss : ∀ x ∈ available, #(univ.filter fun w : ι ↦ x ∉ candidate w) ≤ l)
    (hcapacity : Fintype.card ι ≤ #available) :
    ∃ image : ι → β, Function.Injective image ∧
      ∀ w, image w ∈ candidate w := by
  obtain ⟨image, hinj, hmem⟩ :=
    exists_injective_choice_of_miss_bound (univ : Finset ι) available candidate l
      (by simpa using hdouble) (fun w _ ↦ hcandidate w)
      (fun w _ ↦ by simpa using hsmall w) hmiss (by simpa using hcapacity)
  let image' : ι → β := fun w ↦ image ⟨w, mem_univ w⟩
  refine ⟨image', ?_, ?_⟩
  · intro a b hab
    have : (⟨a, mem_univ a⟩ : (univ : Finset ι)) = ⟨b, mem_univ b⟩ :=
      hinj hab
    exact congrArg Subtype.val this
  · intro w
    exact hmem ⟨w, mem_univ w⟩

/-- Exact pendant-vertex data, stated so that later edge-preservation proofs
do not have to choose a parent again. -/
def IsPendantAt {α : Type*} (T : SimpleGraph α) (leaf parent : α) : Prop :=
  T.Adj leaf parent ∧ ∀ ⦃v⦄, T.Adj leaf v → v = parent

/-- The hard combinatorial extension step in Zhao's Lemma 7.8.

`C` is an already embedded core, `W` is the large family of first-part leaves
attached by Hall, and `D` is the family of deferred second-part leaves.  The
first Hall step is exposed through its exact two numerical consequences:
each candidate set has size at least `|W|-l`, and every available vertex is
missed by at most `l` of the distinct embedded parents.  The second layer is
then attached from the global degree bound `|T|-1`; its parent is already in
`C ∪ W`, and the parent's own occupied image supplies the strictness needed
in the greedy/Hall count.

Besides producing a genuine graph copy, the theorem says that the final copy
agrees with the prescribed copy on every core vertex. -/
theorem extend_core_by_many_and_deferred_leaves
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (T : SimpleGraph α) (G : SimpleGraph β) [DecidableRel T.Adj] [DecidableRel G.Adj]
    (C W D : Finset α)
    (hCW : Disjoint C W) (hCD : Disjoint C D) (hWD : Disjoint W D)
    (hcover : (C ∪ W) ∪ D = univ)
    (coreCopy : (T.induce (C : Set α)).Copy G)
    (parentW : W → C)
    (hpendantW : ∀ w : W, IsPendantAt T w (parentW w))
    (X : Finset β) (l : ℕ)
    (hdouble : 2 * l ≤ #W)
    (hWsmall : ∀ w : W,
      #W - l ≤ #(((G.neighborFinset (coreCopy (parentW w))) ∩ X) \
        (univ.image coreCopy)))
    (hWmiss : ∀ x ∈ X \ univ.image coreCopy,
      #(univ.filter fun w : W ↦
        x ∉ ((G.neighborFinset (coreCopy (parentW w)) ∩ X) \
          (univ.image coreCopy))) ≤ l)
    (hWcapacity : #W ≤ #(X \ univ.image coreCopy))
    (parentD : D → {a : α // a ∈ C ∪ W})
    (hpendantD : ∀ d : D, IsPendantAt T d (parentD d))
    (hglobal : ∀ x ∈ X, Fintype.card α - 1 ≤ G.degree x)
    (hparentDCoreX : ∀ (d : D) (hdW : ((parentD d : {a : α // a ∈ C ∪ W}) : α) ∉ W),
      coreCopy
        (⟨parentD d, (mem_union.mp (parentD d).2).resolve_right hdW⟩ : C) ∈ X) :
    ∃ fullCopy : T.Copy G,
      ∀ c : C, fullCopy c = coreCopy c := by
  classical
  let usedCore : Finset β := univ.image coreCopy
  let candidateW : W → Finset β := fun w ↦
    ((G.neighborFinset (coreCopy (parentW w))) ∩ X) \ usedCore
  have hcandW (w : W) : candidateW w ⊆ (X \ usedCore) := by
    intro x hx
    have hx' : x ∈ ((G.neighborFinset (coreCopy (parentW w)) ∩ X) \ usedCore) := by
      simpa [candidateW] using hx
    apply mem_sdiff.mpr
    exact ⟨(mem_inter.mp (mem_sdiff.mp hx').1).2, (mem_sdiff.mp hx').2⟩
  have hsmallW (w : W) : #W - l ≤ #(candidateW w) := by
    simpa [candidateW, usedCore] using hWsmall w
  have hmissW (x : β) (hx : x ∈ X \ usedCore) :
      #(univ.filter fun w : W ↦ x ∉ candidateW w) ≤ l := by
    simpa [candidateW, usedCore] using hWmiss x hx
  obtain ⟨imageW, himageW_inj, himageW_mem⟩ :=
    exists_injective_choice_fintype_of_miss_bound
      (X \ usedCore) candidateW l
      (by simpa using hdouble) hcandW
      (fun w ↦ by simpa using hsmallW w) hmissW
      (by simpa [usedCore] using hWcapacity)
  have himageW_X (w : W) : imageW w ∈ X :=
    (mem_sdiff.mp (hcandW w (himageW_mem w))).1
  have himageW_fresh (w : W) : imageW w ∉ usedCore :=
    (mem_sdiff.mp (hcandW w (himageW_mem w))).2
  let Base := {a : α // a ∈ C ∪ W}
  let baseMap : Base → β := fun a ↦
    if ha : (a : α) ∈ W then imageW ⟨a, ha⟩
    else coreCopy ⟨a, (mem_union.mp a.2).resolve_right ha⟩
  have baseMap_of_core (c : C) : baseMap ⟨c, mem_union_left W c.2⟩ = coreCopy c := by
    have hcW : (c : α) ∉ W := Finset.disjoint_left.mp hCW c.2
    simp [baseMap, hcW]
  have baseMap_of_W (w : W) : baseMap ⟨w, mem_union_right C w.2⟩ = imageW w := by
    simp [baseMap, w.2]
  have hbaseMap_inj : Function.Injective baseMap := by
    intro a b hab
    by_cases ha : (a : α) ∈ W
    · by_cases hb : (b : α) ∈ W
      · have hw : (⟨a, ha⟩ : W) = ⟨b, hb⟩ := by
          apply himageW_inj
          simpa [baseMap, ha, hb] using hab
        apply Subtype.ext
        exact congrArg (fun x : W ↦ (x : α)) hw
      · have hfresh := himageW_fresh ⟨a, ha⟩
        exfalso
        apply hfresh
        apply mem_image.mpr
        refine ⟨(⟨b, (mem_union.mp b.2).resolve_right hb⟩ : C), mem_univ _, ?_⟩
        simpa [baseMap, ha, hb] using hab.symm
    · by_cases hb : (b : α) ∈ W
      · have hfresh := himageW_fresh ⟨b, hb⟩
        exfalso
        apply hfresh
        apply mem_image.mpr
        refine ⟨(⟨a, (mem_union.mp a.2).resolve_right ha⟩ : C), mem_univ _, ?_⟩
        simpa [baseMap, ha, hb] using hab
      · have hc : (⟨a, (mem_union.mp a.2).resolve_right ha⟩ : C) =
            ⟨b, (mem_union.mp b.2).resolve_right hb⟩ := by
          apply coreCopy.injective
          simpa [baseMap, ha, hb] using hab
        apply Subtype.ext
        exact congrArg (fun x : C ↦ (x : α)) hc
  have hbaseMap_adj : ∀ ⦃a b : Base⦄, T.Adj a b → G.Adj (baseMap a) (baseMap b) := by
    intro a b hab
    by_cases ha : (a : α) ∈ W
    · let w : W := ⟨a, ha⟩
      have hbp : (b : α) = parentW w := (hpendantW w).2 hab
      have hpC : ((parentW w : C) : α) ∈ C := (parentW w).2
      have hpW : ((parentW ⟨a, ha⟩ : C) : α) ∉ W :=
        Finset.disjoint_left.mp hCW hpC
      have hbW : (b : α) ∉ W := by simpa [hbp] using hpW
      have hbC : (b : α) ∈ C := (mem_union.mp b.2).resolve_right hbW
      have hbParent : (⟨b, hbC⟩ : C) = parentW w := Subtype.ext hbp
      have hadj := (G.mem_neighborFinset _ _).mp
        (mem_inter.mp (mem_sdiff.mp (himageW_mem w)).1).1
      simpa [baseMap, ha, hbW, w, hbParent] using hadj.symm
    · by_cases hb : (b : α) ∈ W
      · let w : W := ⟨b, hb⟩
        have hap : (a : α) = parentW w := (hpendantW w).2 hab.symm
        have hpC : ((parentW w : C) : α) ∈ C := (parentW w).2
        have hpW : ((parentW w : C) : α) ∉ W :=
          Finset.disjoint_left.mp hCW hpC
        have haC : (a : α) ∈ C := (mem_union.mp a.2).resolve_right ha
        have haParent : (⟨a, haC⟩ : C) = parentW w := Subtype.ext hap
        have hadj := (G.mem_neighborFinset _ _).mp
          (mem_inter.mp (mem_sdiff.mp (himageW_mem w)).1).1
        simpa [baseMap, ha, hb, w, haParent] using hadj
      · have habCore : (T.induce (C : Set α)).Adj
            ⟨a, (mem_union.mp a.2).resolve_right ha⟩
            ⟨b, (mem_union.mp b.2).resolve_right hb⟩ := by
          simpa using hab
        have := coreCopy.toHom.map_rel habCore
        simpa [baseMap, ha, hb] using this
  let baseCopy : (T.induce (↑(C ∪ W) : Set α)).Copy G :=
    ⟨⟨baseMap, fun {_ _} h ↦ hbaseMap_adj h⟩, hbaseMap_inj⟩
  let usedBase : Finset β := univ.image baseCopy
  have husedBaseCard : #usedBase = Fintype.card Base := by
    exact card_image_iff.mpr fun _ _ _ _ h ↦ baseCopy.injective h
  have hbaseCard : Fintype.card Base + #D = Fintype.card α := by
    dsimp only [Base]
    rw [Fintype.card_coe]
    have hdisj : Disjoint (C ∪ W) D := disjoint_union_left.mpr ⟨hCD, hWD⟩
    rw [← card_univ (α := α), ← hcover, card_union_of_disjoint hdisj]
  have hparentD_X (d : D) : baseCopy (parentD d) ∈ X := by
    by_cases hpW : ((parentD d : Base) : α) ∈ W
    · simpa [baseCopy, baseMap, hpW] using himageW_X
        (⟨parentD d, hpW⟩ : W)
    · simpa [baseCopy, baseMap, hpW] using
        hparentDCoreX d hpW
  let candidateD : D → Finset β := fun d ↦
    G.neighborFinset (baseCopy (parentD d)) \ usedBase
  have hcandidateD (d : D) : #D ≤ #(candidateD d) := by
    have hpUsed : baseCopy (parentD d) ∈ usedBase :=
      mem_image.mpr ⟨parentD d, mem_univ _, rfl⟩
    have hpNotNeighbor : baseCopy (parentD d) ∉
        G.neighborFinset (baseCopy (parentD d)) := by simp
    have hinterLt : #((G.neighborFinset (baseCopy (parentD d))) ∩ usedBase) <
        #usedBase := by
      apply card_lt_card
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨inter_subset_right, ?_⟩
      intro heq
      apply hpNotNeighbor
      have hpIn := hpUsed
      rw [← heq] at hpIn
      exact (mem_inter.mp hpIn).1
    have hdeg := hglobal (baseCopy (parentD d)) (hparentD_X d)
    rw [← G.card_neighborFinset_eq_degree] at hdeg
    have hinterLt' : #(usedBase ∩ G.neighborFinset (baseCopy (parentD d))) <
        #usedBase := by simpa [inter_comm] using hinterLt
    have hinterDeg : #(usedBase ∩ G.neighborFinset (baseCopy (parentD d))) ≤
        #(G.neighborFinset (baseCopy (parentD d))) :=
      card_le_card inter_subset_right
    have halphaPos : 0 < Fintype.card α := by
      have : 0 < #D := card_pos.mpr ⟨d, d.2⟩
      omega
    dsimp only [candidateD]
    rw [card_sdiff]
    rw [husedBaseCard] at hinterLt'
    omega
  obtain ⟨imageD, himageD_inj, himageD_mem⟩ :=
      (Finset.all_card_le_biUnion_card_iff_exists_injective
        (fun d : D ↦ candidateD d)).mp (by
        intro S
        by_cases hS : S.Nonempty
        · obtain ⟨d, hdS⟩ := hS
          calc
            #S ≤ #D := by simpa using S.card_le_univ
            _ ≤ #(candidateD d) := hcandidateD d
            _ ≤ #(S.biUnion candidateD) := by
              apply card_le_card
              exact subset_biUnion_of_mem candidateD hdS
        · simpa [not_nonempty_iff_eq_empty.mp hS])
  let fullMap : α → β := fun a ↦
    if ha : a ∈ D then imageD ⟨a, ha⟩
    else baseCopy ⟨a, by
      have haUniv : a ∈ (C ∪ W) ∪ D := by simpa [hcover]
      exact (mem_union.mp haUniv).resolve_right ha⟩
  have fullMap_of_base (a : Base) : fullMap a = baseCopy a := by
    have haD : (a : α) ∉ D :=
      Finset.disjoint_left.mp (disjoint_union_left.mpr ⟨hCD, hWD⟩) a.2
    simp [fullMap, haD]
  have fullMap_of_D (d : D) : fullMap d = imageD d := by
    simp [fullMap, d.2]
  have hfullMap_inj : Function.Injective fullMap := by
    intro a b hab
    by_cases ha : a ∈ D
    · by_cases hb : b ∈ D
      · have hd : (⟨a, ha⟩ : D) = ⟨b, hb⟩ := by
          apply himageD_inj
          simpa [fullMap, ha, hb] using hab
        exact Subtype.ext_iff.mp hd
      · have hfresh := (mem_sdiff.mp (himageD_mem ⟨a, ha⟩)).2
        exfalso
        apply hfresh
        apply mem_image.mpr
        refine ⟨(⟨b, ?_⟩ : Base), mem_univ _, ?_⟩
        · have hbUniv : b ∈ (C ∪ W) ∪ D := by simpa [hcover]
          exact (mem_union.mp hbUniv).resolve_right hb
        · simpa [fullMap, ha, hb] using hab.symm
    · by_cases hb : b ∈ D
      · have hfresh := (mem_sdiff.mp (himageD_mem ⟨b, hb⟩)).2
        exfalso
        apply hfresh
        apply mem_image.mpr
        refine ⟨(⟨a, ?_⟩ : Base), mem_univ _, ?_⟩
        · have haUniv : a ∈ (C ∪ W) ∪ D := by simpa [hcover]
          exact (mem_union.mp haUniv).resolve_right ha
        · simpa [fullMap, ha, hb] using hab
      · have hbase : (⟨a, by
            have haUniv : a ∈ (C ∪ W) ∪ D := by simpa [hcover]
            exact (mem_union.mp haUniv).resolve_right ha⟩ : Base) =
            ⟨b, by
              have hbUniv : b ∈ (C ∪ W) ∪ D := by simpa [hcover]
              exact (mem_union.mp hbUniv).resolve_right hb⟩ := by
          apply baseCopy.injective
          simpa [fullMap, ha, hb] using hab
        exact Subtype.ext_iff.mp hbase
  have hfullMap_adj : ∀ ⦃a b⦄, T.Adj a b → G.Adj (fullMap a) (fullMap b) := by
    intro a b hab
    by_cases ha : a ∈ D
    · have hbp : b = parentD ⟨a, ha⟩ := (hpendantD ⟨a, ha⟩).2 hab
      subst b
      have hpD : ((parentD ⟨a, ha⟩ : Base) : α) ∉ D :=
        Finset.disjoint_left.mp (disjoint_union_left.mpr ⟨hCD, hWD⟩)
          (parentD ⟨a, ha⟩).2
      have hadj := (G.mem_neighborFinset _ _).mp
        (mem_sdiff.mp (himageD_mem ⟨a, ha⟩)).1
      simpa [fullMap, ha, hpD] using hadj.symm
    · by_cases hb : b ∈ D
      · have hap : a = parentD ⟨b, hb⟩ := (hpendantD ⟨b, hb⟩).2 hab.symm
        subst a
        have hpD : ((parentD ⟨b, hb⟩ : Base) : α) ∉ D :=
          Finset.disjoint_left.mp (disjoint_union_left.mpr ⟨hCD, hWD⟩)
            (parentD ⟨b, hb⟩).2
        have hadj := (G.mem_neighborFinset _ _).mp
          (mem_sdiff.mp (himageD_mem ⟨b, hb⟩)).1
        simpa [fullMap, hb, hpD] using hadj
      · have habBase : (T.induce (↑(C ∪ W) : Set α)).Adj
            ⟨a, by
              have haUniv : a ∈ (C ∪ W) ∪ D := by simpa [hcover]
              exact (mem_union.mp haUniv).resolve_right ha⟩
            ⟨b, by
              have hbUniv : b ∈ (C ∪ W) ∪ D := by simpa [hcover]
              exact (mem_union.mp hbUniv).resolve_right hb⟩ := by
          simpa using hab
        have := baseCopy.toHom.map_rel habBase
        simpa [fullMap, ha, hb] using this
  let fullCopy : T.Copy G :=
    ⟨⟨fullMap, fun {_ _} h ↦ hfullMap_adj h⟩, hfullMap_inj⟩
  refine ⟨fullCopy, ?_⟩
  intro c
  change fullMap c = coreCopy c
  rw [fullMap_of_base ⟨c, mem_union_left W c.2⟩]
  exact baseMap_of_core c

/-- Source-shaped ambient-degree corollary for the hard branch of Zhao's
Lemma 7.8.  The parents of `W` are distinct and already embedded in `Y`.
The two ambient complement-degree bounds produce the small-family and
large-family Hall estimates after the occupied core images are removed.
The remaining deferred leaves are then handled by
`extend_core_by_many_and_deferred_leaves` using the global degree bound. -/
theorem extend_core_by_many_and_deferred_leaves_of_ambient
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (T : SimpleGraph α) (G : SimpleGraph β) [DecidableRel T.Adj] [DecidableRel G.Adj]
    (C W D : Finset α)
    (hCW : Disjoint C W) (hCD : Disjoint C D) (hWD : Disjoint W D)
    (hcover : (C ∪ W) ∪ D = univ)
    (coreCopy : (T.induce (C : Set α)).Copy G)
    (parentW : W → C) (hparentW_inj : Function.Injective parentW)
    (hpendantW : ∀ w : W, IsPendantAt T w (parentW w))
    (X Y : Finset β) (l : ℕ)
    (hdouble : 2 * l ≤ #W)
    (hparentWY : ∀ w : W, coreCopy (parentW w) ∈ Y)
    (hoccupiedX : #(univ.image coreCopy ∩ X) + #W ≤ #X)
    (hdegYX : ∀ y ∈ Y, #X - l ≤ #(G.neighborFinset y ∩ X))
    (hdegXY : ∀ x ∈ X, #Y - l ≤ #(G.neighborFinset x ∩ Y))
    (parentD : D → {a : α // a ∈ C ∪ W})
    (hpendantD : ∀ d : D, IsPendantAt T d (parentD d))
    (hglobal : ∀ x ∈ X, Fintype.card α - 1 ≤ G.degree x)
    (hparentDCoreX : ∀ (d : D) (hdW : ((parentD d : {a : α // a ∈ C ∪ W}) : α) ∉ W),
      coreCopy
        (⟨parentD d, (mem_union.mp (parentD d).2).resolve_right hdW⟩ : C) ∈ X) :
    ∃ fullCopy : T.Copy G,
      ∀ c : C, fullCopy c = coreCopy c := by
  classical
  let usedCore : Finset β := univ.image coreCopy
  have hcapacity : #W ≤ #(X \ usedCore) := by
    rw [card_sdiff]
    have hocc : #(usedCore ∩ X) + #W ≤ #X := by
      simpa [usedCore] using hoccupiedX
    omega
  have hsmall (w : W) :
      #W - l ≤ #((G.neighborFinset (coreCopy (parentW w)) ∩ X) \ usedCore) := by
    let N : Finset β := G.neighborFinset (coreCopy (parentW w)) ∩ X
    have hdegree : #X - l ≤ #N := by
      simpa [N] using hdegYX (coreCopy (parentW w)) (hparentWY w)
    have hocc : #(usedCore ∩ X) + #W ≤ #X := by
      simpa [usedCore] using hoccupiedX
    have hinterOcc : #(usedCore ∩ N) ≤ #(usedCore ∩ X) := by
      apply card_le_card
      intro z hz
      have hz' := mem_inter.mp hz
      exact mem_inter.mpr ⟨hz'.1, (mem_inter.mp hz'.2).2⟩
    have hinterN : #(usedCore ∩ N) ≤ #N :=
      card_le_card inter_subset_right
    change #W - l ≤ #(N \ usedCore)
    rw [card_sdiff]
    omega
  have hmiss (x : β) (hx : x ∈ X \ usedCore) :
      #(univ.filter fun w : W ↦
        x ∉ ((G.neighborFinset (coreCopy (parentW w)) ∩ X) \ usedCore)) ≤ l := by
    let bad : Finset W := univ.filter fun w : W ↦
      x ∉ ((G.neighborFinset (coreCopy (parentW w)) ∩ X) \ usedCore)
    let parentImage : W → β := fun w ↦ coreCopy (parentW w)
    have hparentImage_inj : Function.Injective parentImage :=
      coreCopy.injective.comp hparentW_inj
    have hbadCard : #(bad.image parentImage) = #bad :=
      card_image_iff.mpr fun _ _ _ _ h ↦ hparentImage_inj h
    have hbadSubset : bad.image parentImage ⊆ Y \ G.neighborFinset x := by
      intro y hy
      obtain ⟨w, hwbad, rfl⟩ := mem_image.mp hy
      have hwNot := (mem_filter.mp hwbad).2
      apply mem_sdiff.mpr
      refine ⟨hparentWY w, ?_⟩
      intro hneighbor
      have hadj : G.Adj x (coreCopy (parentW w)) :=
        (G.mem_neighborFinset _ _).mp hneighbor
      apply hwNot
      apply mem_sdiff.mpr
      exact ⟨mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj.symm,
        (mem_sdiff.mp hx).1⟩, (mem_sdiff.mp hx).2⟩
    have hcomplement : #(Y \ G.neighborFinset x) ≤ l := by
      have hdegree := hdegXY x (mem_sdiff.mp hx).1
      rw [card_sdiff]
      omega
    change #bad ≤ l
    rw [← hbadCard]
    exact (card_le_card hbadSubset).trans hcomplement
  exact extend_core_by_many_and_deferred_leaves T G C W D hCW hCD hWD hcover
    coreCopy parentW hpendantW X l hdouble hsmall
    (fun x hx ↦ by
      simpa [usedCore] using hmiss x (by simpa [usedCore] using hx))
    (by simpa [usedCore] using hcapacity) parentD hpendantD hglobal hparentDCoreX

end Erdos547b.Zhao78Hard

#print axioms Erdos547b.Zhao78Hard.exists_injective_choice_of_large_common_reservoir
#print axioms Erdos547b.Zhao78Hard.exists_injective_choice_of_miss_bound
#print axioms Erdos547b.Zhao78Hard.extend_core_by_many_and_deferred_leaves
#print axioms Erdos547b.Zhao78Hard.extend_core_by_many_and_deferred_leaves_of_ambient

/-!
# The leaf--parent flip used in Zhao's Lemma 7.8

This file isolates the finite combinatorial operation.  A collection `W` of
leaves lies in side zero and all its (not necessarily distinct) parents lie in
side one.  We move `W` to side one and its parent set to side zero.  Side one
remains independent, and the exact loss from side zero is
`|W| - |parents W|`.
-/

open Set

namespace SimpleGraph

variable {V : Type*}
variable (T : SimpleGraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel T.Adj]

/-- The local leaf predicate needed by the flip. -/
def IsLeaf (v : V) : Prop := T.degree v = 1

/-- The unique neighbor of a leaf (arbitrary, namely `v`, off the leaves). -/
noncomputable def leafParent (v : V) : V :=
  @dite V (T.IsLeaf v) (Classical.propDecidable _) (fun h =>
    Classical.choose (degree_eq_one_iff_existsUnique_adj.mp h).exists) (fun _ => v)

lemma adj_leafParent {v : V} (hv : T.IsLeaf v) :
    T.Adj v (T.leafParent v) := by
  rw [leafParent, dif_pos hv]
  exact Classical.choose_spec (degree_eq_one_iff_existsUnique_adj.mp hv).exists

lemma eq_leafParent_of_adj {v w : V} (hv : T.IsLeaf v) (hvw : T.Adj v w) :
    w = T.leafParent v := by
  have hu := degree_eq_one_iff_existsUnique_adj.mp hv
  rw [leafParent, dif_pos hv]
  exact hu.unique hvw (Classical.choose_spec hu.exists)

/-- The set of parents; `Finset.image` identifies shared parents. -/
noncomputable def leafParents (W : Finset V) : Finset V :=
  W.image T.leafParent

@[simp] lemma mem_leafParents {W : Finset V} {p : V} :
    p ∈ T.leafParents W ↔ ∃ w ∈ W, T.leafParent w = p := by
  classical
  simp [leafParents]

lemma leafParent_mem_leafParents {W : Finset V} {w : V} (hw : w ∈ W) :
    T.leafParent w ∈ T.leafParents W := by
  classical
  exact Finset.mem_image.mpr ⟨w, hw, rfl⟩

lemma card_leafParents_le (W : Finset V) :
    (T.leafParents W).card ≤ W.card := by
  classical
  exact Finset.card_image_le

/-- Vertices whose side changes in the leaf--parent flip. -/
noncomputable def flipSupport (W : Finset V) : Finset V :=
  W ∪ T.leafParents W

/-- Move the chosen leaves to side one and their parents to side zero. -/
noncomputable def flipSide (side : V → Fin 2) (W : Finset V) (v : V) : Fin 2 :=
  if v ∈ W then 1 else if v ∈ T.leafParents W then 0 else side v

/-- The finite side-`q` class of a coloring. -/
def sidePart (side : V → Fin 2) (q : Fin 2) : Finset V :=
  Finset.univ.filter fun v => side v = q

@[simp] lemma mem_sidePart {side : V → Fin 2} {q : Fin 2} {v : V} :
    v ∈ sidePart side q ↔ side v = q := by
  simp [sidePart]

lemma leafParents_subset_one {side : V → Fin 2} {W : Finset V}
    (hP1 : ∀ w ∈ W, side (T.leafParent w) = 1) :
    T.leafParents W ⊆ sidePart side 1 := by
  classical
  intro p hp
  obtain ⟨w, hw, rfl⟩ := T.mem_leafParents.mp hp
  exact mem_sidePart.mpr (hP1 w hw)

lemma leaves_subset_zero {side : V → Fin 2} {W : Finset V}
    (hW0 : ∀ w ∈ W, side w = 0) :
    W ⊆ sidePart side 0 := by
  intro w hw
  exact mem_sidePart.mpr (hW0 w hw)

lemma leaves_disjoint_leafParents {side : V → Fin 2} {W : Finset V}
    (hW0 : ∀ w ∈ W, side w = 0)
    (hP1 : ∀ w ∈ W, side (T.leafParent w) = 1) :
    Disjoint W (T.leafParents W) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvW hvP
  have hv0 : side v = 0 := hW0 v hvW
  obtain ⟨w, hw, hp⟩ := T.mem_leafParents.mp hvP
  have hv1 : side v = 1 := hp ▸ hP1 w hw
  have : (0 : Fin 2) ≠ 1 := by decide
  exact this (hv0.symm.trans hv1)

lemma flipSide_eq_of_not_mem_support {side : V → Fin 2} {W : Finset V} {v : V}
    (hv : v ∉ T.flipSupport W) : T.flipSide side W v = side v := by
  classical
  simp only [flipSupport, Finset.mem_union, not_or] at hv
  simp [flipSide, hv.1, hv.2]

lemma flipSide_leaf {side : V → Fin 2} {W : Finset V} {w : V}
    (hw : w ∈ W) : T.flipSide side W w = 1 := by
  classical
  simp [flipSide, hw]

lemma flipSide_parent {side : V → Fin 2} {W : Finset V} {p : V}
    (hp : p ∈ T.leafParents W) (hpW : p ∉ W) :
    T.flipSide side W p = 0 := by
  classical
  simp [flipSide, hpW, hp]

/-- Exact description of the new side zero. -/
lemma sidePart_zero_flipSide {side : V → Fin 2} {W : Finset V}
    (hW0 : ∀ w ∈ W, side w = 0)
    (hP1 : ∀ w ∈ W, side (T.leafParent w) = 1) :
    sidePart (T.flipSide side W) 0 =
      (sidePart side 0 \ W) ∪ T.leafParents W := by
  classical
  have hDisj := T.leaves_disjoint_leafParents hW0 hP1
  ext v
  simp only [mem_sidePart, flipSide, Finset.mem_union, Finset.mem_sdiff]
  by_cases hvW : v ∈ W
  · have hvP : v ∉ T.leafParents W :=
      Finset.disjoint_left.mp hDisj hvW
    simp [hvW, hvP]
  · by_cases hvP : v ∈ T.leafParents W
    · simp [hvW, hvP]
    · simp [hvW, hvP]

/-- Exact description of the new side one. -/
lemma sidePart_one_flipSide {side : V → Fin 2} {W : Finset V}
    (hW0 : ∀ w ∈ W, side w = 0)
    (hP1 : ∀ w ∈ W, side (T.leafParent w) = 1) :
    sidePart (T.flipSide side W) 1 =
      (sidePart side 1 \ T.leafParents W) ∪ W := by
  classical
  have hDisj := T.leaves_disjoint_leafParents hW0 hP1
  ext v
  simp only [mem_sidePart, flipSide, Finset.mem_union, Finset.mem_sdiff]
  by_cases hvW : v ∈ W
  · have hvP : v ∉ T.leafParents W :=
      Finset.disjoint_left.mp hDisj hvW
    simp [hvW, hvP]
  · by_cases hvP : v ∈ T.leafParents W
    · simp [hvW, hvP]
    · simp [hvW, hvP]

/-- Side one remains independent after the leaf--parent flip. -/
lemma isIndepSet_one_flipSide {side : V → Fin 2} {W : Finset V}
    (hInd : T.IsIndepSet {v | side v = 1})
    (hW0 : ∀ w ∈ W, side w = 0)
    (hP1 : ∀ w ∈ W, side (T.leafParent w) = 1)
    (hLeaf : ∀ w ∈ W, T.IsLeaf w) :
    T.IsIndepSet {v | T.flipSide side W v = 1} := by
  classical
  intro x hx y hy hxy hAdj
  change T.flipSide side W x = 1 at hx
  change T.flipSide side W y = 1 at hy
  have hx' : x ∈ (sidePart side 1 \ T.leafParents W) ∪ W := by
    rw [← T.sidePart_one_flipSide hW0 hP1]
    exact mem_sidePart.mpr hx
  have hy' : y ∈ (sidePart side 1 \ T.leafParents W) ∪ W := by
    rw [← T.sidePart_one_flipSide hW0 hP1]
    exact mem_sidePart.mpr hy
  rw [Finset.mem_union, Finset.mem_sdiff] at hx' hy'
  rcases hx' with hxOld | hxW
  · rcases hy' with hyOld | hyW
    · exact hInd (mem_sidePart.mp hxOld.1) (mem_sidePart.mp hyOld.1) hxy hAdj
    · have hParent : x = T.leafParent y :=
        T.eq_leafParent_of_adj (hLeaf y hyW) hAdj.symm
      exact hxOld.2 (hParent ▸ T.leafParent_mem_leafParents hyW)
  · rcases hy' with hyOld | hyW
    · have hParent : y = T.leafParent x :=
        T.eq_leafParent_of_adj (hLeaf x hxW) hAdj
      exact hyOld.2 (hParent ▸ T.leafParent_mem_leafParents hxW)
    · have hx0 : side x = 0 := hW0 x hxW
      have hy0 : side y = 0 := hW0 y hyW
      have hpx1 : side (T.leafParent x) = 1 := hP1 x hxW
      have hParent : y = T.leafParent x :=
        T.eq_leafParent_of_adj (hLeaf x hxW) hAdj
      have : (0 : Fin 2) ≠ 1 := by decide
      exact this (hy0.symm.trans (hParent ▸ hpx1))

/-- The exact side-zero cardinality after the flip. -/
lemma card_sidePart_zero_flipSide {side : V → Fin 2} {W : Finset V}
    (hW0 : ∀ w ∈ W, side w = 0)
    (hP1 : ∀ w ∈ W, side (T.leafParent w) = 1) :
    (sidePart (T.flipSide side W) 0).card =
      (sidePart side 0).card - W.card + (T.leafParents W).card := by
  classical
  rw [T.sidePart_zero_flipSide hW0 hP1, Finset.card_union_of_disjoint]
  · rw [Finset.card_sdiff_of_subset (leaves_subset_zero hW0)]
  · rw [Finset.disjoint_left]
    intro v hv0 hvP
    have hvZero : side v = 0 := mem_sidePart.mp (Finset.mem_sdiff.mp hv0).1
    obtain ⟨w, hw, hp⟩ := T.mem_leafParents.mp hvP
    have hvOne : side v = 1 := hp ▸ hP1 w hw
    have : (0 : Fin 2) ≠ 1 := by decide
    exact this (hvZero.symm.trans hvOne)

/-- Integer form of the exact loss identity, avoiding truncated subtraction. -/
lemma sidePart_zero_loss {side : V → Fin 2} {W : Finset V}
    (hW0 : ∀ w ∈ W, side w = 0)
    (hP1 : ∀ w ∈ W, side (T.leafParent w) = 1) :
    ((sidePart side 0).card : ℤ) -
        ((sidePart (T.flipSide side W) 0).card : ℤ) =
      (W.card : ℤ) - ((T.leafParents W).card : ℤ) := by
  have hWle : W.card ≤ (sidePart side 0).card :=
    Finset.card_le_card (leaves_subset_zero hW0)
  rw [T.card_sidePart_zero_flipSide hW0 hP1]
  omega

/-- Natural-number form: the new zero class plus the leaf/parent difference
is exactly the old zero class. -/
lemma card_sidePart_zero_flipSide_add_difference
    {side : V → Fin 2} {W : Finset V}
    (hW0 : ∀ w ∈ W, side w = 0)
    (hP1 : ∀ w ∈ W, side (T.leafParent w) = 1) :
    (sidePart (T.flipSide side W) 0).card +
        (W.card - (T.leafParents W).card) =
      (sidePart side 0).card := by
  have hWle : W.card ≤ (sidePart side 0).card :=
    Finset.card_le_card (leaves_subset_zero hW0)
  have hPle : (T.leafParents W).card ≤ W.card := T.card_leafParents_le W
  rw [T.card_sidePart_zero_flipSide hW0 hP1]
  omega

/-- If there are at least `ell` more selected leaves than distinct parents,
then side zero loses at least `ell` vertices. -/
lemma card_sidePart_zero_flipSide_add_le
    {side : V → Fin 2} {W : Finset V} {ell : ℕ}
    (hW0 : ∀ w ∈ W, side w = 0)
    (hP1 : ∀ w ∈ W, side (T.leafParent w) = 1)
    (hLoss : ell + (T.leafParents W).card ≤ W.card) :
    (sidePart (T.flipSide side W) 0).card + ell ≤
      (sidePart side 0).card := by
  have hExact := T.card_sidePart_zero_flipSide_add_difference hW0 hP1
  omega

/-- Any protected class disjoint from the flip support retains its old side. -/
lemma protected_side_preserved {side : V → Fin 2} {W P : Finset V}
    (hP : Disjoint P (T.flipSupport W)) :
    ∀ v ∈ P, T.flipSide side W v = side v := by
  intro v hv
  exact T.flipSide_eq_of_not_mem_support
    (fun hvs => Finset.disjoint_left.mp hP hv hvs)

/-- Bundled leaf--parent flip, including preservation of arbitrary active and
deferred vertex classes that avoid its support. -/
theorem zhao_lemma78_leaf_parent_flip
    {side : V → Fin 2} {W active deferred : Finset V}
    (hInd : T.IsIndepSet {v | side v = 1})
    (hW0 : ∀ w ∈ W, side w = 0)
    (hP1 : ∀ w ∈ W, side (T.leafParent w) = 1)
    (hLeaf : ∀ w ∈ W, T.IsLeaf w)
    (hActive : Disjoint active (T.flipSupport W))
    (hDeferred : Disjoint deferred (T.flipSupport W)) :
    T.IsIndepSet {v | T.flipSide side W v = 1} ∧
      ((sidePart side 0).card : ℤ) -
          ((sidePart (T.flipSide side W) 0).card : ℤ) =
        (W.card : ℤ) - ((T.leafParents W).card : ℤ) ∧
      (∀ v ∈ active, T.flipSide side W v = side v) ∧
      (∀ v ∈ deferred, T.flipSide side W v = side v) := by
  exact ⟨T.isIndepSet_one_flipSide hInd hW0 hP1 hLeaf,
    T.sidePart_zero_loss hW0 hP1,
    T.protected_side_preserved hActive,
    T.protected_side_preserved hDeferred⟩

#print axioms zhao_lemma78_leaf_parent_flip

end SimpleGraph
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

open scoped BigOperators

noncomputable section

namespace Zhao78Fiber

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The fiber of `p` over `y`, restricted to the finite set `W`. -/
def fiberIn (W : Finset α) (p : α → β) (y : β) : Finset α :=
  W.filter fun w ↦ p w = y

/-- Elements of `W` which are the sole member of their `p`-fiber inside `W`. -/
def uniqueFiberElements (W : Finset α) (p : α → β) : Finset α :=
  W.filter fun w ↦ (fiberIn W p (p w)).card = 1

@[simp] theorem mem_fiberIn {W : Finset α} {p : α → β} {y : β} {w : α} :
    w ∈ fiberIn W p y ↔ w ∈ W ∧ p w = y := by
  simp [fiberIn]

@[simp] theorem mem_uniqueFiberElements {W : Finset α} {p : α → β} {w : α} :
    w ∈ uniqueFiberElements W p ↔
      w ∈ W ∧ (fiberIn W p (p w)).card = 1 := by
  simp [uniqueFiberElements]

/-- Removing the singleton fibers does not change any fiber which was not a singleton. -/
theorem fiberIn_sdiff_uniqueFiberElements_eq {W : Finset α} {p : α → β} {y : β}
    (hy : (fiberIn W p y).card ≠ 1) :
    fiberIn (W \ uniqueFiberElements W p) p y = fiberIn W p y := by
  ext w
  simp only [mem_fiberIn, Finset.mem_sdiff, mem_uniqueFiberElements]
  constructor
  · intro h
    exact ⟨h.1.1, h.2⟩
  · intro h
    refine ⟨⟨h.1, ?_⟩, h.2⟩
    intro hwUnique
    apply hy
    simpa [h.2] using hwUnique.2

/-- Every nonempty fiber left after removing the singleton fibers has at least two elements. -/
theorem two_le_card_fiberIn_sdiff_uniqueFiberElements
    {W : Finset α} {p : α → β} {y : β}
    (hy : y ∈ (W \ uniqueFiberElements W p).image p) :
    2 ≤ (fiberIn (W \ uniqueFiberElements W p) p y).card := by
  obtain ⟨w, hw, hpw⟩ := Finset.mem_image.mp hy
  have hwW : w ∈ W := (Finset.mem_sdiff.mp hw).1
  have hwNotUnique : w ∉ uniqueFiberElements W p := (Finset.mem_sdiff.mp hw).2
  have hfiberNeOne : (fiberIn W p y).card ≠ 1 := by
    intro hOne
    apply hwNotUnique
    exact mem_uniqueFiberElements.mpr ⟨hwW, by simpa [hpw] using hOne⟩
  have hfiberPos : 0 < (fiberIn W p y).card := by
    rw [Finset.card_pos]
    exact ⟨w, mem_fiberIn.mpr ⟨hwW, hpw⟩⟩
  rw [fiberIn_sdiff_uniqueFiberElements_eq hfiberNeOne]
  omega

/-- If all singleton fibers are discarded, the surviving image has at most half as many
elements as the surviving domain. -/
theorem two_mul_card_image_sdiff_unique_le
    (W : Finset α) (p : α → β) :
    2 * ((W \ uniqueFiberElements W p).image p).card ≤
      (W \ uniqueFiberElements W p).card := by
  let W' := W \ uniqueFiberElements W p
  have hsum : W'.card =
      ∑ y ∈ W'.image p, (fiberIn W' p y).card := by
    simpa only [fiberIn] using Finset.card_eq_sum_card_image p W'
  rw [hsum]
  calc
    2 * (W'.image p).card = ∑ _y ∈ W'.image p, 2 := by
      simp [Nat.mul_comm]
    _ ≤ ∑ y ∈ W'.image p, (fiberIn W' p y).card := by
      exact Finset.sum_le_sum fun y hy ↦
        two_le_card_fiberIn_sdiff_uniqueFiberElements (W := W) (p := p) hy

/-- The finite-set dichotomy inequality used in Zhao's Lemma 7.8.  When fewer than `2*l`
elements lie in singleton fibers and `W` has at least `4*l` elements, deleting those
singleton fibers leaves enough repeated fibers to satisfy the required loss estimate. -/
theorem add_card_image_sdiff_unique_le
    (W : Finset α) (p : α → β) (l : ℕ)
    (hunique : (uniqueFiberElements W p).card < 2 * l)
    (hW : 4 * l ≤ W.card) :
    l + ((W \ uniqueFiberElements W p).image p).card ≤
      (W \ uniqueFiberElements W p).card := by
  have huniqueSub : uniqueFiberElements W p ⊆ W := Finset.filter_subset _ _
  have hcard : (W \ uniqueFiberElements W p).card =
      W.card - (uniqueFiberElements W p).card := by
    rw [Finset.card_sdiff_of_subset huniqueSub]
  have htwoL : 2 * l ≤ (W \ uniqueFiberElements W p).card := by
    rw [hcard]
    omega
  have htwice := two_mul_card_image_sdiff_unique_le W p
  omega

/-- The three-way form used directly in Zhao's leaf-embedding argument.  If `hatW` misses
fewer than `l` elements of an ambient set of size at least `5*l-1`, then `hatW` has at
least `4*l` elements.  Thus either many ambient elements were missed, or many elements
of `hatW` have singleton fibers, or the repeated-fiber loss inequality holds. -/
theorem ambient_missing_or_unique_or_loss
    (W₁ hatW : Finset α) (p : α → β) (l : ℕ)
    (hhat : hatW ⊆ W₁) (hW₁ : 5 * l - 1 ≤ W₁.card) :
    l ≤ (W₁ \ hatW).card ∨
      2 * l ≤ (uniqueFiberElements hatW p).card ∨
        l + ((hatW \ uniqueFiberElements hatW p).image p).card ≤
          (hatW \ uniqueFiberElements hatW p).card := by
  by_cases hmissing : l ≤ (W₁ \ hatW).card
  · exact Or.inl hmissing
  by_cases hunique : 2 * l ≤ (uniqueFiberElements hatW p).card
  · exact Or.inr (Or.inl hunique)
  right
  right
  apply add_card_image_sdiff_unique_le
  · omega
  · have hdecomp := Finset.card_sdiff_add_card_eq_card hhat
    omega

#print axioms add_card_image_sdiff_unique_le
#print axioms ambient_missing_or_unique_or_loss

end Zhao78Fiber
namespace Erdos547b.ZhaoLemma78Full74

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoFact72

theorem lemma78_of_reassignment
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (T : SimpleGraph α) (G : SimpleGraph β) [DecidableRel T.Adj] [DecidableRel G.Adj]
    (hT : T.IsTree) (oldSide newSide : α → Fin 2)
    (newActive oldActive : Finset α)
    (hindep : ∀ ⦃u v⦄, T.Adj u v → newSide u = 1 → newSide v ≠ 1)
    (hactive : ∀ x ∈ newActive, newSide x = 1)
    (hdeferred : ∀ x, newSide x = 1 → x ∉ newActive → T.degree x = 1)
    (l : ℕ)
    (hdrop : partCount newSide 0 + l ≤ partCount oldSide 0)
    (hactiveCard : #newActive ≤ #oldActive)
    (X Y : Finset β) (hXY : Disjoint X Y)
    (hXcap : partCount oldSide 0 ≤ #X)
    (hXX : ∀ a ∈ X, #X - l ≤ #((G.neighborFinset a) ∩ X))
    (hYX : ∀ b ∈ Y, #X - l ≤ #((G.neighborFinset b) ∩ X))
    (hXYdeg : ∀ a ∈ X, #oldActive ≤ #((G.neighborFinset a) ∩ Y))
    (hglobal : ∀ a ∈ X, Fintype.card α - 1 ≤ G.degree a)
    (root : α) (hrootCore : newSide root = 0 ∨ root ∈ newActive)
    (rootImage : β) (hrootImage : rootImage ∈ if newSide root = 0 then X else Y) :
    ∃ f : T.Copy G, f root = rootImage := by
  classical
  let parts : Fin 2 → Finset β := fun i ↦ if i = 0 then X else Y
  have hnewCap : partCount newSide 0 ≤ #X - l := by omega
  have hAA : ∀ a ∈ parts 0,
      partCount newSide 0 ≤ #((G.neighborFinset a) ∩ parts 0) := by
    intro a ha
    have haX : a ∈ X := by simpa [parts] using ha
    change partCount newSide 0 ≤ #((G.neighborFinset a) ∩ X)
    exact hnewCap.trans (hXX a haX)
  have hBA : ∀ b ∈ parts 1,
      partCount newSide 0 ≤ #((G.neighborFinset b) ∩ parts 0) := by
    intro b hb
    have hbY : b ∈ Y := by simpa [parts] using hb
    change partCount newSide 0 ≤ #((G.neighborFinset b) ∩ X)
    exact hnewCap.trans (hYX b hbY)
  have hAB : ∀ a ∈ parts 0,
      #newActive ≤ #((G.neighborFinset a) ∩ parts 1) := by
    intro a ha
    have haX : a ∈ X := by simpa [parts] using ha
    change #newActive ≤ #((G.neighborFinset a) ∩ Y)
    exact hactiveCard.trans (hXYdeg a haX)
  have hparts : Set.PairwiseDisjoint Set.univ parts := by
    intro i _ j _ hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · change Disjoint (parts 0) (parts 1)
      simpa [parts] using hXY
    · change Disjoint (parts 1) (parts 0)
      simpa [parts] using hXY.symm
    · exact False.elim (hij rfl)
  have hglobal' : ∀ a ∈ parts 0, Fintype.card α - 1 ≤ G.degree a := by
    intro a ha
    apply hglobal a
    simpa [parts] using ha
  have hrootImage' : rootImage ∈ parts (newSide root) := by
    by_cases hs : newSide root = 0
    · simpa [parts, hs] using hrootImage
    · have hs1 : newSide root = 1 := by
        apply Fin.eq_of_val_eq
        have hv : (newSide root).val < 2 := (newSide root).isLt
        simp only [Fin.val_one]
        omega
      simpa [parts, hs, hs1] using hrootImage
  exact fact72_part3 T G hT newSide hindep newActive hactive hdeferred
    parts hparts hAA hBA hAB hglobal' root hrootCore rootImage hrootImage'

end Erdos547b.ZhaoLemma78Full74

namespace Erdos547b.ZhaoLemma78Full74

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoFact72

/-- Zhao Lemma 7.8 in the zero-defect case, including either prescribed-root
alternative.  This is the exact `l = 0` branch of the published lemma. -/
theorem lemma7_8_zero_defect
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (T : SimpleGraph α) (G : SimpleGraph β) [DecidableRel T.Adj] [DecidableRel G.Adj]
    (hT : T.IsTree) (side : α → Fin 2)
    (hindep : ∀ ⦃u v⦄, T.Adj u v → side u = 1 → side v ≠ 1)
    (active : Finset α)
    (hactive : ∀ x ∈ active, side x = 1)
    (hdeferred : ∀ x, side x = 1 → x ∉ active → T.degree x = 1)
    (X Y : Finset β) (hXY : Disjoint X Y)
    (hXcap : partCount side 0 ≤ #X)
    (hXX : ∀ a ∈ X, #X ≤ #((G.neighborFinset a) ∩ X))
    (hYX : ∀ b ∈ Y, #X ≤ #((G.neighborFinset b) ∩ X))
    (hXYdeg : ∀ a ∈ X, #active ≤ #((G.neighborFinset a) ∩ Y))
    (hglobal : ∀ a ∈ X, Fintype.card α - 1 ≤ G.degree a)
    (root : α) (hrootCore : side root = 0 ∨ root ∈ active)
    (rootImage : β) (hrootImage : rootImage ∈ if side root = 0 then X else Y) :
    ∃ f : T.Copy G, f root = rootImage := by
  apply lemma78_of_reassignment T G hT side side active active hindep hactive hdeferred
    0 (by omega) (by rfl) X Y hXY hXcap
  · simpa using hXX
  · simpa using hYX
  · exact hXYdeg
  · exact hglobal
  · exact hrootCore
  · exact hrootImage

end Erdos547b.ZhaoLemma78Full74

#print axioms Erdos547b.ZhaoLemma78Full74.lemma7_8_zero_defect

namespace Erdos547b.ZhaoLemma78Full74

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoFact72

/-- The repeated-parent (leaf--parent flip) branch of Zhao Lemma 7.8,
with the prescribed first-part root.  All assumptions are direct
specializations of the published hypotheses plus the branch witness `W`. -/
theorem lemma7_8_repeated_parent_branch
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (T : SimpleGraph α) (G : SimpleGraph β) [DecidableRel T.Adj] [DecidableRel G.Adj]
    (hT : T.IsTree) (side : α → Fin 2)
    (hindep : ∀ ⦃u v⦄, T.Adj u v → side u = 1 → side v ≠ 1)
    (active W : Finset α)
    (hactive : ∀ x ∈ active, side x = 1)
    (hdeferred : ∀ x, side x = 1 → x ∉ active → T.degree x = 1)
    (hWzero : ∀ w ∈ W, side w = 0)
    (hWleaf : ∀ w ∈ W, T.IsLeaf w)
    (hPone : ∀ w ∈ W, side (T.leafParent w) = 1)
    (l : ℕ) (hLoss : l + #(T.leafParents W) ≤ #W)
    (X Y : Finset β) (hXY : Disjoint X Y)
    (hXcap : partCount side 0 ≤ #X)
    (hXX : ∀ a ∈ X, #X - l ≤ #((G.neighborFinset a) ∩ X))
    (hYX : ∀ b ∈ Y, #X - l ≤ #((G.neighborFinset b) ∩ X))
    (hXYdeg : ∀ a ∈ X, #active ≤ #((G.neighborFinset a) ∩ Y))
    (hglobal : ∀ a ∈ X, Fintype.card α - 1 ≤ G.degree a)
    (root : α) (hrootSide : side root = 0) (hrootW : root ∉ W)
    (rootImage : β) (hrootImage : rootImage ∈ X) :
    ∃ f : T.Copy G, f root = rootImage := by
  classical
  let newSide := T.flipSide side W
  let newActive := active \ T.leafParents W
  have hOldInd : T.IsIndepSet {v | side v = 1} := by
    intro u hu v hv huv hadj
    exact hindep hadj hu hv
  have hNewInd : T.IsIndepSet {v | newSide v = 1} := by
    exact T.isIndepSet_one_flipSide hOldInd hWzero hPone hWleaf
  have hindep' : ∀ ⦃u v⦄, T.Adj u v → newSide u = 1 → newSide v ≠ 1 := by
    intro u v huv hu hv
    exact hNewInd hu hv (T.ne_of_adj huv) huv
  have hactive' : ∀ x ∈ newActive, newSide x = 1 := by
    intro x hx
    have hxA : x ∈ active := (mem_sdiff.mp hx).1
    have hxP : x ∉ T.leafParents W := (mem_sdiff.mp hx).2
    have hxW : x ∉ W := by
      intro hxW
      have hx0 := hWzero x hxW
      have hx1 := hactive x hxA
      exact Fin.zero_ne_one (hx0.symm.trans hx1)
    simp [newSide, SimpleGraph.flipSide, hxW, hxP, hactive x hxA]
  have hdeferred' : ∀ x, newSide x = 1 → x ∉ newActive → T.degree x = 1 := by
    intro x hxside hxnot
    have hxmem : x ∈ (SimpleGraph.sidePart side 1 \ T.leafParents W) ∪ W := by
      rw [← T.sidePart_one_flipSide hWzero hPone]
      exact SimpleGraph.mem_sidePart.mpr hxside
    rcases mem_union.mp hxmem with hxold | hxW
    · have hx1 : side x = 1 := SimpleGraph.mem_sidePart.mp (mem_sdiff.mp hxold).1
      apply hdeferred x hx1
      intro hxA
      apply hxnot
      exact mem_sdiff.mpr ⟨hxA, (mem_sdiff.mp hxold).2⟩
    · exact hWleaf x hxW
  have hdrop : partCount newSide 0 + l ≤ partCount side 0 := by
    have h := T.card_sidePart_zero_flipSide_add_le hWzero hPone hLoss
    simpa [partCount, SimpleGraph.sidePart, newSide] using h
  have hactiveCard : #newActive ≤ #active :=
    card_le_card (Finset.sdiff_subset : active \ T.leafParents W ⊆ active)
  have hrootP : root ∉ T.leafParents W := by
    intro hrP
    obtain ⟨w, hw, hp⟩ := T.mem_leafParents.mp hrP
    have hr1 : side root = 1 := hp ▸ hPone w hw
    exact Fin.zero_ne_one (hrootSide.symm.trans hr1)
  have hrootNew : newSide root = 0 := by
    simp [newSide, SimpleGraph.flipSide, hrootW, hrootP, hrootSide]
  have hrootImage' : rootImage ∈ if newSide root = 0 then X else Y := by
    simpa [hrootNew] using hrootImage
  exact lemma78_of_reassignment T G hT side newSide newActive active hindep'
    hactive' hdeferred' l hdrop hactiveCard X Y hXY hXcap hXX hYX hXYdeg hglobal
    root (Or.inl hrootNew) rootImage hrootImage'

end Erdos547b.ZhaoLemma78Full74

#print axioms Erdos547b.ZhaoLemma78Full74.lemma7_8_repeated_parent_branch

namespace Erdos547b.ZhaoLemma78Full74

open Finset Fintype SimpleGraph

/-- In a finite tree with at least three vertices, two leaves cannot be adjacent. -/
theorem not_adj_of_both_degree_one_of_three_le_card
    {α : Type*} [Fintype α] [DecidableEq α]
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree)
    {u v : α} (hu : T.degree u = 1) (hv : T.degree v = 1)
    (hcard : 3 ≤ Fintype.card α) : ¬T.Adj u v := by
  intro huv
  obtain ⟨pu, hupu, huniqU⟩ := degree_eq_one_iff_existsUnique_adj.mp hu
  obtain ⟨pv, hvpv, huniqV⟩ := degree_eq_one_iff_existsUnique_adj.mp hv
  have hpu : pu = v := (huniqU v huv).symm
  have hpv : pv = u := (huniqV u huv.symm).symm
  have hall : ∀ z : α, z = u ∨ z = v := by
    intro z
    by_contra hz
    push Not at hz
    let s : Set α := {u}ᶜ
    let vs : s := ⟨v, by simpa [s] using huv.ne'⟩
    let zs : s := ⟨z, by simpa [s] using hz.1⟩
    have hvz : vs ≠ zs := by
      intro h
      exact hz.2 (Subtype.ext_iff.mp h).symm
    let : Nontrivial s := nontrivial_of_ne vs zs hvz
    have hconn : (T.induce s).Connected :=
      hT.connected.induce_compl_singleton_of_degree_eq_one hu
    have hpos : 0 < (T.induce s).degree vs :=
      hconn.preconnected.degree_pos_of_nontrivial vs
    obtain ⟨w, hw⟩ := (T.induce s).degree_pos_iff_nonempty.mp hpos
    have hvw : T.Adj v w := by simpa [s, vs] using hw
    have hwu : (w : α) = u := (huniqV w hvw).trans hpv
    exact w.2 (by simpa [s] using hwu)
  have huniv : (Finset.univ : Finset α) ⊆ {u, v} := by
    intro z _
    rcases hall z with rfl | rfl <;> simp
  have hle := Finset.card_le_card huniv
  rw [Finset.card_univ] at hle
  have hpair : ({u, v} : Finset α).card ≤ 2 := by
    exact (Finset.card_insert_le u {v}).trans_eq (by simp)
  omega

end Erdos547b.ZhaoLemma78Full74

#print axioms Erdos547b.ZhaoLemma78Full74.not_adj_of_both_degree_one_of_three_le_card

namespace Erdos547b.ZhaoLemma78Full74

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoFact72

def moveZeroLeaves74 {α : Type*} [DecidableEq α]
    (side : α → Fin 2) (W : Finset α) (x : α) : Fin 2 :=
  if x ∈ W then 1 else side x

@[simp] theorem moveZeroLeaves74_of_mem {α : Type*} [DecidableEq α]
    {side : α → Fin 2} {W : Finset α} {x : α}
    (hx : x ∈ W) : moveZeroLeaves74 side W x = 1 := by
  simp [moveZeroLeaves74, hx]

@[simp] theorem moveZeroLeaves74_of_notMem {α : Type*} [DecidableEq α]
    {side : α → Fin 2} {W : Finset α} {x : α}
    (hx : x ∉ W) : moveZeroLeaves74 side W x = side x := by
  simp [moveZeroLeaves74, hx]

theorem partCount_moveZeroLeaves74_zero
    {α : Type*} [Fintype α] [DecidableEq α]
    (side : α → Fin 2) (W : Finset α)
    (hWzero : ∀ x ∈ W, side x = 0) :
    partCount (moveZeroLeaves74 side W) 0 = partCount side 0 - #W := by
  have hfiber :
      (Finset.univ.filter fun x ↦ moveZeroLeaves74 side W x = 0) =
        (Finset.univ.filter fun x ↦ side x = 0) \ W := by
    ext x
    by_cases hx : x ∈ W
    · have hx0 := hWzero x hx
      constructor
      · intro hmem
        have hval := (mem_filter.mp hmem).2
        rw [moveZeroLeaves74, if_pos hx] at hval
        exact False.elim (Fin.zero_ne_one hval.symm)
      · intro h
        exact False.elim ((mem_sdiff.mp h).2 hx)
    · constructor
      · intro hmem
        have hside := (mem_filter.mp hmem).2
        exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _, by
          simpa [moveZeroLeaves74, hx] using hside⟩, hx⟩
      · intro hmem
        have hside := (mem_filter.mp (mem_sdiff.mp hmem).1).2
        exact mem_filter.mpr ⟨mem_univ _, by
          simpa [moveZeroLeaves74, hx] using hside⟩
  rw [partCount, partCount, hfiber, card_sdiff]
  congr 2
  ext x
  constructor
  · intro hx
    exact (mem_inter.mp hx).1
  · intro hx
    exact mem_inter.mpr ⟨hx, mem_filter.mpr ⟨mem_univ _, hWzero x hx⟩⟩

theorem moveZeroLeaves74_independent
    {α : Type*} [Fintype α] [DecidableEq α]
    (T : SimpleGraph α) (side : α → Fin 2) (W : Finset α)
    (hindep : ∀ ⦃u v⦄, T.Adj u v → side u = 1 → side v ≠ 1)
    (hWindep : T.IsIndepSet (W : Set α))
    (hWaway : ∀ ⦃w v⦄, w ∈ W → T.Adj w v → side v ≠ 1) :
    ∀ ⦃u v⦄, T.Adj u v → moveZeroLeaves74 side W u = 1 →
      moveZeroLeaves74 side W v ≠ 1 := by
  intro u v huv hu hv
  by_cases huW : u ∈ W
  · by_cases hvW : v ∈ W
    · exact hWindep huW hvW (T.ne_of_adj huv) huv
    · have hvOld : side v = 1 := by simpa [moveZeroLeaves74, hvW] using hv
      exact hWaway huW huv hvOld
  · have huOld : side u = 1 := by simpa [moveZeroLeaves74, huW] using hu
    by_cases hvW : v ∈ W
    · have huNotOne : side u ≠ 1 := hWaway hvW huv.symm
      exact huNotOne huOld
    · have hvOld : side v = 1 := by simpa [moveZeroLeaves74, hvW] using hv
      exact hindep huv huOld hvOld

/-- The easy branch of Zhao's Lemma 7.8: if `l` independent side-zero leaves
have all their neighbors on side zero, move those leaves to the deferred side
and apply Fact 7.2(3).  This helper includes the prescribed-root conclusion. -/
theorem lemma7_8_movable_parent_branch
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (T : SimpleGraph α) (G : SimpleGraph β) [DecidableRel T.Adj] [DecidableRel G.Adj]
    (hT : T.IsTree) (side : α → Fin 2)
    (hindep : ∀ ⦃u v⦄, T.Adj u v → side u = 1 → side v ≠ 1)
    (active W : Finset α)
    (hactive : ∀ x ∈ active, side x = 1)
    (hdeferred : ∀ x, side x = 1 → x ∉ active → T.degree x = 1)
    (hWzero : ∀ x ∈ W, side x = 0)
    (hWleaf : ∀ x ∈ W, T.degree x = 1)
    (hWindep : T.IsIndepSet (W : Set α))
    (hWaway : ∀ ⦃w v⦄, w ∈ W → T.Adj w v → side v ≠ 1)
    (l : ℕ) (hWcard : #W = l)
    (X Y : Finset β) (hXY : Disjoint X Y)
    (hXcap : partCount side 0 ≤ #X)
    (hXX : ∀ a ∈ X, #X - l ≤ #((G.neighborFinset a) ∩ X))
    (hYX : ∀ b ∈ Y, #X - l ≤ #((G.neighborFinset b) ∩ X))
    (hXYdeg : ∀ a ∈ X, #active ≤ #((G.neighborFinset a) ∩ Y))
    (hglobal : ∀ a ∈ X, Fintype.card α - 1 ≤ G.degree a)
    (root : α) (hrootCore : side root = 0 ∨ root ∈ active)
    (hrootW : root ∉ W)
    (rootImage : β) (hrootImage : rootImage ∈ if side root = 0 then X else Y) :
    ∃ f : T.Copy G, f root = rootImage := by
  classical
  let side' := moveZeroLeaves74 side W
  let parts : Fin 2 → Finset β := fun i ↦ if i = 0 then X else Y
  have hside'root : side' root = side root := by
    exact moveZeroLeaves74_of_notMem hrootW
  have hactive' : ∀ x ∈ active, side' x = 1 := by
    intro x hx
    have hxnotW : x ∉ W := by
      intro hxW
      have := hactive x hx
      simpa [hWzero x hxW] using this
    rw [show side' x = side x from moveZeroLeaves74_of_notMem hxnotW]
    exact hactive x hx
  have hdeferred' : ∀ x, side' x = 1 → x ∉ active → T.degree x = 1 := by
    intro x hxside hxactive
    by_cases hxW : x ∈ W
    · exact hWleaf x hxW
    · apply hdeferred x
      · rw [show side' x = side x from moveZeroLeaves74_of_notMem hxW] at hxside
        exact hxside
      · exact hxactive
  have hindep' : ∀ ⦃u v⦄, T.Adj u v → side' u = 1 → side' v ≠ 1 := by
    exact moveZeroLeaves74_independent T side W hindep hWindep hWaway
  have hcount : partCount side' 0 = partCount side 0 - l := by
    simpa [side', hWcard] using partCount_moveZeroLeaves74_zero side W hWzero
  have hAA : ∀ a ∈ parts 0,
      partCount side' 0 ≤ #((G.neighborFinset a) ∩ parts 0) := by
    intro a ha
    simp [parts] at ha
    change partCount side' 0 ≤ #((G.neighborFinset a) ∩ X)
    rw [hcount]
    exact (Nat.sub_le_sub_right hXcap l).trans (hXX a ha)
  have hBA : ∀ b ∈ parts 1,
      partCount side' 0 ≤ #((G.neighborFinset b) ∩ parts 0) := by
    intro b hb
    simp [parts] at hb
    change partCount side' 0 ≤ #((G.neighborFinset b) ∩ X)
    rw [hcount]
    exact (Nat.sub_le_sub_right hXcap l).trans (hYX b hb)
  have hAB : ∀ a ∈ parts 0,
      #active ≤ #((G.neighborFinset a) ∩ parts 1) := by
    intro a ha
    exact hXYdeg a (by simpa [parts] using ha)
  have hparts : Set.PairwiseDisjoint Set.univ parts := by
    intro i _ j _ hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · change Disjoint (parts 0) (parts 1)
      simpa [parts] using hXY
    · change Disjoint (parts 1) (parts 0)
      simpa [parts] using hXY.symm
    · exact False.elim (hij rfl)
  have hrootCore' : side' root = 0 ∨ root ∈ active := by
    simpa [hside'root] using hrootCore
  have hrootImage' : rootImage ∈ parts (side' root) := by
    rw [hside'root]
    by_cases hs : side root = 0
    · simpa [parts, hs] using hrootImage
    · have hs1 : side root = 1 := by
        apply Fin.eq_of_val_eq
        have hv : (side root).val < 2 := (side root).isLt
        simp only [Fin.val_one]
        omega
      simpa [parts, hs, hs1] using hrootImage
  have hglobal' : ∀ a ∈ parts 0, Fintype.card α - 1 ≤ G.degree a := by
    intro a ha
    apply hglobal a
    simpa [parts] using ha
  exact fact72_part3 T G hT side' hindep' active hactive' hdeferred'
    parts hparts hAA hBA hAB hglobal' root hrootCore' rootImage hrootImage'

end Erdos547b.ZhaoLemma78Full74

#print axioms Erdos547b.ZhaoLemma78Full74.lemma7_8_movable_parent_branch

namespace Erdos547b.ZhaoLemma78Full74

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoFact72 Erdos547b.Zhao78Hard

/-- The hard branch with the induced core specified explicitly.  Unlike the
lower-level Hall extender, this theorem constructs the prescribed core copy
by the rooted semibipartite greedy lemma and derives the occupied-`X` count. -/
theorem lemma7_8_hard_branch_of_core
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (T : SimpleGraph α) (G : SimpleGraph β) [DecidableRel T.Adj] [DecidableRel G.Adj]
    (C W D : Finset α)
    (hCW : Disjoint C W) (hCD : Disjoint C D) (hWD : Disjoint W D)
    (hcover : (C ∪ W) ∪ D = (Finset.univ : Finset α))
    (hcoreTree : (T.induce (C : Set α)).IsTree)
    (coreSide : C → Fin 2)
    (hcoreIndep : ∀ ⦃u v : C⦄, (T.induce (C : Set α)).Adj u v →
      coreSide u = 1 → coreSide v ≠ 1)
    (parentW : W → C) (hparentW_inj : Function.Injective parentW)
    (hparentWside : ∀ w, coreSide (parentW w) = 1)
    (hpendantW : ∀ w : W, IsPendantAt T w (parentW w))
    (parentD : D → {a : α // a ∈ C ∪ W})
    (hpendantD : ∀ d : D, IsPendantAt T d (parentD d))
    (hparentDside : ∀ (d : D)
      (hdW : ((parentD d : {a : α // a ∈ C ∪ W}) : α) ∉ W),
      coreSide (⟨parentD d, (mem_union.mp (parentD d).2).resolve_right hdW⟩ : C) = 0)
    (X Y : Finset β) (hXY : Disjoint X Y) (l : ℕ)
    (hdouble : 2 * l ≤ #W)
    (hcap : partCount coreSide 0 + #W ≤ #X)
    (hXX : ∀ x ∈ X,
      partCount coreSide 0 ≤ #((G.neighborFinset x) ∩ X))
    (hYX : ∀ y ∈ Y,
      partCount coreSide 0 ≤ #((G.neighborFinset y) ∩ X))
    (hXYcore : ∀ x ∈ X,
      partCount coreSide 1 ≤ #((G.neighborFinset x) ∩ Y))
    (hdegYX : ∀ y ∈ Y, #X - l ≤ #(G.neighborFinset y ∩ X))
    (hdegXY : ∀ x ∈ X, #Y - l ≤ #(G.neighborFinset x ∩ Y))
    (hglobal : ∀ x ∈ X, Fintype.card α - 1 ≤ G.degree x)
    (root : C) (hrootSide : coreSide root = 0)
    (rootImage : β) (hrootImage : rootImage ∈ X) :
    ∃ fullCopy : T.Copy G, fullCopy root = rootImage := by
  classical
  let parts : Fin 2 → Finset β := fun i ↦ if i = 0 then X else Y
  have hparts : Set.PairwiseDisjoint Set.univ parts := by
    intro i _ j _ hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · change Disjoint (parts 0) (parts 1)
      simpa [parts] using hXY
    · change Disjoint (parts 1) (parts 0)
      simpa [parts] using hXY.symm
    · exact False.elim (hij rfl)
  have hdeg : ∀ i j, ¬(i = 1 ∧ j = 1) → ∀ v ∈ parts i,
      partCount coreSide j ≤ #((G.neighborFinset v) ∩ parts j) := by
    intro i j hij v hv
    fin_cases i <;> fin_cases j
    · exact hXX v (by simpa [parts] using hv)
    · exact hXYcore v (by simpa [parts] using hv)
    · exact hYX v (by simpa [parts] using hv)
    · exact False.elim (hij ⟨rfl, rfl⟩)
  have hrootImagePart : rootImage ∈ parts (coreSide root) := by
    simpa [parts, hrootSide] using hrootImage
  obtain ⟨coreCopy, hcoreRoot, hcoreMem⟩ :=
    exists_rooted_semibipartite_copy (T.induce (C : Set α)) G hcoreTree
      coreSide hcoreIndep parts hparts hdeg root rootImage hrootImagePart
  have hcoreX : ∀ c : C, coreSide c = 0 → coreCopy c ∈ X := by
    intro c hc
    simpa [parts, hc] using hcoreMem c
  have hcoreY : ∀ c : C, coreSide c = 1 → coreCopy c ∈ Y := by
    intro c hc
    simpa [parts, hc] using hcoreMem c
  have himageX : (Finset.univ : Finset C).image coreCopy ∩ X ⊆
      ((Finset.univ : Finset C).filter fun c : C ↦ coreSide c = 0).image coreCopy := by
    intro z hz
    obtain ⟨c, _, rfl⟩ := mem_image.mp (mem_inter.mp hz).1
    have hzX : coreCopy c ∈ X := (mem_inter.mp hz).2
    have hc0 : coreSide c = 0 := by
      by_contra hc
      have hc1 : coreSide c = 1 := by
        apply Fin.eq_of_val_eq
        have hv := (coreSide c).isLt
        simp only [Fin.val_one]
        omega
      have hzY := hcoreY c hc1
      exact Finset.disjoint_left.mp hXY hzX hzY
    exact mem_image.mpr ⟨c, mem_filter.mpr ⟨mem_univ _, hc0⟩, rfl⟩
  have hoccCard : #((Finset.univ : Finset C).image coreCopy ∩ X) ≤
      partCount coreSide 0 := by
    calc
      #((Finset.univ : Finset C).image coreCopy ∩ X) ≤
          #(((Finset.univ : Finset C).filter fun c : C ↦ coreSide c = 0).image coreCopy) :=
        card_le_card himageX
      _ = partCount coreSide 0 := by
        unfold partCount
        exact Finset.card_image_iff.mpr fun _ _ _ _ h ↦ coreCopy.injective h
  have hoccupied : #((Finset.univ : Finset C).image coreCopy ∩ X) + #W ≤ #X := by
    omega
  have hparentWY : ∀ w : W, coreCopy (parentW w) ∈ Y := by
    intro w
    exact hcoreY (parentW w) (hparentWside w)
  have hparentDX : ∀ (d : D)
      (hdW : ((parentD d : {a : α // a ∈ C ∪ W}) : α) ∉ W),
      coreCopy
        (⟨parentD d, (mem_union.mp (parentD d).2).resolve_right hdW⟩ : C) ∈ X := by
    intro d hdW
    apply hcoreX
    exact hparentDside d hdW
  obtain ⟨fullCopy, hfullCore⟩ :=
    extend_core_by_many_and_deferred_leaves_of_ambient T G C W D hCW hCD hWD hcover
      coreCopy parentW hparentW_inj hpendantW X Y l hdouble hparentWY hoccupied
      hdegYX hdegXY parentD hpendantD hglobal hparentDX
  refine ⟨fullCopy, ?_⟩
  rw [hfullCore root, hcoreRoot]

end Erdos547b.ZhaoLemma78Full74

#print axioms Erdos547b.ZhaoLemma78Full74.lemma7_8_hard_branch_of_core
namespace Erdos547b.ZhaoLemma78Full74

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoFact72

/-- Removing any family of leaves from a finite connected graph leaves a
connected induced graph, as soon as one vertex remains.  This local version
is included so the public Lemma 7.8 theorem has no dependency on a later
tree-stripping module. -/
private theorem connected_induce_compl_of_leaves78
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Set V) (hG : G.Connected) (hR : ∀ v ∈ R, G.degree v = 1)
    (hne : Rᶜ.Nonempty) : (G.induce Rᶜ).Connected := by
  rw [connected_iff]
  refine ⟨?_, hne.to_subtype⟩
  rintro ⟨u, hu⟩ ⟨v, hv⟩
  obtain ⟨p, hp⟩ := hG.exists_isPath u v
  refine ⟨p.induce Rᶜ ?_⟩
  intro z hz
  simp only [Set.mem_compl_iff]
  intro hzR
  obtain ⟨i, hiz, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hz
  have hi0 : i ≠ 0 := by
    intro hi0
    subst i
    have huget : p.getVert 0 ∉ R := by simpa using hu
    apply huget
    rw [hiz]
    exact hzR
  have hilt : i < p.length := by
    by_contra hnot
    have hieq : i = p.length := by omega
    subst i
    have hvget : p.getVert p.length ∉ R := by simpa using hv
    apply hvget
    rw [hiz]
    exact hzR
  have hleftSub : p.toSubgraph.Adj (p.getVert i) (p.getVert (i - 1)) := by
    rw [← Subgraph.mem_neighborSet,
      hp.neighborSet_toSubgraph_internal hi0 hilt]
    simp
  have hrightSub : p.toSubgraph.Adj (p.getVert i) (p.getVert (i + 1)) := by
    rw [← Subgraph.mem_neighborSet,
      hp.neighborSet_toSubgraph_internal hi0 hilt]
    simp
  have hleft : G.Adj z (p.getVert (i - 1)) := by
    rw [← hiz]
    exact hleftSub.adj_sub
  have hright : G.Adj z (p.getVert (i + 1)) := by
    rw [← hiz]
    exact hrightSub.adj_sub
  obtain ⟨w, hzw, hw⟩ := degree_eq_one_iff_existsUnique_adj.mp (hR z hzR)
  have hsame : p.getVert (i - 1) = p.getVert (i + 1) :=
    (hw _ hleft).trans (hw _ hright).symm
  have hind := hp.getVert_injOn
      (show i - 1 ∈ Set.Iic p.length by simp; omega)
      (show i + 1 ∈ Set.Iic p.length by simp; omega) hsame
  omega

/-- Zhao's Lemma 7.8, in the prescribed-first-part-vertex formulation.

`side = 0` is the source class `U₁`, `side = 1` is `U₂`, and `active`
is Zhao's `\widetilde U₂`.  The tree is not supplied with a root: `root`
is an arbitrary prescribed vertex of `U₁`, chosen only for the conclusion.
The parameters `n`, `l`, the edge bound, and `l < n` are retained exactly as
in the published statement, although the proof of the lemma uses only the
remaining hypotheses. -/
theorem lemma7_8
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    [DecidableEq alpha] [DecidableEq beta]
    (T : SimpleGraph alpha) (G : SimpleGraph beta)
    [DecidableRel T.Adj] [DecidableRel G.Adj]
    (n l : Nat) (hln : l < n)
    (hT : T.IsTree) (hedges : #T.edgeFinset ≤ n)
    (side : alpha → Fin 2)
    (hindep : ∀ ⦃u v⦄, T.Adj u v → side u = 1 → side v ≠ 1)
    (active : Finset alpha)
    (hactive : ∀ x ∈ active, side x = 1)
    (hdeferred : ∀ x, side x = 1 → x ∉ active → T.degree x = 1)
    (hleaves : 5 * l ≤ #(univ.filter fun x ↦ side x = 0 ∧ T.degree x = 1))
    (X Y : Finset beta) (hXY : Disjoint X Y)
    (hXcap : partCount side 0 ≤ #X)
    (hXX : ∀ a ∈ X, #X - l ≤ #((G.neighborFinset a) ∩ X))
    (hYX : ∀ b ∈ Y, #X - l ≤ #((G.neighborFinset b) ∩ X))
    (hXYdeg : ∀ a ∈ X,
      max (#Y - l) #active ≤ #((G.neighborFinset a) ∩ Y))
    (hglobal : ∀ a ∈ X, #T.edgeFinset ≤ G.degree a)
    (root : alpha) (hrootSide : side root = 0)
    (rootImage : beta) (hrootImage : rootImage ∈ X) :
    ∃ f : T.Copy G, f root = rootImage := by
  classical
  have hglobal' : ∀ a ∈ X, Fintype.card alpha - 1 ≤ G.degree a := by
    intro a ha
    have hedgeCard := hT.card_edgeFinset
    have hga := hglobal a ha
    omega
  have hXYactive : ∀ a ∈ X,
      #active ≤ #((G.neighborFinset a) ∩ Y) := by
    intro a ha
    exact (Nat.le_max_right _ _).trans (hXYdeg a ha)
  by_cases hl0 : l = 0
  · subst l
    exact lemma7_8_zero_defect T G hT side hindep active hactive hdeferred
      X Y hXY hXcap (by simpa using hXX) (by simpa using hYX)
      hXYactive hglobal' root (Or.inl hrootSide) rootImage
      (by simpa [hrootSide] using hrootImage)
  · have hlpos : 0 < l := Nat.pos_of_ne_zero hl0
    let leaves0 : Finset alpha :=
      univ.filter fun x ↦ side x = 0 ∧ T.degree x = 1
    let W1 : Finset alpha := leaves0.erase root
    let hatW : Finset alpha :=
      W1.filter fun w ↦ side (T.leafParent w) = 1
    let uniqueW : Finset alpha :=
      Zhao78Fiber.uniqueFiberElements hatW T.leafParent
    have hleaves0 : 5 * l ≤ #leaves0 := by simpa [leaves0] using hleaves
    have hcardLarge : 3 ≤ Fintype.card alpha := by
      have hsub : leaves0 ⊆ (univ : Finset alpha) := subset_univ _
      have hc := Finset.card_le_card hsub
      rw [card_univ] at hc
      omega
    have hW1card : 5 * l - 1 ≤ #W1 := by
      by_cases hr : root ∈ leaves0
      · have heq : #W1 = #leaves0 - 1 := by simp [W1, hr]
        omega
      · have heq : #W1 = #leaves0 := by simp [W1, hr]
        omega
    have hhatSub : hatW ⊆ W1 := by
      exact filter_subset _ _
    have hdich := Zhao78Fiber.ambient_missing_or_unique_or_loss
      W1 hatW T.leafParent l hhatSub hW1card
    rcases hdich with hmissing | hunique | hloss
    · obtain ⟨W, hWsub, hWcard⟩ := exists_subset_card_eq hmissing
      have hWzero : ∀ w ∈ W, side w = 0 := by
        intro w hw
        have hwW1 := (mem_sdiff.mp (hWsub hw)).1
        exact (mem_filter.mp (mem_erase.mp hwW1).2).2.1
      have hWleaf : ∀ w ∈ W, T.degree w = 1 := by
        intro w hw
        have hwW1 := (mem_sdiff.mp (hWsub hw)).1
        exact (mem_filter.mp (mem_erase.mp hwW1).2).2.2
      have hWparentNotOne : ∀ w ∈ W, side (T.leafParent w) ≠ 1 := by
        intro w hw hp
        have hsd := mem_sdiff.mp (hWsub hw)
        apply hsd.2
        exact mem_filter.mpr ⟨hsd.1, hp⟩
      have hWindep : T.IsIndepSet (W : Set alpha) := by
        intro u hu v hv huv hadj
        exact not_adj_of_both_degree_one_of_three_le_card T hT
          (hWleaf u hu) (hWleaf v hv) hcardLarge hadj
      have hWaway : ∀ ⦃w v⦄, w ∈ W → T.Adj w v → side v ≠ 1 := by
        intro w v hw hadj hvone
        have hvp : v = T.leafParent w :=
          T.eq_leafParent_of_adj (hWleaf w hw) hadj
        exact hWparentNotOne w hw (hvp ▸ hvone)
      have hrootW : root ∉ W := by
        intro hr
        exact (mem_erase.mp (mem_sdiff.mp (hWsub hr)).1).1 rfl
      exact lemma7_8_movable_parent_branch T G hT side hindep active W
        hactive hdeferred hWzero hWleaf hWindep hWaway l hWcard
        X Y hXY hXcap hXX hYX hXYactive hglobal' root (Or.inl hrootSide)
        hrootW rootImage (by simpa [hrootSide] using hrootImage)
    · let W : Finset alpha := uniqueW
      let D : Finset alpha :=
        univ.filter fun x ↦ side x = 1 ∧ x ∉ active
      let C : Finset alpha := univ \ (W ∪ D)
      have hdoubleW : 2 * l ≤ #W := by
        simpa [W, uniqueW] using hunique
      have hWsubHat : W ⊆ hatW := by
        intro w hw
        exact (Zhao78Fiber.mem_uniqueFiberElements.mp hw).1
      have hWzero : ∀ w ∈ W, side w = 0 := by
        intro w hw
        have hwW1 := hhatSub (hWsubHat hw)
        exact (mem_filter.mp (mem_erase.mp hwW1).2).2.1
      have hWleaf : ∀ w ∈ W, T.degree w = 1 := by
        intro w hw
        have hwW1 := hhatSub (hWsubHat hw)
        exact (mem_filter.mp (mem_erase.mp hwW1).2).2.2
      have hWparentOne : ∀ w ∈ W, side (T.leafParent w) = 1 := by
        intro w hw
        exact (mem_filter.mp (hWsubHat hw)).2
      have hDside : ∀ d ∈ D, side d = 1 := by
        intro d hd
        exact (mem_filter.mp hd).2.1
      have hDnotActive : ∀ d ∈ D, d ∉ active := by
        intro d hd
        exact (mem_filter.mp hd).2.2
      have hDleaf : ∀ d ∈ D, T.degree d = 1 := by
        intro d hd
        exact hdeferred d (hDside d hd) (hDnotActive d hd)
      have hrootW : root ∉ W := by
        intro hr
        have hrW1 := hhatSub (hWsubHat hr)
        exact (mem_erase.mp hrW1).1 rfl
      have hrootD : root ∉ D := by
        intro hr
        have := hDside root hr
        exact Fin.zero_ne_one (hrootSide.symm.trans this)
      have hCW : Disjoint C W := by
        rw [Finset.disjoint_left]
        intro c hc hcW
        exact (mem_sdiff.mp hc).2 (mem_union_left D hcW)
      have hCD : Disjoint C D := by
        rw [Finset.disjoint_left]
        intro c hc hcD
        exact (mem_sdiff.mp hc).2 (mem_union_right W hcD)
      have hWD : Disjoint W D := by
        rw [Finset.disjoint_left]
        intro w hw hwD
        exact Fin.zero_ne_one ((hWzero w hw).symm.trans (hDside w hwD))
      have hcover : (C ∪ W) ∪ D = (univ : Finset alpha) := by
        ext x
        simp only [Finset.mem_union, Finset.mem_univ, iff_true]
        by_cases hxW : x ∈ W
        · exact Or.inl (Or.inr hxW)
        by_cases hxD : x ∈ D
        · exact Or.inr hxD
        exact Or.inl (Or.inl (mem_sdiff.mpr ⟨mem_univ x, by simp [hxW, hxD]⟩))
      have hremovedLeaves : ∀ v ∈ (W ∪ D : Finset alpha), T.degree v = 1 := by
        intro v hv
        rcases mem_union.mp hv with hvW | hvD
        · exact hWleaf v hvW
        · exact hDleaf v hvD
      have hcoreTree : (T.induce (C : Set alpha)).IsTree := by
        have hCset : (C : Set alpha) = ((W ∪ D : Finset alpha) : Set alpha)ᶜ := by
          ext x
          simp [C]
        rw [hCset]
        refine ⟨connected_induce_compl_of_leaves78 T
          (((W ∪ D : Finset alpha) : Set alpha)) hT.connected ?_ ?_,
          hT.isAcyclic.induce _⟩
        · intro v hv
          exact hremovedLeaves v hv
        · exact ⟨root, by simpa using ⟨hrootW, hrootD⟩⟩
      let coreSide : C → Fin 2 := fun c ↦ side c
      have hcoreIndep : ∀ ⦃u v : C⦄, (T.induce (C : Set alpha)).Adj u v →
          coreSide u = 1 → coreSide v ≠ 1 := by
        intro u v huv hu hv
        exact hindep (by simpa using huv) hu hv
      let parentW : W → C := fun w ↦ ⟨T.leafParent w, by
        apply mem_sdiff.mpr
        refine ⟨mem_univ _, ?_⟩
        intro hp
        rcases Finset.mem_union.mp hp with hpW | hpD
        ·
          exact Fin.zero_ne_one ((hWzero _ hpW).symm.trans (hWparentOne w w.2))
        ·
          exact not_adj_of_both_degree_one_of_three_le_card T hT
            (hWleaf w w.2) (hDleaf _ hpD) hcardLarge
            (T.adj_leafParent (hWleaf w w.2))
        ⟩
      have hparentW_inj : Function.Injective parentW := by
        intro w1 w2 hp
        have hpval : T.leafParent w1 = T.leafParent w2 :=
          congrArg (fun c : C ↦ (c : alpha)) hp
        have hone := (Zhao78Fiber.mem_uniqueFiberElements.mp w1.2).2
        have hw1fiber : w1.1 ∈ Zhao78Fiber.fiberIn hatW T.leafParent
            (T.leafParent w1) :=
          Zhao78Fiber.mem_fiberIn.mpr ⟨hWsubHat w1.2, rfl⟩
        have hw2fiber : w2.1 ∈ Zhao78Fiber.fiberIn hatW T.leafParent
            (T.leafParent w1) :=
          Zhao78Fiber.mem_fiberIn.mpr ⟨hWsubHat w2.2, hpval.symm⟩
        apply Subtype.ext
        exact Finset.card_le_one.mp (by omega) _ hw1fiber _ hw2fiber
      have hparentWside : ∀ w, coreSide (parentW w) = 1 := by
        intro w
        exact hWparentOne w w.2
      have hpendantW : ∀ w : W,
          Erdos547b.Zhao78Hard.IsPendantAt T w (parentW w) := by
        intro w
        refine ⟨T.adj_leafParent (hWleaf w w.2), ?_⟩
        intro v hv
        exact T.eq_leafParent_of_adj (hWleaf w w.2) hv
      let parentD : D → {a : alpha // a ∈ C ∪ W} := fun d ↦
        ⟨T.leafParent d, by
          have hpNotD : T.leafParent d ∉ D := by
            intro hpD
            exact not_adj_of_both_degree_one_of_three_le_card T hT
              (hDleaf d d.2) (hDleaf _ hpD) hcardLarge
              (T.adj_leafParent (hDleaf d d.2))
          by_cases hpW : T.leafParent d ∈ W
          · exact mem_union_right C hpW
          · apply mem_union_left W
            exact mem_sdiff.mpr ⟨mem_univ _, by simp [hpW, hpNotD]⟩⟩
      have hpendantD : ∀ d : D,
          Erdos547b.Zhao78Hard.IsPendantAt T d (parentD d) := by
        intro d
        refine ⟨T.adj_leafParent (hDleaf d d.2), ?_⟩
        intro v hv
        exact T.eq_leafParent_of_adj (hDleaf d d.2) hv
      have hparentDside : ∀ (d : D)
          (hdW : ((parentD d : {a : alpha // a ∈ C ∪ W}) : alpha) ∉ W),
          coreSide (⟨parentD d,
            (mem_union.mp (parentD d).2).resolve_right hdW⟩ : C) = 0 := by
        intro d hdW
        have hdOne : side d = 1 := hDside d d.2
        have hpNotOne : side (T.leafParent d) ≠ 1 :=
          hindep (T.adj_leafParent (hDleaf d d.2)) hdOne
        apply Fin.eq_of_val_eq
        have hpLt := (side (T.leafParent d)).isLt
        change (side (T.leafParent d)).val = 0
        omega
      have hWzeroSub : W ⊆ univ.filter fun x ↦ side x = 0 := by
        intro w hw
        exact mem_filter.mpr ⟨mem_univ _, hWzero w hw⟩
      have hcoreZeroImage :
          (univ.filter fun c : C ↦ coreSide c = 0).image Subtype.val =
            (univ.filter fun x : alpha ↦ side x = 0) \ W := by
        ext x
        constructor
        · intro hx
          obtain ⟨c, hc, rfl⟩ := mem_image.mp hx
          have hc0 := (mem_filter.mp hc).2
          have hcC := (mem_sdiff.mp c.2).2
          exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _, hc0⟩,
            fun hcW ↦ hcC (mem_union_left D hcW)⟩
        · intro hx
          have hx0 := (mem_filter.mp (mem_sdiff.mp hx).1).2
          have hxW := (mem_sdiff.mp hx).2
          have hxD : x ∉ D := by
            intro hxd
            exact Fin.zero_ne_one (hx0.symm.trans (hDside x hxd))
          let c : C := ⟨x, mem_sdiff.mpr ⟨mem_univ _, by simp [hxW, hxD]⟩⟩
          exact mem_image.mpr ⟨c, mem_filter.mpr ⟨mem_univ _, hx0⟩, rfl⟩
      have hcoreZeroCard : partCount coreSide 0 + #W = partCount side 0 := by
        have himageCard :
            #((univ.filter fun c : C ↦ coreSide c = 0).image Subtype.val) =
              #(univ.filter fun c : C ↦ coreSide c = 0) :=
          card_image_iff.mpr fun _ _ _ _ h ↦ Subtype.ext h
        have hsdiff := card_sdiff_add_card_eq_card hWzeroSub
        unfold partCount
        rw [← himageCard, hcoreZeroImage]
        exact hsdiff
      have hcoreOneCard : partCount coreSide 1 ≤ #active := by
        unfold partCount
        rw [← Finset.card_image_of_injective _ Subtype.val_injective]
        apply Finset.card_le_card
        intro x hx
        obtain ⟨c, hc, rfl⟩ := mem_image.mp hx
        have hcOne := (mem_filter.mp hc).2
        by_contra hcActive
        have hcD : (c : alpha) ∈ D :=
          mem_filter.mpr ⟨mem_univ _, hcOne, hcActive⟩
        exact (mem_sdiff.mp c.2).2 (mem_union_right W hcD)
      have hcap : partCount coreSide 0 + #W ≤ #X := by
        rw [hcoreZeroCard]
        exact hXcap
      have hcoreZeroLe : partCount coreSide 0 ≤ #X - l := by
        omega
      have hXXcore : ∀ x ∈ X,
          partCount coreSide 0 ≤ #((G.neighborFinset x) ∩ X) := by
        intro x hx
        exact hcoreZeroLe.trans (hXX x hx)
      have hYXcore : ∀ y ∈ Y,
          partCount coreSide 0 ≤ #((G.neighborFinset y) ∩ X) := by
        intro y hy
        exact hcoreZeroLe.trans (hYX y hy)
      have hXYcore : ∀ x ∈ X,
          partCount coreSide 1 ≤ #((G.neighborFinset x) ∩ Y) := by
        intro x hx
        exact hcoreOneCard.trans (hXYactive x hx)
      have hdegXY : ∀ x ∈ X,
          #Y - l ≤ #(G.neighborFinset x ∩ Y) := by
        intro x hx
        exact (Nat.le_max_left _ _).trans (hXYdeg x hx)
      let rootC : C := ⟨root,
        mem_sdiff.mpr ⟨mem_univ _, by simp [hrootW, hrootD]⟩⟩
      obtain ⟨f, hf⟩ := Erdos547b.ZhaoLemma78Full74.lemma7_8_hard_branch_of_core
        T G C W D
        hCW hCD hWD hcover hcoreTree coreSide hcoreIndep parentW hparentW_inj
        hparentWside hpendantW parentD hpendantD hparentDside X Y hXY l
        hdoubleW hcap hXXcore hYXcore hXYcore hYX hdegXY hglobal'
        rootC (by simpa [rootC, coreSide] using hrootSide) rootImage hrootImage
      exact ⟨f, by simpa [rootC] using hf⟩
    · let W : Finset alpha :=
        hatW \ Zhao78Fiber.uniqueFiberElements hatW T.leafParent
      have hWsubHat : W ⊆ hatW := sdiff_subset
      have hWzero : ∀ w ∈ W, side w = 0 := by
        intro w hw
        have hwW1 := hhatSub (hWsubHat hw)
        exact (mem_filter.mp (mem_erase.mp hwW1).2).2.1
      have hWleaf : ∀ w ∈ W, T.IsLeaf w := by
        intro w hw
        have hwW1 := hhatSub (hWsubHat hw)
        exact (mem_filter.mp (mem_erase.mp hwW1).2).2.2
      have hPone : ∀ w ∈ W, side (T.leafParent w) = 1 := by
        intro w hw
        exact (mem_filter.mp (hWsubHat hw)).2
      have hLoss : l + #(T.leafParents W) ≤ #W := by
        simpa [W, SimpleGraph.leafParents] using hloss
      have hrootW : root ∉ W := by
        intro hr
        have hrW1 := hhatSub (hWsubHat hr)
        exact (mem_erase.mp hrW1).1 rfl
      exact lemma7_8_repeated_parent_branch T G hT side hindep active W
        hactive hdeferred hWzero hWleaf hPone l hLoss X Y hXY hXcap
        hXX hYX hXYactive hglobal' root hrootSide hrootW rootImage hrootImage

end Erdos547b.ZhaoLemma78Full74

#print axioms Erdos547b.ZhaoLemma78Full74.lemma7_8

namespace Erdos547b.ZhaoLemma78Full74

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoFact72

/-- Unrooted form of Zhao's Lemma 7.8.  The explicit nonemptiness of the
first source class is exactly what is needed to choose the prescribed vertex
in the rooted statement (and it forces `X` to be nonempty by `hXcap`). -/
theorem lemma7_8_unrooted
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    [DecidableEq alpha] [DecidableEq beta]
    (T : SimpleGraph alpha) (G : SimpleGraph beta)
    [DecidableRel T.Adj] [DecidableRel G.Adj]
    (n l : Nat) (hln : l < n)
    (hT : T.IsTree) (hedges : #T.edgeFinset ≤ n)
    (side : alpha → Fin 2)
    (hindep : ∀ ⦃u v⦄, T.Adj u v → side u = 1 → side v ≠ 1)
    (active : Finset alpha)
    (hactive : ∀ x ∈ active, side x = 1)
    (hdeferred : ∀ x, side x = 1 → x ∉ active → T.degree x = 1)
    (hleaves : 5 * l ≤ #(univ.filter fun x ↦ side x = 0 ∧ T.degree x = 1))
    (X Y : Finset beta) (hXY : Disjoint X Y)
    (hXcap : partCount side 0 ≤ #X)
    (hXX : ∀ a ∈ X, #X - l ≤ #((G.neighborFinset a) ∩ X))
    (hYX : ∀ b ∈ Y, #X - l ≤ #((G.neighborFinset b) ∩ X))
    (hXYdeg : ∀ a ∈ X,
      max (#Y - l) #active ≤ #((G.neighborFinset a) ∩ Y))
    (hglobal : ∀ a ∈ X, #T.edgeFinset ≤ G.degree a)
    (hfirst : ∃ root, side root = 0) :
    T.IsContained G := by
  classical
  obtain ⟨root, hrootSide⟩ := hfirst
  have hpartPos : 0 < partCount side 0 := by
    unfold partCount
    exact Finset.card_pos.mpr
      ⟨root, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrootSide⟩⟩
  have hXpos : 0 < #X := hpartPos.trans_le hXcap
  obtain ⟨rootImage, hrootImage⟩ := Finset.card_pos.mp hXpos
  obtain ⟨f, _⟩ := lemma7_8 T G n l hln hT hedges side hindep active
    hactive hdeferred hleaves X Y hXY hXcap hXX hYX hXYdeg hglobal
    root hrootSide rootImage hrootImage
  exact ⟨f⟩

end Erdos547b.ZhaoLemma78Full74

#print axioms Erdos547b.ZhaoLemma78Full74.lemma7_8_unrooted
