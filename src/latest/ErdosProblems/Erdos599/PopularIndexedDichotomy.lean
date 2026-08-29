/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.PopularLayers

/-!
# The indexed-popularity dichotomy

The strict ordinal descent in Definition 8.2 is used by the printed proof of
Theorem 8.4 only to rule out a strongly popular warp whose terminals lie in
the target.  This file isolates that use.  In particular, once target strong
popularity is supplied as the other branch of a dichotomy, the entire layer
construction is independent of strict descent.

This isolation is the first half of the repair of the successor-index issue
in the grounding application: the literal Section 7 bookkeeping gives only a
weak inequality at newly inessential successor records.  Those records must
be handled through the strong-target branch rather than by asserting a false
strict descent.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Popular

open DirectedPath Stationary

universe u

variable {V : Type u}

/-! ## Weak chronology on the common index data -/

/-- Weak chronology: target indices never exceed source indices.  This is
the true statement supplied by the successor bookkeeping. -/
def KappaIndexed.Nonincreasing {Gamma : DWeb V}
    {kappa : Cardinal.{u}} (D : KappaIndexed Gamma kappa) : Prop :=
  ∀ (p : FinitePath Gamma.graph)
    (hstart : p.start ∈ Gamma.source) (hfinish : p.finish ∈ Gamma.target),
    D.g ⟨p.finish, hfinish⟩ ≤ D.f ⟨p.start, hstart⟩

namespace KappaIndexed

/-- Restrict a warp to an arbitrary subfamily of its paths. -/
def subwarp {Gamma : DWeb V} {S : Set V} (P : XSWarp Gamma S)
    (Q : Set (FinitePath Gamma.graph)) (hQ : Q ⊆ P.paths) :
    XSWarp Gamma S where
  paths := Q
  disjoint := by
    intro p hp q hq hpq
    exact P.disjoint (hQ hp) (hQ hq) hpq
  starts_in_source hp := P.starts_in_source (hQ hp)
  ends_in_target hp := P.ends_in_target (hQ hp)

/-- Paths of a target warp on which weak chronology is strict. -/
def strictPaths {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (D : KappaIndexed Gamma kappa) (P : XSWarp Gamma Gamma.target) :
    Set (FinitePath Gamma.graph) :=
  {p | ∃ hp : p ∈ P.paths,
    D.g ⟨p.finish, P.ends_in_target hp⟩ <
      D.f ⟨p.start, P.starts_in_source hp⟩}

/-- Paths of a target warp on which source and target have the same index. -/
def equalPaths {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (D : KappaIndexed Gamma kappa) (P : XSWarp Gamma Gamma.target) :
    Set (FinitePath Gamma.graph) :=
  {p | ∃ hp : p ∈ P.paths,
    D.g ⟨p.finish, P.ends_in_target hp⟩ =
      D.f ⟨p.start, P.starts_in_source hp⟩}

theorem strictPaths_subset {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (D : KappaIndexed Gamma kappa) (P : XSWarp Gamma Gamma.target) :
    D.strictPaths P ⊆ P.paths := by
  rintro p ⟨hp, _⟩
  exact hp

theorem equalPaths_subset {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (D : KappaIndexed Gamma kappa) (P : XSWarp Gamma Gamma.target) :
    D.equalPaths P ⊆ P.paths := by
  rintro p ⟨hp, _⟩
  exact hp

/-- The strict subwarp. -/
def strictSubwarp {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (D : KappaIndexed Gamma kappa) (P : XSWarp Gamma Gamma.target) :
    XSWarp Gamma Gamma.target :=
  subwarp P (D.strictPaths P) (D.strictPaths_subset P)

/-- The same-index subwarp. -/
def equalSubwarp {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (D : KappaIndexed Gamma kappa) (P : XSWarp Gamma Gamma.target) :
    XSWarp Gamma Gamma.target :=
  subwarp P (D.equalPaths P) (D.equalPaths_subset P)

/-- A stationary strongly popular target warp has a stationary strict part
or a stationary same-index part.  This is the precise replacement for
pressing down under a merely nonincreasing chronology. -/
theorem stronglyPopular_target_strict_or_equal
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (D : KappaIndexed Gamma kappa) (hmono : D.Nonincreasing)
    (hstrong : IsStronglyPopular D Gamma.target) :
    (∃ P : XSWarp Gamma Gamma.target,
      IsStationaryBelow kappa
        (initialIndicesOf D (D.strictSubwarp P).paths
          (D.strictSubwarp P).starts_in_source)) ∨
    (∃ P : XSWarp Gamma Gamma.target,
      IsStationaryBelow kappa
        (initialIndicesOf D (D.equalSubwarp P).paths
          (D.equalSubwarp P).starts_in_source)) := by
  obtain ⟨P, hP⟩ := hstrong
  let Istrict := initialIndicesOf D (D.strictSubwarp P).paths
    (D.strictSubwarp P).starts_in_source
  let Iequal := initialIndicesOf D (D.equalSubwarp P).paths
    (D.equalSubwarp P).starts_in_source
  have hcover :
      initialIndicesOf D P.paths P.starts_in_source ⊆
        Istrict ∪ Iequal := by
    rintro a ⟨p, hp, hpa⟩
    have hle := hmono p (P.starts_in_source hp) (P.ends_in_target hp)
    rcases hle.lt_or_eq with hlt | heq
    · apply Or.inl
      refine ⟨p, ⟨hp, hlt⟩, ?_⟩
      simpa [strictSubwarp, subwarp] using hpa
    · apply Or.inr
      refine ⟨p, ⟨hp, heq⟩, ?_⟩
      simpa [equalSubwarp, subwarp] using hpa
  have hunion : IsStationaryBelow kappa (Istrict ∪ Iequal) :=
    hP.mono hcover
  have hcof : Order.cof (Below kappa) ≠ ℵ₀ := by
    rw [Stationary.cof_below_eq_lift D.regular]
    rw [← Cardinal.lift_aleph0.{u + 1, u}]
    exact (Cardinal.lift_lt.mpr D.uncountable).ne'
  rcases (isStationary_union_iff hcof).mp hunion with hs | he
  · exact Or.inl ⟨P, hs⟩
  · exact Or.inr ⟨P, he⟩

/-- Membership in the equality subwarp exposes the exact source/target index
identity needed by the grounding decoder. -/
theorem equalSubwarp_index_eq
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (D : KappaIndexed Gamma kappa) (P : XSWarp Gamma Gamma.target)
    {p : FinitePath Gamma.graph} (hp : p ∈ (D.equalSubwarp P).paths) :
    D.g ⟨p.finish, (D.equalSubwarp P).ends_in_target hp⟩ =
      D.f ⟨p.start, (D.equalSubwarp P).starts_in_source hp⟩ := by
  obtain ⟨hpP, heq⟩ := hp
  simpa [equalSubwarp, subwarp] using heq

/-- Although weak chronology allows equality on some paths, the strict part
of any target warp still has nonstationary source-index set.  This is the
precise local form of Lemma 8.3: its pressing-down proof only uses strict
descent on the paths of the particular warp under consideration. -/
theorem strictSubwarp_initialIndices_nonstationary
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (D : KappaIndexed Gamma kappa) (P : XSWarp Gamma Gamma.target) :
    ¬ IsStationaryBelow kappa
      (initialIndicesOf D (D.strictSubwarp P).paths
        (D.strictSubwarp P).starts_in_source) := by
  classical
  let Q := D.strictSubwarp P
  let I : Set (Below kappa) :=
    initialIndicesOf D Q.paths Q.starts_in_source
  let chosen : (a : Below kappa) → a ∈ I → FinitePath Gamma.graph :=
    fun a ha ↦ Classical.choose ha
  have chosen_mem (a : Below kappa) (ha : a ∈ I) :
      chosen a ha ∈ Q.paths :=
    Classical.choose (Classical.choose_spec ha)
  have chosen_index (a : Below kappa) (ha : a ∈ I) :
      D.f ⟨(chosen a ha).start, Q.starts_in_source (chosen_mem a ha)⟩ = a :=
    Classical.choose_spec (Classical.choose_spec ha)
  let r : Below kappa → Below kappa := fun a ↦
    if ha : a ∈ I then
      D.g ⟨(chosen a ha).finish, Q.ends_in_target (chosen_mem a ha)⟩
    else a
  have hreg : IsRegressiveOn I r := by
    intro a ha
    have hstrict :
        D.g ⟨(chosen a ha).finish, Q.ends_in_target (chosen_mem a ha)⟩ <
          D.f ⟨(chosen a ha).start, Q.starts_in_source (chosen_mem a ha)⟩ := by
      exact (chosen_mem a ha).2
    have hr : r a =
        D.g ⟨(chosen a ha).finish, Q.ends_in_target (chosen_mem a ha)⟩ := by
      simp [r, ha]
    rw [hr]
    exact lt_of_lt_of_eq hstrict (chosen_index a ha)
  have hinj : Set.InjOn r I := by
    intro a ha b hb hrab
    have hra : r a =
        D.g ⟨(chosen a ha).finish, Q.ends_in_target (chosen_mem a ha)⟩ := by
      simp [r, ha]
    have hrb : r b =
        D.g ⟨(chosen b hb).finish, Q.ends_in_target (chosen_mem b hb)⟩ := by
      simp [r, hb]
    have hterminal :
        (⟨(chosen a ha).finish, Q.ends_in_target (chosen_mem a ha)⟩ :
          Gamma.target) =
        ⟨(chosen b hb).finish, Q.ends_in_target (chosen_mem b hb)⟩ := by
      apply D.g.injective
      exact hra.symm.trans (hrab.trans hrb)
    have hfinish : (chosen a ha).finish = (chosen b hb).finish :=
      congrArg Subtype.val hterminal
    have hpath : chosen a ha = chosen b hb :=
      Q.eq_of_finish_eq (chosen_mem a ha) (chosen_mem b hb) hfinish
    have hsource :
        (⟨(chosen a ha).start, Q.starts_in_source (chosen_mem a ha)⟩ :
          Gamma.source) =
        ⟨(chosen b hb).start, Q.starts_in_source (chosen_mem b hb)⟩ := by
      apply Subtype.ext
      exact congrArg FinitePath.start hpath
    exact (chosen_index a ha).symm.trans
      ((congrArg D.f hsource).trans (chosen_index b hb))
  exact not_isStationaryBelow_of_injOn_regressive
    D.uncountable D.regular hreg hinj

/-- Under weak chronology, strong popularity of the target is witnessed by
a stationary family of genuinely equal-stage paths.  The strict alternative
from `stronglyPopular_target_strict_or_equal` is impossible by the local
pressing-down lemma above. -/
theorem stronglyPopular_target_equal
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (D : KappaIndexed Gamma kappa) (hmono : D.Nonincreasing)
    (hstrong : IsStronglyPopular D Gamma.target) :
    ∃ P : XSWarp Gamma Gamma.target,
      IsStationaryBelow kappa
        (initialIndicesOf D (D.equalSubwarp P).paths
          (D.equalSubwarp P).starts_in_source) := by
  rcases D.stronglyPopular_target_strict_or_equal hmono hstrong with
      ⟨P, hP⟩ | hP
  · exact (D.strictSubwarp_initialIndices_nonstationary P hP).elim
  · exact hP

end KappaIndexed

/-- The zero-th unpopular layer is not popular as soon as strong popularity
of the whole target has been excluded.  No ordinal descent is used. -/
theorem unpopularLayer_zero_not_popular_of_target_not_stronglyPopular
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (U : KappaIndexed Gamma kappa)
    (htarget : ¬ IsStronglyPopular U Gamma.target) :
    ¬ IsPopular U (unpopularLayer U 0) := by
  intro hpopular
  apply htarget
  have hstrong : IsStronglyPopular U (unpopularLayer U 0) :=
    stronglyPopular_of_popular_of_all_vertices_unpopular U hpopular <| by
      intro v hv
      exact hv.2
  exact hstrong.mono Set.inter_subset_left

/-- The zero-th popular layer cannot be strongly popular when the target is
not strongly popular. -/
theorem popularLayer_zero_not_stronglyPopular_of_target_not_stronglyPopular
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (U : KappaIndexed Gamma kappa)
    (htarget : ¬ IsStronglyPopular U Gamma.target) :
    ¬ IsStronglyPopular U (popularLayer U 0) := by
  intro hpopular
  exact htarget (hpopular.mono Set.inter_subset_left)

/-- Assertion 8.8 with the unique descent-dependent base case replaced by
the explicit hypothesis that the target is not strongly popular. -/
theorem unpopularLayer_not_popular_of_target_not_stronglyPopular
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (U : KappaIndexed Gamma kappa)
    (htarget : ¬ IsStronglyPopular U Gamma.target) :
    ∀ n : ℕ, ¬ IsPopular U (unpopularLayer U n) := by
  intro n
  induction n with
  | zero =>
      exact unpopularLayer_zero_not_popular_of_target_not_stronglyPopular
        U htarget
  | succ n ih =>
      intro hpopular
      rcases hpopular with hsource | ⟨F, hstat⟩
      · obtain ⟨x, hxlayer, hxsource⟩ := hsource
        exact (unpopularLayer_subset_unpopular U (n + 1) hxlayer)
          (popularVertex_of_mem_source U hxsource)
      · have hstrong : IsStronglyPopular U (unpopularLayer U (n + 1)) :=
          stronglyPopular_of_joined_of_unpopular_terminals U F hstat <| by
            intro v hv
            exact unpopularLayer_subset_unpopular U (n + 1) hv
        apply ih
        exact popular_of_stronglyPopular_of_step U
          (hS := hstrong) fun _ hv ↦ hv.1

/-- Assertion 8.9 under the explicit non-strong-popularity alternative. -/
theorem popularLayer_not_stronglyPopular_of_target_not_stronglyPopular
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (U : KappaIndexed Gamma kappa)
    (htarget : ¬ IsStronglyPopular U Gamma.target) :
    ∀ n : ℕ, ¬ IsStronglyPopular U (popularLayer U n) := by
  intro n
  cases n with
  | zero =>
      exact
        popularLayer_zero_not_stronglyPopular_of_target_not_stronglyPopular
          U htarget
  | succ n =>
      exact popularLayer_succ_not_stronglyPopular_of_not_popular U n
        (unpopularLayer_not_popular_of_target_not_stronglyPopular U htarget n)

/-- The canonical good fan at a non-source point of a popular layer remains
stationary under the explicit target alternative. -/
theorem popularLayerGoodFan_stationary_of_target_not_stronglyPopular
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (U : KappaIndexed Gamma kappa)
    (htarget : ¬ IsStronglyPopular U Gamma.target) (n : ℕ)
    (c : (popularLayer U n \ Gamma.source : Set V)) :
    IsStationaryBelow kappa
      (initialIndicesOf U (popularLayerGoodFan U n c).paths
        (popularLayerGoodFan U n c).starts_in_source) := by
  apply goodJoinedFamily_stationary U
    (nonSourcePopularFan U (popularLayer_subset_popular U n c.2.1) c.2.2)
    (popularLayer U n \ Gamma.source)
  · exact nonSourcePopularFan_stationary U
      (popularLayer_subset_popular U n c.2.1) c.2.2
  · exact not_stronglyPopular_of_subset Set.sdiff_subset
      (popularLayer_not_stronglyPopular_of_target_not_stronglyPopular
        U htarget n)

/-- The cardinal bound for a popular layer also needs only the explicit
target alternative. -/
theorem popularLayer_diff_source_card_le_of_target_not_stronglyPopular
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (U : KappaIndexed Gamma kappa) (hU : U.SourceBounded)
    (htarget : ¬ IsStronglyPopular U Gamma.target) (n : ℕ) :
    #(popularLayer U n \ Gamma.source : Set V) ≤ kappa := by
  apply le_of_not_gt
  intro hlarge
  have hdisjoint :
      Disjoint (popularLayer U n \ Gamma.source : Set V) Gamma.source :=
    Set.disjoint_sdiff_left
  have hstrong :
      IsStronglyPopular U (popularLayer U n \ Gamma.source) :=
    stronglyPopular_of_large_normalized_fans U hU hdisjoint hlarge
      (popularLayerGoodFan U n)
      (popularLayerGoodFan_normalized U n)
      (popularLayerGoodFan_stationary_of_target_not_stronglyPopular
        U htarget n)
  exact
    (popularLayer_not_stronglyPopular_of_target_not_stronglyPopular
      U htarget n) (hstrong.mono Set.sdiff_subset)

/-- The canonical separator has small non-source part under the explicit
target alternative. -/
theorem layerSeparator_diff_source_card_le_of_target_not_stronglyPopular
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (U : KappaIndexed Gamma kappa) (hU : U.SourceBounded)
    (htarget : ¬ IsStronglyPopular U Gamma.target) :
    #(layerSeparator U \ Gamma.source : Set V) ≤ kappa :=
  layerSeparator_diff_source_card_le_of_layers U fun n ↦
    popularLayer_diff_source_card_le_of_target_not_stronglyPopular
      U hU htarget n

/-- The union of the popular layers is not strongly popular under the
explicit target alternative. -/
theorem layerSeparator_not_stronglyPopular_of_target_not_stronglyPopular
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (U : KappaIndexed Gamma kappa)
    (htarget : ¬ IsStronglyPopular U Gamma.target) :
    ¬ IsStronglyPopular U (layerSeparator U) := by
  rintro ⟨P, hP⟩
  have hcover : layerSeparator U ⊆ ⋃ n : ℕ, popularLayer U n :=
    fun _ hx ↦ hx
  have hindices :
      initialIndicesOf U P.paths P.starts_in_source ⊆
        ⋃ n : ℕ, initialIndicesOf U
          (P.restrictTerminal (popularLayer U n)).paths
          (P.restrictTerminal (popularLayer U n)).starts_in_source :=
    initialIndices_subset_iUnion_restrictTerminal U P (popularLayer U) hcover
  obtain ⟨n, hn⟩ := exists_stationary_of_subset_iUnion
    U.regular U.uncountable hP hindices
  exact
    (popularLayer_not_stronglyPopular_of_target_not_stronglyPopular
      U htarget n) ⟨P.restrictTerminal (popularLayer U n), hn⟩

/-- Locality of the canonical fans under the explicit target alternative. -/
theorem layerSeparator_locallyPopular_of_target_not_stronglyPopular
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (U : KappaIndexed Gamma kappa)
    (htarget : ¬ IsStronglyPopular U Gamma.target) :
    ∀ s ∈ layerSeparator U,
      IsLocallyPopularAt U (layerSeparator U) s := by
  intro s hs
  have hspop : IsPopularVertex U s := layerSeparator_subset_popular U hs
  rcases hspop with hsource | ⟨F, hF⟩
  · obtain ⟨x, hxs, hxsource⟩ := hsource
    exact Or.inl ((Set.mem_singleton_iff.1 hxs) ▸ hxsource)
  · apply Or.inr
    let G := goodJoinedFamily F (layerSeparator U)
    have hG : IsStationaryBelow kappa
        (initialIndicesOf U G.paths G.starts_in_source) :=
      goodJoinedFamily_stationary U F (layerSeparator U) hF
        (layerSeparator_not_stronglyPopular_of_target_not_stronglyPopular
          U htarget)
    refine ⟨G, hG, ?_⟩
    intro p hp
    have hpF : p ∈ F.paths := hp.1
    have hstartRoof : p.start ∈ Gamma.roof (layerSeparator U) := by
      intro q hq
      exact layerSeparator_isSeparator U q
        (by simpa [hq.1] using F.starts_in_source hpF) hq.2
    have hfinish : p.finish = s :=
      Set.mem_singleton_iff.1 (F.ends_in_join hpF)
    exact support_subset_strictRoof_union_singleton hs p hstartRoof
      hfinish hp.2

/-- Theorem 8.4 with its genuine logical input exposed: either a strongly
popular target warp is returned by the surrounding argument, or this
constructor builds the usual popular separator. -/
noncomputable def theorem8_4_of_target_not_stronglyPopular
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (U : KappaIndexed Gamma kappa) (hU : U.SourceBounded)
    (htarget : ¬ IsStronglyPopular U Gamma.target) :
    PopularSeparator U where
  cut := layerSeparator U
  separates := layerSeparator_isSeparator U
  locally_popular :=
    layerSeparator_locallyPopular_of_target_not_stronglyPopular U htarget
  card_diff_source := by
    exact Cardinal.lift_le.2
      (layerSeparator_diff_source_card_le_of_target_not_stronglyPopular
        U hU htarget)
  not_strongly_popular :=
    layerSeparator_not_stronglyPopular_of_target_not_stronglyPopular
      U htarget

/-- The indexed-popularity dichotomy.  This formulation is what the repaired
grounding proof consumes: strict descent handles the old-record branch,
whereas the successor-new branch is allowed to emerge as strong target
popularity and is decoded separately. -/
theorem stronglyPopular_target_or_popularSeparator
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (U : KappaIndexed Gamma kappa) (hU : U.SourceBounded) :
    IsStronglyPopular U Gamma.target ∨ Nonempty (PopularSeparator U) := by
  classical
  by_cases htarget : IsStronglyPopular U Gamma.target
  · exact Or.inl htarget
  · exact Or.inr
      ⟨theorem8_4_of_target_not_stronglyPopular U hU htarget⟩

end Popular
end Erdos599
