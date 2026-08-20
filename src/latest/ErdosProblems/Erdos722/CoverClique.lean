/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos722.CoverEmbedding
import ErdosProblems.Erdos722.Cover
import Mathlib

/-!
# The rooted clique specialization of the reserve cover process
-/

namespace Erdos722.CoverClique

open Finset
open Erdos722.Typicality
open Erdos722.Reserve
open Erdos722.RootedEmbedding
open Erdos722.RootSchedule
open Erdos722.CoverEmbedding
open Erdos722.Cover
open Erdos722.RandomGreedy
open Erdos722.AdaptiveChernoff

noncomputable section

/-- The first `r` vertices of `Fin q`. -/
def coverRoot (q r : ℕ) : Finset (Fin q) :=
  (Finset.univ : Finset (Fin q)).filter fun i ↦ i.1 < r

/-- The evident equivalence between the first `r` vertices of `Fin q` and
`Fin r`. -/
def coverRootEquiv (q r : ℕ) (hrq : r ≤ q) : ↑(coverRoot q r) ≃ Fin r where
  toFun x := ⟨x.1.1, (Finset.mem_filter.mp x.2).2⟩
  invFun i := ⟨⟨i.1, i.2.trans_le hrq⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.2⟩⟩
  left_inv x := by apply Subtype.ext; apply Fin.ext; rfl
  right_inv i := by apply Fin.ext; rfl

@[simp] theorem card_coverRoot (hrq : r ≤ q) :
    (coverRoot q r).card = r := by
  rw [← Fintype.card_coe (coverRoot q r)]
  exact (Fintype.card_congr (coverRootEquiv q r hrq)).trans
    (Fintype.card_fin r)

/-- The complete `r`-graph on `q` labelled vertices, rooted at one edge. -/
def coverPattern (q r : ℕ) : RootedPattern q r where
  edges := uniformEdges q r
  root := coverRoot q r
  uniform := by
    intro e he
    exact mem_uniformEdges.mp he

@[simp] theorem coverPattern_edges :
    (coverPattern q r).edges = uniformEdges q r := rfl

@[simp] theorem coverPattern_root :
    (coverPattern q r).root = coverRoot q r := rfl

theorem mem_coverPattern_freeEdges_iff (hrq : r ≤ q)
    {a : Finset (Fin q)} :
    a ∈ (coverPattern q r).freeEdges ↔
      a.card = r ∧ a ≠ coverRoot q r := by
  rw [RootedPattern.freeEdges, Finset.mem_filter]
  simp only [coverPattern_edges, mem_uniformEdges]
  constructor
  · rintro ⟨ha, hnot⟩
    refine ⟨ha, ?_⟩
    intro haroot
    exact hnot (haroot ▸ Finset.Subset.rfl)
  · rintro ⟨ha, hne⟩
    refine ⟨ha, ?_⟩
    intro hsub
    apply hne
    exact Finset.eq_of_subset_of_card_le hsub (by
      rw [card_coverRoot hrq, ha])

/-- A convenient fixed constant for the labelled overlap loss in the cover
denominator. -/
def coverMeetingConstant (q r : ℕ) : ℕ :=
  2 ^ q * (2 ^ r * r ^ r)

theorem faceScheduleNumeratorBound_coverPattern
    (hrq : r ≤ q) (n D : ℕ) :
    faceScheduleNumeratorBound (coverPattern q r) n D =
      (2 ^ (r - 1) * (2 ^ q * r ^ r)) * n ^ (q - r) * D := by
  unfold faceScheduleNumeratorBound
  rw [show (coverPattern q r).root.card = r by
    exact card_coverRoot hrq]

theorem card_coverPattern_freeEdges_le :
    (coverPattern q r).freeEdges.card ≤ 2 ^ q := by
  calc
    (coverPattern q r).freeEdges.card ≤
        (Finset.univ : Finset (Fin q)).powerset.card := by
      apply Finset.card_le_card
      intro a ha
      exact Finset.mem_powerset.mpr (Finset.subset_univ a)
    _ = 2 ^ q := by simp

/-- The generic labelled meeting loss has the essential exponent
`q-r-1` for the rooted clique pattern. -/
theorem codimOneMeetingBound_coverPattern_le
    (hr : 0 < r) (hrq : r < q) (n D : ℕ) :
    codimOneMeetingBound (coverPattern q r) n D ≤
      coverMeetingConstant q r * D * n ^ (q - r - 1) := by
  classical
  let M := (2 ^ r * r ^ r) * D * n ^ (q - r - 1)
  have hterm : ∀ a ∈ (coverPattern q r).freeEdges,
      (n ^ (r - 1 - (a ∩ coverRoot q r).card) * D) *
          (2 ^ r *
            (r ^ (a \ coverRoot q r).card *
              n ^ (q - ((coverRoot q r).card +
                (a \ coverRoot q r).card)))) ≤ M := by
    intro a ha
    have haData := (mem_coverPattern_freeEdges_iff hrq.le).mp ha
    have hspos : 0 < (a \ coverRoot q r).card := by
      by_contra hzero
      have hempty : a \ coverRoot q r = ∅ :=
        Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hzero)
      have hsub : a ⊆ coverRoot q r := by
        exact Finset.sdiff_eq_empty_iff_subset.mp hempty
      exact haData.2 (Finset.eq_of_subset_of_card_le hsub (by
        rw [card_coverRoot hrq.le, haData.1]))
    have hsle : (a \ coverRoot q r).card ≤ r := by
      exact (Finset.card_le_card Finset.sdiff_subset).trans_eq haData.1
    have hsplit := Finset.card_inter_add_card_sdiff a (coverRoot q r)
    have hsqr : (a \ coverRoot q r).card ≤ q - r := by
      have hsub : a \ coverRoot q r ⊆
          (Finset.univ : Finset (Fin q)) \ coverRoot q r := by
        intro x hx
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hx).2⟩
      have hc := Finset.card_le_card hsub
      simpa [Finset.card_sdiff_of_subset (Finset.subset_univ _),
        card_coverRoot hrq.le] using hc
    have hexp :
        (r - 1 - (a ∩ coverRoot q r).card) +
            (q - ((coverRoot q r).card +
              (a \ coverRoot q r).card)) = q - r - 1 := by
      rw [card_coverRoot hrq.le]
      omega
    have hrpow : r ^ (a \ coverRoot q r).card ≤ r ^ r :=
      Nat.pow_le_pow_right hr hsle
    dsimp [M]
    calc
      (n ^ (r - 1 - (a ∩ coverRoot q r).card) * D) *
          (2 ^ r *
            (r ^ (a \ coverRoot q r).card *
              n ^ (q - ((coverRoot q r).card +
                (a \ coverRoot q r).card)))) =
          (2 ^ r * r ^ (a \ coverRoot q r).card * D) *
            (n ^ (r - 1 - (a ∩ coverRoot q r).card) *
              n ^ (q - ((coverRoot q r).card +
                (a \ coverRoot q r).card))) := by ring
      _ = (2 ^ r * r ^ (a \ coverRoot q r).card * D) *
            n ^ ((r - 1 - (a ∩ coverRoot q r).card) +
              (q - ((coverRoot q r).card +
                (a \ coverRoot q r).card))) := by rw [Nat.pow_add]
      _ = (2 ^ r * r ^ (a \ coverRoot q r).card * D) *
            n ^ (q - r - 1) := by rw [hexp]
      _ ≤ (2 ^ r * r ^ r * D) * n ^ (q - r - 1) := by
        exact Nat.mul_le_mul_right _
          (Nat.mul_le_mul_right D (Nat.mul_le_mul_left (2 ^ r) hrpow))
  have hfreeCard : (coverPattern q r).freeEdges.card ≤ 2 ^ q := by
    exact card_coverPattern_freeEdges_le
  unfold codimOneMeetingBound
  calc
    (∑ a ∈ (coverPattern q r).freeEdges,
      (n ^ (r - 1 - (a ∩ (coverPattern q r).root).card) * D) *
        (2 ^ r *
          (r ^ (a \ (coverPattern q r).root).card *
            n ^ (q - ((coverPattern q r).root.card +
              (a \ (coverPattern q r).root).card))))) ≤
        ∑ _a ∈ (coverPattern q r).freeEdges, M := by
      apply Finset.sum_le_sum
      intro a ha
      simpa using hterm a ha
    _ = (coverPattern q r).freeEdges.card * M := by simp
    _ ≤ 2 ^ q * M := Nat.mul_le_mul_right M hfreeCard
    _ = coverMeetingConstant q r * D * n ^ (q - r - 1) := by
      simp [M, coverMeetingConstant]
      ring

/-- A root request with prescribed image `e` exists whenever the two
finite sets have the same cardinality. -/
theorem exists_rootRequest_with_image
    [Nonempty (Fin n)] (root : Finset (Fin v)) (e : Finset (Fin n))
    (hcard : root.card = e.card) :
    ∃ request : RootRequest v n root, requestImage root request = e := by
  classical
  let σ : ↑root ≃ ↑e := Fintype.equivOfCardEq (by simpa using hcard)
  let fallback : Fin n := Classical.choice (inferInstance : Nonempty (Fin n))
  let f : Fin v → Fin n := fun x ↦
    if hx : x ∈ root then (σ ⟨x, hx⟩ : Fin n) else fallback
  have hinj : Set.InjOn f (↑root : Set (Fin v)) := by
    intro x hx y hy hxy
    have hfx : f x = (σ ⟨x, hx⟩ : Fin n) := by
      simp only [f]
      split
      · congr 2
      · contradiction
    have hfy : f y = (σ ⟨y, hy⟩ : Fin n) := by
      simp only [f]
      split
      · congr 2
      · contradiction
    have hsub : σ ⟨x, hx⟩ = σ ⟨y, hy⟩ := by
      apply Subtype.ext
      simpa [hfx, hfy] using hxy
    exact congrArg Subtype.val (σ.injective hsub)
  let request : RootRequest v n root := ⟨f, hinj⟩
  refine ⟨request, ?_⟩
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
    have hf : f x = (σ ⟨x, hx⟩ : Fin n) := by
      simp only [f]
      split
      · congr 2
      · contradiction
    rw [← hxy]
    change f x ∈ e
    rw [hf]
    exact (σ ⟨x, hx⟩).2
  · intro hy
    obtain ⟨x, hx⟩ := σ.surjective ⟨y, hy⟩
    apply Finset.mem_image.mpr
    refine ⟨x.1, x.2, ?_⟩
    have hf : f x.1 = (σ x : Fin n) := by
      simp only [f]
      split
      · congr 2
      · rename_i hnot
        exact (hnot x.2).elim
    exact hf.trans (congrArg Subtype.val hx)

/-- For a full embedding of the clique pattern, the image free edges are
exactly the clique edges other than the prescribed root. -/
theorem imageFreeEdges_coverPattern_eq_spill
    (hrq : r ≤ q) (request : RootRequest q n (coverRoot q r))
    (e B : Finset (Fin n)) (φ : Fin q ↪ Fin n)
    (hext : ExtendsRequest (coverRoot q r) request φ)
    (hrequest : requestImage (coverRoot q r) request = e)
    (hrange : (Finset.univ : Finset (Fin q)).map φ = B) :
    imageFreeEdges (coverPattern q r) φ = cliqueEdges B r \ {e} := by
  classical
  have hrootMap : mapEdge φ (coverRoot q r) = e :=
    (mapEdge_root_eq_requestImage_of_extends (coverRoot q r) request φ hext).trans
      hrequest
  ext g
  constructor
  · intro hg
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hg
    have haData := (mem_coverPattern_freeEdges_iff hrq).mp ha
    apply Finset.mem_sdiff.mpr
    constructor
    · apply Finset.mem_powersetCard.mpr
      refine ⟨?_, by simpa [mapEdge] using haData.1⟩
      rw [← hrange]
      exact Finset.map_subset_map.mpr (Finset.subset_univ a)
    · intro hmem
      have heq : mapEdge φ a = e := Finset.mem_singleton.mp hmem
      have hmaps : a.map φ = (coverRoot q r).map φ :=
        heq.trans hrootMap.symm
      exact haData.2 (Finset.map_injective φ hmaps)
  · intro hg
    have hgData := Finset.mem_sdiff.mp hg
    have hgClique := Finset.mem_powersetCard.mp hgData.1
    let a : Finset (Fin q) := g.preimage φ φ.injective.injOn
    have hmap : a.map φ = g := by
      ext y
      constructor
      · intro hy
        obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp hy
        rw [← hxy]
        exact Finset.mem_preimage.mp hx
      · intro hy
        have hyB : y ∈ B := hgClique.1 hy
        rw [← hrange] at hyB
        obtain ⟨x, _hx, hxy⟩ := Finset.mem_map.mp hyB
        apply Finset.mem_map.mpr
        refine ⟨x, Finset.mem_preimage.mpr ?_, hxy⟩
        exact hxy ▸ hy
    apply Finset.mem_image.mpr
    refine ⟨a, (mem_coverPattern_freeEdges_iff hrq).mpr ?_, ?_⟩
    · constructor
      · have hc := hgClique.2
        rw [← hmap] at hc
        simpa using hc
      · intro haroot
        apply hgData.2
        have hrootMap' : (coverRoot q r).map φ = e := by
          simpa [mapEdge] using hrootMap
        rw [← hmap, haroot, hrootMap']
        simp
    · exact hmap

/-- The `i`th edge of a finset in its canonical linear order, with a fixed
member used outside the canonical range. -/
def scheduledEdge (leave : Finset (Finset (Fin n)))
    (e₀ : Finset (Fin n)) (i : ℕ) : Finset (Fin n) :=
  if hi : i < leave.card then
    ((leave.equivFin).symm ⟨i, hi⟩).1
  else e₀

lemma scheduledEdge_fin (leave : Finset (Finset (Fin n)))
    (e₀ : Finset (Fin n)) (i : Fin leave.card) :
    scheduledEdge leave e₀ i.1 = ((leave.equivFin).symm i).1 := by
  simp [scheduledEdge, i.2]

lemma scheduledEdge_mem (leave : Finset (Finset (Fin n)))
    {e₀ : Finset (Fin n)} (he₀ : e₀ ∈ leave) (i : ℕ) :
    scheduledEdge leave e₀ i ∈ leave := by
  by_cases hi : i < leave.card
  · simp [scheduledEdge, hi]
  · simp [scheduledEdge, hi, he₀]

lemma scheduledEdge_injective_fin (leave : Finset (Finset (Fin n)))
    (e₀ : Finset (Fin n)) :
    Function.Injective (fun i : Fin leave.card ↦
      scheduledEdge leave e₀ i.1) := by
  intro i j hij
  change scheduledEdge leave e₀ i.1 = scheduledEdge leave e₀ j.1 at hij
  rw [scheduledEdge_fin, scheduledEdge_fin] at hij
  have hsub : (leave.equivFin).symm i = (leave.equivFin).symm j :=
    Subtype.ext hij
  exact (leave.equivFin).symm.injective hsub

/-- Finite numerical form of the reserve-cover path theorem specialized to
complete rooted cliques. -/
theorem exists_scheduled_reserveCliquePath_of_finite_bounds
    {n q r D A C : ℕ}
    (hr : 0 < r) (hrq : r < q)
    (leave reserve : Finset (Finset (Fin n)))
    (hleaveUniform : ∀ e ∈ leave, e.card = r)
    (hreserveUniform : ∀ e ∈ reserve, e.card = r)
    (e₀ : Finset (Fin n)) (he₀ : e₀ ∈ leave)
    (hleaveDegree : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree leave J ≤ D)
    (hcandidates : ∀ e ∈ leave,
      A ≤ (reserveCandidates n q r reserve e).card)
    (hLpos : 0 < reserveLegalLowerBound (coverPattern q r) n A C)
    (hquant : (Real.exp 1 - 1) *
        ((faceScheduleNumeratorBound (coverPattern q r) n D : ℝ) /
          reserveLegalLowerBound (coverPattern q r) n A C) ≤
        (C : ℝ) / 2)
    (hcard :
      (Fintype.card (RelevantFaceLoadTarget (coverPattern q r) n) : ℝ) *
          Real.exp (-(C : ℝ) / 2) < 1) :
    ∃ request : ℕ → RootRequest q n (coverRoot q r),
      ∃ path : List (Fin q ↪ Fin n),
        (∀ i, requestImage (coverRoot q r) (request i) =
          scheduledEdge leave e₀ i) ∧
        path.length = leave.card ∧
        IsReserveEmbeddingPath (coverPattern q r) request reserve [] path ∧
        ∀ target : RelevantFaceLoadTarget (coverPattern q r) n,
          pathHits (faceLoadHit (coverPattern q r) target) [] path < C := by
  classical
  have he₀card : e₀.card = r := hleaveUniform e₀ he₀
  have he₀ne : e₀.Nonempty := Finset.card_pos.mp (by omega)
  letI : Nonempty (Fin n) := ⟨he₀ne.choose⟩
  have hedgeCard (i : ℕ) :
      (coverRoot q r).card = (scheduledEdge leave e₀ i).card := by
    rw [card_coverRoot hrq.le,
      hleaveUniform (scheduledEdge leave e₀ i)
        (scheduledEdge_mem leave he₀ i)]
  have hrequestExists (i : ℕ) :
      ∃ request : RootRequest q n (coverRoot q r),
        requestImage (coverRoot q r) request =
          scheduledEdge leave e₀ i :=
    exists_rootRequest_with_image (coverRoot q r)
      (scheduledEdge leave e₀ i) (hedgeCard i)
  let request : ℕ → RootRequest q n (coverRoot q r) :=
    fun i ↦ Classical.choose (hrequestExists i)
  have hrequest (i : ℕ) :
      requestImage (coverRoot q r) (request i) =
        scheduledEdge leave e₀ i :=
    Classical.choose_spec (hrequestExists i)
  have hschedule : IsRootImageSchedule (coverRoot q r) request
      leave.card leave := by
    constructor
    · intro i
      rw [hrequest]
      exact scheduledEdge_mem leave he₀ i.1
    · intro i j hij
      apply scheduledEdge_injective_fin leave e₀
      simpa [hrequest] using hij
  have hbaseline (i : ℕ) :
      A ≤ (reserveEmbeddings (coverPattern q r) (request i) reserve).card := by
    exact (hcandidates (scheduledEdge leave e₀ i)
      (scheduledEdge_mem leave he₀ i)).trans
        (card_reserveCandidates_le_reserveEmbeddings
          (coverPattern q r) coverPattern_edges
          (card_coverRoot hrq.le) (request i)
          (scheduledEdge leave e₀ i) (hrequest i) reserve)
  have hApos : 0 < A := by
    exact hLpos.trans_le (Nat.sub_le A
      (codimOneMeetingBound (coverPattern q r) n
        ((coverPattern q r).freeEdges.card * C)))
  have hreserveEmbNonempty :
      (reserveEmbeddings (coverPattern q r) (request 0) reserve).Nonempty :=
    Finset.card_pos.mp (hApos.trans_le (hbaseline 0))
  letI : Nonempty (Fin q ↪ Fin n) := ⟨hreserveEmbNonempty.choose⟩
  obtain ⟨path, hlen, hpath, hcaps⟩ :=
    exists_reserveEmbeddingPath_of_faceSchedule
      (coverPattern q r) request leave reserve leave.card D A C
      hschedule hleaveUniform hleaveDegree hreserveUniform hbaseline hr
      hLpos hquant hcard
  exact ⟨request, path, hrequest, hlen, hpath, hcaps⟩

/-- A scheduled reserve-clique path is exactly a cover assignment: the
canonical finset equivalence identifies the step belonging to each leave
edge, and path legality gives pairwise disjoint spills. -/
noncomputable def coverAssignment_of_scheduled_reserveCliquePath
    {n q r : ℕ} (hrq : r ≤ q)
    (leave reserve : Finset (Finset (Fin n)))
    (e₀ : Finset (Fin n))
    (request : ℕ → RootRequest q n (coverRoot q r))
    (path : List (Fin q ↪ Fin n))
    (hrequest : ∀ i, requestImage (coverRoot q r) (request i) =
      scheduledEdge leave e₀ i)
    (hlen : path.length = leave.card)
    (hpath : IsReserveEmbeddingPath
      (coverPattern q r) request reserve [] path) :
    CoverAssignment n q r leave reserve := by
  classical
  let index (e : Finset (Fin n)) (he : e ∈ leave) : Fin leave.card :=
    leave.equivFin ⟨e, he⟩
  let pathIndex (e : Finset (Fin n)) (he : e ∈ leave) : Fin path.length :=
    ⟨(index e he).1, by rw [hlen]; exact (index e he).2⟩
  let block : Finset (Fin n) → Finset (Fin n) := fun e ↦
    if he : e ∈ leave then
      mapEdge (path.get (pathIndex e he))
        (Finset.univ : Finset (Fin q))
    else ∅
  have hblock (e : Finset (Fin n)) (he : e ∈ leave) :
      block e = mapEdge (path.get (pathIndex e he))
        (Finset.univ : Finset (Fin q)) := by
    simp only [block]
    split
    · congr 3
    · contradiction
  have hscheduled (e : Finset (Fin n)) (he : e ∈ leave) :
      scheduledEdge leave e₀ (pathIndex e he).1 = e := by
    have hfin := scheduledEdge_fin leave e₀ (index e he)
    have hinv : (leave.equivFin).symm (index e he) = ⟨e, he⟩ := by
      simp [index]
    simpa [pathIndex, hinv] using hfin
  have hstep (e : Finset (Fin n)) (he : e ∈ leave) :
      path.get (pathIndex e he) ∈
        reserveLegalEmbeddings (coverPattern q r) request reserve
          (path.take (pathIndex e he).1) := by
    have hm := FollowsLegal.get_mem
      (reserveLegalEmbeddings (coverPattern q r) request reserve)
      hpath (pathIndex e he)
    simpa using hm
  have hext (e : Finset (Fin n)) (he : e ∈ leave) :
      ExtendsRequest (coverRoot q r)
        (request (pathIndex e he).1) (path.get (pathIndex e he)) :=
    by
      have hx := (mem_reserveLegalEmbeddings.mp (hstep e he)).1
      simpa [List.length_take, Nat.min_eq_left
        (Nat.le_of_lt (pathIndex e he).2)] using hx
  have hrootImage (e : Finset (Fin n)) (he : e ∈ leave) :
      requestImage (coverRoot q r) (request (pathIndex e he).1) = e := by
    rw [hrequest]
    exact hscheduled e he
  have hspill (e : Finset (Fin n)) (he : e ∈ leave) :
      spill r e (block e) =
        imageFreeEdges (coverPattern q r) (path.get (pathIndex e he)) := by
    rw [hblock e he]
    exact (imageFreeEdges_coverPattern_eq_spill hrq
      (request (pathIndex e he).1) e
      (mapEdge (path.get (pathIndex e he))
        (Finset.univ : Finset (Fin q)))
      (path.get (pathIndex e he)) (hext e he) (hrootImage e he) rfl).symm
  refine {
    block := block
    block_mem := ?_
    spill_disjoint := ?_ }
  · intro e he
    apply Finset.mem_filter.mpr
    constructor
    · apply mem_uniformEdges.mpr
      rw [hblock e he, card_mapEdge]
      simp
    · constructor
      · rw [hblock e he]
        have hrootMap :
            mapEdge (path.get (pathIndex e he)) (coverRoot q r) = e :=
          (mapEdge_root_eq_requestImage_of_extends
            (coverRoot q r) (request (pathIndex e he).1)
            (path.get (pathIndex e he)) (hext e he)).trans
              (hrootImage e he)
        intro y hy
        have hyroot : y ∈
            mapEdge (path.get (pathIndex e he)) (coverRoot q r) := by
          rw [hrootMap]
          exact hy
        exact (Finset.map_subset_map.mpr
          (Finset.subset_univ (coverRoot q r))) hyroot
      · change spill r e (block e) ⊆ reserve
        rw [hspill e he]
        exact (mem_reserveLegalEmbeddings.mp (hstep e he)).2.1
  · intro e he f hf hef
    have hindexNe : pathIndex e he ≠ pathIndex f hf := by
      intro hidx
      apply hef
      have hval : (index e he).1 = (index f hf).1 :=
        congrArg (fun z : Fin path.length ↦ z.1) hidx
      have hfin : index e he = index f hf := Fin.ext hval
      have hsub : (⟨e, he⟩ : ↑leave) = ⟨f, hf⟩ :=
        leave.equivFin.injective hfin
      exact congrArg Subtype.val hsub
    rw [hspill e he, hspill f hf]
    exact IsReserveEmbeddingPath.pairwise_disjoint hpath
      (pathIndex e he) (pathIndex f hf) hindexNe

/-- Fully finite cover lemma under its three scalar hypotheses: reserve
candidate lower bounds, positivity of the legal denominator, and the
exponential union bound. -/
theorem exists_coverAssignment_of_finite_bounds
    {n q r D A C : ℕ}
    (hr : 0 < r) (hrq : r < q)
    (leave reserve : Finset (Finset (Fin n)))
    (hleaveUniform : ∀ e ∈ leave, e.card = r)
    (hreserveUniform : ∀ e ∈ reserve, e.card = r)
    (hleaveDegree : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree leave J ≤ D)
    (hcandidates : ∀ e ∈ leave,
      A ≤ (reserveCandidates n q r reserve e).card)
    (hLpos : 0 < reserveLegalLowerBound (coverPattern q r) n A C)
    (hquant : (Real.exp 1 - 1) *
        ((faceScheduleNumeratorBound (coverPattern q r) n D : ℝ) /
          reserveLegalLowerBound (coverPattern q r) n A C) ≤
        (C : ℝ) / 2)
    (hcard :
      (Fintype.card (RelevantFaceLoadTarget (coverPattern q r) n) : ℝ) *
          Real.exp (-(C : ℝ) / 2) < 1) :
    Nonempty (CoverAssignment n q r leave reserve) := by
  classical
  by_cases hempty : leave = ∅
  · subst leave
    refine ⟨{
      block := fun _ ↦ ∅
      block_mem := ?_
      spill_disjoint := ?_ }⟩
    · simp
    · simp
  · obtain ⟨e₀, he₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨request, path, hrequest, hlen, hpath, _hcaps⟩ :=
      exists_scheduled_reserveCliquePath_of_finite_bounds hr hrq
        leave reserve hleaveUniform hreserveUniform e₀ he₀
        hleaveDegree hcandidates hLpos hquant hcard
    exact ⟨coverAssignment_of_scheduled_reserveCliquePath hrq.le
      leave reserve e₀ request path hrequest hlen hpath⟩

end

end Erdos722.CoverClique
