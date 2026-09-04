/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.SuspendedReconstruct
import ErdosProblems.Erdos570.EndpointGrowth

/-!
# Partial compression of a suspended path

The shortcut construction removes every internal path vertex.  For the
endpoint-path argument we instead replace the suspended path by a shorter
path with `ℓ` fresh internal vertices.  A copy of this partially compressed
graph therefore starts the endpoint-growth process at any prescribed fixed
length.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

/-- The retained vertices of the original graph, embedded in the left side
of the vertex type of the compressed graph. -/
def compressedRetainedEmbedding
    {V : Type*} [Fintype V] [DecidableEq V]
    {t ℓ : ℕ} {p : Fin (t + 2) → V} :
    SuspendedRetained p ↪ Sum (SuspendedRetained p) (Fin ℓ) :=
  ⟨Sum.inl, Sum.inl_injective⟩

/-- The canonical replacement path with the old retained endpoints and `ℓ`
fresh internal vertices. -/
def compressedSuspendedSequence
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {t : ℕ} {p : Fin (t + 2) → V} (hp : IsSuspendedPath G p) (ℓ : ℕ)
    (i : Fin (ℓ + 2)) : Sum (SuspendedRetained p) (Fin ℓ) :=
  if hi0 : i.val = 0 then
    Sum.inl (suspendedLeft hp)
  else if hilast : i.val = ℓ + 1 then
    Sum.inl (suspendedRight hp)
  else
    Sum.inr ⟨i.val - 1, by omega⟩

@[simp] theorem compressedSuspendedSequence_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {t : ℕ} {p : Fin (t + 2) → V} (hp : IsSuspendedPath G p) (ℓ : ℕ) :
    compressedSuspendedSequence hp ℓ 0 = Sum.inl (suspendedLeft hp) := by
  simp [compressedSuspendedSequence]

@[simp] theorem compressedSuspendedSequence_last
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {t : ℕ} {p : Fin (t + 2) → V} (hp : IsSuspendedPath G p) (ℓ : ℕ) :
    compressedSuspendedSequence hp ℓ (Fin.last (ℓ + 1)) =
      Sum.inl (suspendedRight hp) := by
  simp [compressedSuspendedSequence]

@[simp] theorem compressedSuspendedSequence_mid
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {t : ℕ} {p : Fin (t + 2) → V} (hp : IsSuspendedPath G p)
    {ℓ : ℕ} (i : Fin ℓ) :
    compressedSuspendedSequence hp ℓ (suspendedMidIndex i) = Sum.inr i := by
  unfold compressedSuspendedSequence
  split <;> rename_i hi0
  · simp [suspendedMidIndex] at hi0
  · split <;> rename_i hilast
    · simp [suspendedMidIndex] at hilast
      omega
    · congr 1

theorem compressedSuspendedSequence_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {t : ℕ} {p : Fin (t + 2) → V} (hp : IsSuspendedPath G p) (ℓ : ℕ) :
    Function.Injective (compressedSuspendedSequence hp ℓ) := by
  intro i j hij
  simp only [compressedSuspendedSequence] at hij
  split at hij <;> rename_i hi0
  · split at hij <;> rename_i hj0
    · exact Fin.ext (hi0.trans hj0.symm)
    · split at hij <;> rename_i hjlast
      · exact (suspended_endpoints_ne hp
          (congrArg Subtype.val (Sum.inl.inj hij))).elim
      · contradiction
  · split at hij <;> rename_i hilast
    · split at hij <;> rename_i hj0
      · exact (suspended_endpoints_ne hp
          (congrArg Subtype.val (Sum.inl.inj hij).symm)).elim
      · split at hij <;> rename_i hjlast
        · exact Fin.ext (hilast.trans hjlast.symm)
        · contradiction
    · split at hij <;> rename_i hj0
      · contradiction
      · split at hij <;> rename_i hjlast
        · contradiction
        · have hv := congrArg Fin.val (Sum.inr.inj hij)
          simp only [Fin.val_mk] at hv
          apply Fin.ext
          omega

/-- The graph consisting exactly of the consecutive edges of an injective
finite sequence. -/
def sequencePathGraph {V : Type*} [Fintype V] [DecidableEq V]
    {t : ℕ} (q : Fin (t + 2) → V) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (suspendedPathEdges q : Set (Sym2 V))

noncomputable instance sequencePathGraph.fintypeEdgeSet
    {V : Type*} [Fintype V] [DecidableEq V]
    {t : ℕ} (q : Fin (t + 2) → V) :
    Fintype (sequencePathGraph q).edgeSet :=
  Fintype.ofFinite _

theorem sequencePathGraph_adj_consecutive
    {V : Type*} [Fintype V] [DecidableEq V]
    {t : ℕ} (q : Fin (t + 2) → V) (hq : Function.Injective q)
    (i j : Fin (t + 2)) (hij : i.val + 1 = j.val) :
    (sequencePathGraph q).Adj (q i) (q j) := by
  rw [sequencePathGraph, SimpleGraph.fromEdgeSet_adj]
  constructor
  · change s(q i, q j) ∈ (suspendedPathEdges q : Set (Sym2 V))
    change s(q i, q j) ∈ suspendedPathEdges q
    rw [suspendedPathEdges, Finset.mem_image]
    let u : Fin (t + 1) := ⟨i.val, by omega⟩
    refine ⟨u, Finset.mem_univ u, ?_⟩
    unfold suspendedPathEdge
    rw [Sym2.eq_iff]
    left
    constructor
    · apply congrArg q
      apply Fin.ext
      simp [u]
    · apply congrArg q
      apply Fin.ext
      simp [u]
      omega
  · exact hq.ne (Fin.ne_of_val_ne (by omega))

theorem sequencePathGraph_edgeFinset_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {t : ℕ} (q : Fin (t + 2) → V) (hq : Function.Injective q) :
    (sequencePathGraph q).edgeFinset = suspendedPathEdges q := by
  classical
  ext e
  rw [SimpleGraph.mem_edgeFinset, sequencePathGraph,
    SimpleGraph.edgeSet_fromEdgeSet]
  constructor
  · exact fun he ↦ he.1
  · intro he
    refine ⟨he, ?_⟩
    rw [suspendedPathEdges, Finset.mem_image] at he
    obtain ⟨i, -, rfl⟩ := he
    unfold suspendedPathEdge
    rw [Sym2.mem_diagSet, Sym2.mk_isDiag_iff]
    intro heq
    have hi := Fin.ext_iff.mp (hq heq)
    simp only at hi
    omega

@[simp] theorem sequencePathGraph_edgeFinset_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {t : ℕ} (q : Fin (t + 2) → V) (hq : Function.Injective q) :
    (sequencePathGraph q).edgeFinset.card = t + 1 := by
  rw [sequencePathGraph_edgeFinset_eq q hq]
  classical
  rw [suspendedPathEdges,
    Finset.card_image_of_injective _ (suspendedPathEdge_injective hq)]
  simp

/-- The shortcut graph on retained vertices, together with the canonical
replacement path.  Keeping the shortcut edge also preserves a possible
original edge between the two endpoints. -/
def compressSuspendedGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {t : ℕ} {p : Fin (t + 2) → V} (hp : IsSuspendedPath G p) (ℓ : ℕ) :
    SimpleGraph (Sum (SuspendedRetained p) (Fin ℓ)) :=
  (shortenSuspendedGraph G hp).map
      (compressedRetainedEmbedding (p := p) (ℓ := ℓ)) ⊔
    sequencePathGraph (compressedSuspendedSequence hp ℓ)

noncomputable instance compressSuspendedGraph.fintypeEdgeSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {t : ℕ} {p : Fin (t + 2) → V} (hp : IsSuspendedPath G p) (ℓ : ℕ) :
    Fintype (compressSuspendedGraph G hp ℓ).edgeSet :=
  Fintype.ofFinite _

/-- Canonical `GraphCode` of the partially compressed graph. -/
def compressSuspendedCode
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {t : ℕ} {p : Fin (t + 2) → V} (hp : IsSuspendedPath G p) (ℓ : ℕ) :
    GraphCode :=
  recodeGraph (compressSuspendedGraph G hp ℓ)

@[simp] theorem compressSuspendedCode_vertexCount
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {t : ℕ} {p : Fin (t + 2) → V} (hp : IsSuspendedPath G p) (ℓ : ℕ) :
    (compressSuspendedCode G hp ℓ).vertexCount = Fintype.card V - t + ℓ := by
  rw [compressSuspendedCode, recodeGraph_vertexCount]
  simp only [Fintype.card_sum, Fintype.card_fin]
  change Fintype.card {v : V // v ∉ suspendedInterior p} + ℓ = _
  rw [Fintype.card_subtype_compl]
  have hcard : Fintype.card {v : V // v ∈ suspendedInterior p} = t := by
    change Fintype.card ↥(suspendedInterior p) = t
    rw [Fintype.card_coe, suspendedInterior_card hp]
  rw [hcard]

/-- Partial compression removes at least `t-(ℓ+1)` edges.  The extra one in
the correction is the retained shortcut edge. -/
theorem compressSuspendedGraph_edgeCount_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {t : ℕ} {p : Fin (t + 2) → V} (hp : IsSuspendedPath G p)
    (ht : 1 ≤ t) {ℓ : ℕ} (hℓt : ℓ + 1 ≤ t) :
    Nat.card (compressSuspendedGraph G hp ℓ).edgeSet + (t - (ℓ + 1)) ≤
      G.edgeFinset.card := by
  classical
  let f := compressedRetainedEmbedding (p := p) (ℓ := ℓ)
  let S := shortenSuspendedGraph G hp
  let : DecidableRel S.Adj := Classical.decRel _
  let A := S.map f
  let P := sequencePathGraph (compressedSuspendedSequence hp ℓ)
  have hAcard : Nat.card A.edgeSet = Nat.card S.edgeSet := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      SimpleGraph.card_edgeSet, SimpleGraph.card_edgeSet]
    exact SimpleGraph.card_edgeFinset_map f S
  have hPcard : Nat.card P.edgeSet = ℓ + 1 := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
    exact sequencePathGraph_edgeFinset_card _
      (compressedSuspendedSequence_injective hp ℓ)
  have hsup : Nat.card (compressSuspendedGraph G hp ℓ).edgeSet ≤
      Nat.card A.edgeSet + Nat.card P.edgeSet := by
    simp only [Nat.card_coe_set_eq, compressSuspendedGraph,
      SimpleGraph.edgeSet_sup, A, S, f, P]
    exact Set.ncard_union_le _ _
  have horig := shortenSuspendedGraph_edgeCount_le hp ht
  change Nat.card S.edgeSet + t ≤ G.edgeFinset.card at horig
  rw [hAcard, hPcard] at hsup
  omega

@[simp] theorem compressSuspendedCode_edgeCount_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {t : ℕ} {p : Fin (t + 2) → V} (hp : IsSuspendedPath G p)
    (ht : 1 ≤ t) {ℓ : ℕ} (hℓt : ℓ + 1 ≤ t) :
    (compressSuspendedCode G hp ℓ).edgeCount + (t - (ℓ + 1)) ≤
      G.edgeFinset.card := by
  classical
  unfold compressSuspendedCode recodeGraph GraphCode.edgeCount
  have hcard :
      Nat.card ((compressSuspendedGraph G hp ℓ).overFin rfl).edgeSet =
        Nat.card (compressSuspendedGraph G hp ℓ).edgeSet := by
    exact (Nat.card_congr (SimpleGraph.overFinIso
      (G := compressSuspendedGraph G hp ℓ) rfl).mapEdgeSet).symm
  rw [hcard]
  exact compressSuspendedGraph_edgeCount_le hp ht hℓt

/-- Partial compression preserves the absence of isolated vertices. -/
theorem compressSuspendedCode_noIsolated
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {t : ℕ} {p : Fin (t + 2) → V} (hp : IsSuspendedPath G p)
    (hG : ∀ v : V, ¬ G.IsIsolated v) (ℓ : ℕ) :
    NoIsolated (compressSuspendedCode G hp ℓ) := by
  apply (recodeGraph_noIsolated_iff (compressSuspendedGraph G hp ℓ)).mpr
  intro x
  rw [← (compressSuspendedGraph G hp ℓ).exists_adj_iff_not_isIsolated]
  cases x with
  | inl z =>
      have hshort : ∀ u : SuspendedRetained p,
          ¬ (shortenSuspendedGraph G hp).IsIsolated u := by
        exact (recodeGraph_noIsolated_iff (shortenSuspendedGraph G hp)).mp
          (shortenSuspendedCode_noIsolated hp hG)
      obtain ⟨y, hzy⟩ :=
        (shortenSuspendedGraph G hp).exists_adj_iff_not_isIsolated.mpr
          (hshort z)
      refine ⟨Sum.inl y, ?_⟩
      change ((shortenSuspendedGraph G hp).map
          (compressedRetainedEmbedding (p := p) (ℓ := ℓ)) ⊔
        sequencePathGraph (compressedSuspendedSequence hp ℓ)).Adj
          (Sum.inl z) (Sum.inl y)
      rw [SimpleGraph.sup_adj]
      left
      rw [SimpleGraph.map_adj]
      exact ⟨z, y, hzy, rfl, rfl⟩
  | inr i =>
      let a : Fin (ℓ + 2) := suspendedMidIndex i
      let b : Fin (ℓ + 2) := suspendedNextIndex i
      refine ⟨compressedSuspendedSequence hp ℓ b, ?_⟩
      change ((shortenSuspendedGraph G hp).map
          (compressedRetainedEmbedding (p := p) (ℓ := ℓ)) ⊔
        sequencePathGraph (compressedSuspendedSequence hp ℓ)).Adj
          (Sum.inr i) (compressedSuspendedSequence hp ℓ b)
      rw [SimpleGraph.sup_adj]
      right
      rw [← compressedSuspendedSequence_mid hp i]
      apply sequencePathGraph_adj_consecutive _
        (compressedSuspendedSequence_injective hp ℓ) a b
      simp [a, b, suspendedMidIndex, suspendedNextIndex]

/-- A copy of the partially compressed graph, together with a fresh full
endpoint path, reconstructs the original graph.  Freshness is required only
from the copied retained vertices; the new path may reuse the canonical
short replacement path. -/
theorem isContained_of_compressSuspended_copy_and_path
    {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {C : SimpleGraph W} {t ℓ : ℕ} {p : Fin (t + 2) → V}
    (hp : IsSuspendedPath G p)
    (copy : SimpleGraph.Copy (compressSuspendedGraph G hp ℓ) C)
    (q : Fin (t + 2) → W) (hqinj : Function.Injective q)
    (hqadj : ∀ i j : Fin (t + 2), i.val + 1 = j.val → C.Adj (q i) (q j))
    (hqleft : q 0 = copy (Sum.inl (suspendedLeft hp)))
    (hqright : q (suspendedLastIndex t) =
      copy (Sum.inl (suspendedRight hp)))
    (hqfresh : ∀ i : Fin t,
      q (suspendedMidIndex i) ∉
        Set.range (fun x : SuspendedRetained p ↦ copy (Sum.inl x))) :
    G ⊑ C := by
  let homS : shortenSuspendedGraph G hp →g C :=
    { toFun := fun x ↦ copy (Sum.inl x)
      map_rel' := by
        intro x y hxy
        apply copy.toHom.map_adj
        change ((shortenSuspendedGraph G hp).map
            (compressedRetainedEmbedding (p := p) (ℓ := ℓ)) ⊔
          sequencePathGraph (compressedSuspendedSequence hp ℓ)).Adj
            (Sum.inl x) (Sum.inl y)
        rw [SimpleGraph.sup_adj]
        left
        rw [SimpleGraph.map_adj]
        exact ⟨x, y, hxy, rfl, rfl⟩ }
  have hhomS : Function.Injective homS := by
    intro x y hxy
    have hs : Sum.inl x = Sum.inl y := copy.injective hxy
    exact Sum.inl.inj hs
  let copyS : SimpleGraph.Copy (shortenSuspendedGraph G hp) C :=
    homS.toCopy hhomS
  apply isContained_of_shortenSuspended_copy_and_path hp copyS q hqinj hqadj
  · exact hqleft
  · exact hqright
  · intro i hi
    exact hqfresh i hi

/-- The canonical replacement path transported through a copy of the
compressed graph. -/
def copiedCompressedPath
    {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {C : SimpleGraph W} {t ℓ : ℕ} {p : Fin (t + 2) → V}
    (hp : IsSuspendedPath G p)
    (copy : SimpleGraph.Copy (compressSuspendedGraph G hp ℓ) C) :
    Fin (ℓ + 2) → W :=
  fun i ↦ copy (compressedSuspendedSequence hp ℓ i)

theorem copiedCompressedPath_isEndpointPath
    {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {C : SimpleGraph W} {t ℓ : ℕ} {p : Fin (t + 2) → V}
    (hp : IsSuspendedPath G p)
    (copy : SimpleGraph.Copy (compressSuspendedGraph G hp ℓ) C) :
    IsEndpointPath C (copiedCompressedPath hp copy) := by
  constructor
  · exact copy.injective.comp (compressedSuspendedSequence_injective hp ℓ)
  · intro i j hij
    apply copy.toHom.map_adj
    change ((shortenSuspendedGraph G hp).map
        (compressedRetainedEmbedding (p := p) (ℓ := ℓ)) ⊔
      sequencePathGraph (compressedSuspendedSequence hp ℓ)).Adj
        (compressedSuspendedSequence hp ℓ i)
        (compressedSuspendedSequence hp ℓ j)
    rw [SimpleGraph.sup_adj]
    right
    exact sequencePathGraph_adj_consecutive _
      (compressedSuspendedSequence_injective hp ℓ) i j hij

@[simp] theorem copiedCompressedPath_zero
    {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {C : SimpleGraph W} {t ℓ : ℕ} {p : Fin (t + 2) → V}
    (hp : IsSuspendedPath G p)
    (copy : SimpleGraph.Copy (compressSuspendedGraph G hp ℓ) C) :
    copiedCompressedPath hp copy 0 = copy (Sum.inl (suspendedLeft hp)) := by
  simp [copiedCompressedPath]

@[simp] theorem copiedCompressedPath_last
    {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {C : SimpleGraph W} {t ℓ : ℕ} {p : Fin (t + 2) → V}
    (hp : IsSuspendedPath G p)
    (copy : SimpleGraph.Copy (compressSuspendedGraph G hp ℓ) C) :
    copiedCompressedPath hp copy (Fin.last (ℓ + 1)) =
      copy (Sum.inl (suspendedRight hp)) := by
  simp [copiedCompressedPath]

/-- Images of all retained target vertices in a compressed copy. -/
def compressedRetainedImage
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {C : SimpleGraph W} {t ℓ : ℕ} {p : Fin (t + 2) → V}
    (hp : IsSuspendedPath G p)
    (copy : SimpleGraph.Copy (compressSuspendedGraph G hp ℓ) C) : Finset W :=
  Finset.univ.image fun x : SuspendedRetained p ↦ copy (Sum.inl x)

/-- Retained images other than the two path endpoints are forbidden during
endpoint growth. -/
def compressedForbidden
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {C : SimpleGraph W} {t ℓ : ℕ} {p : Fin (t + 2) → V}
    (hp : IsSuspendedPath G p)
    (copy : SimpleGraph.Copy (compressSuspendedGraph G hp ℓ) C) : Finset W :=
  ((compressedRetainedImage hp copy).erase
    (copy (Sum.inl (suspendedLeft hp)))).erase
      (copy (Sum.inl (suspendedRight hp)))

/-- Host vertices available to endpoint-path growth. -/
def compressedAvailable
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {C : SimpleGraph W} {t ℓ : ℕ} {p : Fin (t + 2) → V}
    (hp : IsSuspendedPath G p)
    (copy : SimpleGraph.Copy (compressSuspendedGraph G hp ℓ) C) : Finset W :=
  Finset.univ \ compressedForbidden hp copy

theorem compressedRetainedImage_card
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {C : SimpleGraph W} {t ℓ : ℕ} {p : Fin (t + 2) → V}
    (hp : IsSuspendedPath G p)
    (copy : SimpleGraph.Copy (compressSuspendedGraph G hp ℓ) C) :
    (compressedRetainedImage hp copy).card = Fintype.card V - t := by
  rw [compressedRetainedImage, Finset.card_image_of_injective]
  · change Fintype.card (SuspendedRetained p) = Fintype.card V - t
    change Fintype.card {v : V // v ∉ suspendedInterior p} = _
    rw [Fintype.card_subtype_compl]
    have hcard : Fintype.card {v : V // v ∈ suspendedInterior p} = t := by
      change Fintype.card ↥(suspendedInterior p) = t
      rw [Fintype.card_coe, suspendedInterior_card hp]
    rw [hcard]
  · intro x y hxy
    exact Sum.inl.inj (copy.injective hxy)

theorem compressedAvailable_card
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {C : SimpleGraph W} {t ℓ : ℕ} {p : Fin (t + 2) → V}
    (hp : IsSuspendedPath G p)
    (copy : SimpleGraph.Copy (compressSuspendedGraph G hp ℓ) C) :
    (compressedAvailable hp copy).card =
      Fintype.card W - (Fintype.card V - t - 2) := by
  classical
  let L := copy (Sum.inl (suspendedLeft hp))
  let R := copy (Sum.inl (suspendedRight hp))
  let I := compressedRetainedImage hp copy
  have hLI : L ∈ I := by
    simp only [I, L, compressedRetainedImage, Finset.mem_image]
    exact ⟨suspendedLeft hp, Finset.mem_univ _, rfl⟩
  have hRI : R ∈ I := by
    simp only [I, R, compressedRetainedImage, Finset.mem_image]
    exact ⟨suspendedRight hp, Finset.mem_univ _, rfl⟩
  have hLR : L ≠ R := by
    intro h
    have hs := Sum.inl.inj (copy.injective h)
    exact suspended_endpoints_ne hp (congrArg Subtype.val hs)
  have hRerase : R ∈ I.erase L := by simp [hRI, hLR.symm]
  have hforbidden : (compressedForbidden hp copy).card = I.card - 2 := by
    change ((I.erase L).erase R).card = I.card - 2
    rw [Finset.card_erase_of_mem hRerase, Finset.card_erase_of_mem hLI]
    omega
  have havail := Finset.card_sdiff_add_card_eq_card
    (show compressedForbidden hp copy ⊆ (Finset.univ : Finset W) from
      Finset.subset_univ _)
  rw [← compressedAvailable, Finset.card_univ] at havail
  have hIcard : I.card = Fintype.card V - t := by
    exact compressedRetainedImage_card hp copy
  rw [hforbidden, hIcard] at havail
  omega

@[simp] theorem mem_compressedAvailable
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {C : SimpleGraph W} {t ℓ : ℕ} {p : Fin (t + 2) → V}
    {hp : IsSuspendedPath G p}
    {copy : SimpleGraph.Copy (compressSuspendedGraph G hp ℓ) C}
    {x : W} :
    x ∈ compressedAvailable hp copy ↔ x ∉ compressedForbidden hp copy := by
  simp [compressedAvailable]

theorem copiedCompressedPath_mem_available
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {C : SimpleGraph W} {t ℓ : ℕ} {p : Fin (t + 2) → V}
    (hp : IsSuspendedPath G p)
    (copy : SimpleGraph.Copy (compressSuspendedGraph G hp ℓ) C)
    (i : Fin (ℓ + 2)) :
    copiedCompressedPath hp copy i ∈ compressedAvailable hp copy := by
  classical
  rw [mem_compressedAvailable]
  intro hi
  have hiImage : copiedCompressedPath hp copy i ∈
      compressedRetainedImage hp copy := by
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)
  rw [compressedRetainedImage, Finset.mem_image] at hiImage
  obtain ⟨x, -, hx⟩ := hiImage
  have hseq : compressedSuspendedSequence hp ℓ i = Sum.inl x := by
    exact copy.injective hx.symm
  unfold compressedSuspendedSequence at hseq
  split at hseq <;> rename_i hi0
  · have hleft : copiedCompressedPath hp copy i =
        copy (Sum.inl (suspendedLeft hp)) := by
      change copy (compressedSuspendedSequence hp ℓ i) = _
      apply congrArg copy
      unfold compressedSuspendedSequence
      rw [dif_pos hi0]
    have hnot := (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi))
    exact hnot hleft
  · split at hseq <;> rename_i hilast
    · have hright : copiedCompressedPath hp copy i =
          copy (Sum.inl (suspendedRight hp)) := by
        change copy (compressedSuspendedSequence hp ℓ i) = _
        apply congrArg copy
        unfold compressedSuspendedSequence
        rw [dif_neg hi0, dif_pos hilast]
      exact (Finset.ne_of_mem_erase hi) hright
    · contradiction

/-- A full path in the available induced host is fresh from every copied
retained vertex at its internal positions. -/
theorem available_path_fresh_from_retained
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {C : SimpleGraph W} {t ℓ : ℕ} {p : Fin (t + 2) → V}
    (hp : IsSuspendedPath G p)
    (copy : SimpleGraph.Copy (compressSuspendedGraph G hp ℓ) C)
    (q : Fin (t + 2) → W) (hqinj : Function.Injective q)
    (hqmem : ∀ i, q i ∈ compressedAvailable hp copy)
    (hqleft : q 0 = copy (Sum.inl (suspendedLeft hp)))
    (hqright : q (suspendedLastIndex t) =
      copy (Sum.inl (suspendedRight hp))) :
    ∀ i : Fin t, q (suspendedMidIndex i) ∉
      Set.range (fun x : SuspendedRetained p ↦ copy (Sum.inl x)) := by
  intro i hi
  obtain ⟨x, hx⟩ := hi
  have hxImage : copy (Sum.inl x) ∈ compressedRetainedImage hp copy := by
    rw [compressedRetainedImage, Finset.mem_image]
    exact ⟨x, Finset.mem_univ _, rfl⟩
  have hxLeft : x ≠ suspendedLeft hp := by
    intro hxl
    subst x
    have heq : q (suspendedMidIndex i) = q 0 :=
      hx.symm.trans hqleft.symm
    have hind := hqinj heq
    have hv := congrArg Fin.val hind
    simp [suspendedMidIndex] at hv
  have hxRight : x ≠ suspendedRight hp := by
    intro hxr
    subst x
    have heq : q (suspendedMidIndex i) = q (suspendedLastIndex t) :=
      hx.symm.trans hqright.symm
    have hind := hqinj heq
    have hv := congrArg Fin.val hind
    simp [suspendedMidIndex, suspendedLastIndex] at hv
    exact (Nat.ne_of_lt i.isLt) hv
  have hxForbidden : copy (Sum.inl x) ∈ compressedForbidden hp copy := by
    simp only [compressedForbidden, Finset.mem_erase]
    exact ⟨by
      intro heq
      exact hxRight (Sum.inl.inj (copy.injective heq)),
      by
        refine ⟨?_, hxImage⟩
        intro heq
        exact hxLeft (Sum.inl.inj (copy.injective heq))⟩
  exact (mem_compressedAvailable.mp (hqmem (suspendedMidIndex i)))
    (hx ▸ hxForbidden)

end Erdos570
