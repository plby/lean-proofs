import ErdosProblems.Erdos814.Basic
import ErdosProblems.Erdos814.Shadow

/-!
# Erdős 814: Sauermann's extension lemma

This file formalizes Lemma 3.1 of Sauermann's proof.  Everything is phrased on a fixed finite
vertex type.  Thus `U` is the vertex set of the graph called `H` in the paper, while `A` is the
vertex set of a proper induced extension `H̃`.  The graph itself does not change: restricting
`G` to a finset is the operation of taking an induced subgraph.

The conclusion deliberately records all six clauses of the lemma.  In particular, the reserve
sets are not merely a cardinality device: the colouring argument later uses both their support
and their anticompleteness properties.
-/

open Finset SimpleGraph BigOperators

namespace Erdos814

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Vertices of `A` whose degree in the induced graph `G[A]` is at most `k - 1`. -/
def lowVertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) : Finset V :=
  A.filter fun v ↦ degreeOn G A v ≤ k - 1

/-- Vertices of `A` whose degree in `G[A]` is at most `k - 2`. -/
def veryLowVertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) : Finset V :=
  A.filter fun v ↦ degreeOn G A v ≤ k - 2

@[simp] lemma mem_lowVertices {A : Finset V} {k : ℕ} {v : V} :
    v ∈ lowVertices G A k ↔ v ∈ A ∧ degreeOn G A v ≤ k - 1 := by
  simp [lowVertices]

@[simp] lemma mem_veryLowVertices {A : Finset V} {k : ℕ} {v : V} :
    v ∈ veryLowVertices G A k ↔ v ∈ A ∧ degreeOn G A v ≤ k - 2 := by
  simp [veryLowVertices]

lemma veryLowVertices_subset_lowVertices {A : Finset V} {k : ℕ} (hk : 2 ≤ k) :
    veryLowVertices G A k ⊆ lowVertices G A k := by
  intro v hv
  rw [mem_veryLowVertices] at hv
  rw [mem_lowVertices]
  exact ⟨hv.1, by omega⟩

/-- `X` and `Y` have no edge between them. -/
def Anticomplete (G : SimpleGraph V) (X Y : Finset V) : Prop :=
  ¬ AdjacentSets G X Y

lemma Anticomplete.symm {X Y : Finset V} (h : Anticomplete G X Y) :
    Anticomplete G Y X := by
  intro hadj
  exact h hadj.symm

lemma Anticomplete.mono {X Y X' Y' : Finset V} (h : Anticomplete G X Y)
    (hX : X' ⊆ X) (hY : Y' ⊆ Y) : Anticomplete G X' Y' := by
  intro hadj
  rcases hadj with ⟨x, hx, y, hy, hxy⟩
  exact h ⟨x, hX hx, y, hY hy, hxy⟩

lemma Anticomplete.union_left {X Y Z : Finset V}
    (hX : Anticomplete G X Z) (hY : Anticomplete G Y Z) :
    Anticomplete G (X ∪ Y) Z := by
  intro hadj
  rcases hadj with ⟨x, hx, z, hz, hxz⟩
  rcases mem_union.mp hx with hx | hx
  · exact hX ⟨x, hx, z, hz, hxz⟩
  · exact hY ⟨x, hx, z, hz, hxz⟩

lemma anticomplete_empty_left (X : Finset V) : Anticomplete G ∅ X := by
  simp [Anticomplete, AdjacentSets]

lemma anticomplete_empty_right (X : Finset V) : Anticomplete G X ∅ := by
  simp [Anticomplete, AdjacentSets]

/-- The union of the reserve sets indexed by low-degree vertices of `A`. -/
def reserveUnion (B : V → Finset V) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) : Finset V :=
  (lowVertices G A k).biUnion B

/-- The six-clause conclusion of Sauermann's extension lemma for one extension `A` of `U`. -/
structure ExtensionConclusion
    (C : ProtectedFamily G U k) (B : V → Finset V) (A U' : Finset V) : Prop where
  /-- Clause (a): the retained induced graph is nonempty and has minimum degree at least `k`. -/
  minDegree : HasMinDegreeOn G U' k
  /-- The retained graph is induced inside the extension. -/
  subset_extension : U' ⊆ A
  /-- Clause (b): deleting vertices does not increase signed shortage. -/
  shortage_le : shortage k G U' ≤ shortage k G A
  /-- Clause (c), first part: every deleted vertex lies in a reserve indexed by a low vertex. -/
  deleted_subset_reserves : A \ U' ⊆ reserveUnion B G A k
  /-- Clause (c), second part: every deleted vertex was already in the old graph. -/
  deleted_subset_old : A \ U' ⊆ U
  /-- Clause (d): deleted vertices have no neighbour among the genuinely new vertices. -/
  deleted_anticomplete_new : Anticomplete G (A \ U') (A \ U)
  /-- Clause (e): every protected block is wholly retained or wholly deleted. -/
  blocks_whole : C.WholeBlocks U'
  /-- Clause (f): a retained protected block has no neighbour among the deleted vertices. -/
  retained_blocks_anticomplete :
    ∀ D ∈ C.blocks, D ⊆ U' → Anticomplete G D (A \ U')

/-- The quantified extension assertion attached to the output of Lemma 3.1. -/
def HasExtensionProperty
    (C : ProtectedFamily G U k) (S : Finset V) (B : V → Finset V) : Prop :=
  ∀ A : Finset V,
    U ⊂ A →
    lowVertices G A k ⊆ lowVertices G U k \ S →
    (∀ D ∈ C.blocks, Anticomplete G (A \ U) D) →
    ∃ U' : Finset V, ExtensionConclusion C B A U'

/-- The exact output data in Sauermann's Lemma 3.1. -/
structure ExtensionCertificate
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (k : ℕ) (C : ProtectedFamily G U k) where
  /-- Low-degree vertices paid for directly by the deficiency budget. -/
  S : Finset V
  S_subset_low : S ⊆ lowVertices G U k
  veryLow_subset_S : veryLowVertices G U k ⊆ S
  /-- Reserve associated with every low vertex not put in `S` (irrelevant indices may be empty). -/
  reserve : V → Finset V
  reserve_subset : ∀ v ∈ lowVertices G U k \ S, reserve v ⊆ U
  reserve_pairwise :
    ∀ v ∈ lowVertices G U k \ S,
      ∀ w ∈ lowVertices G U k \ S, v ≠ w → Disjoint (reserve v) (reserve w)
  /-- Equation (3.1) of the paper, kept in `ℤ` to match signed shortage. -/
  deficit_le :
    ((S.sum fun s ↦ k - degreeOn G U s : ℕ) : ℤ) ≤ 2 * shortage k G U
  extension : HasExtensionProperty C S reserve

namespace ExtensionCertificate

variable {U : Finset V} {k : ℕ} {C : ProtectedFamily G U k}

lemma reserve_subset_old (E : ExtensionCertificate G U k C)
    {v : V} (hv : v ∈ lowVertices G U k \ E.S) : E.reserve v ⊆ U :=
  E.reserve_subset v hv

lemma reserve_disjoint (E : ExtensionCertificate G U k C)
    {v w : V} (hv : v ∈ lowVertices G U k \ E.S)
    (hw : w ∈ lowVertices G U k \ E.S) (hvw : v ≠ w) :
    Disjoint (E.reserve v) (E.reserve w) :=
  E.reserve_pairwise v hv w hw hvw

end ExtensionCertificate

lemma hasMinDegreeOn_of_lowVertices_eq_empty {A : Finset V} {k : ℕ}
    (hA : A.Nonempty) (hlow : lowVertices G A k = ∅) :
    HasMinDegreeOn G A k := by
  refine ⟨hA, ?_⟩
  intro v hv
  by_contra hnot
  have hvlow : v ∈ lowVertices G A k := by
    rw [mem_lowVertices]
    exact ⟨hv, by omega⟩
  simpa [hlow] using hvlow

lemma nonempty_of_ssubset {A B : Finset V} (h : A ⊂ B) : B.Nonempty := by
  rcases Finset.ssubset_iff_subset_ne.mp h with ⟨hAB, hne⟩
  by_contra hB
  rw [Finset.not_nonempty_iff_eq_empty] at hB
  subst B
  have hA : A = ∅ := Finset.subset_empty.mp hAB
  exact hne hA

/-- If the extension already has minimum degree `k`, Lemma 3.1 deletes nothing. -/
lemma extensionConclusion_self {U A : Finset V} {k : ℕ}
    (C : ProtectedFamily G U k) (B : V → Finset V)
    (hUA : U ⊆ A) (hmin : HasMinDegreeOn G A k) :
    ExtensionConclusion C B A A := by
  refine
    { minDegree := hmin
      subset_extension := Subset.rfl
      shortage_le := le_rfl
      deleted_subset_reserves := ?_
      deleted_subset_old := ?_
      deleted_anticomplete_new := ?_
      blocks_whole := ?_
      retained_blocks_anticomplete := ?_ }
  · simp
  · simp
  · simpa using anticomplete_empty_left (G := G) (A \ U)
  · intro D hD
    exact Or.inl ((C.subset_ambient D hD).trans hUA)
  · intro D hD hDA
    simpa using anticomplete_empty_right (G := G) D

lemma lowVertices_eq_empty_of_subset_empty {A : Finset V} {k : ℕ}
    (h : lowVertices G A k ⊆ ∅) : lowVertices G A k = ∅ :=
  Finset.subset_empty.mp h

lemma extensionConclusion_self_of_low_empty {U A : Finset V} {k : ℕ}
    (C : ProtectedFamily G U k) (B : V → Finset V)
    (hUA : U ⊆ A) (hproper : U ⊂ A)
    (hlow : lowVertices G A k ⊆ ∅) :
    ExtensionConclusion C B A A := by
  apply extensionConclusion_self C B hUA
  exact hasMinDegreeOn_of_lowVertices_eq_empty (nonempty_of_ssubset hproper)
    (lowVertices_eq_empty_of_subset_empty hlow)

/-- Conclusions obtained from the shadow complement lift back to the original old graph.
This is the common bookkeeping in Cases B.1 and B.2.a. -/
lemma ExtensionConclusion.lift_shadow_complement
    {U W F A U' : Finset V} {k : ℕ}
    (C : ProtectedFamily G U k) (CF : ProtectedFamily G F k)
    (B : V → Finset V)
    (hWU : W ⊆ U) (hF : F = U \ W) (hUA : U ⊆ A)
    (hCF : ∀ D, D ∈ CF.blocks ↔ D ∈ C.blocks ∧ D ⊆ F)
    (hwhole : C.WholeBlocks W)
    (R : ExtensionConclusion CF B A U') :
    ExtensionConclusion C B A U' := by
  have hFU : F ⊆ U := by
    rw [hF]
    exact sdiff_subset
  have hnew : A \ U ⊆ A \ F := by
    intro x hx
    rw [mem_sdiff] at hx ⊢
    exact ⟨hx.1, fun hxF ↦ hx.2 (hFU hxF)⟩
  refine
    { minDegree := R.minDegree
      subset_extension := R.subset_extension
      shortage_le := R.shortage_le
      deleted_subset_reserves := R.deleted_subset_reserves
      deleted_subset_old := fun x hx ↦ hFU (R.deleted_subset_old hx)
      deleted_anticomplete_new :=
        R.deleted_anticomplete_new.mono Subset.rfl hnew
      blocks_whole := ?_
      retained_blocks_anticomplete := ?_ }
  · intro D hDC
    by_cases hDCF : D ∈ CF.blocks
    · exact R.blocks_whole D hDCF
    · have hDW : D ⊆ W := by
        rcases hwhole D hDC with hDW | hdisj
        · exact hDW
        · exfalso
          apply hDCF
          rw [hCF]
          refine ⟨hDC, ?_⟩
          intro x hxD
          rw [hF, mem_sdiff]
          exact ⟨C.subset_ambient D hDC hxD,
            fun hxW ↦ Finset.disjoint_left.mp hdisj hxD hxW⟩
      left
      intro x hxD
      have hxA : x ∈ A := hUA (C.subset_ambient D hDC hxD)
      by_contra hxU'
      have hxdel : x ∈ A \ U' := mem_sdiff.mpr ⟨hxA, hxU'⟩
      have hxF := R.deleted_subset_old hxdel
      rw [hF, mem_sdiff] at hxF
      exact hxF.2 (hDW hxD)
  · intro D hDC hDU'
    by_cases hDCF : D ∈ CF.blocks
    · exact R.retained_blocks_anticomplete D hDCF hDU'
    · have hDW : D ⊆ W := by
        rcases hwhole D hDC with hDW | hdisj
        · exact hDW
        · exfalso
          apply hDCF
          rw [hCF]
          refine ⟨hDC, ?_⟩
          intro x hxD
          rw [hF, mem_sdiff]
          exact ⟨C.subset_ambient D hDC hxD,
            fun hxW ↦ Finset.disjoint_left.mp hdisj hxD hxW⟩
      have hDAF : D ⊆ A \ F := by
        intro x hxD
        rw [mem_sdiff]
        refine ⟨hUA (C.subset_ambient D hDC hxD), ?_⟩
        intro hxF
        rw [hF, mem_sdiff] at hxF
        exact hxF.2 (hDW hxD)
      exact R.deleted_anticomplete_new.symm.mono hDAF Subset.rfl

lemma deficitSum_mono_of_subset {F U S : Finset V} {k : ℕ}
    (hFU : F ⊆ U) (hS : S ⊆ lowVertices G F k) :
    (S.sum fun s ↦ k - degreeOn G U s) ≤
      S.sum fun s ↦ k - degreeOn G F s := by
  exact Finset.sum_le_sum (s := S) fun s hs ↦
    Nat.sub_le_sub_left (degreeOn_mono G hFU s) k

lemma lowVertices_mono_degree {F U : Finset V} {k : ℕ}
    (hFU : F ⊆ U) {x : V} (hxF : x ∈ F)
    (hxlow : x ∈ lowVertices G U k) : x ∈ lowVertices G F k := by
  rw [mem_lowVertices] at hxlow ⊢
  exact ⟨hxF, (degreeOn_mono G hFU x).trans hxlow.2⟩

lemma veryLowVertices_mono_degree {F U : Finset V} {k : ℕ}
    (hFU : F ⊆ U) {x : V} (hxF : x ∈ F)
    (hxlow : x ∈ veryLowVertices G U k) : x ∈ veryLowVertices G F k := by
  rw [mem_veryLowVertices] at hxlow ⊢
  exact ⟨hxF, (degreeOn_mono G hFU x).trans hxlow.2⟩

private lemma extensionCertificate_empty (k : ℕ)
    (C : ProtectedFamily G (∅ : Finset V) k) :
    Nonempty (ExtensionCertificate G ∅ k C) := by
  let B : V → Finset V := fun _ ↦ ∅
  refine ⟨{
    S := ∅
    S_subset_low := by simp
    veryLow_subset_S := by simp [veryLowVertices]
    reserve := B
    reserve_subset := ?_
    reserve_pairwise := ?_
    deficit_le := ?_
    extension := ?_ }⟩
  · intro v hv
    simp [lowVertices] at hv
  · intro v hv
    simp [lowVertices] at hv
  · simp [shortage]
  · intro A hproper hlow hblocks
    refine ⟨A, extensionConclusion_self_of_low_empty C B ?_ hproper ?_⟩
    · simp
    · simpa [lowVertices] using hlow

lemma lowDefect_eq_sum_lowVertices_inter {U X : Finset V} {k : ℕ}
    (hXU : X ⊆ U) :
    lowDefect k G U X =
      (lowVertices G U k ∩ X).sum (fun x ↦ k - degreeOn G U x) := by
  classical
  have heq : X.filter (fun x ↦ degreeOn G U x ≤ k - 1) =
      lowVertices G U k ∩ X := by
    ext x
    simp only [mem_filter, mem_inter, mem_lowVertices]
    constructor
    · rintro ⟨hxX, hxlow⟩
      exact ⟨⟨hXU hxX, hxlow⟩, hxX⟩
    · rintro ⟨⟨hxU, hxlow⟩, hxX⟩
      exact ⟨hxX, hxlow⟩
  unfold lowDefect
  calc
    X.sum (fun x ↦ if degreeOn G U x ≤ k - 1 then
        k - degreeOn G U x else 0) =
        (X.filter (fun x ↦ degreeOn G U x ≤ k - 1)).sum
          (fun x ↦ k - degreeOn G U x) :=
      (Finset.sum_filter (s := X) (fun x ↦ degreeOn G U x ≤ k - 1)
        (fun x ↦ k - degreeOn G U x)).symm
    _ = (lowVertices G U k ∩ X).sum (fun x ↦ k - degreeOn G U x) := by rw [heq]

private lemma extensionCertificate_allLow {U : Finset V} {k : ℕ}
    (C : ProtectedFamily G U k) (hk : 2 ≤ k)
    (hdef : (lowDefect k G U U : ℤ) ≤ 2 * shortage k G U) :
    Nonempty (ExtensionCertificate G U k C) := by
  let B : V → Finset V := fun _ ↦ ∅
  refine ⟨{
    S := lowVertices G U k
    S_subset_low := Subset.rfl
    veryLow_subset_S := veryLowVertices_subset_lowVertices (G := G) hk
    reserve := B
    reserve_subset := ?_
    reserve_pairwise := ?_
    deficit_le := ?_
    extension := ?_ }⟩
  · intro v hv
    simp at hv
  · intro v hv
    simp at hv
  · have hsum : lowDefect k G U U =
        (lowVertices G U k ∩ U).sum (fun x ↦ k - degreeOn G U x) :=
      lowDefect_eq_sum_lowVertices_inter (G := G) (k := k)
        (U := U) (X := U) Subset.rfl
    have hinter : lowVertices G U k ∩ U = lowVertices G U k := by
      apply inter_eq_left.mpr
      intro x hx
      exact (mem_lowVertices.mp hx).1
    rw [hinter] at hsum
    exact hsum ▸ hdef
  · intro A hproper hlow hblocks
    refine ⟨A, extensionConclusion_self_of_low_empty C B
      (Finset.ssubset_iff_subset_ne.mp hproper).1 hproper ?_⟩
    simpa using hlow

private lemma delete_zero_shadow_conclusion
    {U A : Finset V} {k : ℕ} {w : V}
    (C : ProtectedFamily G U k) (B : V → Finset V)
    (hk : 2 ≤ k) (hUA : U ⊆ A) (hproper : U ⊂ A)
    (hwU : w ∈ U) (hwlowU : degreeOn G U w ≤ k - 1)
    (hwlowA : degreeOn G A w ≤ k - 1)
    (huniqueA : ∀ x ∈ A, degreeOn G A x ≤ k - 1 → x = w)
    (hnew : ∀ D ∈ C.blocks, Anticomplete G (A \ U) D)
    (hzero : deletionPotential k G U (shadow C w) = 0)
    (hreserve : shadow C w ⊆ B w) :
    ∃ U' : Finset V, ExtensionConclusion C B A U' := by
  let CA : ProtectedFamily G A k := C.extendAmbient hUA hnew
  let WA : Finset V := shadow CA w
  have hwA : w ∈ A := hUA hwU
  have hstable := shadow_stable_in_extension C (by omega) hUA hwU hwlowA hnew hzero
  have hWAold : WA ⊆ shadow C w := by simpa [CA, WA] using hstable.1
  have hWAanti : Anticomplete G WA (A \ U) := by
    change ¬ AdjacentSets G WA (A \ U)
    simpa [CA, WA] using hstable.2
  have hWAA : WA ⊆ A := by
    simpa [CA, WA] using shadow_subset_ambient CA hwA
  have hWAproper : WA ≠ A := by
    intro heq
    have hAU : A ⊆ U := by
      intro x hxA
      have hxWA : x ∈ WA := by simpa [heq] using hxA
      exact (shadow_subset_ambient C hwU) (hWAold hxWA)
    exact (Finset.ssubset_iff_subset_ne.mp hproper).2 (Subset.antisymm hUA hAU)
  have hmin : HasMinDegreeOn G (A \ WA) k := by
    apply shadow_complement_minDegree_of_unique_low CA (by omega) hwA hwlowA
      (by simpa [WA])
    intro x hxA hxlow
    exact huniqueA x hxA hxlow
  have hshort : shortage k G (A \ WA) ≤ shortage k G A := by
    simpa [WA] using shortage_delete_shadow_le CA (by omega) hwA hwlowA
  have hdel : A \ (A \ WA) = WA := by
    ext x
    simp only [mem_sdiff]
    constructor
    · rintro ⟨hxA, hxnot⟩
      by_contra hxWA
      exact hxnot ⟨hxA, hxWA⟩
    · intro hxWA
      exact ⟨hWAA hxWA, fun hx ↦ hx.2 hxWA⟩
  refine ⟨A \ WA, ?_⟩
  refine
    { minDegree := hmin
      subset_extension := sdiff_subset
      shortage_le := hshort
      deleted_subset_reserves := ?_
      deleted_subset_old := ?_
      deleted_anticomplete_new := ?_
      blocks_whole := ?_
      retained_blocks_anticomplete := ?_ }
  · rw [hdel]
    intro x hxWA
    rw [reserveUnion, mem_biUnion]
    refine ⟨w, ?_, hreserve (hWAold hxWA)⟩
    rw [mem_lowVertices]
    exact ⟨hwA, hwlowA⟩
  · rw [hdel]
    exact hWAold.trans (shadow_subset_ambient C hwU)
  · simpa [hdel] using hWAanti
  · intro D hDC
    have hDCA : D ∈ CA.blocks := by
      change D ∈ C.blocks
      exact hDC
    have hclosed := shadow_closed CA (by omega) hwA hwlowA
    rcases hclosed.whole_blocks D hDCA with hDWA | hdisj
    · right
      rw [Finset.disjoint_left]
      intro x hxD hxcomp
      exact (mem_sdiff.mp hxcomp).2 (hDWA hxD)
    · left
      intro x hxD
      rw [mem_sdiff]
      exact ⟨hUA (C.subset_ambient D hDC hxD),
        fun hxWA ↦ Finset.disjoint_left.mp hdisj hxD hxWA⟩
  · intro D hDC hDret
    rw [hdel]
    intro hadj
    have hDCA : D ∈ CA.blocks := by
      change D ∈ C.blocks
      exact hDC
    have hclosed := shadow_closed CA (by omega) hwA hwlowA
    have hDWA : D ⊆ WA := hclosed.adjacent_blocks D hDCA hadj
    obtain ⟨x, hxD⟩ := C.nonempty D hDC
    have hxret := hDret hxD
    exact (mem_sdiff.mp hxret).2 (hDWA hxD)

private lemma extensionCertificate_zero_full_shadow
    {U : Finset V} {k : ℕ} {w : V}
    (C : ProtectedFamily G U k) (hk : 2 ≤ k)
    (hwU : w ∈ U) (hwlow : degreeOn G U w ≤ k - 1)
    (hfull : shadow C w = U)
    (hzero : deletionPotential k G U (shadow C w) = 0) :
    Nonempty (ExtensionCertificate G U k C) := by
  let B : V → Finset V := fun v ↦ if v = w then shadow C w else ∅
  have huniq := shadow_zero_unique_low C (by omega) hwU hwlow hzero
  refine ⟨{
    S := ∅
    S_subset_low := by simp
    veryLow_subset_S := ?_
    reserve := B
    reserve_subset := ?_
    reserve_pairwise := ?_
    deficit_le := ?_
    extension := ?_ }⟩
  · intro x hx
    rw [mem_veryLowVertices] at hx
    have hxw := huniq.1 x (by simpa [hfull] using hx.1) (by omega)
    subst x
    rw [huniq.2] at hx
    omega
  · intro v hv
    rw [mem_sdiff, mem_lowVertices] at hv
    have hvw := huniq.1 v (by simpa [hfull] using hv.1.1) hv.1.2
    subst v
    simp [B, hfull]
  · intro v hv z hz hvz
    rw [mem_sdiff, mem_lowVertices] at hv hz
    have hvw := huniq.1 v (by simpa [hfull] using hv.1.1) hv.1.2
    have hzw := huniq.1 z (by simpa [hfull] using hz.1.1) hz.1.2
    exact (hvz (hvw.trans hzw.symm)).elim
  · have hshort := shortage_delete_shadow_eq C hwU hzero
    rw [hfull] at hshort
    simp [shortage] at hshort ⊢
    omega
  · intro A hproper hlow hnew
    have hUA := (Finset.ssubset_iff_subset_ne.mp hproper).1
    by_cases hempty : lowVertices G A k = ∅
    · exact ⟨A, extensionConclusion_self C B hUA
        (hasMinDegreeOn_of_lowVertices_eq_empty (nonempty_of_ssubset hproper) hempty)⟩
    · obtain ⟨x, hxlow⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have hxold := hlow hxlow
      rw [mem_sdiff, mem_lowVertices] at hxold
      have hxw := huniq.1 x (by simpa [hfull] using hxold.1.1) hxold.1.2
      have hwlowA : degreeOn G A w ≤ k - 1 := by
        subst x
        exact (mem_lowVertices.mp hxlow).2
      have huniqueA : ∀ y ∈ A, degreeOn G A y ≤ k - 1 → y = w := by
        intro y hyA hylow
        have hyold := hlow (mem_lowVertices.mpr ⟨hyA, hylow⟩)
        rw [mem_sdiff, mem_lowVertices] at hyold
        exact huniq.1 y (by simpa [hfull] using hyold.1.1) hyold.1.2
      apply delete_zero_shadow_conclusion C B hk hUA hproper hwU hwlow hwlowA
        huniqueA hnew hzero
      intro y hy
      change y ∈ (if w = w then shadow C w else ∅)
      simp only [ite_true]
      exact hy

lemma shadow_anticomplete_restricted_block
    {U : Finset V} {k : ℕ} {w : V}
    (C : ProtectedFamily G U k) (hk : 1 ≤ k)
    (hwU : w ∈ U) (hwlow : degreeOn G U w ≤ k - 1)
    {D : Finset V}
    (hD : D ∈ (C.restrictShadowComplement hk hwU hwlow).blocks) :
    Anticomplete G (shadow C w) D := by
  intro hadj
  have hmem := (ProtectedFamily.mem_restrictShadowComplement_blocks
    C hk hwU hwlow).mp hD
  have hDW : D ⊆ shadow C w :=
    (shadow_closed C hk hwU hwlow).adjacent_blocks D hmem.1 hadj.symm
  obtain ⟨x, hxD⟩ := C.nonempty D hmem.1
  exact (mem_sdiff.mp (hmem.2 hxD)).2 (hDW hxD)

lemma extension_anticomplete_restricted_block
    {U A : Finset V} {k : ℕ} {w : V}
    (C : ProtectedFamily G U k) (hk : 1 ≤ k)
    (hwU : w ∈ U) (hwlow : degreeOn G U w ≤ k - 1)
    (hUA : U ⊆ A)
    (hnew : ∀ D ∈ C.blocks, Anticomplete G (A \ U) D)
    {D : Finset V}
    (hD : D ∈ (C.restrictShadowComplement hk hwU hwlow).blocks) :
    Anticomplete G (A \ (U \ shadow C w)) D := by
  have hmem := (ProtectedFamily.mem_restrictShadowComplement_blocks
    C hk hwU hwlow).mp hD
  have hcontain : A \ (U \ shadow C w) ⊆ (A \ U) ∪ shadow C w := by
    intro x hx
    rw [mem_sdiff] at hx
    by_cases hxU : x ∈ U
    · exact mem_union_right _ (by
        by_contra hxW
        exact hx.2 (mem_sdiff.mpr ⟨hxU, hxW⟩))
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hx.1, hxU⟩)
  exact (Anticomplete.union_left (hnew D hmem.1)
    (shadow_anticomplete_restricted_block C hk hwU hwlow hD)).mono
      hcontain Subset.rfl

private lemma extensionCertificate_positive_proper_shadow
    {U : Finset V} {k : ℕ} {w : V}
    (C : ProtectedFamily G U k) (hk : 2 ≤ k)
    (hwU : w ∈ U) (hwlow : degreeOn G U w ≤ k - 1)
    (hproperW : shadow C w ≠ U)
    (hpos : 0 < deletionPotential k G U (shadow C w))
    (EF : ExtensionCertificate G (U \ shadow C w) k
      (C.restrictShadowComplement (by omega) hwU hwlow)) :
    Nonempty (ExtensionCertificate G U k C) := by
  let W := shadow C w
  let F := U \ W
  let CF := C.restrictShadowComplement (by omega) hwU hwlow
  let T := lowVertices G U k ∩ W
  let S := EF.S ∪ T
  have hWU : W ⊆ U := by simpa [W] using shadow_subset_ambient C hwU
  have hFU : F ⊆ U := by simp [F]
  have hlowFU : lowVertices G F k ⊆ lowVertices G U k := by
    intro x hx
    rw [mem_lowVertices] at hx ⊢
    have hold := low_degree_after_delete_shadow C (by omega) hwU hwlow
      (by simpa [F, W] using hx.1) (by simpa [F, W] using hx.2)
    exact ⟨hFU hx.1, hold.1⟩
  refine ⟨{
    S := S
    S_subset_low := ?_
    veryLow_subset_S := ?_
    reserve := EF.reserve
    reserve_subset := ?_
    reserve_pairwise := ?_
    deficit_le := ?_
    extension := ?_ }⟩
  · intro x hx
    rcases mem_union.mp hx with hx | hx
    · exact hlowFU (EF.S_subset_low hx)
    · exact (mem_inter.mp hx).1
  · intro x hx
    rw [mem_veryLowVertices] at hx
    by_cases hxW : x ∈ W
    · exact mem_union_right _ (mem_inter.mpr
        ⟨mem_lowVertices.mpr ⟨hx.1, by omega⟩, hxW⟩)
    · apply mem_union_left
      apply EF.veryLow_subset_S
      exact veryLowVertices_mono_degree hFU (mem_sdiff.mpr ⟨hx.1, hxW⟩)
        (mem_veryLowVertices.mpr hx)
  · intro v hv
    rw [mem_sdiff] at hv
    have hvlow := mem_lowVertices.mp hv.1
    have hvW : v ∉ W := by
      intro hvW
      exact hv.2 (mem_union_right _ (mem_inter.mpr ⟨hv.1, hvW⟩))
    have hvS : v ∉ EF.S := fun hvS ↦ hv.2 (mem_union_left _ hvS)
    exact (EF.reserve_subset v (mem_sdiff.mpr
      ⟨lowVertices_mono_degree hFU (mem_sdiff.mpr ⟨hvlow.1, hvW⟩) hv.1, hvS⟩)).trans hFU
  · intro v hv z hz hvz
    rw [mem_sdiff] at hv hz
    have index : ∀ x, x ∈ lowVertices G U k → x ∉ S →
        x ∈ lowVertices G F k \ EF.S := by
      intro x hxlow hxS
      have hxW : x ∉ W := by
        intro hxW
        exact hxS (mem_union_right _ (mem_inter.mpr ⟨hxlow, hxW⟩))
      exact mem_sdiff.mpr
        ⟨lowVertices_mono_degree hFU
          (mem_sdiff.mpr ⟨(mem_lowVertices.mp hxlow).1, hxW⟩) hxlow,
          fun hxEF ↦ hxS (mem_union_left _ hxEF)⟩
    exact EF.reserve_pairwise v (index v hv.1 hv.2) z (index z hz.1 hz.2) hvz
  · have hdisj : Disjoint EF.S T := by
      rw [Finset.disjoint_left]
      intro x hxS hxT
      have hxF := (mem_lowVertices.mp (EF.S_subset_low hxS)).1
      exact (mem_sdiff.mp (by simpa [F, W] using hxF)).2 (mem_inter.mp hxT).2
    have hunion : S.sum (fun x ↦ k - degreeOn G U x) =
        EF.S.sum (fun x ↦ k - degreeOn G U x) +
          T.sum (fun x ↦ k - degreeOn G U x) := by
      simpa [S] using Finset.sum_union hdisj
    have hmono := deficitSum_mono_of_subset (G := G) hFU EF.S_subset_low
    have hmonoZ : ((EF.S.sum (fun x ↦ k - degreeOn G U x) : ℕ) : ℤ) ≤
        ((EF.S.sum (fun x ↦ k - degreeOn G F x) : ℕ) : ℤ) := by
      exact_mod_cast hmono
    have hshadow := lowDefect_shadow_le_two_mul C (by omega) hwU hwlow hpos
    have hdefeq := lowDefect_eq_sum_lowVertices_inter (G := G) (k := k)
      (U := U) (X := W) hWU
    have hshort : shortage k G F = shortage k G U -
        deletionPotential k G U W := by
      simpa [F, W] using shortage_sdiff k G (shadow_subset_ambient C hwU)
    rw [hunion]
    rw [Nat.cast_add]
    have hshadowT : ((T.sum (fun x ↦ k - degreeOn G U x) : ℕ) : ℤ) ≤
        2 * deletionPotential k G U W := by
      simpa [T, W, hdefeq] using hshadow
    have hEF := EF.deficit_le
    change ((EF.S.sum (fun x ↦ k - degreeOn G F x) : ℕ) : ℤ) ≤
      2 * shortage k G F at hEF
    omega
  · intro A hproper hlow hnew
    have hUA := (Finset.ssubset_iff_subset_ne.mp hproper).1
    have hFA : F ⊂ A := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨hFU.trans hUA, ?_⟩
      intro hFAeq
      have hAU : A ⊆ U := fun x hx ↦ hFU (by simpa [hFAeq] using hx)
      exact (Finset.ssubset_iff_subset_ne.mp hproper).2 (Subset.antisymm hUA hAU)
    have hlowF : lowVertices G A k ⊆ lowVertices G F k \ EF.S := by
      intro x hxA
      have hx := hlow hxA
      rw [mem_sdiff] at hx
      have hxW : x ∉ W := by
        intro hxW
        exact hx.2 (mem_union_right _ (mem_inter.mpr ⟨hx.1, hxW⟩))
      exact mem_sdiff.mpr
        ⟨lowVertices_mono_degree hFU
          (mem_sdiff.mpr ⟨(mem_lowVertices.mp hx.1).1, hxW⟩) hx.1,
          fun hxEF ↦ hx.2 (mem_union_left _ hxEF)⟩
    have hnewF : ∀ D ∈ CF.blocks, Anticomplete G (A \ F) D := by
      intro D hD
      simpa [CF, F, W] using extension_anticomplete_restricted_block
        C (by omega) hwU hwlow hUA hnew hD
    obtain ⟨U', R⟩ := EF.extension A hFA hlowF hnewF
    refine ⟨U', ?_⟩
    apply R.lift_shadow_complement C CF EF.reserve hWU rfl hUA
    · intro D
      simpa [CF, F, W] using
        (ProtectedFamily.mem_restrictShadowComplement_blocks
          C (by omega) hwU hwlow (D := D))
    · simpa [W] using (shadow_closed C (by omega) hwU hwlow).whole_blocks

/-- The two-stage bookkeeping in Case B.2.b: first delete the extension shadow, then use the
inductive certificate on the old shadow complement. -/
lemma ExtensionConclusion.lift_shadow_then_complement
    {U W F A WA U' : Finset V} {k : ℕ} {w : V}
    (C : ProtectedFamily G U k) (CF : ProtectedFamily G F k)
    (B BF : V → Finset V)
    (hWU : W ⊆ U) (hF : F = U \ W) (hUA : U ⊆ A)
    (hWAU : WA ⊆ U) (hwlowA : w ∈ lowVertices G A k)
    (hWAres : WA ⊆ B w)
    (hBFres : ∀ v ∈ lowVertices G (A \ WA) k, BF v ⊆ B v)
    (hshort : shortage k G (A \ WA) ≤ shortage k G A)
    (hWAanti : Anticomplete G WA (A \ U))
    (hlow : lowVertices G (A \ WA) k ⊆ lowVertices G A k)
    (hwholeW : C.WholeBlocks W) (hwholeWA : C.WholeBlocks WA)
    (hCF : ∀ D, D ∈ CF.blocks ↔ D ∈ C.blocks ∧ D ⊆ F)
    (hblockAntiWA : ∀ D ∈ C.blocks, Disjoint D WA → Anticomplete G D WA)
    (R : ExtensionConclusion CF BF (A \ WA) U') :
    ExtensionConclusion C B A U' := by
  have hFU : F ⊆ U := by rw [hF]; exact sdiff_subset
  have hnewSub : A \ U ⊆ (A \ WA) \ F := by
    intro x hx
    exact mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨(mem_sdiff.mp hx).1,
      fun hxWA ↦ (mem_sdiff.mp hx).2 (hWAU hxWA)⟩,
      fun hxF ↦ (mem_sdiff.mp hx).2 (hFU hxF)⟩
  have hdelSub : A \ U' ⊆ WA ∪ ((A \ WA) \ U') := by
    intro x hx
    by_cases hxWA : x ∈ WA
    · exact mem_union_left _ hxWA
    · exact mem_union_right _ (mem_sdiff.mpr
        ⟨mem_sdiff.mpr ⟨(mem_sdiff.mp hx).1, hxWA⟩, (mem_sdiff.mp hx).2⟩)
  have hblockW : ∀ {D}, D ∈ C.blocks → D ∉ CF.blocks → D ⊆ W := by
    intro D hDC hnot
    rcases hwholeW D hDC with hDW | hdisj
    · exact hDW
    · exfalso
      apply hnot
      apply (hCF D).2
      refine ⟨hDC, ?_⟩
      intro x hxD
      have hxUW : x ∈ U \ W := mem_sdiff.mpr
        ⟨C.subset_ambient D hDC hxD,
         fun hxW ↦ Finset.disjoint_left.mp hdisj hxD hxW⟩
      simpa [hF] using hxUW
  refine
    { minDegree := R.minDegree
      subset_extension := R.subset_extension.trans sdiff_subset
      shortage_le := R.shortage_le.trans hshort
      deleted_subset_reserves := ?_
      deleted_subset_old := ?_
      deleted_anticomplete_new := ?_
      blocks_whole := ?_
      retained_blocks_anticomplete := ?_ }
  · intro x hx
    rcases mem_union.mp (hdelSub hx) with hxWA | hxR
    · rw [reserveUnion, mem_biUnion]
      exact ⟨w, hwlowA, hWAres hxWA⟩
    · have hr := R.deleted_subset_reserves hxR
      rw [reserveUnion, mem_biUnion] at hr ⊢
      rcases hr with ⟨v, hv, hxBF⟩
      exact ⟨v, hlow hv, hBFres v hv hxBF⟩
  · intro x hx
    rcases mem_union.mp (hdelSub hx) with hxWA | hxR
    · exact hWAU hxWA
    · exact hFU (R.deleted_subset_old hxR)
  · intro hadj
    rcases hadj with ⟨x, hx, y, hy, hxy⟩
    rcases mem_union.mp (hdelSub hx) with hxWA | hxR
    · exact hWAanti ⟨x, hxWA, y, hy, hxy⟩
    · exact R.deleted_anticomplete_new ⟨x, hxR, y, hnewSub hy, hxy⟩
  · intro D hDC
    rcases hwholeWA D hDC with hDWA | hdisjWA
    · right
      rw [Finset.disjoint_left]
      intro x hxD hxU'
      exact (mem_sdiff.mp (R.subset_extension (hxU'))).2 (hDWA hxD)
    · by_cases hDCF : D ∈ CF.blocks
      · exact R.blocks_whole D hDCF
      · left
        have hDW := hblockW hDC hDCF
        intro x hxD
        have hxAF : x ∈ A \ WA := mem_sdiff.mpr
          ⟨hUA (C.subset_ambient D hDC hxD),
           fun hxWA ↦ Finset.disjoint_left.mp hdisjWA hxD hxWA⟩
        by_contra hxU'
        have hxF := R.deleted_subset_old (mem_sdiff.mpr ⟨hxAF, hxU'⟩)
        have hxUW : x ∈ U \ W := by simpa [hF] using hxF
        exact (mem_sdiff.mp hxUW).2 (hDW hxD)
  · intro D hDC hDU'
    have hdisjWA : Disjoint D WA := by
      rw [Finset.disjoint_left]
      intro x hxD hxWA
      exact (mem_sdiff.mp (R.subset_extension (hDU' hxD))).2 hxWA
    have hantiWA := hblockAntiWA D hDC hdisjWA
    have hantiR : Anticomplete G D ((A \ WA) \ U') := by
      by_cases hDCF : D ∈ CF.blocks
      · exact R.retained_blocks_anticomplete D hDCF hDU'
      · have hDW := hblockW hDC hDCF
        have hDnew : D ⊆ (A \ WA) \ F := by
          intro x hxD
          refine mem_sdiff.mpr ⟨R.subset_extension (hDU' hxD), ?_⟩
          intro hxF
          have hxUW : x ∈ U \ W := by simpa [hF] using hxF
          exact (mem_sdiff.mp hxUW).2 (hDW hxD)
        exact R.deleted_anticomplete_new.symm.mono hDnew Subset.rfl
    intro hadj
    rcases hadj with ⟨x, hxD, y, hy, hxy⟩
    rcases mem_union.mp (hdelSub hy) with hyWA | hyR
    · exact hantiWA ⟨x, hxD, y, hyWA, hxy⟩
    · exact hantiR ⟨x, hxD, y, hyR, hxy⟩

lemma ExtensionConclusion.map_reserve
    {U A U' : Finset V} {k : ℕ}
    {C : ProtectedFamily G U k} {B B' : V → Finset V}
    (R : ExtensionConclusion C B A U')
    (hBB : ∀ v ∈ lowVertices G A k, B v ⊆ B' v) :
    ExtensionConclusion C B' A U' := by
  refine
    { minDegree := R.minDegree
      subset_extension := R.subset_extension
      shortage_le := R.shortage_le
      deleted_subset_reserves := ?_
      deleted_subset_old := R.deleted_subset_old
      deleted_anticomplete_new := R.deleted_anticomplete_new
      blocks_whole := R.blocks_whole
      retained_blocks_anticomplete := R.retained_blocks_anticomplete }
  intro x hx
  have hr := R.deleted_subset_reserves hx
  rw [reserveUnion, mem_biUnion] at hr ⊢
  rcases hr with ⟨v, hv, hxB⟩
  exact ⟨v, hv, hBB v hv hxB⟩

private lemma extensionCertificate_zero_proper_shadow
    {U : Finset V} {k : ℕ} {w : V}
    (C : ProtectedFamily G U k) (hk : 2 ≤ k)
    (hwU : w ∈ U) (hwlow : degreeOn G U w ≤ k - 1)
    (hproperW : shadow C w ≠ U)
    (hzero : deletionPotential k G U (shadow C w) = 0)
    (EF : ExtensionCertificate G (U \ shadow C w) k
      (C.restrictShadowComplement (by omega) hwU hwlow)) :
    Nonempty (ExtensionCertificate G U k C) := by
  let W := shadow C w
  let F := U \ W
  let CF := C.restrictShadowComplement (by omega) hwU hwlow
  let B : V → Finset V := fun v ↦ if v = w then W else EF.reserve v
  have hWU : W ⊆ U := by simpa [W] using shadow_subset_ambient C hwU
  have hFU : F ⊆ U := by simp [F]
  have huniq := shadow_zero_unique_low C (by omega) hwU hwlow hzero
  have hlowFU : lowVertices G F k ⊆ lowVertices G U k := by
    intro x hx
    rw [mem_lowVertices] at hx ⊢
    have hold := low_degree_after_delete_shadow C (by omega) hwU hwlow
      (by simpa [F, W] using hx.1) (by simpa [F, W] using hx.2)
    exact ⟨hFU hx.1, hold.1⟩
  have index_of_ne : ∀ x, x ∈ lowVertices G U k → x ∉ EF.S → x ≠ w →
      x ∈ lowVertices G F k \ EF.S := by
    intro x hxlow hxS hxw
    have hxW : x ∉ W := by
      intro hxW
      exact hxw (huniq.1 x (by simpa [W] using hxW) (mem_lowVertices.mp hxlow).2)
    exact mem_sdiff.mpr
      ⟨lowVertices_mono_degree hFU
        (mem_sdiff.mpr ⟨(mem_lowVertices.mp hxlow).1, hxW⟩) hxlow, hxS⟩
  refine ⟨{
    S := EF.S
    S_subset_low := fun x hx ↦ hlowFU (EF.S_subset_low hx)
    veryLow_subset_S := ?_
    reserve := B
    reserve_subset := ?_
    reserve_pairwise := ?_
    deficit_le := ?_
    extension := ?_ }⟩
  · intro x hx
    rw [mem_veryLowVertices] at hx
    have hxne : x ≠ w := by
      intro hxw
      subst x
      rw [huniq.2] at hx
      omega
    apply EF.veryLow_subset_S
    have hxW : x ∉ W := by
      intro hxW
      exact hxne (huniq.1 x (by simpa [W] using hxW) (by omega))
    exact veryLowVertices_mono_degree hFU (mem_sdiff.mpr ⟨hx.1, hxW⟩)
      (mem_veryLowVertices.mpr hx)
  · intro v hv
    rw [mem_sdiff] at hv
    by_cases hvw : v = w
    · subst v
      simp [B, hWU]
    · have hidx := index_of_ne v hv.1 hv.2 hvw
      have hsub := (EF.reserve_subset v hidx).trans hFU
      simpa [B, hvw] using hsub
  · intro v hv z hz hvz
    rw [mem_sdiff] at hv hz
    by_cases hvw : v = w
    · by_cases hzw : z = w
      · exact (hvz (hvw.trans hzw.symm)).elim
      · have hzidx := index_of_ne z hz.1 hz.2 hzw
        simp only [B, hvw, hzw, if_pos, if_neg]
        rw [Finset.disjoint_left]
        intro x hxW hxB
        have hxF := EF.reserve_subset z hzidx hxB
        exact (mem_sdiff.mp (by simpa [F, W] using hxF)).2 hxW
    · by_cases hzw : z = w
      · have hvidx := index_of_ne v hv.1 hv.2 hvw
        simp only [B, hvw, hzw, if_pos, if_neg]
        rw [Finset.disjoint_left]
        intro x hxB hxW
        have hxF := EF.reserve_subset v hvidx hxB
        exact (mem_sdiff.mp (by simpa [F, W] using hxF)).2 hxW
      · simpa [B, hvw, hzw] using
          EF.reserve_pairwise v (index_of_ne v hv.1 hv.2 hvw)
            z (index_of_ne z hz.1 hz.2 hzw) hvz
  · have hmono := deficitSum_mono_of_subset (G := G) hFU EF.S_subset_low
    have hmonoZ : ((EF.S.sum (fun x ↦ k - degreeOn G U x) : ℕ) : ℤ) ≤
        ((EF.S.sum (fun x ↦ k - degreeOn G F x) : ℕ) : ℤ) := by
      exact_mod_cast hmono
    have hshort : shortage k G F = shortage k G U := by
      simpa [F, W] using shortage_delete_shadow_eq C hwU hzero
    have hEF := EF.deficit_le
    change ((EF.S.sum (fun x ↦ k - degreeOn G F x) : ℕ) : ℤ) ≤
      2 * shortage k G F at hEF
    omega
  · intro A hproper hlow hnew
    have hUA := (Finset.ssubset_iff_subset_ne.mp hproper).1
    by_cases hwA : w ∈ lowVertices G A k
    · let CA : ProtectedFamily G A k := C.extendAmbient hUA hnew
      let WA : Finset V := shadow CA w
      let AF : Finset V := A \ WA
      have hwlowA := (mem_lowVertices.mp hwA).2
      have hstable := shadow_stable_in_extension C (by omega) hUA hwU hwlowA hnew hzero
      have hWA_W : WA ⊆ W := by simpa [CA, WA, W] using hstable.1
      have hWAU : WA ⊆ U := hWA_W.trans hWU
      have hWAanti : Anticomplete G WA (A \ U) := by
        change ¬ AdjacentSets G WA (A \ U)
        simpa [CA, WA] using hstable.2
      have hFAF : F ⊂ AF := by
        apply Finset.ssubset_iff_subset_ne.mpr
        constructor
        · intro x hxF
          rw [mem_sdiff] at hxF
          exact mem_sdiff.mpr ⟨hUA hxF.1, fun hxWA ↦ hxF.2 (hWA_W hxWA)⟩
        · intro hEq
          have hAU : A ⊆ U := by
            intro x hxA
            by_cases hxWA : x ∈ WA
            · exact hWAU hxWA
            · have hxAF : x ∈ AF := mem_sdiff.mpr ⟨hxA, hxWA⟩
              exact hFU (by simpa [hEq] using hxAF)
          exact (Finset.ssubset_iff_subset_ne.mp hproper).2 (Subset.antisymm hUA hAU)
      have hlowAF : lowVertices G AF k ⊆ lowVertices G F k \ EF.S := by
        intro x hxAF
        have hr := low_degree_after_delete_shadow CA (by omega) (hUA hwU) hwlowA
          (by simpa [AF, WA] using (mem_lowVertices.mp hxAF).1)
          (by simpa [AF, WA] using (mem_lowVertices.mp hxAF).2)
        have hxlowA : x ∈ lowVertices G A k := mem_lowVertices.mpr
          ⟨(mem_sdiff.mp (mem_lowVertices.mp hxAF).1).1, hr.1⟩
        have hxUS := hlow hxlowA
        rw [mem_sdiff] at hxUS
        have hxnotW : x ∉ W := by
          intro hxW
          exact hr.2 (huniq.1 x (by simpa [W] using hxW)
            (mem_lowVertices.mp hxUS.1).2)
        exact mem_sdiff.mpr
          ⟨lowVertices_mono_degree hFU
            (mem_sdiff.mpr ⟨(mem_lowVertices.mp hxUS.1).1, hxnotW⟩) hxUS.1,
            hxUS.2⟩
      have hnewAF : ∀ D ∈ CF.blocks, Anticomplete G (AF \ F) D := by
        intro D hD
        have hantiA : Anticomplete G (A \ F) D := by
          simpa [CF, F, W] using extension_anticomplete_restricted_block
            C (by omega) hwU hwlow hUA hnew hD
        apply hantiA.mono ?_ Subset.rfl
        intro x hx
        exact mem_sdiff.mpr
          ⟨(mem_sdiff.mp ((mem_sdiff.mp hx).1)).1, (mem_sdiff.mp hx).2⟩
      obtain ⟨U', R⟩ := EF.extension AF hFAF hlowAF hnewAF
      refine ⟨U', ?_⟩
      have hshort : shortage k G AF ≤ shortage k G A := by
        have heq := shortage_delete_extension_shadow_eq C (by omega) hUA hwU
          hwlowA hnew hzero
        simpa [CA, WA, AF] using heq.le
      have hlowAFA : lowVertices G AF k ⊆ lowVertices G A k := by
        intro x hxAF
        have hr := low_degree_after_delete_shadow CA (by omega) (hUA hwU) hwlowA
          (by simpa [AF, WA] using (mem_lowVertices.mp hxAF).1)
          (by simpa [AF, WA] using (mem_lowVertices.mp hxAF).2)
        exact mem_lowVertices.mpr
          ⟨(mem_sdiff.mp (mem_lowVertices.mp hxAF).1).1, hr.1⟩
      have hwholeWA : C.WholeBlocks WA := by
        intro D hDC
        have hDCA : D ∈ CA.blocks := by change D ∈ C.blocks; exact hDC
        simpa [WA] using (shadow_closed CA (by omega) (hUA hwU) hwlowA).whole_blocks D hDCA
      apply R.lift_shadow_then_complement C CF B EF.reserve hWU rfl hUA hWAU hwA
      · intro x hxWA
        change x ∈ (if w = w then W else EF.reserve w)
        simp only [ite_true]
        exact hWA_W hxWA
      · intro v hvlow x hxB
        have hr := low_degree_after_delete_shadow CA (by omega) (hUA hwU) hwlowA
          (by simpa [AF, WA] using (mem_lowVertices.mp hvlow).1)
          (by simpa [AF, WA] using (mem_lowVertices.mp hvlow).2)
        simpa [B, hr.2] using hxB
      · exact hshort
      · exact hWAanti
      · exact hlowAFA
      · simpa [W] using (shadow_closed C (by omega) hwU hwlow).whole_blocks
      · exact hwholeWA
      · intro D
        simpa [CF, F, W] using
          (ProtectedFamily.mem_restrictShadowComplement_blocks
            C (by omega) hwU hwlow (D := D))
      · intro D hDC hdisj
        have hDCA : D ∈ CA.blocks := by change D ∈ C.blocks; exact hDC
        have hanti := shadow_anticomplete_block_of_disjoint CA (by omega)
          (hUA hwU) hwlowA hDCA (by simpa [WA] using hdisj)
        change ¬ AdjacentSets G D WA
        simpa [WA] using hanti
    · have hFA : F ⊂ A := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨hFU.trans hUA, ?_⟩
        intro hEq
        have hAU : A ⊆ U := fun x hx ↦ hFU (by simpa [hEq] using hx)
        exact (Finset.ssubset_iff_subset_ne.mp hproper).2 (Subset.antisymm hUA hAU)
      have hlowF : lowVertices G A k ⊆ lowVertices G F k \ EF.S := by
        intro x hxA
        have hxUS := hlow hxA
        rw [mem_sdiff] at hxUS
        have hxne : x ≠ w := fun hxw ↦ hwA (hxw ▸ hxA)
        exact index_of_ne x hxUS.1 hxUS.2 hxne
      have hnewF : ∀ D ∈ CF.blocks, Anticomplete G (A \ F) D := by
        intro D hD
        simpa [CF, F, W] using extension_anticomplete_restricted_block
          C (by omega) hwU hwlow hUA hnew hD
      obtain ⟨U', R⟩ := EF.extension A hFA hlowF hnewF
      have RB : ExtensionConclusion CF B A U' := R.map_reserve fun v hv ↦ by
        have hvne : v ≠ w := fun hvw ↦ hwA (hvw ▸ hv)
        simpa [B, hvne]
      refine ⟨U', ?_⟩
      apply RB.lift_shadow_complement C CF B hWU rfl hUA
      · intro D
        simpa [CF, F, W] using
          (ProtectedFamily.mem_restrictShadowComplement_blocks
            C (by omega) hwU hwlow (D := D))
      · simpa [W] using (shadow_closed C (by omega) hwU hwlow).whole_blocks

/-- Sauermann's extension lemma (Lemma 3.1), in fixed-ambient-set form. -/
theorem exists_extensionCertificate {U : Finset V} {k : ℕ}
    (C : ProtectedFamily G U k) (hk : 2 ≤ k)
    (hno : ∀ X : Finset V, X ⊆ U → ¬ HasMinDegreeOn G X k) :
    Nonempty (ExtensionCertificate G U k C) := by
  classical
  refine Finset.strongInduction (p := fun U : Finset V ↦
    ∀ C : ProtectedFamily G U k,
      (∀ X : Finset V, X ⊆ U → ¬ HasMinDegreeOn G X k) →
      Nonempty (ExtensionCertificate G U k C)) ?_ U C hno
  intro U ih C hno
  by_cases hU : U = ∅
  · subst U
    exact extensionCertificate_empty k C
  have hUne : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hU
  have hex : ∃ w ∈ U, degreeOn G U w < k := by
    by_contra hnot
    push_neg at hnot
    exact hno U Subset.rfl ⟨hUne, hnot⟩
  obtain ⟨w, hwU, hwlt⟩ := hex
  have hwlow : degreeOn G U w ≤ k - 1 := by omega
  let W := shadow C w
  have hWU : W ⊆ U := by simpa [W] using shadow_subset_ambient C hwU
  have hqnonneg : 0 ≤ deletionPotential k G U W := by
    simpa [W] using shadow_potential_nonneg C (by omega) hwU hwlow
  by_cases hfull : W = U
  · by_cases hzero : deletionPotential k G U W = 0
    · apply extensionCertificate_zero_full_shadow C hk hwU hwlow
      · simpa [W] using hfull
      · simpa [W] using hzero
    · have hpos : 0 < deletionPotential k G U W := by omega
      apply extensionCertificate_allLow C hk
      have hdef := lowDefect_shadow_le_two_mul C (by omega) hwU hwlow
        (by simpa [W] using hpos)
      have hpot : deletionPotential k G U U = shortage k G U := by
        have hi := edgeCount_sdiff_add_incidentCount G U U
        simp at hi
        unfold deletionPotential shortage
        rw [hi]
      simpa [W, hfull, hpot] using hdef
  · let F := U \ W
    have hFsub : F ⊂ U := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨by simp [F], ?_⟩
      intro hEq
      have hwF : w ∈ F := by simpa [hEq] using hwU
      exact (mem_sdiff.mp (by simpa [F] using hwF)).2
        (by simpa [W] using root_mem_shadow C w)
    let CF := C.restrictShadowComplement (by omega) hwU hwlow
    have hnoF : ∀ X : Finset V, X ⊆ F → ¬ HasMinDegreeOn G X k := by
      intro X hXF
      exact hno X (hXF.trans (by simp [F]))
    have hIH := ih F hFsub CF hnoF
    obtain ⟨EF⟩ := hIH
    by_cases hzero : deletionPotential k G U W = 0
    · apply extensionCertificate_zero_proper_shadow C hk hwU hwlow
        (by simpa [W] using hfull) (by simpa [W] using hzero)
      simpa [F, W, CF] using EF
    · have hpos : 0 < deletionPotential k G U W := by omega
      apply extensionCertificate_positive_proper_shadow C hk hwU hwlow
        (by simpa [W] using hfull) (by simpa [W] using hpos)
      simpa [F, W, CF] using EF

end Erdos814
