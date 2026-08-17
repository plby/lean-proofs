/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1024.LowerStructure
import Mathlib.Tactic.Ring

/-!
# A finite weighted independent-set inequality

This file proves a deliberately coarse, completely finite version of KMV
Lemma 5 for linear triangle-free triple systems.  The weight
`B * 4^B` is larger than KMV's optimized exponential weight, which makes
the matching calculation elementary while retaining the required order of
magnitude.
-/

open scoped BigOperators

namespace Erdos1024
namespace Lower

variable {V : Type*} [Fintype V] [DecidableEq V]

def independentSets (H : System V) : Finset (Finset V) :=
  Finset.univ.powerset.filter (Independent H)

@[simp] lemma mem_independentSets {H : System V} {I : Finset V} :
    I ∈ independentSets H ↔ Independent H I := by
  simp [independentSets]

lemma independent_mono {H : System V} {I J : Finset V}
    (hI : Independent H I) (hJI : J ⊆ I) : Independent H J := by
  intro e heH heJ
  exact hI heH (heJ.trans hJI)

/-- The number of link pairs through `v` fully contained in `I`. -/
def extensionCount (H : System V) (v : V) (I : Finset V) : ℕ :=
  coveredPairs (linkPairs H v (neighborhood H v)) (I ∩ neighborhood H v)

def truncatedExtension (H : System V) (B : ℕ) (v : V) (I : Finset V) : ℕ :=
  min (extensionCount H v I) B

def pivotWeight (H : System V) (B : ℕ) (v : V) (I : Finset V) : ℕ :=
  if v ∈ I then B * 4 ^ B else truncatedExtension H B v I

def omitImage (R J : Finset V) : Finset (Finset V) :=
  J.powerset.image fun S ↦ R ∪ S

def containImage (v : V) (R J : Finset V) : Finset (Finset V) :=
  J.powerset.image fun S ↦ insert v (R ∪ S)

def baseFiber (H : System V) (v : V) (R : Finset V) :
    Finset (Finset V) :=
  (independentSets H).filter fun I ↦ outsidePart H v I = R

lemma available_subset_neighborhood (H : System V) (v : V) (R : Finset V) :
    available H v R ⊆ neighborhood H v := by
  intro u hu
  exact (mem_available.mp hu).1

lemma outsidePart_subset (H : System V) (v : V) (I : Finset V) :
    outsidePart H v I ⊆ I := by
  exact Finset.sdiff_subset

lemma outsidePart_disjoint (H : System V) (v : V) (I : Finset V) :
    Disjoint (outsidePart H v I) (closedNeighborhood H v) := by
  exact Finset.sdiff_disjoint

lemma outsidePart_union_of_disjoint {H : System V} {v : V}
    {R S : Finset V} (hR : Disjoint R (closedNeighborhood H v))
    (hS : S ⊆ neighborhood H v) :
    outsidePart H v (R ∪ S) = R := by
  ext x
  constructor
  · intro hx
    have hxU := (Finset.mem_sdiff.mp hx).1
    have hxC := (Finset.mem_sdiff.mp hx).2
    rcases Finset.mem_union.mp hxU with hxR | hxS
    · exact hxR
    · exact False.elim (hxC (by
        simp only [closedNeighborhood, Finset.mem_insert]
        exact Or.inr (hS hxS)))
  · intro hxR
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hxR, ?_⟩
    intro hxC
    exact Finset.disjoint_left.mp hR hxR hxC

lemma outsidePart_insert_union_of_disjoint {H : System V} {v : V}
    {R S : Finset V} (hR : Disjoint R (closedNeighborhood H v))
    (hS : S ⊆ neighborhood H v) :
    outsidePart H v (insert v (R ∪ S)) = R := by
  ext x
  constructor
  · intro hx
    have hxI := (Finset.mem_sdiff.mp hx).1
    have hxC := (Finset.mem_sdiff.mp hx).2
    rcases Finset.mem_insert.mp hxI with rfl | hxU
    · exact False.elim (hxC (by simp [closedNeighborhood]))
    · rcases Finset.mem_union.mp hxU with hxR | hxS
      · exact hxR
      · exact False.elim (hxC (by
          simp only [closedNeighborhood, Finset.mem_insert]
          exact Or.inr (hS hxS)))
  · intro hxR
    refine Finset.mem_sdiff.mpr ⟨by simp [hxR], ?_⟩
    intro hxC
    exact Finset.disjoint_left.mp hR hxR hxC

lemma union_available_independent {H : System V}
    (hlin : Linear H) (htri : TriangleFree H)
    {v : V} {R S : Finset V} (hR : Independent H R)
    (hdisj : Disjoint R (closedNeighborhood H v))
    (hSJ : S ⊆ available H v R) :
    Independent H (R ∪ S) := by
  apply independent_mono (independent_union_available (H := H)
    hlin htri hR hdisj)
  exact Finset.union_subset_union Finset.Subset.rfl hSJ

lemma union_right_injective_of_disjoint {R J : Finset V}
    (hRJ : Disjoint R J) : Set.InjOn (fun S : Finset V ↦ R ∪ S) J.powerset := by
  intro S hS T hT hEq
  apply Finset.ext
  intro x
  have hSsub := Finset.mem_powerset.mp hS
  have hTsub := Finset.mem_powerset.mp hT
  have hxRnotS : x ∈ R → x ∉ S := fun hxR hxS ↦
    Finset.disjoint_left.mp hRJ hxR (hSsub hxS)
  have hxRnotT : x ∈ R → x ∉ T := fun hxR hxT ↦
    Finset.disjoint_left.mp hRJ hxR (hTsub hxT)
  by_cases hxR : x ∈ R
  · simp [hxR, hxRnotS hxR, hxRnotT hxR]
  · have hm := Finset.ext_iff.mp hEq x
    simpa [hxR] using hm

lemma insert_union_injective_of_disjoint {v : V} {R J : Finset V}
    (hvR : v ∉ R) (hvJ : v ∉ J) (hRJ : Disjoint R J) :
    Set.InjOn (fun S : Finset V ↦ insert v (R ∪ S)) J.powerset := by
  intro S hS T hT hEq
  apply union_right_injective_of_disjoint hRJ hS hT
  have hSsub := Finset.mem_powerset.mp hS
  have hTsub := Finset.mem_powerset.mp hT
  have hvS : v ∉ S := fun h ↦ hvJ (hSsub h)
  have hvT : v ∉ T := fun h ↦ hvJ (hTsub h)
  have hvRS : v ∉ R ∪ S := by simp [hvR, hvS]
  have hvRT : v ∉ R ∪ T := by simp [hvR, hvT]
  have hErase := congrArg (fun U : Finset V ↦ U.erase v) hEq
  simpa [hvRS, hvRT] using hErase

lemma extensionCount_union {H : System V} {v : V} {R S : Finset V}
    (hdisj : Disjoint R (closedNeighborhood H v))
    (hSJ : S ⊆ available H v R) :
    extensionCount H v (R ∪ S) =
      coveredPairs (linkPairs H v (available H v R)) S := by
  classical
  unfold extensionCount coveredPairs
  congr 1
  ext a
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨ha, haSub⟩
    obtain ⟨e, heH, hve, -, hea⟩ := mem_linkPairs.mp ha
    have haN : a ⊆ neighborhood H v := linkPairs_subset ha
    have haS : a ⊆ S := by
      intro x hxa
      have hxBoth := haSub hxa
      have hxUnion := (Finset.mem_inter.mp hxBoth).1
      rcases Finset.mem_union.mp hxUnion with hxR | hxS
      · exact False.elim (Finset.disjoint_left.mp hdisj hxR
          (by simp [closedNeighborhood, haN hxa]))
      · exact hxS
    have haJ : a ⊆ available H v R := haS.trans hSJ
    have heJ : e.erase v ⊆ available H v R := by simpa [hea] using haJ
    exact ⟨mem_linkPairs.mpr ⟨e, heH, hve, heJ, hea⟩, haS⟩
  · rintro ⟨ha, haS⟩
    obtain ⟨e, heH, hve, haJ, hea⟩ := mem_linkPairs.mp ha
    have haN : a ⊆ neighborhood H v :=
      (by simpa [hea] using haJ.trans (available_subset_neighborhood H v R))
    have heN : e.erase v ⊆ neighborhood H v := by simpa [hea] using haN
    exact ⟨mem_linkPairs.mpr ⟨e, heH, hve, heN, hea⟩,
      fun x hx ↦ Finset.mem_inter.mpr
        ⟨Finset.mem_union.mpr (Or.inr (haS hx)), haN hx⟩⟩

lemma omitImage_subset_baseFiber {H : System V}
    (hlin : Linear H) (htri : TriangleFree H)
    {v : V} {R : Finset V} (hR : Independent H R)
    (hdisj : Disjoint R (closedNeighborhood H v)) :
    omitImage R (available H v R) ⊆ baseFiber H v R := by
  classical
  intro I hI
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hI
  have hSJ := Finset.mem_powerset.mp hS
  simp only [baseFiber, Finset.mem_filter, mem_independentSets]
  exact ⟨union_available_independent hlin htri hR hdisj hSJ,
    outsidePart_union_of_disjoint hdisj
      (hSJ.trans (available_subset_neighborhood H v R))⟩

lemma baseFiber_subset_images {H : System V} {v : V} {R : Finset V} :
    baseFiber H v R ⊆
      omitImage R (available H v R) ∪
        containImage v R (available H v R) := by
  classical
  intro I hI
  have hIf := Finset.mem_filter.mp hI
  have hInd : Independent H I := mem_independentSets.mp hIf.1
  have hbase : outsidePart H v I = R := hIf.2
  let J := available H v R
  let S := I ∩ J
  have hSsub : S ⊆ J := Finset.inter_subset_right
  have hRsub : R ⊆ I := by
    rw [← hbase]
    exact outsidePart_subset H v I
  have hneighbor_available : ∀ x ∈ I, x ∈ neighborhood H v → x ∈ J := by
    intro x hxI hxN
    apply mem_available.mpr
    refine ⟨hxN, independent_mono hInd ?_⟩
    exact Finset.insert_subset hxI hRsub
  have hcover : I ⊆ insert v (R ∪ S) := by
    intro x hxI
    by_cases hxC : x ∈ closedNeighborhood H v
    · have hx : x = v ∨ x ∈ neighborhood H v := by
        simpa [closedNeighborhood] using hxC
      rcases hx with rfl | hxN
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _
          (Finset.mem_inter.mpr ⟨hxI, hneighbor_available x hxI hxN⟩))
    · have hxOut : x ∈ outsidePart H v I := Finset.mem_sdiff.mpr ⟨hxI, hxC⟩
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (hbase ▸ hxOut))
  have hback : insert v (R ∪ S) \ {v} ⊆ I := by
    intro x hx
    have hxIns := (Finset.mem_sdiff.mp hx).1
    have hxv := (Finset.mem_sdiff.mp hx).2
    rcases Finset.mem_insert.mp hxIns with rfl | hxU
    · exact False.elim (hxv (by simp))
    · rcases Finset.mem_union.mp hxU with hxR | hxS
      · exact hRsub hxR
      · exact (Finset.mem_inter.mp hxS).1
  by_cases hvI : v ∈ I
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨S, Finset.mem_powerset.mpr hSsub, ?_⟩
    apply Finset.Subset.antisymm
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxU
      · exact hvI
      · rcases Finset.mem_union.mp hxU with hxR | hxS
        · exact hRsub hxR
        · exact (Finset.mem_inter.mp hxS).1
    · exact hcover
  · apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨S, Finset.mem_powerset.mpr hSsub, ?_⟩
    apply Finset.Subset.antisymm
    · intro x hxU
      rcases Finset.mem_union.mp hxU with hxR | hxS
      · exact hRsub hxR
      · exact (Finset.mem_inter.mp hxS).1
    · intro x hxI
      have hxIns := hcover hxI
      exact (Finset.mem_insert.mp hxIns).resolve_left fun hxv ↦ hvI (hxv ▸ hxI)

lemma baseFiber_card_le {H : System V} {v : V} {R : Finset V} :
    (baseFiber H v R).card ≤ 2 * 2 ^ (available H v R).card := by
  classical
  let J := available H v R
  calc
    (baseFiber H v R).card ≤
        (omitImage R J ∪ containImage v R J).card :=
      Finset.card_le_card baseFiber_subset_images
    _ ≤ (omitImage R J).card + (containImage v R J).card :=
      Finset.card_union_le _ _
    _ ≤ J.powerset.card + J.powerset.card :=
      Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
    _ = 2 * 2 ^ J.card := by simp [Finset.card_powerset]; ring

lemma omitImage_card {R J : Finset V} (hRJ : Disjoint R J) :
    (omitImage R J).card = 2 ^ J.card := by
  classical
  unfold omitImage
  rw [Finset.card_image_of_injOn (union_right_injective_of_disjoint hRJ),
    Finset.card_powerset]

lemma pivotWeight_union {H : System V} {B : ℕ} {v : V} {R S : Finset V}
    (hdisj : Disjoint R (closedNeighborhood H v))
    (hSJ : S ⊆ available H v R) :
    pivotWeight H B v (R ∪ S) =
      min (coveredPairs (linkPairs H v (available H v R)) S) B := by
  have hvR : v ∉ R := vertex_not_mem_of_disjoint_closed hdisj
  have hvJ : v ∉ available H v R := by
    intro hv
    exact available_ne_self hv rfl
  have hvS : v ∉ S := fun hv ↦ hvJ (hSJ hv)
  rw [pivotWeight, if_neg (by simp [hvR, hvS]), truncatedExtension,
    extensionCount_union hdisj hSJ]

lemma sum_pivotWeight_omitImage {H : System V} {B : ℕ} {v : V}
    {R : Finset V} (hdisj : Disjoint R (closedNeighborhood H v)) :
    ∑ I ∈ omitImage R (available H v R), pivotWeight H B v I =
      ∑ S ∈ (available H v R).powerset,
        min (coveredPairs (linkPairs H v (available H v R)) S) B := by
  classical
  have hRJ : Disjoint R (available H v R) :=
    hdisj.mono_right (available_subset_neighborhood H v R |>.trans (by
      intro x hx
      simp [closedNeighborhood, hx]))
  unfold omitImage
  rw [Finset.sum_image (union_right_injective_of_disjoint hRJ)]
  apply Finset.sum_congr rfl
  intro S hS
  exact pivotWeight_union hdisj (Finset.mem_powerset.mp hS)

theorem baseFiber_weighted_large {H : System V}
    (h3 : ThreeUniform H) (hlin : Linear H) (htri : TriangleFree H)
    {B : ℕ} (hB : 0 < B) {v : V} {R : Finset V}
    (hR : Independent H R) (hdisj : Disjoint R (closedNeighborhood H v))
    (hlarge : B ≤ (linkPairs H v (available H v R)).card) :
    B * (baseFiber H v R).card ≤
      8 * ∑ I ∈ baseFiber H v R, pivotWeight H B v I := by
  classical
  let J := available H v R
  let M := linkPairs H v J
  have hmatch := four_mul_sum_min_coveredPairs (J := J) (M := M)
    hB hlarge (fun e he ↦ linkPairs_subset he)
    (fun e he ↦ linkPairs_card_two h3 he)
  have hOsub := omitImage_subset_baseFiber hlin htri hR hdisj
  have hsum :
      (∑ I ∈ omitImage R J, pivotWeight H B v I) ≤
        ∑ I ∈ baseFiber H v R, pivotWeight H B v I :=
    Finset.sum_le_sum_of_subset hOsub
  rw [sum_pivotWeight_omitImage hdisj] at hsum
  have hcard := baseFiber_card_le (H := H) (v := v) (R := R)
  calc
    B * (baseFiber H v R).card ≤ B * (2 * 2 ^ J.card) :=
      Nat.mul_le_mul_left B hcard
    _ = 2 * (B * 2 ^ J.card) := by ring
    _ ≤ 2 * (4 * ∑ S ∈ J.powerset, min (coveredPairs M S) B) :=
      Nat.mul_le_mul_left 2 hmatch
    _ = 8 * ∑ S ∈ J.powerset, min (coveredPairs M S) B := by ring
    _ ≤ 8 * ∑ I ∈ baseFiber H v R, pivotWeight H B v I :=
      Nat.mul_le_mul_left 8 hsum

def linkVertices (M : Finset (Finset V)) : Finset V :=
  M.biUnion id

def unusedVertices (J : Finset V) (M : Finset (Finset V)) : Finset V :=
  J \ linkVertices M

lemma linkVertices_subset {J : Finset V} {M : Finset (Finset V)}
    (hMJ : ∀ e ∈ M, e ⊆ J) : linkVertices M ⊆ J := by
  intro x hx
  obtain ⟨e, heM, hxe⟩ := Finset.mem_biUnion.mp hx
  exact hMJ e heM hxe

lemma card_linkVertices {H : System V} (h3 : ThreeUniform H)
    (hlin : Linear H) {v : V} {J : Finset V} :
    (linkVertices (linkPairs H v J)).card = 2 * (linkPairs H v J).card := by
  classical
  unfold linkVertices
  rw [Finset.card_biUnion (linkPairs_pairwiseDisjoint hlin)]
  calc
    ∑ e ∈ linkPairs H v J, e.card =
        ∑ _e ∈ linkPairs H v J, 2 := by
      apply Finset.sum_congr rfl
      intro e he
      rw [linkPairs_card_two h3 he]
    _ = 2 * (linkPairs H v J).card := by simp [Nat.mul_comm]

lemma card_available_eq_link_unused {H : System V}
    (h3 : ThreeUniform H) (hlin : Linear H) {v : V} {R : Finset V} :
    (available H v R).card =
      2 * (linkPairs H v (available H v R)).card +
        (unusedVertices (available H v R)
          (linkPairs H v (available H v R))).card := by
  let J := available H v R
  let M := linkPairs H v J
  let U := linkVertices M
  let L := unusedVertices J M
  have hUJ : U ⊆ J := linkVertices_subset fun e he ↦ linkPairs_subset he
  have hcard := Finset.card_sdiff_add_card_eq_card hUJ
  have hUcard := card_linkVertices h3 hlin (v := v) (J := J)
  change J.card = 2 * M.card + L.card
  change L.card + U.card = J.card at hcard
  change U.card = 2 * M.card at hUcard
  omega

lemma independent_insert_union_unused {H : System V}
    (h3 : ThreeUniform H) (hlin : Linear H) (htri : TriangleFree H)
    {v : V} {R S : Finset V} (hR : Independent H R)
    (hdisj : Disjoint R (closedNeighborhood H v))
    (hSL : S ⊆ unusedVertices (available H v R)
      (linkPairs H v (available H v R))) :
    Independent H (insert v (R ∪ S)) := by
  classical
  let J := available H v R
  let M := linkPairs H v J
  let U := linkVertices M
  let L := unusedVertices J M
  have hLJ : L ⊆ J := Finset.sdiff_subset
  have hSJ : S ⊆ J := hSL.trans hLJ
  have hbaseInd := union_available_independent hlin htri hR hdisj hSJ
  intro e heH heSub
  by_cases hve : v ∈ e
  · let a := e.erase v
    have haS : a ⊆ S := by
      intro x hxa
      have hxe : x ∈ e := Finset.mem_of_mem_erase hxa
      have hxv : x ≠ v := (Finset.mem_erase.mp hxa).1
      have hxIns := heSub hxe
      have hxU := (Finset.mem_insert.mp hxIns).resolve_left fun h ↦ hxv h
      rcases Finset.mem_union.mp hxU with hxR | hxS
      · have hxN : x ∈ neighborhood H v :=
          vertex_of_edge_neighborhood heH hve hxe hxv
        exact False.elim (Finset.disjoint_left.mp hdisj hxR
          (by simp [closedNeighborhood, hxN]))
      · exact hxS
    have haJ : a ⊆ J := haS.trans hSJ
    have haM : a ∈ M := mem_linkPairs.mpr ⟨e, heH, hve, haJ, rfl⟩
    have haU : a ⊆ U := by
      intro x hxa
      exact Finset.mem_biUnion.mpr ⟨a, haM, hxa⟩
    have haL : a ⊆ L := haS.trans hSL
    have hdisUL : Disjoint U L := by
      dsimp [L, unusedVertices]
      exact Finset.disjoint_sdiff
    have haEmpty : a = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hxa
      exact Finset.disjoint_left.mp hdisUL (haU hxa) (haL hxa)
    have hacard : a.card = 2 := linkPairs_card_two h3 haM
    simp [haEmpty] at hacard
  · apply hbaseInd heH
    intro x hxe
    have hx := heSub hxe
    exact (Finset.mem_insert.mp hx).resolve_left fun hxv ↦ hve (hxv ▸ hxe)

lemma containUnused_subset_baseFiber {H : System V}
    (h3 : ThreeUniform H) (hlin : Linear H) (htri : TriangleFree H)
    {v : V} {R : Finset V} (hR : Independent H R)
    (hdisj : Disjoint R (closedNeighborhood H v)) :
    containImage v R
      (unusedVertices (available H v R)
        (linkPairs H v (available H v R))) ⊆ baseFiber H v R := by
  classical
  intro I hI
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hI
  have hSL := Finset.mem_powerset.mp hS
  have hLN : unusedVertices (available H v R)
      (linkPairs H v (available H v R)) ⊆ neighborhood H v :=
    Finset.sdiff_subset.trans (available_subset_neighborhood H v R)
  simp only [baseFiber, Finset.mem_filter, mem_independentSets]
  exact ⟨independent_insert_union_unused h3 hlin htri hR hdisj hSL,
    outsidePart_insert_union_of_disjoint hdisj (hSL.trans hLN)⟩

lemma sum_pivotWeight_containUnused {H : System V} {B : ℕ} {v : V}
    {R : Finset V} (hdisj : Disjoint R (closedNeighborhood H v)) :
    ∑ I ∈ containImage v R
        (unusedVertices (available H v R)
          (linkPairs H v (available H v R))), pivotWeight H B v I =
      2 ^ (unusedVertices (available H v R)
        (linkPairs H v (available H v R))).card * (B * 4 ^ B) := by
  classical
  let J := available H v R
  let M := linkPairs H v J
  let L := unusedVertices J M
  have hvR : v ∉ R := vertex_not_mem_of_disjoint_closed hdisj
  have hvJ : v ∉ J := by
    intro hv
    exact available_ne_self hv rfl
  have hLJ : L ⊆ J := Finset.sdiff_subset
  have hvL : v ∉ L := fun hv ↦ hvJ (hLJ hv)
  have hRJ : Disjoint R J := hdisj.mono_right
    ((available_subset_neighborhood H v R).trans (by
      intro x hx
      simp [closedNeighborhood, hx]))
  have hRL : Disjoint R L := hRJ.mono_right hLJ
  unfold containImage
  rw [Finset.sum_image (insert_union_injective_of_disjoint hvR hvL hRL)]
  calc
    ∑ S ∈ L.powerset, pivotWeight H B v (insert v (R ∪ S)) =
        ∑ _S ∈ L.powerset, B * 4 ^ B := by
      apply Finset.sum_congr rfl
      intro S hS
      simp [pivotWeight]
    _ = 2 ^ L.card * (B * 4 ^ B) := by
      simp [Finset.card_powerset, Nat.mul_comm]

theorem baseFiber_weighted_small {H : System V}
    (h3 : ThreeUniform H) (hlin : Linear H) (htri : TriangleFree H)
    {B : ℕ} {v : V} {R : Finset V}
    (hR : Independent H R) (hdisj : Disjoint R (closedNeighborhood H v))
    (hsmall : (linkPairs H v (available H v R)).card < B) :
    B * (baseFiber H v R).card ≤
      8 * ∑ I ∈ baseFiber H v R, pivotWeight H B v I := by
  classical
  let J := available H v R
  let M := linkPairs H v J
  let L := unusedVertices J M
  have hCsub := containUnused_subset_baseFiber h3 hlin htri hR hdisj
  have hsum :
      2 ^ L.card * (B * 4 ^ B) ≤
        ∑ I ∈ baseFiber H v R, pivotWeight H B v I := by
    rw [← sum_pivotWeight_containUnused hdisj]
    exact Finset.sum_le_sum_of_subset hCsub
  have hcard := baseFiber_card_le (H := H) (v := v) (R := R)
  have hJcard := card_available_eq_link_unused h3 hlin (v := v) (R := R)
  change J.card = 2 * M.card + L.card at hJcard
  have hkB : M.card ≤ B := hsmall.le
  have hpows : 4 ^ M.card ≤ 4 ^ B := Nat.pow_le_pow_right (by omega) hkB
  have hpowJ : 2 ^ J.card = 4 ^ M.card * 2 ^ L.card := by
    rw [hJcard, pow_add, pow_mul]
    norm_num
  calc
    B * (baseFiber H v R).card ≤ B * (2 * 2 ^ J.card) :=
      Nat.mul_le_mul_left B hcard
    _ = 2 * B * 4 ^ M.card * 2 ^ L.card := by rw [hpowJ]; ring
    _ ≤ 2 * B * 4 ^ B * 2 ^ L.card := by
      gcongr
    _ ≤ 8 * (2 ^ L.card * (B * 4 ^ B)) := by
      have htwo : 2 * (B * 4 ^ B * 2 ^ L.card) ≤
          8 * (B * 4 ^ B * 2 ^ L.card) :=
        Nat.mul_le_mul_right _ (by omega)
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using htwo
    _ ≤ 8 * ∑ I ∈ baseFiber H v R, pivotWeight H B v I :=
      Nat.mul_le_mul_left 8 hsum

lemma independentSets_nonempty {H : System V} (h3 : ThreeUniform H) :
    (independentSets H).Nonempty := by
  refine ⟨∅, mem_independentSets.mpr ?_⟩
  intro e heH heSub
  have he0 : e = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun x hx ↦ by
    simpa using heSub hx
  have := h3 e heH
  simp [he0] at this

theorem pivot_weighted_sum_at_vertex {H : System V}
    (h3 : ThreeUniform H) (hlin : Linear H) (htri : TriangleFree H)
    {B : ℕ} (hB : 0 < B) (v : V) :
    B * (independentSets H).card ≤
      8 * ∑ I ∈ independentSets H, pivotWeight H B v I := by
  classical
  have hlocal : ∀ R : Finset V,
      B * (baseFiber H v R).card ≤
        8 * ∑ I ∈ baseFiber H v R, pivotWeight H B v I := by
    intro R
    by_cases hF : (baseFiber H v R).Nonempty
    · obtain ⟨I, hIF⟩ := hF
      have hIf := Finset.mem_filter.mp hIF
      have hInd : Independent H I := mem_independentSets.mp hIf.1
      have hbase : outsidePart H v I = R := hIf.2
      have hR : Independent H R := by
        rw [← hbase]
        exact independent_mono hInd (outsidePart_subset H v I)
      have hdisj : Disjoint R (closedNeighborhood H v) := by
        rw [← hbase]
        exact outsidePart_disjoint H v I
      by_cases hk : B ≤ (linkPairs H v (available H v R)).card
      · exact baseFiber_weighted_large h3 hlin htri hB hR hdisj hk
      · exact baseFiber_weighted_small h3 hlin htri hR hdisj
          (Nat.lt_of_not_ge hk)
    · have hEmpty : baseFiber H v R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
      simp [hEmpty]
  have hsum :
      ∑ R : Finset V, B * (baseFiber H v R).card ≤
        ∑ R : Finset V,
          8 * ∑ I ∈ baseFiber H v R, pivotWeight H B v I :=
    Finset.sum_le_sum fun R _ ↦ hlocal R
  have hcardFib :
      ∑ R : Finset V, (baseFiber H v R).card = (independentSets H).card := by
    symm
    apply Finset.card_eq_sum_card_fiberwise
    intro I hI
    exact Finset.mem_univ _
  have hsumFib :
      ∑ R : Finset V, ∑ I ∈ baseFiber H v R, pivotWeight H B v I =
        ∑ I ∈ independentSets H, pivotWeight H B v I := by
    exact Finset.sum_fiberwise (independentSets H) (outsidePart H v)
      (pivotWeight H B v)
  simpa only [← Finset.mul_sum, hcardFib, hsumFib] using hsum

/-- The KMV quantity `h_I(V)`, specialized to triple systems. -/
def totalTruncatedExtension (H : System V) (B : ℕ) (I : Finset V) : ℕ :=
  ∑ v ∈ Finset.univ \ I, truncatedExtension H B v I

lemma sum_pivotWeight_eq (H : System V) (B : ℕ) (I : Finset V) :
    ∑ v : V, pivotWeight H B v I =
      I.card * (B * 4 ^ B) + totalTruncatedExtension H B I := by
  classical
  unfold pivotWeight totalTruncatedExtension
  rw [Finset.sum_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr
    (Finset.subset_univ I), Finset.sum_const, nsmul_eq_mul]
  congr 1
  apply Finset.sum_congr
  · ext v
    simp
  · intro v hv
    rfl

/-- Coarse finite KMV weighted inequality. -/
theorem weighted_independent_set_inequality {H : System V}
    (h3 : ThreeUniform H) (hlin : Linear H) (htri : TriangleFree H)
    {B : ℕ} (hB : 0 < B) :
    B * Fintype.card V * (independentSets H).card ≤
      8 * ∑ I ∈ independentSets H,
        (I.card * (B * 4 ^ B) + totalTruncatedExtension H B I) := by
  classical
  have hv := Finset.sum_le_sum fun v (_hv : v ∈ (Finset.univ : Finset V)) ↦
    pivot_weighted_sum_at_vertex h3 hlin htri hB v
  have hcomm :
      ∑ v : V, ∑ I ∈ independentSets H, pivotWeight H B v I =
        ∑ I ∈ independentSets H, ∑ v : V, pivotWeight H B v I := by
    exact Finset.sum_comm
  simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hv
  rw [hcomm] at hv
  simp_rw [sum_pivotWeight_eq] at hv
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hv

/-- If all independent sets have size at most `A` and truncated extension
sum at most `U`, the common number of independent sets cancels from the
weighted inequality. -/
theorem weighted_numeric_consequence {H : System V}
    (h3 : ThreeUniform H) (hlin : Linear H) (htri : TriangleFree H)
    {B A U : ℕ} (hB : 0 < B)
    (hcard : ∀ I, Independent H I → I.card ≤ A)
    (hext : ∀ I, Independent H I → totalTruncatedExtension H B I ≤ U) :
    B * Fintype.card V ≤ 8 * (A * (B * 4 ^ B) + U) := by
  classical
  let F := independentSets H
  have hweighted := weighted_independent_set_inequality h3 hlin htri hB
  have hpoint : ∀ I ∈ F,
      I.card * (B * 4 ^ B) + totalTruncatedExtension H B I ≤
        A * (B * 4 ^ B) + U := by
    intro I hI
    exact Nat.add_le_add
      (Nat.mul_le_mul_right _ (hcard I (mem_independentSets.mp hI)))
      (hext I (mem_independentSets.mp hI))
  have hsum :
      (∑ I ∈ F, (I.card * (B * 4 ^ B) + totalTruncatedExtension H B I)) ≤
        F.card * (A * (B * 4 ^ B) + U) := by
    calc
      _ ≤ ∑ _I ∈ F, (A * (B * 4 ^ B) + U) :=
        Finset.sum_le_sum fun I hI ↦ hpoint I hI
      _ = F.card * (A * (B * 4 ^ B) + U) := by simp
  have hmul :
      (B * Fintype.card V) * F.card ≤
        (8 * (A * (B * 4 ^ B) + U)) * F.card := by
    calc
      (B * Fintype.card V) * F.card =
          B * Fintype.card V * (independentSets H).card := rfl
      _ ≤ 8 * ∑ I ∈ independentSets H,
          (I.card * (B * 4 ^ B) + totalTruncatedExtension H B I) := hweighted
      _ ≤ 8 * (F.card * (A * (B * 4 ^ B) + U)) :=
        Nat.mul_le_mul_left 8 hsum
      _ = (8 * (A * (B * 4 ^ B) + U)) * F.card := by ring
  apply Nat.le_of_mul_le_mul_right hmul
  exact (independentSets_nonempty h3).card_pos

end Lower
end Erdos1024

#print axioms Erdos1024.Lower.weighted_numeric_consequence
