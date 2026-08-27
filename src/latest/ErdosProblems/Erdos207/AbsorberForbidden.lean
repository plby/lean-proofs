/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSReduction

/-!
# Forbidden configurations induced by an absorber bank

An outside packing must rule out not only short configurations contained in
itself, but every short configuration that can be completed using triangles
from the fixed absorber bank.  The family below is the exact finite family of
outside parts of such configurations.
-/

namespace Erdos207

open Finset

/-- Nonempty outside parts of all canonical short configurations after the
triangles belonging to the absorber bank have been removed. -/
def absorberForbiddenConfigurationsOn
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) : ForbiddenFamilyOn V :=
  (univ : Finset (TripleSystemOn V)).filter fun S ↦
    S.Nonempty ∧ ∃ E ∈ forbiddenConfigurationsOn q, E \ B = S

@[simp]
lemma mem_absorberForbiddenConfigurationsOn_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B S : TripleSystemOn V} :
    S ∈ absorberForbiddenConfigurationsOn q B ↔
      S.Nonempty ∧ ∃ E ∈ forbiddenConfigurationsOn q, E \ B = S := by
  simp [absorberForbiddenConfigurationsOn]

/-- The smaller KSSS family keeps only outside parts of *minimal* short
configurations which are themselves partial Steiner systems.  The packing
condition is automatic for every configuration contained in the final
Steiner packing.  Recording it here is essential at order four: two triples
sharing a pair span four vertices, but such a pair can never occur inside a
packing and therefore must not make an otherwise usable outside triangle
illegal merely because some unused bank triangle contains the same pair.
Minimality is what makes the localization property (A2) applicable. -/
noncomputable def absorberErdosForbiddenConfigurationsOn
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) : ForbiddenFamilyOn V := by
  classical
  exact ((Icc 4 q).biUnion fun r ↦
    ((univ : Finset (TripleSystemOn V)).filter fun E ↦
      IsErdosConfigOn r E ∧ IsPackingOn E).image fun E ↦ E \ B).erase ∅

@[simp]
lemma mem_absorberErdosForbiddenConfigurationsOn_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B S : TripleSystemOn V} :
    S ∈ absorberErdosForbiddenConfigurationsOn q B ↔
      S.Nonempty ∧ ∃ r, 4 ≤ r ∧ r ≤ q ∧
        ∃ E : TripleSystemOn V,
          IsErdosConfigOn r E ∧ IsPackingOn E ∧ E \ B = S := by
  classical
  simp only [absorberErdosForbiddenConfigurationsOn, mem_erase,
    mem_biUnion, mem_Icc, mem_image, mem_filter, mem_univ, true_and]
  rw [nonempty_iff_ne_empty]
  aesop

/-- If an outside triangle does not belong to the bank, membership in a
union with a bank subfamily forces membership in the outside family. -/
lemma mem_left_of_mem_union_bank
    {V : Type*} [DecidableEq V]
    {B P C : TripleSystemOn V} (hCB : C ⊆ B)
    {T : TripleOn V} (hT : T ∈ P ∪ C) (hTB : T ∉ B) : T ∈ P := by
  rcases mem_union.mp hT with hTP | hTC
  · exact hTP
  · exact (hTB (hCB hTC)).elim

/-- A bank triangle in a union of a bank-disjoint outside family and a bank
subfamily must belong to the latter. -/
lemma mem_right_of_mem_union_bank
    {V : Type*} [DecidableEq V]
    {B P C : TripleSystemOn V} (hPB : Disjoint P B)
    {T : TripleOn V} (hT : T ∈ P ∪ C) (hTB : T ∈ B) : T ∈ C := by
  rcases mem_union.mp hT with hTP | hTC
  · exact (Finset.disjoint_left.mp hPB hTP hTB).elim
  · exact hTC

/-- Avoiding every absorber-induced outside part makes every high-girth bank
switch compatible with the outside packing. -/
theorem girthGreater_union_bank_of_avoids_absorberForbidden
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B P C : TripleSystemOn V}
    (hPB : Disjoint P B)
    (hP : AvoidsForbidden P (absorberForbiddenConfigurationsOn q B))
    (hCB : C ⊆ B) (hC : GirthGreaterOn q C) :
    GirthGreaterOn q (P ∪ C) := by
  intro r hr4 hrq
  rintro ⟨E, hEPC, hEconfig⟩
  have hEforbidden : E ∈ forbiddenConfigurationsOn q :=
    mem_forbiddenConfigurationsOn_iff.mpr ⟨r, hr4, hrq, hEconfig⟩
  by_cases hout : (E \ B).Nonempty
  · have houtsideForbidden : E \ B ∈ absorberForbiddenConfigurationsOn q B :=
      mem_absorberForbiddenConfigurationsOn_iff.mpr
        ⟨hout, E, hEforbidden, rfl⟩
    apply hP (E \ B) houtsideForbidden
    intro T hT
    have hTE := (mem_sdiff.mp hT).1
    have hTnotB := (mem_sdiff.mp hT).2
    exact mem_left_of_mem_union_bank hCB (hEPC hTE) hTnotB
  · have hEB : E ⊆ B := by
      intro T hTE
      by_contra hTnotB
      exact hout ⟨T, mem_sdiff.mpr ⟨hTE, hTnotB⟩⟩
    apply hC r hr4 hrq
    refine ⟨E, ?_, hEconfig⟩
    intro T hTE
    exact mem_right_of_mem_union_bank hPB (hEPC hTE) (hEB hTE)

/-- It is enough to avoid outside parts of minimal configurations.  Every
failure of girth contains one by `exists_erdosConfig_of_not_girthGreater`. -/
theorem girthGreater_union_bank_of_avoids_absorberErdosForbidden
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B P C : TripleSystemOn V}
    (hPB : Disjoint P B)
    (hP : AvoidsForbidden P (absorberErdosForbiddenConfigurationsOn q B))
    (hCB : C ⊆ B) (hC : GirthGreaterOn q C)
    (hpacking : IsPackingOn (P ∪ C)) :
    GirthGreaterOn q (P ∪ C) := by
  by_contra hnot
  obtain ⟨r, hr4, hrq, E, hEPC, hE⟩ :=
    exists_erdosConfig_of_not_girthGreater hnot
  by_cases hout : (E \ B).Nonempty
  · have houtsideForbidden :
        E \ B ∈ absorberErdosForbiddenConfigurationsOn q B :=
      mem_absorberErdosForbiddenConfigurationsOn_iff.mpr
        ⟨hout, r, hr4, hrq, E, hE, hpacking.mono hEPC, rfl⟩
    apply hP (E \ B) houtsideForbidden
    intro T hT
    have hTE := (mem_sdiff.mp hT).1
    have hTnotB := (mem_sdiff.mp hT).2
    exact mem_left_of_mem_union_bank hCB (hEPC hTE) hTnotB
  · have hEB : E ⊆ B := by
      intro T hTE
      by_contra hTnotB
      exact hout ⟨T, mem_sdiff.mpr ⟨hTE, hTnotB⟩⟩
    apply hC r hr4 hrq
    refine ⟨E, ?_, hE.1⟩
    intro T hTE
    exact mem_right_of_mem_union_bank hPB (hEPC hTE) (hEB hTE)

/-- Two packings whose covered graphs are disjoint remain a packing after
union. -/
lemma IsPackingOn.union_of_coveredGraph_disjoint
    {V : Type*} [DecidableEq V]
    {P C : TripleSystemOn V}
    (hP : IsPackingOn P) (hC : IsPackingOn C)
    (hdisjoint : Disjoint (coveredGraph P) (coveredGraph C)) :
    IsPackingOn (P ∪ C) := by
  intro u v huv T hT huT hvT U hU huU hvU
  rcases mem_union.mp hT with hTP | hTC
  · rcases mem_union.mp hU with hUP | hUC
    · exact hP u v huv T hTP huT hvT U hUP huU hvU
    · exfalso
      exact SimpleGraph.disjoint_left.mp hdisjoint u v
        ⟨T, hTP, huT, hvT, huv⟩ ⟨U, hUC, huU, hvU, huv⟩
  · rcases mem_union.mp hU with hUP | hUC
    · exfalso
      exact SimpleGraph.disjoint_left.mp hdisjoint u v
        ⟨U, hUP, huU, hvU, huv⟩ ⟨T, hTC, huT, hvT, huv⟩
    · exact hC u v huv T hTC huT hvT U hUC huU hvU

/-- Every triangle decomposition is a packing. -/
lemma isPackingOn_of_isTriangleDecomposition
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {C : TripleSystemOn V} (hC : IsTriangleDecomposition G C) :
    IsPackingOn C := by
  intro u v huv T hT huT hvT U hU huU hvU
  exact (hC.2 u v (hC.1 T hT u huT v hvT huv)).unique
    ⟨hT, huT, hvT⟩ ⟨hU, huU, hvU⟩

/-- A convenient constructor for the compatibility condition in a KSSS
cover-down certificate. -/
theorem hasAbsorberCompatibleCoverDown_of_avoids
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B P : TripleSystemOn V} {L : SimpleGraph V}
    (hpacking : IsPackingOn P)
    (hedgeDisjoint : Disjoint (coveredGraph P) (H ⊔ L))
    (hcomplete : coveredGraph P ⊔ (H ⊔ L) =
      SimpleGraph.completeGraph V)
    (hsupport : GraphSupportedOn L (X : Set V))
    (hdiv : @TriangleDivisible V _ _ L (Classical.decRel L.Adj))
    (hPB : Disjoint P B)
    (havoid : AvoidsForbidden P (absorberForbiddenConfigurationsOn q B)) :
    HasAbsorberCompatibleCoverDown q H X B P L := by
  refine ⟨hpacking, hedgeDisjoint, hcomplete, hsupport, hdiv, ?_⟩
  intro C hCB hC
  exact girthGreater_union_bank_of_avoids_absorberForbidden
    hPB havoid hCB hC.2

/-- Minimal absorber-induced configurations give the same cover-down
constructor and are the formulation used by the random process. -/
theorem hasAbsorberCompatibleCoverDown_of_avoids_erdos
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B P : TripleSystemOn V} {L : SimpleGraph V}
    (hpacking : IsPackingOn P)
    (hedgeDisjoint : Disjoint (coveredGraph P) (H ⊔ L))
    (hcomplete : coveredGraph P ⊔ (H ⊔ L) =
      SimpleGraph.completeGraph V)
    (hsupport : GraphSupportedOn L (X : Set V))
    (hdiv : @TriangleDivisible V _ _ L (Classical.decRel L.Adj))
    (hPB : Disjoint P B)
    (havoid : AvoidsForbidden P
      (absorberErdosForbiddenConfigurationsOn q B)) :
    HasAbsorberCompatibleCoverDown q H X B P L := by
  refine ⟨hpacking, hedgeDisjoint, hcomplete, hsupport, hdiv, ?_⟩
  intro C hCB hC
  have hCpacking : IsPackingOn C :=
    isPackingOn_of_isTriangleDecomposition hC.1
  have hcoveredC : coveredGraph C = H ⊔ L := by
    apply le_antisymm
    · intro u v huv
      obtain ⟨T, hTC, huT, hvT, huvne⟩ := huv
      exact hC.1.1 T hTC u huT v hvT huvne
    · intro u v huv
      obtain ⟨T, hT, huT, hvT⟩ := (hC.1.2 u v huv).exists
      exact ⟨T, hT, huT, hvT, (H ⊔ L).ne_of_adj huv⟩
  have hdisjointC : Disjoint (coveredGraph P) (coveredGraph C) := by
    simpa only [hcoveredC] using hedgeDisjoint
  have hpackingUnion : IsPackingOn (P ∪ C) :=
    hpacking.union_of_coveredGraph_disjoint hCpacking hdisjointC
  exact girthGreater_union_bank_of_avoids_absorberErdosForbidden
    hPB havoid hCB hC.2 hpackingUnion

end Erdos207
