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
import ErdosProblems.Erdos76.PentagonTwoBlobExceptionalCanonicalGeneral

/-!
# Finite certificates for Proposition 7.2(c)

Proposition 7.2(c) of Gruslys--Letzter concerns two nearly equal blobs whose
complete cross graph has two deleted edges with a common endpoint in the
smaller blob.  Only the size pairs `(3,3)`, `(3,4)`, `(4,4)`, and `(4,5)`
occur in the pentagon-extension argument.  This file records exact rational
certificates for those four pairs.

The small generic layer below packages three finite triangle families with a
common denominator.  Thus the finite proofs only have to check two natural
number identities: every edge score is at most the denominator, and every
internal edge score is exactly half the denominator.
-/

open Finset

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A sum of three constant-denominator family weights, with natural
numerators `n₁`, `n₂`, and `n₃`. -/
def threeFamilyWeight
    (F₁ F₂ F₃ : Finset (Finset α)) (D n₁ n₂ n₃ : ℕ) :
    Finset α → ℝ :=
  addTriangleWeight
    (scaleTriangleWeight n₁ (constantTriangleFamilyWeight F₁ D))
    (addTriangleWeight
      (scaleTriangleWeight n₂ (constantTriangleFamilyWeight F₂ D))
      (scaleTriangleWeight n₃ (constantTriangleFamilyWeight F₃ D)))

/-- The integer numerator of the edge load in `threeFamilyWeight`. -/
def threeFamilyEdgeScore
    (F₁ F₂ F₃ : Finset (Finset α)) (n₁ n₂ n₃ : ℕ)
    (e : Sym2 α) : ℕ :=
  n₁ * (F₁.filter fun t ↦ e ∈ t.sym2).card +
    n₂ * (F₂.filter fun t ↦ e ∈ t.sym2).card +
      n₃ * (F₃.filter fun t ↦ e ∈ t.sym2).card

private lemma fractionalEdgeLoad_threeFamilyWeight
    {G : SimpleGraph α} {F₁ F₂ F₃ : Finset (Finset α)}
    {D n₁ n₂ n₃ : ℕ}
    (hF₁ : ∀ t ∈ F₁, G.IsNClique 3 t)
    (hF₂ : ∀ t ∈ F₂, G.IsNClique 3 t)
    (hF₃ : ∀ t ∈ F₃, G.IsNClique 3 t)
    (e : Sym2 α) :
    fractionalEdgeLoad G (threeFamilyWeight F₁ F₂ F₃ D n₁ n₂ n₃) e =
      (threeFamilyEdgeScore F₁ F₂ F₃ n₁ n₂ n₃ e : ℝ) * (D : ℝ)⁻¹ := by
  rw [threeFamilyWeight,
    show addTriangleWeight _ _ = (fun t ↦ _ + _) by rfl,
    fractionalEdgeLoad_add,
    show addTriangleWeight _ _ = (fun t ↦ _ + _) by rfl,
    fractionalEdgeLoad_add]
  rw [show scaleTriangleWeight (n₁ : ℝ)
        (constantTriangleFamilyWeight F₁ D) =
      (fun t ↦ (n₁ : ℝ) * constantTriangleFamilyWeight F₁ D t) by rfl,
    show scaleTriangleWeight (n₂ : ℝ)
        (constantTriangleFamilyWeight F₂ D) =
      (fun t ↦ (n₂ : ℝ) * constantTriangleFamilyWeight F₂ D t) by rfl,
    show scaleTriangleWeight (n₃ : ℝ)
        (constantTriangleFamilyWeight F₃ D) =
      (fun t ↦ (n₃ : ℝ) * constantTriangleFamilyWeight F₃ D t) by rfl]
  rw [fractionalEdgeLoad_smul,
    fractionalEdgeLoad_constantTriangleFamilyWeight hF₁,
    fractionalEdgeLoad_smul,
    fractionalEdgeLoad_constantTriangleFamilyWeight hF₂,
    fractionalEdgeLoad_smul,
    fractionalEdgeLoad_constantTriangleFamilyWeight hF₃]
  unfold threeFamilyEdgeScore
  push_cast
  ring

private lemma fractionalEdgeLoad_threeFamilyWeight_of_incident
    {G : SimpleGraph α} {F₁ F₂ F₃ : Finset (Finset α)}
    {D n₁ n₂ n₃ : ℕ} {e : Sym2 α}
    (hF₁ : ∀ t ∈ F₁, e ∈ t.sym2 → G.IsNClique 3 t)
    (hF₂ : ∀ t ∈ F₂, e ∈ t.sym2 → G.IsNClique 3 t)
    (hF₃ : ∀ t ∈ F₃, e ∈ t.sym2 → G.IsNClique 3 t) :
    fractionalEdgeLoad G (threeFamilyWeight F₁ F₂ F₃ D n₁ n₂ n₃) e =
      (threeFamilyEdgeScore F₁ F₂ F₃ n₁ n₂ n₃ e : ℝ) * (D : ℝ)⁻¹ := by
  rw [threeFamilyWeight,
    show addTriangleWeight _ _ = (fun t ↦ _ + _) by rfl,
    fractionalEdgeLoad_add,
    show addTriangleWeight _ _ = (fun t ↦ _ + _) by rfl,
    fractionalEdgeLoad_add]
  rw [show scaleTriangleWeight (n₁ : ℝ)
        (constantTriangleFamilyWeight F₁ D) =
      (fun t ↦ (n₁ : ℝ) * constantTriangleFamilyWeight F₁ D t) by rfl,
    show scaleTriangleWeight (n₂ : ℝ)
        (constantTriangleFamilyWeight F₂ D) =
      (fun t ↦ (n₂ : ℝ) * constantTriangleFamilyWeight F₂ D t) by rfl,
    show scaleTriangleWeight (n₃ : ℝ)
        (constantTriangleFamilyWeight F₃ D) =
      (fun t ↦ (n₃ : ℝ) * constantTriangleFamilyWeight F₃ D t) by rfl]
  rw [fractionalEdgeLoad_smul,
    fractionalEdgeLoad_constantTriangleFamilyWeight_of_incident hF₁,
    fractionalEdgeLoad_smul,
    fractionalEdgeLoad_constantTriangleFamilyWeight_of_incident hF₂,
    fractionalEdgeLoad_smul,
    fractionalEdgeLoad_constantTriangleFamilyWeight_of_incident hF₃]
  unfold threeFamilyEdgeScore
  push_cast
  ring

private lemma threeFamilyWeight_nonneg
    (F₁ F₂ F₃ : Finset (Finset α)) (D n₁ n₂ n₃ : ℕ)
    (t : Finset α) :
    0 ≤ threeFamilyWeight F₁ F₂ F₃ D n₁ n₂ n₃ t := by
  simp only [threeFamilyWeight, addTriangleWeight, scaleTriangleWeight,
    constantTriangleFamilyWeight]
  split_ifs <;> positivity

/-- A finite three-family score certificate gives a fractional internal
cross packing.  The second conclusion records the exact half-load on every
actual internal edge and is what makes the total size calculation insensitive
to the colours inside the two blobs. -/
theorem threeFamilyCertificate
    {G : SimpleGraph α} {s : Set α}
    {F₁ F₂ F₃ : Finset (Finset α)} {D n₁ n₂ n₃ : ℕ}
    (hD : 0 < D)
    (hF₁ : F₁ ⊆ internalCrossTriangles G s)
    (hF₂ : F₂ ⊆ internalCrossTriangles G s)
    (hF₃ : F₃ ⊆ internalCrossTriangles G s)
    (hscore : ∀ e, ¬ e.IsDiag →
      threeFamilyEdgeScore F₁ F₂ F₃ n₁ n₂ n₃ e ≤ D)
    (hinternal : ∀ e, ¬ e.IsDiag → SameSide s e →
      2 * threeFamilyEdgeScore F₁ F₂ F₃ n₁ n₂ n₃ e = D) :
    IsFractionalInternalCrossPacking G s
        (threeFamilyWeight F₁ F₂ F₃ D n₁ n₂ n₃) ∧
      ∀ e ∈ internalEdgeFinset G s,
        fractionalEdgeLoad G
          (threeFamilyWeight F₁ F₂ F₃ D n₁ n₂ n₃) e = 1 / 2 := by
  classical
  have htri₁ : ∀ t ∈ F₁, G.IsNClique 3 t := by
    intro t ht
    exact (mem_internalCrossTriangles.mp (hF₁ ht)).1
  have htri₂ : ∀ t ∈ F₂, G.IsNClique 3 t := by
    intro t ht
    exact (mem_internalCrossTriangles.mp (hF₂ ht)).1
  have htri₃ : ∀ t ∈ F₃, G.IsNClique 3 t := by
    intro t ht
    exact (mem_internalCrossTriangles.mp (hF₃ ht)).1
  have hpacking : IsFractionalPacking G
      (threeFamilyWeight F₁ F₂ F₃ D n₁ n₂ n₃) := by
    constructor
    · intro t _ht
      exact threeFamilyWeight_nonneg F₁ F₂ F₃ D n₁ n₂ n₃ t
    · intro e he
      rw [fractionalEdgeLoad_threeFamilyWeight htri₁ htri₂ htri₃]
      have hs := hscore e (G.not_isDiag_of_mem_edgeFinset he)
      have hDR : (0 : ℝ) < D := by exact_mod_cast hD
      rw [← div_eq_mul_inv]
      exact (div_le_one hDR).mpr (by exact_mod_cast hs)
  have hcross : IsFractionalInternalCrossPacking G s
      (threeFamilyWeight F₁ F₂ F₃ D n₁ n₂ n₃) := by
    refine ⟨hpacking, ?_⟩
    intro t ht
    have ht₁ : t ∉ F₁ := fun h ↦ ht (hF₁ h)
    have ht₂ : t ∉ F₂ := fun h ↦ ht (hF₂ h)
    have ht₃ : t ∉ F₃ := fun h ↦ ht (hF₃ h)
    simp [threeFamilyWeight, addTriangleWeight, scaleTriangleWeight,
      constantTriangleFamilyWeight, ht₁, ht₂, ht₃]
  refine ⟨hcross, ?_⟩
  intro e he
  rw [fractionalEdgeLoad_threeFamilyWeight htri₁ htri₂ htri₃]
  have heData := mem_filter.mp he
  have hs := hinternal e (G.not_isDiag_of_mem_edgeFinset heData.1) heData.2
  have hsR :
      2 * (threeFamilyEdgeScore F₁ F₂ F₃ n₁ n₂ n₃ e : ℝ) = D := by
    exact_mod_cast hs
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  rw [← div_eq_mul_inv]
  field_simp
  linarith

private lemma topDeleteEdges_isNClique_of_card_avoids
    {β : Type*} [Fintype β] [DecidableEq β]
    (M : Finset (Sym2 β)) (t : Finset β) (hcard : t.card = 3)
    (havoid : ∀ e ∈ M, ¬ e.toFinset ⊆ t) :
    ((⊤ : SimpleGraph β).deleteEdges (M : Set (Sym2 β))).IsNClique 3 t := by
  rw [SimpleGraph.isNClique_iff]
  refine ⟨?_, hcard⟩
  intro x hx y hy hxy
  rw [SimpleGraph.deleteEdges_adj]
  refine ⟨by simpa using hxy, ?_⟩
  intro hxyMissing
  exact havoid s(x, y) hxyMissing (by
    intro z hz
    simp only [Sym2.toFinset_mk_eq, mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy)

private lemma family_subset_internalCross_of_twoOne
    {G : SimpleGraph α} {A B : Finset α} {F : Finset (Finset α)}
    (hAB : Disjoint A B)
    (htri : ∀ t ∈ F, G.IsNClique 3 t)
    (htwo : F ⊆ twoOneTriangleFamily A B ∪ twoOneTriangleFamily B A) :
    F ⊆ internalCrossTriangles G (A : Set α) := by
  intro t ht
  rcases mem_union.mp (htwo ht) with htAB | htBA
  · exact twoOneTriangleFamily_mem_internalCrossTriangles_of_sides
      (s := (A : Set α)) (fun _x hx ↦ hx)
      (fun _z hzB hzA ↦ Finset.disjoint_left.mp hAB hzA hzB)
      htAB (htri t ht)
  · have hcomp := twoOneTriangleFamily_mem_internalCrossTriangles_of_sides
      (s := (A : Set α)ᶜ)
      (fun _x hxB ↦ by
        simp only [Set.mem_compl_iff, Finset.mem_coe]
        exact fun hxA ↦ Finset.disjoint_left.mp hAB hxA hxB)
      (fun _z hzA ↦ by simp [hzA]) htBA (htri t ht)
    simpa only [internalCrossTriangles_set_compl] using hcomp

private lemma le_of_sameCross_of_internal_complete
    {G H : SimpleGraph α} {s : Set α}
    (hinternal : ∀ x y, x ≠ y → (x ∈ s ↔ y ∈ s) → H.Adj x y)
    (hcross : SameCrossAdj G H s) :
    G ≤ H := by
  intro x y hGxy
  by_cases hsame : x ∈ s ↔ y ∈ s
  · exact hinternal x y hGxy.ne hsame
  · exact (hcross x y hsame).mp hGxy

private lemma internalCrossTriangle_isNClique_of_internalEdge
    {G H : SimpleGraph α} {s : Set α} {t : Finset α} {e : Sym2 α}
    (hGH : G ≤ H) (hcross : SameCrossAdj G H s)
    (htH : t ∈ internalCrossTriangles H s)
    (he : e ∈ internalEdgeFinset G s) (het : e ∈ t.sym2) :
    G.IsNClique 3 t := by
  classical
  rcases mem_internalCrossTriangles.mp htH with ⟨htHClique, htOne⟩
  rw [SimpleGraph.isNClique_iff]
  refine ⟨?_, htHClique.card_eq⟩
  intro x hx y hy hxy
  by_cases hsame : x ∈ s ↔ y ∈ s
  · have hHxy : H.Adj x y := htHClique.isClique hx hy hxy
    have hqInternal : s(x, y) ∈ internalEdgeFinset H s :=
      mem_filter.mpr ⟨by
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hHxy,
        by simpa only [sameSide_mk] using hsame⟩
    have hq : s(x, y) ∈
        (internalEdgeFinset H s).filter (fun q ↦ q ∈ t.sym2) :=
      mem_filter.mpr ⟨hqInternal, by
        simpa only [Finset.mk_mem_sym2_iff, Finset.mem_coe] using And.intro hx hy⟩
    rcases mem_filter.mp he with ⟨heGEdge, heSame⟩
    have heHInternal : e ∈ internalEdgeFinset H s :=
      mem_filter.mpr ⟨SimpleGraph.edgeFinset_mono hGH heGEdge, heSame⟩
    have he' : e ∈
        (internalEdgeFinset H s).filter (fun q ↦ q ∈ t.sym2) :=
      mem_filter.mpr ⟨heHInternal, het⟩
    have hqe : s(x, y) = e :=
      (card_le_one.mp (by omega)) s(x, y) hq e he'
    have heGSet := SimpleGraph.mem_edgeFinset.mp heGEdge
    rw [← hqe] at heGSet
    simpa only [SimpleGraph.mem_edgeSet] using heGSet
  · exact (hcross x y hsame).mpr (htHClique.isClique hx hy hxy)

/-- The common arbitrary-internal-colour transport theorem for all four
canonical Proposition 7.2(c) certificates. -/
theorem threeFamilyCertificate_arbitraryInternal
    {G H : SimpleGraph α} {s : Set α}
    {F₁ F₂ F₃ : Finset (Finset α)} {D n₁ n₂ n₃ : ℕ}
    (hD : 0 < D)
    (hHinternal : ∀ x y, x ≠ y → (x ∈ s ↔ y ∈ s) → H.Adj x y)
    (hF₁ : F₁ ⊆ internalCrossTriangles H s)
    (hF₂ : F₂ ⊆ internalCrossTriangles H s)
    (hF₃ : F₃ ⊆ internalCrossTriangles H s)
    (hscore : ∀ e, ¬ e.IsDiag →
      threeFamilyEdgeScore F₁ F₂ F₃ n₁ n₂ n₃ e ≤ D)
    (hinternal : ∀ e, ¬ e.IsDiag → SameSide s e →
      2 * threeFamilyEdgeScore F₁ F₂ F₃ n₁ n₂ n₃ e = D)
    (hcross : SameCrossAdj G H s) :
    IsFractionalInternalCrossPacking G s
        (zeroExtendTriangleWeight G
          (threeFamilyWeight F₁ F₂ F₃ D n₁ n₂ n₃)) ∧
      fractionalSize G
          (zeroExtendTriangleWeight G
            (threeFamilyWeight F₁ F₂ F₃ D n₁ n₂ n₃)) =
        ((internalEdgeFinset G s).card : ℝ) / 2 := by
  classical
  have hGH : G ≤ H := le_of_sameCross_of_internal_complete hHinternal hcross
  have hcanonical := threeFamilyCertificate hD hF₁ hF₂ hF₃ hscore hinternal
  have hpacking : IsFractionalInternalCrossPacking G s
      (zeroExtendTriangleWeight G
        (threeFamilyWeight F₁ F₂ F₃ D n₁ n₂ n₃)) := by
    refine ⟨hcanonical.1.1.restrictToSubgraph hGH, ?_⟩
    intro t htNot
    by_cases htG : t ∈ G.cliqueFinset 3
    · rw [zeroExtendTriangleWeight_of_mem htG]
      apply hcanonical.1.2 t
      intro htH
      exact htNot (mem_internalCrossTriangles_of_le_of_isNClique hGH htH
        (SimpleGraph.mem_cliqueFinset_iff.mp htG))
    · exact zeroExtendTriangleWeight_of_not_mem htG
  refine ⟨hpacking, ?_⟩
  calc
    fractionalSize G
        (zeroExtendTriangleWeight G
          (threeFamilyWeight F₁ F₂ F₃ D n₁ n₂ n₃)) =
        ∑ e ∈ internalEdgeFinset G s,
          fractionalEdgeLoad G
            (zeroExtendTriangleWeight G
              (threeFamilyWeight F₁ F₂ F₃ D n₁ n₂ n₃)) e := by
      exact (sum_internalEdge_fractionalEdgeLoad_eq_fractionalSize hpacking).symm
    _ = ∑ _e ∈ internalEdgeFinset G s, (1 / 2 : ℝ) := by
      apply sum_congr rfl
      intro e he
      rw [fractionalEdgeLoad_zeroExtend (G := G) le_rfl,
        fractionalEdgeLoad_threeFamilyWeight_of_incident
          (fun t ht het ↦ internalCrossTriangle_isNClique_of_internalEdge
            hGH hcross (hF₁ ht) he het)
          (fun t ht het ↦ internalCrossTriangle_isNClique_of_internalEdge
            hGH hcross (hF₂ ht) he het)
          (fun t ht het ↦ internalCrossTriangle_isNClique_of_internalEdge
            hGH hcross (hF₃ ht) he het)]
      rcases mem_filter.mp he with ⟨heG, heSame⟩
      have hs := hinternal e (G.not_isDiag_of_mem_edgeFinset heG) heSame
      have hsR :
          2 * (threeFamilyEdgeScore F₁ F₂ F₃ n₁ n₂ n₃ e : ℝ) = D := by
        exact_mod_cast hs
      have hDR : (0 : ℝ) < D := by exact_mod_cast hD
      rw [← div_eq_mul_inv]
      field_simp
      linarith
    _ = ((internalEdgeFinset G s).card : ℝ) / 2 := by
      simp [div_eq_mul_inv]

/-! ## The `(3,3)` certificate -/

abbrev Proposition72c33Vertex := Fin 6

def proposition72c33A : Finset Proposition72c33Vertex := {0, 1, 2}

def proposition72c33B : Finset Proposition72c33Vertex := {3, 4, 5}

def proposition72c33Missing : Finset (Sym2 Proposition72c33Vertex) :=
  {s(0, 3), s(0, 4)}

def proposition72c33Graph : SimpleGraph Proposition72c33Vertex :=
  (⊤ : SimpleGraph Proposition72c33Vertex).deleteEdges
    (proposition72c33Missing : Set (Sym2 Proposition72c33Vertex))

def proposition72c33HalfFamily : Finset (Finset Proposition72c33Vertex) :=
  {{0, 1, 5}, {0, 2, 5}}

def proposition72c33QuarterFamily : Finset (Finset Proposition72c33Vertex) :=
  {{1, 2, 3}, {1, 2, 4}, {1, 3, 4}, {1, 3, 5},
    {1, 4, 5}, {2, 3, 4}, {2, 3, 5}, {2, 4, 5}}

def proposition72c33Weight : Finset Proposition72c33Vertex → ℝ :=
  threeFamilyWeight proposition72c33HalfFamily proposition72c33QuarterFamily ∅
    4 2 1 0

private def Proposition72c33FamilyData
    (t : Finset Proposition72c33Vertex) : Prop :=
  t.card = 3 ∧
    (∀ e ∈ proposition72c33Missing, ¬ e.toFinset ⊆ t) ∧
      t ∈ twoOneTriangleFamily proposition72c33A proposition72c33B ∪
        twoOneTriangleFamily proposition72c33B proposition72c33A

private lemma proposition72c33HalfFamily_data :
    ∀ t ∈ proposition72c33HalfFamily, Proposition72c33FamilyData t := by
  intro t ht
  simp only [proposition72c33HalfFamily, mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl
  all_goals unfold Proposition72c33FamilyData
  all_goals decide

private lemma proposition72c33QuarterFamily_data :
    ∀ t ∈ proposition72c33QuarterFamily, Proposition72c33FamilyData t := by
  intro t ht
  simp only [proposition72c33QuarterFamily, mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold Proposition72c33FamilyData
  all_goals decide

private lemma proposition72c33Families_internalCross :
    proposition72c33HalfFamily ⊆
        internalCrossTriangles proposition72c33Graph
          (proposition72c33A : Set Proposition72c33Vertex) ∧
      proposition72c33QuarterFamily ⊆
        internalCrossTriangles proposition72c33Graph
          (proposition72c33A : Set Proposition72c33Vertex) := by
  have hAB : Disjoint proposition72c33A proposition72c33B := by decide
  constructor
  · apply family_subset_internalCross_of_twoOne hAB
    · intro t ht
      exact topDeleteEdges_isNClique_of_card_avoids proposition72c33Missing t
        (proposition72c33HalfFamily_data t ht).1
        (proposition72c33HalfFamily_data t ht).2.1
    · intro t ht
      exact (proposition72c33HalfFamily_data t ht).2.2
  · apply family_subset_internalCross_of_twoOne hAB
    · intro t ht
      exact topDeleteEdges_isNClique_of_card_avoids proposition72c33Missing t
        (proposition72c33QuarterFamily_data t ht).1
        (proposition72c33QuarterFamily_data t ht).2.1
    · intro t ht
      exact (proposition72c33QuarterFamily_data t ht).2.2

private lemma proposition72c33Score_le
    (e : Sym2 Proposition72c33Vertex) (hne : ¬ e.IsDiag) :
    threeFamilyEdgeScore proposition72c33HalfFamily
      proposition72c33QuarterFamily ∅ 2 1 0 e ≤ 4 := by
  induction e using Sym2.inductionOn with
  | hf x y =>
      have hxy : x ≠ y := by
        simpa only [Sym2.mk_isDiag_iff] using hne
      fin_cases x <;> fin_cases y
      all_goals simp at hxy
      all_goals decide

private lemma proposition72c33Score_internal
    (e : Sym2 Proposition72c33Vertex) (hne : ¬ e.IsDiag)
    (hsame : SameSide (proposition72c33A : Set Proposition72c33Vertex) e) :
    2 * threeFamilyEdgeScore proposition72c33HalfFamily
      proposition72c33QuarterFamily ∅ 2 1 0 e = 4 := by
  induction e using Sym2.inductionOn with
  | hf x y =>
      have hxy : x ≠ y := by
        simpa only [Sym2.mk_isDiag_iff] using hne
      simp only [sameSide_mk] at hsame
      fin_cases x <;> fin_cases y
      all_goals simp [proposition72c33A] at hxy hsame
      all_goals decide

theorem proposition72c33CanonicalPacking :
    IsFractionalInternalCrossPacking proposition72c33Graph
        (proposition72c33A : Set Proposition72c33Vertex)
        proposition72c33Weight ∧
      ∀ e ∈ internalEdgeFinset proposition72c33Graph
        (proposition72c33A : Set Proposition72c33Vertex),
        fractionalEdgeLoad proposition72c33Graph proposition72c33Weight e = 1 / 2 := by
  simpa only [proposition72c33Weight] using
    (threeFamilyCertificate (G := proposition72c33Graph)
      (s := (proposition72c33A : Set Proposition72c33Vertex))
      (F₁ := proposition72c33HalfFamily)
      (F₂ := proposition72c33QuarterFamily) (F₃ := ∅)
      (D := 4) (n₁ := 2) (n₂ := 1) (n₃ := 0)
      (by norm_num)
      proposition72c33Families_internalCross.1
      proposition72c33Families_internalCross.2
      (by simp)
      proposition72c33Score_le proposition72c33Score_internal)

private lemma proposition72c33Graph_adj_of_sameSide
    {x y : Proposition72c33Vertex} (hxy : x ≠ y)
    (hsame : x ∈ (proposition72c33A : Set Proposition72c33Vertex) ↔
      y ∈ (proposition72c33A : Set Proposition72c33Vertex)) :
    proposition72c33Graph.Adj x y := by
  fin_cases x <;> fin_cases y
  all_goals simp [proposition72c33A] at hxy hsame
  all_goals
    norm_num [proposition72c33Graph, proposition72c33Missing, Sym2.eq_iff]
  all_goals decide

theorem proposition72c33CanonicalPacking_arbitraryInternal
    {G : SimpleGraph Proposition72c33Vertex}
    (hcross : SameCrossAdj G proposition72c33Graph
      (proposition72c33A : Set Proposition72c33Vertex)) :
    IsFractionalInternalCrossPacking G
        (proposition72c33A : Set Proposition72c33Vertex)
        (zeroExtendTriangleWeight G proposition72c33Weight) ∧
      fractionalSize G (zeroExtendTriangleWeight G proposition72c33Weight) =
        ((internalEdgeFinset G
          (proposition72c33A : Set Proposition72c33Vertex)).card : ℝ) / 2 := by
  simpa only [proposition72c33Weight] using
    (threeFamilyCertificate_arbitraryInternal
      (G := G) (H := proposition72c33Graph)
      (s := (proposition72c33A : Set Proposition72c33Vertex))
      (F₁ := proposition72c33HalfFamily)
      (F₂ := proposition72c33QuarterFamily) (F₃ := ∅)
      (D := 4) (n₁ := 2) (n₂ := 1) (n₃ := 0)
      (by norm_num) (fun x y ↦ proposition72c33Graph_adj_of_sameSide)
      proposition72c33Families_internalCross.1
      proposition72c33Families_internalCross.2
      (by simp) proposition72c33Score_le proposition72c33Score_internal hcross)

/-! ## The `(3,4)` certificate -/

abbrev Proposition72c34Vertex := Fin 7

def proposition72c34A : Finset Proposition72c34Vertex := {0, 1, 2}

def proposition72c34B : Finset Proposition72c34Vertex := {3, 4, 5, 6}

def proposition72c34Missing : Finset (Sym2 Proposition72c34Vertex) :=
  {s(0, 3), s(0, 4)}

def proposition72c34Graph : SimpleGraph Proposition72c34Vertex :=
  (⊤ : SimpleGraph Proposition72c34Vertex).deleteEdges
    (proposition72c34Missing : Set (Sym2 Proposition72c34Vertex))

def proposition72c34HalfFamily : Finset (Finset Proposition72c34Vertex) :=
  {{0, 5, 6}}

def proposition72c34QuarterFamily : Finset (Finset Proposition72c34Vertex) :=
  {{0, 1, 5}, {0, 1, 6}, {0, 2, 5}, {0, 2, 6},
    {1, 2, 3}, {1, 2, 4}, {1, 3, 4}, {1, 3, 5},
    {1, 3, 6}, {1, 4, 5}, {1, 4, 6}, {2, 3, 4},
    {2, 3, 5}, {2, 3, 6}, {2, 4, 5}, {2, 4, 6}}

def proposition72c34Weight : Finset Proposition72c34Vertex → ℝ :=
  threeFamilyWeight proposition72c34HalfFamily proposition72c34QuarterFamily ∅
    4 2 1 0

private def Proposition72c34FamilyData
    (t : Finset Proposition72c34Vertex) : Prop :=
  t.card = 3 ∧
    (∀ e ∈ proposition72c34Missing, ¬ e.toFinset ⊆ t) ∧
      t ∈ twoOneTriangleFamily proposition72c34A proposition72c34B ∪
        twoOneTriangleFamily proposition72c34B proposition72c34A

private lemma proposition72c34HalfFamily_data :
    ∀ t ∈ proposition72c34HalfFamily, Proposition72c34FamilyData t := by
  intro t ht
  simp only [proposition72c34HalfFamily, mem_singleton] at ht
  subst t
  unfold Proposition72c34FamilyData
  decide

private lemma proposition72c34QuarterFamily_data :
    ∀ t ∈ proposition72c34QuarterFamily, Proposition72c34FamilyData t := by
  intro t ht
  simp only [proposition72c34QuarterFamily, mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold Proposition72c34FamilyData
  all_goals decide

private lemma proposition72c34Families_internalCross :
    proposition72c34HalfFamily ⊆
        internalCrossTriangles proposition72c34Graph
          (proposition72c34A : Set Proposition72c34Vertex) ∧
      proposition72c34QuarterFamily ⊆
        internalCrossTriangles proposition72c34Graph
          (proposition72c34A : Set Proposition72c34Vertex) := by
  have hAB : Disjoint proposition72c34A proposition72c34B := by decide
  constructor
  · apply family_subset_internalCross_of_twoOne hAB
    · intro t ht
      exact topDeleteEdges_isNClique_of_card_avoids proposition72c34Missing t
        (proposition72c34HalfFamily_data t ht).1
        (proposition72c34HalfFamily_data t ht).2.1
    · intro t ht
      exact (proposition72c34HalfFamily_data t ht).2.2
  · apply family_subset_internalCross_of_twoOne hAB
    · intro t ht
      exact topDeleteEdges_isNClique_of_card_avoids proposition72c34Missing t
        (proposition72c34QuarterFamily_data t ht).1
        (proposition72c34QuarterFamily_data t ht).2.1
    · intro t ht
      exact (proposition72c34QuarterFamily_data t ht).2.2

private lemma proposition72c34Score_le
    (e : Sym2 Proposition72c34Vertex) (hne : ¬ e.IsDiag) :
    threeFamilyEdgeScore proposition72c34HalfFamily
      proposition72c34QuarterFamily ∅ 2 1 0 e ≤ 4 := by
  induction e using Sym2.inductionOn with
  | hf x y =>
      have hxy : x ≠ y := by
        simpa only [Sym2.mk_isDiag_iff] using hne
      fin_cases x <;> fin_cases y
      all_goals simp at hxy
      all_goals decide

private lemma proposition72c34Score_internal
    (e : Sym2 Proposition72c34Vertex) (hne : ¬ e.IsDiag)
    (hsame : SameSide (proposition72c34A : Set Proposition72c34Vertex) e) :
    2 * threeFamilyEdgeScore proposition72c34HalfFamily
      proposition72c34QuarterFamily ∅ 2 1 0 e = 4 := by
  induction e using Sym2.inductionOn with
  | hf x y =>
      have hxy : x ≠ y := by
        simpa only [Sym2.mk_isDiag_iff] using hne
      simp only [sameSide_mk] at hsame
      fin_cases x <;> fin_cases y
      all_goals simp [proposition72c34A] at hxy hsame
      all_goals decide

theorem proposition72c34CanonicalPacking :
    IsFractionalInternalCrossPacking proposition72c34Graph
        (proposition72c34A : Set Proposition72c34Vertex)
        proposition72c34Weight ∧
      ∀ e ∈ internalEdgeFinset proposition72c34Graph
        (proposition72c34A : Set Proposition72c34Vertex),
        fractionalEdgeLoad proposition72c34Graph proposition72c34Weight e = 1 / 2 := by
  simpa only [proposition72c34Weight] using
    (threeFamilyCertificate (G := proposition72c34Graph)
      (s := (proposition72c34A : Set Proposition72c34Vertex))
      (F₁ := proposition72c34HalfFamily)
      (F₂ := proposition72c34QuarterFamily) (F₃ := ∅)
      (D := 4) (n₁ := 2) (n₂ := 1) (n₃ := 0)
      (by norm_num)
      proposition72c34Families_internalCross.1
      proposition72c34Families_internalCross.2
      (by simp)
      proposition72c34Score_le proposition72c34Score_internal)

private lemma proposition72c34Graph_adj_of_sameSide
    {x y : Proposition72c34Vertex} (hxy : x ≠ y)
    (hsame : x ∈ (proposition72c34A : Set Proposition72c34Vertex) ↔
      y ∈ (proposition72c34A : Set Proposition72c34Vertex)) :
    proposition72c34Graph.Adj x y := by
  fin_cases x <;> fin_cases y
  all_goals simp [proposition72c34A] at hxy hsame
  all_goals
    norm_num [proposition72c34Graph, proposition72c34Missing, Sym2.eq_iff]
  all_goals decide

theorem proposition72c34CanonicalPacking_arbitraryInternal
    {G : SimpleGraph Proposition72c34Vertex}
    (hcross : SameCrossAdj G proposition72c34Graph
      (proposition72c34A : Set Proposition72c34Vertex)) :
    IsFractionalInternalCrossPacking G
        (proposition72c34A : Set Proposition72c34Vertex)
        (zeroExtendTriangleWeight G proposition72c34Weight) ∧
      fractionalSize G (zeroExtendTriangleWeight G proposition72c34Weight) =
        ((internalEdgeFinset G
          (proposition72c34A : Set Proposition72c34Vertex)).card : ℝ) / 2 := by
  simpa only [proposition72c34Weight] using
    (threeFamilyCertificate_arbitraryInternal
      (G := G) (H := proposition72c34Graph)
      (s := (proposition72c34A : Set Proposition72c34Vertex))
      (F₁ := proposition72c34HalfFamily)
      (F₂ := proposition72c34QuarterFamily) (F₃ := ∅)
      (D := 4) (n₁ := 2) (n₂ := 1) (n₃ := 0)
      (by norm_num) (fun x y ↦ proposition72c34Graph_adj_of_sameSide)
      proposition72c34Families_internalCross.1
      proposition72c34Families_internalCross.2
      (by simp) proposition72c34Score_le proposition72c34Score_internal hcross)

/-! ## The `(4,4)` certificate -/

abbrev Proposition72c44Vertex := Fin 8

def proposition72c44A : Finset Proposition72c44Vertex := {0, 1, 2, 3}

def proposition72c44B : Finset Proposition72c44Vertex := {4, 5, 6, 7}

def proposition72c44Missing : Finset (Sym2 Proposition72c44Vertex) :=
  {s(0, 4), s(0, 5)}

def proposition72c44Graph : SimpleGraph Proposition72c44Vertex :=
  (⊤ : SimpleGraph Proposition72c44Vertex).deleteEdges
    (proposition72c44Missing : Set (Sym2 Proposition72c44Vertex))

def proposition72c44QuarterFamily : Finset (Finset Proposition72c44Vertex) :=
  {{0, 1, 6}, {0, 1, 7}, {0, 2, 6}, {0, 2, 7},
    {0, 3, 6}, {0, 3, 7}, {0, 6, 7}, {1, 2, 4},
    {1, 2, 5}, {1, 3, 4}, {1, 3, 5}, {2, 3, 4}, {2, 3, 5}}

def proposition72c44SixthFamily : Finset (Finset Proposition72c44Vertex) :=
  {{1, 4, 5}, {1, 4, 6}, {1, 4, 7}, {1, 5, 6}, {1, 5, 7},
    {2, 4, 5}, {2, 4, 6}, {2, 4, 7}, {2, 5, 6}, {2, 5, 7},
    {3, 4, 5}, {3, 4, 6}, {3, 4, 7}, {3, 5, 6}, {3, 5, 7}}

def proposition72c44TwelfthFamily : Finset (Finset Proposition72c44Vertex) :=
  {{1, 6, 7}, {2, 6, 7}, {3, 6, 7}}

def proposition72c44Weight : Finset Proposition72c44Vertex → ℝ :=
  threeFamilyWeight proposition72c44QuarterFamily proposition72c44SixthFamily
    proposition72c44TwelfthFamily 12 3 2 1

private def Proposition72c44FamilyData
    (t : Finset Proposition72c44Vertex) : Prop :=
  t.card = 3 ∧
    (∀ e ∈ proposition72c44Missing, ¬ e.toFinset ⊆ t) ∧
      t ∈ twoOneTriangleFamily proposition72c44A proposition72c44B ∪
        twoOneTriangleFamily proposition72c44B proposition72c44A

private lemma proposition72c44QuarterFamily_data :
    ∀ t ∈ proposition72c44QuarterFamily, Proposition72c44FamilyData t := by
  intro t ht
  simp only [proposition72c44QuarterFamily, mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold Proposition72c44FamilyData
  all_goals decide

private lemma proposition72c44SixthFamily_data :
    ∀ t ∈ proposition72c44SixthFamily, Proposition72c44FamilyData t := by
  intro t ht
  simp only [proposition72c44SixthFamily, mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold Proposition72c44FamilyData
  all_goals decide

private lemma proposition72c44TwelfthFamily_data :
    ∀ t ∈ proposition72c44TwelfthFamily, Proposition72c44FamilyData t := by
  intro t ht
  simp only [proposition72c44TwelfthFamily, mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  all_goals unfold Proposition72c44FamilyData
  all_goals decide

private lemma proposition72c44Families_internalCross :
    proposition72c44QuarterFamily ⊆
        internalCrossTriangles proposition72c44Graph
          (proposition72c44A : Set Proposition72c44Vertex) ∧
      proposition72c44SixthFamily ⊆
        internalCrossTriangles proposition72c44Graph
          (proposition72c44A : Set Proposition72c44Vertex) ∧
      proposition72c44TwelfthFamily ⊆
        internalCrossTriangles proposition72c44Graph
          (proposition72c44A : Set Proposition72c44Vertex) := by
  have hAB : Disjoint proposition72c44A proposition72c44B := by decide
  refine ⟨?_, ?_, ?_⟩
  · apply family_subset_internalCross_of_twoOne hAB
    · intro t ht
      exact topDeleteEdges_isNClique_of_card_avoids proposition72c44Missing t
        (proposition72c44QuarterFamily_data t ht).1
        (proposition72c44QuarterFamily_data t ht).2.1
    · intro t ht
      exact (proposition72c44QuarterFamily_data t ht).2.2
  · apply family_subset_internalCross_of_twoOne hAB
    · intro t ht
      exact topDeleteEdges_isNClique_of_card_avoids proposition72c44Missing t
        (proposition72c44SixthFamily_data t ht).1
        (proposition72c44SixthFamily_data t ht).2.1
    · intro t ht
      exact (proposition72c44SixthFamily_data t ht).2.2
  · apply family_subset_internalCross_of_twoOne hAB
    · intro t ht
      exact topDeleteEdges_isNClique_of_card_avoids proposition72c44Missing t
        (proposition72c44TwelfthFamily_data t ht).1
        (proposition72c44TwelfthFamily_data t ht).2.1
    · intro t ht
      exact (proposition72c44TwelfthFamily_data t ht).2.2

private lemma proposition72c44Score_le
    (e : Sym2 Proposition72c44Vertex) (hne : ¬ e.IsDiag) :
    threeFamilyEdgeScore proposition72c44QuarterFamily
      proposition72c44SixthFamily proposition72c44TwelfthFamily 3 2 1 e ≤ 12 := by
  induction e using Sym2.inductionOn with
  | hf x y =>
      have hxy : x ≠ y := by
        simpa only [Sym2.mk_isDiag_iff] using hne
      fin_cases x <;> fin_cases y
      all_goals simp at hxy
      all_goals decide

private lemma proposition72c44Score_internal
    (e : Sym2 Proposition72c44Vertex) (hne : ¬ e.IsDiag)
    (hsame : SameSide (proposition72c44A : Set Proposition72c44Vertex) e) :
    2 * threeFamilyEdgeScore proposition72c44QuarterFamily
      proposition72c44SixthFamily proposition72c44TwelfthFamily 3 2 1 e = 12 := by
  induction e using Sym2.inductionOn with
  | hf x y =>
      have hxy : x ≠ y := by
        simpa only [Sym2.mk_isDiag_iff] using hne
      simp only [sameSide_mk] at hsame
      fin_cases x <;> fin_cases y
      all_goals simp [proposition72c44A] at hxy hsame
      all_goals decide

theorem proposition72c44CanonicalPacking :
    IsFractionalInternalCrossPacking proposition72c44Graph
        (proposition72c44A : Set Proposition72c44Vertex)
        proposition72c44Weight ∧
      ∀ e ∈ internalEdgeFinset proposition72c44Graph
        (proposition72c44A : Set Proposition72c44Vertex),
        fractionalEdgeLoad proposition72c44Graph proposition72c44Weight e = 1 / 2 := by
  simpa only [proposition72c44Weight] using
    (threeFamilyCertificate (G := proposition72c44Graph)
      (s := (proposition72c44A : Set Proposition72c44Vertex))
      (F₁ := proposition72c44QuarterFamily)
      (F₂ := proposition72c44SixthFamily)
      (F₃ := proposition72c44TwelfthFamily)
      (D := 12) (n₁ := 3) (n₂ := 2) (n₃ := 1)
      (by norm_num)
      proposition72c44Families_internalCross.1
      proposition72c44Families_internalCross.2.1
      proposition72c44Families_internalCross.2.2
      proposition72c44Score_le proposition72c44Score_internal)

private lemma proposition72c44Graph_adj_of_sameSide
    {x y : Proposition72c44Vertex} (hxy : x ≠ y)
    (hsame : x ∈ (proposition72c44A : Set Proposition72c44Vertex) ↔
      y ∈ (proposition72c44A : Set Proposition72c44Vertex)) :
    proposition72c44Graph.Adj x y := by
  fin_cases x <;> fin_cases y
  all_goals simp [proposition72c44A] at hxy hsame
  all_goals
    norm_num [proposition72c44Graph, proposition72c44Missing, Sym2.eq_iff]
  all_goals decide

theorem proposition72c44CanonicalPacking_arbitraryInternal
    {G : SimpleGraph Proposition72c44Vertex}
    (hcross : SameCrossAdj G proposition72c44Graph
      (proposition72c44A : Set Proposition72c44Vertex)) :
    IsFractionalInternalCrossPacking G
        (proposition72c44A : Set Proposition72c44Vertex)
        (zeroExtendTriangleWeight G proposition72c44Weight) ∧
      fractionalSize G (zeroExtendTriangleWeight G proposition72c44Weight) =
        ((internalEdgeFinset G
          (proposition72c44A : Set Proposition72c44Vertex)).card : ℝ) / 2 := by
  simpa only [proposition72c44Weight] using
    (threeFamilyCertificate_arbitraryInternal
      (G := G) (H := proposition72c44Graph)
      (s := (proposition72c44A : Set Proposition72c44Vertex))
      (F₁ := proposition72c44QuarterFamily)
      (F₂ := proposition72c44SixthFamily)
      (F₃ := proposition72c44TwelfthFamily)
      (D := 12) (n₁ := 3) (n₂ := 2) (n₃ := 1)
      (by norm_num) (fun x y ↦ proposition72c44Graph_adj_of_sameSide)
      proposition72c44Families_internalCross.1
      proposition72c44Families_internalCross.2.1
      proposition72c44Families_internalCross.2.2
      proposition72c44Score_le proposition72c44Score_internal hcross)

/-! ## The `(4,5)` certificate -/

abbrev Proposition72c45Vertex := Fin 9

def proposition72c45A : Finset Proposition72c45Vertex := {0, 1, 2, 3}

def proposition72c45B : Finset Proposition72c45Vertex := {4, 5, 6, 7, 8}

def proposition72c45Missing : Finset (Sym2 Proposition72c45Vertex) :=
  {s(0, 4), s(0, 5)}

def proposition72c45Graph : SimpleGraph Proposition72c45Vertex :=
  (⊤ : SimpleGraph Proposition72c45Vertex).deleteEdges
    (proposition72c45Missing : Set (Sym2 Proposition72c45Vertex))

def proposition72c45SixthFamily : Finset (Finset Proposition72c45Vertex) :=
  {{0, 1, 6}, {0, 1, 7}, {0, 1, 8},
    {0, 2, 6}, {0, 2, 7}, {0, 2, 8},
    {0, 3, 6}, {0, 3, 7}, {0, 3, 8},
    {0, 6, 7}, {0, 6, 8}, {0, 7, 8},
    {1, 2, 4}, {1, 2, 5}, {1, 3, 4}, {1, 3, 5},
    {1, 4, 5}, {1, 4, 6}, {1, 4, 7}, {1, 4, 8},
    {1, 5, 6}, {1, 5, 7}, {1, 5, 8},
    {2, 3, 4}, {2, 3, 5},
    {2, 4, 5}, {2, 4, 6}, {2, 4, 7}, {2, 4, 8},
    {2, 5, 6}, {2, 5, 7}, {2, 5, 8},
    {3, 4, 5}, {3, 4, 6}, {3, 4, 7}, {3, 4, 8},
    {3, 5, 6}, {3, 5, 7}, {3, 5, 8}}

def proposition72c45EighteenthFamily : Finset (Finset Proposition72c45Vertex) :=
  {{1, 2, 6}, {1, 2, 7}, {1, 2, 8},
    {1, 3, 6}, {1, 3, 7}, {1, 3, 8},
    {2, 3, 6}, {2, 3, 7}, {2, 3, 8}}

def proposition72c45NinthFamily : Finset (Finset Proposition72c45Vertex) :=
  {{1, 6, 7}, {1, 6, 8}, {1, 7, 8},
    {2, 6, 7}, {2, 6, 8}, {2, 7, 8},
    {3, 6, 7}, {3, 6, 8}, {3, 7, 8}}

def proposition72c45Weight : Finset Proposition72c45Vertex → ℝ :=
  threeFamilyWeight proposition72c45SixthFamily
    proposition72c45EighteenthFamily proposition72c45NinthFamily 18 3 1 2

private def Proposition72c45FamilyData
    (t : Finset Proposition72c45Vertex) : Prop :=
  t.card = 3 ∧
    (∀ e ∈ proposition72c45Missing, ¬ e.toFinset ⊆ t) ∧
      ((∃ z ∈ proposition72c45B,
          ∃ p ∈ proposition72c45A.powersetCard 2, t = insert z p) ∨
        (∃ z ∈ proposition72c45A,
          ∃ p ∈ proposition72c45B.powersetCard 2, t = insert z p))

private lemma proposition72c45FamilyData_twoOne
    {t : Finset Proposition72c45Vertex} (ht : Proposition72c45FamilyData t) :
    t ∈ twoOneTriangleFamily proposition72c45A proposition72c45B ∪
      twoOneTriangleFamily proposition72c45B proposition72c45A := by
  rcases ht.2.2 with htAB | htBA
  · exact mem_union_left _ (mem_twoOneTriangleFamily_iff.mpr htAB)
  · exact mem_union_right _ (mem_twoOneTriangleFamily_iff.mpr htBA)

private lemma proposition72c45SixthFamily_data :
    ∀ t ∈ proposition72c45SixthFamily, Proposition72c45FamilyData t := by
  intro t ht
  simp only [proposition72c45SixthFamily, mem_insert, mem_singleton] at ht
  rcases ht with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold Proposition72c45FamilyData
  all_goals decide

private lemma proposition72c45EighteenthFamily_data :
    ∀ t ∈ proposition72c45EighteenthFamily, Proposition72c45FamilyData t := by
  intro t ht
  simp only [proposition72c45EighteenthFamily, mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold Proposition72c45FamilyData
  all_goals decide

private lemma proposition72c45NinthFamily_data :
    ∀ t ∈ proposition72c45NinthFamily, Proposition72c45FamilyData t := by
  intro t ht
  simp only [proposition72c45NinthFamily, mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold Proposition72c45FamilyData
  all_goals decide

private lemma proposition72c45Families_internalCross :
    proposition72c45SixthFamily ⊆
        internalCrossTriangles proposition72c45Graph
          (proposition72c45A : Set Proposition72c45Vertex) ∧
      proposition72c45EighteenthFamily ⊆
        internalCrossTriangles proposition72c45Graph
          (proposition72c45A : Set Proposition72c45Vertex) ∧
      proposition72c45NinthFamily ⊆
        internalCrossTriangles proposition72c45Graph
          (proposition72c45A : Set Proposition72c45Vertex) := by
  have hAB : Disjoint proposition72c45A proposition72c45B := by decide
  refine ⟨?_, ?_, ?_⟩
  · apply family_subset_internalCross_of_twoOne hAB
    · intro t ht
      exact topDeleteEdges_isNClique_of_card_avoids proposition72c45Missing t
        (proposition72c45SixthFamily_data t ht).1
        (proposition72c45SixthFamily_data t ht).2.1
    · intro t ht
      exact proposition72c45FamilyData_twoOne
        (proposition72c45SixthFamily_data t ht)
  · apply family_subset_internalCross_of_twoOne hAB
    · intro t ht
      exact topDeleteEdges_isNClique_of_card_avoids proposition72c45Missing t
        (proposition72c45EighteenthFamily_data t ht).1
        (proposition72c45EighteenthFamily_data t ht).2.1
    · intro t ht
      exact proposition72c45FamilyData_twoOne
        (proposition72c45EighteenthFamily_data t ht)
  · apply family_subset_internalCross_of_twoOne hAB
    · intro t ht
      exact topDeleteEdges_isNClique_of_card_avoids proposition72c45Missing t
        (proposition72c45NinthFamily_data t ht).1
        (proposition72c45NinthFamily_data t ht).2.1
    · intro t ht
      exact proposition72c45FamilyData_twoOne
        (proposition72c45NinthFamily_data t ht)

private lemma proposition72c45Score_le
    (e : Sym2 Proposition72c45Vertex) (hne : ¬ e.IsDiag) :
    threeFamilyEdgeScore proposition72c45SixthFamily
      proposition72c45EighteenthFamily proposition72c45NinthFamily 3 1 2 e ≤ 18 := by
  induction e using Sym2.inductionOn with
  | hf x y =>
      have hxy : x ≠ y := by
        simpa only [Sym2.mk_isDiag_iff] using hne
      fin_cases x <;> fin_cases y
      all_goals simp at hxy
      all_goals decide

private lemma proposition72c45Score_internal
    (e : Sym2 Proposition72c45Vertex) (hne : ¬ e.IsDiag)
    (hsame : SameSide (proposition72c45A : Set Proposition72c45Vertex) e) :
    2 * threeFamilyEdgeScore proposition72c45SixthFamily
      proposition72c45EighteenthFamily proposition72c45NinthFamily 3 1 2 e = 18 := by
  induction e using Sym2.inductionOn with
  | hf x y =>
      have hxy : x ≠ y := by
        simpa only [Sym2.mk_isDiag_iff] using hne
      simp only [sameSide_mk] at hsame
      fin_cases x <;> fin_cases y
      all_goals simp [proposition72c45A] at hxy hsame
      all_goals decide

theorem proposition72c45CanonicalPacking :
    IsFractionalInternalCrossPacking proposition72c45Graph
        (proposition72c45A : Set Proposition72c45Vertex)
        proposition72c45Weight ∧
      ∀ e ∈ internalEdgeFinset proposition72c45Graph
        (proposition72c45A : Set Proposition72c45Vertex),
        fractionalEdgeLoad proposition72c45Graph proposition72c45Weight e = 1 / 2 := by
  simpa only [proposition72c45Weight] using
    (threeFamilyCertificate (G := proposition72c45Graph)
      (s := (proposition72c45A : Set Proposition72c45Vertex))
      (F₁ := proposition72c45SixthFamily)
      (F₂ := proposition72c45EighteenthFamily)
      (F₃ := proposition72c45NinthFamily)
      (D := 18) (n₁ := 3) (n₂ := 1) (n₃ := 2)
      (by norm_num)
      proposition72c45Families_internalCross.1
      proposition72c45Families_internalCross.2.1
      proposition72c45Families_internalCross.2.2
      proposition72c45Score_le proposition72c45Score_internal)

private lemma proposition72c45Graph_adj_of_sameSide
    {x y : Proposition72c45Vertex} (hxy : x ≠ y)
    (hsame : x ∈ (proposition72c45A : Set Proposition72c45Vertex) ↔
      y ∈ (proposition72c45A : Set Proposition72c45Vertex)) :
    proposition72c45Graph.Adj x y := by
  fin_cases x <;> fin_cases y
  all_goals simp [proposition72c45A] at hxy hsame
  all_goals
    norm_num [proposition72c45Graph, proposition72c45Missing, Sym2.eq_iff]
  all_goals decide

theorem proposition72c45CanonicalPacking_arbitraryInternal
    {G : SimpleGraph Proposition72c45Vertex}
    (hcross : SameCrossAdj G proposition72c45Graph
      (proposition72c45A : Set Proposition72c45Vertex)) :
    IsFractionalInternalCrossPacking G
        (proposition72c45A : Set Proposition72c45Vertex)
        (zeroExtendTriangleWeight G proposition72c45Weight) ∧
      fractionalSize G (zeroExtendTriangleWeight G proposition72c45Weight) =
        ((internalEdgeFinset G
          (proposition72c45A : Set Proposition72c45Vertex)).card : ℝ) / 2 := by
  simpa only [proposition72c45Weight] using
    (threeFamilyCertificate_arbitraryInternal
      (G := G) (H := proposition72c45Graph)
      (s := (proposition72c45A : Set Proposition72c45Vertex))
      (F₁ := proposition72c45SixthFamily)
      (F₂ := proposition72c45EighteenthFamily)
      (F₃ := proposition72c45NinthFamily)
      (D := 18) (n₁ := 3) (n₂ := 1) (n₃ := 2)
      (by norm_num) (fun x y ↦ proposition72c45Graph_adj_of_sameSide)
      proposition72c45Families_internalCross.1
      proposition72c45Families_internalCross.2.1
      proposition72c45Families_internalCross.2.2
      proposition72c45Score_le proposition72c45Score_internal hcross)

end

end Erdos76
