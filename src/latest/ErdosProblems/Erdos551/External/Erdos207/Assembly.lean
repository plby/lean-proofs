import ErdosProblems.Erdos551.External.Erdos207.SphereExpansion

namespace Erdos207

open Finset

namespace IsSteiner

/-- Distinct triples in a Steiner triple system meet in at most one vertex. -/
lemma inter_card_le_one {n : ℕ} {H : TripleSystem n} (hH : IsSteiner H)
    {T U : Triple n} (hTH : T ∈ H) (hUH : U ∈ H) (hTU : T ≠ U) :
    (T.1 ∩ U.1).card ≤ 1 := by
  by_contra hinter
  have hinter' : 1 < (T.1 ∩ U.1).card := by omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hinter'
  have hpair := hH u v huv
  have hT : T ∈ H ∧ u ∈ T.1 ∧ v ∈ T.1 :=
    ⟨hTH, (Finset.mem_inter.mp hu).1, (Finset.mem_inter.mp hv).1⟩
  have hU : U ∈ H ∧ u ∈ U.1 ∧ v ∈ U.1 :=
    ⟨hUH, (Finset.mem_inter.mp hu).2, (Finset.mem_inter.mp hv).2⟩
  exact hTU (hpair.unique hT hU)

/-- Every Steiner triple system already satisfies the two-edge case of local
sparsity. -/
lemma locallySparse_two {n : ℕ} {H : TripleSystem n} (hH : IsSteiner H) :
    LocallySparse 2 H := by
  intro C hCH hC2 hC_le
  have hCcard : C.card = 2 := by omega
  obtain ⟨T, U, hTU, rfl⟩ := Finset.card_eq_two.mp hCcard
  have hTH : T ∈ H := hCH (by simp)
  have hUH : U ∈ H := hCH (by simp)
  have hinter := hH.inter_card_le_one hTH hUH hTU
  have hcard := Finset.card_union_add_card_inter T.1 U.1
  have hvertices : verticesOn ({T, U} : TripleSystem n) = T.1 ∪ U.1 := by
    simp [verticesOn]
  rw [hvertices]
  simp only [Finset.card_pair hTU]
  omega

end IsSteiner

/-- KSSS's vertex-indexed girth condition at cutoff `g + 2` implies the
edge-indexed local-sparsity condition in Erdős Problem 207. -/
lemma locallySparse_of_girthGreater {n g : ℕ} {H : TripleSystem n}
    (hH : GirthGreater (g + 2) H) : LocallySparse g H := by
  intro C hCH hC2 hCg
  by_contra hspan
  have hspan' : (verticesOn C).card ≤ C.card + 2 := by omega
  have hr4 : 4 ≤ C.card + 2 := by omega
  have hrg : C.card + 2 ≤ g + 2 := by omega
  apply hH (C.card + 2) hr4 hrg
  refine ⟨C, hCH, ?_⟩
  constructor
  · omega
  · exact hspan'

/-- The edge-indexed and vertex-indexed formulations of high girth agree,
including the shift by two. -/
lemma girthGreater_of_locallySparse {n g : ℕ} {H : TripleSystem n}
    (hH : LocallySparse g H) : GirthGreater (g + 2) H := by
  intro r hr4 hrg
  rintro ⟨C, hCH, hcard, hspan⟩
  have hC2 : 2 ≤ C.card := by omega
  have hCg : C.card ≤ g := by omega
  have hsparse := hH C hCH hC2 hCg
  omega

theorem girthGreater_add_two_iff_locallySparse {n g : ℕ} {H : TripleSystem n} :
    GirthGreater (g + 2) H ↔ LocallySparse g H :=
  ⟨locallySparse_of_girthGreater, girthGreater_of_locallySparse⟩

/-- Raising the cutoff strengthens the high-girth condition. -/
lemma GirthGreater.mono {n q q' : ℕ} {H : TripleSystem n}
    (hH : GirthGreater q H) (hqq' : q' ≤ q) : GirthGreater q' H := by
  intro r hr4 hrq'
  exact hH r hr4 (hrq'.trans hqq')

/-- Deterministic final assembly.  A decomposition of each side of an
edge-partition of the complete graph is a Steiner triple system. -/
theorem highGirthSteiner_of_edge_partition {n q : ℕ}
    {G K : SimpleGraph (Fin n)} {C D : TripleSystem n}
    (hC : IsTriangleDecomposition G C)
    (hD : IsTriangleDecomposition K D)
    (hGK : Disjoint G K)
    (hcomplete : G ⊔ K = SimpleGraph.completeGraph (Fin n))
    (hgirth : GirthGreater q (C ∪ D)) :
    IsSteiner (C ∪ D) ∧ GirthGreater q (C ∪ D) := by
  refine ⟨isSteiner_iff_triangleDecomposition.mpr ?_, hgirth⟩
  rw [← hcomplete]
  exact hC.union hD hGK

/-- A high-girth decomposition of the leave completes a partial Steiner
packing to a high-girth Steiner triple system. -/
theorem IsPackingOn.complete_with_leave {n q : ℕ}
    {C D : TripleSystem n} (hC : IsPacking C)
    (hD : IsTriangleDecomposition (leaveGraph C) D)
    (hgirth : GirthGreater q (C ∪ D)) :
    IsSteiner (C ∪ D) ∧ GirthGreater q (C ∪ D) :=
  highGirthSteiner_of_edge_partition hC.isTriangleDecomposition hD
    (coveredGraph_disjoint_leaveGraph C)
    (coveredGraph_sup_leaveGraph C) hgirth

/-- The exact finite output required from the probabilistic construction:
a partial packing whose leave can be decomposed without creating a forbidden
configuration. -/
def HasCompletableHighGirthPacking (q n : ℕ) : Prop :=
  ∃ C D : TripleSystem n, IsPacking C ∧
    IsTriangleDecomposition (leaveGraph C) D ∧
    GirthGreater q (C ∪ D)

theorem highGirthSteiner_of_completablePacking {q n : ℕ}
    (h : HasCompletableHighGirthPacking q n) :
    ∃ H : TripleSystem n, IsSteiner H ∧ GirthGreater q H := by
  obtain ⟨C, D, hC, hD, hgirth⟩ := h
  exact ⟨C ∪ D, hC.complete_with_leave hD hgirth⟩

/-- The exact high-girth Steiner-system existence assertion proved by KSSS. -/
def HighGirthSteinerSystems : Prop :=
  ∀ q : ℕ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Admissible n →
    ∃ H : TripleSystem n, IsSteiner H ∧ GirthGreater q H

/-- The literal finite statement of Erdős Problem 207. -/
def Erdos207Statement : Prop :=
  ∀ g : ℕ, 2 ≤ g → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Admissible n →
    ∃ H : TripleSystem n, IsSteiner H ∧ LocallySparse g H

/-- The exact parameter shift from KSSS Theorem 1.1 to Erdős Problem 207. -/
theorem erdos207_of_highGirthSteinerSystems
    (hKSSS : HighGirthSteinerSystems) : Erdos207Statement := by
  intro g _
  obtain ⟨N₀, hN₀⟩ := hKSSS (g + 2)
  refine ⟨N₀, fun n hn hadm ↦ ?_⟩
  obtain ⟨H, hsteiner, hgirth⟩ := hN₀ n hn hadm
  exact ⟨H, hsteiner, locallySparse_of_girthGreater hgirth⟩

end Erdos207
