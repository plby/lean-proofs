import Mathlib
import Wikipedia.SzemeredisTheorem.Hypergraph.SourceFullBundleRemovalAssembly

/-!
# The Frankl–Rödl unique-clique bound

The rank-three, four-partite hypergraph-removal theorem supplies the analytic
input. Uniqueness of the clique containing each edge makes every face projection
injective on tetrahedra; removal then bounds the original edge set.
-/

open Finset
open scoped BigOperators

/-- The unique-clique form of the Frankl–Rödl theorem for 3-uniform hypergraphs. -/
def Theorem_2_2 : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ n₀ : ℕ,
    ∀ (V : Finset ℕ) (E : Finset (Finset ℕ)),
    V.card ≥ n₀ →
    (∀ e ∈ E, e.card = 3 ∧ e ⊆ V) →
    (∀ e ∈ E, ∃! K, K ⊆ V ∧ K.card ≥ 4 ∧
      (∀ t ⊆ K, t.card = 3 → t ∈ E) ∧ e ⊆ K) →
    (E.card : ℝ) < ε * (V.card : ℝ) ^ 3

namespace FranklRodl

open Wikipedia.SzemeredisTheorem

private theorem pair_in_face :
    ∀ i j : Fin 4, ∃ e : OrderedFace 4 3, ∃ a b : Fin 3,
      e a = i ∧ e b = j := by
  intro i j
  have h : ∀ i j : Fin 4, ∃ k : Fin 4, k ≠ i ∧ k ≠ j := by decide
  obtain ⟨k, hki, hkj⟩ := h i j
  have hi : i ∈ Set.range (Fin.succAboveOrderEmb k) := by
    simpa [Fin.range_succAboveOrderEmb] using hki.symm
  have hj : j ∈ Set.range (Fin.succAboveOrderEmb k) := by
    simpa [Fin.range_succAboveOrderEmb] using hkj.symm
  obtain ⟨a, ha⟩ := hi
  obtain ⟨b, hb⟩ := hj
  exact ⟨Fin.succAboveOrderEmb k, a, b, ha, hb⟩

private theorem three_set_is_face :
    ∀ S : Finset (Fin 4), S.card = 3 →
      ∃ e : OrderedFace 4 3, univ.image e = S := by
  intro S hS
  exact ⟨S.orderEmbOfFin hS, S.image_orderEmbOfFin_univ hS⟩

private theorem outside_face_unique :
    ∀ e : OrderedFace 4 3, ∀ i j : Fin 4,
      (∀ a, e a ≠ i) → (∀ a, e a ≠ j) → i = j := by
  intro e i j hi hj
  have h01 := e.strictMono (show (0 : Fin 3) < 1 by decide)
  have h12 := e.strictMono (show (1 : Fin 3) < 2 by decide)
  have hi0 := hi 0
  have hi1 := hi 1
  have hi2 := hi 2
  have hj0 := hj 0
  have hj1 := hj 1
  have hj2 := hj 2
  omega

variable {V : Finset ℕ}

private def vertices {r : ℕ} (x : Fin r → V) : Finset ℕ :=
  univ.image fun i => (x i : ℕ)

private theorem vertices_subset {r : ℕ} (x : Fin r → V) :
    vertices x ⊆ V := by
  intro a ha
  obtain ⟨i, _, rfl⟩ := mem_image.mp ha
  exact (x i).property

private theorem vertices_card {r : ℕ} {x : Fin r → V}
    (hx : Function.Injective x) : (vertices x).card = r := by
  rw [vertices, card_image_of_injective]
  · simp
  · exact Subtype.val_injective.comp hx

private def pattern (V : Finset ℕ) (E : Finset (Finset ℕ)) :
    OrderedPattern V 4 3 where
  edge _ y := Function.Injective y ∧ vertices y ∈ E

private theorem occurrence_injective {E : Finset (Finset ℕ)}
    {x : Fin 4 → V} (hx : (pattern V E).IsOccurrence x) :
    Function.Injective x := by
  intro i j hij
  obtain ⟨e, a, b, ha, hb⟩ := pair_in_face i j
  have hab : a = b := (hx e).1 (by simpa [orderedFaceTuple, ha, hb] using hij)
  simpa [ha, hb] using congrArg e hab

private theorem face_vertices_subset (x : Fin 4 → V) (e : OrderedFace 4 3) :
    vertices (orderedFaceTuple e x) ⊆ vertices x := by
  intro a ha
  obtain ⟨i, _, rfl⟩ := mem_image.mp ha
  exact mem_image.mpr ⟨e i, mem_univ _, rfl⟩

private theorem three_subset_is_face {x : Fin 4 → V}
    (hx : Function.Injective x) {t : Finset ℕ}
    (ht : t ⊆ vertices x) (hcard : t.card = 3) :
    ∃ e : OrderedFace 4 3, vertices (orderedFaceTuple e x) = t := by
  classical
  let S : Finset (Fin 4) := univ.filter fun i => (x i : ℕ) ∈ t
  have himage : S.image (fun i => (x i : ℕ)) = t := by
    ext a
    simp only [mem_image]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact (mem_filter.mp hi).2
    · intro ha
      obtain ⟨i, _, hi⟩ := mem_image.mp (ht ha)
      exact ⟨i, mem_filter.mpr ⟨mem_univ _, by simpa [hi] using ha⟩, hi⟩
  have hS : S.card = 3 := by
    rw [← hcard, ← himage]
    exact (card_image_of_injective S (Subtype.val_injective.comp hx)).symm
  obtain ⟨e, he⟩ := three_set_is_face S hS
  refine ⟨e, ?_⟩
  rw [← himage, ← he, image_image]
  rfl

private def IsClique (V : Finset ℕ) (E : Finset (Finset ℕ))
    (K : Finset ℕ) : Prop :=
  K ⊆ V ∧ 4 ≤ K.card ∧ ∀ t ⊆ K, t.card = 3 → t ∈ E

private theorem occurrence_clique {E : Finset (Finset ℕ)}
    {x : Fin 4 → V} (hx : (pattern V E).IsOccurrence x) :
    IsClique V E (vertices x) := by
  have hinj := occurrence_injective hx
  refine ⟨vertices_subset x, (vertices_card hinj).ge, ?_⟩
  intro t ht hcard
  obtain ⟨e, rfl⟩ := three_subset_is_face hinj ht hcard
  exact (hx e).2

private theorem face_projection_injective {E : Finset (Finset ℕ)}
    (hunique : ∀ t ∈ E, ∃! K, IsClique V E K ∧ t ⊆ K)
    (e : OrderedFace 4 3) :
    Set.InjOn (fun x : Fin 4 → V => orderedFaceTuple e x)
      ↑(pattern V E).occurrenceFinset := by
  classical
  intro x hx y hy hxy
  change orderedFaceTuple e x = orderedFaceTuple e y at hxy
  have hx' := ((pattern V E).mem_occurrenceFinset x).mp hx
  have hy' := ((pattern V E).mem_occurrenceFinset y).mp hy
  obtain ⟨K, _, hK⟩ := hunique _ (hx' e).2
  have hKx := hK _ ⟨occurrence_clique hx', face_vertices_subset x e⟩
  have hKy := hK _ ⟨occurrence_clique hy', by
    rw [hxy]
    exact face_vertices_subset y e⟩
  have hrange : vertices x = vertices y := hKx.trans hKy.symm
  have hxi := occurrence_injective hx'
  funext i
  by_cases hi : ∃ a, e a = i
  · obtain ⟨a, rfl⟩ := hi
    exact congrFun hxy a
  · have hmem : (x i : ℕ) ∈ vertices y := by
      rw [← hrange]
      exact mem_image.mpr ⟨i, mem_univ _, rfl⟩
    obtain ⟨j, _, hj⟩ := mem_image.mp hmem
    have hj' : y j = x i := Subtype.ext hj
    have hji : j = i := outside_face_unique e j i
      (by
        intro a ha
        have hval : x (e a) = x i :=
          (congrFun hxy a).trans (by simpa [orderedFaceTuple, ha] using hj')
        exact hi ⟨a, hxi hval⟩)
      (by simpa using hi)
    simpa [hji] using hj'.symm

private theorem occurrence_card_le {E : Finset (Finset ℕ)}
    (hunique : ∀ t ∈ E, ∃! K, IsClique V E K ∧ t ⊆ K) :
    (pattern V E).occurrenceFinset.card ≤ V.card ^ 3 := by
  classical
  let e : OrderedFace 4 3 := Fin.succAboveOrderEmb 0
  calc
    (pattern V E).occurrenceFinset.card ≤
        (univ : Finset (Fin 3 → V)).card :=
      card_le_card_of_injOn (orderedFaceTuple e)
        (fun _ _ => mem_univ _) (face_projection_injective hunique e)
    _ = V.card ^ 3 := by simp

private theorem edge_in_occurrence {E : Finset (Finset ℕ)}
    (hE : ∀ t ∈ E, t.card = 3)
    (hunique : ∀ t ∈ E, ∃! K, IsClique V E K ∧ t ⊆ K)
    {t : Finset ℕ} (ht : t ∈ E) :
    ∃ x ∈ (pattern V E).occurrenceFinset, ∃ e : OrderedFace 4 3,
      vertices (orderedFaceTuple e x) = t := by
  classical
  obtain ⟨K, ⟨hKV, hKcard, hKE⟩, htK⟩ := (hunique t ht).exists
  obtain ⟨L, htL, hLK, hLcard⟩ :=
    exists_subsuperset_card_eq htK (by have := hE t ht; omega : t.card ≤ 4) hKcard
  let x : Fin 4 → V := fun i =>
    ⟨L.orderEmbOfFin hLcard i, hKV (hLK (L.orderEmbOfFin_mem hLcard i))⟩
  have hxi : Function.Injective x := by
    intro i j hij
    exact (L.orderEmbOfFin hLcard).injective (congrArg (fun z : V => (z : ℕ)) hij)
  have hxL : vertices x = L := L.image_orderEmbOfFin_univ hLcard
  have hx : (pattern V E).IsOccurrence x := by
    intro e
    refine ⟨hxi.comp e.injective, hKE _ ?_ (vertices_card (hxi.comp e.injective))⟩
    exact (face_vertices_subset x e).trans (by simpa [hxL] using hLK)
  refine ⟨x, ((pattern V E).mem_occurrenceFinset x).mpr hx, ?_⟩
  exact three_subset_is_face hxi (by simpa [hxL] using htL) (hE t ht)

private theorem edge_card_le {E : Finset (Finset ℕ)}
    (hE : ∀ t ∈ E, t.card = 3)
    (hunique : ∀ t ∈ E, ∃! K, IsClique V E K ∧ t ⊆ K) :
    E.card ≤ Fintype.card (OrderedFace 4 3) * (pattern V E).occurrenceFinset.card := by
  classical
  have hsub : E ⊆ (pattern V E).occurrenceFinset.biUnion
      (fun x => univ.image fun e : OrderedFace 4 3 => vertices (orderedFaceTuple e x)) := by
    intro t ht
    obtain ⟨x, hx, e, he⟩ := edge_in_occurrence hE hunique ht
    exact mem_biUnion.mpr ⟨x, hx, mem_image.mpr ⟨e, mem_univ _, he⟩⟩
  calc
    E.card ≤ _ := card_le_card hsub
    _ ≤ ∑ x ∈ (pattern V E).occurrenceFinset,
        (univ.image fun e : OrderedFace 4 3 => vertices (orderedFaceTuple e x)).card :=
      card_biUnion_le
    _ ≤ ∑ _x ∈ (pattern V E).occurrenceFinset, Fintype.card (OrderedFace 4 3) := by
      apply sum_le_sum
      intro x _
      exact card_image_le.trans_eq (card_univ)
    _ = _ := by simp [mul_comm]

private theorem occurrence_card_le_deletions {E : Finset (Finset ℕ)}
    (hunique : ∀ t ∈ E, ∃! K, IsClique V E K ∧ t ⊆ K)
    (D : OrderedPattern.DeletionFamily (G := V) 4 3)
    (hD : (pattern V E).IsCover D) :
    (pattern V E).occurrenceFinset.card ≤ ∑ e, (D e).card := by
  classical
  have hsub : (pattern V E).occurrenceFinset ⊆
      univ.biUnion (fun e : OrderedFace 4 3 =>
        (pattern V E).occurrenceFinset.filter fun x => orderedFaceTuple e x ∈ D e) := by
    intro x hx
    obtain ⟨e, he⟩ := hD x hx
    exact mem_biUnion.mpr ⟨e, mem_univ _, mem_filter.mpr ⟨hx, he⟩⟩
  calc
    (pattern V E).occurrenceFinset.card ≤ _ := card_le_card hsub
    _ ≤ ∑ e : OrderedFace 4 3,
        ((pattern V E).occurrenceFinset.filter fun x => orderedFaceTuple e x ∈ D e).card :=
      card_biUnion_le
    _ ≤ _ := by
      apply sum_le_sum
      intro e _
      exact card_le_card_of_injOn (orderedFaceTuple e)
        (fun _ hx => (mem_filter.mp hx).2)
        (fun _ hx _ hy hxy => face_projection_injective hunique e
          (mem_filter.mp hx).1 (mem_filter.mp hy).1 hxy)

end FranklRodl

open FranklRodl Wikipedia.SzemeredisTheorem in
/-- Frankl–Rödl's unique-clique bound, proved from uniform hypergraph removal. -/
theorem frankl_roedl_theorem : Theorem_2_2 := by
  classical
  intro ε hε
  let M := Fintype.card (OrderedFace 4 3)
  have hM : (0 : ℝ) < M := by
    exact_mod_cast (Fintype.card_pos_iff.mpr
      ⟨Fin.succAboveOrderEmb (0 : Fin 4)⟩ : 0 < Fintype.card (OrderedFace 4 3))
  let η := ε / (2 * (M : ℝ) ^ 2)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨c, hc, hrem⟩ :=
    hasUniformOrderedPatternRemoval_sourceFull 4 2 (by omega) η hη
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (max (1 : ℝ) (1 / c))
  refine ⟨n₀, ?_⟩
  intro V E hV hE hunique
  have hn : (1 : ℝ) < V.card := by
    exact ((le_max_left 1 (1 / c)).trans_lt hn₀).trans_le (by exact_mod_cast hV)
  have hnpos : (0 : ℝ) < V.card := by linarith
  have hVpos : 0 < V.card := by exact_mod_cast hnpos
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hVpos
  let : Nonempty V := ⟨⟨v, hv⟩⟩
  have hu : ∀ t ∈ E, ∃! K, IsClique V E K ∧ t ⊆ K := by
    simpa only [IsClique, and_assoc] using hunique
  have hcount : (pattern V E).toWeighted.patternCount < c := by
    rw [OrderedPattern.toWeighted_patternCount_eq]
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Nat.cast_pow]
    have hupper : ((pattern V E).occurrenceFinset.card : ℝ) ≤ (V.card : ℝ) ^ 3 := by
      exact_mod_cast occurrence_card_le hu
    have hlarge : 1 / c < (V.card : ℝ) :=
      ((le_max_right 1 (1 / c)).trans_lt hn₀).trans_le (by exact_mod_cast hV)
    have hinv : 1 / (V.card : ℝ) < c := by
      rw [div_lt_iff₀ hnpos]
      have := (div_lt_iff₀ hc).mp hlarge
      nlinarith
    calc
      ((pattern V E).occurrenceFinset.card : ℝ) / (V.card : ℝ) ^ 4 ≤
          (V.card : ℝ) ^ 3 / (V.card : ℝ) ^ 4 :=
        div_le_div_of_nonneg_right hupper (by positivity)
      _ = 1 / (V.card : ℝ) := by field_simp
      _ < c := hinv
  obtain ⟨D, hcover, hsmall⟩ := hrem V (pattern V E) hcount
  have hD : ∀ e, ((D e).card : ℝ) ≤ η * (V.card : ℝ) ^ 3 := by
    intro e
    have h := hsmall e
    simp only [OrderedPattern.faceDeletionDensity, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_coe, Nat.cast_pow] at h
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < (V.card : ℝ) ^ 3)).mp h
  have hC : ((pattern V E).occurrenceFinset.card : ℝ) ≤
      (M : ℝ) * (η * (V.card : ℝ) ^ 3) := by
    calc
      ((pattern V E).occurrenceFinset.card : ℝ) ≤ ∑ e, ((D e).card : ℝ) := by
        exact_mod_cast occurrence_card_le_deletions hu D hcover
      _ ≤ ∑ _e : OrderedFace 4 3, η * (V.card : ℝ) ^ 3 :=
        sum_le_sum fun e _ => hD e
      _ = _ := by simp [M]
  have hEC : (E.card : ℝ) ≤ (M : ℝ) * (pattern V E).occurrenceFinset.card := by
    exact_mod_cast edge_card_le (fun t ht => (hE t ht).1) hu
  calc
    (E.card : ℝ) ≤ (M : ℝ) * ((M : ℝ) * (η * (V.card : ℝ) ^ 3)) :=
      hEC.trans (mul_le_mul_of_nonneg_left hC hM.le)
    _ = ε / 2 * (V.card : ℝ) ^ 3 := by dsimp [η]; field_simp
    _ < ε * (V.card : ℝ) ^ 3 :=
      mul_lt_mul_of_pos_right (by linarith) (pow_pos hnpos _)
