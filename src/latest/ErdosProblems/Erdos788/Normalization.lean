import ErdosProblems.Erdos788.GraphFormulation
import ErdosProblems.Erdos788.NormalizedGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact normalization for Erdős Problem 788

This production module proves that translating `I n` by `n + 1` identifies its vertex
type with `Fin (n - 1)`.  It also records the exact attainable sum interval,
the two palette translations, the resulting graph isomorphism, and the fact
that deleting colors which occur on no edge can only decrease the graph
score.
-/

namespace Erdos788

open Finset

/-- The constant term in the identity
`(n + 1 + x) + (n + 1 + y) = sumOffset n + x + y`. -/
def sumOffset (n : ℕ) : ℕ :=
  2 * n + 2

/-- Exact translation of `(n,2n) ∩ ℕ` to `0, ..., n - 2`.

The equivalence is valid for every `n`; for `n = 0,1` both types are empty.
-/
def vertexEquivFin (n : ℕ) : Vertex n ≃ Fin (n - 1) where
  toFun c := ⟨c.1 - (n + 1), by
    have hc := Finset.mem_Ioo.mp c.2
    omega⟩
  invFun x := ⟨n + 1 + x.1, by
    rw [show I n = Finset.Ioo n (2 * n) from rfl, Finset.mem_Ioo]
    omega⟩
  left_inv c := by
    apply Subtype.ext
    have hc := Finset.mem_Ioo.mp c.2
    simp only
    omega
  right_inv x := by
    apply Fin.ext
    simp only
    omega

@[simp]
theorem vertexEquivFin_apply_val (n : ℕ) (c : Vertex n) :
    (vertexEquivFin n c).1 = c.1 - (n + 1) :=
  rfl

@[simp]
theorem vertexEquivFin_symm_val (n : ℕ) (x : Fin (n - 1)) :
    ((vertexEquivFin n).symm x).1 = n + 1 + x.1 :=
  rfl

/-- Endpoint form of the vertex normalization: `c = n + 1 + x`. -/
theorem vertex_eq_offset_add_normalized (n : ℕ) (c : Vertex n) :
    c.1 = n + 1 + (vertexEquivFin n c).1 := by
  have hc := Finset.mem_Ioo.mp c.2
  simp only [vertexEquivFin_apply_val]
  omega

/-- Distinct (indeed arbitrary) pair sums translate by `2n+2`. -/
theorem vertex_sum_eq_normalized (n : ℕ) (c c' : Vertex n) :
    c.1 + c'.1 =
      sumOffset n + (vertexEquivFin n c).1 + (vertexEquivFin n c').1 := by
  rw [vertex_eq_offset_add_normalized n c,
    vertex_eq_offset_add_normalized n c']
  simp only [sumOffset]
  omega

/-- The proposition that `s` is the sum of two distinct elements of `Fin N`. -/
def IsAttainableNormalizedSum (N s : ℕ) : Prop :=
  ∃ x y : Fin N, x ≠ y ∧ x.1 + y.1 = s

/-- The exact interval of normalized sums supplied by distinct pairs. -/
def attainableNormalizedSums (N : ℕ) : Finset ℕ :=
  Finset.Icc 1 (2 * N - 3)

/-- Distinct elements of `Fin N` have precisely the sums
`1, ..., 2N - 3`.  The statement includes `N = 0,1`, where both sides are
empty. -/
theorem isAttainableNormalizedSum_iff_mem (N s : ℕ) :
    IsAttainableNormalizedSum N s ↔ s ∈ attainableNormalizedSums N := by
  rw [attainableNormalizedSums, Finset.mem_Icc]
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    have hx := x.2
    have hy := y.2
    have hval : x.1 ≠ y.1 := fun h ↦ hxy (Fin.ext h)
    omega
  · rintro ⟨hs1, hsmax⟩
    by_cases hsN : s < N
    · let x : Fin N := ⟨0, by omega⟩
      let y : Fin N := ⟨s, hsN⟩
      refine ⟨x, y, ?_, ?_⟩
      · intro hxy
        have := congrArg Fin.val hxy
        simp only [x, y] at this
        omega
      · simp [x, y]
    · let x : Fin N := ⟨N - 1, by omega⟩
      let y : Fin N := ⟨s - (N - 1), by omega⟩
      refine ⟨x, y, ?_, ?_⟩
      · intro hxy
        have := congrArg Fin.val hxy
        simp only [x, y] at this
        omega
      · simp only [x, y]
        omega

/-- Set-level wording of the exact attainable-sum result. -/
theorem mem_attainableNormalizedSums_iff (N s : ℕ) :
    s ∈ attainableNormalizedSums N ↔
      ∃ x y : Fin N, x ≠ y ∧ x.1 + y.1 = s := by
  exact (isAttainableNormalizedSum_iff_mem N s).symm

/-- The selected normalized colors: retain exactly the attainable normalized
sums whose translate by `2n+2` belongs to `B`. -/
def normalizePalette (n : ℕ) (B : Finset ℕ) : Finset ℕ :=
  (attainableNormalizedSums (n - 1)).filter
    fun s ↦ sumOffset n + s ∈ B

/-- Translate a normalized palette back by adding `2n+2`; normalized colors
outside the attainable interval are discarded. -/
def denormalizePalette (n : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (A.filter fun s ↦ s ∈ attainableNormalizedSums (n - 1)).image
    fun s ↦ sumOffset n + s

@[simp]
theorem mem_normalizePalette {n s : ℕ} {B : Finset ℕ} :
    s ∈ normalizePalette n B ↔
      s ∈ attainableNormalizedSums (n - 1) ∧ sumOffset n + s ∈ B := by
  simp [normalizePalette]

@[simp]
theorem mem_denormalizePalette {n b : ℕ} {A : Finset ℕ} :
    b ∈ denormalizePalette n A ↔
      ∃ s, s ∈ A ∧ s ∈ attainableNormalizedSums (n - 1) ∧
        sumOffset n + s = b := by
  simp only [denormalizePalette, Finset.mem_image, Finset.mem_filter]
  aesop

/-- Translating to original coordinates and back retains exactly the
attainable part of a normalized palette. -/
theorem normalizePalette_denormalizePalette (n : ℕ) (A : Finset ℕ) :
    normalizePalette n (denormalizePalette n A) =
      A.filter fun s ↦ s ∈ attainableNormalizedSums (n - 1) := by
  ext s
  simp only [mem_normalizePalette, mem_denormalizePalette, Finset.mem_filter]
  constructor
  · rintro ⟨hsatt, t, htA, htatt, heq⟩
    have hst : s = t := by omega
    simpa [hst] using! ⟨htA, htatt⟩
  · rintro ⟨hsA, hsatt⟩
    exact ⟨hsatt, s, hsA, hsatt, rfl⟩

/-- The part of `B` which is the sum of an actual pair of distinct original
vertices. -/
def activePalette (n : ℕ) (B : Finset ℕ) : Finset ℕ :=
  B.filter fun b ↦ ∃ c c' : Vertex n, c ≠ c' ∧ c.1 + c'.1 = b

@[simp]
theorem mem_activePalette {n b : ℕ} {B : Finset ℕ} :
    b ∈ activePalette n B ↔
      b ∈ B ∧ ∃ c c' : Vertex n, c ≠ c' ∧ c.1 + c'.1 = b := by
  simp [activePalette]

/-- Translating an original palette down and back gives precisely its active
part. -/
theorem denormalizePalette_normalizePalette (n : ℕ) (B : Finset ℕ) :
    denormalizePalette n (normalizePalette n B) = activePalette n B := by
  ext b
  simp only [mem_denormalizePalette, mem_normalizePalette, mem_activePalette]
  constructor
  · rintro ⟨s, ⟨hsatt, hsB⟩, _hsatt', hsb⟩
    refine ⟨?_, ?_⟩
    · simpa [hsb] using! hsB
    · obtain ⟨x, y, hxy, hsum⟩ :=
        (mem_attainableNormalizedSums_iff (n - 1) s).mp hsatt
      let c : Vertex n := (vertexEquivFin n).symm x
      let c' : Vertex n := (vertexEquivFin n).symm y
      refine ⟨c, c', ?_, ?_⟩
      · exact fun h ↦ hxy ((vertexEquivFin n).symm.injective h)
      · rw [vertex_sum_eq_normalized n c c']
        simp only [c, c', Equiv.apply_symm_apply]
        omega
  · rintro ⟨hbB, c, c', hcc', rfl⟩
    let x : Fin (n - 1) := vertexEquivFin n c
    let y : Fin (n - 1) := vertexEquivFin n c'
    have hxy : x ≠ y := fun h ↦ hcc' ((vertexEquivFin n).injective h)
    have hsatt : x.1 + y.1 ∈ attainableNormalizedSums (n - 1) :=
      (mem_attainableNormalizedSums_iff (n - 1) (x.1 + y.1)).mpr
        ⟨x, y, hxy, rfl⟩
    refine ⟨x.1 + y.1, ⟨hsatt, ?_⟩, hsatt, ?_⟩
    · rw [show sumOffset n + (x.1 + y.1) = c.1 + c'.1 by
          simpa [x, y, Nat.add_assoc] using!
            (vertex_sum_eq_normalized n c c').symm]
      exact hbB
    · simpa [x, y, Nat.add_assoc] using!
        (vertex_sum_eq_normalized n c c').symm

/-- Adding the fixed offset is injective, so denormalization preserves the
cardinality of the attainable part of a normalized palette. -/
theorem card_denormalizePalette (n : ℕ) (A : Finset ℕ) :
    (denormalizePalette n A).card =
      (A.filter fun s ↦ s ∈ attainableNormalizedSums (n - 1)).card := by
  rw [denormalizePalette]
  apply Finset.card_image_of_injective
  intro s t hst
  exact Nat.add_left_cancel hst

/-- The active original palette and its normalized translate have exactly
the same number of colors. -/
theorem card_activePalette_eq_card_normalizePalette
    (n : ℕ) (B : Finset ℕ) :
    (activePalette n B).card = (normalizePalette n B).card := by
  calc
    (activePalette n B).card =
        (denormalizePalette n (normalizePalette n B)).card :=
      congrArg Finset.card (denormalizePalette_normalizePalette n B).symm
    _ = ((normalizePalette n B).filter
          fun s ↦ s ∈ attainableNormalizedSums (n - 1)).card :=
      card_denormalizePalette n (normalizePalette n B)
    _ = (normalizePalette n B).card := by
      congr 1
      apply Finset.filter_eq_self.mpr
      intro s hs
      exact (mem_normalizePalette.mp hs).1

/-- The original palette graph is exactly the normalized sum graph, up to
the coordinate equivalence. -/
def paletteGraphIso (n : ℕ) (B : Finset ℕ) :
    paletteGraph n B ≃g sumGraph (n - 1) (normalizePalette n B) where
  toEquiv := vertexEquivFin n
  map_rel_iff' := by
    intro c c'
    rw [paletteGraph_adj, sumGraph_adj]
    constructor
    · rintro ⟨hxy, hmem⟩
      have hcc' : c ≠ c' := fun h ↦ hxy (congrArg (vertexEquivFin n) h)
      refine ⟨hcc', ?_⟩
      have htranslated := vertex_sum_eq_normalized n c c'
      rw [htranslated]
      simpa [Nat.add_assoc] using! (mem_normalizePalette.mp hmem).2
    · rintro ⟨hcc', hmem⟩
      have hxy : vertexEquivFin n c ≠ vertexEquivFin n c' :=
        fun h ↦ hcc' ((vertexEquivFin n).injective h)
      refine ⟨hxy, ?_⟩
      apply mem_normalizePalette.mpr
      constructor
      · exact (mem_attainableNormalizedSums_iff (n - 1)
          ((vertexEquivFin n c).1 + (vertexEquivFin n c').1)).mpr
          ⟨vertexEquivFin n c, vertexEquivFin n c', hxy, rfl⟩
      · rw [show sumOffset n +
            ((vertexEquivFin n c).1 + (vertexEquivFin n c').1) =
            c.1 + c'.1 by
              simpa [Nat.add_assoc] using!
                (vertex_sum_eq_normalized n c c').symm]
        exact hmem

/-- A finite graph isomorphism preserves the independence number. -/
theorem indepNum_eq_of_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    G.indepNum = H.indepNum := by
  apply le_antisymm
  · obtain ⟨S, hS⟩ := G.exists_isNIndepSet_indepNum
    let T : Finset W := S.map e.toEquiv.toEmbedding
    have hTind : H.IsIndepSet (T : Set W) := by
      intro u hu v hv huv hadj
      simp only [T, Finset.mem_coe, Finset.mem_map] at hu hv
      obtain ⟨x, hxS, rfl⟩ := hu
      obtain ⟨y, hyS, rfl⟩ := hv
      have hxy : x ≠ y := fun h ↦ huv (congrArg e h)
      exact hS.isIndepSet hxS hyS hxy (e.map_adj_iff.mp hadj)
    have hcard : T.card = S.card := Finset.card_map _
    rw [← hS.card_eq, ← hcard]
    exact hTind.card_le_indepNum
  · obtain ⟨T, hT⟩ := H.exists_isNIndepSet_indepNum
    let S : Finset V := T.map e.symm.toEquiv.toEmbedding
    have hSind : G.IsIndepSet (S : Set V) := by
      intro u hu v hv huv hadj
      simp only [S, Finset.mem_coe, Finset.mem_map] at hu hv
      obtain ⟨x, hxT, rfl⟩ := hu
      obtain ⟨y, hyT, rfl⟩ := hv
      have hxy : x ≠ y := fun h ↦ huv (congrArg e.symm h)
      exact hT.isIndepSet hxT hyT hxy (e.symm.map_adj_iff.mp hadj)
    have hcard : S.card = T.card := Finset.card_map _
    rw [← hT.card_eq, ← hcard]
    exact hSind.card_le_indepNum

/-- Exact independence-number equality between original and normalized
coordinates. -/
theorem indepNum_paletteGraph_eq_sumGraph (n : ℕ) (B : Finset ℕ) :
    (paletteGraph n B).indepNum =
      (sumGraph (n - 1) (normalizePalette n B)).indepNum :=
  indepNum_eq_of_iso (paletteGraphIso n B)

/-- Removing colors which label no edge does not change the graph. -/
theorem paletteGraph_activePalette (n : ℕ) (B : Finset ℕ) :
    paletteGraph n (activePalette n B) = paletteGraph n B := by
  ext c c'
  simp only [paletteGraph_adj, mem_activePalette]
  constructor
  · rintro ⟨hcc', hb, _⟩
    exact ⟨hcc', hb⟩
  · rintro ⟨hcc', hb⟩
    exact ⟨hcc', hb, c, c', hcc', rfl⟩

/-- The active palette is a subpalette of the original palette. -/
theorem activePalette_subset (n : ℕ) (B : Finset ℕ) :
    activePalette n B ⊆ B :=
  Finset.filter_subset _ _

/-- Deleting unattainable colors cannot increase the graph score: the graph
and its independence number stay fixed, while the palette cardinality can
only decrease. -/
theorem graphScore_activePalette_le (n : ℕ) (B : Finset ℕ) :
    graphScore n (activePalette n B) ≤ graphScore n B := by
  rw [graphScore, graphScore, paletteGraph_activePalette n B]
  exact Nat.add_le_add_right
    (Finset.card_le_card (activePalette_subset n B)) _

/-- Exact normalized form of the score after inactive colors are deleted. -/
theorem graphScore_activePalette_eq_normalized (n : ℕ) (B : Finset ℕ) :
    graphScore n (activePalette n B) =
      (normalizePalette n B).card +
        (sumGraph (n - 1) (normalizePalette n B)).indepNum := by
  rw [graphScore, paletteGraph_activePalette n B,
    indepNum_paletteGraph_eq_sumGraph n B,
    card_activePalette_eq_card_normalizePalette n B]

/-- Palette support remains inside `J n` after inactive colors are deleted. -/
theorem activePalette_subset_J {n : ℕ} {B : Finset ℕ} (hB : B ⊆ J n) :
    activePalette n B ⊆ J n :=
  (activePalette_subset n B).trans hB

end Erdos788
