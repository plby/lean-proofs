/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Formalization Project
-/
import Mathlib.Data.Finset.Interval
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic
import ErdosProblems.Erdos565.Rounding
import ErdosProblems.Erdos565.Numeric
import ErdosProblems.Erdos565.SpecialContainer
import ErdosProblems.Erdos565.SpecialContainerTheorem
import ErdosProblems.Erdos565.ExtensionAux
import ErdosProblems.Erdos565.Pullback
import ErdosProblems.Erdos565.ProjectionFibers

/-!
# The counting step in the extension lemma

This file isolates the last, purely finite, part of the extension lemma used in the proof of
Erdos problem 565.  The edges from a newly exposed vertex to an old vertex set `U` are encoded by
a subset `A ⊆ U`.  A subgraph of those edges is encoded by a second set `B ⊆ A`.  The associated
two-layer set contains `(u, 0)` for every non-neighbour and `(u, 1)` for every selected neighbour.

The specialised container theorem supplies a finite family of two-layer containers.  A container
which can contain a pattern with many selected neighbours must omit many vertices from its zero
layer.  Consequently the random neighbour set has to contain a fixed set of omitted vertices.
There are exactly `2 ^ (|U| - |F|)` subsets of `U` containing a fixed set `F`; the union bound below
is the complete probability calculation in the extension lemma.

The statements are deliberately phrased as cardinality inequalities.  Dividing by `2 ^ |U|`
gives the corresponding probability for the uniform random subset of `U`, without requiring a
second probability-space model.
-/

open scoped BigOperators

namespace Erdos565
namespace Extension

variable {V : Type*} [DecidableEq V]

/-- The reciprocal density used in the extension container theorem. -/
noncomputable def extensionQ (r : ℕ) : ℝ :=
  1 / (2 ^ 15 * (r : ℝ) ^ 2)

/-- The Janson density used throughout the ACDFM induction. -/
noncomputable def extensionP (r k : ℕ) : ℝ :=
  1 / (2 ^ 25 * (k : ℝ) ^ 2 * (r : ℝ) ^ 4)

/-- The radius in the one-vertex extension lemma. -/
noncomputable def extensionR (r k m : ℕ) : ℝ :=
  extensionP r k * m / (32 * r)

/-- The radius increment furnished by the specialised container theorem. -/
noncomputable def extensionEta (r k s : ℕ) : ℝ :=
  extensionP r k ^ 4 * (extensionQ r / 2) ^ (4 * s)

lemma extensionQ_pos {r : ℕ} (hr : 0 < r) : 0 < extensionQ r := by
  unfold extensionQ
  positivity

lemma extensionP_pos {r k : ℕ} (hr : 0 < r) (hk : 0 < k) :
    0 < extensionP r k := by
  unfold extensionP
  positivity

lemma extensionR_pos {r k m : ℕ} (hr : 0 < r) (hk : 0 < k) (hm : 0 < m) :
    0 < extensionR r k m := by
  unfold extensionR
  exact div_pos (mul_pos (extensionP_pos hr hk) (by exact_mod_cast hm)) (by positivity)

lemma extensionQ_lt_one_eighth {r : ℕ} (hr : 2 ≤ r) :
    extensionQ r < (1 : ℝ) / 8 := by
  unfold extensionQ
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  apply one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 8)
  nlinarith [sq_nonneg ((r : ℝ) - 2)]

lemma extensionP_le_special_threshold {r k s : ℕ}
    (hr : 2 ≤ r) (hk : 2 ≤ k) (hsposNat : 1 ≤ s) (hs : s + 1 ≤ k) :
    extensionP r k ≤ extensionQ r / (2 ^ 11 * (r : ℝ) * (s : ℝ) ^ 2) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hsle : (s : ℝ) ≤ k := by exact_mod_cast (by omega : s ≤ k)
  have hspos : (0 : ℝ) < s := by exact_mod_cast hsposNat
  unfold extensionP extensionQ
  rw [div_div]
  have hsquares : (s : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := by gcongr
  have hcore : (2 : ℝ) * (s : ℝ) ^ 2 ≤ (r : ℝ) * (k : ℝ) ^ 2 := by
    calc
      (2 : ℝ) * (s : ℝ) ^ 2 ≤ 2 * (k : ℝ) ^ 2 := by gcongr
      _ ≤ (r : ℝ) * (k : ℝ) ^ 2 := by
        gcongr
        exact_mod_cast hr
  apply one_div_le_one_div_of_le (by positivity)
  calc
    2 ^ 15 * (r : ℝ) ^ 2 * (2 ^ 11 * (r : ℝ) * (s : ℝ) ^ 2) =
        (2 ^ 25 * (r : ℝ) ^ 3) * (2 * (s : ℝ) ^ 2) := by ring
    _ ≤ (2 ^ 25 * (r : ℝ) ^ 3) * ((r : ℝ) * (k : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = 2 ^ 25 * (k : ℝ) ^ 2 * (r : ℝ) ^ 4 := by ring

/-- The concrete extension parameters satisfy the numerical hypotheses of the specialised
container theorem on a two-layer ground set of size `2m`. -/
lemma extension_parameterConditions {r k s m : ℕ} {R' : ℝ}
    (hr : 2 ≤ r) (hk : 2 ≤ k) (hspos : 1 ≤ s) (hs : s + 1 ≤ k)
    (hsm : s ≤ m) (hR'0 : 0 ≤ R')
    (hR' : R' ≤ extensionR r k m / 16) :
    SpecialContainer.ParameterConditions (2 * m) s r
      (extensionQ r) (extensionP r k) (extensionR r k m) R'
      (extensionEta r k s) := by
  refine ⟨by omega, hr, extensionQ_pos (by omega), extensionQ_lt_one_eighth hr,
    extensionP_pos (by omega) (by omega),
    extensionP_le_special_threshold hr hk hspos hs, ?_, hR'0, hR', rfl⟩
  unfold extensionR
  norm_num
  ring

/-- The scale assumption used in the main induction makes the radius increment at least one. -/
lemma one_le_extensionEta_mul_extensionR {r k s m : ℕ}
    (hr : 2 ≤ r) (hk : 2 ≤ k) (hs : s + 1 ≤ k)
    (hm : r ^ (300 * k) ≤ m) :
    1 ≤ extensionEta r k s * extensionR r k m := by
  simpa [extensionEta, extensionR, extensionP, extensionQ] using
    (Numeric.one_le_extension_eta_mul_radius hr hk hs hm)

/-- Exact two-fingerprint count at `q = 1/(2·(2^14 r²))`, absorbed into the small
exponential budget used by the extension lemma. -/
lemma extension_fingerprintCount_bound {r m : ℕ} (hr : 2 ≤ r) :
    let d := 2 ^ 14 * r ^ 2
    SpecialContainer.fingerprintCount (2 * m) ((2 * m) / d) *
        SpecialContainer.fingerprintCount (2 * m) ((2 * m) / (2 * d)) ≤
      2 ^ (m / (512 * r)) := by
  dsimp only
  let d := 2 ^ 14 * r ^ 2
  have hd : 0 < d := by simp [d]; positivity
  have h2d : 0 < 2 * d := Nat.mul_pos (by omega) hd
  calc
    SpecialContainer.fingerprintCount (2 * m) ((2 * m) / d) *
        SpecialContainer.fingerprintCount (2 * m) ((2 * m) / (2 * d))
        ≤ (8 * d) ^ ((2 * m) / d) *
            (8 * (2 * d)) ^ ((2 * m) / (2 * d)) :=
      Nat.mul_le_mul
        (BinomialBounds.partialChooseSum_floor_le (2 * m) d hd)
        (BinomialBounds.partialChooseSum_floor_le (2 * m) (2 * d) h2d)
    _ ≤ (16 * d) ^ ((2 * m) / d) *
          (16 * d) ^ ((2 * m) / (2 * d)) := by
      apply Nat.mul_le_mul
      · exact pow_le_pow_left' (by omega) _
      · rw [show 8 * (2 * d) = 16 * d by omega]
    _ = (16 * d) ^ ((2 * m) / d + (2 * m) / (2 * d)) := by
      rw [pow_add]
    _ ≤ 2 ^ (m / (512 * r)) := by
      simpa [d] using (Numeric.extension_container_count (r := r) (m := m) hr)

/-- The real cutoffs appearing in the specialised theorem are exactly the two natural
floor-divisions used in the finite fingerprint estimate. -/
lemma extensionQ_floor_cutoffs (r m : ℕ) :
    let d := 2 ^ 14 * r ^ 2
    ⌊extensionQ r * (2 * m : ℕ)⌋₊ = (2 * m) / (2 * d) ∧
      ⌊2 * extensionQ r * (2 * m : ℕ)⌋₊ = (2 * m) / d := by
  dsimp only
  let d := 2 ^ 14 * r ^ 2
  constructor
  · rw [show extensionQ r * (2 * m : ℕ) =
        ((2 * m : ℕ) : ℝ) / (2 * d : ℕ) by
      simp [extensionQ, d]
      ring]
    exact Nat.floor_div_eq_div (K := ℝ) (2 * m) (2 * d)
  · rw [show 2 * extensionQ r * (2 * m : ℕ) =
        ((2 * m : ℕ) : ℝ) / (d : ℕ) by
      simp [extensionQ, d]
      ring]
    exact Nat.floor_div_eq_div (K := ℝ) (2 * m) d

section GraphStars

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- Neighbours of the distinguished new vertex in a graph on `Option U`. -/
noncomputable def graphStar (G : SimpleGraph (Option U)) : Finset U := by
  classical
  exact Finset.univ.filter fun u ↦ G.Adj (some u) none

@[simp] theorem mem_graphStar {G : SimpleGraph (Option U)} {u : U} :
    u ∈ graphStar G ↔ G.Adj (some u) none := by
  classical
  simp [graphStar]

theorem graphStar_mono {G' G : SimpleGraph (Option U)} (hG : G' ≤ G) :
    graphStar G' ⊆ graphStar G := by
  intro u hu
  exact mem_graphStar.mpr (hG (mem_graphStar.mp hu))

end GraphStars

/-- The vertices of `U` which occur in layer `b` of a two-layer set. -/
def taggedLayer (U : Finset V) (b : Fin 2) (X : Finset (V × Fin 2)) : Finset V :=
  U.filter fun u ↦ (u, b) ∈ X

@[simp] theorem mem_taggedLayer {U : Finset V} {b : Fin 2} {X : Finset (V × Fin 2)}
    {u : V} :
    u ∈ taggedLayer U b X ↔ u ∈ U ∧ (u, b) ∈ X := by
  simp [taggedLayer]

/-- The points omitted from the zero layer of a container. -/
def zeroOmissions (U : Finset V) (X : Finset (V × Fin 2)) : Finset V :=
  U \ taggedLayer U 0 X

@[simp] theorem mem_zeroOmissions {U : Finset V} {X : Finset (V × Fin 2)} {u : V} :
    u ∈ zeroOmissions U X ↔ u ∈ U ∧ (u, (0 : Fin 2)) ∉ X := by
  constructor
  · simp only [zeroOmissions, Finset.mem_sdiff, mem_taggedLayer, not_and]
    rintro ⟨hu, hnot⟩
    exact ⟨hu, hnot hu⟩
  · rintro ⟨hu, hnot⟩
    exact Finset.mem_sdiff.mpr ⟨hu, by simpa [mem_taggedLayer, hu] using hnot⟩

theorem zeroOmissions_subset (U : Finset V) (X : Finset (V × Fin 2)) :
    zeroOmissions U X ⊆ U :=
  Finset.sdiff_subset

/-- The two-layer set associated to an ambient star `A` and a selected substar `B`.

The intended hypotheses are `B ⊆ A ⊆ U`.  They are kept outside the definition because the
two elementary containment consequences below do not need all of them. -/
def starCode (U A B : Finset V) : Finset (V × Fin 2) :=
  (U \ A).image (fun u ↦ (u, (0 : Fin 2))) ∪
    B.image (fun u ↦ (u, (1 : Fin 2)))

theorem extensionIota_eq_starCode {U : Type*} [Fintype U] [DecidableEq U]
    (G' G : SimpleGraph (Option U)) :
    extensionIota G' G =
      starCode (Finset.univ : Finset U) (graphStar G) (graphStar G') := by
  classical
  ext z
  rcases z with ⟨u, b⟩
  fin_cases b <;> simp [starCode, SimpleGraph.adj_comm]

/-- Pushing a hypergraph along an injective vertex map preserves the Janson property.  This is
derived from the already formalized pullback theorem by using an inverse on the range. -/
theorem isJanson_map_of_injective {S T : Type*}
    [Fintype S] [Nonempty S] [DecidableEq S] [Fintype T] [DecidableEq T]
    (K : Hypergraph S) (f : S → T) (hf : Function.Injective f)
    {p R : ℝ} (hp : 0 < p) (hK : K.IsJanson p R) :
    (K.map f).IsJanson p R := by
  classical
  let g : T → S := Function.invFun f
  have hleft : Function.LeftInverse g f := Function.leftInverse_invFun hf
  have hinj : Hypergraph.EdgewiseInjective (K.map f) g := by
    intro E hE
    obtain ⟨D, hDK, rfl⟩ := Hypergraph.mem_map.mp hE
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    have hab : a = b := by simpa [g, hleft a, hleft b] using hxy
    exact congrArg f hab
  apply Hypergraph.IsJanson.pullback hinj hp
  rw [Hypergraph.map_comp]
  have hcomp : g ∘ f = id := funext hleft
  rw [hcomp, Hypergraph.map_id]
  exact hK

/-- An old copy remains a copy after the old host is embedded into the `some` part of a
one-vertex extension.  The statement is deliberately about the current pair of graphs, so it
can be applied after rewriting their old parts to the fixed graphs exposed earlier. -/
theorem image_some_mem_copyHypergraph_of_mem_oldPart
    {A U : Type*} [Fintype A] [Fintype U] [DecidableEq U]
    (target : SimpleGraph A) (G' G : SimpleGraph (Option U))
    {L : Finset U}
    (hL : L ∈ copyHypergraph target (oldPart G') (oldPart G)) :
    L.image some ∈ copyHypergraph target G' G := by
  classical
  obtain ⟨⟨e⟩, heq⟩ :=
    (mem_copyHypergraph target (oldPart G') (oldPart G) L).mp hL
  let j : (oldPart G').induce (↑L : Set U) ↪g G' :=
    { toFun := fun x ↦ some x.1
      inj' := fun x y hxy ↦ Subtype.ext (Option.some.inj hxy)
      map_rel_iff' := by
        intro x y
        change G'.Adj (some x.1) (some y.1) ↔ G'.Adj (some x.1) (some y.1)
        rfl }
  have hrange : Set.range j = (↑(L.image some) : Set (Option U)) := by
    ext z
    change (∃ x, j x = z) ↔ z ∈ L.image some
    constructor
    · rintro ⟨x, rfl⟩
      exact Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩
    · intro hz
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
      exact ⟨⟨u, hu⟩, rfl⟩
  apply (mem_copyHypergraph target G' G (L.image some)).mpr
  constructor
  · refine ⟨e.trans ?_⟩
    rw [← hrange]
    exact j.isoInduceRange
  · apply SimpleGraph.ext
    funext x y
    apply propext
    rcases x with ⟨x, hx⟩
    rcases y with ⟨y, hy⟩
    obtain ⟨u, huL, hux⟩ := Finset.mem_image.mp hx
    obtain ⟨w, hwL, hwy⟩ := Finset.mem_image.mp hy
    subst x
    subst y
    change ((oldPart G').induce (↑L : Set U)).Adj ⟨u, huL⟩ ⟨w, hwL⟩ ↔
      ((oldPart G).induce (↑L : Set U)).Adj ⟨u, huL⟩ ⟨w, hwL⟩
    rw [heq]

/-- The mapped old-copy family is contained in the full copy family of every one-vertex
extension having those old parts. -/
theorem map_oldCopies_subset_fullCopies
    {A U : Type*} [Fintype A] [Fintype U] [DecidableEq U]
    (target : SimpleGraph A) (oldColor oldAmbient : SimpleGraph U)
    (G' G : SimpleGraph (Option U))
    (hG' : oldPart G' = oldColor) (hG : oldPart G = oldAmbient) :
    (copyHypergraph target oldColor oldAmbient).map some ⊆
      copyHypergraph target G' G := by
  intro E hE
  obtain ⟨L, hL, rfl⟩ := Hypergraph.mem_map.mp hE
  apply image_some_mem_copyHypergraph_of_mem_oldPart target G' G
  simpa [hG', hG] using hL

/-- The auxiliary two-layer hypergraph depends only on the old parts of its two graph
arguments. -/
theorem extensionAuxHypergraph_eq_of_oldPart_eq
    {A U : Type*} [Fintype A] [DecidableEq A] [Fintype U] [DecidableEq U]
    (target : SimpleGraph A) (root : A)
    (G₁' G₁ G₂' G₂ : SimpleGraph (Option U))
    (hcolor : oldPart G₁' = oldPart G₂')
    (hambient : oldPart G₁ = oldPart G₂) :
    extensionAuxHypergraph target root G₁' G₁ =
      extensionAuxHypergraph target root G₂' G₂ := by
  classical
  ext E
  simp only [mem_extensionAuxHypergraph]
  change
    (∃ e : deleteVertex target root ↪g oldPart G₁,
      (∀ {x y}, (deleteVertex target root).Adj x y →
        (oldPart G₁').Adj (e x) (e y)) ∧
      E = extensionEdge target root e.toEmbedding) ↔
    (∃ e : deleteVertex target root ↪g oldPart G₂,
      (∀ {x y}, (deleteVertex target root).Adj x y →
        (oldPart G₂').Adj (e x) (e y)) ∧
      E = extensionEdge target root e.toEmbedding)
  rw [hcolor, hambient]

/-- Both parts of the local extension union are genuine full-target copies for the graph
extension which produced its two-layer code. -/
theorem extensionUnion_subset_fullCopies
    {A U : Type*} [Fintype A] [DecidableEq A] [Fintype U] [DecidableEq U]
    (target : SimpleGraph A) (root : A)
    (baseColor baseAmbient G' G : SimpleGraph (Option U))
    (hle : G' ≤ G)
    (hcolor : oldPart G' = oldPart baseColor)
    (hambient : oldPart G = oldPart baseAmbient) :
    SpecialContainer.extensionUnion (fun z : U × Fin 2 ↦ some z.1) none
        (extensionAuxHypergraph target root baseColor baseAmbient)
        ((copyHypergraph target (oldPart baseColor) (oldPart baseAmbient)).map some)
        (extensionIota G' G) ⊆
      copyHypergraph target G' G := by
  classical
  intro E hE
  rcases Finset.mem_union.mp hE with hnew | hold
  · obtain ⟨L, hL, rfl⟩ := SpecialContainer.mem_coneAt.mp hnew
    obtain ⟨D, hD, rfl⟩ := Hypergraph.mem_map.mp hL
    have hDr := Hypergraph.mem_restrict.mp hD
    apply cone_image_mem_copyHypergraph_of_subset_iota target root G' G hle
    · rw [extensionAuxHypergraph_eq_of_oldPart_eq target root G' G
          baseColor baseAmbient hcolor hambient]
      exact hDr.1
    · exact hDr.2
  · exact map_oldCopies_subset_fullCopies target
      (oldPart baseColor) (oldPart baseAmbient) G' G hcolor hambient hold

/-- The forget-the-layer projection has the two structural properties required by the
specialised container theorem.  Its fibres have size at most two globally, and it is injective
on every auxiliary edge because an embedded target vertex has a unique required layer. -/
theorem extensionAux_projectionConditions
    {A U : Type*} [Fintype A] [DecidableEq A]
    [Fintype U] [DecidableEq U]
    (target : SimpleGraph A) (root : A)
    (baseColor baseAmbient : SimpleGraph (Option U)) :
    SpecialContainer.ProjectionConditions (fun z : U × Fin 2 ↦ some z.1)
      (extensionAuxHypergraph target root baseColor baseAmbient) := by
  classical
  constructor
  · intro L
    let π : U × Fin 2 → Option U := fun z ↦ some z.1
    have hfibers : ProjectionFibers.FibersBounded π 2 := by
      intro ou
      let fiber := (Finset.univ : Finset (U × Fin 2)).filter fun z ↦ π z = ou
      have hinj : Set.InjOn Prod.snd (↑fiber : Set (U × Fin 2)) := by
        intro x hx y hy hxy
        have hxou : π x = ou := (Finset.mem_filter.mp hx).2
        have hyou : π y = ou := (Finset.mem_filter.mp hy).2
        have hfst : x.1 = y.1 := Option.some.inj (hxou.trans hyou.symm)
        exact Prod.ext hfst hxy
      calc
        fiber.card = (fiber.image Prod.snd).card :=
          (Finset.card_image_iff.mpr hinj).symm
        _ ≤ (Finset.univ : Finset (Fin 2)).card :=
          Finset.card_le_card (Finset.subset_univ _)
        _ = 2 := by simp
    exact ProjectionFibers.card_le_mul_card_image π L 2 (hfibers.on_finset L)
  · intro E hE
    obtain ⟨e, _hmono, rfl⟩ :=
      (mem_extensionAuxHypergraph target root baseColor baseAmbient E).mp hE
    rw [image_some_fst_eq_image_some_layerProjection,
      layerProjection_extensionEdge,
      Finset.card_image_of_injective _ (Option.some_injective U)]
    simp [embeddingImage, card_extensionEdge]

/-- Uniformity of the extension auxiliary hypergraph. -/
theorem extensionAux_isUniform
    {A U : Type*} [Fintype A] [DecidableEq A]
    [Fintype U] [DecidableEq U]
    (target : SimpleGraph A) (root : A)
    (baseColor baseAmbient : SimpleGraph (Option U)) :
    Hypergraph.IsUniform (extensionAuxHypergraph target root baseColor baseAmbient)
      (Fintype.card (DeletedVertices root)) := by
  intro E hE
  exact card_eq_of_mem_extensionAuxHypergraph target root baseColor baseAmbient hE

/-- Uniformity of old full-target copies after embedding them into the old part of the
one-vertex host. -/
theorem map_oldCopies_isUniform
    {A U : Type*} [Fintype A] [Fintype U] [DecidableEq U]
    (target : SimpleGraph A) (oldColor oldAmbient : SimpleGraph U) :
    Hypergraph.IsUniform ((copyHypergraph target oldColor oldAmbient).map some)
      (Fintype.card A) := by
  classical
  intro E hE
  obtain ⟨L, hL, rfl⟩ := Hypergraph.mem_map.mp hE
  rw [Finset.card_image_of_injective _ (Option.some_injective U)]
  exact card_eq_of_mem_copyHypergraph target oldColor oldAmbient hL

@[simp] theorem extensionProjection_ne_newVertex
    {U : Type*} (z : U × Fin 2) : (some z.1 : Option U) ≠ none := by
  simp

section GraphBadEvent

variable {A U : Type*} [Fintype A] [DecidableEq A]
  [Fintype U] [DecidableEq U]

/-- The exact one-new-vertex bad event, expressed as a family of ambient star patterns.

The old ambient and colour graphs are fixed.  For a star `S`, membership means that there are
extensions `G' ≤ G` with ambient star `S`, a selected colour star of size at least `d`, and a
non-Janson full-target copy hypergraph. -/
noncomputable def graphExtensionBadStars
    (target : SimpleGraph A) (oldColor oldAmbient : SimpleGraph U)
    (p badRadius : ℝ) (d : ℕ) : Finset (Finset U) := by
  classical
  exact (Finset.univ : Finset U).powerset.filter fun S ↦
    ∃ (G' G : SimpleGraph (Option U)),
      G' ≤ G ∧ oldPart G' = oldColor ∧ oldPart G = oldAmbient ∧
        graphStar G = S ∧ d ≤ (graphStar G').card ∧
          ¬ (copyHypergraph target G' G).IsJanson p badRadius

@[simp] theorem mem_graphExtensionBadStars
    {target : SimpleGraph A} {oldColor oldAmbient : SimpleGraph U}
    {p badRadius : ℝ} {d : ℕ} {S : Finset U} :
    S ∈ graphExtensionBadStars target oldColor oldAmbient p badRadius d ↔
      S ⊆ Finset.univ ∧
        ∃ (G' G : SimpleGraph (Option U)),
          G' ≤ G ∧ oldPart G' = oldColor ∧ oldPart G = oldAmbient ∧
            graphStar G = S ∧ d ≤ (graphStar G').card ∧
              ¬ (copyHypergraph target G' G).IsJanson p badRadius := by
  classical
  simp [graphExtensionBadStars]

end GraphBadEvent

theorem selected_subset_oneLayer {U A B : Finset V} {X : Finset (V × Fin 2)}
    (hBU : B ⊆ U) (hcode : starCode U A B ⊆ X) :
    B ⊆ taggedLayer U 1 X := by
  intro u hu
  rw [mem_taggedLayer]
  refine ⟨hBU hu, hcode ?_⟩
  simp [starCode, hu]

theorem zeroOmissions_subset_ambientStar {U A B : Finset V}
    {X : Finset (V × Fin 2)} (hcode : starCode U A B ⊆ X) :
    zeroOmissions U X ⊆ A := by
  intro u hu
  rw [mem_zeroOmissions] at hu
  by_contra huA
  exact hu.2 (hcode (by simp [starCode, hu.1, huA]))

/-- The full two-layer lift of `U`. -/
def twoLayerUniverse (U : Finset V) : Finset (V × Fin 2) :=
  U.product Finset.univ

theorem taggedLayer_union_image {U : Finset V} {X : Finset (V × Fin 2)}
    (hX : X ⊆ twoLayerUniverse U) :
    (taggedLayer U 0 X).image (fun u ↦ (u, (0 : Fin 2))) ∪
        (taggedLayer U 1 X).image (fun u ↦ (u, (1 : Fin 2))) = X := by
  ext z
  rcases z with ⟨u, b⟩
  fin_cases b
  · constructor
    · simpa [taggedLayer]
    · intro hz
      change (u, (0 : Fin 2)) ∈ X at hz
      have hu : u ∈ U := by
        have := hX hz
        simpa [twoLayerUniverse] using this
      simp [taggedLayer, hz, hu]
  · constructor
    · simpa [taggedLayer]
    · intro hz
      change (u, (1 : Fin 2)) ∈ X at hz
      have hu : u ∈ U := by
        have := hX hz
        simpa [twoLayerUniverse] using this
      simp [taggedLayer, hz, hu]

theorem taggedLayer_card_add {U : Finset V} {X : Finset (V × Fin 2)}
    (hX : X ⊆ twoLayerUniverse U) :
    (taggedLayer U 0 X).card + (taggedLayer U 1 X).card = X.card := by
  let f₀ : V → V × Fin 2 := fun u ↦ (u, (0 : Fin 2))
  let f₁ : V → V × Fin 2 := fun u ↦ (u, (1 : Fin 2))
  have hf₀ : Function.Injective f₀ := by
    intro x y h
    exact congrArg Prod.fst h
  have hf₁ : Function.Injective f₁ := by
    intro x y h
    exact congrArg Prod.fst h
  have hdis : Disjoint ((taggedLayer U 0 X).image f₀)
      ((taggedLayer U 1 X).image f₁) := by
    rw [Finset.disjoint_left]
    intro z hz₀ hz₁
    rcases Finset.mem_image.mp hz₀ with ⟨u, _, rfl⟩
    rcases Finset.mem_image.mp hz₁ with ⟨v, _, hv⟩
    simp [f₀, f₁] at hv
  calc
    (taggedLayer U 0 X).card + (taggedLayer U 1 X).card =
        ((taggedLayer U 0 X).image f₀).card +
          ((taggedLayer U 1 X).image f₁).card := by
            rw [Finset.card_image_of_injective _ hf₀,
              Finset.card_image_of_injective _ hf₁]
    _ = (((taggedLayer U 0 X).image f₀) ∪
          ((taggedLayer U 1 X).image f₁)).card :=
      (Finset.card_union_of_disjoint hdis).symm
    _ = X.card := by
      rw [show f₀ = (fun u ↦ (u, (0 : Fin 2))) from rfl,
        show f₁ = (fun u ↦ (u, (1 : Fin 2))) from rfl,
        taggedLayer_union_image hX]

theorem card_zeroOmissions (U : Finset V) (X : Finset (V × Fin 2)) :
    (zeroOmissions U X).card = U.card - (taggedLayer U 0 X).card := by
  exact Finset.card_sdiff_of_subset (Finset.filter_subset _ _)

/-- The cardinality calculation behind the zero-layer omission conclusion.

`Y` is the large subset supplied by the specialised container theorem.  Its two projections have
intersection of size at most `w`, and at most `l` points of `X` were deleted.  If the one-layer
threshold `d` exceeds `a + w + l`, then `X` omits at least `a` zero-layer points. -/
theorem zeroOmissions_card_lower {U : Finset V} {X Y : Finset (V × Fin 2)}
    {d a w l : ℕ} (hX : X ⊆ twoLayerUniverse U) (hY : Y ⊆ twoLayerUniverse U)
    (hd : d ≤ (taggedLayer U 1 X).card)
    (hloss : X.card ≤ Y.card + l)
    (hinter : ((taggedLayer U 0 Y) ∩ taggedLayer U 1 Y).card ≤ w)
    (hbudget : a + w + l ≤ d) :
    a ≤ (zeroOmissions U X).card := by
  have hunion : (taggedLayer U 0 Y ∪ taggedLayer U 1 Y).card ≤ U.card := by
    apply Finset.card_le_card
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu <;>
      exact (mem_taggedLayer.mp hu).1
  have hYcard : Y.card ≤ U.card + w := by
    rw [← taggedLayer_card_add hY]
    rw [← Finset.card_union_add_card_inter]
    exact Nat.add_le_add hunion hinter
  have hXcard : X.card ≤ U.card + w + l :=
    hloss.trans (Nat.add_le_add_right hYcard l)
  have hzero : (taggedLayer U 0 X).card + a ≤ U.card := by
    have hsum := taggedLayer_card_add hX
    omega
  rw [card_zeroOmissions]
  exact Nat.le_sub_of_add_le (by omega)

/-- The extension configurations captured by a family of containers.

Membership says that `A` is an ambient star for which some selected substar `B` has at least `d`
vertices and whose two-layer code lies in a container. -/
def extensionBadStars (U : Finset V) (containers : Finset (Finset (V × Fin 2)))
    (d : ℕ) : Finset (Finset V) :=
  U.powerset.filter fun A ↦
    ∃ B ⊆ U, B ⊆ A ∧ d ≤ B.card ∧
      ∃ X ∈ containers, starCode U A B ⊆ X

@[simp] theorem mem_extensionBadStars {U : Finset V}
    {containers : Finset (Finset (V × Fin 2))} {d : ℕ} {A : Finset V} :
    A ∈ extensionBadStars U containers d ↔
      A ⊆ U ∧ ∃ B ⊆ U, B ⊆ A ∧ d ≤ B.card ∧
        ∃ X ∈ containers, starCode U A B ⊆ X := by
  simp [extensionBadStars]

/-- Any mechanism which places each bad extension set `extensionIota G' G` in a member of a
fixed container family turns the graph-facing bad event into `extensionBadStars`. -/
theorem graphExtensionBadStars_subset_of_capture
    {A U : Type*} [Fintype A] [DecidableEq A] [Fintype U] [DecidableEq U]
    (target : SimpleGraph A) (oldColor oldAmbient : SimpleGraph U)
    (p badRadius : ℝ) (d : ℕ)
    (containers : Finset (Finset (U × Fin 2)))
    (capture : ∀ (G' G : SimpleGraph (Option U)),
      G' ≤ G → oldPart G' = oldColor → oldPart G = oldAmbient →
      d ≤ (graphStar G').card →
      ¬ (copyHypergraph target G' G).IsJanson p badRadius →
      ∃ X ∈ containers, extensionIota G' G ⊆ X) :
    graphExtensionBadStars target oldColor oldAmbient p badRadius d ⊆
      extensionBadStars (Finset.univ : Finset U) containers d := by
  intro S hS
  rw [mem_graphExtensionBadStars] at hS
  rcases hS with ⟨_, G', G, hle, hOldColor, hOldAmbient, rfl, hdegree, hbad⟩
  rw [mem_extensionBadStars]
  obtain ⟨X, hXC, hiota⟩ :=
    capture G' G hle hOldColor hOldAmbient hdegree hbad
  refine ⟨Finset.subset_univ _, graphStar G', Finset.subset_univ _,
    graphStar_mono hle, hdegree, X, hXC, ?_⟩
  rw [← extensionIota_eq_starCode]
  exact hiota

/-- The larger event used for the union bound: the one-layer condition selects relevant
containers, while every zero-layer omission is forced to be an ambient neighbour. -/
def containerStarEvent (U : Finset V) (containers : Finset (Finset (V × Fin 2)))
    (d : ℕ) : Finset (Finset V) :=
  U.powerset.filter fun A ↦
    ∃ X ∈ containers,
      d ≤ (taggedLayer U 1 X).card ∧ zeroOmissions U X ⊆ A

@[simp] theorem mem_containerStarEvent {U : Finset V}
    {containers : Finset (Finset (V × Fin 2))} {d : ℕ} {A : Finset V} :
    A ∈ containerStarEvent U containers d ↔
      A ⊆ U ∧ ∃ X ∈ containers,
        d ≤ (taggedLayer U 1 X).card ∧ zeroOmissions U X ⊆ A := by
  simp [containerStarEvent]

theorem extensionBadStars_subset_containerStarEvent (U : Finset V)
    (containers : Finset (Finset (V × Fin 2))) (d : ℕ) :
    extensionBadStars U containers d ⊆ containerStarEvent U containers d := by
  intro A hA
  rw [mem_extensionBadStars] at hA
  rw [mem_containerStarEvent]
  rcases hA with ⟨hAU, B, hBU, hBA, hdB, X, hXC, hcode⟩
  refine ⟨hAU, X, hXC, ?_, zeroOmissions_subset_ambientStar hcode⟩
  exact hdB.trans (Finset.card_le_card (selected_subset_oneLayer hBU hcode))

/-- The ambient stars containing all zero-layer omissions of one fixed container are precisely a
finite interval in the Boolean lattice. -/
theorem stars_for_fixed_container (U : Finset V) (X : Finset (V × Fin 2)) :
    (U.powerset.filter fun A ↦ zeroOmissions U X ⊆ A) =
      Finset.Icc (zeroOmissions U X) U := by
  ext A
  simp [and_comm]

theorem card_stars_for_fixed_container (U : Finset V) (X : Finset (V × Fin 2)) :
    (U.powerset.filter fun A ↦ zeroOmissions U X ⊆ A).card =
      2 ^ (U.card - (zeroOmissions U X).card) := by
  rw [stars_for_fixed_container]
  exact Finset.card_Icc_finset (zeroOmissions_subset U X)

/-- Union bound for extension patterns.

If every relevant container omits at least `a` zero-layer vertices, then the number of bad stars
is at most the number of containers times `2 ^ (|U| - a)`. -/
theorem card_containerStarEvent_le (U : Finset V)
    (containers : Finset (Finset (V × Fin 2))) (d a : ℕ)
    (homit : ∀ X ∈ containers,
      d ≤ (taggedLayer U 1 X).card → a ≤ (zeroOmissions U X).card) :
    (containerStarEvent U containers d).card ≤
      containers.card * 2 ^ (U.card - a) := by
  let relevant : Finset (Finset (V × Fin 2)) :=
    containers.filter fun X ↦ d ≤ (taggedLayer U 1 X).card
  let stars : Finset (V × Fin 2) → Finset (Finset V) := fun X ↦
    Finset.Icc (zeroOmissions U X) U
  have hsub : containerStarEvent U containers d ⊆ relevant.biUnion stars := by
    intro A hA
    rw [mem_containerStarEvent] at hA
    rcases hA with ⟨hAU, X, hXC, hdX, hforce⟩
    rw [Finset.mem_biUnion]
    exact ⟨X, by simp [relevant, hXC, hdX], by simpa [stars] using And.intro hforce hAU⟩
  calc
    (containerStarEvent U containers d).card
        ≤ (relevant.biUnion stars).card := Finset.card_le_card hsub
    _ ≤ ∑ X ∈ relevant, (stars X).card := Finset.card_biUnion_le
    _ ≤ ∑ _X ∈ relevant, 2 ^ (U.card - a) := by
      apply Finset.sum_le_sum
      intro X hXrel
      have hXC : X ∈ containers := (Finset.mem_filter.mp hXrel).1
      have hdX : d ≤ (taggedLayer U 1 X).card := (Finset.mem_filter.mp hXrel).2
      rw [Finset.card_Icc_finset (zeroOmissions_subset U X)]
      exact pow_le_pow_right' (by omega : 1 ≤ (2 : ℕ))
        (Nat.sub_le_sub_left (homit X hXC hdX) U.card)
    _ = relevant.card * 2 ^ (U.card - a) := by simp
    _ ≤ containers.card * 2 ^ (U.card - a) := by
      exact Nat.mul_le_mul_right _ (Finset.card_le_card (Finset.filter_subset _ _))

/-- Cardinal form of the extension probability bound. -/
theorem card_extensionBadStars_le (U : Finset V)
    (containers : Finset (Finset (V × Fin 2))) (d a : ℕ)
    (homit : ∀ X ∈ containers,
      d ≤ (taggedLayer U 1 X).card → a ≤ (zeroOmissions U X).card) :
    (extensionBadStars U containers d).card ≤
      containers.card * 2 ^ (U.card - a) := by
  exact (Finset.card_le_card (extensionBadStars_subset_containerStarEvent U containers d)).trans
    (card_containerStarEvent_le U containers d a homit)

/-- Uniform probability of a family of subsets of `U`, represented as its cardinality divided by
the `2 ^ |U|` equally likely subsets. -/
noncomputable def uniformStarProbability (U : Finset V) (event : Finset (Finset V)) : ℝ :=
  event.card / (2 : ℝ) ^ U.card

theorem uniformStarProbability_nonneg (U : Finset V) (event : Finset (Finset V)) :
    0 ≤ uniformStarProbability U event := by
  exact div_nonneg (Nat.cast_nonneg _) (by positivity)

/-- The cardinal union bound, after division by the number of all stars. -/
theorem uniformStarProbability_extensionBadStars_le (U : Finset V)
    (containers : Finset (Finset (V × Fin 2))) (d a : ℕ) (ha : a ≤ U.card)
    (homit : ∀ X ∈ containers,
      d ≤ (taggedLayer U 1 X).card → a ≤ (zeroOmissions U X).card) :
    uniformStarProbability U (extensionBadStars U containers d) ≤
      containers.card / (2 : ℝ) ^ a := by
  have hcard := card_extensionBadStars_le U containers d a homit
  have hcardReal : ((extensionBadStars U containers d).card : ℝ) ≤
      containers.card * (2 : ℝ) ^ (U.card - a) := by
    exact_mod_cast hcard
  have hpow : (2 : ℝ) ^ U.card = (2 : ℝ) ^ a * (2 : ℝ) ^ (U.card - a) := by
    rw [← pow_add, Nat.add_sub_of_le ha]
  rw [uniformStarProbability, hpow]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc
    ((extensionBadStars U containers d).card : ℝ) * (2 : ℝ) ^ a
        ≤ (containers.card * (2 : ℝ) ^ (U.card - a)) * (2 : ℝ) ^ a := by
          exact mul_le_mul_of_nonneg_right hcardReal (by positivity)
    _ = (containers.card : ℝ) *
          ((2 : ℝ) ^ a * (2 : ℝ) ^ (U.card - a)) := by ring

/-- Absorb an exponential container count into the forced-zero-layer saving. -/
theorem card_extensionBadStars_mul_pow_le (U : Finset V)
    (containers : Finset (Finset (V × Fin 2))) (d a c t : ℕ)
    (ha : a ≤ U.card) (hct : c + t ≤ a)
    (hcontainers : containers.card ≤ 2 ^ c)
    (homit : ∀ X ∈ containers,
      d ≤ (taggedLayer U 1 X).card → a ≤ (zeroOmissions U X).card) :
    (extensionBadStars U containers d).card * 2 ^ t ≤ 2 ^ U.card := by
  have hbad := card_extensionBadStars_le U containers d a homit
  have hexp : U.card - a + c + t ≤ U.card := by omega
  calc
    (extensionBadStars U containers d).card * 2 ^ t
        ≤ (containers.card * 2 ^ (U.card - a)) * 2 ^ t :=
      Nat.mul_le_mul_right _ hbad
    _ ≤ ((2 ^ c) * 2 ^ (U.card - a)) * 2 ^ t := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcontainers)
    _ = 2 ^ (U.card - a + c + t) := by
      rw [pow_add, pow_add]
      ac_rfl
    _ ≤ 2 ^ U.card :=
      pow_le_pow_right' (by omega : 1 ≤ (2 : ℕ)) hexp

theorem card_graphExtensionBadStars_mul_pow_le_of_capture
    {A U : Type*} [Fintype A] [DecidableEq A] [Fintype U] [DecidableEq U]
    (target : SimpleGraph A) (oldColor oldAmbient : SimpleGraph U)
    (p badRadius : ℝ) (d a c t : ℕ)
    (containers : Finset (Finset (U × Fin 2)))
    (ha : a ≤ Fintype.card U) (hct : c + t ≤ a)
    (hcontainers : containers.card ≤ 2 ^ c)
    (homit : ∀ X ∈ containers,
      d ≤ (taggedLayer (Finset.univ : Finset U) 1 X).card →
        a ≤ (zeroOmissions (Finset.univ : Finset U) X).card)
    (capture : ∀ (G' G : SimpleGraph (Option U)),
      G' ≤ G → oldPart G' = oldColor → oldPart G = oldAmbient →
      d ≤ (graphStar G').card →
      ¬ (copyHypergraph target G' G).IsJanson p badRadius →
      ∃ X ∈ containers, extensionIota G' G ⊆ X) :
    (graphExtensionBadStars target oldColor oldAmbient p badRadius d).card * 2 ^ t ≤
      2 ^ Fintype.card U := by
  have hsub := graphExtensionBadStars_subset_of_capture target oldColor oldAmbient
    p badRadius d containers capture
  have hcard := Finset.card_le_card hsub
  calc
    (graphExtensionBadStars target oldColor oldAmbient p badRadius d).card * 2 ^ t
        ≤ (extensionBadStars (Finset.univ : Finset U) containers d).card * 2 ^ t :=
      Nat.mul_le_mul_right _ hcard
    _ ≤ 2 ^ (Finset.univ : Finset U).card :=
      card_extensionBadStars_mul_pow_le (Finset.univ : Finset U)
        containers d a c t (by simpa using ha) hct hcontainers homit
    _ = 2 ^ Fintype.card U := by simp

theorem uniformStarProbability_extensionBadStars_pow_le (U : Finset V)
    (containers : Finset (Finset (V × Fin 2))) (d a c t : ℕ)
    (ha : a ≤ U.card) (hct : c + t ≤ a)
    (hcontainers : containers.card ≤ 2 ^ c)
    (homit : ∀ X ∈ containers,
      d ≤ (taggedLayer U 1 X).card → a ≤ (zeroOmissions U X).card) :
    uniformStarProbability U (extensionBadStars U containers d) ≤
      1 / (2 : ℝ) ^ t := by
  have hscaled := card_extensionBadStars_mul_pow_le U containers d a c t ha hct
    hcontainers homit
  rw [uniformStarProbability]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hscaledReal :
      ((extensionBadStars U containers d).card : ℝ) * (2 : ℝ) ^ t ≤
        (2 : ℝ) ^ U.card := by
    exact_mod_cast hscaled
  simpa using hscaledReal

/-- The exact floor arithmetic used in the paper's final union bound:
`1/512 + 1/32 < 1/16`. -/
theorem extensionExponent_sum_le (m r : ℕ) (hr : 0 < r) :
    m / (512 * r) + m / (32 * r) ≤ m / (16 * r) := by
  have hden₃₂ : 0 < 32 * r := Nat.mul_pos (by omega) hr
  have hden₁₆ : 0 < 16 * r := Nat.mul_pos (by omega) hr
  have hfirst : m / (512 * r) ≤ m / (32 * r) := by
    apply Nat.div_le_div_left
    · omega
    · exact hden₃₂
  calc
    m / (512 * r) + m / (32 * r) ≤
        m / (32 * r) + m / (32 * r) := Nat.add_le_add_right hfirst _
    _ = 2 * (m / (32 * r)) := by omega
    _ ≤ m / (16 * r) := by
      apply (Nat.le_div_iff_mul_le hden₁₆).2
      calc
        (2 * (m / (32 * r))) * (16 * r) =
            (32 * r) * (m / (32 * r)) := by ring
        _ ≤ m := Nat.mul_div_le m (32 * r)

theorem extensionBudget_sum_le (m r : ℕ) :
    m / (16 * r) + m / (8 * r) + m / (128 * r) ≤ m / (4 * r) := by
  have h16 : m / (16 * r) = (m / (4 * r)) / 4 := by
    calc
      m / (16 * r) = m / ((4 * r) * 4) := by
        congr 1
        ring
      _ = (m / (4 * r)) / 4 := (Nat.div_div_eq_div_mul m (4 * r) 4).symm
  have h8 : m / (8 * r) = (m / (4 * r)) / 2 := by
    calc
      m / (8 * r) = m / ((4 * r) * 2) := by
        congr 1
        ring
      _ = (m / (4 * r)) / 2 := (Nat.div_div_eq_div_mul m (4 * r) 2).symm
  have h128 : m / (128 * r) = (m / (4 * r)) / 32 := by
    calc
      m / (128 * r) = m / ((4 * r) * 32) := by
        congr 1
        ring
      _ = (m / (4 * r)) / 32 := (Nat.div_div_eq_div_mul m (4 * r) 32).symm
  rw [h16, h8, h128]
  generalize m / (4 * r) = q
  omega

theorem localizedDeletion_le (m r loss : ℕ) (hr : 0 < r)
    (h : 256 * r * loss ≤ 2 * m) :
    loss ≤ m / (128 * r) := by
  have hden : 0 < 128 * r := Nat.mul_pos (by omega) hr
  apply (Nat.le_div_iff_mul_le hden).2
  have htwice : 2 * ((128 * r) * loss) ≤ 2 * m := by
    simpa only [show 2 * ((128 * r) * loss) = 256 * r * loss by ring] using h
  have hcanceled : (128 * r) * loss ≤ m :=
    Nat.le_of_mul_le_mul_left htwice (by omega)
  simpa [mul_comm] using hcanceled

/-- Supersaturation of deleted-target copies forces the intersection of the two localized layers
to be small.  The proof uses both deterministic bridges from `ExtensionAux`: every deleted copy
lifts to an auxiliary edge supported in the two layers, and injective vertex maps preserve
Jansonness. -/
theorem small_layerIntersection_of_aux_nonJanson
    {A U : Type*} [Fintype A] [DecidableEq A]
    [Fintype U] [Nonempty U] [DecidableEq U]
    (target : SimpleGraph A) (root : A)
    (baseColor baseAmbient : SimpleGraph (Option U))
    (p R : ℝ) (hp : 0 < p) (r : ℕ) (hr : 0 < r)
    (supersaturated : ∀ W : Finset U,
      Fintype.card U ≤ 8 * r * W.card →
      ((copyHypergraph (deleteVertex target root)
        (oldPart baseColor) (oldPart baseAmbient)).restrict W).IsJanson p R)
    (Y : Finset (U × Fin 2))
    (hnonJanson :
      ¬ (Hypergraph.map (fun z ↦ some z.1)
        (Hypergraph.restrict
          (extensionAuxHypergraph target root baseColor baseAmbient) Y)).IsJanson p R) :
    ((taggedLayer (Finset.univ : Finset U) 0 Y) ∩
      taggedLayer (Finset.univ : Finset U) 1 Y).card ≤
        Fintype.card U / (8 * r) := by
  let W : Finset U := layerVertices 0 Y ∩ layerVertices 1 Y
  have hWtag : W =
      taggedLayer (Finset.univ : Finset U) 0 Y ∩
        taggedLayer (Finset.univ : Finset U) 1 Y := by
    ext u
    simp [W, layerVertices, taggedLayer]
  have hnotLarge : ¬ Fintype.card U ≤ 8 * r * W.card := by
    intro hlarge
    have hold := supersaturated W hlarge
    have hmapped :
        (((copyHypergraph (deleteVertex target root)
          (oldPart baseColor) (oldPart baseAmbient)).restrict W).map some).IsJanson p R :=
      isJanson_map_of_injective _ some (Option.some_injective U) hp hold
    have hsubset :=
      map_restrict_copyHypergraph_subset_map_restrict_extensionAuxHypergraph
        target root baseColor baseAmbient Y
    exact hnonJanson (hmapped.mono_edges hsubset)
  rw [← hWtag]
  apply (Nat.le_div_iff_mul_le (Nat.mul_pos (by omega) hr)).2
  have : 8 * r * W.card ≤ Fintype.card U := by omega
  simpa [mul_comm, mul_left_comm] using this

/-- A wrapper which turns the exact output of the specialised non-Janson container theorem into
the extension probability bound.

The sole application-specific input is `smallIntersection`: supersaturation of the deleted-copy
hypergraph says that the two projections of the localized set have small intersection.  Everything
else (the localization loss, layer bookkeeping, union bound, and all floor arithmetic) is proved in
this file. -/
theorem extension_probability_bound_of_output
    {W Z : Type*} [Fintype W] [DecidableEq W] [Fintype Z] [DecidableEq Z]
    (oldToTarget : W × Fin 2 → Z) (newVertex : Z)
    (H : Hypergraph (W × Fin 2)) (F : Hypergraph Z)
    (p radius R : ℝ) (r bound : ℕ) (hr : 0 < r)
    (out : SpecialContainer.Output oldToTarget newVertex H F p radius R r bound)
    (hbound : bound ≤ 2 ^ (Fintype.card W / (512 * r)))
    (smallIntersection :
      ∀ X ∈ out.containers,
        (Fintype.card W ⌈/⌉ (4 * r)) ≤
            (taggedLayer (Finset.univ : Finset W) 1 X).card →
        ∀ Y : Finset (W × Fin 2), Y ⊆ X →
          256 * r * (X.card - Y.card) ≤ Fintype.card (W × Fin 2) →
          ¬ ((H.restrict Y).map oldToTarget).IsJanson p R →
          ((taggedLayer (Finset.univ : Finset W) 0 Y) ∩
            taggedLayer (Finset.univ : Finset W) 1 Y).card ≤
              Fintype.card W / (8 * r)) :
    uniformStarProbability (Finset.univ : Finset W)
        (extensionBadStars (Finset.univ : Finset W) out.containers
          (Fintype.card W ⌈/⌉ (4 * r))) ≤
      1 / (2 : ℝ) ^ (Fintype.card W / (32 * r)) := by
  let m := Fintype.card W
  let d := m ⌈/⌉ (4 * r)
  have h4r : 0 < 4 * r := Nat.mul_pos (by omega) hr
  have hlarge : 2 * m ≤ 8 * r * d := by
    have hm : m ≤ (4 * r) * d := ceilDiv_lower m (4 * r) h4r
    calc
      2 * m ≤ 2 * ((4 * r) * d) := Nat.mul_le_mul_left 2 hm
      _ = 8 * r * d := by ring
  have homit : ∀ X ∈ out.containers,
      d ≤ (taggedLayer (Finset.univ : Finset W) 1 X).card →
        m / (16 * r) ≤
          (zeroOmissions (Finset.univ : Finset W) X).card := by
    intro X hXC hdX
    have hXfull : X ⊆ twoLayerUniverse (Finset.univ : Finset W) := by
      intro z hz
      simp [twoLayerUniverse]
    have hLayerCard : (taggedLayer (Finset.univ : Finset W) 1 X).card ≤ X.card := by
      have := taggedLayer_card_add hXfull
      omega
    have hXcard : d ≤ X.card := hdX.trans hLayerCard
    have hOutputLarge : Fintype.card (W × Fin 2) ≤ 8 * r * X.card := by
      have : 2 * m ≤ 8 * r * X.card :=
        hlarge.trans (Nat.mul_le_mul_left (8 * r) hXcard)
      simpa [m, Fintype.card_prod, Nat.mul_comm] using this
    obtain ⟨Y, hYX, hlossRaw, hnonJanson⟩ := out.localized X hXC hOutputLarge
    have hlossNumeral : 256 * r * (X.card - Y.card) ≤ 2 * m := by
      simpa [m, Fintype.card_prod, Nat.mul_comm] using hlossRaw
    have hlossSmall : X.card - Y.card ≤ m / (128 * r) :=
      localizedDeletion_le m r (X.card - Y.card) hr hlossNumeral
    have hXYcard : X.card ≤ Y.card + m / (128 * r) := by
      have hcardYX : Y.card ≤ X.card := Finset.card_le_card hYX
      omega
    have hinter :
        ((taggedLayer (Finset.univ : Finset W) 0 Y) ∩
          taggedLayer (Finset.univ : Finset W) 1 Y).card ≤ m / (8 * r) := by
      exact smallIntersection X hXC (by simpa [d, m] using hdX) Y hYX hlossRaw hnonJanson
    apply zeroOmissions_card_lower
      (U := (Finset.univ : Finset W))
      (d := d) (w := m / (8 * r)) (l := m / (128 * r))
    · intro z hz
      simp [twoLayerUniverse]
    · intro z hz
      simp [twoLayerUniverse]
    · exact hdX
    · exact hXYcard
    · exact hinter
    · have hfloor : m / (4 * r) ≤ d := by
        simpa [d] using (floorDiv_le_ceilDiv (a := 4 * r) (b := m))
      exact (extensionBudget_sum_le m r).trans hfloor
  apply uniformStarProbability_extensionBadStars_pow_le
    (Finset.univ : Finset W) out.containers d
      (m / (16 * r)) (m / (512 * r)) (m / (32 * r))
  · simpa [m] using Nat.div_le_self m (16 * r)
  · exact extensionExponent_sum_le m r hr
  · exact out.card_containers.trans hbound
  · exact homit

/-- Graph-facing form of the strong one-vertex extension estimate, conditional only on the
finite output package of the specialised container theorem.  Unlike the abstract counting
lemma above, this theorem proves the capture implication from the actual auxiliary hypergraph:
the coned auxiliary edges and the already available old copies are all full-target copies.

The final unconditional theorem below obtains `out` from the specialised container theorem;
this intermediate statement keeps the graph reduction independently reusable. -/
theorem graphExtensionBadStars_mul_pow_le_of_output
    {A U : Type*} [Fintype A] [DecidableEq A]
    [Fintype U] [Nonempty U] [DecidableEq U]
    (target : SimpleGraph A) (root : A)
    (baseColor baseAmbient : SimpleGraph (Option U))
    (p R' R eta : ℝ) (r bound : ℕ)
    (hp : 0 < p) (hr : 0 < r) (hR' : 0 ≤ R')
    (heta : 1 ≤ eta * R)
    (out : SpecialContainer.Output (fun z : U × Fin 2 ↦ some z.1) none
      (extensionAuxHypergraph target root baseColor baseAmbient)
      ((copyHypergraph target (oldPart baseColor) (oldPart baseAmbient)).map some)
      p (R' + eta * R) R r bound)
    (hbound : bound ≤ 2 ^ (Fintype.card U / (512 * r)))
    (supersaturated : ∀ W : Finset U,
      Fintype.card U ≤ 8 * r * W.card →
      ((copyHypergraph (deleteVertex target root)
        (oldPart baseColor) (oldPart baseAmbient)).restrict W).IsJanson p R) :
    (graphExtensionBadStars target (oldPart baseColor) (oldPart baseAmbient)
        p (R' + 1) (Fintype.card U ⌈/⌉ (4 * r))).card *
        2 ^ (Fintype.card U / (32 * r)) ≤
      2 ^ Fintype.card U := by
  classical
  let m := Fintype.card U
  let d := m ⌈/⌉ (4 * r)
  have h4r : 0 < 4 * r := Nat.mul_pos (by omega) hr
  have hlarge : 2 * m ≤ 8 * r * d := by
    have hm : m ≤ (4 * r) * d := ceilDiv_lower m (4 * r) h4r
    calc
      2 * m ≤ 2 * ((4 * r) * d) := Nat.mul_le_mul_left 2 hm
      _ = 8 * r * d := by ring
  have homit : ∀ X ∈ out.containers,
      d ≤ (taggedLayer (Finset.univ : Finset U) 1 X).card →
        m / (16 * r) ≤
          (zeroOmissions (Finset.univ : Finset U) X).card := by
    intro X hXC hdX
    have hXfull : X ⊆ twoLayerUniverse (Finset.univ : Finset U) := by
      intro z hz
      simp [twoLayerUniverse]
    have hLayerCard :
        (taggedLayer (Finset.univ : Finset U) 1 X).card ≤ X.card := by
      have := taggedLayer_card_add hXfull
      omega
    have hXcard : d ≤ X.card := hdX.trans hLayerCard
    have hOutputLarge : Fintype.card (U × Fin 2) ≤ 8 * r * X.card := by
      have : 2 * m ≤ 8 * r * X.card :=
        hlarge.trans (Nat.mul_le_mul_left (8 * r) hXcard)
      simpa [m, Fintype.card_prod, Nat.mul_comm] using this
    obtain ⟨Y, hYX, hlossRaw, hnonJanson⟩ := out.localized X hXC hOutputLarge
    have hlossNumeral : 256 * r * (X.card - Y.card) ≤ 2 * m := by
      simpa [m, Fintype.card_prod, Nat.mul_comm] using hlossRaw
    have hlossSmall : X.card - Y.card ≤ m / (128 * r) :=
      localizedDeletion_le m r (X.card - Y.card) hr hlossNumeral
    have hXYcard : X.card ≤ Y.card + m / (128 * r) := by
      have hcardYX : Y.card ≤ X.card := Finset.card_le_card hYX
      omega
    have hinter :
        ((taggedLayer (Finset.univ : Finset U) 0 Y) ∩
          taggedLayer (Finset.univ : Finset U) 1 Y).card ≤ m / (8 * r) := by
      exact small_layerIntersection_of_aux_nonJanson target root baseColor baseAmbient
        p R hp r hr supersaturated Y hnonJanson
    apply zeroOmissions_card_lower
      (U := (Finset.univ : Finset U))
      (d := d) (w := m / (8 * r)) (l := m / (128 * r))
    · exact hXfull
    · intro z hz
      simp [twoLayerUniverse]
    · exact hdX
    · exact hXYcard
    · exact hinter
    · have hfloor : m / (4 * r) ≤ d := by
        simpa [d] using (floorDiv_le_ceilDiv (a := 4 * r) (b := m))
      exact (extensionBudget_sum_le m r).trans hfloor
  have hcapture : ∀ (G' G : SimpleGraph (Option U)),
      G' ≤ G → oldPart G' = oldPart baseColor →
      oldPart G = oldPart baseAmbient →
      d ≤ (graphStar G').card →
      ¬ (copyHypergraph target G' G).IsJanson p (R' + 1) →
      ∃ X ∈ out.containers, extensionIota G' G ⊆ X := by
    intro G' G hle hcolor hambient _hdegree hbad
    apply out.bad_subset
    intro hlocal
    apply hbad
    have hfull : (copyHypergraph target G' G).IsJanson p (R' + eta * R) :=
      hlocal.mono_edges
        (extensionUnion_subset_fullCopies target root baseColor baseAmbient
          G' G hle hcolor hambient)
    apply Hypergraph.IsJanson.mono_params hfull hp (le_refl p)
    · linarith
    · linarith
  apply card_graphExtensionBadStars_mul_pow_le_of_capture
    target (oldPart baseColor) (oldPart baseAmbient) p (R' + 1) d
      (m / (16 * r)) (m / (512 * r)) (m / (32 * r)) out.containers
  · exact Nat.div_le_self _ _
  · exact extensionExponent_sum_le m r hr
  · exact out.card_containers.trans hbound
  · exact homit
  · simpa [d, m] using hcapture

/-- The numerical `2^{-m/(32r)}` conclusion of the extension union bound, with all floors made
explicit.  The two hypotheses are exactly the outputs needed from the specialised container
theorem: at most `2^{m/(512r)}` containers and at least `m/(16r)` forced zero-layer omissions. -/
theorem extension_probability_bound (U : Finset V) (r d : ℕ) (hr : 0 < r)
    (containers : Finset (Finset (V × Fin 2)))
    (hcontainers : containers.card ≤ 2 ^ (U.card / (512 * r)))
    (homit : ∀ X ∈ containers,
      d ≤ (taggedLayer U 1 X).card →
        U.card / (16 * r) ≤ (zeroOmissions U X).card) :
    uniformStarProbability U (extensionBadStars U containers d) ≤
      1 / (2 : ℝ) ^ (U.card / (32 * r)) := by
  apply uniformStarProbability_extensionBadStars_pow_le U containers d
    (U.card / (16 * r)) (U.card / (512 * r)) (U.card / (32 * r))
  · exact Nat.div_le_self _ _
  · exact extensionExponent_sum_le U.card r hr
  · exact hcontainers
  · exact homit

/-- **Strong one-vertex extension lemma (ACDFM Lemma 5.1), finite cardinal form.**

Assume the old full-target copy hypergraph is Janson at radius `R'`, and every sufficiently
large old set is supersaturated with deleted-target copies at the extension radius.  Then among
all possible stars at the new vertex, the proportion for which a degree-`m/(4r)` colour substar
can still leave the full-target copy hypergraph non-Janson at radius `R' + 1` is at most
`2^(-m/(32r))`.  The displayed conclusion is the denominator-cleared exact finite statement.

All constants, real parameters, fingerprint floors, and the radius increment are discharged in
the proof; in particular, no container theorem or probabilistic assertion remains as a
hypothesis. -/
theorem strongExtensionLemma
    {A U : Type*} [Fintype A] [DecidableEq A]
    [Fintype U] [Nonempty U] [DecidableEq U]
    (target : SimpleGraph A) (root : A)
    (baseColor baseAmbient : SimpleGraph (Option U))
    (r k s : ℕ) (R' : ℝ)
    (hr : 2 ≤ r) (hk : 2 ≤ k) (hspos : 1 ≤ s)
    (hs : s + 1 ≤ k)
    (htarget : Fintype.card A = s + 1)
    (hscale : r ^ (300 * k) ≤ Fintype.card U)
    (hR'0 : 0 ≤ R')
    (hR' : R' ≤ extensionR r k (Fintype.card U) / 16)
    (availableJanson :
      (copyHypergraph target (oldPart baseColor) (oldPart baseAmbient)).IsJanson
        (extensionP r k) R')
    (supersaturated : ∀ W : Finset U,
      Fintype.card U ≤ 8 * r * W.card →
      ((copyHypergraph (deleteVertex target root)
        (oldPart baseColor) (oldPart baseAmbient)).restrict W).IsJanson
          (extensionP r k) (extensionR r k (Fintype.card U))) :
    (graphExtensionBadStars target (oldPart baseColor) (oldPart baseAmbient)
        (extensionP r k) (R' + 1)
        (Fintype.card U ⌈/⌉ (4 * r))).card *
        2 ^ (Fintype.card U / (32 * r)) ≤
      2 ^ Fintype.card U := by
  classical
  let m := Fintype.card U
  have hrpos : 0 < r := by omega
  have hkpos : 0 < k := by omega
  have hdeleted : Fintype.card (DeletedVertices root) = s := by
    have hcard : Fintype.card (DeletedVertices root) = Fintype.card A - 1 := by
      simp [DeletedVertices]
    rw [hcard, htarget]
    omega
  have hsm : s ≤ m := by
    have hsk : s ≤ k := by omega
    have hkpow : k ≤ r ^ k := Numeric.self_le_r_pow_self r k hr
    have hpows : r ^ k ≤ r ^ (300 * k) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    exact hsk.trans (hkpow.trans (hpows.trans hscale))
  have hpar : SpecialContainer.ParameterConditions
      (Fintype.card (U × Fin 2)) s r
      (extensionQ r) (extensionP r k) (extensionR r k m) R'
      (extensionEta r k s) := by
    simpa [m, Fintype.card_prod, Nat.mul_comm] using
      (extension_parameterConditions hr hk hspos hs hsm hR'0 hR')
  have hH : Hypergraph.IsUniform
      (extensionAuxHypergraph target root baseColor baseAmbient) s := by
    simpa [hdeleted] using
      (extensionAux_isUniform target root baseColor baseAmbient)
  have hF : Hypergraph.IsUniform
      ((copyHypergraph target (oldPart baseColor) (oldPart baseAmbient)).map some)
      (s + 1) := by
    simpa [htarget] using
      (map_oldCopies_isUniform target (oldPart baseColor) (oldPart baseAmbient))
  have hFJ : Hypergraph.IsJanson
      ((copyHypergraph target (oldPart baseColor) (oldPart baseAmbient)).map some)
        (extensionP r k) R' :=
    isJanson_map_of_injective _ some (Option.some_injective U)
      (extensionP_pos hrpos hkpos) availableJanson
  have hFfresh : ∀ E ∈
      (copyHypergraph target (oldPart baseColor) (oldPart baseAmbient)).map some,
      none ∉ E := by
    intro E hE
    obtain ⟨L, hL, rfl⟩ := Hypergraph.mem_map.mp hE
    simp
  let out := SpecialContainerTheorem.specializedNonJansonContainer
    (fun z : U × Fin 2 ↦ some z.1) none
    (extensionAuxHypergraph target root baseColor baseAmbient)
    ((copyHypergraph target (oldPart baseColor) (oldPart baseAmbient)).map some)
    (extensionQ r) (extensionP r k) (extensionR r k m) R'
    (extensionEta r k s) r s (by omega) hpar hH hF hFJ hFfresh
    (extensionAux_projectionConditions target root baseColor baseAmbient)
    (fun z ↦ extensionProjection_ne_newVertex z)
  have hcardTwo : Fintype.card (U × Fin 2) = 2 * m := by
    simp [m, Fintype.card_prod, Nat.mul_comm]
  have hcut := extensionQ_floor_cutoffs r m
  have hbound :
      SpecialContainer.fingerprintCount (Fintype.card (U × Fin 2))
          ⌊2 * extensionQ r * Fintype.card (U × Fin 2)⌋₊ *
        SpecialContainer.fingerprintCount (Fintype.card (U × Fin 2))
          ⌊extensionQ r * Fintype.card (U × Fin 2)⌋₊ ≤
        2 ^ (m / (512 * r)) := by
    rw [hcardTwo, hcut.2, hcut.1]
    exact extension_fingerprintCount_bound hr
  exact graphExtensionBadStars_mul_pow_le_of_output target root baseColor baseAmbient
    (extensionP r k) R' (extensionR r k m) (extensionEta r k s) r _
    (extensionP_pos hrpos hkpos) hrpos hR'0
    (one_le_extensionEta_mul_extensionR hr hk hs hscale)
    out hbound supersaturated

end Extension
end Erdos565
