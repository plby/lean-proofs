/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos223.Basic

/-!
# Diameter graphs on a large two-sphere

This file contains the spherical-thrackle estimate used in the odd-dimensional
part of Erdős Problem 223.  The geometric core is most conveniently expressed
by saying that a vertex has at most two neighbours which are not leaves.  The
first theorem below records the (purely graph-theoretic) reduction from that
local assertion to the required linear edge bound.
-/

open Metric
open scoped BigOperators EuclideanGeometry Matrix RealInnerProductSpace SimpleGraph

namespace Erdos223
namespace SphericalThrackle

noncomputable section

/-! ## The graph-theoretic reduction -/

/-- If every vertex of a finite graph has at most two neighbours whose degree
is at least two, then the graph is a pseudoforest, in the numerical sense that
it has at most one edge per vertex.  This induction formulation is useful for
geometric thrackle arguments: the hypothesis is inherited by induced
subgraphs, while a graph of minimum degree two has maximum degree two. -/
theorem card_edgeFinset_le_card_of_coreNeighbor_le_two
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcore : ∀ x : V,
      ((G.neighborFinset x).filter fun y => 2 ≤ G.degree y).card ≤ 2) :
    G.edgeFinset.card ≤ Fintype.card V := by
  classical
  induction hn : Fintype.card V using Nat.strong_induction_on generalizing V with
  | h N ih =>
      by_cases hmin : ∀ x : V, 2 ≤ G.degree x
      · have hdegree : ∀ x : V, G.degree x ≤ 2 := by
          intro x
          have hfilter :
              (G.neighborFinset x).filter (fun y => 2 ≤ G.degree y) =
                G.neighborFinset x := by
            apply Finset.filter_eq_self.mpr
            intro y _
            exact hmin y
          simpa [hfilter] using hcore x
        have hsum : (∑ x : V, G.degree x) ≤ ∑ _x : V, 2 :=
          Finset.sum_le_sum fun x _ => hdegree x
        rw [G.sum_degrees_eq_twice_card_edges] at hsum
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
        have : 2 * G.edgeFinset.card ≤ 2 * Fintype.card V := by
          simpa [Nat.mul_comm] using hsum
        exact (Nat.le_of_mul_le_mul_left this (by omega)).trans_eq hn
      · push_neg at hmin
        obtain ⟨v, hv⟩ := hmin
        let s : Set V := {v}ᶜ
        let H : SimpleGraph s := G.induce s
        let e : s ↪ V := Function.Embedding.subtype _
        have hdegree_le (y : s) : H.degree y ≤ G.degree (y : V) := by
          have hm := G.map_neighborFinset_induce (s := s) y
          have hc := congrArg Finset.card hm
          rw [Finset.card_map] at hc
          change (H.neighborFinset y).card ≤ (G.neighborFinset (y : V)).card
          rw [hc]
          exact Finset.card_mono Finset.inter_subset_left
        have hHcore : ∀ x : s,
            ((H.neighborFinset x).filter fun y => 2 ≤ H.degree y).card ≤ 2 := by
          intro x
          let S := (H.neighborFinset x).filter fun y => 2 ≤ H.degree y
          let T := (G.neighborFinset (x : V)).filter fun y => 2 ≤ G.degree y
          have hmap : S.card = (S.map e).card := (Finset.card_map e).symm
          rw [hmap]
          apply (Finset.card_le_card ?_).trans (hcore (x : V))
          intro y hy
          rw [Finset.mem_map] at hy
          obtain ⟨z, hz, rfl⟩ := hy
          have hz' : z ∈ H.neighborFinset x ∧ 2 ≤ H.degree z := by
            simpa [S] using hz
          have hadjH : H.Adj x z :=
            (H.mem_neighborFinset x z).mp hz'.1
          have hadj : G.Adj (x : V) (z : V) := hadjH
          exact Finset.mem_filter.mpr
            ⟨(G.mem_neighborFinset (x : V) (z : V)).mpr hadj,
              hz'.2.trans (hdegree_le z)⟩
        have hcard_s : Fintype.card s < N := by
          have hs_card : Fintype.card s = Fintype.card V - 1 := by
            simpa [s] using Fintype.card_compl_set ({v} : Set V)
          have hVpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
          rw [← hn]
          omega
        have hIH : H.edgeFinset.card ≤ Fintype.card s :=
          ih (Fintype.card s) hcard_s H hHcore rfl
        have hdel : H.edgeFinset.card = G.edgeFinset.card - G.degree v := by
          rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
            G.card_edgeFinset_deleteIncidenceSet]
        have hdeg_edge : G.degree v ≤ G.edgeFinset.card :=
          G.degree_le_card_edgeFinset (v := v)
        have hcard : Fintype.card s + 1 = Fintype.card V := by
          have hs_card : Fintype.card s = Fintype.card V - 1 := by
            simpa [s] using Fintype.card_compl_set ({v} : Set V)
          have hVpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
          omega
        omega

/-! ## Metric-to-inner-product conversion -/

/-- Squared distance in a real inner-product space, in the form used by the
spherical calculation. -/
private lemma dist_sq_eq_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x y : E) :
    dist x y ^ 2 = inner ℝ x x + inner ℝ y y - 2 * inner ℝ x y := by
  rw [dist_eq_norm, sq]
  calc
    ‖x - y‖ * ‖x - y‖ = ‖x - y‖ ^ 2 := by ring
    _ = inner ℝ (x - y) (x - y) :=
      (real_inner_self_eq_norm_sq (x - y)).symm
    _ = inner ℝ x x + inner ℝ y y - 2 * inner ℝ x y := by
      simp only [inner_sub_left, inner_sub_right]
      rw [real_inner_comm y x]
      ring

/-- Points on a radius-`r` sphere have squared norm `r²` after translation
to the centre. -/
private lemma inner_vsub_self_of_mem_sphere {d : ℕ} {x c : Point d} {r : ℝ}
    (hx : dist x c = r) : inner ℝ (x - c) (x - c) = r ^ 2 := by
  rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hx]

/-- On a common sphere, a unit chord is equivalently a prescribed inner
product. -/
private lemma inner_vsub_eq_of_dist_eq_one {d : ℕ} {x y c : Point d} {r : ℝ}
    (hx : dist x c = r) (hy : dist y c = r) (hxy : dist x y = 1) :
    inner ℝ (x - c) (y - c) = r ^ 2 - 1 / 2 := by
  have h := dist_sq_eq_inner (x - c) (y - c)
  rw [show dist (x - c) (y - c) = dist x y by
    simp only [dist_eq_norm]
    congr 1
    abel, hxy, inner_vsub_self_of_mem_sphere hx,
    inner_vsub_self_of_mem_sphere hy] at h
  nlinarith

/-- The diameter condition turns into the corresponding lower bound for all
inner products of translated radius vectors. -/
private lemma inner_vsub_ge_of_dist_le_one {d : ℕ} {x y c : Point d} {r : ℝ}
    (hx : dist x c = r) (hy : dist y c = r) (hxy : dist x y ≤ 1) :
    r ^ 2 - 1 / 2 ≤ inner ℝ (x - c) (y - c) := by
  have h := dist_sq_eq_inner (x - c) (y - c)
  have hdist : dist (x - c) (y - c) = dist x y := by
    simp only [dist_eq_norm]
    congr 1
    abel
  rw [hdist, inner_vsub_self_of_mem_sphere hx,
    inner_vsub_self_of_mem_sphere hy] at h
  have hnonneg : 0 ≤ dist x y := dist_nonneg
  nlinarith

private lemma inner_vsub_le_sq {d : ℕ} {x y c : Point d} {r : ℝ}
    (hx : dist x c = r) (hy : dist y c = r) :
    inner ℝ (x - c) (y - c) ≤ r ^ 2 := by
  have h := dist_sq_eq_inner (x - c) (y - c)
  have hdist : dist (x - c) (y - c) = dist x y := by
    simp only [dist_eq_norm]
    congr 1
    abel
  rw [hdist, inner_vsub_self_of_mem_sphere hx,
    inner_vsub_self_of_mem_sphere hy] at h
  nlinarith [sq_nonneg (dist x y)]

private lemma inner_vsub_lt_sq_of_ne {d : ℕ} {x y c : Point d} {r : ℝ}
    (hx : dist x c = r) (hy : dist y c = r) (hxy : x ≠ y) :
    inner ℝ (x - c) (y - c) < r ^ 2 := by
  have h := dist_sq_eq_inner (x - c) (y - c)
  have hdist : dist (x - c) (y - c) = dist x y := by
    simp only [dist_eq_norm]
    congr 1
    abel
  rw [hdist, inner_vsub_self_of_mem_sphere hx,
    inner_vsub_self_of_mem_sphere hy] at h
  have hdpos : 0 < dist x y := dist_pos.mpr hxy
  nlinarith

/-- The threshold `1 / sqrt 2` is positive. -/
private lemma inv_sqrt_two_pos : 0 < (1 / Real.sqrt 2 : ℝ) := by positivity

/-- At the large-sphere threshold, the inner product belonging to a unit
chord is nonnegative. -/
private lemma half_le_sq_of_inv_sqrt_two_le {r : ℝ}
    (hr : 1 / Real.sqrt 2 ≤ r) : 1 / 2 ≤ r ^ 2 := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hr0 : 0 ≤ r := (inv_sqrt_two_pos.le.trans hr)
  have h := sq_le_sq₀ (by positivity : 0 ≤ (1 / Real.sqrt 2 : ℝ)) hr0 |>.mpr hr
  field_simp [ne_of_gt hsqrt] at h
  nlinarith

/-! ## The algebraic spherical-thrackle lemma -/

private abbrev RawVector := Fin 3 → ℝ

private def translatedRaw (c x : Point 3) : RawVector :=
  WithLp.ofLp (x - c)

private lemma translatedRaw_dot (c x y : Point 3) :
    translatedRaw c x ⬝ᵥ translatedRaw c y = inner ℝ (x - c) (y - c) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [translatedRaw, star_trivial]
  exact dotProduct_comm _ _

private def translatedRawEmbedding (c : Point 3) : Point 3 ↪ RawVector where
  toFun := translatedRaw c
  inj' := by
    intro x y h
    have h' := congrArg (WithLp.toLp 2) h
    simp only [translatedRaw, WithLp.toLp_ofLp] at h'
    exact sub_left_injective h'

private lemma beta_lt_alpha_of_projection_degenerate {q α β : ℝ}
    (hq : 0 < q) (hα : 0 ≤ α) (hαq : α < q) (hβq : β < q)
    (hdet : (q - β ^ 2 / q) * (q - α ^ 2 / q) =
      (α * (1 - β / q)) ^ 2) : β < α := by
  have hqne : q ≠ 0 := ne_of_gt hq
  field_simp [hqne] at hdet
  have hfactor : (q - β) * (q * (q + β) - 2 * α ^ 2) = 0 := by
    ring_nf at hdet ⊢
    nlinarith
  have heq : q * (q + β) = 2 * α ^ 2 := by
    rcases mul_eq_zero.mp hfactor with hzero | hzero <;> nlinarith
  have hp : 0 < (2 * α + q) * (q - α) :=
    mul_pos (by nlinarith) (sub_pos.mpr hαq)
  nlinarith

/-- Algebraic form of the endpoint lemma.  Here `X` is a fixed vertex and
`B` is its set of neighbours, written as radius vectors.  A member of `B`
which has another diameter neighbour has a tangent supporting direction;
the scalar `lambda` records on which of the two sides that direction points.
-/
private lemma exists_endpoint_orientation
    {q α : ℝ} (hq : 0 < q) (hα : 0 ≤ α) (hαq : α < q)
    {X : RawVector} {B : Finset RawVector}
    (hXX : X ⬝ᵥ X = q)
    (hYY : ∀ Y ∈ B, Y ⬝ᵥ Y = q)
    (hXY : ∀ Y ∈ B, X ⬝ᵥ Y = α)
    (hlo : ∀ Y ∈ B, ∀ Y' ∈ B, α ≤ Y ⬝ᵥ Y')
    (hhi : ∀ Y ∈ B, ∀ Y' ∈ B, Y ⬝ᵥ Y' ≤ q)
    {Y : RawVector} (hY : Y ∈ B)
    (hwitness : ∃ Z : RawVector,
      Z ⬝ᵥ Z = q ∧ Y ⬝ᵥ Z = α ∧
      α ≤ X ⬝ᵥ Z ∧ X ⬝ᵥ Z < q ∧
      ∀ Y' ∈ B, α ≤ Z ⬝ᵥ Y') :
    ∃ lambda : ℝ, lambda ≠ 0 ∧
      ∀ Y' ∈ B,
        0 ≤ lambda *
          ((X ⨯₃ (Y - (α / q) • X)) ⬝ᵥ
            ((Y' - (α / q) • X) - (Y - (α / q) • X))) := by
  obtain ⟨Z, hZZ, hYZ, hβlo, hβhi, hZB⟩ := hwitness
  let a : ℝ := α / q
  let β : ℝ := X ⬝ᵥ Z
  let b : ℝ := β / q
  let u : RawVector := Y - a • X
  let w : RawVector := Z - b • X
  have hYX : Y ⬝ᵥ X = α := by rw [dotProduct_comm, hXY Y hY]
  have hZX : Z ⬝ᵥ X = β := by rw [dotProduct_comm]
  have hXZ : X ⬝ᵥ Z = β := rfl
  have hxu : X ⬝ᵥ u = 0 := by
    simp only [u, dotProduct_sub, dotProduct_smul, hXY Y hY, hXX,
      smul_eq_mul, a]
    field_simp
    ring
  have hux : u ⬝ᵥ X = 0 := by rw [dotProduct_comm, hxu]
  have hU : u ⬝ᵥ u = q - α ^ 2 / q := by
    simp only [u, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, hYY Y hY, hYX, hXY Y hY, hXX, smul_eq_mul, a]
    field_simp
    ring
  have hUpos : 0 < u ⬝ᵥ u := by
    rw [hU, sub_pos, div_lt_iff₀ hq]
    nlinarith [mul_pos (sub_pos.mpr hαq) (by nlinarith : 0 < q + α)]
  have hxw : X ⬝ᵥ w = 0 := by
    simp only [w, dotProduct_sub, dotProduct_smul, hXZ, hXX, smul_eq_mul, b]
    field_simp
    ring
  have hwx : w ⬝ᵥ X = 0 := by rw [dotProduct_comm, hxw]
  have hwu : w ⬝ᵥ u = α * (1 - b) := by
    have hZY : Z ⬝ᵥ Y = α := by rw [dotProduct_comm, hYZ]
    simp only [w, u, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, hZY, hZX, hXZ, hYX, hXX, smul_eq_mul, a, b]
    rw [hXY Y hY]
    field_simp
    ring
  have hww : w ⬝ᵥ w = q - β ^ 2 / q := by
    simp only [w, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, hZZ, hZX, hXZ, hXX, smul_eq_mul, b]
    field_simp
    ring
  have hb_le : b ≤ 1 := by
    dsimp [b, β]
    rw [div_le_one hq]
    exact hβhi.le
  have hwu_nonneg : 0 ≤ w ⬝ᵥ u := by
    rw [hwu]
    exact mul_nonneg hα (sub_nonneg.mpr hb_le)
  let k : ℝ := (w ⬝ᵥ u) / (u ⬝ᵥ u)
  have hk : 0 ≤ k := div_nonneg hwu_nonneg hUpos.le
  let t : RawVector := w - k • u
  have hxt : X ⬝ᵥ t = 0 := by simp [t, dotProduct_sub, dotProduct_smul, hxu, hxw]
  have hut : u ⬝ᵥ t = 0 := by
    simp only [t, dotProduct_sub, dotProduct_smul, smul_eq_mul, k]
    rw [dotProduct_comm u w]
    field_simp
    ring
  have htu : t ⬝ᵥ u = 0 := by rw [dotProduct_comm, hut]
  have htx : t ⬝ᵥ X = 0 := by rw [dotProduct_comm, hxt]
  have ht_ne : t ≠ 0 := by
    intro ht
    have hwku : w = k • u := by
      simpa [t, sub_eq_zero] using ht
    have hww' : w ⬝ᵥ w = k ^ 2 * (u ⬝ᵥ u) := by
      rw [hwku, smul_dotProduct, dotProduct_smul]
      simp only [smul_eq_mul]
      ring
    have hwu' : w ⬝ᵥ u = k * (u ⬝ᵥ u) := by
      rw [hwku, smul_dotProduct]
      rfl
    have hdet : (w ⬝ᵥ w) * (u ⬝ᵥ u) = (w ⬝ᵥ u) ^ 2 := by
      rw [hww', hwu']
      ring
    have hβlt : β < α := by
      rw [hww, hU, hwu] at hdet
      dsimp only [a, b] at hdet
      exact beta_lt_alpha_of_projection_degenerate hq hα hαq hβhi hdet
    exact (not_lt_of_ge hβlo) hβlt
  let j : RawVector := X ⨯₃ u
  have hjj : j ⬝ᵥ j = q * (u ⬝ᵥ u) := by
    simpa [j, hXX, hxu, hux] using cross_dot_cross X u X u
  have hj_ne : j ≠ 0 := by
    intro hj
    have : j ⬝ᵥ j = 0 := by simp [hj]
    rw [hjj] at this
    nlinarith
  have hjt_cross : j ⨯₃ t = 0 := by
    rw [show j ⨯₃ t = (X ⬝ᵥ t) • u - (u ⬝ᵥ t) • X by
      simpa [j] using cross_cross_eq_smul_sub_smul X u t]
    simp [hxt, hut]
  have hdep : ¬ LinearIndependent ℝ ![j, t] := by
    rw [← crossProduct_ne_zero_iff_linearIndependent]
    exact not_ne_iff.mpr hjt_cross
  rw [LinearIndependent.pair_iff' hj_ne] at hdep
  push_neg at hdep
  obtain ⟨lambda, hlambda⟩ := hdep
  have hlambda_ne : lambda ≠ 0 := by
    intro hzero
    rw [hzero, zero_smul] at hlambda
    exact ht_ne hlambda.symm
  refine ⟨lambda, hlambda_ne, ?_⟩
  intro Y' hY'
  let u' : RawVector := Y' - a • X
  have hxu' : X ⬝ᵥ u' = 0 := by
    simp only [u', dotProduct_sub, dotProduct_smul, hXY Y' hY', hXX,
      smul_eq_mul, a]
    field_simp
    ring
  have hdiff : u' - u = Y' - Y := by
    simp [u', u]
  have hwdiff : 0 ≤ w ⬝ᵥ (u' - u) := by
    have hZY : Z ⬝ᵥ Y = α := by rw [dotProduct_comm, hYZ]
    have hZY' := hZB Y' hY'
    rw [hdiff]
    simp only [w, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      hZY, hXY Y' hY', hXY Y hY, smul_eq_mul]
    nlinarith
  have hudiff : u ⬝ᵥ (u' - u) ≤ 0 := by
    have hYY' := hhi Y hY Y' hY'
    rw [hdiff]
    simp only [u, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      hYY Y hY, hXY Y' hY', hXY Y hY, smul_eq_mul]
    nlinarith
  have htdiff : 0 ≤ t ⬝ᵥ (u' - u) := by
    simp only [t, sub_dotProduct, smul_dotProduct, smul_eq_mul]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hk hudiff]
  rw [← hlambda] at htdiff
  change 0 ≤ lambda * (j ⬝ᵥ (u' - u))
  simp only [smul_dotProduct, dotProduct_sub, smul_eq_mul] at htdiff ⊢
  linarith

/-- At most two neighbours of `X` can possess the endpoint certificates from
`exists_endpoint_orientation`.  The two possibilities are the two signs of
the oriented scalar triple product. -/
private lemma card_le_two_of_endpoint_certificates
    {q α : ℝ} (hq : 0 < q) (hα : 0 ≤ α) (hαq : α < q)
    {X : RawVector} {B : Finset RawVector}
    (hXX : X ⬝ᵥ X = q)
    (hYY : ∀ Y ∈ B, Y ⬝ᵥ Y = q)
    (hXY : ∀ Y ∈ B, X ⬝ᵥ Y = α)
    (hlo : ∀ Y ∈ B, ∀ Y' ∈ B, α ≤ Y ⬝ᵥ Y')
    (hhi : ∀ Y ∈ B, ∀ Y' ∈ B, Y ⬝ᵥ Y' ≤ q)
    (hwitness : ∀ Y ∈ B, ∃ Z : RawVector,
      Z ⬝ᵥ Z = q ∧ Y ⬝ᵥ Z = α ∧
      α ≤ X ⬝ᵥ Z ∧ X ⬝ᵥ Z < q ∧
      ∀ Y' ∈ B, α ≤ Z ⬝ᵥ Y') :
    B.card ≤ 2 := by
  classical
  let lambda : RawVector → ℝ := fun Y =>
    if hY : Y ∈ B then Classical.choose
      (exists_endpoint_orientation hq hα hαq hXX hYY hXY hlo hhi hY
        (hwitness Y hY))
    else 1
  have hlambda (Y : RawVector) (hY : Y ∈ B) : lambda Y ≠ 0 := by
    simp only [lambda, dif_pos hY]
    exact (Classical.choose_spec
      (exists_endpoint_orientation hq hα hαq hXX hYY hXY hlo hhi hY
        (hwitness Y hY))).1
  have hexpose (Y : RawVector) (hY : Y ∈ B) (Y' : RawVector) (hY' : Y' ∈ B) :
      0 ≤ lambda Y *
        ((X ⨯₃ (Y - (α / q) • X)) ⬝ᵥ
          ((Y' - (α / q) • X) - (Y - (α / q) • X))) := by
    simp only [lambda, dif_pos hY]
    exact (Classical.choose_spec
      (exists_endpoint_orientation hq hα hαq hXX hYY hXY hlo hhi hY
        (hwitness Y hY))).2 Y' hY'
  let sign : RawVector → Bool := fun Y => decide (0 < lambda Y)
  have hsign_inj : Set.InjOn sign (↑B : Set RawVector) := by
    intro Y hY Y' hY' hsign
    have hcase : (0 < lambda Y ∧ 0 < lambda Y') ∨
        (lambda Y < 0 ∧ lambda Y' < 0) := by
      have hdec : decide (0 < lambda Y) = decide (0 < lambda Y') := hsign
      by_cases hp : 0 < lambda Y
      · left
        refine ⟨hp, ?_⟩
        simpa [sign, hp] using hdec
      · right
        have hYneg : lambda Y < 0 := lt_of_le_of_ne (not_lt.mp hp) (hlambda Y hY)
        have hp' : ¬ 0 < lambda Y' := by
          intro hp'
          simp [sign, hp, hp'] at hdec
        exact ⟨hYneg,
          lt_of_le_of_ne (not_lt.mp hp') (hlambda Y' hY')⟩
    let u : RawVector := Y - (α / q) • X
    let u' : RawVector := Y' - (α / q) • X
    let D : ℝ := (X ⨯₃ u) ⬝ᵥ u'
    have hD1 : 0 ≤ lambda Y * D := by
      have h := hexpose Y hY Y' hY'
      change 0 ≤ lambda Y * ((X ⨯₃ u) ⬝ᵥ (u' - u)) at h
      have hself : (X ⨯₃ u) ⬝ᵥ u = 0 := by
        rw [dotProduct_comm]
        exact dot_cross_self X u
      rw [dotProduct_sub, hself, sub_zero] at h
      exact h
    have hDswap : (X ⨯₃ u') ⬝ᵥ u = -D := by
      have hDtriple : D = X ⬝ᵥ (u ⨯₃ u') := by
        dsimp [D]
        rw [dotProduct_comm, triple_product_permutation u' X u]
      rw [hDtriple, dotProduct_comm (X ⨯₃ u') u,
        triple_product_permutation u X u', ← cross_anticomm u u', dotProduct_neg]
    have hD2 : 0 ≤ lambda Y' * (-D) := by
      have h := hexpose Y' hY' Y hY
      change 0 ≤ lambda Y' * ((X ⨯₃ u') ⬝ᵥ (u - u')) at h
      have hself : (X ⨯₃ u') ⬝ᵥ u' = 0 := by
        rw [dotProduct_comm]
        exact dot_cross_self X u'
      rw [dotProduct_sub, hself, sub_zero, hDswap] at h
      exact h
    have hD : D = 0 := by
      rcases hcase with hp | hn
      · have hDnonneg : 0 ≤ D := (mul_nonneg_iff_of_pos_left hp.1).mp hD1
        have hnegDnonneg : 0 ≤ -D := (mul_nonneg_iff_of_pos_left hp.2).mp hD2
        linarith
      · have hDnonpos : D ≤ 0 :=
          nonpos_of_mul_nonneg_left (by simpa [mul_comm] using hD1) hn.1
        have hnegDnonpos : -D ≤ 0 :=
          nonpos_of_mul_nonneg_left (by simpa [mul_comm] using hD2) hn.2
        linarith
    have hxu : X ⬝ᵥ u = 0 := by
      simp only [u, dotProduct_sub, dotProduct_smul, hXY Y hY, hXX, smul_eq_mul]
      field_simp
      ring
    have hxu' : X ⬝ᵥ u' = 0 := by
      simp only [u', dotProduct_sub, dotProduct_smul, hXY Y' hY', hXX, smul_eq_mul]
      field_simp
      ring
    have hU : u ⬝ᵥ u = q - α ^ 2 / q := by
      have hYX : Y ⬝ᵥ X = α := by rw [dotProduct_comm, hXY Y hY]
      simp only [u, sub_dotProduct, dotProduct_sub, smul_dotProduct,
        dotProduct_smul, hYY Y hY, hYX, hXY Y hY, hXX, smul_eq_mul]
      field_simp
      ring
    have hU' : u' ⬝ᵥ u' = q - α ^ 2 / q := by
      have hY'X : Y' ⬝ᵥ X = α := by rw [dotProduct_comm, hXY Y' hY']
      simp only [u', sub_dotProduct, dotProduct_sub, smul_dotProduct,
        dotProduct_smul, hYY Y' hY', hY'X, hXY Y' hY', hXX, smul_eq_mul]
      field_simp
      ring
    have hUpos : 0 < u ⬝ᵥ u := by
      rw [hU, sub_pos, div_lt_iff₀ hq]
      nlinarith [mul_pos (sub_pos.mpr hαq) (by nlinarith : 0 < q + α)]
    let j : RawVector := X ⨯₃ u
    have hjj : j ⬝ᵥ j = q * (u ⬝ᵥ u) := by
      simpa [j, hXX, hxu, dotProduct_comm u X] using cross_dot_cross X u X u
    have hj_ne : j ≠ 0 := by
      intro hj
      have : j ⬝ᵥ j = 0 := by simp [hj]
      rw [hjj] at this
      nlinarith
    let gamma : ℝ := (u ⬝ᵥ u') / (u ⬝ᵥ u)
    let v : RawVector := u' - gamma • u
    have hxv : X ⬝ᵥ v = 0 := by simp [v, dotProduct_sub, dotProduct_smul, hxu, hxu']
    have huv : u ⬝ᵥ v = 0 := by
      simp only [v, dotProduct_sub, dotProduct_smul, smul_eq_mul, gamma]
      field_simp
      ring
    have hjv : j ⬝ᵥ v = 0 := by
      have hself : j ⬝ᵥ u = 0 := by
        dsimp [j]
        rw [dotProduct_comm]
        exact dot_cross_self X u
      simp only [v, dotProduct_sub, dotProduct_smul, smul_eq_mul, j, D, hD,
        hself, mul_zero, sub_zero]
    have hjv_cross : j ⨯₃ v = 0 := by
      rw [show j ⨯₃ v = (X ⬝ᵥ v) • u - (u ⬝ᵥ v) • X by
        simpa [j] using cross_cross_eq_smul_sub_smul X u v]
      simp [hxv, huv]
    have hvdep : ¬ LinearIndependent ℝ ![j, v] := by
      rw [← crossProduct_ne_zero_iff_linearIndependent]
      exact not_ne_iff.mpr hjv_cross
    rw [LinearIndependent.pair_iff' hj_ne] at hvdep
    push_neg at hvdep
    obtain ⟨mu, hmu⟩ := hvdep
    have hv0 : v = 0 := by
      have hmuj : mu * (j ⬝ᵥ j) = 0 := by
        rw [← hjv, ← hmu]
        simp [smul_dotProduct]
      have hmu0 : mu = 0 := by
        apply (mul_eq_zero.mp hmuj).resolve_right
        rw [hjj]
        exact mul_ne_zero (ne_of_gt hq) (ne_of_gt hUpos)
      rw [← hmu, hmu0, zero_smul]
    have hu' : u' = gamma • u := by simpa [v, sub_eq_zero] using hv0
    have hgamma_sq : gamma ^ 2 = 1 := by
      have := hU'
      rw [hu', smul_dotProduct, dotProduct_smul, hU] at this
      simp only [smul_eq_mul] at this
      rw [hU] at hUpos
      nlinarith
    have hgamma_nonneg : 0 ≤ gamma := by
      have hpair := hlo Y hY Y' hY'
      have huu' : 0 ≤ u ⬝ᵥ u' := by
        have hYX : Y ⬝ᵥ X = α := by rw [dotProduct_comm, hXY Y hY]
        have hY'X : Y' ⬝ᵥ X = α := by rw [dotProduct_comm, hXY Y' hY']
        have huu_formula : u ⬝ᵥ u' = Y ⬝ᵥ Y' - α ^ 2 / q := by
          simp only [u, u', sub_dotProduct, dotProduct_sub, smul_dotProduct,
            dotProduct_smul, hYX, hY'X, hXY Y hY, hXX, smul_eq_mul]
          rw [hXY Y' hY']
          field_simp
          ring
        have halpha : 0 ≤ α - α ^ 2 / q := by
          rw [sub_nonneg, div_le_iff₀ hq]
          nlinarith
        rw [huu_formula]
        nlinarith
      dsimp [gamma]
      exact div_nonneg huu' hUpos.le
    have hgamma : gamma = 1 := by nlinarith
    have huu : u' = u := by rw [hu', hgamma, one_smul]
    dsimp [u, u'] at huu
    exact sub_left_injective huu.symm
  have hmap : B.card = (B.image sign).card :=
    (Finset.card_image_iff.mpr hsign_inj).symm
  rw [hmap]
  calc
    (B.image sign).card ≤ (Finset.univ : Finset Bool).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = 2 := by decide

/-! ## Application to a diameter graph -/

/-- The geometric core of the spherical-thrackle proof: on a two-sphere of
radius at least `1 / sqrt 2`, a vertex has at most two unit-distance
neighbours which themselves have degree at least two. -/
theorem coreNeighbor_card_le_two
    {A : Finset (Point 3)} {c : Point 3} {r : ℝ}
    (hsphere : ∀ x ∈ A, dist x c = r)
    (hr : 1 / Real.sqrt 2 ≤ r) (hA : IsDiameterOne A)
    (x : {z // z ∈ A}) :
    (((diameterGraph A).neighborFinset x).filter fun y =>
      2 ≤ (diameterGraph A).degree y).card ≤ 2 := by
  classical
  let G := diameterGraph A
  let S := (G.neighborFinset x).filter fun y => 2 ≤ G.degree y
  let e : {z // z ∈ A} ↪ RawVector :=
    (Function.Embedding.subtype _).trans (translatedRawEmbedding c)
  let B : Finset RawVector := S.map e
  let q : ℝ := r ^ 2
  let α : ℝ := q - 1 / 2
  have hrpos : 0 < r := inv_sqrt_two_pos.trans_le hr
  have hq : 0 < q := sq_pos_of_pos hrpos
  have hhalf : 1 / 2 ≤ q := half_le_sq_of_inv_sqrt_two_le hr
  have hα : 0 ≤ α := sub_nonneg.mpr hhalf
  have hαq : α < q := by dsimp [α]; norm_num
  have hXX : e x ⬝ᵥ e x = q := by
    rw [show e x = translatedRaw c (x : Point 3) by rfl,
      translatedRaw_dot, inner_vsub_self_of_mem_sphere (hsphere x x.property)]
  have recover {Y : RawVector} (hY : Y ∈ B) :
      ∃ y ∈ S, e y = Y := by
    exact Finset.mem_map.mp hY
  have hYY : ∀ Y ∈ B, Y ⬝ᵥ Y = q := by
    intro Y hY
    obtain ⟨y, hy, rfl⟩ := recover hY
    rw [show e y = translatedRaw c (y : Point 3) by rfl,
      translatedRaw_dot, inner_vsub_self_of_mem_sphere (hsphere y y.property)]
  have hXY : ∀ Y ∈ B, e x ⬝ᵥ Y = α := by
    intro Y hY
    obtain ⟨y, hy, rfl⟩ := recover hY
    have hyS : y ∈ G.neighborFinset x := (Finset.mem_filter.mp hy).1
    have hxy : dist (x : Point 3) (y : Point 3) = 1 := by
      exact (G.mem_neighborFinset x y).mp hyS
    rw [show e x = translatedRaw c (x : Point 3) by rfl,
      show e y = translatedRaw c (y : Point 3) by rfl,
      translatedRaw_dot,
      inner_vsub_eq_of_dist_eq_one (hsphere x x.property)
        (hsphere y y.property) hxy]
  have hlo : ∀ Y ∈ B, ∀ Y' ∈ B, α ≤ Y ⬝ᵥ Y' := by
    intro Y hY Y' hY'
    obtain ⟨y, hy, rfl⟩ := recover hY
    obtain ⟨y', hy', rfl⟩ := recover hY'
    rw [show e y = translatedRaw c (y : Point 3) by rfl,
      show e y' = translatedRaw c (y' : Point 3) by rfl,
      translatedRaw_dot]
    exact inner_vsub_ge_of_dist_le_one (hsphere y y.property)
      (hsphere y' y'.property) (hA.dist_le y.property y'.property)
  have hhi : ∀ Y ∈ B, ∀ Y' ∈ B, Y ⬝ᵥ Y' ≤ q := by
    intro Y hY Y' hY'
    obtain ⟨y, hy, rfl⟩ := recover hY
    obtain ⟨y', hy', rfl⟩ := recover hY'
    rw [show e y = translatedRaw c (y : Point 3) by rfl,
      show e y' = translatedRaw c (y' : Point 3) by rfl,
      translatedRaw_dot]
    exact inner_vsub_le_sq (hsphere y y.property) (hsphere y' y'.property)
  have hwitness : ∀ Y ∈ B, ∃ Z : RawVector,
      Z ⬝ᵥ Z = q ∧ Y ⬝ᵥ Z = α ∧
      α ≤ e x ⬝ᵥ Z ∧ e x ⬝ᵥ Z < q ∧
      ∀ Y' ∈ B, α ≤ Z ⬝ᵥ Y' := by
    intro Y hY
    obtain ⟨y, hy, rfl⟩ := recover hY
    have hycore : 2 ≤ G.degree y := (Finset.mem_filter.mp hy).2
    have hyx_mem : x ∈ G.neighborFinset y := by
      have hyS : y ∈ G.neighborFinset x := (Finset.mem_filter.mp hy).1
      exact (G.mem_neighborFinset y x).mpr ((G.mem_neighborFinset x y).mp hyS).symm
    have hone : 1 < (G.neighborFinset y).card := by
      change 1 < G.degree y
      omega
    obtain ⟨z₁, hz₁, z₂, hz₂, hz_ne⟩ := Finset.one_lt_card.mp hone
    obtain ⟨z, hz, hzx⟩ : ∃ z ∈ G.neighborFinset y, z ≠ x := by
      by_cases h₁ : z₁ = x
      · exact ⟨z₂, hz₂, fun h₂ => hz_ne (h₁.trans h₂.symm)⟩
      · exact ⟨z₁, hz₁, h₁⟩
    refine ⟨e z, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show e z = translatedRaw c (z : Point 3) by rfl,
        translatedRaw_dot, inner_vsub_self_of_mem_sphere (hsphere z z.property)]
    · have hyz : dist (y : Point 3) (z : Point 3) = 1 :=
        (G.mem_neighborFinset y z).mp hz
      rw [show e y = translatedRaw c (y : Point 3) by rfl,
        show e z = translatedRaw c (z : Point 3) by rfl,
        translatedRaw_dot,
        inner_vsub_eq_of_dist_eq_one (hsphere y y.property)
          (hsphere z z.property) hyz]
    · rw [show e x = translatedRaw c (x : Point 3) by rfl,
        show e z = translatedRaw c (z : Point 3) by rfl,
        translatedRaw_dot]
      exact inner_vsub_ge_of_dist_le_one (hsphere x x.property)
        (hsphere z z.property) (hA.dist_le x.property z.property)
    · rw [show e x = translatedRaw c (x : Point 3) by rfl,
        show e z = translatedRaw c (z : Point 3) by rfl,
        translatedRaw_dot]
      exact inner_vsub_lt_sq_of_ne (hsphere x x.property)
        (hsphere z z.property) (fun h => hzx (Subtype.ext h.symm))
    · intro Y' hY'
      obtain ⟨y', hy', rfl⟩ := recover hY'
      rw [show e z = translatedRaw c (z : Point 3) by rfl,
        show e y' = translatedRaw c (y' : Point 3) by rfl,
        translatedRaw_dot]
      exact inner_vsub_ge_of_dist_le_one (hsphere z z.property)
        (hsphere y' y'.property) (hA.dist_le z.property y'.property)
  have hB : B.card ≤ 2 :=
    card_le_two_of_endpoint_certificates hq hα hαq hXX hYY hXY hlo hhi hwitness
  simpa [B, S] using hB

/-- A diameter-one set contained in a two-sphere of radius at least
`1 / sqrt 2` has at most one diameter pair per point. -/
theorem diameterPairCount_le_card
    {A : Finset (Point 3)} {c : Point 3} {r : ℝ}
    (hsphere : ∀ x ∈ A, dist x c = r)
    (hr : 1 / Real.sqrt 2 ≤ r) (hA : IsDiameterOne A) :
    diameterPairCount A ≤ A.card := by
  classical
  have hcore : ∀ x : {z // z ∈ A},
      (((diameterGraph A).neighborFinset x).filter fun y =>
        2 ≤ (diameterGraph A).degree y).card ≤ 2 :=
    coreNeighbor_card_le_two hsphere hr hA
  have h := card_edgeFinset_le_card_of_coreNeighbor_le_two (diameterGraph A) hcore
  simpa [diameterPairCount] using h

end

end SphericalThrackle
end Erdos223
