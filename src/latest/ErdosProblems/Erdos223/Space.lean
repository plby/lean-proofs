/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos223.Basic
import ErdosProblems.Erdos223.SphericalEuler
import ErdosProblems.Erdos223.SphericalEuler.VazsonyiBridge

/-!
# Erdős Problem 223 in three-dimensional space

This file develops the three-dimensional case of Vázsonyi's diameter problem.
It supplies explicit sharp configurations, proves the exceptional small cases,
and connects the sharp upper bound to the finite spherical Euler certificate.
-/

open Metric
open scoped BigOperators EuclideanGeometry RealInnerProductSpace SimpleGraph

namespace Erdos223

/-! ## The spherical Euler interface -/

/-- The finite Euler certificate for the canonical bipartite double cover gives
the sharp Vázsonyi count.  The geometric part of the upper-bound proof is exactly
the construction of this certificate. -/
theorem diameterPairCount_add_two_le_of_doubleCover_certificate
    {A : Finset (Point 3)} (hA : A.Nonempty)
    (C : SimpleGraph.SphereRotationCertificate
      (diameterGraph A).bipartiteDoubleCover) :
    diameterPairCount A + 2 ≤ 2 * A.card := by
  classical
  obtain ⟨x, hx⟩ := hA
  letI : Nonempty {x // x ∈ A} := ⟨⟨x, hx⟩⟩
  simpa [diameterPairCount] using
    SimpleGraph.edge_add_two_le_two_mul_vertex_of_doubleCover_certificate C

/-- The inductively constructed ribbon certificate gives the same sharp edge
bound, with its Euler equality derived from the construction. -/
theorem diameterPairCount_add_two_le_of_constructible_doubleCover_certificate
    {A : Finset (Point 3)} (hA : A.Nonempty)
    (C : SimpleGraph.ConstructibleSphereRotationCertificate
      (diameterGraph A).bipartiteDoubleCover) :
    diameterPairCount A + 2 ≤ 2 * A.card := by
  classical
  obtain ⟨x, hx⟩ := hA
  letI : Nonempty {x // x ∈ A} := ⟨⟨x, hx⟩⟩
  simpa [diameterPairCount] using
    SimpleGraph.edge_add_two_le_two_mul_vertex_of_constructible_doubleCover_certificate C

/-! ## Peeling to a minimum-degree-two core -/

/-- Peeling vertices of degree at most one reduces the sharp linear edge
bound to an induced core of minimum degree at least two.  `Good` packages a
property inherited by induced subgraphs. -/
private theorem edge_add_two_le_two_mul_card_of_induce_peeling
    {V : Type} [Fintype V] [Nonempty V]
    (Good : ∀ (W : Type) [Fintype W], SimpleGraph W → Prop)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : Good V G)
    (hcore : ∀ (W : Type) [Fintype W] [Nonempty W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj], Good W H →
        (∀ w : W, 2 ≤ H.degree w) →
          H.edgeFinset.card + 2 ≤ 2 * Fintype.card W)
    (hinduce : ∀ (W : Type) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj], Good W H →
        ∀ v : W, Good {x : W // x ∈ ({v}ᶜ : Set W)}
          (H.induce ({v}ᶜ : Set W))) :
    G.edgeFinset.card + 2 ≤ 2 * Fintype.card V := by
  classical
  induction hn : Fintype.card V using Nat.strong_induction_on generalizing V with
  | h n ih =>
      by_cases hmin : ∀ v : V, 2 ≤ G.degree v
      · simpa only [← hn] using hcore V G hG hmin
      · push Not at hmin
        obtain ⟨v, hv⟩ := hmin
        have hv' : G.degree v ≤ 1 := by omega
        by_cases hn_one : n = 1
        · have hedge := G.card_edgeFinset_le_card_choose_two
          have hedge_zero : G.edgeFinset.card = 0 := by
            have hchoose : (1 : Nat).choose 2 = 0 := by decide
            have : G.edgeFinset.card ≤ 0 := by
              rw [hn, hn_one, hchoose] at hedge
              exact hedge
            omega
          rw [hedge_zero]
          omega
        · let K := G.induce ({v}ᶜ : Set V)
          have hn_gt_one : 1 < n := by
            have hn_pos : 0 < n := by
              rw [← hn, Fintype.card_pos_iff]
              exact ⟨v⟩
            omega
          have hcardK : Fintype.card {x : V // x ∈ ({v}ᶜ : Set V)} = n - 1 := by
            simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
            rw [Fintype.card_subtype_compl]
            simp [hn]
          have hcardK_pos : 0 < Fintype.card {x : V // x ∈ ({v}ᶜ : Set V)} := by
            omega
          let _ : Nonempty {x : V // x ∈ ({v}ᶜ : Set V)} :=
            Fintype.card_pos_iff.mp hcardK_pos
          have hcardK_lt : Fintype.card {x : V // x ∈ ({v}ᶜ : Set V)} < n := by
            omega
          have hGoodK := hinduce V G hG v
          have hboundK := ih _ hcardK_lt K hGoodK rfl
          have hedgeK := G.card_edgeFinset_induce_compl_singleton v
          have hedgeDel := G.card_edgeFinset_deleteIncidenceSet v
          dsimp [K] at hboundK
          omega

/-- To prove the sharp upper bound for every diameter-one configuration, it
suffices to construct the spherical certificate when every vertex has degree
at least two.  The proof transports induced graphs to honest finite point sets
and then applies the graph-theoretic peeling lemma above. -/
theorem diameterPairCount_add_two_le_of_minDegree_certificates
    (hcert : ∀ (B : Finset (Point 3)), IsDiameterOne B →
      (∀ v, 2 ≤ (diameterGraph B).degree v) →
      SimpleGraph.ConstructibleSphereRotationCertificate
        (diameterGraph B).bipartiteDoubleCover)
    (A : Finset (Point 3)) (hA : IsDiameterOne A) :
    diameterPairCount A + 2 ≤ 2 * A.card := by
  classical
  let V := {x // x ∈ A}
  let G := diameterGraph A
  let p : V ↪ Point 3 := Function.Embedding.subtype (fun x ↦ x ∈ A)
  letI : Nonempty V := by
    obtain ⟨x, hx, -⟩ := hA.exists_dist_eq_one
    exact ⟨⟨x, hx⟩⟩
  let Good : ∀ (W : Type) [Fintype W], SimpleGraph W → Prop :=
    fun W _ H ↦ ∃ q : W ↪ Point 3,
      (∀ x y, dist (q x) (q y) ≤ 1) ∧
      (∀ x y, H.Adj x y ↔ dist (q x) (q y) = 1)
  have hgood : Good V G := by
    refine ⟨p, ?_, ?_⟩
    · intro x y
      exact hA.dist_le x.prop y.prop
    · intro x y
      rfl
  have hcore : ∀ (W : Type) [Fintype W] [Nonempty W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj], Good W H →
        (∀ w : W, 2 ≤ H.degree w) →
          H.edgeFinset.card + 2 ≤ 2 * Fintype.card W := by
    intro W _ _ _ H _ hgoodW hmin
    obtain ⟨q, hdist, hadj⟩ := hgoodW
    let B : Finset (Point 3) := Finset.univ.map q
    have hcardB : B.card = Fintype.card W := by
      simp [B]
    have hBdiam : IsDiameterOne B := by
      rw [isDiameterOne_iff]
      constructor
      · intro x hx y hy
        obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
        obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hy
        exact hdist i j
      · let w : W := Classical.choice inferInstance
        have hwpos : 0 < H.degree w := lt_of_lt_of_le (by omega) (hmin w)
        obtain ⟨z, hwz⟩ := (H.degree_pos_iff_exists_adj w).mp hwpos
        refine ⟨q w, ?_, q z, ?_, ?_⟩
        · exact Finset.mem_map.mpr ⟨w, Finset.mem_univ w, rfl⟩
        · exact Finset.mem_map.mpr ⟨z, Finset.mem_univ z, rfl⟩
        · exact (hadj w z).mp hwz
    let e : W ≃ {x // x ∈ B} :=
      Equiv.ofBijective
        (fun w ↦ (⟨q w, Finset.mem_map.mpr ⟨w, Finset.mem_univ w, rfl⟩⟩ : {x // x ∈ B}))
        ⟨fun _ _ h ↦ q.injective (congrArg Subtype.val h), by
          intro x
          obtain ⟨w, -, hw⟩ := Finset.mem_map.mp x.prop
          exact ⟨w, Subtype.ext hw⟩⟩
    let iso : H ≃g diameterGraph B :=
      ⟨e, by
        intro x y
        change dist (q x) (q y) = 1 ↔ H.Adj x y
        exact (hadj x y).symm⟩
    have hminB : ∀ v, 2 ≤ (diameterGraph B).degree v := by
      intro v
      have heq : (diameterGraph B).degree v = H.degree (iso.symm v) := by
        simpa using iso.degree_eq (iso.symm v)
      rw [heq]
      exact hmin (iso.symm v)
    have hb := diameterPairCount_add_two_le_of_constructible_doubleCover_certificate
      (A := B) (by
        let w : W := Classical.choice inferInstance
        exact ⟨q w, Finset.mem_map.mpr ⟨w, Finset.mem_univ w, rfl⟩⟩)
      (hcert B hBdiam hminB)
    rw [diameterPairCount, ← iso.card_edgeFinset_eq, hcardB] at hb
    exact hb
  have hinduce : ∀ (W : Type) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj], Good W H →
        ∀ v : W, Good {x : W // x ∈ ({v}ᶜ : Set W)}
          (H.induce ({v}ᶜ : Set W)) := by
    intro W _ _ H _ hgoodW v
    obtain ⟨q, hdist, hadj⟩ := hgoodW
    let j : {x : W // x ∈ ({v}ᶜ : Set W)} ↪ W :=
      Function.Embedding.subtype (fun x ↦ x ∈ ({v}ᶜ : Set W))
    refine ⟨j.trans q, ?_, ?_⟩
    · exact fun x y ↦ hdist x y
    · exact fun x y ↦ hadj x y
  have hbound := edge_add_two_le_two_mul_card_of_induce_peeling
    Good G hgood hcore hinduce
  simpa [G, V, diameterPairCount] using hbound

/-- A direct sharp bound for every minimum-degree-two diameter graph extends
to all diameter-one configurations by deleting vertices of degree at most
one.  This variant is the interface used by a planar-drawing edge theorem
when that theorem returns the numerical bound rather than a rotation
certificate. -/
theorem diameterPairCount_add_two_le_of_minDegree_upper
    (hcoreUpper : ∀ (B : Finset (Point 3)), IsDiameterOne B →
      (∀ v, 2 ≤ (diameterGraph B).degree v) →
      diameterPairCount B + 2 ≤ 2 * B.card)
    (A : Finset (Point 3)) (hA : IsDiameterOne A) :
    diameterPairCount A + 2 ≤ 2 * A.card := by
  classical
  let V := {x // x ∈ A}
  let G := diameterGraph A
  let p : V ↪ Point 3 := Function.Embedding.subtype (fun x ↦ x ∈ A)
  letI : Nonempty V := by
    obtain ⟨x, hx, -⟩ := hA.exists_dist_eq_one
    exact ⟨⟨x, hx⟩⟩
  let Good : ∀ (W : Type) [Fintype W], SimpleGraph W → Prop :=
    fun W _ H ↦ ∃ q : W ↪ Point 3,
      (∀ x y, dist (q x) (q y) ≤ 1) ∧
      (∀ x y, H.Adj x y ↔ dist (q x) (q y) = 1)
  have hgood : Good V G := by
    refine ⟨p, ?_, ?_⟩
    · intro x y
      exact hA.dist_le x.prop y.prop
    · intro x y
      rfl
  have hcore : ∀ (W : Type) [Fintype W] [Nonempty W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj], Good W H →
        (∀ w : W, 2 ≤ H.degree w) →
          H.edgeFinset.card + 2 ≤ 2 * Fintype.card W := by
    intro W _ _ _ H _ hgoodW hmin
    obtain ⟨q, hdist, hadj⟩ := hgoodW
    let B : Finset (Point 3) := Finset.univ.map q
    have hcardB : B.card = Fintype.card W := by
      simp [B]
    have hBdiam : IsDiameterOne B := by
      rw [isDiameterOne_iff]
      constructor
      · intro x hx y hy
        obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
        obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hy
        exact hdist i j
      · let w : W := Classical.choice inferInstance
        have hwpos : 0 < H.degree w := lt_of_lt_of_le (by omega) (hmin w)
        obtain ⟨z, hwz⟩ := (H.degree_pos_iff_exists_adj w).mp hwpos
        refine ⟨q w, ?_, q z, ?_, ?_⟩
        · exact Finset.mem_map.mpr ⟨w, Finset.mem_univ w, rfl⟩
        · exact Finset.mem_map.mpr ⟨z, Finset.mem_univ z, rfl⟩
        · exact (hadj w z).mp hwz
    let e : W ≃ {x // x ∈ B} :=
      Equiv.ofBijective
        (fun w ↦ (⟨q w, Finset.mem_map.mpr ⟨w, Finset.mem_univ w, rfl⟩⟩ : {x // x ∈ B}))
        ⟨fun _ _ h ↦ q.injective (congrArg Subtype.val h), by
          intro x
          obtain ⟨w, -, hw⟩ := Finset.mem_map.mp x.prop
          exact ⟨w, Subtype.ext hw⟩⟩
    let iso : H ≃g diameterGraph B :=
      ⟨e, by
        intro x y
        change dist (q x) (q y) = 1 ↔ H.Adj x y
        exact (hadj x y).symm⟩
    have hminB : ∀ v, 2 ≤ (diameterGraph B).degree v := by
      intro v
      have heq : (diameterGraph B).degree v = H.degree (iso.symm v) := by
        simpa using iso.degree_eq (iso.symm v)
      rw [heq]
      exact hmin (iso.symm v)
    have hb := hcoreUpper B hBdiam hminB
    rw [diameterPairCount, ← iso.card_edgeFinset_eq, hcardB] at hb
    exact hb
  have hinduce : ∀ (W : Type) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj], Good W H →
        ∀ v : W, Good {x : W // x ∈ ({v}ᶜ : Set W)}
          (H.induce ({v}ᶜ : Set W)) := by
    intro W _ _ H _ hgoodW v
    obtain ⟨q, hdist, hadj⟩ := hgoodW
    let j : {x : W // x ∈ ({v}ᶜ : Set W)} ↪ W :=
      Function.Embedding.subtype (fun x ↦ x ∈ ({v}ᶜ : Set W))
    refine ⟨j.trans q, ?_, ?_⟩
    · exact fun x y ↦ hdist x y
    · exact fun x y ↦ hadj x y
  have hbound := edge_add_two_le_two_mul_card_of_induce_peeling
    Good G hgood hcore hinduce
  simpa [G, V, diameterPairCount] using hbound

/-! ## Explicit sharp configurations -/

namespace Sharp3

noncomputable section

def basePoint (t : ℝ) : Point 3 :=
  EuclideanSpace.single (0 : Fin 3)
      ((Real.sqrt 3 / 2) * ((1 - t ^ 2) / (1 + t ^ 2))) +
    EuclideanSpace.single (1 : Fin 3)
      ((Real.sqrt 3) * t / (1 + t ^ 2))

def polePoint (j : Fin 2) : Point 3 :=
  EuclideanSpace.single (2 : Fin 3)
    (if (j : ℕ) = 0 then (1 / 2 : ℝ) else -1 / 2)

lemma basePoint_apply_zero (t : ℝ) :
    basePoint t 0 = (Real.sqrt 3 / 2) * ((1 - t ^ 2) / (1 + t ^ 2)) := by
  simp [basePoint, EuclideanSpace.single_apply]

lemma basePoint_apply_one (t : ℝ) :
    basePoint t 1 = Real.sqrt 3 * t / (1 + t ^ 2) := by
  simp [basePoint, EuclideanSpace.single_apply]

lemma basePoint_apply_two (t : ℝ) : basePoint t 2 = 0 := by
  simp [basePoint, EuclideanSpace.single_apply]

lemma polePoint_apply_two (j : Fin 2) :
    polePoint j 2 = (if (j : ℕ) = 0 then (1 / 2 : ℝ) else -1 / 2) := by
  simp [polePoint, EuclideanSpace.single_apply]

lemma polePoint_apply_zero (j : Fin 2) : polePoint j 0 = 0 := by
  simp [polePoint, EuclideanSpace.single_apply]

lemma basePoint_norm_sq (t : ℝ) : ‖basePoint t‖ ^ 2 = 3 / 4 := by
  rw [← real_inner_self_eq_norm_sq]
  have hsqrt : Real.sqrt (3 : ℝ) ^ 2 = 3 := by norm_num
  simp only [basePoint, inner_add_left, inner_add_right,
    EuclideanSpace.inner_single_left, EuclideanSpace.single_apply,
    starRingEnd_apply, star_trivial]
  norm_num
  field_simp
  nlinarith

lemma polePoint_norm_sq (j : Fin 2) : ‖polePoint j‖ ^ 2 = 1 / 4 := by
  rw [← real_inner_self_eq_norm_sq]
  fin_cases j <;> norm_num [polePoint, EuclideanSpace.inner_single_left,
    EuclideanSpace.single_apply]

lemma inner_pole_base (j : Fin 2) (t : ℝ) :
    inner ℝ (polePoint j) (basePoint t) = 0 := by
  simp [polePoint, basePoint, inner_add_right, EuclideanSpace.inner_single_left,
    EuclideanSpace.single_apply]

lemma dist_pole_base (j : Fin 2) (t : ℝ) : dist (polePoint j) (basePoint t) = 1 := by
  have hsq : dist (polePoint j) (basePoint t) ^ 2 = 1 := by
    rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    rw [show inner ℝ (polePoint j) (polePoint j) = 1 / 4 by
      rw [real_inner_self_eq_norm_sq, polePoint_norm_sq]]
    rw [show inner ℝ (basePoint t) (basePoint t) = 3 / 4 by
      rw [real_inner_self_eq_norm_sq, basePoint_norm_sq]]
    rw [inner_pole_base]
    rw [real_inner_comm, inner_pole_base]
    norm_num
  have hd : 0 ≤ dist (polePoint j) (basePoint t) := dist_nonneg
  nlinarith

lemma dist_poles : dist (polePoint 0) (polePoint 1) = 1 := by
  rw [show polePoint 0 = EuclideanSpace.single (2 : Fin 3) (1 / 2 : ℝ) by
    simp [polePoint]]
  rw [show polePoint 1 = EuclideanSpace.single (2 : Fin 3) (-1 / 2 : ℝ) by
    simp [polePoint]]
  norm_num [Real.dist_eq, abs_of_nonneg, abs_of_nonpos]

lemma base_dist_sq (s t : ℝ) :
    dist (basePoint s) (basePoint t) ^ 2 =
      3 * (t - s) ^ 2 / ((1 + s ^ 2) * (1 + t ^ 2)) := by
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
  have hsqrt : Real.sqrt (3 : ℝ) ^ 2 = 3 := by norm_num
  simp only [basePoint, inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    EuclideanSpace.inner_single_left, EuclideanSpace.single_apply,
    starRingEnd_apply, star_trivial]
  norm_num
  field_simp
  rw [hsqrt]
  ring

lemma base_dist_le_one {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t)
    (htsq : t ^ 2 ≤ 1 / 2) : dist (basePoint s) (basePoint t) ≤ 1 := by
  have ht0 : 0 ≤ t := hs0.trans hst
  have hsqt : s ^ 2 ≤ t ^ 2 := (sq_le_sq₀ hs0 ht0).2 hst
  have hfirst : 0 ≤ 1 - 2 * t ^ 2 := by nlinarith
  have hfactor : 0 ≤ 6 * t - s * (2 - t ^ 2) := by
    have h2mt : 0 ≤ 2 - t ^ 2 := by nlinarith
    have hsmul : s * (2 - t ^ 2) ≤ t * (2 - t ^ 2) :=
      mul_le_mul_of_nonneg_right hst h2mt
    nlinarith [mul_nonneg ht0 h2mt]
  have hpoly :
      3 * (t - s) ^ 2 ≤ (1 + s ^ 2) * (1 + t ^ 2) := by
    nlinarith [mul_nonneg hs0 hfactor]
  have hden : 0 < (1 + s ^ 2) * (1 + t ^ 2) := by positivity
  have hsq := base_dist_sq s t
  have hdsq : dist (basePoint s) (basePoint t) ^ 2 ≤ 1 := by
    rw [hsq]
    exact (div_le_one hden).mpr hpoly
  have hd : 0 ≤ dist (basePoint s) (basePoint t) := dist_nonneg
  nlinarith

lemma base_dist_le_one' {s t : ℝ} (hs0 : 0 ≤ s) (ht0 : 0 ≤ t)
    (hsq : s ^ 2 ≤ 1 / 2) (htsq : t ^ 2 ≤ 1 / 2) :
    dist (basePoint s) (basePoint t) ≤ 1 := by
  rcases le_total s t with hst | hts
  · exact base_dist_le_one hs0 hst htsq
  · rw [dist_comm]
    exact base_dist_le_one ht0 hts hsq

lemma base_dist_endpoints : dist (basePoint 0) (basePoint (1 / Real.sqrt 2)) = 1 := by
  have hsqrt : Real.sqrt (2 : ℝ) ^ 2 = 2 := by norm_num
  have hsqrt0 : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hratio :
      3 * ((1 / Real.sqrt 2 : ℝ) - 0) ^ 2 /
          ((1 + (0 : ℝ) ^ 2) * (1 + (1 / Real.sqrt 2) ^ 2)) = 1 := by
    field_simp [hsqrt0]
    nlinarith
  have hsq := (base_dist_sq 0 (1 / Real.sqrt 2)).trans hratio
  have hd : 0 ≤ dist (basePoint 0) (basePoint (1 / Real.sqrt 2)) := dist_nonneg
  nlinarith

def parameter {m : ℕ} (hm : 1 < m) (i : Fin m) : ℝ :=
  (i : ℝ) / ((m - 1 : ℕ) : ℝ) / Real.sqrt 2

lemma parameter_nonneg {m : ℕ} (hm : 1 < m) (i : Fin m) : 0 ≤ parameter hm i := by
  unfold parameter
  positivity

lemma parameter_le_endpoint {m : ℕ} (hm : 1 < m) (i : Fin m) :
    parameter hm i ≤ 1 / Real.sqrt 2 := by
  unfold parameter
  have hden : 0 < (((m - 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.sub_pos_iff_lt.mpr hm
  have hi : (i : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_pred_of_lt i.isLt
  have hsqrt : 0 < Real.sqrt (2 : ℝ) := by positivity
  apply (div_le_div_iff_of_pos_right hsqrt).mpr
  exact (div_le_one hden).mpr hi

lemma parameter_sq_le_half {m : ℕ} (hm : 1 < m) (i : Fin m) :
    parameter hm i ^ 2 ≤ 1 / 2 := by
  have h := parameter_le_endpoint hm i
  have h0 := parameter_nonneg hm i
  have hsqrt : Real.sqrt (2 : ℝ) ^ 2 = 2 := by norm_num
  have hsqrt0 : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hend : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
    rw [div_pow, one_pow, hsqrt]
  nlinarith

lemma parameter_first {m : ℕ} (hm : 1 < m) :
    parameter hm ⟨0, Nat.zero_lt_of_lt hm⟩ = 0 := by simp [parameter]

lemma parameter_last {m : ℕ} (hm : 1 < m) :
    parameter hm ⟨m - 1, Nat.sub_lt (Nat.zero_lt_of_lt hm) zero_lt_one⟩ =
      1 / Real.sqrt 2 := by
  unfold parameter
  have hden : (((m - 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.sub_ne_zero_of_lt hm
  rw [div_self hden]

lemma parameter_injective {m : ℕ} (hm : 1 < m) : Function.Injective (parameter hm) := by
  intro i j hij
  unfold parameter at hij
  have hden : (((m - 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.sub_ne_zero_of_lt hm
  have hsqrt : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hcast : (i : ℝ) = (j : ℝ) := by
    field_simp [hden, hsqrt] at hij
    exact hij
  exact Fin.ext (by exact_mod_cast hcast)

lemma basePoint_injective_on_parameters {m : ℕ} (hm : 1 < m) :
    Function.Injective (fun i : Fin m ↦ basePoint (parameter hm i)) := by
  intro i j hij
  have hx := congrArg (fun z : Point 3 ↦ z 0) hij
  rw [basePoint_apply_zero, basePoint_apply_zero] at hx
  have hsqrt3 : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
  have hiDen : 0 < 1 + parameter hm i ^ 2 := by positivity
  have hjDen : 0 < 1 + parameter hm j ^ 2 := by positivity
  have hsquares : parameter hm i ^ 2 = parameter hm j ^ 2 := by
    field_simp [hsqrt3] at hx
    nlinarith
  have hparam : parameter hm i = parameter hm j := by
    nlinarith [parameter_nonneg hm i, parameter_nonneg hm j]
  exact parameter_injective hm hparam

def vertexPoint {m : ℕ} (hm : 1 < m) : Fin m ⊕ Fin 2 → Point 3
  | .inl i => basePoint (parameter hm i)
  | .inr j => polePoint j

lemma vertexPoint_injective {m : ℕ} (hm : 1 < m) : Function.Injective (vertexPoint hm) := by
  intro u v huv
  cases u with
  | inl i =>
      cases v with
      | inl j => exact congrArg Sum.inl (basePoint_injective_on_parameters hm huv)
      | inr j =>
          exfalso
          have hz := congrArg (fun z : Point 3 ↦ z 2) huv
          simp only [vertexPoint] at hz
          rw [basePoint_apply_two, polePoint_apply_two] at hz
          fin_cases j <;> norm_num at hz
  | inr i =>
      cases v with
      | inl j =>
          exfalso
          have hz := congrArg (fun z : Point 3 ↦ z 2) huv
          simp only [vertexPoint] at hz
          rw [polePoint_apply_two, basePoint_apply_two] at hz
          fin_cases i <;> norm_num at hz
      | inr j =>
          apply congrArg Sum.inr
          have hz := congrArg (fun z : Point 3 ↦ z 2) huv
          simp only [vertexPoint] at hz
          rw [polePoint_apply_two, polePoint_apply_two] at hz
          fin_cases i <;> fin_cases j <;>
            (try rfl) <;> norm_num [div_eq_mul_inv] at hz

def vertexEmbedding {m : ℕ} (hm : 1 < m) : (Fin m ⊕ Fin 2) ↪ Point 3 :=
  ⟨vertexPoint hm, vertexPoint_injective hm⟩

def configuration {m : ℕ} (hm : 1 < m) : Finset (Point 3) :=
  Finset.univ.map (vertexEmbedding hm)

lemma card_configuration {m : ℕ} (hm : 1 < m) : (configuration hm).card = m + 2 := by
  simp [configuration]

lemma mem_configuration {m : ℕ} (hm : 1 < m) (v : Fin m ⊕ Fin 2) :
    vertexPoint hm v ∈ configuration hm := by
  exact Finset.mem_map.mpr ⟨v, Finset.mem_univ v, rfl⟩

lemma vertex_dist_le_one {m : ℕ} (hm : 1 < m) (u v : Fin m ⊕ Fin 2) :
    dist (vertexPoint hm u) (vertexPoint hm v) ≤ 1 := by
  cases u with
  | inl i =>
      cases v with
      | inl j =>
          simpa [vertexPoint] using
            (base_dist_le_one' (parameter_nonneg hm i) (parameter_nonneg hm j)
              (parameter_sq_le_half hm i) (parameter_sq_le_half hm j))
      | inr j => simpa [vertexPoint, dist_comm] using (dist_pole_base j (parameter hm i)).le
  | inr i =>
      cases v with
      | inl j => simpa [vertexPoint] using (dist_pole_base i (parameter hm j)).le
      | inr j =>
          fin_cases i <;> fin_cases j <;> simp [vertexPoint, dist_poles, dist_comm]

lemma isDiameterOne_configuration {m : ℕ} (hm : 1 < m) :
    IsDiameterOne (configuration hm) := by
  rw [isDiameterOne_iff]
  constructor
  · intro x hx y hy
    obtain ⟨u, -, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨v, -, rfl⟩ := Finset.mem_map.mp hy
    exact vertex_dist_le_one hm u v
  · refine ⟨polePoint 0, mem_configuration hm (.inr 0),
      polePoint 1, mem_configuration hm (.inr 1), dist_poles⟩

def firstBase {m : ℕ} (hm : 1 < m) : Fin m ⊕ Fin 2 :=
  .inl ⟨0, Nat.zero_lt_of_lt hm⟩

def lastBase {m : ℕ} (hm : 1 < m) : Fin m ⊕ Fin 2 :=
  .inl ⟨m - 1, Nat.sub_lt (Nat.zero_lt_of_lt hm) zero_lt_one⟩

def north {m : ℕ} : Fin m ⊕ Fin 2 := .inr 0
def south {m : ℕ} : Fin m ⊕ Fin 2 := .inr 1

/-- The `K_{m,2}` pole--base edges, together with the pole edge and the
endpoint chord of the base arc. -/
def witnessGraph {m : ℕ} (hm : 1 < m) : SimpleGraph (Fin m ⊕ Fin 2) :=
  (completeBipartiteGraph (Fin m) (Fin 2) ⊔
      SimpleGraph.edge (firstBase hm) (lastBase hm)) ⊔
    SimpleGraph.edge north south

noncomputable instance witnessGraph.instDecidableRel {m : ℕ} (hm : 1 < m) :
    DecidableRel (witnessGraph hm).Adj := Classical.decRel _

lemma ncard_completeBipartite (m : ℕ) :
    (completeBipartiteGraph (Fin m) (Fin 2)).edgeSet.ncard = 2 * m := by
  rw [Set.ncard_def, SimpleGraph.encard_edgeSet_completeBipartiteGraph]
  simp [mul_comm]

lemma firstBase_ne_lastBase {m : ℕ} (hm : 1 < m) : firstBase hm ≠ lastBase hm := by
  intro h
  have hv := congrArg Fin.val (Sum.inl.inj h)
  simp [firstBase, lastBase] at hv
  omega

lemma card_witnessGraph {m : ℕ} (hm : 1 < m) :
    (witnessGraph hm).edgeFinset.card = 2 * m + 2 := by
  classical
  let K := completeBipartiteGraph (Fin m) (Fin 2)
  letI : DecidableRel K.Adj := Classical.decRel _
  have hK : K.edgeFinset.card = 2 * m := by
    rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
    simpa [K] using ncard_completeBipartite m
  have hbase_not : ¬ K.Adj (firstBase hm) (lastBase hm) := by
    simp [K, firstBase, lastBase, completeBipartiteGraph]
  have hbase_ne : firstBase hm ≠ lastBase hm := firstBase_ne_lastBase hm
  have h1 := K.card_edgeFinset_sup_edge hbase_not hbase_ne
  let K1 := K ⊔ SimpleGraph.edge (firstBase hm) (lastBase hm)
  letI : DecidableRel K1.Adj := Classical.decRel _
  have hpole_not : ¬ K1.Adj north south := by
    simp [K1, K, north, south, completeBipartiteGraph,
      firstBase, lastBase, SimpleGraph.edge_adj]
  have hpole_ne : (north : Fin m ⊕ Fin 2) ≠ south := by simp [north, south]
  have h2 := K1.card_edgeFinset_sup_edge hpole_not hpole_ne
  have h2' :
      ((completeBipartiteGraph (Fin m) (Fin 2) ⊔
          SimpleGraph.edge (firstBase hm) (lastBase hm)) ⊔
        SimpleGraph.edge north south).edgeFinset.card =
      (completeBipartiteGraph (Fin m) (Fin 2) ⊔
          SimpleGraph.edge (firstBase hm) (lastBase hm)).edgeFinset.card + 1 := by
    simpa [K1, K] using h2
  have h1' :
      (completeBipartiteGraph (Fin m) (Fin 2) ⊔
        SimpleGraph.edge (firstBase hm) (lastBase hm)).edgeFinset.card =
      (completeBipartiteGraph (Fin m) (Fin 2)).edgeFinset.card + 1 := by
    simpa [K] using h1
  have h2n := h2'
  rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset,
    ← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset] at h2n
  have h1n := h1'
  rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset,
    ← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset] at h1n
  have hKn := hK
  rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset] at hKn
  rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
  unfold witnessGraph
  rw [h2n, h1n, hKn]

lemma dist_eq_one_of_witnessGraph_adj {m : ℕ} (hm : 1 < m)
    {u v : Fin m ⊕ Fin 2} (huv : (witnessGraph hm).Adj u v) :
    dist (vertexPoint hm u) (vertexPoint hm v) = 1 := by
  change ((completeBipartiteGraph (Fin m) (Fin 2)).Adj u v ∨
      (SimpleGraph.edge (firstBase hm) (lastBase hm)).Adj u v) ∨
    (SimpleGraph.edge north south).Adj u v at huv
  rcases huv with (hcross | hbase) | hpole
  · cases u with
    | inl i =>
        cases v with
        | inl j => simp [completeBipartiteGraph] at hcross
        | inr j =>
            simpa [vertexPoint, dist_comm] using dist_pole_base j (parameter hm i)
    | inr i =>
        cases v with
        | inl j => simpa [vertexPoint] using dist_pole_base i (parameter hm j)
        | inr j => simp [completeBipartiteGraph] at hcross
  · rcases ((SimpleGraph.edge_adj _ _ _ _).mp hbase).1 with h | h
    · rcases h with ⟨rfl, rfl⟩
      simpa [vertexPoint, firstBase, lastBase, parameter_first, parameter_last] using
        base_dist_endpoints
    · rcases h with ⟨rfl, rfl⟩
      simpa [vertexPoint, firstBase, lastBase, parameter_first, parameter_last, dist_comm] using
        base_dist_endpoints
  · rcases ((SimpleGraph.edge_adj _ _ _ _).mp hpole).1 with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact dist_poles
    · rcases h with ⟨rfl, rfl⟩
      simpa [vertexPoint, north, south, dist_comm] using dist_poles

def configurationVertexEmbedding {m : ℕ} (hm : 1 < m) :
    (Fin m ⊕ Fin 2) ↪ {x // x ∈ configuration hm} where
  toFun v := ⟨vertexPoint hm v, mem_configuration hm v⟩
  inj' := by
    intro u v huv
    apply vertexPoint_injective hm
    exact congrArg Subtype.val huv

lemma witnessGraph_map_le_diameterGraph {m : ℕ} (hm : 1 < m) :
    (witnessGraph hm).map (configurationVertexEmbedding hm) ≤
      diameterGraph (configuration hm) := by
  intro x y hxy
  obtain ⟨u, v, huv, rfl, rfl⟩ :=
    (SimpleGraph.map_adj (configurationVertexEmbedding hm) (witnessGraph hm) x y).mp hxy
  exact dist_eq_one_of_witnessGraph_adj hm huv

lemma witness_count_le_diameterPairCount {m : ℕ} (hm : 1 < m) :
    2 * m + 2 ≤ diameterPairCount (configuration hm) := by
  classical
  have hmono := SimpleGraph.edgeFinset_mono (witnessGraph_map_le_diameterGraph hm)
  have hcard := Finset.card_le_card hmono
  rw [SimpleGraph.card_edgeFinset_map, card_witnessGraph] at hcard
  exact hcard

/-- Explicit sharp lower configuration for the three-dimensional problem. -/
theorem exists_sharp_configuration (n : ℕ) (hn : 4 ≤ n) :
    ∃ A : Finset (Point 3), A.card = n ∧ IsDiameterOne A ∧
      2 * n - 2 ≤ diameterPairCount A := by
  have hm : 1 < n - 2 := by omega
  refine ⟨configuration hm, ?_, isDiameterOne_configuration hm, ?_⟩
  · rw [card_configuration]
    omega
  · have h := witness_count_le_diameterPairCount hm
    omega

/-- The explicit construction gives the sharp lower bound. -/
theorem sharp_lower_bound (n : ℕ) (hn : 4 ≤ n) : 2 * n - 2 ≤ f 3 n :=
  le_f_of_exists (exists_sharp_configuration n hn)

/-! ## The three-point exception -/

def trianglePoint : Fin 3 → Point 3
  | 0 => polePoint 0
  | 1 => polePoint 1
  | 2 => basePoint 0

lemma trianglePoint_injective : Function.Injective trianglePoint := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals
    exfalso
    have h := congrArg (fun z : Point 3 ↦ z 2) hij
    simp [trianglePoint, polePoint_apply_two, basePoint_apply_two] at h <;>
      norm_num at h

def triangleEmbedding : Fin 3 ↪ Point 3 :=
  ⟨trianglePoint, trianglePoint_injective⟩

def triangleConfiguration : Finset (Point 3) :=
  Finset.univ.map triangleEmbedding

@[simp] lemma card_triangleConfiguration : triangleConfiguration.card = 3 := by
  simp [triangleConfiguration]

lemma mem_triangleConfiguration (i : Fin 3) : trianglePoint i ∈ triangleConfiguration := by
  exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩

lemma triangle_dist_eq_one {i j : Fin 3} (hij : i ≠ j) :
    dist (trianglePoint i) (trianglePoint j) = 1 := by
  fin_cases i <;> fin_cases j
  · contradiction
  · exact dist_poles
  · simpa [trianglePoint] using dist_pole_base (0 : Fin 2) (0 : ℝ)
  · simpa [trianglePoint, dist_comm] using dist_poles
  · contradiction
  · simpa [trianglePoint] using dist_pole_base (1 : Fin 2) (0 : ℝ)
  · simpa [trianglePoint, dist_comm] using dist_pole_base (0 : Fin 2) (0 : ℝ)
  · simpa [trianglePoint, dist_comm] using dist_pole_base (1 : Fin 2) (0 : ℝ)
  · contradiction

lemma isDiameterOne_triangleConfiguration : IsDiameterOne triangleConfiguration := by
  rw [isDiameterOne_iff]
  constructor
  · intro x hx y hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hy
    by_cases hij : i = j
    · subst j
      simp
    · exact (triangle_dist_eq_one hij).le
  · exact ⟨trianglePoint 0, mem_triangleConfiguration 0,
      trianglePoint 1, mem_triangleConfiguration 1,
      triangle_dist_eq_one (by decide)⟩

def triangleConfigurationVertexEmbedding :
    Fin 3 ↪ {x // x ∈ triangleConfiguration} where
  toFun i := ⟨trianglePoint i, mem_triangleConfiguration i⟩
  inj' i j h := trianglePoint_injective (congrArg Subtype.val h)

lemma top_map_le_triangle_diameterGraph :
    (⊤ : SimpleGraph (Fin 3)).map triangleConfigurationVertexEmbedding ≤
      diameterGraph triangleConfiguration := by
  intro x y hxy
  obtain ⟨i, j, hij, rfl, rfl⟩ :=
    (SimpleGraph.map_adj triangleConfigurationVertexEmbedding (⊤ : SimpleGraph (Fin 3)) x y).mp hxy
  exact triangle_dist_eq_one hij

lemma triangle_diameterGraph_eq_top :
    diameterGraph triangleConfiguration = ⊤ := by
  apply le_antisymm
  · exact le_top
  · intro x y hxy
    rcases x with ⟨x, hx⟩
    rcases y with ⟨y, hy⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hy
    rw [diameterGraph_adj]
    apply triangle_dist_eq_one
    intro hij
    subst j
    exact (⊤ : SimpleGraph {x // x ∈ triangleConfiguration}).loopless.irrefl _ hxy

lemma triangle_pair_count : diameterPairCount triangleConfiguration = 3 := by
  classical
  change (diameterGraph triangleConfiguration).edgeFinset.card = 3
  rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset,
    triangle_diameterGraph_eq_top, ← SimpleGraph.coe_edgeFinset,
    Set.ncard_coe_finset, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  norm_num

/-- Exactly three diameter pairs are possible for three points in space. -/
theorem f_space_three : f 3 3 = 3 := by
  apply Nat.le_antisymm
  · simpa using f_le_choose 3 3
  · exact le_f_of_exists ⟨triangleConfiguration, card_triangleConfiguration,
      isDiameterOne_triangleConfiguration, triangle_pair_count.ge⟩

/-- Four points attain all six possible pairs, so the spatial formula starts at `n = 4`. -/
theorem f_space_four : f 3 4 = 6 := by
  apply Nat.le_antisymm
  · have h := f_le_choose 3 4
    norm_num [Nat.choose] at h
    exact h
  · have h := sharp_lower_bound 4 (by norm_num)
    norm_num at h
    exact h

end
end Sharp3

export Sharp3 (exists_sharp_configuration sharp_lower_bound f_space_three f_space_four)

/-- The exact spatial value follows as soon as the minimum-degree core
certificate has been constructed.  This wrapper keeps the extremal-function
arithmetic separate from the spherical topology. -/
theorem f_space_of_minDegree_certificates
    (hcert : ∀ (B : Finset (Point 3)), IsDiameterOne B →
      (∀ v, 2 ≤ (diameterGraph B).degree v) →
      SimpleGraph.ConstructibleSphereRotationCertificate
        (diameterGraph B).bipartiteDoubleCover)
    (n : ℕ) (hn : 4 ≤ n) :
    f 3 n = 2 * n - 2 := by
  apply Nat.le_antisymm
  · apply f_le_of_forall (by norm_num) (by omega)
    intro A hcard hdiam
    have hupper := diameterPairCount_add_two_le_of_minDegree_certificates
      hcert A hdiam
    omega
  · exact sharp_lower_bound n hn

/-- Numerical minimum-degree upper bounds can be fed directly into the same
extremal-function argument, without first packaging a rotation certificate. -/
theorem f_space_of_minDegree_upper
    (hcoreUpper : ∀ (B : Finset (Point 3)), IsDiameterOne B →
      (∀ v, 2 ≤ (diameterGraph B).degree v) →
      diameterPairCount B + 2 ≤ 2 * B.card)
    (n : ℕ) (hn : 4 ≤ n) :
    f 3 n = 2 * n - 2 := by
  apply Nat.le_antisymm
  · apply f_le_of_forall (by norm_num) (by omega)
    intro A hcard hdiam
    have hupper := diameterPairCount_add_two_le_of_minDegree_upper
      hcoreUpper A hdiam
    omega
  · exact sharp_lower_bound n hn

/-! ## Vázsonyi's exact three-dimensional theorem -/

/-- Every finite diameter-one configuration in three-dimensional Euclidean
space has at most twice its number of points minus two diameter pairs. -/
theorem diameterPairCount_add_two_le
    (A : Finset (Point 3)) (hA : IsDiameterOne A) :
    diameterPairCount A + 2 ≤ 2 * A.card :=
  diameterPairCount_add_two_le_of_minDegree_upper
    SphericalEuler.diameterPairCount_add_two_le_of_minDegree_planar A hA

/-- Vázsonyi's exact solution in three dimensions: for every `n ≥ 4`, the
maximum number of diameter pairs among `n` points is `2n - 2`. -/
theorem f_space (n : ℕ) (hn : 4 ≤ n) :
    f 3 n = 2 * n - 2 :=
  f_space_of_minDegree_upper
    SphericalEuler.diameterPairCount_add_two_le_of_minDegree_planar n hn

end Erdos223
