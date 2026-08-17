import ErdosProblems.Erdos581.Peeling
import ErdosProblems.Erdos127.BalancedCut
import Mathlib.Algebra.Order.Floor.Div

/-!
# Erdős 581: the dense minimum-degree core

The sampler in this file is completely finite.  From a triangle-free graph
of minimum degree at least `D`, sample `ceil (4M/D)` vertices with
replacement.  Vertices having a sampled neighbour span, for some outcome,
at least three fifths of all edges.  Their first sampled neighbour is a
proper color.  Balanced aggregation of those colors and the induced-cut
extension theorem then produce a cut with a surplus proportional to `D^2`.
-/

open Finset Set
open scoped BigOperators

namespace Erdos581

universe u v

/-! ## Counting functions with pointwise restrictions -/

private def AllowedFunctions {alpha : Type u} {beta : alpha → Type v}
    (allowed : ∀ x, Finset (beta x)) :=
  {f : ∀ x, beta x // ∀ x, f x ∈ allowed x}

private def allowedFunctionsEquiv {alpha : Type u} {beta : alpha → Type v}
    (allowed : ∀ x, Finset (beta x)) :
    AllowedFunctions allowed ≃ ∀ x, ↑(allowed x) where
  toFun f x := ⟨f.1 x, f.2 x⟩
  invFun f := ⟨fun x ↦ (f x).1, fun x ↦ (f x).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma card_filter_pointwise_mem {alpha : Type u} {beta : alpha → Type v}
    [Fintype alpha] [∀ x, Fintype (beta x)] [Fintype (∀ x, beta x)]
    [∀ x, DecidableEq (beta x)]
    (allowed : ∀ x, Finset (beta x)) :
    ((Finset.univ : Finset (∀ x, beta x)).filter
      (fun f ↦ ∀ x, f x ∈ allowed x)).card = ∏ x, (allowed x).card := by
  classical
  let e : {f : ∀ x, beta x // ∀ x, f x ∈ allowed x} ≃
      ∀ x, ↑(allowed x) :=
    { toFun := fun f x ↦ ⟨f.1 x, f.2 x⟩
      invFun := fun f ↦ ⟨fun x ↦ (f x).1, fun x ↦ (f x).2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  calc
    ((Finset.univ : Finset (∀ x, beta x)).filter
        (fun f ↦ ∀ x, f x ∈ allowed x)).card =
        Fintype.card {f : ∀ x, beta x // ∀ x, f x ∈ allowed x} := by
          rw [Fintype.card_subtype]
    _ = Fintype.card (∀ x, ↑(allowed x)) := Fintype.card_congr e
    _ = ∏ x, (allowed x).card := by simp

/-! ## The avoidance inequality -/

private lemma five_mul_sub_pow_le_pow {M d r : ℕ}
    (hr : 0 < r) (hdM : d ≤ M) (hrd : 4 * M ≤ r * d) :
    5 * (M - d) ^ r ≤ M ^ r := by
  let a := M - d
  have had : a + d = M := Nat.sub_add_cancel hdM
  have haM : a ≤ M := Nat.sub_le _ _
  have hfour : 4 * a ≤ r * d := (Nat.mul_le_mul_left 4 haM).trans hrd
  have hrform : r - 1 + 1 = r := by omega
  have hpow : a ^ r = a ^ (r - 1) * a := by
    conv_lhs => rw [← hrform, pow_succ]
  have hmul : 4 * a ^ r ≤ r * a ^ (r - 1) * d := by
    rw [hpow]
    have h := Nat.mul_le_mul_right (a ^ (r - 1)) hfour
    nlinarith
  have hbern : a ^ r + r * a ^ (r - 1) * d ≤ (a + d) ^ r := by
    exact pow_add_mul_le_add_pow (R := ℕ) (by omega) (by omega) r
  rw [had] at hbern
  nlinarith

section Sampling

variable {W : Type u} [Fintype W] [DecidableEq W]
  (K : SimpleGraph W) [DecidableRel K.Adj]

/-- Number of samples in the dense-core argument. -/
def sampleCount (D : ℕ) : ℕ :=
  4 * Fintype.card W ⌈/⌉ D

/-- A vertex is covered when one of the sampled vertices is adjacent to it. -/
def IsCovered {r : ℕ} (omega : Fin r → W) (v : W) : Prop :=
  ∃ i, K.Adj (omega i) v

private noncomputable instance {r : ℕ} (omega : Fin r → W) (v : W) :
    Decidable (IsCovered K omega v) := Classical.propDecidable _

/-- The finset of covered vertices. -/
noncomputable def coveredVertices {r : ℕ} (omega : Fin r → W) : Finset W :=
  Finset.univ.filter (IsCovered K omega)

/-- Edges having both endpoints covered. -/
noncomputable def coveredEdges {r : ℕ} (omega : Fin r → W) :
    Finset (Sym2 W) :=
  K.edgeFinset.filter fun e ↦ e.toFinset ⊆ coveredVertices K omega

private lemma card_not_neighbor (v : W) :
    ((Finset.univ : Finset W).filter fun z ↦ ¬K.Adj z v).card =
      Fintype.card W - K.degree v := by
  have heq : ((Finset.univ : Finset W).filter fun z ↦ ¬K.Adj z v) =
      Finset.univ \ K.neighborFinset v := by
    ext z
    simp [SimpleGraph.mem_neighborFinset, K.adj_comm]
  rw [heq, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, SimpleGraph.card_neighborFinset_eq_degree]

private lemma card_avoiding_samples (v : W) (r : ℕ) :
    ((Finset.univ : Finset (Fin r → W)).filter
      (fun omega ↦ ∀ i, ¬K.Adj (omega i) v)).card =
      (Fintype.card W - K.degree v) ^ r := by
  classical
  let allowed : Fin r → Finset W := fun _ ↦
    (Finset.univ : Finset W).filter fun z ↦ ¬K.Adj z v
  calc
    ((Finset.univ : Finset (Fin r → W)).filter
        (fun omega ↦ ∀ i, ¬K.Adj (omega i) v)).card =
        ((Finset.univ : Finset (Fin r → W)).filter
          (fun omega ↦ ∀ i, omega i ∈ allowed i)).card := by
            congr 1
            ext omega
            simp [allowed]
    _ = ∏ i, (allowed i).card := by
      simpa only [allowed] using card_filter_pointwise_mem allowed
    _ = (Fintype.card W - K.degree v) ^ r := by
      simp [allowed, card_not_neighbor K v]

private lemma card_uncovered_samples_le
    {D : ℕ} (hD : 0 < D) (hW : Nonempty W)
    (hmin : ∀ v, D ≤ K.degree v) (v : W) :
    5 * ((Finset.univ : Finset (Fin (sampleCount (W := W) D) → W)).filter
      (fun omega ↦ ¬IsCovered K omega v)).card ≤
      Fintype.card (Fin (sampleCount (W := W) D) → W) := by
  classical
  let M := Fintype.card W
  let r := sampleCount (W := W) D
  have hM : 0 < M := Fintype.card_pos_iff.mpr hW
  have hdegM : K.degree v ≤ M := by
    exact (K.degree_lt_card_verts v).le
  have hrD : 4 * M ≤ r * D := by
    have h : 4 * M ≤ D • (4 * M ⌈/⌉ D) := le_smul_ceilDiv hD
    simpa [r, sampleCount, M, nsmul_eq_mul, mul_comm] using h
  have hr : 0 < r := by
    by_contra hz
    have hr0 : r = 0 := Nat.eq_zero_of_not_pos hz
    rw [hr0, zero_mul] at hrD
    omega
  have hpow := five_mul_sub_pow_le_pow hr hdegM
    ((Nat.mul_le_mul_left r (hmin v)).trans' hrD)
  have hfilter :
      ((Finset.univ : Finset (Fin r → W)).filter
        (fun omega ↦ ¬IsCovered K omega v)).card =
        (M - K.degree v) ^ r := by
    calc
      ((Finset.univ : Finset (Fin r → W)).filter
          (fun omega ↦ ¬IsCovered K omega v)).card =
          ((Finset.univ : Finset (Fin r → W)).filter
            (fun omega ↦ ∀ i, ¬K.Adj (omega i) v)).card := by
              congr 1
              ext omega
              simp [IsCovered]
      _ = (M - K.degree v) ^ r := by
        rw [card_avoiding_samples K v r]
  rw [show sampleCount (W := W) D = r by rfl, hfilter]
  simpa [Fintype.card_fun, Fintype.card_fin, M] using hpow

private lemma three_mul_card_samples_le_five_mul_edge_covered
    {D : ℕ} (hD : 0 < D) (hW : Nonempty W)
    (hmin : ∀ v, D ≤ K.degree v) (e : Sym2 W) :
    3 * Fintype.card (Fin (sampleCount (W := W) D) → W) ≤
      5 * ((Finset.univ : Finset (Fin (sampleCount (W := W) D) → W)).filter
        (fun omega ↦ e.toFinset ⊆ coveredVertices K omega)).card := by
  classical
  induction e using Sym2.inductionOn with
  | _ u v =>
      let Ω : Finset (Fin (sampleCount (W := W) D) → W) := Finset.univ
      let Bu := Ω.filter fun omega ↦ ¬IsCovered K omega u
      let Bv := Ω.filter fun omega ↦ ¬IsCovered K omega v
      let Good := Ω.filter fun omega ↦
        IsCovered K omega u ∧ IsCovered K omega v
      have hBu : 5 * Bu.card ≤ Fintype.card
          (Fin (sampleCount (W := W) D) → W) := by
        simpa [Bu, Ω] using card_uncovered_samples_le K hD hW hmin u
      have hBv : 5 * Bv.card ≤ Fintype.card
          (Fin (sampleCount (W := W) D) → W) := by
        simpa [Bv, Ω] using card_uncovered_samples_le K hD hW hmin v
      have hbad : 5 * (Bu ∪ Bv).card ≤
          2 * Fintype.card (Fin (sampleCount (W := W) D) → W) := by
        have hunion := Finset.card_union_le Bu Bv
        omega
      have hpart : Good.card + (Bu ∪ Bv).card =
          Fintype.card (Fin (sampleCount (W := W) D) → W) := by
        have h := Finset.card_filter_add_card_filter_not
          (s := Ω) (fun omega ↦ IsCovered K omega u ∧ IsCovered K omega v)
        simpa only [Good, Bu, Bv, Ω, not_and_or, Finset.filter_or,
          Finset.card_univ] using h
      have hgood : 3 * Fintype.card
          (Fin (sampleCount (W := W) D) → W) ≤ 5 * Good.card := by
        omega
      simpa [Good, Ω, Sym2.toFinset_mk_eq, coveredVertices,
        Finset.insert_subset_iff] using hgood

/-- Some sampling outcome covers at least three fifths of all edges. -/
theorem exists_many_covered_edges
    {D : ℕ} (hD : 0 < D) (hW : Nonempty W)
    (hmin : ∀ v, D ≤ K.degree v) :
    ∃ omega : Fin (sampleCount (W := W) D) → W,
      3 * K.edgeFinset.card ≤ 5 * (coveredEdges K omega).card := by
  classical
  let Ω : Finset (Fin (sampleCount (W := W) D) → W) := Finset.univ
  let T := Fintype.card (Fin (sampleCount (W := W) D) → W)
  have hdouble :
      (∑ e ∈ K.edgeFinset,
        ((Ω.filter fun omega ↦
          e.toFinset ⊆ coveredVertices K omega).card)) =
        ∑ omega ∈ Ω, (coveredEdges K omega).card := by
    calc
      (∑ e ∈ K.edgeFinset,
          ((Ω.filter fun omega ↦
            e.toFinset ⊆ coveredVertices K omega).card)) =
          ∑ e ∈ K.edgeFinset, ∑ omega ∈ Ω,
            if e.toFinset ⊆ coveredVertices K omega then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro e _he
              exact Finset.sum_boole _ _ |>.symm
      _ = ∑ omega ∈ Ω, ∑ e ∈ K.edgeFinset,
          if e.toFinset ⊆ coveredVertices K omega then 1 else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ omega ∈ Ω, (coveredEdges K omega).card := by
            apply Finset.sum_congr rfl
            intro omega _homega
            simp only [coveredEdges]
            exact Finset.sum_boole _ _
  have hedgeSum :
      (∑ e ∈ K.edgeFinset, 3 * T) ≤
        ∑ e ∈ K.edgeFinset,
          5 * ((Ω.filter fun omega ↦
            e.toFinset ⊆ coveredVertices K omega).card) := by
    apply Finset.sum_le_sum
    intro e he
    simpa [Ω, T] using
      three_mul_card_samples_le_five_mul_edge_covered K hD hW hmin e
  have hsum :
      (∑ omega ∈ Ω, 3 * K.edgeFinset.card) ≤
        ∑ omega ∈ Ω, 5 * (coveredEdges K omega).card := by
    calc
      (∑ omega ∈ Ω, 3 * K.edgeFinset.card) =
          T * (3 * K.edgeFinset.card) := by simp [Ω, T]
      _ = K.edgeFinset.card * (3 * T) := by ring
      _ = ∑ e ∈ K.edgeFinset, 3 * T := by simp
      _ ≤ ∑ e ∈ K.edgeFinset,
          5 * ((Ω.filter fun omega ↦
            e.toFinset ⊆ coveredVertices K omega).card) := hedgeSum
      _ = 5 * (∑ e ∈ K.edgeFinset,
          ((Ω.filter fun omega ↦
            e.toFinset ⊆ coveredVertices K omega).card)) := by
              simp [Finset.mul_sum]
      _ = 5 * (∑ omega ∈ Ω, (coveredEdges K omega).card) := by rw [hdouble]
      _ = ∑ omega ∈ Ω, 5 * (coveredEdges K omega).card := by
            simp [Finset.mul_sum]
  have hΩ : Ω.Nonempty := by simp [Ω]
  obtain ⟨omega, _homega, homega⟩ :=
    Finset.exists_le_of_sum_le hΩ hsum
  exact ⟨omega, homega⟩

lemma sampleCount_mul_le (D : ℕ) (hD : 0 < D)
    (hDM : D ≤ Fintype.card W) :
    sampleCount (W := W) D * D ≤ 5 * Fintype.card W := by
  rw [sampleCount, Nat.ceilDiv_eq_add_pred_div]
  have hdiv := Nat.div_mul_le_self
    (4 * Fintype.card W + D - 1) D
  omega

lemma minDegree_mul_card_le_twice_edges (D : ℕ)
    (hmin : ∀ v, D ≤ K.degree v) :
    D * Fintype.card W ≤ 2 * K.edgeFinset.card := by
  calc
    D * Fintype.card W = ∑ _v : W, D := by simp [mul_comm]
    _ ≤ ∑ v : W, K.degree v := by
      exact Finset.sum_le_sum fun v _hv ↦ hmin v
    _ = 2 * K.edgeFinset.card := K.sum_degrees_eq_twice_card_edges

private noncomputable def coveredIndex {r : ℕ} (omega : Fin r → W)
    (v : ↑(coveredVertices K omega)) : Fin r :=
  Classical.choose (by
    have hv : IsCovered K omega v.1 := by
      simpa [coveredVertices] using v.2
    exact hv)

private lemma coveredIndex_adj {r : ℕ} (omega : Fin r → W)
    (v : ↑(coveredVertices K omega)) :
    K.Adj (omega (coveredIndex K omega v)) v.1 := by
  exact Classical.choose_spec (by
    have hv : IsCovered K omega v.1 := by
      simpa [coveredVertices] using v.2
    exact hv)

/-- Covered vertices are properly colored by a chosen sampled neighbor. -/
noncomputable def coveredColoring {r : ℕ} (omega : Fin r → W)
    (htri : K.CliqueFree 3) :
    (K.induce (↑(coveredVertices K omega) : Set W)).Coloring (Fin r) :=
  SimpleGraph.Coloring.mk (coveredIndex K omega) (by
    intro u v huv heq
    have hu := coveredIndex_adj K omega u
    have hv := coveredIndex_adj K omega v
    rw [heq] at hu
    have hind := K.isIndepSet_neighborSet_of_triangleFree htri
      (omega (coveredIndex K omega v))
    exact hind hu hv (by
      intro huvEq
      have huvEq' : u = v := Subtype.ext huvEq
      subst v
      exact K.loopless.irrefl u.1 (by simpa using huv)) (by simpa using huv))

lemma card_coveredEdges {r : ℕ} (omega : Fin r → W) :
    (coveredEdges K omega).card =
      (K.induce (↑(coveredVertices K omega) : Set W)).edgeFinset.card := by
  exact K.card_filter_edgeFinset_toFinset_subset (coveredVertices K omega)

private theorem exists_balanced_cut_compressed
    {X : Type*} [Fintype X] [DecidableEq X]
    (H : SimpleGraph X) [DecidableRel H.Adj]
    {r : ℕ} (c : H.Coloring (Fin r)) (hedge : H.edgeFinset.Nonempty) :
    ∃ q : ℕ, ∃ A : Finset X,
      2 ≤ q ∧ q ≤ r ∧
        (q + 1) * H.edgeFinset.card ≤
          2 * q * (H.cutEdgeFinset A).card := by
  classical
  let C : Finset (Fin r) := Finset.univ.image c
  let q := Fintype.card C
  let eC : C ≃ Fin q := Fintype.equivFin C
  let c' : H.Coloring (Fin q) := SimpleGraph.Coloring.mk
    (fun v ↦ eC ⟨c v, by simp [C]⟩) (by
      intro u v huv heq
      have hsub : (⟨c u, by simp [C]⟩ : C) = ⟨c v, by simp [C]⟩ :=
        eC.injective heq
      exact c.valid huv (congr_arg Subtype.val hsub))
  have hc' : Function.Surjective c' := by
    intro j
    let z : C := eC.symm j
    obtain ⟨v, _hv, hvz⟩ := Finset.mem_image.mp z.property
    refine ⟨v, ?_⟩
    change eC ⟨c v, _⟩ = j
    have hz : (⟨c v, by simp [C]⟩ : C) = z := Subtype.ext hvz
    rw [hz]
    exact eC.apply_symm_apply j
  have hqle : q ≤ r := by
    calc
      q = C.card := by simp [q]
      _ ≤ (Finset.univ : Finset (Fin r)).card := by
        exact Finset.card_le_card (Finset.subset_univ C)
      _ = r := by simp
  have hq : 2 ≤ q := by
    obtain ⟨e, he⟩ := hedge
    induction e using Sym2.inductionOn with
    | _ u v =>
        have huv : H.Adj u v := by
          simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
        have hne := c.valid huv
        have hsub : ({c u, c v} : Finset (Fin r)) ⊆ C := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> simp [C]
        calc
          2 = ({c u, c v} : Finset (Fin r)).card := by simp [hne]
          _ ≤ C.card := Finset.card_le_card hsub
          _ = q := by simp [q]
  obtain ⟨A, hA⟩ := SimpleGraph.exists_cutEdgeFinset_mul_bound hq c' hc'
  exact ⟨q, A, hq, hqle, hA⟩

/-- A triangle-free graph of minimum degree at least `D` has a cut whose
surplus over half the edges is at least `D^2 / 200`. -/
theorem exists_cut_denseCore {D : ℕ} (hD : 0 < D) (hW : Nonempty W)
    (htri : K.CliqueFree 3) (hmin : ∀ v, D ≤ K.degree v) :
    ∃ s : Set W,
      (K.edgeFinset.card : ℝ) / 2 + (D : ℝ) ^ 2 / 200 ≤
        ((cutGraph K s).edgeSet.ncard : ℝ) := by
  classical
  let M := Fintype.card W
  let r := sampleCount (W := W) D
  obtain ⟨omega, hcovered⟩ := exists_many_covered_edges K hD hW hmin
  let T := coveredVertices K omega
  let H := K.induce (↑T : Set W)
  let c : H.Coloring (Fin r) := coveredColoring K omega htri
  have hM : 0 < M := Fintype.card_pos_iff.mpr hW
  have hDM : D ≤ M := by
    let v : W := Classical.choice hW
    have hdlt : K.degree v < M := K.degree_lt_card_verts v
    exact (hmin v).trans hdlt.le
  have hhand : D * M ≤ 2 * K.edgeFinset.card := by
    simpa [M] using minDegree_mul_card_le_twice_edges K D hmin
  have hedge : 0 < K.edgeFinset.card := by
    have hprod : 0 < D * M := Nat.mul_pos hD hM
    omega
  have hHcard : H.edgeFinset.card = (coveredEdges K omega).card := by
    simpa [H, T] using (card_coveredEdges K omega).symm
  have hHedge : H.edgeFinset.Nonempty := by
    apply Finset.card_pos.mp
    rw [hHcard]
    omega
  obtain ⟨q, A, hq, hqr, hbalanced⟩ :=
    exists_balanced_cut_compressed H c hHedge
  have hrD : r * D ≤ 5 * M := by
    simpa [r, M] using sampleCount_mul_le (W := W) D hD hDM
  have hcovered' : 3 * K.edgeFinset.card ≤ 5 * H.edgeFinset.card := by
    rwa [hHcard]
  have hcutEq : inducedCutEdges K T A = H.cutEdgeFinset A := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
        simp [inducedCutEdges, H, cutGraph_adj,
          SimpleGraph.mem_cutEdgeFinset_mk]
  obtain ⟨s, hs⟩ := exists_cut_extending_induced K T A
  have hcoveredR : 3 * (K.edgeFinset.card : ℝ) ≤
      5 * (H.edgeFinset.card : ℝ) := by exact_mod_cast hcovered'
  have hhandR : (D : ℝ) * (M : ℝ) ≤
      2 * (K.edgeFinset.card : ℝ) := by exact_mod_cast hhand
  have hrDR : (r : ℝ) * (D : ℝ) ≤ 5 * (M : ℝ) := by
    exact_mod_cast hrD
  have hqrR : (q : ℝ) ≤ (r : ℝ) := by exact_mod_cast hqr
  have hbalancedR : ((q + 1) : ℝ) * (H.edgeFinset.card : ℝ) ≤
      2 * (q : ℝ) * (H.cutEdgeFinset A).card := by
    exact_mod_cast hbalanced
  have hqR : 0 < (q : ℝ) := by positivity
  have hQD : (q : ℝ) * (D : ℝ) ≤ 5 * (M : ℝ) := by
    calc
      (q : ℝ) * (D : ℝ) ≤ (r : ℝ) * (D : ℝ) := by
        exact mul_le_mul_of_nonneg_right hqrR (by positivity)
      _ ≤ 5 * (M : ℝ) := hrDR
  have hDME : 3 * (D : ℝ) * (M : ℝ) ≤
      10 * (H.edgeFinset.card : ℝ) := by
    nlinarith
  have hQDDM : 3 * (q : ℝ) * (D : ℝ) ^ 2 ≤
      15 * (D : ℝ) * (M : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hQD
      (show 0 ≤ 3 * (D : ℝ) by positivity)
    nlinarith
  have hQDDE : 3 * (q : ℝ) * (D : ℝ) ^ 2 ≤
      50 * (H.edgeFinset.card : ℝ) := by
    nlinarith
  have hbalanceRearranged : (H.edgeFinset.card : ℝ) ≤
      (q : ℝ) * (2 * (H.cutEdgeFinset A).card - H.edgeFinset.card) := by
    nlinarith
  have hQsurplus : 0 ≤
      (q : ℝ) * (2 * (H.cutEdgeFinset A).card - H.edgeFinset.card) :=
    (Nat.cast_nonneg _).trans hbalanceRearranged
  have hcancel : (q : ℝ) * (D : ℝ) ^ 2 ≤
      (q : ℝ) * (100 *
        (2 * (H.cutEdgeFinset A).card - H.edgeFinset.card)) := by
    nlinarith
  have hsurplus : (D : ℝ) ^ 2 / 200 ≤
      (H.cutEdgeFinset A).card - (H.edgeFinset.card : ℝ) / 2 := by
    have hcancel' : (D : ℝ) ^ 2 ≤
        100 * (2 * (H.cutEdgeFinset A).card - H.edgeFinset.card) := by
      nlinarith [hcancel]
    nlinarith
  refine ⟨s, ?_⟩
  rw [hcutEq] at hs
  nlinarith

end Sampling

end Erdos581
