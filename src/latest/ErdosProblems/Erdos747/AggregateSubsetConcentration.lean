import ErdosProblems.Erdos747.AllDensityUnions

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Aggregate degree concentration through vertex-set incidences -/

/-- Number of vertices of `W` hit by an edge. -/
def edgeVertexSetHits {n : ℕ} (W : Finset (Vertex n))
    (A : Edge n) : ℕ :=
  (A ∩ W).card

/-- Potential triples hitting `W` in exactly `j` vertices. -/
def edgeVertexSetClass (n : ℕ) (W : Finset (Vertex n))
    (j : ℕ) : Finset (Edge n) :=
  (allEdges n).filter fun A ↦ edgeVertexSetHits W A = j

/-- Number of present edges in the `j`th intersection class. -/
def sampledEdgeVertexSetClassCount {n : ℕ}
    (H : Finset (Edge n)) (W : Finset (Vertex n)) (j : ℕ) : ℕ :=
  (H.filter fun A ↦ edgeVertexSetHits W A = j).card

/-- Total degree carried by a set of vertices. -/
def vertexSetDegreeSum {n : ℕ} (H : Finset (Edge n))
    (W : Finset (Vertex n)) : ℝ :=
  ∑ v ∈ W, (vertexDegree H v : ℝ)

lemma vertexSetDegreeSum_eq_edge_hits {n : ℕ}
    (H : Finset (Edge n)) (W : Finset (Vertex n)) :
    vertexSetDegreeSum H W =
      ∑ A ∈ H, (edgeVertexSetHits W A : ℝ) := by
  unfold vertexSetDegreeSum vertexDegree edgeVertexSetHits
  calc
    (∑ v ∈ W, ((H.filter fun A ↦ v ∈ A).card : ℝ)) =
        ∑ v ∈ W, ∑ A ∈ H, if v ∈ A then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.sum_boole]
    _ = ∑ A ∈ H, ∑ v ∈ W, if v ∈ A then (1 : ℝ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ A ∈ H, ((A ∩ W).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro A hA
      rw [Finset.sum_boole]
      norm_cast
      congr 1
      ext v
      simp [and_comm]

lemma edgeVertexSetHits_le_three {n : ℕ}
    {W : Finset (Vertex n)} {A : Edge n} (hA : A ∈ allEdges n) :
    edgeVertexSetHits W A ≤ 3 := by
  unfold edgeVertexSetHits
  exact (Finset.card_le_card Finset.inter_subset_left).trans_eq
    (mem_allEdges.mp hA)

lemma vertexSetDegreeSum_eq_class_sum {n : ℕ}
    {H : Finset (Edge n)} (W : Finset (Vertex n))
    (hH : H ⊆ allEdges n) :
    vertexSetDegreeSum H W =
      ∑ j ∈ Finset.range 4,
        (j : ℝ) * sampledEdgeVertexSetClassCount H W j := by
  rw [vertexSetDegreeSum_eq_edge_hits]
  unfold sampledEdgeVertexSetClassCount
  calc
    (∑ A ∈ H, (edgeVertexSetHits W A : ℝ)) =
        ∑ A ∈ H, ∑ j ∈ Finset.range 4,
          if edgeVertexSetHits W A = j then (j : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro A hA
      have hhits : edgeVertexSetHits W A < 4 := by
        exact lt_of_le_of_lt (edgeVertexSetHits_le_three (hH hA))
          (by omega)
      rw [Finset.sum_eq_single (edgeVertexSetHits W A)]
      · simp
      · intro b hb hne
        simp [hne.symm]
      · exact fun hnot ↦ False.elim
          (hnot (Finset.mem_range.mpr hhits))
    _ = ∑ j ∈ Finset.range 4, ∑ A ∈ H,
          if edgeVertexSetHits W A = j then (j : ℝ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.range 4,
          (j : ℝ) * ((H.filter fun A ↦
            edgeVertexSetHits W A = j).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [show (∑ A ∈ H,
          if edgeVertexSetHits W A = j then (j : ℝ) else 0) =
          ∑ _A ∈ H.filter (fun A ↦ edgeVertexSetHits W A = j),
            (j : ℝ) by
        rw [← Finset.sum_filter]]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Exact mean of the total degree on `W` in a uniform `M`-edge layer. -/
lemma complete_vertexSetDegreeSum_density
    (n : ℕ) (W : Finset (Vertex n)) (hn : 0 < n) :
    vertexSetDegreeSum (allEdges n) W /
        ((allEdges n).card : ℝ) =
      (W.card : ℝ) / n := by
  unfold vertexSetDegreeSum
  have hpoint : ∀ v ∈ W,
      (vertexDegree (allEdges n) v : ℝ) /
          ((allEdges n).card : ℝ) = 1 / (n : ℝ) := by
    intro v hv
    have hdegree : vertexDegree (allEdges n) v =
        (incidentEdges n v).card := by
      rw [vertexDegree_eq_card_inter_incidentEdges v
        (Finset.Subset.rfl)]
      congr 1
      exact Finset.inter_eq_right.mpr (incidentEdges_subset n v)
    rw [hdegree]
    exact incidentEdges_density n v hn
  have hKpos : (0 : ℝ) < (allEdges n).card := by
    exact_mod_cast Finset.card_pos.mpr (allEdges_nonempty n hn)
  rw [Finset.sum_div]
  calc
    (∑ v ∈ W, (vertexDegree (allEdges n) v : ℝ) /
        ((allEdges n).card : ℝ)) =
      ∑ _v ∈ W, (1 / (n : ℝ)) :=
        Finset.sum_congr rfl hpoint
    _ = (W.card : ℝ) / n := by
      simp [div_eq_mul_inv]

/-- Weighted class means add up to the exact expected incidence sum. -/
lemma weighted_edgeVertexSetClass_means
    (n M : ℕ) (W : Finset (Vertex n)) (hn : 0 < n) :
    ∑ j ∈ Finset.range 4,
        (j : ℝ) * ((M : ℝ) *
          ((edgeVertexSetClass n W j).card : ℝ) /
            (allEdges n).card) =
      (W.card : ℝ) * ((M : ℝ) / n) := by
  have hclass := vertexSetDegreeSum_eq_class_sum W
    (H := allEdges n) (Finset.Subset.rfl)
  have hcount : ∀ j,
      sampledEdgeVertexSetClassCount (allEdges n) W j =
        (edgeVertexSetClass n W j).card := by
    intro j
    unfold sampledEdgeVertexSetClassCount edgeVertexSetClass
    rfl
  simp_rw [hcount] at hclass
  have hdensity := complete_vertexSetDegreeSum_density n W hn
  have hKne : ((allEdges n).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr (allEdges_nonempty n hn)).ne'
  calc
    (∑ j ∈ Finset.range 4,
        (j : ℝ) * ((M : ℝ) *
          ((edgeVertexSetClass n W j).card : ℝ) /
            (allEdges n).card)) =
      (M : ℝ) *
        ((∑ j ∈ Finset.range 4,
          (j : ℝ) * ((edgeVertexSetClass n W j).card : ℝ)) /
            (allEdges n).card) := by
      calc
        _ = ∑ j ∈ Finset.range 4,
            ((M : ℝ) / (allEdges n).card) *
              ((j : ℝ) * ((edgeVertexSetClass n W j).card : ℝ)) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = ((M : ℝ) / (allEdges n).card) *
            (∑ j ∈ Finset.range 4,
              (j : ℝ) * ((edgeVertexSetClass n W j).card : ℝ)) := by
          rw [Finset.mul_sum]
        _ = _ := by ring
    _ = (M : ℝ) *
        (vertexSetDegreeSum (allEdges n) W /
          (allEdges n).card) := by rw [hclass]
    _ = (M : ℝ) * ((W.card : ℝ) / n) := by rw [hdensity]
    _ = (W.card : ℝ) * ((M : ℝ) / n) := by ring

lemma edgeVertexSetClass_subset (n : ℕ)
    (W : Finset (Vertex n)) (j : ℕ) :
    edgeVertexSetClass n W j ⊆ allEdges n :=
  Finset.filter_subset _ _

lemma sampledEdgeVertexSetClassCount_eq_inter {n : ℕ}
    {H : Finset (Edge n)} (W : Finset (Vertex n)) (j : ℕ)
    (hH : H ⊆ allEdges n) :
    sampledEdgeVertexSetClassCount H W j =
      (H ∩ edgeVertexSetClass n W j).card := by
  unfold sampledEdgeVertexSetClassCount edgeVertexSetClass
  apply congrArg Finset.card
  ext A
  simp only [Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨hAH, hAj⟩
    exact ⟨hAH, hH hAH, hAj⟩
  · rintro ⟨hAH, -, hAj⟩
    exact ⟨hAH, hAj⟩

/-- Mean of one intersection class in a uniform fixed-size sample. -/
def edgeVertexSetClassMean (n M : ℕ)
    (W : Finset (Vertex n)) (j : ℕ) : ℝ :=
  (M : ℝ) * ((edgeVertexSetClass n W j).card : ℝ) /
    (allEdges n).card

lemma edgeVertexSetClassMean_nonneg
    (n M : ℕ) (W : Finset (Vertex n)) (j : ℕ) :
    0 ≤ edgeVertexSetClassMean n M W j := by
  unfold edgeVertexSetClassMean
  positivity

lemma edgeVertexSetClassMean_le
    (n M : ℕ) (W : Finset (Vertex n)) (j : ℕ)
    (hn : 0 < n) :
    edgeVertexSetClassMean n M W j ≤ M := by
  have hKpos : (0 : ℝ) < (allEdges n).card := by
    exact_mod_cast Finset.card_pos.mpr (allEdges_nonempty n hn)
  have hcard : ((edgeVertexSetClass n W j).card : ℝ) ≤
      (allEdges n).card := by
    exact_mod_cast Finset.card_le_card
      (edgeVertexSetClass_subset n W j)
  unfold edgeVertexSetClassMean
  have hratio : ((edgeVertexSetClass n W j).card : ℝ) /
      (allEdges n).card ≤ 1 := (div_le_one hKpos).2 hcard
  have hM0 : (0 : ℝ) ≤ M := by positivity
  calc
    (M : ℝ) * (edgeVertexSetClass n W j).card /
        (allEdges n).card =
      (M : ℝ) * (((edgeVertexSetClass n W j).card : ℝ) /
        (allEdges n).card) := by ring
    _ ≤ (M : ℝ) * 1 := mul_le_mul_of_nonneg_left hratio hM0
    _ = M := by ring

lemma sampledEdgeVertexSetClass_upper_tail_exp_le
    (n M : ℕ) (W : Finset (Vertex n)) (j : ℕ)
    (theta delta : ℝ) (hn : 0 < n)
    (hM : M ≤ (allEdges n).card) (htheta : 0 ≤ theta) :
    finsetProbability (sample n M)
        (fun H ↦ edgeVertexSetClassMean n M W j + delta ≤
          sampledEdgeVertexSetClassCount H W j) ≤
      ((allEdges n).card + 1 : ℝ) *
        Real.exp (edgeVertexSetClassMean n M W j *
          (Real.exp theta - 1 - theta) - theta * delta) := by
  have hraw := powersetCardOrdinaryHit_upper_tail_exp_le
    (allEdges n) (edgeVertexSetClass n W j) M theta
    (edgeVertexSetClassMean n M W j + delta)
    (edgeVertexSetClass_subset n W j) (allEdges_nonempty n hn) hM htheta
  have hdec :
      (fun A B : Edge n ↦ Classical.propDecidable (A = B)) =
        (Finset.decidableEq : DecidableEq (Edge n)) :=
    Subsingleton.elim _ _
  rw [hdec] at hraw
  calc
    finsetProbability (sample n M)
        (fun H ↦ edgeVertexSetClassMean n M W j + delta ≤
          sampledEdgeVertexSetClassCount H W j) =
      finsetProbability (sample n M)
        (fun H ↦ edgeVertexSetClassMean n M W j + delta ≤
          ((H ∩ edgeVertexSetClass n W j).card : ℝ)) := by
      apply finsetProbability_congr_event
      intro H hHs
      rw [sampledEdgeVertexSetClassCount_eq_inter W j
        (Finset.mem_powersetCard.mp hHs).1]
    _ ≤ ((allEdges n).card + 1 : ℝ) *
        Real.exp (((edgeVertexSetClass n W j).card : ℝ) *
          ((M : ℝ) / (allEdges n).card) *
            (Real.exp theta - 1) -
          theta * (edgeVertexSetClassMean n M W j + delta)) := by
      simpa only [sample] using hraw
    _ = ((allEdges n).card + 1 : ℝ) *
        Real.exp (edgeVertexSetClassMean n M W j *
          (Real.exp theta - 1 - theta) - theta * delta) := by
      unfold edgeVertexSetClassMean
      congr 2
      ring

lemma sampledEdgeVertexSetClass_lower_tail_exp_le
    (n M : ℕ) (W : Finset (Vertex n)) (j : ℕ)
    (theta delta : ℝ) (hn : 0 < n)
    (hM : M ≤ (allEdges n).card) (htheta : 0 ≤ theta) :
    finsetProbability (sample n M)
        (fun H ↦ (sampledEdgeVertexSetClassCount H W j : ℝ) ≤
          edgeVertexSetClassMean n M W j - delta) ≤
      ((allEdges n).card + 1 : ℝ) *
        Real.exp (edgeVertexSetClassMean n M W j *
          (Real.exp (-theta) - 1 + theta) - theta * delta) := by
  have hraw := powersetCardOrdinaryHit_lower_tail_exp_le
    (allEdges n) (edgeVertexSetClass n W j) M theta
    (edgeVertexSetClassMean n M W j - delta)
    (edgeVertexSetClass_subset n W j) (allEdges_nonempty n hn) hM htheta
  have hdec :
      (fun A B : Edge n ↦ Classical.propDecidable (A = B)) =
        (Finset.decidableEq : DecidableEq (Edge n)) :=
    Subsingleton.elim _ _
  rw [hdec] at hraw
  calc
    finsetProbability (sample n M)
        (fun H ↦ (sampledEdgeVertexSetClassCount H W j : ℝ) ≤
          edgeVertexSetClassMean n M W j - delta) =
      finsetProbability (sample n M)
        (fun H ↦ ((H ∩ edgeVertexSetClass n W j).card : ℝ) ≤
          edgeVertexSetClassMean n M W j - delta) := by
      apply finsetProbability_congr_event
      intro H hHs
      rw [sampledEdgeVertexSetClassCount_eq_inter W j
        (Finset.mem_powersetCard.mp hHs).1]
    _ ≤ ((allEdges n).card + 1 : ℝ) *
        Real.exp (((edgeVertexSetClass n W j).card : ℝ) *
          ((M : ℝ) / (allEdges n).card) *
            (Real.exp (-theta) - 1) +
          theta * (edgeVertexSetClassMean n M W j - delta)) := by
      simpa only [sample] using hraw
    _ = ((allEdges n).card + 1 : ℝ) *
        Real.exp (edgeVertexSetClassMean n M W j *
          (Real.exp (-theta) - 1 + theta) - theta * delta) := by
      unfold edgeVertexSetClassMean
      congr 2
      ring

lemma exp_sub_one_sub_id_le_sq {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x - 1 - x ≤ x^2 := by
  have hrem := Real.norm_exp_sub_one_sub_id_le (by
    simpa [Real.norm_eq_abs] using hx)
  calc
    Real.exp x - 1 - x ≤ |Real.exp x - 1 - x| := le_abs_self _
    _ = ‖Real.exp x - 1 - x‖ := by rw [Real.norm_eq_abs]
    _ ≤ ‖x‖^2 := hrem
    _ = x^2 := by rw [Real.norm_eq_abs, sq_abs]

lemma sampledEdgeVertexSetClass_upper_additive_le
    (n M : ℕ) (W : Finset (Vertex n)) (j : ℕ) (delta : ℝ)
    (hn : 0 < n) (hM0 : 0 < M)
    (hM : M ≤ (allEdges n).card)
    (hdelta0 : 0 ≤ delta) (hdeltaM : delta ≤ 2 * M) :
    finsetProbability (sample n M)
        (fun H ↦ edgeVertexSetClassMean n M W j + delta ≤
          sampledEdgeVertexSetClassCount H W j) ≤
      ((allEdges n).card + 1 : ℝ) *
        Real.exp (-(delta^2 / (4 * M))) := by
  let theta : ℝ := delta / (2 * M)
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM0
  have htheta0 : 0 ≤ theta := by positivity
  have htheta1 : theta ≤ 1 := by
    dsimp only [theta]
    apply (div_le_one (by positivity)).2
    exact_mod_cast hdeltaM
  have hthetaAbs : |theta| ≤ 1 := by
    rw [abs_of_nonneg htheta0]
    exact htheta1
  have hrem0 : 0 ≤ Real.exp theta - 1 - theta := by
    linarith [Real.add_one_le_exp theta]
  have hrem : Real.exp theta - 1 - theta ≤ theta^2 :=
    exp_sub_one_sub_id_le_sq hthetaAbs
  have hmean0 := edgeVertexSetClassMean_nonneg n M W j
  have hmeanM := edgeVertexSetClassMean_le n M W j hn
  have harg : edgeVertexSetClassMean n M W j *
      (Real.exp theta - 1 - theta) - theta * delta ≤
        -(delta^2 / (4 * M)) := by
    have hprod : edgeVertexSetClassMean n M W j *
        (Real.exp theta - 1 - theta) ≤ (M : ℝ) * theta^2 :=
      (mul_le_mul hmeanM hrem hrem0 (by positivity))
    dsimp only [theta] at hprod ⊢
    field_simp [hMR.ne'] at hprod ⊢
    nlinarith
  exact (sampledEdgeVertexSetClass_upper_tail_exp_le
    n M W j theta delta hn hM htheta0).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by positivity))

lemma sampledEdgeVertexSetClass_lower_additive_le
    (n M : ℕ) (W : Finset (Vertex n)) (j : ℕ) (delta : ℝ)
    (hn : 0 < n) (hM0 : 0 < M)
    (hM : M ≤ (allEdges n).card)
    (hdelta0 : 0 ≤ delta) (hdeltaM : delta ≤ 2 * M) :
    finsetProbability (sample n M)
        (fun H ↦ (sampledEdgeVertexSetClassCount H W j : ℝ) ≤
          edgeVertexSetClassMean n M W j - delta) ≤
      ((allEdges n).card + 1 : ℝ) *
        Real.exp (-(delta^2 / (4 * M))) := by
  let theta : ℝ := delta / (2 * M)
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM0
  have htheta0 : 0 ≤ theta := by positivity
  have htheta1 : theta ≤ 1 := by
    dsimp only [theta]
    apply (div_le_one (by positivity)).2
    exact_mod_cast hdeltaM
  have hthetaNegAbs : |-theta| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg htheta0]
    exact htheta1
  have hrem0 : 0 ≤ Real.exp (-theta) - 1 + theta := by
    linarith [Real.add_one_le_exp (-theta)]
  have hrem : Real.exp (-theta) - 1 + theta ≤ theta^2 := by
    have := exp_sub_one_sub_id_le_sq hthetaNegAbs
    nlinarith
  have hmean0 := edgeVertexSetClassMean_nonneg n M W j
  have hmeanM := edgeVertexSetClassMean_le n M W j hn
  have harg : edgeVertexSetClassMean n M W j *
      (Real.exp (-theta) - 1 + theta) - theta * delta ≤
        -(delta^2 / (4 * M)) := by
    have hprod : edgeVertexSetClassMean n M W j *
        (Real.exp (-theta) - 1 + theta) ≤ (M : ℝ) * theta^2 :=
      (mul_le_mul hmeanM hrem hrem0 (by positivity))
    dsimp only [theta] at hprod ⊢
    field_simp [hMR.ne'] at hprod ⊢
    nlinarith
  exact (sampledEdgeVertexSetClass_lower_tail_exp_le
    n M W j theta delta hn hM htheta0).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by positivity))

/-- Upper deviation of the total degree carried by `W`. -/
def VertexSetDegreeUpperDeviation (n M : ℕ) (q : ℝ)
    (W : Finset (Vertex n)) (H : Finset (Edge n)) : Prop :=
  q * (W.card : ℝ) * ((M : ℝ) / n) ≤
    vertexSetDegreeSum H W - (W.card : ℝ) * ((M : ℝ) / n)

/-- Lower deviation of the total degree carried by `W`. -/
def VertexSetDegreeLowerDeviation (n M : ℕ) (q : ℝ)
    (W : Finset (Vertex n)) (H : Finset (Edge n)) : Prop :=
  q * (W.card : ℝ) * ((M : ℝ) / n) ≤
    (W.card : ℝ) * ((M : ℝ) / n) - vertexSetDegreeSum H W

lemma vertexSetDegree_upperDeviation_implies_class
    (n M : ℕ) (q : ℝ) (W : Finset (Vertex n))
    {H : Finset (Edge n)} (hn : 0 < n) (hHs : H ∈ sample n M)
    (hdev : VertexSetDegreeUpperDeviation n M q W H) :
    ∃ j ∈ Finset.range 4,
      q * (W.card : ℝ) * ((M : ℝ) / n) / 6 ≤
        (sampledEdgeVertexSetClassCount H W j : ℝ) -
          edgeVertexSetClassMean n M W j := by
  let D : ℝ := q * (W.card : ℝ) * ((M : ℝ) / n)
  have hclass := vertexSetDegreeSum_eq_class_sum W
    (Finset.mem_powersetCard.mp hHs).1
  have hmeans := weighted_edgeVertexSetClass_means n M W hn
  change (∑ j ∈ Finset.range 4, (j : ℝ) *
      edgeVertexSetClassMean n M W j) =
        (W.card : ℝ) * ((M : ℝ) / n) at hmeans
  have hdecomp : vertexSetDegreeSum H W -
      (W.card : ℝ) * ((M : ℝ) / n) =
      ∑ j ∈ Finset.range 4, (j : ℝ) *
        ((sampledEdgeVertexSetClassCount H W j : ℝ) -
          edgeVertexSetClassMean n M W j) := by
    rw [hclass, ← hmeans]
    unfold edgeVertexSetClassMean
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  by_contra hnone
  push Not at hnone
  have h1 := hnone 1 (by simp)
  have h2 := hnone 2 (by simp)
  have h3 := hnone 3 (by simp)
  change D ≤ vertexSetDegreeSum H W -
    (W.card : ℝ) * ((M : ℝ) / n) at hdev
  change D / 6 >
    (sampledEdgeVertexSetClassCount H W 1 : ℝ) -
      edgeVertexSetClassMean n M W 1 at h1
  change D / 6 >
    (sampledEdgeVertexSetClassCount H W 2 : ℝ) -
      edgeVertexSetClassMean n M W 2 at h2
  change D / 6 >
    (sampledEdgeVertexSetClassCount H W 3 : ℝ) -
      edgeVertexSetClassMean n M W 3 at h3
  rw [hdecomp] at hdev
  norm_num [Finset.sum_range_succ] at hdev
  nlinarith

lemma vertexSetDegree_lowerDeviation_implies_class
    (n M : ℕ) (q : ℝ) (W : Finset (Vertex n))
    {H : Finset (Edge n)} (hn : 0 < n) (hHs : H ∈ sample n M)
    (hdev : VertexSetDegreeLowerDeviation n M q W H) :
    ∃ j ∈ Finset.range 4,
      q * (W.card : ℝ) * ((M : ℝ) / n) / 6 ≤
        edgeVertexSetClassMean n M W j -
          (sampledEdgeVertexSetClassCount H W j : ℝ) := by
  let D : ℝ := q * (W.card : ℝ) * ((M : ℝ) / n)
  have hclass := vertexSetDegreeSum_eq_class_sum W
    (Finset.mem_powersetCard.mp hHs).1
  have hmeans := weighted_edgeVertexSetClass_means n M W hn
  change (∑ j ∈ Finset.range 4, (j : ℝ) *
      edgeVertexSetClassMean n M W j) =
        (W.card : ℝ) * ((M : ℝ) / n) at hmeans
  have hdecomp : (W.card : ℝ) * ((M : ℝ) / n) -
      vertexSetDegreeSum H W =
      ∑ j ∈ Finset.range 4, (j : ℝ) *
        (edgeVertexSetClassMean n M W j -
          (sampledEdgeVertexSetClassCount H W j : ℝ)) := by
    rw [hclass, ← hmeans]
    unfold edgeVertexSetClassMean
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  by_contra hnone
  push Not at hnone
  have h1 := hnone 1 (by simp)
  have h2 := hnone 2 (by simp)
  have h3 := hnone 3 (by simp)
  change D ≤ (W.card : ℝ) * ((M : ℝ) / n) -
    vertexSetDegreeSum H W at hdev
  change D / 6 > edgeVertexSetClassMean n M W 1 -
    (sampledEdgeVertexSetClassCount H W 1 : ℝ) at h1
  change D / 6 > edgeVertexSetClassMean n M W 2 -
    (sampledEdgeVertexSetClassCount H W 2 : ℝ) at h2
  change D / 6 > edgeVertexSetClassMean n M W 3 -
    (sampledEdgeVertexSetClassCount H W 3 : ℝ) at h3
  rw [hdecomp] at hdev
  norm_num [Finset.sum_range_succ] at hdev
  nlinarith

lemma vertexSetDegree_classDelta_nonneg
    (n M : ℕ) (q : ℝ) (W : Finset (Vertex n))
    (hq0 : 0 ≤ q) :
    0 ≤ q * (W.card : ℝ) * ((M : ℝ) / n) / 6 := by
  positivity

lemma vertexSetDegree_classDelta_le_two_mul
    (n M : ℕ) (q : ℝ) (W : Finset (Vertex n))
    (hn : 0 < n) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    q * (W.card : ℝ) * ((M : ℝ) / n) / 6 ≤ 2 * M := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hWnat : W.card ≤ 3 * n := by
    simpa only [Fintype.card_fin] using W.card_le_univ
  have hWR : (W.card : ℝ) ≤ 3 * n := by exact_mod_cast hWnat
  have hM0 : (0 : ℝ) ≤ M := by positivity
  calc
    q * (W.card : ℝ) * ((M : ℝ) / n) / 6 ≤
        1 * (3 * (n : ℝ)) * ((M : ℝ) / n) / 6 := by
      gcongr
    _ = (M : ℝ) / 2 := by field_simp [hnR.ne'] <;> ring
    _ ≤ 2 * M := by linarith

/-- A fixed vertex set has exponentially small upper incidence deviation,
uniformly over all sampling densities. -/
lemma vertexSetDegree_upperDeviation_probability_le
    (n M : ℕ) (q : ℝ) (W : Finset (Vertex n))
    (hn : 0 < n) (hM0 : 0 < M) (hM : M ≤ (allEdges n).card)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    finsetProbability (sample n M)
        (VertexSetDegreeUpperDeviation n M q W) ≤
      4 * (((allEdges n).card + 1 : ℝ) *
        Real.exp (-((q * (W.card : ℝ) * ((M : ℝ) / n) / 6)^2 /
          (4 * M)))) := by
  let delta : ℝ := q * (W.card : ℝ) * ((M : ℝ) / n) / 6
  let P : ℕ → Finset (Edge n) → Prop := fun j H ↦
    edgeVertexSetClassMean n M W j + delta ≤
      sampledEdgeVertexSetClassCount H W j
  have hcontain : finsetProbability (sample n M)
      (VertexSetDegreeUpperDeviation n M q W) ≤
      finsetProbability (sample n M)
        (fun H ↦ ∃ j ∈ Finset.range 4, P j H) := by
    apply finsetProbability_mono_event
    intro H hHs hdev
    obtain ⟨j, hj, hclass⟩ :=
      vertexSetDegree_upperDeviation_implies_class n M q W hn hHs hdev
    refine ⟨j, hj, ?_⟩
    dsimp only [P, delta]
    linarith
  calc
    finsetProbability (sample n M)
        (VertexSetDegreeUpperDeviation n M q W) ≤
      finsetProbability (sample n M)
        (fun H ↦ ∃ j ∈ Finset.range 4, P j H) := hcontain
    _ ≤ ∑ j ∈ Finset.range 4,
        finsetProbability (sample n M) (P j) :=
      finsetProbability_bexists_le_sum _ _ _
    _ ≤ ∑ _j ∈ Finset.range 4,
        (((allEdges n).card + 1 : ℝ) *
          Real.exp (-(delta^2 / (4 * M)))) := by
      apply Finset.sum_le_sum
      intro j hj
      exact sampledEdgeVertexSetClass_upper_additive_le
        n M W j delta hn hM0 hM
          (vertexSetDegree_classDelta_nonneg n M q W hq0)
          (vertexSetDegree_classDelta_le_two_mul n M q W hn hq0 hq1)
    _ = 4 * (((allEdges n).card + 1 : ℝ) *
        Real.exp (-((q * (W.card : ℝ) * ((M : ℝ) / n) / 6)^2 /
          (4 * M)))) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rfl

/-- Lower-tail companion to
`vertexSetDegree_upperDeviation_probability_le`. -/
lemma vertexSetDegree_lowerDeviation_probability_le
    (n M : ℕ) (q : ℝ) (W : Finset (Vertex n))
    (hn : 0 < n) (hM0 : 0 < M) (hM : M ≤ (allEdges n).card)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    finsetProbability (sample n M)
        (VertexSetDegreeLowerDeviation n M q W) ≤
      4 * (((allEdges n).card + 1 : ℝ) *
        Real.exp (-((q * (W.card : ℝ) * ((M : ℝ) / n) / 6)^2 /
          (4 * M)))) := by
  let delta : ℝ := q * (W.card : ℝ) * ((M : ℝ) / n) / 6
  let P : ℕ → Finset (Edge n) → Prop := fun j H ↦
    (sampledEdgeVertexSetClassCount H W j : ℝ) ≤
      edgeVertexSetClassMean n M W j - delta
  have hcontain : finsetProbability (sample n M)
      (VertexSetDegreeLowerDeviation n M q W) ≤
      finsetProbability (sample n M)
        (fun H ↦ ∃ j ∈ Finset.range 4, P j H) := by
    apply finsetProbability_mono_event
    intro H hHs hdev
    obtain ⟨j, hj, hclass⟩ :=
      vertexSetDegree_lowerDeviation_implies_class n M q W hn hHs hdev
    refine ⟨j, hj, ?_⟩
    dsimp only [P, delta]
    linarith
  calc
    finsetProbability (sample n M)
        (VertexSetDegreeLowerDeviation n M q W) ≤
      finsetProbability (sample n M)
        (fun H ↦ ∃ j ∈ Finset.range 4, P j H) := hcontain
    _ ≤ ∑ j ∈ Finset.range 4,
        finsetProbability (sample n M) (P j) :=
      finsetProbability_bexists_le_sum _ _ _
    _ ≤ ∑ _j ∈ Finset.range 4,
        (((allEdges n).card + 1 : ℝ) *
          Real.exp (-(delta^2 / (4 * M)))) := by
      apply Finset.sum_le_sum
      intro j hj
      exact sampledEdgeVertexSetClass_lower_additive_le
        n M W j delta hn hM0 hM
          (vertexSetDegree_classDelta_nonneg n M q W hq0)
          (vertexSetDegree_classDelta_le_two_mul n M q W hn hq0 hq1)
    _ = 4 * (((allEdges n).card + 1 : ℝ) *
        Real.exp (-((q * (W.card : ℝ) * ((M : ℝ) / n) / 6)^2 /
          (4 * M)))) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rfl

def degreeRelativeLowerBadVertices (n M : ℕ) (q : ℝ)
    (H : Finset (Edge n)) : Finset (Vertex n) :=
  Finset.univ.filter fun v ↦
    (vertexDegree H v : ℝ) ≤ (1 - q) * ((M : ℝ) / n)

def degreeRelativeUpperBadVertices (n M : ℕ) (q : ℝ)
    (H : Finset (Edge n)) : Finset (Vertex n) :=
  Finset.univ.filter fun v ↦
    (1 + q) * ((M : ℝ) / n) ≤ vertexDegree H v

lemma degreeRelativeBadVertices_subset_lower_union_upper
    (n M : ℕ) (q : ℝ) (H : Finset (Edge n)) :
    degreeRelativeBadVertices n M q H ⊆
      degreeRelativeLowerBadVertices n M q H ∪
        degreeRelativeUpperBadVertices n M q H := by
  intro v hv
  rcases (Finset.mem_filter.mp hv).2 with hlower | hupper
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨by simp, hlower⟩)
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨by simp, hupper⟩)

lemma degreeRelativeLowerBadVertices_deviation
    (n M : ℕ) (q : ℝ) (H : Finset (Edge n)) :
    VertexSetDegreeLowerDeviation n M q
      (degreeRelativeLowerBadVertices n M q H) H := by
  let W := degreeRelativeLowerBadVertices n M q H
  have hsum : vertexSetDegreeSum H W ≤
      ∑ _v ∈ W, (1 - q) * ((M : ℝ) / n) := by
    unfold vertexSetDegreeSum
    apply Finset.sum_le_sum
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have hconst : (∑ _v ∈ W, (1 - q) * ((M : ℝ) / n)) =
      (W.card : ℝ) * ((1 - q) * ((M : ℝ) / n)) := by simp
  unfold VertexSetDegreeLowerDeviation
  dsimp only [W] at hsum hconst ⊢
  rw [hconst] at hsum
  nlinarith

lemma degreeRelativeUpperBadVertices_deviation
    (n M : ℕ) (q : ℝ) (H : Finset (Edge n)) :
    VertexSetDegreeUpperDeviation n M q
      (degreeRelativeUpperBadVertices n M q H) H := by
  let W := degreeRelativeUpperBadVertices n M q H
  have hsum : (∑ _v ∈ W, (1 + q) * ((M : ℝ) / n)) ≤
      vertexSetDegreeSum H W := by
    unfold vertexSetDegreeSum
    apply Finset.sum_le_sum
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have hconst : (∑ _v ∈ W, (1 + q) * ((M : ℝ) / n)) =
      (W.card : ℝ) * ((1 + q) * ((M : ℝ) / n)) := by simp
  unfold VertexSetDegreeUpperDeviation
  dsimp only [W] at hsum hconst ⊢
  rw [hconst] at hsum
  nlinarith

/-- If more than an `eta` proportion of vertices have atypical degree,
then one of the two one-sided bad sets is large and its total incidence
sum has the corresponding deviation. -/
lemma degreeRelativeBadVertices_large_implies_vertexSetDeviation
    (n M : ℕ) (q eta : ℝ) (H : Finset (Edge n))
    (hlarge : eta * (3 * n : ℝ) <
      (degreeRelativeBadVertices n M q H).card) :
    ∃ W ∈ (Finset.univ : Finset (Vertex n)).powerset,
      eta * (3 * n : ℝ) / 2 < (W.card : ℝ) ∧
        (VertexSetDegreeLowerDeviation n M q W H ∨
          VertexSetDegreeUpperDeviation n M q W H) := by
  let WL := degreeRelativeLowerBadVertices n M q H
  let WU := degreeRelativeUpperBadVertices n M q H
  have hsub : degreeRelativeBadVertices n M q H ⊆ WL ∪ WU := by
    exact degreeRelativeBadVertices_subset_lower_union_upper n M q H
  have hcardNat : (degreeRelativeBadVertices n M q H).card ≤
      WL.card + WU.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le WL WU)
  have hcard : ((degreeRelativeBadVertices n M q H).card : ℝ) ≤
      (WL.card : ℝ) + WU.card := by exact_mod_cast hcardNat
  have hbig : eta * (3 * n : ℝ) / 2 < (WL.card : ℝ) ∨
      eta * (3 * n : ℝ) / 2 < (WU.card : ℝ) := by
    by_contra hnot
    push Not at hnot
    linarith
  rcases hbig with hWL | hWU
  · refine ⟨WL, ?_, hWL, Or.inl ?_⟩
    · exact Finset.mem_powerset.mpr (by simp [WL, degreeRelativeLowerBadVertices])
    · exact degreeRelativeLowerBadVertices_deviation n M q H
  · refine ⟨WU, ?_, hWU, Or.inr ?_⟩
    · exact Finset.mem_powerset.mpr (by simp [WU, degreeRelativeUpperBadVertices])
    · exact degreeRelativeUpperBadVertices_deviation n M q H

lemma vertexSetDegree_class_exp_le_uniform
    (n M : ℕ) (q eta : ℝ) (W : Finset (Vertex n))
    (hn : 0 < n) (hM0 : 0 < M)
    (hq0 : 0 ≤ q) (heta0 : 0 ≤ eta)
    (hW : eta * (3 * n : ℝ) / 2 ≤ (W.card : ℝ)) :
    ((allEdges n).card + 1 : ℝ) *
        Real.exp (-((q * (W.card : ℝ) * ((M : ℝ) / n) / 6)^2 /
          (4 * M))) ≤
      ((allEdges n).card + 1 : ℝ) *
        Real.exp (-(q^2 * eta^2 * (M : ℝ) / 64)) := by
  let D : ℝ := q * (W.card : ℝ) * ((M : ℝ) / n)
  let R : ℝ := ((allEdges n).card + 1 : ℝ)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM0
  have hfactor0 : 0 ≤ q * ((M : ℝ) / n) := by positivity
  have hDlower : (3 / 2 : ℝ) * q * eta * M ≤ D := by
    calc
      (3 / 2 : ℝ) * q * eta * M =
          (q * ((M : ℝ) / n)) * (eta * (3 * n : ℝ) / 2) := by
        field_simp [hnR.ne']
      _ ≤ (q * ((M : ℝ) / n)) * (W.card : ℝ) :=
        mul_le_mul_of_nonneg_left hW hfactor0
      _ = D := by dsimp only [D]; ring
  have hD0 : 0 ≤ D := by dsimp only [D]; positivity
  have hlower0 : 0 ≤ (3 / 2 : ℝ) * q * eta * M := by positivity
  have hsquare : ((3 / 2 : ℝ) * q * eta * M)^2 ≤ D^2 := by
    nlinarith [sq_nonneg (D - (3 / 2 : ℝ) * q * eta * M)]
  have hquad : q^2 * eta^2 * (M : ℝ) / 64 ≤
      (D / 6)^2 / (4 * M) := by
    field_simp [hMR.ne'] at hsquare ⊢
    nlinarith
  have hexp : Real.exp (-((D / 6)^2 / (4 * M))) ≤
      Real.exp (-(q^2 * eta^2 * (M : ℝ) / 64)) :=
    Real.exp_le_exp.mpr (neg_le_neg hquad)
  have htail : R * Real.exp (-((D / 6)^2 / (4 * M))) ≤
      R * Real.exp (-(q^2 * eta^2 * (M : ℝ) / 64)) :=
    mul_le_mul_of_nonneg_left hexp (by dsimp only [R]; positivity)
  simpa only [D, R] using htail

lemma vertexSetDegree_lowerDeviation_probability_le_uniform
    (n M : ℕ) (q eta : ℝ) (W : Finset (Vertex n))
    (hn : 0 < n) (hM0 : 0 < M) (hM : M ≤ (allEdges n).card)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (heta0 : 0 ≤ eta)
    (hW : eta * (3 * n : ℝ) / 2 ≤ (W.card : ℝ)) :
    finsetProbability (sample n M)
        (VertexSetDegreeLowerDeviation n M q W) ≤
      4 * (((allEdges n).card + 1 : ℝ) *
        Real.exp (-(q^2 * eta^2 * (M : ℝ) / 64))) := by
  exact (vertexSetDegree_lowerDeviation_probability_le
    n M q W hn hM0 hM hq0 hq1).trans
      (mul_le_mul_of_nonneg_left
        (vertexSetDegree_class_exp_le_uniform
          n M q eta W hn hM0 hq0 heta0 hW) (by norm_num))

lemma vertexSetDegree_upperDeviation_probability_le_uniform
    (n M : ℕ) (q eta : ℝ) (W : Finset (Vertex n))
    (hn : 0 < n) (hM0 : 0 < M) (hM : M ≤ (allEdges n).card)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (heta0 : 0 ≤ eta)
    (hW : eta * (3 * n : ℝ) / 2 ≤ (W.card : ℝ)) :
    finsetProbability (sample n M)
        (VertexSetDegreeUpperDeviation n M q W) ≤
      4 * (((allEdges n).card + 1 : ℝ) *
        Real.exp (-(q^2 * eta^2 * (M : ℝ) / 64))) := by
  exact (vertexSetDegree_upperDeviation_probability_le
    n M q W hn hM0 hM hq0 hq1).trans
      (mul_le_mul_of_nonneg_left
        (vertexSetDegree_class_exp_le_uniform
          n M q eta W hn hM0 hq0 heta0 hW) (by norm_num))

noncomputable def largeVertexSubsets (n : ℕ) (eta : ℝ) :
    Finset (Finset (Vertex n)) :=
  (Finset.univ : Finset (Vertex n)).powerset.filter fun W ↦
    eta * (3 * n : ℝ) / 2 < (W.card : ℝ)

lemma largeVertexSubsets_card_le_pow (n : ℕ) (eta : ℝ) :
    (largeVertexSubsets n eta).card ≤ 2^(3 * n) := by
  calc
    (largeVertexSubsets n eta).card ≤
        ((Finset.univ : Finset (Vertex n)).powerset).card := by
      unfold largeVertexSubsets
      exact Finset.card_filter_le _ _
    _ = 2^(3 * n) := by
      rw [Finset.card_powerset, Finset.card_univ, Fintype.card_fin]

noncomputable def largeLowerDegreeDeviationFailureSet
    (n M : ℕ) (q eta : ℝ) : Finset (Finset (Edge n)) :=
  (largeVertexSubsets n eta).biUnion fun W ↦
    (sample n M).filter (VertexSetDegreeLowerDeviation n M q W)

noncomputable def largeUpperDegreeDeviationFailureSet
    (n M : ℕ) (q eta : ℝ) : Finset (Finset (Edge n)) :=
  (largeVertexSubsets n eta).biUnion fun W ↦
    (sample n M).filter (VertexSetDegreeUpperDeviation n M q W)

lemma finsetProbability_mem_biUnion_le_card_mul
    {α ι : Type*} (s : Finset α) (I : Finset ι)
    (F : ι → Finset α) (R : ℝ)
    (hsub : ∀ i ∈ I, F i ⊆ s)
    (hpoint : ∀ i ∈ I,
      finsetProbability s (fun x ↦ x ∈ F i) ≤ R) :
    finsetProbability s (fun x ↦ x ∈ I.biUnion F) ≤
      (I.card : ℝ) * R := by
  calc
    finsetProbability s (fun x ↦ x ∈ I.biUnion F) ≤
      ∑ i ∈ I, finsetProbability s (fun x ↦ x ∈ F i) :=
        finsetProbability_mem_biUnion_le_sum s I F hsub
    _ ≤ ∑ _i ∈ I, R := Finset.sum_le_sum hpoint
    _ = (I.card : ℝ) * R := by simp

lemma finsetProbability_filter_membership_eq {α : Type*}
    (s : Finset α) (P : α → Prop) :
    finsetProbability s (fun x ↦ x ∈ s.filter P) =
      finsetProbability s P := by
  apply finsetProbability_congr_event
  intro x hx
  simp [hx]

lemma largeLowerDegreeDeviationFailureSet_probability_le_card
    (n M : ℕ) (q eta : ℝ)
    (hn : 0 < n) (hM0 : 0 < M) (hM : M ≤ (allEdges n).card)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (heta0 : 0 ≤ eta) :
    finsetProbability (sample n M)
        (fun H ↦ H ∈ largeLowerDegreeDeviationFailureSet n M q eta) ≤
      ((largeVertexSubsets n eta).card : ℝ) *
        (4 * (((allEdges n).card + 1 : ℝ) *
          Real.exp (-(q^2 * eta^2 * (M : ℝ) / 64)))) := by
  let I := largeVertexSubsets n eta
  let F : Finset (Vertex n) → Finset (Finset (Edge n)) := fun W ↦
    (sample n M).filter (VertexSetDegreeLowerDeviation n M q W)
  let R : ℝ := 4 * (((allEdges n).card + 1 : ℝ) *
    Real.exp (-(q^2 * eta^2 * (M : ℝ) / 64)))
  have hbase := finsetProbability_mem_biUnion_le_sum
    (sample n M) I F (fun W _ ↦ Finset.filter_subset _ _)
  have hdec :
      (fun A B : Finset (Edge n) ↦ Classical.propDecidable (A = B)) =
        (Finset.decidableEq : DecidableEq (Finset (Edge n))) :=
    Subsingleton.elim _ _
  rw [hdec] at hbase
  calc
    finsetProbability (sample n M)
        (fun H ↦ H ∈ largeLowerDegreeDeviationFailureSet n M q eta) =
      finsetProbability (sample n M) (fun H ↦ H ∈ I.biUnion F) := by rfl
    _ ≤ ∑ W ∈ I, finsetProbability (sample n M)
        (fun H ↦ H ∈ F W) := hbase
    _ = ∑ W ∈ I, finsetProbability (sample n M)
        (VertexSetDegreeLowerDeviation n M q W) := by
      apply Finset.sum_congr rfl
      intro W hWI
      apply finsetProbability_congr_event
      intro H hHs
      simp [F, hHs]
    _ ≤ ∑ _W ∈ I, R := by
      apply Finset.sum_le_sum
      intro W hWI
      exact vertexSetDegree_lowerDeviation_probability_le_uniform
        n M q eta W hn hM0 hM hq0 hq1 heta0
          (Finset.mem_filter.mp hWI).2.le
    _ = (I.card : ℝ) * R := by simp
    _ = _ := by rfl

lemma largeLowerDegreeDeviationFailureSet_probability_le
    (n M : ℕ) (q eta : ℝ)
    (hn : 0 < n) (hM0 : 0 < M) (hM : M ≤ (allEdges n).card)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (heta0 : 0 ≤ eta) :
    finsetProbability (sample n M)
        (fun H ↦ H ∈ largeLowerDegreeDeviationFailureSet n M q eta) ≤
      (2 : ℝ)^(3 * n) *
        (4 * (((allEdges n).card + 1 : ℝ) *
          Real.exp (-(q^2 * eta^2 * (M : ℝ) / 64)))) := by
  have hcard : ((largeVertexSubsets n eta).card : ℝ) ≤
      (2 : ℝ)^(3 * n) := by
    exact_mod_cast largeVertexSubsets_card_le_pow n eta
  exact (largeLowerDegreeDeviationFailureSet_probability_le_card
    n M q eta hn hM0 hM hq0 hq1 heta0).trans
      (mul_le_mul_of_nonneg_right hcard (by positivity))

lemma largeUpperDegreeDeviationFailureSet_probability_le_card
    (n M : ℕ) (q eta : ℝ)
    (hn : 0 < n) (hM0 : 0 < M) (hM : M ≤ (allEdges n).card)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (heta0 : 0 ≤ eta) :
    finsetProbability (sample n M)
        (fun H ↦ H ∈ largeUpperDegreeDeviationFailureSet n M q eta) ≤
      ((largeVertexSubsets n eta).card : ℝ) *
        (4 * (((allEdges n).card + 1 : ℝ) *
          Real.exp (-(q^2 * eta^2 * (M : ℝ) / 64)))) := by
  let I := largeVertexSubsets n eta
  let F : Finset (Vertex n) → Finset (Finset (Edge n)) := fun W ↦
    (sample n M).filter (VertexSetDegreeUpperDeviation n M q W)
  let R : ℝ := 4 * (((allEdges n).card + 1 : ℝ) *
    Real.exp (-(q^2 * eta^2 * (M : ℝ) / 64)))
  have hbase := finsetProbability_mem_biUnion_le_sum
    (sample n M) I F (fun W _ ↦ Finset.filter_subset _ _)
  have hdec :
      (fun A B : Finset (Edge n) ↦ Classical.propDecidable (A = B)) =
        (Finset.decidableEq : DecidableEq (Finset (Edge n))) :=
    Subsingleton.elim _ _
  rw [hdec] at hbase
  calc
    finsetProbability (sample n M)
        (fun H ↦ H ∈ largeUpperDegreeDeviationFailureSet n M q eta) =
      finsetProbability (sample n M) (fun H ↦ H ∈ I.biUnion F) := by rfl
    _ ≤ ∑ W ∈ I, finsetProbability (sample n M)
        (fun H ↦ H ∈ F W) := hbase
    _ = ∑ W ∈ I, finsetProbability (sample n M)
        (VertexSetDegreeUpperDeviation n M q W) := by
      apply Finset.sum_congr rfl
      intro W hWI
      apply finsetProbability_congr_event
      intro H hHs
      simp [F, hHs]
    _ ≤ ∑ _W ∈ I, R := by
      apply Finset.sum_le_sum
      intro W hWI
      exact vertexSetDegree_upperDeviation_probability_le_uniform
        n M q eta W hn hM0 hM hq0 hq1 heta0
          (Finset.mem_filter.mp hWI).2.le
    _ = (I.card : ℝ) * R := by simp
    _ = _ := by rfl

lemma largeUpperDegreeDeviationFailureSet_probability_le
    (n M : ℕ) (q eta : ℝ)
    (hn : 0 < n) (hM0 : 0 < M) (hM : M ≤ (allEdges n).card)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (heta0 : 0 ≤ eta) :
    finsetProbability (sample n M)
        (fun H ↦ H ∈ largeUpperDegreeDeviationFailureSet n M q eta) ≤
      (2 : ℝ)^(3 * n) *
        (4 * (((allEdges n).card + 1 : ℝ) *
          Real.exp (-(q^2 * eta^2 * (M : ℝ) / 64)))) := by
  have hcard : ((largeVertexSubsets n eta).card : ℝ) ≤
      (2 : ℝ)^(3 * n) := by
    exact_mod_cast largeVertexSubsets_card_le_pow n eta
  exact (largeUpperDegreeDeviationFailureSet_probability_le_card
    n M q eta hn hM0 hM hq0 hq1 heta0).trans
      (mul_le_mul_of_nonneg_right hcard (by positivity))

/-- Exponential aggregate-degree concentration at every sampling density.
The factor `2^(3n)` is the crude union bound over vertex subsets; its cost
is absorbed later because `q^2 eta^2 M / n` tends to infinity. -/
lemma degreeRelativeBadVertices_large_probability_le_allDensity
    (n M : ℕ) (q eta : ℝ)
    (hn : 0 < n) (hM0 : 0 < M) (hM : M ≤ (allEdges n).card)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (heta0 : 0 ≤ eta) :
    finsetProbability (sample n M)
        (fun H ↦ eta * (3 * n : ℝ) <
          (degreeRelativeBadVertices n M q H).card) ≤
      (2 : ℝ)^(3 * n) *
        (8 * (((allEdges n).card + 1 : ℝ) *
          Real.exp (-(q^2 * eta^2 * (M : ℝ) / 64)))) := by
  let PL : Finset (Edge n) → Prop := fun H ↦
    H ∈ largeLowerDegreeDeviationFailureSet n M q eta
  let PU : Finset (Edge n) → Prop := fun H ↦
    H ∈ largeUpperDegreeDeviationFailureSet n M q eta
  have hcontain : finsetProbability (sample n M)
      (fun H ↦ eta * (3 * n : ℝ) <
        (degreeRelativeBadVertices n M q H).card) ≤
      finsetProbability (sample n M) (fun H ↦ PL H ∨ PU H) := by
    apply finsetProbability_mono_event
    intro H hHs hlarge
    obtain ⟨W, hWp, hWlarge, hdev⟩ :=
      degreeRelativeBadVertices_large_implies_vertexSetDeviation
        n M q eta H hlarge
    have hWI : W ∈ largeVertexSubsets n eta :=
      Finset.mem_filter.mpr ⟨hWp, hWlarge⟩
    rcases hdev with hlow | hupp
    · apply Or.inl
      exact Finset.mem_biUnion.mpr
        ⟨W, hWI, Finset.mem_filter.mpr ⟨hHs, hlow⟩⟩
    · apply Or.inr
      exact Finset.mem_biUnion.mpr
        ⟨W, hWI, Finset.mem_filter.mpr ⟨hHs, hupp⟩⟩
  calc
    finsetProbability (sample n M)
        (fun H ↦ eta * (3 * n : ℝ) <
          (degreeRelativeBadVertices n M q H).card) ≤
      finsetProbability (sample n M) (fun H ↦ PL H ∨ PU H) := hcontain
    _ ≤ finsetProbability (sample n M) PL +
        finsetProbability (sample n M) PU :=
      finsetProbability_or_le_add _ _ _
    _ ≤ (2 : ℝ)^(3 * n) *
          (4 * (((allEdges n).card + 1 : ℝ) *
            Real.exp (-(q^2 * eta^2 * (M : ℝ) / 64)))) +
        (2 : ℝ)^(3 * n) *
          (4 * (((allEdges n).card + 1 : ℝ) *
            Real.exp (-(q^2 * eta^2 * (M : ℝ) / 64)))) :=
      add_le_add
        (largeLowerDegreeDeviationFailureSet_probability_le
          n M q eta hn hM0 hM hq0 hq1 heta0)
        (largeUpperDegreeDeviationFailureSet_probability_le
          n M q eta hn hM0 hM hq0 hq1 heta0)
    _ = (2 : ℝ)^(3 * n) *
        (8 * (((allEdges n).card + 1 : ℝ) *
          Real.exp (-(q^2 * eta^2 * (M : ℝ) / 64)))) := by ring

end

end Erdos747
