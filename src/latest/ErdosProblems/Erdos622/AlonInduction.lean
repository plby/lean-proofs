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
import ErdosProblems.Erdos622.HighGirthLinear
import ErdosProblems.Erdos622.AlonSparseSubgraph

/-!
# The deterministic induction in Alon's linear-arboricity argument

This file isolates the exact induction used after the high-girth extraction
and high-girth decomposition steps.  At one peeling step a graph `G` is
covered by a high-girth block `H` and a remainder `R`.  The block has a
linear-forest cover costing at most `(1 + eta) * q / 2` colours, while the
degree parameter of the remainder drops from `D` to `D - q`.  Iteration gives

`la(G) <= (1 + eta) * D / 2 + baseCost`.

The additive base cost is then absorbed by using `eta = epsilon / 2` and
taking `D >= 4 * baseCost / epsilon`.  All graph-theoretic input is supplied
as local theorem parameters, so this module contains precisely the
well-founded induction and the scalar estimates, without introducing any
ambient assumptions.
-/

open Filter Finset
open scoped Topology

namespace Erdos622
namespace AlonInduction

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u} [Fintype V]

open LinearArboricity

/-! ## Covers convenient for recursive gluing -/

/-- A cover by `k` linear forests, with a chosen covering colour for every
edge.  The chosen colour makes gluing covers across a graph split completely
explicit. -/
structure Cover (G : SimpleGraph V) (k : ℕ) where
  graph : Fin k → SimpleGraph V
  graph_le : ∀ i, graph i ≤ G
  linear : ∀ i, Erdos622.SimpleGraph.IsLinearForest (graph i)
  locate : G.edgeSet → Fin k
  mem_graph_locate : ∀ e, e.1 ∈ (graph (locate e)).edgeSet

namespace Cover

variable {G H R : SimpleGraph V} {a b : ℕ}

/-- Every edge-partition decomposition gives a chosen-colour cover. -/
def ofDecomposition (d : Decomposition G a) : Cover G a where
  graph i := colorGraph d.color i
  graph_le i := colorGraph_le d.color i
  linear i := d.linear i
  locate e := d.color e
  mem_graph_locate e := mem_colorGraph_edgeSet d.color e

/-- A chosen-colour cover gives an edge-partition decomposition.  Its colour
graph is a subgraph of the corresponding covering forest, so linearity is
inherited downward. -/
def toDecomposition (c : Cover G a) : Decomposition G a where
  color := c.locate
  linear i := by
    apply c.linear i |>.anti
    rw [colorGraph, SimpleGraph.fromEdgeSet_le]
    intro e he
    obtain ⟨heG, hi⟩ := he.1
    have he := c.mem_graph_locate ⟨e, heG⟩
    simpa [hi] using he

/-- Restrict a cover along an induced graph embedding. -/
def pullback {W : Type*} [Fintype W] {K : SimpleGraph W}
    (f : G ↪g K) (c : Cover K a) : Cover G a :=
  ofDecomposition
    (GraphRegularCompletion.pullbackDecomposition f c.toDecomposition)

/-- Glue covers of two subgraphs whose union covers the ambient graph. -/
def add (hH : H ≤ G) (hR : R ≤ G) (hcover : G ≤ H ⊔ R)
    (cH : Cover H a) (cR : Cover R b) : Cover G (a + b) where
  graph := Fin.addCases cH.graph cR.graph
  graph_le i := by
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [Fin.addCases_left] using (cH.graph_le j).trans hH
    · intro j
      simpa only [Fin.addCases_right] using (cR.graph_le j).trans hR
  linear i := by
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [Fin.addCases_left] using cH.linear j
    · intro j
      simpa only [Fin.addCases_right] using cR.linear j
  locate e := by
    by_cases heH : e.1 ∈ H.edgeSet
    · exact Fin.castAdd b (cH.locate ⟨e.1, heH⟩)
    · have heSup : e.1 ∈ (H ⊔ R).edgeSet := by
        exact SimpleGraph.edgeSet_mono hcover e.2
      rw [SimpleGraph.edgeSet_sup] at heSup
      have heR : e.1 ∈ R.edgeSet := heSup.resolve_left heH
      exact Fin.natAdd a (cR.locate ⟨e.1, heR⟩)
  mem_graph_locate e := by
    by_cases heH : e.1 ∈ H.edgeSet
    · simp only [dif_pos heH, Fin.addCases_left]
      exact cH.mem_graph_locate ⟨e.1, heH⟩
    · have heSup : e.1 ∈ (H ⊔ R).edgeSet := by
        exact SimpleGraph.edgeSet_mono hcover e.2
      rw [SimpleGraph.edgeSet_sup] at heSup
      have heR : e.1 ∈ R.edgeSet := heSup.resolve_left heH
      simp only [dif_neg heH, Fin.addCases_right]
      exact cR.mem_graph_locate ⟨e.1, heR⟩

end Cover

/-! ## Removing a sampled spanning block -/

/-- The residual graph after removing all edges of `H` from `G`. -/
def edgeRemainder (G H : SimpleGraph V) : SimpleGraph V :=
  G.deleteEdges H.edgeSet

lemma edgeRemainder_le (G H : SimpleGraph V) : edgeRemainder G H ≤ G :=
  SimpleGraph.deleteEdges_le H.edgeSet

/-- A subgraph and its edge remainder cover the original graph. -/
lemma sup_edgeRemainder_eq {G H : SimpleGraph V} (hHG : H ≤ G) :
    H ⊔ edgeRemainder G H = G := by
  apply le_antisymm
  · exact sup_le hHG (edgeRemainder_le G H)
  · intro v w hvw
    by_cases hH : H.Adj v w
    · exact Or.inl hH
    · apply Or.inr
      rw [edgeRemainder, SimpleGraph.deleteEdges_adj]
      refine ⟨hvw, ?_⟩
      simpa only [SimpleGraph.mem_edgeSet] using hH

/-- At each vertex, the remainder neighbour set is the set difference of the
host and sampled-block neighbour sets. -/
lemma neighborSet_edgeRemainder {G H : SimpleGraph V} (hHG : H ≤ G) (v : V) :
    (edgeRemainder G H).neighborSet v = G.neighborSet v \ H.neighborSet v := by
  ext w
  simp only [SimpleGraph.mem_neighborSet, Set.mem_sdiff, edgeRemainder,
    SimpleGraph.deleteEdges_adj, SimpleGraph.mem_edgeSet]

/-- In a `D`-regular host, removing a block of minimum degree at least `q`
leaves maximum degree at most `D-q`. -/
lemma ncard_neighborSet_edgeRemainder_le {G H : SimpleGraph V}
    (hHG : H ≤ G) {D q : ℕ}
    (hregular : ∀ v, (G.neighborSet v).ncard = D)
    (hminimum : ∀ v, q ≤ (H.neighborSet v).ncard) (v : V) :
    ((edgeRemainder G H).neighborSet v).ncard ≤ D - q := by
  rw [neighborSet_edgeRemainder hHG,
    Set.ncard_sdiff' (SimpleGraph.neighborSet_mono hHG v), hregular v]
  exact Nat.sub_le_sub_left (hminimum v) D

/-! ## Abstract form of the high-girth peeling input -/

/-- The output required from the high-girth selection and decomposition
lemmas at a fixed relative error `eta`.

The base clause handles bounded degree.  The step clause selects a block `H`
and a remainder `R`; `q` is the guaranteed degree drop and `m` is the number
of linear forests used on the selected block. -/
structure PeelingData (eta : ℝ) where
  threshold : ℕ
  baseCost : ℕ
  base :
    ∀ (W : Type u) [Fintype W] (G : SimpleGraph W) [DecidableRel G.Adj]
      (D : ℕ),
      D ≤ threshold →
      (∀ v, (G.neighborSet v).ncard ≤ D) →
      ∃ k : ℕ, Nonempty (Cover G k) ∧ k ≤ baseCost
  step :
    ∀ (W : Type u) [Fintype W] (G : SimpleGraph W) [DecidableRel G.Adj]
      (D : ℕ),
      threshold < D →
      (∀ v, (G.neighborSet v).ncard = D) →
      ∃ (H R : SimpleGraph W) (q m : ℕ),
        H ≤ G ∧ R ≤ G ∧ G ≤ H ⊔ R ∧
        0 < q ∧ q ≤ D ∧
        (∀ v, (R.neighborSet v).ncard ≤ D - q) ∧
        Nonempty (Cover H m) ∧
        (m : ℝ) ≤ (1 + eta) * (q : ℝ) / 2

/-- The one-step theorem naturally produced by Alon's sparse high-girth
subgraph lemma and the high-girth linear-forest decomposition. -/
def RegularPeelingStep (eta : ℝ) (threshold : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] (G : SimpleGraph W) [DecidableRel G.Adj]
    (D : ℕ),
    threshold < D →
    (∀ v, (G.neighborSet v).ncard = D) →
    ∃ (H R : SimpleGraph W) (q m : ℕ),
      H ≤ G ∧ R ≤ G ∧ G ≤ H ⊔ R ∧
      0 < q ∧ q ≤ D ∧
      (∀ v, (R.neighborSet v).ncard ≤ D - q) ∧
      Nonempty (Cover H m) ∧
      (m : ℝ) ≤ (1 + eta) * (q : ℝ) / 2

/-- The output format naturally supplied by the sparse-subgraph theorem and
the high-girth decomposition theorem: a sampled block with a minimum-degree
lower bound and the desired colour budget. -/
def RegularBlockSelection (eta : ℝ) (threshold : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] (G : SimpleGraph W) [DecidableRel G.Adj]
    (D : ℕ),
    threshold < D →
    (∀ v, (G.neighborSet v).ncard = D) →
    ∃ (H : SimpleGraph W) (q m : ℕ),
      H ≤ G ∧ 0 < q ∧ q ≤ D ∧
      (∀ v, q ≤ (H.neighborSet v).ncard) ∧
      Nonempty (Cover H m) ∧
      (m : ℝ) ≤ (1 + eta) * (q : ℝ) / 2

/-- A regular block selection supplies a peeling step by taking the literal
edge complement inside the regular host. -/
theorem regularPeelingStep_of_blockSelection {eta : ℝ} {threshold : ℕ}
    (hselect : RegularBlockSelection.{u} eta threshold) :
    RegularPeelingStep.{u} eta threshold := by
  intro W _ G _ D hD hregular
  obtain ⟨H, q, m, hHG, hq, hqD, hminimum, cH, hm⟩ :=
    hselect W G D hD hregular
  let R := edgeRemainder G H
  refine ⟨H, R, q, m, hHG, edgeRemainder_le G H, ?_, hq, hqD, ?_, cH, hm⟩
  · exact (sup_edgeRemainder_eq hHG).ge
  · intro v
    exact ncard_neighborSet_edgeRemainder_le hHG hregular hminimum v

/-- A regular-graph peeling step extends to arbitrary bounded-degree graphs:
the low-degree endpoint is greedily coloured, while every recursive graph is
first embedded in the explicit regular completion. -/
def PeelingData.ofRegularStep (eta : ℝ) (threshold : ℕ)
    (hstep : RegularPeelingStep.{u} eta threshold) : PeelingData.{u} eta where
  threshold := threshold
  baseCost := 2 * threshold + 1
  base := by
    intro W _ G _ D hD hdegree
    obtain ⟨d⟩ :=
      GraphRegularCompletion.exists_greedyLinearForestDecomposition
        G threshold (fun v ↦ (hdegree v).trans hD)
    exact ⟨2 * threshold + 1, ⟨Cover.ofDecomposition d⟩, le_rfl⟩
  step := hstep

/-- Uniform availability of peeling data for every positive relative error. -/
def HasPeelingData : Prop :=
  ∀ eta : ℝ, 0 < eta → Nonempty (PeelingData.{u} eta)

/-- Uniform one-step form of the two concrete high-girth inputs. -/
def HasRegularPeelingSteps : Prop :=
  ∀ eta : ℝ, 0 < eta →
    ∃ threshold : ℕ, RegularPeelingStep.{u} eta threshold

/-! ## Scalar normalization of the high-girth block cost -/

/-- In Corollary 2.7 of Alon's paper, a high-girth block of maximum degree
`upper` costs at most `upper / 2 + 200 * upper / girth`.  Relative to a
guaranteed degree drop `lower`, its normalized cost multiplier is the
following expression. -/
def normalizedBlockCost (upper lower girth : ℝ) : ℝ :=
  upper / lower * (1 + 400 / girth)

/-- If the upper and lower sampled degrees are asymptotic and the girth tends
to infinity, the normalized high-girth decomposition cost tends to one. -/
theorem tendsto_normalizedBlockCost
    (upper lower girth : ℕ → ℝ)
    (hdegreeRatio :
      Tendsto (fun D ↦ upper D / lower D) atTop (nhds 1))
    (hGirthInv : Tendsto (fun D ↦ 1 / girth D) atTop (nhds 0)) :
    Tendsto (fun D ↦ normalizedBlockCost (upper D) (lower D) (girth D))
      atTop (nhds 1) := by
  have hsecond : Tendsto (fun D ↦ 1 + 400 * (1 / girth D))
      atTop (nhds (1 + 400 * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hGirthInv)
  simpa only [normalizedBlockCost, div_eq_mul_inv, mul_zero, add_zero,
    one_mul, mul_one]
    using hdegreeRatio.mul hsecond

/-- Eventual epsilon form of `tendsto_normalizedBlockCost`. -/
theorem eventually_normalizedBlockCost_le
    (upper lower girth : ℕ → ℝ)
    (hdegreeRatio :
      Tendsto (fun D ↦ upper D / lower D) atTop (nhds 1))
    (hGirthInv : Tendsto (fun D ↦ 1 / girth D) atTop (nhds 0))
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ D : ℕ in atTop,
      normalizedBlockCost (upper D) (lower D) (girth D) ≤ 1 + eta := by
  have hlt :=
    (tendsto_normalizedBlockCost upper lower girth hdegreeRatio hGirthInv).eventually_lt_const
      (by linarith : (1 : ℝ) < 1 + eta)
  filter_upwards [hlt] with D hD
  exact hD.le

/-- Exact algebra converting the normalized multiplier bound into the colour
budget required by a peeling step. -/
theorem blockCost_le_of_normalizedBlockCost_le
    {upper lower girth eta cost : ℝ}
    (hlower : 0 < lower) (hgirth : 0 < girth)
    (hcost : cost ≤ upper / 2 + 200 * upper / girth)
    (hnormalized : normalizedBlockCost upper lower girth ≤ 1 + eta) :
    cost ≤ (1 + eta) * lower / 2 := by
  have hidentity :
      upper / 2 + 200 * upper / girth =
        normalizedBlockCost upper lower girth * lower / 2 := by
    rw [normalizedBlockCost]
    field_simp
    <;> ring
  rw [hidentity] at hcost
  exact hcost.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hnormalized hlower.le) (by norm_num))

/-- A source-facing package: eventually every regular host contains a block
with prescribed lower degree, a linear-forest cover satisfying Alon's raw
Corollary 2.7 cost, and the indicated girth parameter. -/
def EventualRawBlockSelection
    (lower : ℕ → ℕ) (upper girth : ℕ → ℝ) : Prop :=
  ∀ᶠ D : ℕ in atTop,
    ∀ (W : Type u) [Fintype W] (G : SimpleGraph W) [DecidableRel G.Adj],
      (∀ v, (G.neighborSet v).ncard = D) →
      ∃ (H : SimpleGraph W) (m : ℕ),
        H ≤ G ∧ 0 < lower D ∧ lower D ≤ D ∧
        (∀ v, lower D ≤ (H.neighborSet v).ncard) ∧
        Nonempty (Cover H m) ∧
        (m : ℝ) ≤ upper D / 2 + 200 * upper D / girth D

/-- The source-facing eventual package, together with the two scalar limits,
produces all regular peeling steps required by the induction. -/
theorem hasRegularPeelingSteps_of_eventualRawBlockSelection
    (lower : ℕ → ℕ) (upper girth : ℕ → ℝ)
    (hraw : EventualRawBlockSelection.{u} lower upper girth)
    (hdegreeRatio :
      Tendsto (fun D ↦ upper D / (lower D : ℝ)) atTop (nhds 1))
    (hGirthInv : Tendsto (fun D ↦ 1 / girth D) atTop (nhds 0))
    (hGirthPos : ∀ᶠ D : ℕ in atTop, 0 < girth D) :
    HasRegularPeelingSteps.{u} := by
  intro eta heta
  have hnormalized := eventually_normalizedBlockCost_le
    upper (fun D ↦ (lower D : ℝ)) girth hdegreeRatio hGirthInv heta
  obtain ⟨threshold, hthreshold⟩ :=
    eventually_atTop.1 ((hraw.and hnormalized).and hGirthPos)
  refine ⟨threshold, regularPeelingStep_of_blockSelection ?_⟩
  intro W _ G _ D hD hregular
  obtain ⟨H, m, hHG, hlower, hlowerD, hminimum, cH, hcost⟩ :=
    (hthreshold D hD.le).1.1 W G hregular
  refine ⟨H, lower D, m, hHG, hlower, hlowerD, hminimum, cH, ?_⟩
  exact blockCost_le_of_normalizedBlockCost_le
    (by exact_mod_cast hlower) (hthreshold D hD.le).2
    hcost (hthreshold D hD.le).1.2

/-! ## The concrete logarithmic parameters

The sparse block in Alon's proof has degree
`(log D)^10 + O((log D)^6)` and girth scale
`log D / (20 log log D)`.  The following definitions include the integral
rounding needed by the graph-theoretic statements.  The limit lemmas below
verify, without an abstract asymptotic hypothesis, that the upper and lower
degrees are equivalent and that the reciprocal girth scale tends to zero. -/

def alonLogDegree (D : ℕ) : ℝ := Real.log (D : ℝ)

def alonLowerDegree (D : ℕ) : ℕ :=
  ⌊alonLogDegree D ^ 10 - alonLogDegree D ^ 6⌋₊

def alonUpperDegree (D : ℕ) : ℕ :=
  ⌈alonLogDegree D ^ 10 + alonLogDegree D ^ 6⌉₊

def alonGirthScale (D : ℕ) : ℕ :=
  ⌊alonLogDegree D / (20 * Real.log (alonLogDegree D))⌋₊ + 1

lemma tendsto_alonLogDegree_atTop :
    Tendsto alonLogDegree atTop atTop := by
  exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma tendsto_alonRelativeError_zero :
    Tendsto (fun D : ℕ ↦ alonLogDegree D ^ 6 / alonLogDegree D ^ 10)
      atTop (nhds 0) := by
  have hpow : Tendsto (fun D : ℕ ↦ alonLogDegree D ^ 4) atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (by norm_num)).comp tendsto_alonLogDegree_atTop
  apply hpow.inv_tendsto_atTop.congr'
  filter_upwards [tendsto_alonLogDegree_atTop.eventually_ne_atTop 0] with D hD
  simp only [Pi.inv_apply]
  field_simp

lemma tendsto_alonLowerReal_atTop :
    Tendsto (fun D : ℕ ↦ alonLogDegree D ^ 10 - alonLogDegree D ^ 6)
      atTop atTop := by
  have hrelativeEventually :
      ∀ᶠ D : ℕ in atTop,
        alonLogDegree D ^ 6 ≤ (1 / 2 : ℝ) * alonLogDegree D ^ 10 := by
    have h := tendsto_alonRelativeError_zero.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [h, tendsto_alonLogDegree_atTop.eventually_ge_atTop 1] with D hD hlog
    have hpowpos : 0 < alonLogDegree D ^ 10 := pow_pos (by positivity) _
    rw [div_lt_iff₀ hpowpos] at hD
    exact hD.le
  have hbound : ∀ᶠ D : ℕ in atTop,
      (1 / 2 : ℝ) * alonLogDegree D ^ 10 ≤
        alonLogDegree D ^ 10 - alonLogDegree D ^ 6 := by
    filter_upwards [hrelativeEventually] with D hD
    linarith
  exact tendsto_atTop_mono' atTop hbound
    (((tendsto_pow_atTop (α := ℝ) (by norm_num)).comp tendsto_alonLogDegree_atTop)
      |>.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2))

lemma tendsto_alonUpperReal_atTop :
    Tendsto (fun D : ℕ ↦ alonLogDegree D ^ 10 + alonLogDegree D ^ 6)
      atTop atTop := by
  exact tendsto_atTop_mono' atTop
    (Eventually.of_forall fun D ↦ le_add_of_nonneg_right
      (by positivity : 0 ≤ alonLogDegree D ^ 6))
    ((tendsto_pow_atTop (α := ℝ) (by norm_num)).comp tendsto_alonLogDegree_atTop)

lemma tendsto_alonUpperLowerRealRatio_one :
    Tendsto (fun D : ℕ ↦
      (alonLogDegree D ^ 10 + alonLogDegree D ^ 6) /
        (alonLogDegree D ^ 10 - alonLogDegree D ^ 6)) atTop (nhds 1) := by
  have hrelative := tendsto_alonRelativeError_zero
  have hnumer : Tendsto (fun D : ℕ ↦
      1 + alonLogDegree D ^ 6 / alonLogDegree D ^ 10)
      atTop (nhds 1) := by simpa using tendsto_const_nhds.add hrelative
  have hdenom : Tendsto (fun D : ℕ ↦
      1 - alonLogDegree D ^ 6 / alonLogDegree D ^ 10)
      atTop (nhds 1) := by simpa using tendsto_const_nhds.sub hrelative
  have hquot : Tendsto (fun D : ℕ ↦
      (1 + alonLogDegree D ^ 6 / alonLogDegree D ^ 10) /
        (1 - alonLogDegree D ^ 6 / alonLogDegree D ^ 10)) atTop (nhds 1) := by
    have h := hnumer.div hdenom (by norm_num)
    change Tendsto
      ((fun D : ℕ ↦ 1 + alonLogDegree D ^ 6 / alonLogDegree D ^ 10) /
        (fun D : ℕ ↦ 1 - alonLogDegree D ^ 6 / alonLogDegree D ^ 10))
      atTop (nhds 1)
    simpa using h
  apply hquot.congr'
  filter_upwards [tendsto_alonLogDegree_atTop.eventually_ne_atTop 0] with D hD
  field_simp

lemma tendsto_alonDegreeRatio_one :
    Tendsto (fun D : ℕ ↦ (alonUpperDegree D : ℝ) / (alonLowerDegree D : ℝ))
      atTop (nhds 1) := by
  let lo : ℕ → ℝ := fun D ↦ alonLogDegree D ^ 10 - alonLogDegree D ^ 6
  let hi : ℕ → ℝ := fun D ↦ alonLogDegree D ^ 10 + alonLogDegree D ^ 6
  have hlo : Tendsto lo atTop atTop := tendsto_alonLowerReal_atTop
  have hhi : Tendsto hi atTop atTop := tendsto_alonUpperReal_atTop
  have hceil : Tendsto (fun D : ℕ ↦ (⌈hi D⌉₊ : ℝ) / hi D) atTop (nhds 1) :=
    tendsto_nat_ceil_div_atTop.comp hhi
  have hfloor : Tendsto (fun D : ℕ ↦ (⌊lo D⌋₊ : ℝ) / lo D) atTop (nhds 1) :=
    tendsto_nat_floor_div_atTop.comp hlo
  have hreal : Tendsto (fun D : ℕ ↦ hi D / lo D) atTop (nhds 1) := by
    simpa [lo, hi] using tendsto_alonUpperLowerRealRatio_one
  have hprod := hceil.mul (hreal.mul (hfloor.inv₀ (by norm_num)))
  have hprod' : Tendsto (fun D ↦
      (⌈hi D⌉₊ : ℝ) / hi D *
        (hi D / lo D * ((⌊lo D⌋₊ : ℝ) / lo D)⁻¹)) atTop (nhds 1) := by
    simpa using hprod
  apply hprod'.congr'
  filter_upwards [hlo.eventually_ne_atTop 0, hhi.eventually_ne_atTop 0,
    (tendsto_nat_floor_atTop.comp hlo).eventually_ne_atTop 0] with D hloD hhiD hfloorD
  have hfloorDR : (⌊lo D⌋₊ : ℝ) ≠ 0 := by exact_mod_cast hfloorD
  change (⌈hi D⌉₊ : ℝ) / hi D *
      (hi D / lo D * ((⌊lo D⌋₊ : ℝ) / lo D)⁻¹) =
    (⌈hi D⌉₊ : ℝ) / (⌊lo D⌋₊ : ℝ)
  field_simp [hloD, hhiD, hfloorDR]

lemma tendsto_alonLowerDegree_atTop : Tendsto alonLowerDegree atTop atTop := by
  exact tendsto_nat_floor_atTop.comp tendsto_alonLowerReal_atTop

lemma eventually_alonLowerDegree_pos :
    ∀ᶠ D : ℕ in atTop, 0 < alonLowerDegree D :=
  tendsto_alonLowerDegree_atTop.eventually_gt_atTop 0

lemma eventually_alonLowerDegree_le :
    ∀ᶠ D : ℕ in atTop, alonLowerDegree D ≤ D := by
  have hratio : Tendsto (fun D : ℕ ↦
      alonLogDegree D ^ 10 / (D : ℝ)) atTop (nhds 0) := by
    exact Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hlt := hratio.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hlt, eventually_gt_atTop (0 : ℕ)] with D hD hDpos
  have hpow : alonLogDegree D ^ 10 < (D : ℝ) := by
    rw [div_lt_iff₀ (by exact_mod_cast hDpos)] at hD
    simpa only [one_mul] using hD
  apply Nat.floor_le_of_le
  exact (sub_le_self _ (by positivity)).trans hpow.le

lemma eventually_alonLowerReal_nonneg :
    ∀ᶠ D : ℕ in atTop,
      0 ≤ alonLogDegree D ^ 10 - alonLogDegree D ^ 6 :=
  tendsto_alonLowerReal_atTop.eventually_ge_atTop 0

/-- A real-valued lower-tail estimate implies the rounded natural lower
degree bound used by the peeling recurrence. -/
lemma alonLowerDegree_le_of_abs_sub_lt {D d : ℕ}
    (hlower : 0 ≤ alonLogDegree D ^ 10 - alonLogDegree D ^ 6)
    (hwindow : |(d : ℝ) - alonLogDegree D ^ 10| < alonLogDegree D ^ 6) :
    alonLowerDegree D ≤ d := by
  have hlowerReal : alonLogDegree D ^ 10 - alonLogDegree D ^ 6 < (d : ℝ) := by
    have := (abs_lt.mp hwindow).1
    linarith
  have hfloor : (alonLowerDegree D : ℝ) ≤
      alonLogDegree D ^ 10 - alonLogDegree D ^ 6 := by
    exact Nat.floor_le hlower
  exact_mod_cast hfloor.trans hlowerReal.le

/-- The same real window implies the rounded natural upper degree bound. -/
lemma le_alonUpperDegree_of_abs_sub_lt {D d : ℕ}
    (hwindow : |(d : ℝ) - alonLogDegree D ^ 10| < alonLogDegree D ^ 6) :
    d ≤ alonUpperDegree D := by
  have hupperReal : (d : ℝ) <
      alonLogDegree D ^ 10 + alonLogDegree D ^ 6 := by
    have := (abs_lt.mp hwindow).2
    linarith
  have hlt : (d : ℝ) < (alonUpperDegree D : ℝ) :=
    hupperReal.trans_le (Nat.le_ceil _)
  have : d < alonUpperDegree D := by exact_mod_cast hlt
  exact this.le

lemma tendsto_id_div_log_atTop :
    Tendsto (fun x : ℝ ↦ x / Real.log x) atTop atTop := by
  have hzero : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < Real.log x / x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (Real.log_pos hx) (by linarith)
  have hwithin : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  apply hwithin.inv_tendsto_nhdsGT_zero.congr'
  filter_upwards [hpos] with x hx
  simp only [Pi.inv_apply]
  rw [inv_div]

lemma tendsto_alonGirthArgument_atTop :
    Tendsto (fun D : ℕ ↦
      alonLogDegree D / (20 * Real.log (alonLogDegree D))) atTop atTop := by
  have hcomp : Tendsto (fun D : ℕ ↦
      alonLogDegree D / Real.log (alonLogDegree D)) atTop atTop := by
    exact (tendsto_id_div_log_atTop.comp tendsto_alonLogDegree_atTop).congr
      (fun _ ↦ rfl)
  apply (hcomp.atTop_div_const (by norm_num : (0 : ℝ) < 20)).congr'
  filter_upwards [tendsto_alonLogDegree_atTop.eventually_ne_atTop 0,
    (Real.tendsto_log_atTop.comp tendsto_alonLogDegree_atTop).eventually_ne_atTop 0]
      with D hD hlogD
  field_simp

lemma tendsto_alonGirthScale_atTop :
    Tendsto (fun D : ℕ ↦ (alonGirthScale D : ℝ)) atTop atTop := by
  have hfloorNat : Tendsto (fun D : ℕ ↦
      ⌊alonLogDegree D / (20 * Real.log (alonLogDegree D))⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp tendsto_alonGirthArgument_atTop
  have hcast : Tendsto (fun D : ℕ ↦
      (⌊alonLogDegree D / (20 * Real.log (alonLogDegree D))⌋₊ : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hfloorNat
  simpa only [alonGirthScale, Nat.cast_add, Nat.cast_one] using
    tendsto_atTop_add_const_right atTop 1 hcast

lemma tendsto_alonGirthScale_inv_zero :
    Tendsto (fun D : ℕ ↦ 1 / (alonGirthScale D : ℝ)) atTop (nhds 0) := by
  have h := tendsto_alonGirthScale_atTop.inv_tendsto_atTop
  apply h.congr'
  exact Eventually.of_forall fun _ ↦ by simp only [one_div, Pi.inv_apply]

/-! The concrete LLL invocation also needs the logarithmic cutoff to be
negligible compared with `sqrt D`, not merely compared with the selected
degree.  These estimates are stated separately so that the eventual
parameter package below contains every scalar side condition of the sparse
extractor. -/

lemma tendsto_alonLogDegree_div_sqrt_zero :
    Tendsto (fun D : ℕ ↦ alonLogDegree D / Real.sqrt D)
      atTop (nhds 0) := by
  have hsqrt : Tendsto (fun D : ℕ ↦ Real.sqrt (D : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hbase : Tendsto (fun D : ℕ ↦
      Real.log (Real.sqrt (D : ℝ)) / Real.sqrt (D : ℝ))
      atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hsqrt
  have htwice := hbase.const_mul 2
  simpa only [mul_zero] using htwice.congr' (by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with D hD
    have hDR : (0 : ℝ) ≤ D := by positivity
    rw [Real.log_sqrt hDR]
    simp only [alonLogDegree]
    ring)

lemma eventually_alonGirthScale_le_log_add_one :
    ∀ᶠ D : ℕ in atTop,
      (alonGirthScale D : ℝ) ≤ alonLogDegree D + 1 := by
  have hloglog : Tendsto (fun D : ℕ ↦ Real.log (alonLogDegree D))
      atTop atTop := Real.tendsto_log_atTop.comp tendsto_alonLogDegree_atTop
  filter_upwards [tendsto_alonLogDegree_atTop.eventually_ge_atTop 0,
    hloglog.eventually_ge_atTop (1 / 20 : ℝ)] with D hlog hloglogD
  have hdenom : (1 : ℝ) ≤ 20 * Real.log (alonLogDegree D) := by
    nlinarith
  have hargNonneg : 0 ≤
      alonLogDegree D / (20 * Real.log (alonLogDegree D)) :=
    div_nonneg hlog (zero_le_one.trans hdenom)
  have hfloor :
      (⌊alonLogDegree D / (20 * Real.log (alonLogDegree D))⌋₊ : ℝ) ≤
        alonLogDegree D / (20 * Real.log (alonLogDegree D)) :=
    Nat.floor_le hargNonneg
  calc
    (alonGirthScale D : ℝ) =
        (⌊alonLogDegree D / (20 * Real.log (alonLogDegree D))⌋₊ : ℝ) + 1 := by
      simp only [alonGirthScale, Nat.cast_add, Nat.cast_one]
    _ ≤ alonLogDegree D / (20 * Real.log (alonLogDegree D)) + 1 :=
      by simpa only [add_comm] using add_le_add_right hfloor 1
    _ ≤ alonLogDegree D + 1 := by
      gcongr
      exact div_le_self hlog hdenom

lemma tendsto_alonGirthScale_div_sqrt_zero :
    Tendsto (fun D : ℕ ↦ (alonGirthScale D : ℝ) / Real.sqrt D)
      atTop (nhds 0) := by
  have hsqrt : Tendsto (fun D : ℕ ↦ Real.sqrt (D : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinvSqrt : Tendsto (fun D : ℕ ↦ 1 / Real.sqrt (D : ℝ))
      atTop (nhds 0) := by
    have h := hsqrt.inv_tendsto_atTop
    apply h.congr'
    exact Eventually.of_forall fun _ ↦ by simp only [one_div, Pi.inv_apply]
  have hupper : Tendsto (fun D : ℕ ↦
      (alonLogDegree D + 1) / Real.sqrt D) atTop (nhds 0) := by
    have hadd := tendsto_alonLogDegree_div_sqrt_zero.add hinvSqrt
    simpa only [add_zero] using hadd.congr' (by
      filter_upwards with D
      ring)
  apply squeeze_zero'
  · exact Eventually.of_forall fun D ↦ by positivity
  · filter_upwards [eventually_alonGirthScale_le_log_add_one,
      eventually_gt_atTop (0 : ℕ)] with D hscale hD
    exact div_le_div_of_nonneg_right hscale (Real.sqrt_nonneg _)
  · exact hupper

lemma eventually_alonMeanDegree_le_degree :
    ∀ᶠ D : ℕ in atTop, alonLogDegree D ^ 10 ≤ (D : ℝ) := by
  have hratio : Tendsto (fun D : ℕ ↦
      alonLogDegree D ^ 10 / (D : ℝ)) atTop (nhds 0) := by
    exact Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hlt := hratio.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hlt, eventually_gt_atTop (0 : ℕ)] with D hD hDpos
  rw [div_lt_iff₀ (by exact_mod_cast hDpos)] at hD
  simpa only [one_mul] using hD.le

/-! ## Scalar cost of grouping the degree-two factors

`HighGirthLinear.exists_grouped_decomposition` groups `k` degree-two factors
in blocks of `q` and uses `(k / q + 1) * (q + 1)` forests.  Here `k` is the
rounded half upper degree and `q` is one hundredth of the available girth.
The next limit calculation includes both divisions and all additive rounding
terms; its endpoint is exactly the relative budget required by
`RegularBlockSelection`. -/

def alonFactorCount (D : ℕ) : ℕ := ⌈(alonUpperDegree D : ℝ) / 2⌉₊

def alonGroupSize (D : ℕ) : ℕ := alonGirthScale D / 100

def alonGroupedCost (D : ℕ) : ℕ :=
  (alonFactorCount D / alonGroupSize D + 1) * (alonGroupSize D + 1)

lemma tendsto_alonUpperDegree_atTop :
    Tendsto alonUpperDegree atTop atTop := by
  exact tendsto_nat_ceil_atTop.comp tendsto_alonUpperReal_atTop

lemma tendsto_alonFactorCount_atTop :
    Tendsto alonFactorCount atTop atTop := by
  apply tendsto_nat_ceil_atTop.comp
  exact (tendsto_natCast_atTop_atTop.comp tendsto_alonUpperDegree_atTop).atTop_div_const
    (by norm_num)

lemma tendsto_alonGroupSize_atTop :
    Tendsto alonGroupSize atTop atTop := by
  exact (Nat.tendsto_div_const_atTop (by norm_num)).comp
    ((tendsto_natCast_atTop_iff).mp tendsto_alonGirthScale_atTop)

lemma eventually_alonFactorCount_pos :
    ∀ᶠ D : ℕ in atTop, 0 < alonFactorCount D :=
  tendsto_alonFactorCount_atTop.eventually_gt_atTop 0

lemma eventually_alonGroupSize_pos :
    ∀ᶠ D : ℕ in atTop, 0 < alonGroupSize D :=
  tendsto_alonGroupSize_atTop.eventually_gt_atTop 0

lemma alonUpperDegree_le_two_mul_factorCount (D : ℕ) :
    alonUpperDegree D ≤ 2 * alonFactorCount D := by
  have h : (alonUpperDegree D : ℝ) / 2 ≤ (alonFactorCount D : ℝ) :=
    Nat.le_ceil _
  simpa [Nat.mul_comm] using
    (by exact_mod_cast ((div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp h) :
      alonUpperDegree D ≤ alonFactorCount D * 2)

lemma alonGroupSize_girth (D : ℕ) :
    100 * alonGroupSize D ≤ alonGirthScale D := by
  exact Nat.mul_div_le _ _

lemma tendsto_alonFactorCount_div_lower :
    Tendsto (fun D : ℕ ↦
      (alonFactorCount D : ℝ) / (alonLowerDegree D : ℝ)) atTop (nhds (1 / 2)) := by
  have hUpperCast : Tendsto (fun D : ℕ ↦ (alonUpperDegree D : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_alonUpperDegree_atTop
  have hhalfTop : Tendsto (fun D : ℕ ↦ (alonUpperDegree D : ℝ) / 2) atTop atTop :=
    hUpperCast.atTop_div_const (by norm_num)
  have hceilRatio : Tendsto (fun D : ℕ ↦
      (alonFactorCount D : ℝ) / ((alonUpperDegree D : ℝ) / 2)) atTop (nhds 1) :=
    tendsto_nat_ceil_div_atTop.comp hhalfTop
  have hUpperLower : Tendsto (fun D : ℕ ↦
      (alonUpperDegree D : ℝ) / (alonLowerDegree D : ℝ)) atTop (nhds 1) :=
    tendsto_alonDegreeRatio_one
  have hprod := hceilRatio.mul (hUpperLower.div_const 2)
  have hprod' : Tendsto (fun D : ℕ ↦
      ((alonFactorCount D : ℝ) / ((alonUpperDegree D : ℝ) / 2)) *
        (((alonUpperDegree D : ℝ) / (alonLowerDegree D : ℝ)) / 2))
      atTop (nhds (1 / 2)) := by simpa using hprod
  apply hprod'.congr'
  filter_upwards [tendsto_alonUpperDegree_atTop.eventually_ne_atTop 0] with D hU
  have hUR : (alonUpperDegree D : ℝ) ≠ 0 := by exact_mod_cast hU
  field_simp [hUR]

lemma tendsto_alonLogDegree_div_upper_zero :
    Tendsto (fun D : ℕ ↦
      alonLogDegree D / (alonUpperDegree D : ℝ)) atTop (nhds 0) := by
  have hright : Tendsto (fun D : ℕ ↦ 1 / alonLogDegree D ^ 9)
      atTop (nhds 0) := by
    have hpow : Tendsto (fun D : ℕ ↦ alonLogDegree D ^ 9) atTop atTop :=
      (tendsto_pow_atTop (α := ℝ) (by norm_num)).comp tendsto_alonLogDegree_atTop
    have h := hpow.inv_tendsto_atTop
    apply h.congr'
    exact Eventually.of_forall fun _ ↦ by simp only [one_div, Pi.inv_apply]
  apply squeeze_zero'
  · filter_upwards [tendsto_alonLogDegree_atTop.eventually_ge_atTop 1] with D hD
    positivity
  · filter_upwards [tendsto_alonLogDegree_atTop.eventually_ge_atTop 1] with D hD
    have hdenom : alonLogDegree D ^ 10 ≤ (alonUpperDegree D : ℝ) := by
      exact (le_add_of_nonneg_right (by positivity)).trans (Nat.le_ceil _)
    calc
      alonLogDegree D / (alonUpperDegree D : ℝ) ≤
          alonLogDegree D / alonLogDegree D ^ 10 :=
        div_le_div_of_nonneg_left (zero_le_one.trans hD)
          (pow_pos (by positivity) _) hdenom
      _ = 1 / alonLogDegree D ^ 9 := by
        field_simp [ne_of_gt (by positivity : 0 < alonLogDegree D)]
  · exact hright

lemma tendsto_alonLogDegree_div_lower_zero :
    Tendsto (fun D : ℕ ↦
      alonLogDegree D / (alonLowerDegree D : ℝ)) atTop (nhds 0) := by
  have hprod := tendsto_alonLogDegree_div_upper_zero.mul tendsto_alonDegreeRatio_one
  have hprod' : Tendsto (fun D : ℕ ↦
      (alonLogDegree D / (alonUpperDegree D : ℝ)) *
        ((alonUpperDegree D : ℝ) / (alonLowerDegree D : ℝ))) atTop (nhds 0) := by
    simpa using hprod
  apply hprod'.congr'
  filter_upwards [tendsto_alonUpperDegree_atTop.eventually_ne_atTop 0] with D hU
  have hUR : (alonUpperDegree D : ℝ) ≠ 0 := by exact_mod_cast hU
  field_simp [hUR]

lemma tendsto_alonGirthArgument_div_lower_zero :
    Tendsto (fun D : ℕ ↦
      (alonLogDegree D / (20 * Real.log (alonLogDegree D))) /
        (alonLowerDegree D : ℝ)) atTop (nhds 0) := by
  have hdenom : Tendsto (fun D : ℕ ↦ 20 * Real.log (alonLogDegree D)) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_alonLogDegree_atTop).const_mul_atTop
      (by norm_num)
  have hdiv := Tendsto.div_atTop tendsto_alonLogDegree_div_lower_zero hdenom
  apply hdiv.congr'
  filter_upwards [hdenom.eventually_ne_atTop 0,
    tendsto_alonLowerDegree_atTop.eventually_ne_atTop 0] with D hdenomD hlowerD
  have hlowerR : (alonLowerDegree D : ℝ) ≠ 0 := by exact_mod_cast hlowerD
  field_simp [hdenomD, hlowerR]

lemma tendsto_alonGirthScale_div_lower_zero :
    Tendsto (fun D : ℕ ↦
      (alonGirthScale D : ℝ) / (alonLowerDegree D : ℝ)) atTop (nhds 0) := by
  let A : ℕ → ℝ := fun D ↦
    alonLogDegree D / (20 * Real.log (alonLogDegree D))
  have hA : Tendsto A atTop atTop := tendsto_alonGirthArgument_atTop
  have hfloorRatio : Tendsto (fun D : ℕ ↦ (⌊A D⌋₊ : ℝ) / A D)
      atTop (nhds 1) := tendsto_nat_floor_div_atTop.comp hA
  have hinvA : Tendsto (fun D : ℕ ↦ 1 / A D) atTop (nhds 0) := by
    have h := hA.inv_tendsto_atTop
    apply h.congr'
    exact Eventually.of_forall fun _ ↦ by simp only [one_div, Pi.inv_apply]
  have hgA : Tendsto (fun D : ℕ ↦ (alonGirthScale D : ℝ) / A D)
      atTop (nhds 1) := by
    have hsum := hfloorRatio.add hinvA
    have hsum' : Tendsto (fun D : ℕ ↦ (⌊A D⌋₊ : ℝ) / A D + 1 / A D)
        atTop (nhds 1) := by simpa using hsum
    apply hsum'.congr'
    filter_upwards [hA.eventually_ne_atTop 0] with D hAD
    simp only [alonGirthScale, Nat.cast_add, Nat.cast_one, A]
    field_simp [hAD]
  have hAdivLower : Tendsto (fun D : ℕ ↦ A D / (alonLowerDegree D : ℝ))
      atTop (nhds 0) := by
    simpa [A] using tendsto_alonGirthArgument_div_lower_zero
  have hprod := hgA.mul hAdivLower
  have hprod' : Tendsto (fun D : ℕ ↦
      ((alonGirthScale D : ℝ) / A D) *
        (A D / (alonLowerDegree D : ℝ))) atTop (nhds 0) := by simpa using hprod
  apply hprod'.congr'
  filter_upwards [hA.eventually_ne_atTop 0] with D hAD
  field_simp [hAD]

lemma tendsto_alonGroupSize_div_lower_zero :
    Tendsto (fun D : ℕ ↦
      (alonGroupSize D : ℝ) / (alonLowerDegree D : ℝ)) atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_ tendsto_alonGirthScale_div_lower_zero
  · exact Eventually.of_forall fun _ ↦ by positivity
  · exact Eventually.of_forall fun D ↦ by
      exact div_le_div_of_nonneg_right
        (by
          have hnat : alonGroupSize D ≤ alonGirthScale D := by
            exact Nat.div_le_self _ _
          exact_mod_cast hnat)
        (by positivity)

lemma tendsto_alonFactorQuotient_div_lower_zero :
    Tendsto (fun D : ℕ ↦
      (alonFactorCount D / alonGroupSize D : ℕ) / (alonLowerDegree D : ℝ))
      atTop (nhds 0) := by
  have hqCast : Tendsto (fun D : ℕ ↦ (alonGroupSize D : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_alonGroupSize_atTop
  have hqInv : Tendsto (fun D : ℕ ↦ 1 / (alonGroupSize D : ℝ))
      atTop (nhds 0) := by
    have h := hqCast.inv_tendsto_atTop
    apply h.congr'
    exact Eventually.of_forall fun _ ↦ by simp only [one_div, Pi.inv_apply]
  have hupper := tendsto_alonFactorCount_div_lower.mul hqInv
  have hupper' : Tendsto (fun D : ℕ ↦
      ((alonFactorCount D : ℝ) / (alonLowerDegree D : ℝ)) *
        (1 / (alonGroupSize D : ℝ))) atTop (nhds 0) := by simpa using hupper
  refine squeeze_zero' ?_ ?_ hupper'
  · exact Eventually.of_forall fun _ ↦ by positivity
  · filter_upwards [eventually_alonLowerDegree_pos,
      eventually_alonGroupSize_pos] with D hL hq
    have hdiv : ((alonFactorCount D / alonGroupSize D : ℕ) : ℝ) ≤
        (alonFactorCount D : ℝ) / (alonGroupSize D : ℝ) := Nat.cast_div_le
    have hLR : (0 : ℝ) < alonLowerDegree D := by exact_mod_cast hL
    have hqR : (alonGroupSize D : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    calc
      ((alonFactorCount D / alonGroupSize D : ℕ) : ℝ) /
          (alonLowerDegree D : ℝ) ≤
        ((alonFactorCount D : ℝ) / (alonGroupSize D : ℝ)) /
          (alonLowerDegree D : ℝ) :=
        div_le_div_of_nonneg_right hdiv hLR.le
      _ = ((alonFactorCount D : ℝ) / (alonLowerDegree D : ℝ)) *
          (1 / (alonGroupSize D : ℝ)) := by field_simp [hqR]

lemma tendsto_alonGroupedResidual_div_lower_zero :
    Tendsto (fun D : ℕ ↦
      ((alonFactorCount D / alonGroupSize D : ℕ) + alonGroupSize D + 1 : ℕ) /
        (alonLowerDegree D : ℝ)) atTop (nhds 0) := by
  have hLcast : Tendsto (fun D : ℕ ↦ (alonLowerDegree D : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_alonLowerDegree_atTop
  have hinvL : Tendsto (fun D : ℕ ↦ 1 / (alonLowerDegree D : ℝ))
      atTop (nhds 0) := by
    have h := hLcast.inv_tendsto_atTop
    apply h.congr'
    exact Eventually.of_forall fun _ ↦ by simp only [one_div, Pi.inv_apply]
  have hsum := tendsto_alonFactorQuotient_div_lower_zero.add
    (tendsto_alonGroupSize_div_lower_zero.add hinvL)
  have hsum' : Tendsto (fun D : ℕ ↦
      ((alonFactorCount D / alonGroupSize D : ℕ) : ℝ) /
          (alonLowerDegree D : ℝ) +
        ((alonGroupSize D : ℝ) / (alonLowerDegree D : ℝ) +
          1 / (alonLowerDegree D : ℝ))) atTop (nhds 0) := by simpa using hsum
  apply hsum'.congr'
  filter_upwards [eventually_alonLowerDegree_pos] with D hL
  have hLR : (alonLowerDegree D : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  push_cast
  field_simp [hLR]
  ring

lemma alonGroupedCost_le (D : ℕ) :
    alonGroupedCost D ≤ alonFactorCount D +
      (alonFactorCount D / alonGroupSize D + alonGroupSize D + 1) := by
  unfold alonGroupedCost
  have h := Nat.div_mul_le_self (alonFactorCount D) (alonGroupSize D)
  calc
    (alonFactorCount D / alonGroupSize D + 1) * (alonGroupSize D + 1) =
        (alonFactorCount D / alonGroupSize D) * alonGroupSize D +
          alonFactorCount D / alonGroupSize D + alonGroupSize D + 1 := by ring
    _ ≤ alonFactorCount D +
          alonFactorCount D / alonGroupSize D + alonGroupSize D + 1 := by omega
    _ = alonFactorCount D +
        (alonFactorCount D / alonGroupSize D + alonGroupSize D + 1) := by omega

theorem eventually_alonGroupedCost_le {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ D : ℕ in atTop,
      (alonGroupedCost D : ℝ) ≤
        (1 + eta) * (alonLowerDegree D : ℝ) / 2 := by
  have hsum := tendsto_alonFactorCount_div_lower.add
    tendsto_alonGroupedResidual_div_lower_zero
  have hsum' : Tendsto (fun D : ℕ ↦
      (alonFactorCount D : ℝ) / (alonLowerDegree D : ℝ) +
        ((alonFactorCount D / alonGroupSize D : ℕ) + alonGroupSize D + 1 : ℕ) /
          (alonLowerDegree D : ℝ)) atTop (nhds (1 / 2)) := by simpa using hsum
  have hlt := hsum'.eventually_lt_const
    (by linarith : (1 / 2 : ℝ) < (1 + eta) / 2)
  filter_upwards [hlt, eventually_alonLowerDegree_pos] with D hD hL
  have hcost : (alonGroupedCost D : ℝ) ≤
      (alonFactorCount D : ℝ) +
        ((alonFactorCount D / alonGroupSize D : ℕ) + alonGroupSize D + 1 : ℕ) := by
    exact_mod_cast alonGroupedCost_le D
  have hLR : (0 : ℝ) < alonLowerDegree D := by exact_mod_cast hL
  have hdiv : (alonGroupedCost D : ℝ) / (alonLowerDegree D : ℝ) <
      (1 + eta) / 2 := by
    exact (div_le_div_of_nonneg_right hcost hLR.le).trans_lt (by
      convert hD using 1 <;> field_simp)
  calc
    (alonGroupedCost D : ℝ) ≤ ((1 + eta) / 2) * (alonLowerDegree D : ℝ) :=
      ((div_lt_iff₀ hLR).mp hdiv).le
    _ = (1 + eta) * (alonLowerDegree D : ℝ) / 2 := by ring

/-! ## Exact integration boundary for the sparse extractor -/

/-- The graph-theoretic statement delivered by the finite local-lemma
construction: an eventual spanning subgraph with the concrete rounded degree
window and extended girth. -/
def EventualAlonSparseBlockSelection : Prop :=
  ∀ᶠ D : ℕ in atTop,
    ∀ (W : Type u) [Fintype W] (G : SimpleGraph W) [DecidableRel G.Adj],
      (∀ v, (G.neighborSet v).ncard = D) →
      ∃ H : SimpleGraph W,
        H ≤ G ∧ ((alonGirthScale D : ℕ) : ℕ∞) ≤ H.egirth ∧
          ∀ v, alonLowerDegree D ≤ H.degree v ∧
            H.degree v ≤ alonUpperDegree D

/-- The concrete sparse-block statement and the checked grouped high-girth
decomposition supply every regular peeling step. -/
theorem hasRegularPeelingSteps_of_eventualAlonSparseBlockSelection
    (hsparse : EventualAlonSparseBlockSelection.{u}) :
    HasRegularPeelingSteps.{u} := by
  intro eta heta
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.1
    (hsparse.and <| (eventually_alonGroupedCost_le heta).and <|
      eventually_alonLowerDegree_pos.and <|
        eventually_alonLowerDegree_le.and <|
          eventually_alonFactorCount_pos.and eventually_alonGroupSize_pos)
  refine ⟨threshold, regularPeelingStep_of_blockSelection ?_⟩
  intro W _ G _ D hD hregular
  obtain ⟨H, hHG, hegirth, hdegree⟩ := (hthreshold D hD.le).1 W G hregular
  let k := alonFactorCount D
  let q := alonGroupSize D
  have hdegreek : ∀ v, H.degree v ≤ 2 * k := by
    intro v
    exact (hdegree v).2.trans (alonUpperDegree_le_two_mul_factorCount D)
  have hegirthq : (((100 * q : ℕ) : ℕ∞)) ≤ H.egirth := by
    apply le_trans ?_ hegirth
    exact_mod_cast alonGroupSize_girth D
  obtain ⟨d⟩ := HighGirthLinear.exists_grouped_decomposition H
    (hthreshold D hD.le).2.2.2.2.1 (hthreshold D hD.le).2.2.2.2.2
    hdegreek hegirthq
  refine ⟨H, alonLowerDegree D, alonGroupedCost D, hHG,
    (hthreshold D hD.le).2.2.1, (hthreshold D hD.le).2.2.2.1, ?_,
    ⟨Cover.ofDecomposition d⟩, (hthreshold D hD.le).2.1⟩
  intro v
  simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset_def,
    Set.ncard_eq_toFinset_card'] using (hdegree v).1

/-! ## The finite induction -/

/-- The recurrence behind Alon's proof.  Notice that the induction is on the
declared degree bound `D`, not on a graph-dependent maximum operation. -/
theorem PeelingData.exists_cover_bound {eta : ℝ} (p : PeelingData.{u} eta)
    (heta : 0 ≤ eta) (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ)
    (hdegree : ∀ v, (G.neighborSet v).ncard ≤ D) :
    ∃ k : ℕ, Nonempty (Cover G k) ∧
      (k : ℝ) ≤ (1 + eta) * (D : ℝ) / 2 + p.baseCost := by
  induction D using Nat.strong_induction_on generalizing V G with
  | h D ih =>
      by_cases hsmall : D ≤ p.threshold
      · obtain ⟨k, ⟨ck⟩, hk⟩ := p.base V G D hsmall hdegree
        refine ⟨k, ⟨ck⟩, ?_⟩
        have hkR : (k : ℝ) ≤ p.baseCost := by exact_mod_cast hk
        have hDnonneg : (0 : ℝ) ≤ D := by positivity
        have hfactor : 0 ≤ 1 + eta := by linarith
        exact hkR.trans (le_add_of_nonneg_left
          (div_nonneg (mul_nonneg hfactor hDnonneg) (by norm_num)))
      · have hlarge : p.threshold < D := Nat.lt_of_not_ge hsmall
        letI : DecidableRel G.Adj := Classical.decRel G.Adj
        have hdegree' : ∀ v, G.degree v ≤ D := by
          intro v
          simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset_def,
            Set.ncard_eq_toFinset_card'] using hdegree v
        let C := GraphRegularCompletion.completion G D hdegree'
        letI : DecidableRel C.Adj := Classical.decRel C.Adj
        let f : G ↪g C :=
          GraphRegularCompletion.originalGraphEmbedding G D hdegree'
        have hregular : ∀ v, (C.neighborSet v).ncard = D := by
          intro v
          simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset_def,
            Set.ncard_eq_toFinset_card'] using
              GraphRegularCompletion.degree_completion G D hdegree' v
        obtain ⟨H, R, q, m, hHC, hRC, hcover, hqpos, hqD, hRdegree,
          ⟨cH⟩, hm⟩ := p.step _ C D hlarge hregular
        have hsub : D - q < D := Nat.sub_lt (Nat.zero_lt_of_lt hlarge) hqpos
        letI : DecidableRel R.Adj := Classical.decRel R.Adj
        obtain ⟨k, ⟨cR⟩, hk⟩ := ih (D - q) hsub R hRdegree
        let cC : Cover C (m + k) := Cover.add hHC hRC hcover cH cR
        refine ⟨m + k, ⟨Cover.pullback f cC⟩, ?_⟩
        have hcastSub : ((D - q : ℕ) : ℝ) = (D : ℝ) - (q : ℝ) := by
          rw [Nat.cast_sub hqD]
        rw [Nat.cast_add]
        rw [hcastSub] at hk
        calc
          (m : ℝ) + (k : ℝ) ≤
              (1 + eta) * (q : ℝ) / 2 +
                ((1 + eta) * ((D : ℝ) - (q : ℝ)) / 2 + p.baseCost) :=
            add_le_add hm hk
          _ = (1 + eta) * (D : ℝ) / 2 + p.baseCost := by ring

/-! ## Absorbing the bounded-degree endpoint -/

/-- A concrete threshold which absorbs an additive natural-number cost into
half of a prescribed positive relative error. -/
def absorptionThreshold (epsilon : ℝ) (c : ℕ) : ℕ :=
  ⌈(4 * (c : ℝ)) / epsilon⌉₊

lemma baseCost_le_quarter_epsilon_mul_degree {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (c D : ℕ)
    (hD : absorptionThreshold epsilon c ≤ D) :
    (c : ℝ) ≤ epsilon * (D : ℝ) / 4 := by
  have hceil : (4 * (c : ℝ)) / epsilon ≤
      (absorptionThreshold epsilon c : ℝ) := by
    exact Nat.le_ceil ((4 * (c : ℝ)) / epsilon)
  have hthreshold : (4 * (c : ℝ)) / epsilon ≤ (D : ℝ) :=
    hceil.trans (by exact_mod_cast hD)
  have := (div_le_iff₀ hepsilon).mp hthreshold
  nlinarith

/-- The complete scalar endpoint: the finite recurrence with error
`epsilon / 2` and bounded base cost satisfies the target coefficient
`(1 + epsilon) / 2` once the degree is above the explicit threshold. -/
theorem PeelingData.exists_decomposition_epsilon
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (p : PeelingData.{u} (epsilon / 2))
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ)
    (hD : absorptionThreshold epsilon p.baseCost ≤ D)
    (hDtwo : 2 ≤ D)
    (hdegree : ∀ v, (G.neighborSet v).ncard ≤ D) :
    ∃ k : ℕ, 0 < k ∧
      (k : ℝ) ≤ (1 + epsilon) * (D : ℝ) / 2 ∧
      Nonempty (Decomposition G k) := by
  obtain ⟨k, ⟨ck⟩, hk⟩ := p.exists_cover_bound (by positivity) G D hdegree
  have hc := baseCost_le_quarter_epsilon_mul_degree hepsilon p.baseCost D hD
  have hbound : (k : ℝ) ≤ (1 + epsilon) * (D : ℝ) / 2 := by
    calc
      (k : ℝ) ≤ (1 + epsilon / 2) * (D : ℝ) / 2 + p.baseCost := hk
      _ ≤ (1 + epsilon / 2) * (D : ℝ) / 2 + epsilon * (D : ℝ) / 4 :=
        by linarith
      _ = (1 + epsilon) * (D : ℝ) / 2 := by ring
  by_cases hkzero : k = 0
  · have hGbot : G = ⊥ := by
      apply le_bot_iff.mp
      intro v w hvw
      let e : G.edgeSet := ⟨s(v, w), hvw⟩
      exact Fin.elim0 (hkzero ▸ ck.locate e)
    subst G
    refine ⟨1, Nat.zero_lt_succ 0, ?_, ⟨?_⟩⟩
    · have hDtwoR : (2 : ℝ) ≤ D := by exact_mod_cast hDtwo
      nlinarith
    · exact {
        color := fun _ ↦ 0
        linear := fun i ↦
          Erdos622.SimpleGraph.IsLinearForest.anti
            (colorGraph_le (fun _ ↦ 0) i)
            Erdos622.SimpleGraph.isLinearForest_bot }
  · exact ⟨k, Nat.pos_of_ne_zero hkzero, hbound, ⟨ck.toDecomposition⟩⟩

/-- The peeling theorem implies the exact uniform asymptotic linear-arboricity
interface used elsewhere in the Erdős 622 development. -/
theorem asymptoticLinearArboricity_of_hasPeelingData
    (hpeel : HasPeelingData.{u}) : AsymptoticLinearArboricity.{u} := by
  intro epsilon hepsilon
  let p : PeelingData.{u} (epsilon / 2) :=
    Classical.choice (hpeel (epsilon / 2) (by positivity))
  refine ⟨max (absorptionThreshold epsilon p.baseCost) 2, ?_⟩
  intro W _ G _ D hD hdegree
  have hdegree' : ∀ v, (G.neighborSet v).ncard ≤ D := by
    intro v
    rw [Set.ncard_eq_toFinset_card']
    exact hdegree v
  exact p.exists_decomposition_epsilon hepsilon G D
    ((le_max_left _ _).trans hD) ((le_max_right _ _).trans hD) hdegree'

/-- Checked deterministic reduction from the two concrete high-girth
theorems, packaged as regular peeling steps, to asymptotic linear
arboricity for all finite simple graphs. -/
theorem asymptoticLinearArboricity_of_regularPeelingSteps
    (hstep : HasRegularPeelingSteps.{u}) : AsymptoticLinearArboricity.{u} := by
  apply asymptoticLinearArboricity_of_hasPeelingData
  intro eta heta
  obtain ⟨threshold, hthreshold⟩ := hstep eta heta
  exact ⟨PeelingData.ofRegularStep eta threshold hthreshold⟩

/-- The final deterministic composition specialized to the exact output of
the sparse high-girth extractor. -/
theorem asymptoticLinearArboricity_of_eventualAlonSparseBlockSelection
    (hsparse : EventualAlonSparseBlockSelection.{u}) :
    AsymptoticLinearArboricity.{u} :=
  asymptoticLinearArboricity_of_regularPeelingSteps
    (hasRegularPeelingSteps_of_eventualAlonSparseBlockSelection hsparse)

/-! ## Unconditional Alon bound -/

/-- The checked probabilistic sparse-subgraph theorem has exactly the
integral window required by the deterministic peeling reduction. -/
theorem eventualAlonSparseBlockSelection :
    EventualAlonSparseBlockSelection.{u} := by
  have hsparse : ∀ᶠ D : ℕ in atTop,
      ∀ (W : Type u) [Fintype W] (G : SimpleGraph W),
        G.IsRegularOfDegree D →
          ∃ H ≤ G,
            (((⌊Real.log (D : ℝ) /
                (20 * Real.log (Real.log (D : ℝ)))⌋₊ + 1 : ℕ) : ℕ∞) ≤
                H.egirth ∧
              ∀ v,
                ⌊Real.log (D : ℝ) ^ 10 - Real.log (D : ℝ) ^ 6⌋₊ ≤
                    H.degree v ∧
                  H.degree v ≤
                    ⌈Real.log (D : ℝ) ^ 10 + Real.log (D : ℝ) ^ 6⌉₊) :=
    AlonSparseSubgraph.eventually_exists_alon_sparse_subgraph
  filter_upwards [hsparse] with D hD
  intro W _ G _ hregular
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hreg : G.IsRegularOfDegree D := by
    intro v
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset_def,
      Set.ncard_eq_toFinset_card'] using hregular v
  obtain ⟨H, hHG, hegirth, hdegree⟩ := hD W G hreg
  refine ⟨H, hHG, ?_, ?_⟩
  · simpa only [alonGirthScale, alonLogDegree] using hegirth
  · intro v
    simpa only [alonLowerDegree, alonUpperDegree, alonLogDegree] using hdegree v

/-- Alon's unconditional asymptotic linear-arboricity theorem, in the exact
uniform interface consumed by the Erdős 622 counting argument. -/
theorem alon_asymptoticLinearArboricity :
    LinearArboricity.AsymptoticLinearArboricity.{u} :=
  asymptoticLinearArboricity_of_eventualAlonSparseBlockSelection
    eventualAlonSparseBlockSelection

#print axioms alon_asymptoticLinearArboricity

end

end AlonInduction
end Erdos622
