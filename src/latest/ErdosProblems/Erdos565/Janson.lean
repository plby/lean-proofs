import ErdosProblems.Erdos565.Hypergraph
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Weighted Janson parameters for finite hypergraphs

This file contains the deterministic algebra surrounding the Janson parameter used in the
proof of Erdős Problem 565.  An `EdgeWeight H` is represented by a nonnegative function on all
finite vertex sets; only its values on the edges of `H` are observed.  This representation makes
extension by zero to a larger hypergraph completely explicit.

The convention at radius `R = 0` is part of the definition: every hypergraph is
`(p, 0)`-Janson.
-/

namespace Erdos565
namespace Hypergraph

variable {V : Type*} [DecidableEq V]

/-- A nonnegative weight on the edges of `H`.

Values away from `H` are ignored by all observables below.  This is equivalent to a function on
the subtype of edges, while avoiding repeated subtype transports when hypergraphs are enlarged.
-/
abbrev EdgeWeight (_H : Hypergraph V) := Finset V → NNReal

/-- Total mass of an edge weight. -/
def mass (H : Hypergraph V) (ν : EdgeWeight H) : ℝ :=
  ∑ E ∈ H, (ν E : ℝ)

/-- Weighted degree of a finite set: the mass of all hyperedges containing it. -/
def weightedDegree (H : Hypergraph V) (ν : EdgeWeight H) (L : Finset V) : ℝ :=
  ∑ E ∈ H with L ⊆ E, (ν E : ℝ)

/-- The finite sets which can contribute to the Janson energy. -/
def jansonSets [Fintype V] : Finset (Finset V) :=
  Finset.univ.powerset.filter fun L ↦ 2 ≤ L.card

/-- The weighted Janson energy
`∑_{|L| ≥ 2} d_ν(L)^2 / p^|L|`. -/
noncomputable def Lambda [Fintype V] (H : Hypergraph V) (p : ℝ) (ν : EdgeWeight H) : ℝ :=
  ∑ L ∈ jansonSets, weightedDegree H ν L ^ 2 / p ^ L.card

/-- The `(p,R)`-Janson property.  At `R = 0` it holds by convention. -/
def IsJanson [Fintype V] (H : Hypergraph V) (p R : ℝ) : Prop :=
  R = 0 ∨ ∃ ν : EdgeWeight H, Lambda H p ν < mass H ν ^ 2 / R

/-- Multiply every edge weight by a nonnegative scalar. -/
def scale {H : Hypergraph V} (c : NNReal) (ν : EdgeWeight H) : EdgeWeight H :=
  c • ν

/-- Extend a weight by zero from a subhypergraph to a larger hypergraph. -/
def zeroExtend {H K : Hypergraph V} (_hHK : H ⊆ K) (ν : EdgeWeight H) : EdgeWeight K :=
  fun E ↦ if E ∈ H then ν E else 0

@[simp] lemma scale_apply {H : Hypergraph V} (c : NNReal) (ν : EdgeWeight H)
    (E : Finset V) : scale c ν E = c * ν E := by
  rfl

@[simp] lemma zeroExtend_apply_of_mem {H K : Hypergraph V} (hHK : H ⊆ K)
    (ν : EdgeWeight H) {E : Finset V} (hE : E ∈ H) :
    zeroExtend hHK ν E = ν E := by
  simp [zeroExtend, hE]

@[simp] lemma zeroExtend_apply_of_not_mem {H K : Hypergraph V} (hHK : H ⊆ K)
    (ν : EdgeWeight H) {E : Finset V} (hE : E ∉ H) :
    zeroExtend hHK ν E = 0 := by
  simp [zeroExtend, hE]

/-! ## Linearity of mass and degree -/

@[simp] lemma mass_zero (H : Hypergraph V) : mass H (0 : EdgeWeight H) = 0 := by
  simp [mass]

lemma mass_add (H : Hypergraph V) (ν μ : EdgeWeight H) :
    mass H (ν + μ) = mass H ν + mass H μ := by
  simp [mass, Finset.sum_add_distrib]

lemma mass_scale (H : Hypergraph V) (c : NNReal) (ν : EdgeWeight H) :
    mass H (scale c ν) = (c : ℝ) * mass H ν := by
  simp [mass, scale, Finset.mul_sum]

@[simp] lemma weightedDegree_zero (H : Hypergraph V) (L : Finset V) :
    weightedDegree H (0 : EdgeWeight H) L = 0 := by
  simp [weightedDegree]

lemma weightedDegree_add (H : Hypergraph V) (ν μ : EdgeWeight H) (L : Finset V) :
    weightedDegree H (ν + μ) L =
      weightedDegree H ν L + weightedDegree H μ L := by
  simp [weightedDegree, Finset.sum_add_distrib]

lemma weightedDegree_scale (H : Hypergraph V) (c : NNReal) (ν : EdgeWeight H)
    (L : Finset V) :
    weightedDegree H (scale c ν) L = (c : ℝ) * weightedDegree H ν L := by
  simp [weightedDegree, scale, Finset.mul_sum]

lemma mass_nonneg (H : Hypergraph V) (ν : EdgeWeight H) : 0 ≤ mass H ν := by
  exact Finset.sum_nonneg fun E _ ↦ NNReal.coe_nonneg (ν E)

lemma weightedDegree_nonneg (H : Hypergraph V) (ν : EdgeWeight H) (L : Finset V) :
    0 ≤ weightedDegree H ν L := by
  exact Finset.sum_nonneg fun E _ ↦ NNReal.coe_nonneg (ν E)

/-! ## Scaling and elementary estimates for `Lambda` -/

@[simp] lemma Lambda_zero [Fintype V] (H : Hypergraph V) (p : ℝ) :
    Lambda H p (0 : EdgeWeight H) = 0 := by
  simp [Lambda]

lemma Lambda_scale [Fintype V] (H : Hypergraph V) (p : ℝ) (c : NNReal)
    (ν : EdgeWeight H) :
    Lambda H p (scale c ν) = (c : ℝ) ^ 2 * Lambda H p ν := by
  rw [Lambda, Lambda, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro L hL
  rw [weightedDegree_scale]
  ring

lemma Lambda_nonneg [Fintype V] (H : Hypergraph V) {p : ℝ} (hp : 0 ≤ p)
    (ν : EdgeWeight H) : 0 ≤ Lambda H p ν := by
  apply Finset.sum_nonneg
  intro L hL
  exact div_nonneg (sq_nonneg _) (pow_nonneg hp _)

/-- Increasing `p` can only decrease the Janson energy. -/
lemma Lambda_anti [Fintype V] (H : Hypergraph V) (ν : EdgeWeight H)
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    Lambda H q ν ≤ Lambda H p ν := by
  apply Finset.sum_le_sum
  intro L hL
  exact div_le_div_of_nonneg_left (sq_nonneg _)
    (pow_pos hp L.card) (pow_le_pow_left₀ hp.le hpq L.card)

/-! ## Extension by zero -/

lemma mass_zeroExtend {H K : Hypergraph V} (hHK : H ⊆ K) (ν : EdgeWeight H) :
    mass K (zeroExtend hHK ν) = mass H ν := by
  rw [mass, mass]
  symm
  apply Finset.sum_subset_zero_on_sdiff hHK
  · intro E hE
    obtain ⟨_, hEnot⟩ := Finset.mem_sdiff.mp hE
    simp [zeroExtend, hEnot]
  · intro E hE
    simp [zeroExtend, hE]

lemma weightedDegree_zeroExtend {H K : Hypergraph V} (hHK : H ⊆ K)
    (ν : EdgeWeight H) (L : Finset V) :
    weightedDegree K (zeroExtend hHK ν) L = weightedDegree H ν L := by
  rw [weightedDegree, weightedDegree]
  symm
  apply Finset.sum_subset_zero_on_sdiff
  · intro E hE
    obtain ⟨hEH, hLE⟩ := Finset.mem_filter.mp hE
    exact Finset.mem_filter.2 ⟨hHK hEH, hLE⟩
  · intro E hE
    obtain ⟨hEKL, hEnotFilter⟩ := Finset.mem_sdiff.mp hE
    obtain ⟨_, hLE⟩ := Finset.mem_filter.mp hEKL
    have hEnot : E ∉ H := by
      intro hEin
      exact hEnotFilter (Finset.mem_filter.2 ⟨hEin, hLE⟩)
    simp [zeroExtend, hEnot]
  · intro E hE
    obtain ⟨hEin, _⟩ := Finset.mem_filter.mp hE
    simp [zeroExtend, hEin]

lemma Lambda_zeroExtend [Fintype V] {H K : Hypergraph V} (hHK : H ⊆ K)
    (p : ℝ) (ν : EdgeWeight H) :
    Lambda K p (zeroExtend hHK ν) = Lambda H p ν := by
  apply Finset.sum_congr rfl
  intro L hL
  rw [weightedDegree_zeroExtend]

/-! ## Closure properties of the Janson predicate -/

namespace IsJanson

lemma radius_zero [Fintype V] (H : Hypergraph V) (p : ℝ) : H.IsJanson p 0 := by
  exact Or.inl rfl

/-- Jansonness is monotone under increasing `p` and decreasing the radius. -/
lemma mono_params [Fintype V] {H : Hypergraph V} {p q R S : ℝ}
    (h : H.IsJanson p R) (hp : 0 < p) (hpq : p ≤ q) (hS : 0 ≤ S) (hSR : S ≤ R) :
    H.IsJanson q S := by
  rcases eq_or_lt_of_le hS with rfl | hSpos
  · exact radius_zero H q
  have hRpos : 0 < R := hSpos.trans_le hSR
  rcases h with hRzero | ⟨ν, hν⟩
  · exact (hRpos.ne' hRzero).elim
  right
  refine ⟨ν, (Lambda_anti H ν hp hpq).trans_lt (hν.trans_le ?_)⟩
  exact div_le_div_of_nonneg_left (sq_nonneg _) hSpos hSR

/-- Adding hyperedges preserves the Janson property. -/
lemma mono_edges [Fintype V] {H K : Hypergraph V} (hHK : H ⊆ K) {p R : ℝ}
    (h : H.IsJanson p R) : K.IsJanson p R := by
  rcases h with hR | ⟨ν, hν⟩
  · exact Or.inl hR
  right
  refine ⟨zeroExtend hHK ν, ?_⟩
  simpa [mass_zeroExtend, Lambda_zeroExtend] using hν

/-- At nonzero radius, unfold `IsJanson` to obtain an actual witnessing edge weight. -/
lemma exists_witness [Fintype V] {H : Hypergraph V} {p R : ℝ}
    (h : H.IsJanson p R) (hR : R ≠ 0) :
    ∃ ν : EdgeWeight H, Lambda H p ν < mass H ν ^ 2 / R := by
  rcases h with hRzero | hν
  · exact (hR hRzero).elim
  · exact hν

/-- A positive-radius Janson witness necessarily has positive mass (when `p ≥ 0`). -/
lemma witness_mass_pos [Fintype V] {H : Hypergraph V} {p R : ℝ}
    (hp : 0 ≤ p) (hR : 0 < R) {ν : EdgeWeight H}
    (hν : Lambda H p ν < mass H ν ^ 2 / R) : 0 < mass H ν := by
  have hright : 0 < mass H ν ^ 2 / R :=
    (Lambda_nonneg H hp ν).trans_lt hν
  have hsq : 0 < mass H ν ^ 2 := by
    rcases div_pos_iff.mp hright with hpos | hneg
    · exact hpos.1
    · exact False.elim ((not_lt_of_ge hR.le) hneg.2)
  exact lt_of_le_of_ne (mass_nonneg H ν) (sq_pos_iff.mp hsq).symm

/-- A hypergraph which is Janson at positive radius contains an edge. -/
lemma nonempty [Fintype V] {H : Hypergraph V} {p R : ℝ}
    (h : H.IsJanson p R) (hp : 0 ≤ p) (hR : 0 < R) : H.Nonempty := by
  rcases exists_witness h hR.ne' with ⟨ν, hν⟩
  have hm : 0 < mass H ν := witness_mass_pos hp hR hν
  rw [Finset.nonempty_iff_ne_empty]
  intro hEmpty
  subst H
  simpa [mass] using hm

/-- Scale a positive-radius witness to any prescribed positive total mass. -/
lemma exists_normalized [Fintype V] {H : Hypergraph V} {p R y : ℝ}
    (h : H.IsJanson p R) (hp : 0 < p) (hR : 0 < R) (hy : 0 < y) :
    ∃ ν : EdgeWeight H, mass H ν = y ∧ Lambda H p ν < y ^ 2 / R := by
  rcases h with hRzero | ⟨ν, hν⟩
  · exact (hR.ne' hRzero).elim
  have hm : 0 < mass H ν := witness_mass_pos hp.le hR hν
  let c : NNReal := ⟨y / mass H ν, (div_pos hy hm).le⟩
  refine ⟨scale c ν, ?_, ?_⟩
  · rw [mass_scale]
    change (y / mass H ν) * mass H ν = y
    field_simp
  · rw [Lambda_scale]
    change (y / mass H ν) ^ 2 * Lambda H p ν < y ^ 2 / R
    calc
      (y / mass H ν) ^ 2 * Lambda H p ν <
          (y / mass H ν) ^ 2 * (mass H ν ^ 2 / R) := by
            exact mul_lt_mul_of_pos_left hν (sq_pos_of_pos (div_pos hy hm))
      _ = y ^ 2 / R := by field_simp

end IsJanson
end Hypergraph
end Erdos565
