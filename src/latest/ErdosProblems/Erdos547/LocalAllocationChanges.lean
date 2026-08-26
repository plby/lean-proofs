import ErdosProblems.Erdos547.BoundedFractional

/-!
# Elementary edge decreases and oriented arc increments
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

namespace FractionalMatching

def decreaseEdge (μ : FractionalMatching G) (x y : V) (a : ℝ)
    (ha : 0 ≤ a) (he : a ≤ μ.weight x y) : FractionalMatching G :=
  μ.ofBoundedWeight (fun u v ↦ μ.weight u v - edgeIncrement x y a u v)
    (fun u v ↦ by rw [μ.symmetric u v, edgeIncrement_symmetric x y a u v])
    (fun u v ↦ by
      classical
      apply sub_nonneg.mpr
      rw [edgeIncrement]
      split_ifs with huv
      · rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
        · simpa only [hu, hv] using he
        · simpa only [hu, hv, μ.symmetric y x] using he
      · exact μ.nonnegative u v)
    (fun u v ↦ sub_le_self _ (edgeIncrement_nonneg x y ha u v))

open scoped Classical in
theorem decreaseEdge_load [DecidableEq V] (μ : FractionalMatching G) (x y : V) (hxy : x ≠ y)
    (a : ℝ) (ha : 0 ≤ a) (he : a ≤ μ.weight x y) (u : V) :
    (μ.decreaseEdge x y a ha he).load u =
      μ.load u - (if u = x then a else 0) - (if u = y then a else 0) := by
  classical
  change (∑ v, (μ.weight u v - edgeIncrement x y a u v)) = _
  rw [Finset.sum_sub_distrib, sum_edgeIncrement hxy]
  by_cases hux : u = x
  · subst u
    simp [hxy, load]
  · by_cases huy : u = y
    · subst u
      simp [Ne.symm hxy, load]
    · simp [hux, huy, load]

end FractionalMatching

open scoped Classical in
def arcIncrement (a b : V) (t : ℝ) (u v : V) : ℝ := if u = a ∧ v = b then t else 0

omit [Fintype V] in
theorem arcIncrement_nonneg (a b : V) {t : ℝ} (ht : 0 ≤ t) (u v : V) :
    0 ≤ arcIncrement a b t u v := by
  classical
  rw [arcIncrement]
  split_ifs <;> linarith

omit [Fintype V] in
theorem arcIncrement_supported {a b : V} (hab : G.Adj a b) (t : ℝ) {u v : V}
    (huv : ¬ G.Adj u v) : arcIncrement a b t u v = 0 := by
  classical
  rw [arcIncrement]
  apply if_neg
  rintro ⟨rfl, rfl⟩
  exact huv hab

open scoped Classical in
theorem sum_arcIncrement [DecidableEq V] (a b : V) (t : ℝ) (u : V) :
    (∑ v, arcIncrement a b t u v) = if u = a then t else 0 := by
  classical
  by_cases hua : u = a <;> simp [arcIncrement, hua]

open scoped Classical in
theorem sum_arcIncrement_reverse [DecidableEq V] (a b : V) (t : ℝ) (u : V) :
    (∑ v, arcIncrement a b t v u) = if u = b then t else 0 := by
  classical
  by_cases hub : u = b <;> simp [arcIncrement, hub]

namespace SkewMatching

def vertexLoadOf (γ : ℝ) (f : V → V → ℝ) (u : V) : ℝ :=
  (∑ v, f u v) / (1 + γ) + γ * (∑ v, f v u) / (1 + γ)

theorem vertexLoadOf_weight {γ : ℝ} (σ : SkewMatching G γ) (u : V) :
    vertexLoadOf γ σ.weight u = σ.load u := rfl

theorem vertexLoadOf_add (γ : ℝ) (f g : V → V → ℝ) (u : V) :
    vertexLoadOf γ (fun x y ↦ f x y + g x y) u = vertexLoadOf γ f u + vertexLoadOf γ g u := by
  simp only [vertexLoadOf, Finset.sum_add_distrib]
  ring

open scoped Classical in
theorem vertexLoadOf_normalized_arc [DecidableEq V] {γ : ℝ} (hγ : 0 ≤ γ)
    (a b : V) (t : ℝ) (u : V) :
    vertexLoadOf γ (arcIncrement a b ((1 + γ) * t)) u =
      (if u = a then t else 0) + (if u = b then γ * t else 0) := by
  classical
  rw [vertexLoadOf, sum_arcIncrement, sum_arcIncrement_reverse]
  have hden : 1 + γ ≠ 0 := by linarith
  split_ifs <;> field_simp [hden] <;> ring

def ofVertexLoad {γ : ℝ} (hγ : 0 ≤ γ) (f : V → V → ℝ)
    (hz : ∀ u v, 0 ≤ f u v) (hs : ∀ u v, ¬ G.Adj u v → f u v = 0)
    (hc : ∀ u, vertexLoadOf γ f u ≤ 1) : SkewMatching G γ where
  skew_nonneg := hγ
  weight := f
  nonnegative := hz
  supported := hs
  capacity u := by
    have hden : 0 < 1 + γ := by linarith
    apply (div_le_one hden).mp
    simpa only [add_div, vertexLoadOf] using hc u

end SkewMatching

end Erdos547.DPRS

#print axioms Erdos547.DPRS.FractionalMatching.decreaseEdge_load
#print axioms Erdos547.DPRS.SkewMatching.vertexLoadOf_normalized_arc
