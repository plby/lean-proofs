import ErdosProblems.Erdos547.PrivateClassBounds

/-!
# Constructing private sets independently inside disjoint head clusters
-/

namespace Erdos547

open Finset
open scoped BigOperators

theorem sum_filter_coe {F M : Type*} [AddCommMonoid M] (S : Finset F)
    (p : F → Prop) [DecidablePred p] (w : F → M) :
    (∑ x ∈ (Finset.univ : Finset ↥S).filter (fun x ↦ p x.val), w x.val) =
      ∑ x ∈ S.filter p, w x := by
  rw [Finset.sum_filter, Finset.sum_coe_sort S (fun x ↦ if p x then w x else 0),
    ← Finset.sum_filter]

open scoped Classical in
theorem exists_clusterwise_private_sets {F V I C : Type*} [Fintype F] [DecidableEq C] [DecidableEq I]
    (cluster : I → Finset V) (head : F → I) (col : F → C)
    (w : F → ℕ) (candidates : F → Finset V) (D : I → C → ℝ)
    (hcluster : ∀ i j, i ≠ j → Disjoint (cluster i) (cluster j))
    (hsub : ∀ x, candidates x ⊆ cluster (head x))
    (hsingle : ∀ x,
      ((∑ y ∈ (Finset.univ : Finset F).filter
        (fun y ↦ head y = head x ∧ col y = col x), w y) : ℝ) ≤ D (head x) (col x))
    (hjoint : ∀ x y, head x = head y → col x ≠ col y →
      ((∑ z ∈ (Finset.univ : Finset F).filter (fun z ↦ head z = head x), w z) : ℝ) ≤
        max (D (head x) (col x)) (D (head x) (col y)))
    (hsize : ∀ x, D (head x) (col x) ≤ ((candidates x).card : ℝ)) :
    ∃ R : F → Finset V, (∀ x, R x ⊆ candidates x) ∧
      (∀ x, (R x).card = w x) ∧ Pairwise (fun x y ↦ Disjoint (R x) (R y)) := by
  classical
  let fiber (i : I) := (Finset.univ : Finset F).filter (fun x ↦ head x = i)
  have hex (i : I) : ∃ R : F → Finset V,
      (∀ x, head x = i → R x ⊆ candidates x) ∧
      (∀ x, head x = i → (R x).card = w x) ∧
      (∀ x y, head x = i → head y = i → x ≠ y → Disjoint (R x) (R y)) := by
    have hhead (x : ↥(fiber i)) : head x.val = i := (Finset.mem_filter.mp x.property).2
    have hsingle' (x : ↥(fiber i)) :
        ((∑ y ∈ (Finset.univ : Finset ↥(fiber i)).filter (fun y ↦ col y.val = col x.val),
          w y.val) : ℝ) ≤ D i (col x.val) := by
      rw [sum_filter_coe (fiber i) (fun y ↦ col y = col x.val) (fun y ↦ (w y : ℝ))]
      simp only [fiber, Finset.filter_filter]
      have hh := hsingle x.val
      rwa [hhead x] at hh
    have hjoint' (x y : ↥(fiber i)) (hxy : col x.val ≠ col y.val) :
        ((∑ z : ↥(fiber i), w z.val) : ℝ) ≤ max (D i (col x.val)) (D i (col y.val)) := by
      rw [Finset.sum_coe_sort (fiber i) (fun z ↦ (w z : ℝ))]
      have hh := hjoint x.val y.val ((hhead x).trans (hhead y).symm) hxy
      rwa [hhead x] at hh
    have hsize' (x : ↥(fiber i)) : D i (col x.val) ≤ ((candidates x.val).card : ℝ) := by
      have hh := hsize x.val
      rwa [hhead x] at hh
    obtain ⟨R, hR, hcard, hdis⟩ := exists_private_sets_of_class_bounds
      (fun x : ↥(fiber i) ↦ col x.val) (fun x ↦ w x.val) (fun x ↦ candidates x.val)
      (D i) hsingle' hjoint' hsize'
    let lift : F → Finset V := fun x ↦ if hx : x ∈ fiber i then R ⟨x, hx⟩ else ∅
    refine ⟨lift, ?_, ?_, ?_⟩
    · intro x hx
      have hxf : x ∈ fiber i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
      simpa only [lift, dif_pos hxf] using hR ⟨x, hxf⟩
    · intro x hx
      have hxf : x ∈ fiber i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
      simpa only [lift, dif_pos hxf] using hcard ⟨x, hxf⟩
    · intro x y hx hy hxy
      have hxf : x ∈ fiber i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
      have hyf : y ∈ fiber i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
      have hne : (⟨x, hxf⟩ : ↥(fiber i)) ≠ ⟨y, hyf⟩ :=
        fun he ↦ hxy (congrArg Subtype.val he)
      simpa only [lift, dif_pos hxf, dif_pos hyf] using hdis hne
  choose R hR hcard hdis using hex
  refine ⟨fun x ↦ R (head x) x, fun x ↦ hR _ x rfl, fun x ↦ hcard _ x rfl, ?_⟩
  intro x y hxy
  change Disjoint (R (head x) x) (R (head y) y)
  by_cases hhead : head x = head y
  · rw [hhead]
    exact hdis _ x y hhead rfl hxy
  · exact (hcluster (head x) (head y) hhead).mono
      ((hR _ x rfl).trans (hsub x)) ((hR _ y rfl).trans (hsub y))

end Erdos547

#print axioms Erdos547.exists_clusterwise_private_sets
