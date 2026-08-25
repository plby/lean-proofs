import StackExchange.Puzzling139335.JordanAccessibility
import StackExchange.Puzzling139335.JordanCrosscut
import StackExchange.Puzzling139335.JordanSubarc

/-!
# Alternating boundary contacts of Jordan regions

The crosscut required by the alternating-endpoint theorem is constructed from
two disjoint access spokes of the first region.  Thus the obstruction below
does not assume that the contact configuration already includes a crosscut.
-/

open Set Schoenflies

namespace Puzzling139335

namespace IsJordanRegion

/-- Two distinct frontier points of a closed Jordan region can be joined by an
arc whose other points are interior to that region. -/
theorem exists_arc_between_frontier {P : Set Plane} {p q : Plane}
    (hP : IsJordanRegion P) (hp : p ∈ frontier P) (hq : q ∈ frontier P)
    (hpq : p ≠ q) :
    ∃ A : Set Plane, IsArcBetween A p q ∧ A ⊆ P ∧
      A \ {p, q} ⊆ interior P := by
  obtain ⟨x, hx⟩ := hP.interior_nonempty
  let b : Bool → Plane := fun i => if i then q else p
  have hb : ∀ i, b i ∈ frontier P := by
    intro i
    cases i <;> simp only [b, Bool.false_eq_true, if_false, if_true]
    · exact hp
    · exact hq
  have hbi : Function.Injective b := by
    intro i j hij
    cases i <;> cases j
    · rfl
    · exact False.elim (hpq (by simpa [b] using hij))
    · exact False.elim (hpq (by simpa [b] using hij.symm))
    · rfl
  obtain ⟨A, hA, hAi, hdis⟩ := hP.exists_disjoint_arcs_to_frontier hx b hb hbi
  have harc : IsArcBetween (A false ∪ A true) p q := by
    apply (hA false).reverse.concatenate (hA true)
    intro z hz₀ hz₁
    have hz : z ∈ A false ∩ A true := ⟨hz₀, hz₁⟩
    rw [hdis false true (by decide)] at hz
    exact mem_singleton_iff.mp hz
  have hint : (A false ∪ A true) \ {p, q} ⊆ interior P := by
    rintro z ⟨hz | hz, hzne⟩
    · apply hAi false
      refine ⟨hz, ?_⟩
      simpa only [b, Bool.false_eq_true, if_false, mem_singleton_iff] using
        (fun heq : z = p => hzne (mem_insert_iff.mpr (Or.inl heq)))
    · apply hAi true
      refine ⟨hz, ?_⟩
      simpa only [b, if_true, mem_singleton_iff] using
        (fun heq : z = q => hzne (mem_insert_of_mem _ (mem_singleton_iff.mpr heq)))
  refine ⟨A false ∪ A true, harc, ?_, hint⟩
  intro z hz
  by_cases hends : z ∈ ({p, q} : Set Plane)
  · rcases mem_insert_iff.mp hends with rfl | hq'
    · exact hP.isClosed.closure_eq ▸ hp.1
    · obtain rfl := mem_singleton_iff.mp hq'
      exact hP.isClosed.closure_eq ▸ hq.1
  · exact interior_subset (hint ⟨hz, hends⟩)

/-- The bounded region of the frontier is the ordinary interior. -/
theorem inside_frontier_eq_interior {P : Set Plane} (hP : IsJordanRegion P) :
    inside (frontier P) = interior P := by
  obtain ⟨C, hC, rfl⟩ := hP
  rw [frontier_closure_inside (jordan_curve_theorem hC),
    interior_closure_inside (jordan_curve_theorem hC)]

end IsJordanRegion

namespace RectangularHull

/-- Changing plane coordinates preserves disjointness of the two interiors. -/
theorem disjoint_interiors_image_homeomorph {P Q : Set Plane}
    (h : Disjoint (interior P) (interior Q)) (e : Plane ≃ₜ Plane) :
    Disjoint (interior (e '' P)) (interior (e '' Q)) := by
  rw [← e.image_interior, ← e.image_interior]
  exact disjoint_image_of_injective e.injective h

/-- A point of a subregion on the ambient frontier is also on the
frontier of the subregion. -/
theorem mem_frontier_of_subset {P S : Set Plane} {p : Plane}
    (hPS : P ⊆ S) (hpP : p ∈ P) (hpS : p ∈ frontier S) :
    p ∈ frontier P := by
  refine ⟨subset_closure hpP, ?_⟩
  intro hp
  exact hpS.2 (interior_mono hPS hp)

/-- Two closed Jordan regions with disjoint interiors cannot have contacts
on opposite arcs between two contacts of the first region. -/
theorem alternating_contacts_impossible {P Q S A B : Set Plane} {p q r s : Plane}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q) (hS : IsJordanRegion S)
    (hPS : P ⊆ S) (hQS : Q ⊆ S)
    (hdis : Disjoint (interior P) (interior Q))
    (hcut : IsCutPair (frontier S) p q A B)
    (hp : p ∈ P) (hq : q ∈ P) (hr : r ∈ Q) (hs : s ∈ Q)
    (hrA : r ∈ A) (hrB : r ∉ B) (hsB : s ∈ B) (hsA : s ∉ A) : False := by
  have hpS : p ∈ frontier S := hcut.fst_subset hcut.fst.left_mem
  have hqS : q ∈ frontier S := hcut.fst_subset hcut.fst.right_mem
  have hpP := mem_frontier_of_subset hPS hp hpS
  have hqP := mem_frontier_of_subset hPS hq hqS
  have hpq : p ≠ q := by
    obtain ⟨f, _, hi, _, h0, h1⟩ := hcut.fst
    intro heq
    exact zero_ne_one (hi zero_mem_I one_mem_I (h0.trans (heq.trans h1.symm)))
  obtain ⟨X, hX, hXP, hXi⟩ := hP.exists_arc_between_frontier hpP hqP hpq
  have hcross : JordanCrosscut (frontier S) X p q := by
    refine ⟨hS.frontier_isJordanCurve, hX, hpS, hqS, ?_⟩
    rw [hS.inside_frontier_eq_interior]
    exact hXi.trans (interior_mono hPS)
  have hQi : interior Q ⊆ inside (frontier S) := by
    rw [hS.inside_frontier_eq_interior]
    exact interior_mono hQS
  obtain ⟨z, hzQ, hzX⟩ := hcross.inter_nonempty_of_alternating hcut
    hQ.isConnected_interior.isPreconnected hQi
    (hQ.closure_interior.symm ▸ hr) (hQ.closure_interior.symm ▸ hs) hrA hrB hsB hsA
  exact Set.disjoint_left.mp (hP.disjoint_interior_left hdis.symm) hzQ (hXP hzX)

/-- The boundary arc itself determines the two sides; no named cut pair is
needed as an input. -/
theorem boundary_arc_contacts_impossible {P Q S A : Set Plane} {p q r s : Plane}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q) (hS : IsJordanRegion S)
    (hPS : P ⊆ S) (hQS : Q ⊆ S)
    (hdis : Disjoint (interior P) (interior Q))
    (hA : IsArcBetween A p q) (hAS : A ⊆ frontier S)
    (hp : p ∈ P) (hq : q ∈ P) (hr : r ∈ Q) (hs : s ∈ Q)
    (hrA : r ∈ A \ {p, q}) (hsS : s ∈ frontier S) (hsA : s ∉ A) : False := by
  obtain ⟨B, hcut⟩ := hS.frontier_isJordanCurve.exists_cutPair_of_subset_arc hA hAS
  have hrB : r ∉ B := by
    intro hrB
    exact hrA.2 (hcut.inter_eq ▸ (show r ∈ A ∩ B from ⟨hrA.1, hrB⟩))
  have hsB : s ∈ B := by
    rw [← hcut.union_eq] at hsS
    exact hsS.resolve_left hsA
  exact alternating_contacts_impossible hP hQ hS hPS hQS hdis hcut
    hp hq hr hs hrA.1 hrB hsB hsA

end RectangularHull

end Puzzling139335
