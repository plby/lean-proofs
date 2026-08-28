import ErdosProblems.Erdos577.PawElevenWitnesses
import ErdosProblems.Erdos577.PawEncoding
import ErdosProblems.Erdos577.CycleLabels

/-! The exact exceptional cross-edge pattern of Wang's Lemma 3.4(a). -/

namespace Erdos577

variable {V : Type*} {G : SimpleGraph V}

/-- The leaf meets labels 0,1,2; the center meets all four labels; each
noncentral triangle vertex meets precisely the opposite pair 0,2. -/
def PawEleven.Pattern (p : Paw G) (q : Quadrilateral G) : Prop :=
  ∀ i j : Fin 4, G.Adj (p.vertices i) (q j) ↔
    (if i = 0 then j ≠ 3 else if i = 1 then True else j = 0 ∨ j = 2)

variable [DecidableEq V] [DecidableRel G.Adj]

open Finset
open scoped BigOperators

lemma Paw.contacts_support (p : Paw G) (s : Finset V) :
    contacts G p.support s = degreeIn G p.leaf s + contacts G p.triangle s := by
  rw [p.support_eq, ← singleton_union,
    contacts_union_left G (disjoint_singleton_left.mpr p.leaf_not_mem_triangle),
    contacts_singleton_left]

lemma Paw.contacts_triangle (p : Paw G) (s : Finset V) :
    contacts G p.triangle s = degreeIn G (p.vertices 1) s +
      (degreeIn G (p.vertices 2) s + degreeIn G (p.vertices 3) s) := by
  simp [contacts, Paw.triangle, p.vertices.injective.eq_iff]

lemma PawEleven.Pattern.degree {p : Paw G} {q : Quadrilateral G} (h : Pattern p q)
    (i : Fin 4) : degreeIn G (p.vertices i) q.support =
      if i = 0 then 3 else if i = 1 then 4 else 2 := by
  have hq : Function.Injective (q : Fin 4 → V) := q.injective
  rw [Quadrilateral.support, degreeIn_image G _ _ _ hq]
  simp_rw [h i]
  fin_cases i <;> decide +kernel

lemma PawEleven.Pattern.triangle_contacts {p : Paw G} {q : Quadrilateral G}
    (h : Pattern p q) : contacts G p.triangle q.support = 8 := by
  rw [p.contacts_triangle, h.degree, h.degree, h.degree]
  decide

/-- Eleven cross contacts and a positive leaf row give a factor or the
source's exact cyclic exceptional pattern. No optimality is assumed. -/
theorem Paw.eleven_contacts (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (hleaf : 1 ≤ degreeIn G p.leaf q.support)
    (hcross : 11 ≤ contacts G p.support q.support) :
    LocalFactor G (p.support ∪ q.support) ∨
      ∃ q' : Quadrilateral G, q'.support = q.support ∧ PawEleven.Pattern p q' := by
  have hc := PawEleven.finite_classification (PawEncoding.encoded p q)
    (by rw [PawEncoding.terminalCount_encoded]; exact hleaf)
    (by rw [PawEncoding.crossCount_encoded]; exact hcross)
  rcases hc with hfactor | hex
  · left
    have hf := hfactor.image (PawEncoding.baseCopy p q hd)
    rw [PawEncoding.baseCopy_image] at hf
    exact hf
  · right
    obtain ⟨r, hr⟩ := PawEleven.exceptional_rows hex
    refine ⟨q.rotate r, q.rotate_support r, ?_⟩
    intro i j
    rw [Quadrilateral.rotate_apply]
    have hbit := hr i j
    rw [PawEncoding.encoded_bit] at hbit
    change decide (G.Adj (p.vertices i) (q (j + r))) =
      decide (if i = 0 then j ≠ 3 else if i = 1 then True else j = 0 ∨ j = 2) at hbit
    constructor
    · intro he
      apply of_decide_eq_true
      rw [← hbit]
      exact decide_eq_true he
    · intro he
      apply of_decide_eq_true
      rw [hbit]
      exact decide_eq_true he

/-- The first reduction in Wang 3.4(b): a nonfactor with nine triangle
contacts and a positive leaf row must have exactly one leaf contact and nine triangle contacts. -/
theorem Paw.nine_triangle_contacts (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (hn : ¬LocalFactor G (p.support ∪ q.support))
    (hleaf : 1 ≤ degreeIn G p.leaf q.support) (htri : 9 ≤ contacts G p.triangle q.support) :
    degreeIn G p.leaf q.support = 1 ∧ contacts G p.triangle q.support = 9 := by
  have ht : contacts G p.support q.support ≤ 10 := by
    by_contra hh
    have h11 : 11 ≤ contacts G p.support q.support := by omega
    rcases p.eleven_contacts q hd hleaf h11 with hf | ⟨r, hr, hp⟩
    · exact hn hf
    · have he := hp.triangle_contacts
      rw [hr] at he
      omega
  rw [p.contacts_support] at ht
  omega

end Erdos577
