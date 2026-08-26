/- Incident oriented edges and their exact degree count. -/
import ErdosProblems.Erdos73.Foundations
import ErdosProblems.Erdos73.ThreeArms

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Erdos73Infrastructure.SimpleGraph
variable {W : Type*} [Fintype W] [LinearOrder W] {H : SimpleGraph W}

abbrev IncidentOrientedEdge (H : SimpleGraph W) (w : W) :=
  {e : OrientedEdge H // e.lo = w ∨ e.hi = w}

def incidentOrientedNeighbor {w : W} (e : IncidentOrientedEdge H w) : H.neighborSet w :=
  if h : e.val.lo = w then
    ⟨e.val.hi, (congrArg (fun z => H.Adj z e.val.hi) h).mp e.val.adj⟩ else
    ⟨e.val.lo, (congrArg (fun z => H.Adj z e.val.lo)
      (e.property.resolve_left h)).mp e.val.adj.symm⟩

theorem incidentOrientedNeighbor_injective (w : W) :
    Function.Injective (incidentOrientedNeighbor (H := H) (w := w)) := by
  intro e f hef
  have hn := congrArg Subtype.val hef
  by_cases he : e.val.lo = w <;> by_cases hf : f.val.lo = w
  · simp only [incidentOrientedNeighbor, dif_pos he, dif_pos hf] at hn
    exact Subtype.ext (Subtype.ext (Prod.ext (he.trans hf.symm) hn))
  · simp only [incidentOrientedNeighbor, dif_pos he, dif_neg hf] at hn
    have hft := f.property.resolve_left hf
    have hl := e.val.lo_lt_hi
    have hr := f.val.lo_lt_hi
    rw [he, hn] at hl
    rw [hft] at hr
    exact (lt_asymm hl hr).elim
  · simp only [incidentOrientedNeighbor, dif_neg he, dif_pos hf] at hn
    have het := e.property.resolve_left he
    have hl := e.val.lo_lt_hi
    have hr := f.val.lo_lt_hi
    rw [het] at hl
    rw [hf, ← hn] at hr
    exact (lt_asymm hl hr).elim
  · simp only [incidentOrientedNeighbor, dif_neg he, dif_neg hf] at hn
    exact Subtype.ext (Subtype.ext (Prod.ext hn
      ((e.property.resolve_left he).trans (f.property.resolve_left hf).symm)))

theorem card_incidentOrientedEdge_le_degree (w : W) :
    Fintype.card (IncidentOrientedEdge H w) ≤ H.degree w := by
  have hc := Fintype.card_le_of_injective (incidentOrientedNeighbor (H := H) (w := w))
    (incidentOrientedNeighbor_injective w)
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using hc

def OrientedEdge.incidentLo (e : OrientedEdge H) : IncidentOrientedEdge H e.lo := ⟨e, Or.inl rfl⟩
def OrientedEdge.incidentHi (e : OrientedEdge H) : IncidentOrientedEdge H e.hi := ⟨e, Or.inr rfl⟩

end
end Erdos73
