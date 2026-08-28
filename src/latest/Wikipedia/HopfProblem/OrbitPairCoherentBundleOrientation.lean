import Wikipedia.HopfProblem.OrbitPairDeterminantSignCover
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Coherent local orientation choices

A section of the determinant-sign cover gives continuous local orientation
bits. On chart overlaps they transform by the determinant of the original
vector bundle's transition map. Along any connected path contained in one
trivialization the bit is constant.
-/

noncomputable section

open Set Function Topology

namespace Wikipedia.HopfProblem.OrbitPair.DeterminantSignCover

variable {B E ι : Type*} [TopologicalSpace B]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (Z : VectorBundleCore ℝ B E ι)

/-- A continuous section, with its projection identity recorded pointwise. -/
structure Orientation where
  lift : C(B, (core Z).TotalSpace)
  proj_lift : ∀ x, (core Z).proj (lift x) = x

theorem nonempty_orientation [SimplyConnectedSpace B] [LocallyPathConnectedSpace B] :
    Nonempty (Orientation Z) := by
  let x₀ : B := Classical.arbitrary B
  obtain ⟨s, hs, _⟩ := existsUnique_section Z x₀ false
  exact ⟨⟨s, fun x => congrFun hs.2 x⟩⟩

namespace Orientation

variable {Z} (o : Orientation Z)

/-- Coordinates in the basepoint's preferred trivialization. This raw bit
need not be continuous as the preferred chart changes. -/
def rawSign (x : B) : Bool := (o.lift x).2

def localSign (i : ι) (x : B) : Bool := ((core Z).localTriv i (o.lift x)).2

theorem continuousOn_localSign (i : ι) : ContinuousOn (o.localSign i) (Z.baseSet i) := by
  apply continuous_snd.comp_continuousOn
  refine ((core Z).localTriv i).continuousOn.comp o.lift.continuous.continuousOn ?_
  intro x hx
  change (core Z).proj (o.lift x) ∈ Z.baseSet i
  rw [o.proj_lift x]
  exact hx

theorem localSign_eq (i : ι) (x : B) :
    o.localSign i x = action (Z.coordChange (Z.indexAt x) i x).det (o.lift x).2 := by
  change action (Z.coordChange (Z.indexAt ((core Z).proj (o.lift x))) i
    ((core Z).proj (o.lift x))).det (o.lift x).2 = _
  rw [o.proj_lift x]

theorem localSign_eq_action_rawSign (i : ι) (x : B) :
    o.localSign i x = action (Z.coordChange (Z.indexAt x) i x).det (o.rawSign x) :=
  o.localSign_eq i x

/-- The overlap law is the sign of the actual transition determinant. -/
theorem localSign_coordChange (i j : ι) {x : B}
    (hx : x ∈ Z.baseSet i ∩ Z.baseSet j) :
    action (Z.coordChange i j x).det (o.localSign i x) = o.localSign j x := by
  rw [o.localSign_eq i x, o.localSign_eq j x]
  exact (core Z).coordChange_comp (Z.indexAt x) i j x
    ⟨⟨Z.mem_baseSet_at x, hx.1⟩, hx.2⟩ (o.lift x).2

theorem localSign_eq_on_preconnected {A : Type*} [TopologicalSpace A]
    (i : ι) {a : A → B} {s : Set A} (hs : IsPreconnected s)
    (ha : ContinuousOn a s) (himage : MapsTo a s (Z.baseSet i))
    {x y : A} (hx : x ∈ s) (hy : y ∈ s) :
    o.localSign i (a x) = o.localSign i (a y) :=
  hs.constant ((o.continuousOn_localSign i).comp ha himage) hx hy

end Orientation

end Wikipedia.HopfProblem.OrbitPair.DeterminantSignCover
