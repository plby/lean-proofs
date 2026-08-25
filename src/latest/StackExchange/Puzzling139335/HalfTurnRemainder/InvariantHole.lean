import StackExchange.Puzzling139335.QuarterTurnTopology.InvariantCurve
import StackExchange.Puzzling139335.QuarterTurnTopology.CurveNesting
import StackExchange.Puzzling139335.JordanInvolution
import StackExchange.Puzzling139335.HalfTurnRemainder.InvariantHole.Exterior
import Mathlib.Topology.Connected.LocallyConnected

/-!
# A bounded complementary component cannot be invariant under a half-turn

An invariant open connected set avoiding the center contains a centrally
symmetric Jordan curve. Its center lies inside that curve. A connected set
containing the center and missing the curve therefore lies entirely inside.
The curve's exterior then lies in the same complementary component as the
curve, so that component is unbounded. No winding-number argument is used.
-/

open Set

namespace Puzzling139335.HalfTurnRemainder

noncomputable section

/-- An invariant open connected planar set avoiding the half-turn center
contains an invariant Jordan curve which encloses that center. -/
theorem exists_pointReflection_invariant_jordanCurve_subset {H : Set Plane} {c : Plane}
    (hopen : IsOpen H) (hconn : IsConnected H) (hcnot : c ∉ H)
    (hsym : AffineIsometryEquiv.pointReflection ℝ c '' H = H) :
    ∃ C ⊆ H, Schoenflies.IsJordanCurve C ∧
      AffineIsometryEquiv.pointReflection ℝ c '' C = C ∧ c ∈ Schoenflies.inside C := by
  let e := (AffineIsometryEquiv.pointReflection ℝ c).toHomeomorph
  have hinv : Function.Involutive e :=
    AffineIsometryEquiv.pointReflection_involutive (𝕜 := ℝ) c
  have heH : e '' H = H := hsym
  have hmaps : MapsTo e H H := by
    intro x hx
    rw [← heH]
    exact mem_image_of_mem e hx
  have hfree : ∀ x ∈ H, e x ≠ x := by
    intro x hx hxx
    exact hcnot ((AffineIsometryEquiv.pointReflection_fixed_iff (𝕜 := ℝ)).mp hxx ▸ hx)
  obtain ⟨x, hx⟩ := hconn.nonempty
  obtain ⟨A, hAH, -, hA⟩ := Schoenflies.exists_simple_arc_of_isPreconnected
    hopen hconn.isPreconnected hx (hmaps hx) (hfree x hx).symm
  obtain ⟨C, hCsub, hC, hCsym⟩ :=
    hA.exists_invariant_jordanCurve e hinv (fun z hz => hfree z (hAH hz))
  have hCH : C ⊆ H := by
    apply hCsub.trans
    apply union_subset hAH
    rintro z ⟨y, hy, rfl⟩
    exact hmaps (hAH hy)
  have hregion : IsJordanRegion (closure (Schoenflies.inside C)) := ⟨C, hC, rfl⟩
  have hregionsym : AffineIsometryEquiv.pointReflection ℝ c ''
      closure (Schoenflies.inside C) = closure (Schoenflies.inside C) := by
    change e '' closure (Schoenflies.inside C) = closure (Schoenflies.inside C)
    rw [e.image_closure, Schoenflies.homeomorph_image_inside, hCsym]
  have hcinside : c ∈ Schoenflies.inside C := by
    have hc := hregion.center_mem_interior_of_pointReflection hregionsym
    simpa only [interior_closure_inside (Schoenflies.jordan_curve_theorem hC)] using hc
  exact ⟨C, hCH, hC, hCsym, hcinside⟩

/-- A complementary component of a closed connected planar set containing the
half-turn center is unbounded whenever that component is invariant under the
half-turn. Compactness of the closed set is not needed. -/
theorem not_isBounded_connectedComponentIn_compl_of_pointReflection
    {K : Set Plane} {c x : Plane} (hKclosed : IsClosed K) (hKconn : IsConnected K)
    (hcK : c ∈ K) (hxK : x ∉ K)
    (hsym : AffineIsometryEquiv.pointReflection ℝ c '' connectedComponentIn Kᶜ x =
      connectedComponentIn Kᶜ x) :
    ¬ Bornology.IsBounded (connectedComponentIn Kᶜ x) := by
  have hHopen : IsOpen (connectedComponentIn Kᶜ x) :=
    hKclosed.isOpen_compl.connectedComponentIn
  have hHconn : IsConnected (connectedComponentIn Kᶜ x) :=
    isConnected_connectedComponentIn_iff.mpr hxK
  have hcnot : c ∉ connectedComponentIn Kᶜ x := by
    intro hcH
    exact (connectedComponentIn_subset Kᶜ x hcH) hcK
  obtain ⟨C, hCH, hC, -, hcinside⟩ :=
    exists_pointReflection_invariant_jordanCurve_subset hHopen hHconn hcnot hsym
  have hdis : Disjoint K C := by
    apply disjoint_left.mpr
    intro y hyK hyC
    exact (connectedComponentIn_subset Kᶜ x (hCH hyC)) hyK
  have hKinside : K ⊆ Schoenflies.inside C := by
    rcases (Schoenflies.jordan_curve_theorem hC).subset_inside_or_outside_of_isConnected
      hKconn hdis with hinside | houtside
    · exact hinside
    · exact False.elim (disjoint_left.mp Schoenflies.disjoint_inside_outside
        hcinside (houtside hcK))
  exact not_isBounded_connectedComponentIn_compl_of_subset_inside hC hKinside hCH

/-- In particular, a compact connected planar set containing `c` has no
bounded complementary component invariant under reflection in `c`. -/
theorem no_bounded_invariant_complement_component {K : Set Plane} {c x : Plane}
    (hKcompact : IsCompact K) (hKconn : IsConnected K) (hcK : c ∈ K) (hxK : x ∉ K)
    (hbounded : Bornology.IsBounded (connectedComponentIn Kᶜ x))
    (hsym : AffineIsometryEquiv.pointReflection ℝ c '' connectedComponentIn Kᶜ x =
      connectedComponentIn Kᶜ x) : False :=
  not_isBounded_connectedComponentIn_compl_of_pointReflection
    hKcompact.isClosed hKconn hcK hxK hsym hbounded

end

end Puzzling139335.HalfTurnRemainder
