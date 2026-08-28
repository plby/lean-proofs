import Wikipedia.NoExoticSixSphere.OpenZeroSliceAvoidance
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Zero-slice avoidance with a bound in the original coordinates

Keep a second copy of the original point as a fixed complementary coordinate.
The open condition that the moving point stays within a prescribed distance
of that copy then gives a uniformly small homotopy in the original metric,
not merely in the partial-gradient coordinates.
-/

open Set Module
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere

variable {B H M F Q E : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [PseudoMetricSpace Q] [PseudoMetricSpace E]

include I

theorem exists_relational_zeroSlice_avoiding_chart_homotopy
    (e : OpenPartialHomeomorph E (F × Q)) (f : C(M, E))
    (V : Set E) (hV : IsOpen V) (hsource : V ⊆ e.source) (hmem : ∀ x, f x ∈ V)
    (R : Set (E × E)) (hR : IsOpen R) (hdiag : ∀ x, (f x, f x) ∈ R)
    (S : Set M) (hS : IsCompact S)
    (hSafe : ∀ x ∈ S, (e (f x)).1 ≠ 0) (hd : finrank ℝ B < finrank ℝ F) :
    ∃ g : C(M, E), (∀ x, (e (g x)).1 ≠ 0) ∧
      ∃ G : ContinuousMap.HomotopyRel f g S,
        ∀ t x, G (t, x) ∈ V ∧ (e (G (t, x))).2 = (e (f x)).2 ∧
          (G (t, x), f x) ∈ R := by
  let e' : OpenPartialHomeomorph (E × E) (F × (Q × E)) :=
    (e.prod (OpenPartialHomeomorph.refl E)).trans
      (Homeomorph.prodAssoc F Q E).toOpenPartialHomeomorph
  let W : Set (E × E) := {p | p.1 ∈ V ∧ p ∈ R}
  have hW : IsOpen W := (hV.preimage continuous_fst).inter hR
  have hWsource : W ⊆ e'.source := by
    intro p hp
    change (p.1 ∈ e.source ∧ p.2 ∈ (univ : Set E)) ∧
      (e p.1, p.2) ∈ (univ : Set ((F × Q) × E))
    exact ⟨⟨hsource hp.1, mem_univ _⟩, mem_univ _⟩
  let f' := f.prodMk f
  have hf' : ∀ x, f' x ∈ W := fun x ↦ ⟨hmem x, hdiag x⟩
  obtain ⟨g', hg', G', hG'⟩ := exists_zeroSlice_avoiding_chart_homotopy (I := I)
    e' f' W hW hWsource hf' S hS hSafe hd
  have hfixed (t) (x) : (G' (t, x)).2 = f x := by
    have hh : ((e (G' (t, x)).1).2, (G' (t, x)).2) = ((e (f x)).2, f x) := (hG' t x).2
    exact congrArg Prod.snd hh
  let fstMap : C(E × E, E) := ContinuousMap.fst
  let G : ContinuousMap.HomotopyRel f (fstMap.comp g') S :=
    (G'.compContinuousMap fstMap).cast (by
    exact ContinuousMap.ext (fun _ ↦ rfl)) rfl
  refine ⟨fstMap.comp g', hg', G, fun t x ↦ ⟨(hG' t x).1.1, ?_, ?_⟩⟩
  · have hh : ((e (G' (t, x)).1).2, (G' (t, x)).2) = ((e (f x)).2, f x) := (hG' t x).2
    exact congrArg Prod.fst hh
  · have hh := (hG' t x).1.2
    change ((G' (t, x)).1, (G' (t, x)).2) ∈ R at hh
    change ((G' (t, x)).1, f x) ∈ R
    rwa [hfixed t x] at hh

theorem exists_small_zeroSlice_avoiding_chart_homotopy
    (e : OpenPartialHomeomorph E (F × Q)) (f : C(M, E))
    (V : Set E) (hV : IsOpen V) (hsource : V ⊆ e.source) (hmem : ∀ x, f x ∈ V)
    (ε : ℝ) (hε : 0 < ε) (S : Set M) (hS : IsCompact S)
    (hSafe : ∀ x ∈ S, (e (f x)).1 ≠ 0) (hd : finrank ℝ B < finrank ℝ F) :
    ∃ g : C(M, E), (∀ x, (e (g x)).1 ≠ 0) ∧
      ∃ G : ContinuousMap.HomotopyRel f g S,
        ∀ t x, G (t, x) ∈ V ∧ (e (G (t, x))).2 = (e (f x)).2 ∧
          dist (G (t, x)) (f x) < ε :=
  exists_relational_zeroSlice_avoiding_chart_homotopy (I := I) e f V hV hsource hmem
    {p | dist p.1 p.2 < ε}
    (isOpen_lt (continuous_fst.dist continuous_snd) continuous_const)
    (fun _ ↦ by simpa only [mem_ofPred_eq, dist_self] using hε) S hS hSafe hd

end NoExoticSixSphere
