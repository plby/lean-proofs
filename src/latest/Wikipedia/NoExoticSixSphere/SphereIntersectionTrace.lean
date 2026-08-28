import Wikipedia.NoExoticSixSphere.TransverseSphereIntersections
import Wikipedia.NoExoticSixSphere.CompactHalfLineBoundary

/-!
# The actual compact trace of intersections of two families

The trace uses the original source pairs and the real time coordinate. Its
endpoint set is the disjoint union of the actual intersection sets at times
zero and one. Compactness follows directly from continuity and compact source
manifolds. An even boundary therefore gives equality of the two mod-two counts.

The final theorem makes the required half-line atlas explicit. Constructing
that atlas from transversality, and obtaining transversality by perturbing a
given homotopy, are separate geometric obligations, not assumed conclusions.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.IntersectionTrace

open MapIntersections InvolutionQuotient

variable {X Y Z : Type*} (f : ℝ → X → Z) (g : ℝ → Y → Z)

/-- The genuine coincidence locus in the closed time slab. -/
def space : Set (ℝ × (X × Y)) :=
  {p | p.1 ∈ Icc 0 1 ∧ f p.1 p.2.1 = g p.1 p.2.2}

/-- The actual time-end locus, without a manifold-boundary assertion. -/
def ends : Set (space f g) := {p | p.val.1 = 0 ∨ p.val.1 = 1}

def endpoint (t : unitInterval) (p : pairs (f t) (g t)) : space f g :=
  ⟨(t, p.val), t.property, p.property⟩

theorem endpoint_injective (t : unitInterval) : Injective (endpoint f g t) := by
  intro p q h
  apply Subtype.ext
  exact congrArg (fun r : space f g ↦ r.val.2) h

theorem endpoint_mem_ends (t : unitInterval) (ht : t = 0 ∨ t = 1)
    (p : pairs (f t) (g t)) : endpoint f g t p ∈ ends f g := by
  rcases ht with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem ends_eq_union : ends f g = range (endpoint f g 0) ∪ range (endpoint f g 1) := by
  ext p
  constructor
  · rintro (h | h)
    · left
      have hp : p.val.2 ∈ pairs (f 0) (g 0) := by
        change f 0 p.val.2.1 = g 0 p.val.2.2
        simpa only [h] using p.property.2
      exact ⟨⟨p.val.2, hp⟩, Subtype.ext (Prod.ext h.symm rfl)⟩
    · right
      have hp : p.val.2 ∈ pairs (f 1) (g 1) := by
        change f 1 p.val.2.1 = g 1 p.val.2.2
        simpa only [h] using p.property.2
      exact ⟨⟨p.val.2, hp⟩, Subtype.ext (Prod.ext h.symm rfl)⟩
  · rintro (⟨q, rfl⟩ | ⟨q, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem disjoint_endpoints :
    Disjoint (range (endpoint f g 0)) (range (endpoint f g 1)) := by
  rw [disjoint_left]
  rintro p ⟨a, rfl⟩ ⟨b, h⟩
  have ht : (1 : ℝ) = 0 := congrArg (fun r : space f g ↦ r.val.1) h
  exact one_ne_zero ht

theorem finite_endpoint (t : unitInterval) (ht : (pairs (f t) (g t)).Finite) :
    (range (endpoint f g t)).Finite := by
  let := ht.to_subtype
  exact finite_range _

theorem endpoint_ncard (t : unitInterval) :
    (range (endpoint f g t)).ncard = (pairs (f t) (g t)).ncard :=
  ncard_range_of_injective (endpoint_injective f g t)

theorem finite_ends (h0 : (pairs (f 0) (g 0)).Finite)
    (h1 : (pairs (f 1) (g 1)).Finite) : (ends f g).Finite := by
  rw [ends_eq_union]
  exact (finite_endpoint f g 0 h0).union (finite_endpoint f g 1 h1)

theorem ends_ncard (h0 : (pairs (f 0) (g 0)).Finite)
    (h1 : (pairs (f 1) (g 1)).Finite) :
    (ends f g).ncard = (pairs (f 0) (g 0)).ncard + (pairs (f 1) (g 1)).ncard := by
  rw [ends_eq_union, ncard_union_eq (disjoint_endpoints f g)
    (finite_endpoint f g 0 h0) (finite_endpoint f g 1 h1), endpoint_ncard, endpoint_ncard]
  rfl

theorem parity_eq_of_even_ends (h0 : (pairs (f 0) (g 0)).Finite)
    (h1 : (pairs (f 1) (g 1)).Finite) (he : Even (ends f g).ncard) :
    parity (f 0) (g 0) = parity (f 1) (g 1) := by
  have hz := he.natCast_zmod_two
  rw [ends_ncard f g h0 h1, Nat.cast_add] at hz
  have heq := eq_neg_of_add_eq_zero_left hz
  rw [ZMod.neg_eq_self_mod_two] at heq
  exact heq

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Z]

theorem isClosed_space (hf : Continuous (uncurry f)) (hg : Continuous (uncurry g)) :
    IsClosed (space f g) :=
  (isClosed_Icc.preimage continuous_fst).inter
    (isClosed_eq (hf.comp (continuous_fst.prodMk continuous_snd.fst))
      (hg.comp (continuous_fst.prodMk continuous_snd.snd)))

theorem isCompact_space [CompactSpace X] [CompactSpace Y]
    (hf : Continuous (uncurry f)) (hg : Continuous (uncurry g)) :
    IsCompact (space f g) :=
  (isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set (X × Y)))).of_isClosed_subset
    (isClosed_space f g hf hg) (fun _ hp ↦ ⟨hp.1, mem_univ _⟩)

theorem compactSpace_space [CompactSpace X] [CompactSpace Y]
    (hf : Continuous (uncurry f)) (hg : Continuous (uncurry g)) :
    CompactSpace (space f g) := isCompact_iff_compactSpace.mp (isCompact_space f g hf hg)

omit [TopologicalSpace Z] [T2Space Z] in
theorem isClosed_ends : IsClosed (ends f g) :=
  (isClosed_eq continuous_subtype_val.fst continuous_const).union
    (isClosed_eq continuous_subtype_val.fst continuous_const)

/-- A genuine half-line atlas on the actual trace, with precisely the time ends
as its zero locus, implies equality of the actual endpoint intersection counts. -/
theorem parity_eq_of_halfLine_atlas [CompactSpace X] [CompactSpace Y]
    [T2Space X] [T2Space Y]
    (hf : Continuous (uncurry f)) (hg : Continuous (uncurry g))
    (h0 : (pairs (f 0) (g 0)).Finite) (h1 : (pairs (f 1) (g 1)).Finite)
    (e : space f g → OpenPartialHomeomorph (space f g) HalfLine)
    (he : ∀ p, p ∈ (e p).source)
    (hB : ∀ p, ∀ q ∈ (e p).source, (e p q).val = 0 ↔ q ∈ ends f g) :
    parity (f 0) (g 0) = parity (f 1) (g 1) := by
  let := compactSpace_space f g hf hg
  have h := CurveDecomposition.finite_even_boundary_of_compact_atlas (ends f g) e he hB
  exact parity_eq_of_even_ends f g h0 h1 h.2

end NoExoticSixSphere.IntersectionTrace
