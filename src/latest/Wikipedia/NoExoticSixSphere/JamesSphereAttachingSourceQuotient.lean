import Wikipedia.NoExoticSixSphere.JamesSphereAttachingFacesContraction
import Wikipedia.NoExoticSixSphere.ContractedQuotientNativeHomotopy
import Wikipedia.NoExoticSixSphere.CollapsedSubspaceSeparation

/-!
# The actual attaching-source quotient preserves native homotopy groups

Extend the constructed contraction of the discarded faces using their
proved homotopy-extension property. Its full prescribed face tracks
remain visible. The literal collapse therefore induces bijections on
all native homotopy classes, and the original attaching map factors
through that collapse up to an actual based homotopy. Identification
of this quotient with the suspended smash sphere is a separate step.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace NoExoticSixSphere.JamesSphere.AttachingSquare

theorem exists_sourceExtension (n : ℕ) :
    ∃ L : C(I × fullBoundary n, fullBoundary n),
      (∀ x, L (0, x) = x) ∧
      ∀ (t : I) (p : collapsedFaces n), L (t, p.val) = (collapsedContraction n (t, p)).val := by
  let G : C(I × collapsedFaces n, fullBoundary n) :=
    (⟨Subtype.val, continuous_subtype_val⟩ : C(collapsedFaces n, fullBoundary n)).comp
      (collapsedContraction n).toContinuousMap
  have hG : ∀ p : collapsedFaces n, G (0, p) = p.val :=
    fun p ↦ congrArg Subtype.val ((collapsedContraction n).map_zero_left p)
  exact collapsedFaces_hasHomotopyExtension n (TopCat.of (fullBoundary n))
    (ContinuousMap.id _) G hG

def sourceExtension (n : ℕ) : C(I × fullBoundary n, fullBoundary n) :=
  Classical.choose (exists_sourceExtension n)

theorem sourceExtension_zero (n : ℕ) (p : fullBoundary n) : sourceExtension n (0, p) = p :=
  (Classical.choose_spec (exists_sourceExtension n)).1 p

theorem sourceExtension_faces (n : ℕ) (t : I) (p : collapsedFaces n) :
    sourceExtension n (t, p.val) = (collapsedContraction n (t, p)).val :=
  (Classical.choose_spec (exists_sourceExtension n)).2 t p

def sourceEndpoint (n : ℕ) : C(fullBoundary n, fullBoundary n) :=
  (sourceExtension n).comp ⟨fun p ↦ (1, p), continuous_const.prodMk continuous_id⟩

theorem sourceEndpoint_faces (n : ℕ) (p : collapsedFaces n) :
    sourceEndpoint n p.val = fullPoint n := by
  change sourceExtension n (1, p.val) = fullPoint n
  rw [sourceExtension_faces]
  exact congrArg Subtype.val ((collapsedContraction n).map_one_left p)

def sourceHomotopy (n : ℕ) :
    (ContinuousMap.id (fullBoundary n)).HomotopyRel (sourceEndpoint n) {fullPoint n} where
  toContinuousMap := sourceExtension n
  map_zero_left := sourceExtension_zero n
  map_one_left _ := rfl
  prop' := by
    intro t p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    change sourceExtension n (t, (collapsedPoint n).val) = (collapsedPoint n).val
    rw [sourceExtension_faces]
    exact congrArg Subtype.val ((collapsedContraction n).prop t _ (Set.mem_singleton _))

theorem sourceHomotopy_preserves (n : ℕ) (t : I) (p : fullBoundary n)
    (hp : p ∈ collapsedFaces n) : sourceHomotopy n (t, p) ∈ collapsedFaces n := by
  change sourceExtension n (t, (⟨p, hp⟩ : collapsedFaces n).val) ∈ collapsedFaces n
  rw [sourceExtension_faces]
  exact (collapsedContraction n (t, ⟨p, hp⟩)).property

abbrev SourceQuotient (n : ℕ) := CollapsedSubspace.Space (collapsedFaces n)

instance (n : ℕ) : T2Space (SourceQuotient n) :=
  CollapsedSubspace.t2Space (collapsedFaces n) (isClosed_collapsedFaces n).isCompact

def sourceCollapse (n : ℕ) : C(fullBoundary n, SourceQuotient n) :=
  CollapsedSubspace.quotientMap (collapsedFaces n)

def sourcePoint (n : ℕ) : SourceQuotient n := sourceCollapse n (fullPoint n)

theorem sourceCollapse_map_bijective (n : ℕ) (N : Type*) :
    Function.Bijective (HigherHomotopy.map (N := N) (sourceCollapse n) (y := fullPoint n) rfl) :=
  ContractedQuotient.map_bijective_of_fixed_contraction (sourceCollapse n)
    (CollapsedSubspace.isQuotientMap (collapsedFaces n)) (collapsedFaces n)
    (CollapsedSubspace.quotientMap_eq_iff (collapsedFaces n))
    (fullPoint n) (collapsedPoint n).property
    (fun x hx ↦ sourceEndpoint_faces n ⟨x, hx⟩) (sourceHomotopy n)
    (sourceHomotopy_preserves n)

def sourceCollapseHom (n d : ℕ) [NeZero d] :
    π_ d (fullBoundary n) (fullPoint n) →* π_ d (SourceQuotient n) (sourcePoint n) :=
  HigherHomotopy.mapMonoidHom (sourceCollapse n) rfl

def sourceCollapseEquiv (n d : ℕ) [NeZero d] :
    π_ d (fullBoundary n) (fullPoint n) ≃* π_ d (SourceQuotient n) (sourcePoint n) :=
  MulEquiv.ofBijective (sourceCollapseHom n d) (sourceCollapse_map_bijective n (Fin d))

theorem sourceAttaching_constant (n : ℕ) (p : fullBoundary n) (hp : p ∈ collapsedFaces n) :
    fullAttaching n (sourceEndpoint n p) = spherePole (n + 1) := by
  rw [sourceEndpoint_faces n ⟨p, hp⟩, fullAttaching_point]

def sourceQuotientAttaching (n : ℕ) : C(SourceQuotient n, Sphere (n + 1)) :=
  CollapsedSubspace.lift (collapsedFaces n) ((fullAttaching n).comp (sourceEndpoint n))
    (fun p hp q hq ↦ (sourceAttaching_constant n p hp).trans
      (sourceAttaching_constant n q hq).symm)

theorem sourceQuotientAttaching_collapse (n : ℕ) (p : fullBoundary n) :
    sourceQuotientAttaching n (sourceCollapse n p) = fullAttaching n (sourceEndpoint n p) := rfl

theorem sourceQuotientAttaching_point (n : ℕ) :
    sourceQuotientAttaching n (sourcePoint n) = spherePole (n + 1) :=
  sourceAttaching_constant n (fullPoint n) (collapsedPoint n).property

def sourceAttachingHomotopy (n : ℕ) :
    (fullAttaching n).HomotopyRel
      ((sourceQuotientAttaching n).comp (sourceCollapse n)) {fullPoint n} :=
  ((sourceHomotopy n).compContinuousMap (fullAttaching n)).cast rfl
    (ContinuousMap.ext (fun p ↦ (sourceQuotientAttaching_collapse n p).symm))

end NoExoticSixSphere.JamesSphere.AttachingSquare
