import Wikipedia.HopfProblem.EllipticFillingTopologyFundamentalGroup

/-!
# Restricting a strong deformation retract to an invariant subset

If a subset contains the retract and is preserved throughout the
deformation, the same deformation descends to its actual subtype topology.
This applies in particular to the open and closed radius tubes in the
elliptic filling.
-/

noncomputable section

namespace Wikipedia.HopfProblem

variable {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]

/-- Regard the retract inclusion as a continuous map into a subset
containing its image. -/
def restrictedRetractionInclusion (i : C(A, X)) (K : Set X)
    (hinc : Set.range i ⊆ K) : C(A, K) where
  toFun a := ⟨i a, hinc ⟨a, rfl⟩⟩
  continuous_toFun := i.continuous.subtype_mk _

@[simp] theorem restrictedRetractionInclusion_coe (i : C(A, X)) (K : Set X)
    (hinc : Set.range i ⊆ K) (a : A) :
    (restrictedRetractionInclusion i K hinc a : X) = i a := rfl

/-- Restrict the domain of the retraction to the actual subset subtype. -/
def restrictedRetraction (r : C(X, A)) (K : Set X) : C(K, A) where
  toFun x := r x
  continuous_toFun := r.continuous.comp continuous_subtype_val

@[simp] theorem restrictedRetraction_apply (r : C(X, A)) (K : Set X) (x : K) :
    restrictedRetraction r K x = r x := rfl

/-- The retraction identity is unchanged by restricting the ambient space. -/
theorem restrictedRetraction_comp_inclusion (i : C(A, X)) (r : C(X, A))
    (hir : r.comp i = ContinuousMap.id A) (K : Set X) (hinc : Set.range i ⊆ K) :
    (restrictedRetraction r K).comp (restrictedRetractionInclusion i K hinc) =
      ContinuousMap.id A := by
  ext a
  exact retraction_leftInverse i r hir a

/-- A deformation preserving the subset restricts to a relative homotopy
on its actual subtype, fixing the restricted inclusion pointwise. -/
def restrictedRetractionHomotopy (i : C(A, X)) (r : C(X, A))
    (H : (ContinuousMap.id X).HomotopyRel (i.comp r) (Set.range i))
    (K : Set X) (hinc : Set.range i ⊆ K)
    (hstable : ∀ t x, x ∈ K → H (t, x) ∈ K) :
    (ContinuousMap.id K).HomotopyRel
      ((restrictedRetractionInclusion i K hinc).comp (restrictedRetraction r K))
      (Set.range (restrictedRetractionInclusion i K hinc)) where
  toFun tx := ⟨H (tx.1, tx.2.val), hstable tx.1 tx.2.val tx.2.property⟩
  continuous_toFun := (H.continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left x := Subtype.ext (H.map_zero_left x.val)
  map_one_left x := Subtype.ext (H.map_one_left x.val)
  prop' t x hx := by
    apply Subtype.ext
    apply H.eq_fst t
    obtain ⟨a, rfl⟩ := hx
    exact ⟨a, rfl⟩

@[simp] theorem restrictedRetractionHomotopy_coe (i : C(A, X)) (r : C(X, A))
    (H : (ContinuousMap.id X).HomotopyRel (i.comp r) (Set.range i))
    (K : Set X) (hinc : Set.range i ⊆ K)
    (hstable : ∀ t x, x ∈ K → H (t, x) ∈ K) (t : unitInterval) (x : K) :
    (restrictedRetractionHomotopy i r H K hinc hstable (t, x) : X) =
      H (t, x.val) := rfl

/-- The retract and every deformation-invariant subset containing it are
homotopy equivalent through the actual restricted maps. -/
def restrictedRetractionHomotopyEquiv (i : C(A, X)) (r : C(X, A))
    (hir : r.comp i = ContinuousMap.id A)
    (H : (ContinuousMap.id X).HomotopyRel (i.comp r) (Set.range i))
    (K : Set X) (hinc : Set.range i ⊆ K)
    (hstable : ∀ t x, x ∈ K → H (t, x) ∈ K) :
    ContinuousMap.HomotopyEquiv A K :=
  retractionHomotopyEquiv (restrictedRetractionInclusion i K hinc)
    (restrictedRetraction r K) (restrictedRetraction_comp_inclusion i r hir K hinc)
    (restrictedRetractionHomotopy i r H K hinc hstable)

/-- The actual restricted inclusion induces an isomorphism of pointed
fundamental groups. -/
def restrictedRetractionFundamentalGroupEquiv (i : C(A, X)) (r : C(X, A))
    (hir : r.comp i = ContinuousMap.id A)
    (H : (ContinuousMap.id X).HomotopyRel (i.comp r) (Set.range i))
    (K : Set X) (hinc : Set.range i ⊆ K)
    (hstable : ∀ t x, x ∈ K → H (t, x) ∈ K) (a : A) :
    FundamentalGroup A a ≃*
      FundamentalGroup K (restrictedRetractionInclusion i K hinc a) :=
  retractionFundamentalGroupEquiv (restrictedRetractionInclusion i K hinc)
    (restrictedRetraction r K) (restrictedRetraction_comp_inclusion i r hir K hinc)
    (restrictedRetractionHomotopy i r H K hinc hstable) a

@[simp] theorem restrictedRetractionFundamentalGroupEquiv_toMonoidHom
    (i : C(A, X)) (r : C(X, A)) (hir : r.comp i = ContinuousMap.id A)
    (H : (ContinuousMap.id X).HomotopyRel (i.comp r) (Set.range i))
    (K : Set X) (hinc : Set.range i ⊆ K)
    (hstable : ∀ t x, x ∈ K → H (t, x) ∈ K) (a : A) :
    (restrictedRetractionFundamentalGroupEquiv i r hir H K hinc hstable a).toMonoidHom =
      FundamentalGroup.map (restrictedRetractionInclusion i K hinc) a := rfl

end Wikipedia.HopfProblem
