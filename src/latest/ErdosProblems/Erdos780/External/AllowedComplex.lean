import ErdosProblems.Erdos780.External.AllowedFaces
import ErdosProblems.Erdos780.External.PositiveTarget
import ErdosProblems.Erdos780.External.TargetOrbits
import ErdosProblems.Erdos780.External.LabelChainMap
import ErdosProblems.Erdos780.External.SignedSphereLength

/-!
The normalized (nonempty) simplicial chain complex on the allowed target
faces.  `TargetOrbits.TotalChain` is the coefficient model used by the orbit
calculation; `PositiveAllowed` is the same module inside the exterior-algebra
positive target chains.
-/

namespace AllowedComplex

open TargetChains

noncomputable section

variable {p m alpha : ℕ} [NeZero p]

abbrev Vertex (p m : ℕ) := ZMod p × Fin m

noncomputable local instance targetOrder : LinearOrder (Vertex p m) :=
  LabelChainMap.targetLinearOrder

theorem targetAllowed_iff (s : Finset (Vertex p m)) :
    TargetOrbits.Allowed alpha s ↔ AllowedFaces.IsAllowed alpha s := by
  rfl

/-! ## Basis faces and downward closure -/

/-- Increasing enumeration of a finite target face.  The `List.ofFn` form
keeps its length definitionally tied to `s.card`, which is convenient for the
exterior basis. -/
noncomputable def faceList (s : Finset (Vertex p m)) : List (Vertex p m) :=
  List.ofFn (fun i : Fin s.card ↦ s.orderEmbOfFin rfl i)

@[simp] theorem faceList_length (s : Finset (Vertex p m)) :
    (faceList s).length = s.card := by simp [faceList]

@[simp] theorem faceList_toFinset (s : Finset (Vertex p m)) :
    (faceList s).toFinset = s := by
  ext v
  simp only [faceList, List.mem_toFinset, List.mem_ofFn]
  change v ∈ Set.range (s.orderEmbOfFin rfl) ↔ v ∈ (s : Set (Vertex p m))
  rw [Finset.range_orderEmbOfFin]

/-- Left exterior multiplication by one vertex sends a basis face to an
integer multiple of the basis of the inserted face. -/
theorem wedgePrepend_single_exists
    {V : Type*} [Fintype V] [LinearOrder V]
    (v : V) (s : Finset V) :
    ∃ z : ℤ, TargetBridge.wedgePrepend v
        (Finsupp.single s (1 : ℤ)) =
      z • Finsupp.single (insert v s) (1 : ℤ) := by
  by_cases hvs : v ∈ s
  · refine ⟨0, ?_⟩
    have hprod :
        TargetChains.exteriorBasis ℤ V {v} *
          TargetChains.exteriorBasis ℤ V s = 0 := by
      let sv : Set.powersetCard V 1 := ⟨{v}, by simp⟩
      let ss : Set.powersetCard V s.card := ⟨s, rfl⟩
      apply ExteriorAlgebra.basis_mul_of_not_disjoint
        (TargetChains.vertexBasis ℤ V) sv ss
      simpa [sv, ss, Finset.disjoint_singleton_left]
    simp only [zero_smul]
    apply (TargetChains.toExterior ℤ V).injective
    rw [map_zero, TargetBridge.toExterior_wedgePrepend,
      TargetChains.toExterior_single, one_smul,
      PositiveTarget.iota_single_eq_exteriorBasis_singleton, hprod]
  · let sv : Set.powersetCard V 1 := ⟨{v}, by simp⟩
    let ss : Set.powersetCard V s.card := ⟨s, rfl⟩
    have hd : Disjoint sv.val ss.val := by
      simpa [sv, ss, Finset.disjoint_singleton_left]
    refine ⟨(Set.powersetCard.permOfDisjoint hd).sign, ?_⟩
    apply (TargetChains.toExterior ℤ V).injective
    rw [TargetBridge.toExterior_wedgePrepend,
      TargetChains.toExterior_single, one_smul,
      PositiveTarget.iota_single_eq_exteriorBasis_singleton]
    change (TargetChains.vertexBasis ℤ V).ExteriorAlgebra sv.val *
        (TargetChains.vertexBasis ℤ V).ExteriorAlgebra ss.val = _
    rw [ExteriorAlgebra.basis_mul_of_disjoint
      (TargetChains.vertexBasis ℤ V) sv ss hd]
    simp [sv, ss, TargetChains.exteriorBasis,
      Set.powersetCard.disjUnion, Units.smul_def, Algebra.smul_def]

/-- A list label has a single possible exterior coordinate, namely the
unordered set of labels.  Repetitions are absorbed by the integer coefficient
being zero. -/
theorem labelList_eq_smul_single_toFinset
    {X V : Type*} [Fintype V] [LinearOrder V]
    (lab : X → V) (l : List X) :
    ∃ z : ℤ, TargetBridge.labelList lab l =
      z • Finsupp.single (l.map lab).toFinset (1 : ℤ) := by
  induction l with
  | nil =>
      refine ⟨1, ?_⟩
      rw [PositiveTarget.labelList_nil_eq_single_empty]
      simp
  | cons x xs ih =>
      obtain ⟨z, hz⟩ := ih
      obtain ⟨w, hw⟩ := wedgePrepend_single_exists (lab x)
        (xs.map lab).toFinset
      refine ⟨z * w, ?_⟩
      rw [TargetBridge.labelList, hz, map_smul, hw]
      simp [smul_smul]

/-- Positive target chains whose nonzero faces satisfy the capacity bounds. -/
noncomputable def PositiveAllowed (p m alpha : ℕ) [NeZero p] :
    Submodule ℤ (PositiveTarget.Chain ℤ (Vertex p m)) :=
  (AllowedFaces.allowedChains ℤ p m alpha).comap
    (TargetChains.positiveInclusion ℤ (Vertex p m))

theorem mem_positiveAllowed
    (c : PositiveTarget.Chain ℤ (Vertex p m)) :
    c ∈ PositiveAllowed p m alpha ↔
      ∀ s ∈ (c : TargetChains.FullChain ℤ (Vertex p m)).support,
        AllowedFaces.IsAllowed alpha s := by
  rw [PositiveAllowed, Submodule.mem_comap,
    AllowedFaces.mem_allowedChains]
  rfl

/-- The corresponding supported submodule of the full coefficient module.
The predicate includes nonemptiness, so no augmentation coordinate occurs. -/
noncomputable def NonemptyAllowed (p m alpha : ℕ) [NeZero p] :
    Submodule ℤ (TargetChains.FullChain ℤ (Vertex p m)) :=
  Finsupp.supported ℤ ℤ
    {s | s.Nonempty ∧ AllowedFaces.IsAllowed alpha s}

theorem mem_nonemptyAllowed
    (c : TargetChains.FullChain ℤ (Vertex p m)) :
    c ∈ NonemptyAllowed p m alpha ↔
      ∀ s ∈ c.support,
        s.Nonempty ∧ AllowedFaces.IsAllowed alpha s := by
  rw [NonemptyAllowed, Finsupp.mem_supported]
  constructor
  · intro h s hs
    exact h hs
  · intro h s hs
    exact h s hs

/-- Forgetting the positive-chain subtype identifies positive allowed chains
with full chains supported on nonempty allowed faces. -/
noncomputable def positiveAllowedEquivSupported :
    PositiveAllowed p m alpha ≃ₗ[ℤ] NonemptyAllowed p m alpha := by
  let f : PositiveAllowed p m alpha →ₗ[ℤ]
      TargetChains.FullChain ℤ (Vertex p m) :=
    (TargetChains.positiveInclusion ℤ (Vertex p m)).comp
      (PositiveAllowed p m alpha).subtype
  let g : PositiveAllowed p m alpha →ₗ[ℤ] NonemptyAllowed p m alpha :=
    f.codRestrict (NonemptyAllowed p m alpha) (by
      intro c
      rw [mem_nonemptyAllowed]
      intro s hs
      constructor
      · rw [Finset.nonempty_iff_ne_empty]
        intro hse
        subst s
        have hc0 : ((c.1 : PositiveTarget.Chain ℤ (Vertex p m)) :
            TargetChains.FullChain ℤ (Vertex p m)) ∅ = 0 := by
          have hker := c.1.property
          change Finsupp.lapply ∅
            ((c.1 : PositiveTarget.Chain ℤ (Vertex p m)) :
              TargetChains.FullChain ℤ (Vertex p m)) = 0 at hker
          simpa using hker
        exact (Finsupp.mem_support_iff.mp hs) hc0
      · exact (mem_positiveAllowed c.1).1 c.2 s hs)
  refine LinearEquiv.ofBijective g ⟨?_, ?_⟩
  · intro x y h
    have hfull :
        (g x : TargetChains.FullChain ℤ (Vertex p m)) = g y :=
      congrArg (fun z : NonemptyAllowed p m alpha ↦
        (z.1 : TargetChains.FullChain ℤ (Vertex p m))) h
    exact Subtype.ext (Subtype.ext hfull)
  · intro c
    have hc0 : (c.1 : TargetChains.FullChain ℤ (Vertex p m)) ∅ = 0 := by
      by_contra h
      have hempty : (∅ : Finset (Vertex p m)) ∈ c.1.support :=
        Finsupp.mem_support_iff.mpr h
      exact ((mem_nonemptyAllowed c.1).1 c.2 ∅ hempty).1.ne_empty rfl
    let pc : PositiveTarget.Chain ℤ (Vertex p m) :=
      ⟨c.1, by
        change Finsupp.lapply ∅
          (c.1 : TargetChains.FullChain ℤ (Vertex p m)) = 0
        simpa using hc0⟩
    have hpa : pc ∈ PositiveAllowed p m alpha := by
      rw [mem_positiveAllowed]
      intro s hs
      exact ((mem_nonemptyAllowed c.1).1 c.2 s hs).2
    refine ⟨⟨pc, hpa⟩, ?_⟩
    apply Subtype.ext
    rfl

/-- The two files' definitionally equivalent allowed-face predicates induce
an equivalence of their nonempty face subtypes. -/
noncomputable def positivePredicateEquiv :
    TargetOrbits.PositiveAllowedFinset p m alpha ≃
      {s : Finset (Vertex p m) //
        s.Nonempty ∧ AllowedFaces.IsAllowed alpha s} where
  toFun s := ⟨s.1, s.2.1, (targetAllowed_iff s.1).1 s.2.2⟩
  invFun s := ⟨s.1, s.2.1, (targetAllowed_iff s.1).2 s.2.2⟩
  left_inv s := Subtype.ext rfl
  right_inv s := Subtype.ext rfl

/-- The orbit-indexed total face basis, with the duplicate target predicate
replaced by `AllowedFaces.IsAllowed`. -/
noncomputable def totalFaceEquivNonemptyAllowed :
    TargetOrbits.TotalFace p m alpha ≃
      {s : Finset (Vertex p m) //
        s.Nonempty ∧ AllowedFaces.IsAllowed alpha s} :=
  (TargetOrbits.totalFaceEquivPositive p m alpha).trans
    (positivePredicateEquiv (p := p) (m := m) (alpha := alpha))

/-- Canonical coefficient equivalence between orbit/descent total chains and
the positive allowed submodule of the normalized target complex. -/
noncomputable def totalChainEquivPositiveAllowed :
    TargetOrbits.TotalChain p m alpha ≃ₗ[ℤ] PositiveAllowed p m alpha :=
  (Finsupp.lcongr (totalFaceEquivNonemptyAllowed (p := p) (m := m)
      (alpha := alpha)) (LinearEquiv.refl ℤ ℤ)).trans
    ((Finsupp.supportedEquivFinsupp
      {s : Finset (Vertex p m) |
        s.Nonempty ∧ AllowedFaces.IsAllowed alpha s}).symm.trans
      (positiveAllowedEquivSupported (p := p) (m := m)
        (alpha := alpha)).symm)

end

end AllowedComplex
