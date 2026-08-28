import Wikipedia.HopfProblem.MappingTorusHomologyCover
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleDisjoint

/-!
# Actual retractions and inclusion homotopies for a mapping torus

Each arc chart contracts its real coordinate, keeping the fibre coordinate
fixed. After inclusion in the mapping torus, both contractions end at the
same actual fibre inclusion at time zero. On the intersection, the first
projection is the fold and the second is the fold twisted by `f` on the
upper component.
-/

noncomputable section

open Set ContinuousMap

namespace Wikipedia.HopfProblem.MappingTorus.HomologyCover

open PeriodTorusHigherHomology PeriodTorusHigherHomology.CircleTopology

variable {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)

/-- Inclusion of the genuine fibre over the circle origin. -/
def fibreInclusion : C(X, Torus f) :=
  ⟨fun x => mk f (0, x), (mk_continuous f).comp (continuous_const.prodMk continuous_id)⟩

@[simp] theorem fibreInclusion_apply (x : X) : fibreInclusion f x = mk f (0, x) := rfl

/-- Moving once through the actual cylinder realizes the endpoint gluing
by `f`, fixing the monodromy convention independently of homology. -/
def fibreMonodromyHomotopy : (fibreInclusion f).Homotopy
    ((fibreInclusion f).comp (f : C(X, X))) where
  toFun p := mk f ((p.1 : ℝ), p.2)
  continuous_toFun := (mk_continuous f).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  map_zero_left _ := rfl
  map_one_left x := by simpa [fibreInclusion] using mk_add_one f 0 x

/-- An actual lift to the infinite cylinder contracts to its time-zero fibre coordinate. -/
def liftContraction {S : Type} [TopologicalSpace S]
    (q : C(S, Torus f)) (l : C(S, ℝ × X))
    (hl : ∀ s, mk f (l s) = q s) :
    q.Homotopy ((fibreInclusion f).comp (ContinuousMap.snd.comp l)) where
  toFun p := mk f ((1 - (p.1 : ℝ)) * (l p.2).1, (l p.2).2)
  continuous_toFun := (mk_continuous f).comp
    (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (l.continuous.fst.comp continuous_snd)).prodMk
        (l.continuous.snd.comp continuous_snd))
  map_zero_left s := by simpa using hl s
  map_one_left s := by simp [fibreInclusion]

/-- The actual cylinder lift on the first open member. -/
def liftU : C(U f, ℝ × X) :=
  ⟨fun q => (((chartU f q).1 : ℝ), (chartU f q).2),
    (continuous_subtype_val.comp (chartU f).continuous.fst).prodMk
      (chartU f).continuous.snd⟩

/-- The actual cylinder lift on the second open member. -/
def liftV : C(V f, ℝ × X) :=
  ⟨fun q => (((chartV f q).1 : ℝ), (chartV f q).2),
    (continuous_subtype_val.comp (chartV f).continuous.fst).prodMk
      (chartV f).continuous.snd⟩

/-- Projection in the first actual interval chart is a homotopy equivalence. -/
def homotopyEquivU : U f ≃ₕ X := by
  letI : ContractibleSpace (Ioo (0 : ℝ) 1) := intervalContractible 0 1 zero_lt_one
  exact (chartU f).toHomotopyEquiv.trans
    (contractibleProdHomotopyEquiv (Ioo (0 : ℝ) 1) X)

/-- Projection in the second actual interval chart is a homotopy equivalence. -/
def homotopyEquivV : V f ≃ₕ X := by
  letI : ContractibleSpace (Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
    intervalContractible _ _ (by norm_num)
  exact (chartV f).toHomotopyEquiv.trans
    (contractibleProdHomotopyEquiv (Ioo (-(1 / 2 : ℝ)) (1 / 2)) X)

@[simp] theorem homotopyEquivU_apply (q : U f) :
    homotopyEquivU f q = (chartU f q).2 := rfl

@[simp] theorem homotopyEquivV_apply (q : V f) :
    homotopyEquivV f q = (chartV f q).2 := rfl

/-- The genuine first open inclusion contracts to the fixed fibre inclusion. -/
def inclusionUHomotopy : (inclusionU f).Homotopy
    ((fibreInclusion f).comp (homotopyEquivU f).toFun) :=
  liftContraction f (inclusionU f) (liftU f) (chartU_representation f)

/-- The second open inclusion contracts to exactly the same fibre inclusion. -/
def inclusionVHomotopy : (inclusionV f).Homotopy
    ((fibreInclusion f).comp (homotopyEquivV f).toFun) :=
  liftContraction f (inclusionV f) (liftV f) (chartV_representation f)

/-- The actual intersection retracts to two copies of the fibre, lower component first. -/
def intersectionHomotopyEquiv : ↥(U f ∩ V f) ≃ₕ X ⊕ X :=
  (intersectionHomeomorph f).toHomotopyEquiv.trans
    (sumHomotopyEquiv
      (contractibleProdHomotopyEquiv (Ioo (0 : ℝ) (1 / 2)) X)
      (contractibleProdHomotopyEquiv (Ioo (1 / 2 : ℝ) 1) X))

@[simp] theorem intersectionHomotopyEquiv_inl
    (p : Ioo (0 : ℝ) (1 / 2) × X) :
    intersectionHomotopyEquiv f ((intersectionHomeomorph f).symm (Sum.inl p)) =
      Sum.inl p.2 := by
  change Sum.map (fun p : Ioo (0 : ℝ) (1 / 2) × X => p.2)
    (fun p : Ioo (1 / 2 : ℝ) 1 × X => p.2)
    (intersectionHomeomorph f ((intersectionHomeomorph f).symm (Sum.inl p))) = _
  rw [Homeomorph.apply_symm_apply]
  rfl

@[simp] theorem intersectionHomotopyEquiv_inr
    (p : Ioo (1 / 2 : ℝ) 1 × X) :
    intersectionHomotopyEquiv f ((intersectionHomeomorph f).symm (Sum.inr p)) =
      Sum.inr p.2 := by
  change Sum.map (fun p : Ioo (0 : ℝ) (1 / 2) × X => p.2)
    (fun p : Ioo (1 / 2 : ℝ) 1 × X => p.2)
    (intersectionHomeomorph f ((intersectionHomeomorph f).symm (Sum.inr p))) = _
  rw [Homeomorph.apply_symm_apply]
  rfl

/-- In the first open member, both actual intersection inclusions are the identity on the fibre. -/
theorem intersectionToU_fold :
    (homotopyEquivU f).toFun.comp (intersectionToU f) =
      (sumElimMap (ContinuousMap.id X) (ContinuousMap.id X)).comp
        (intersectionHomotopyEquiv f).toFun := by
  apply ContinuousMap.ext
  intro q
  obtain ⟨p, rfl⟩ := (intersectionHomeomorph f).symm.surjective q
  cases p with
  | inl p =>
    change (chartU f (intersectionToU f _)).2 =
      sumElimMap (ContinuousMap.id X) (ContinuousMap.id X) (intersectionHomotopyEquiv f _)
    rw [intersectionHomotopyEquiv_inl, chartU_intersection_inl]
    rfl
  | inr p =>
    change (chartU f (intersectionToU f _)).2 =
      sumElimMap (ContinuousMap.id X) (ContinuousMap.id X) (intersectionHomotopyEquiv f _)
    rw [intersectionHomotopyEquiv_inr, chartU_intersection_inr]
    rfl

/-- The upper overlap contributes the actual monodromy to the second open member. -/
theorem intersectionToV_twistedFold :
    (homotopyEquivV f).toFun.comp (intersectionToV f) =
      (sumElimMap (ContinuousMap.id X) (f : C(X, X))).comp
        (intersectionHomotopyEquiv f).toFun := by
  apply ContinuousMap.ext
  intro q
  obtain ⟨p, rfl⟩ := (intersectionHomeomorph f).symm.surjective q
  cases p with
  | inl p =>
    change (chartV f (intersectionToV f _)).2 =
      sumElimMap (ContinuousMap.id X) (f : C(X, X)) (intersectionHomotopyEquiv f _)
    rw [intersectionHomotopyEquiv_inl, chartV_intersection_inl]
    rfl
  | inr p =>
    change (chartV f (intersectionToV f _)).2 =
      sumElimMap (ContinuousMap.id X) (f : C(X, X)) (intersectionHomotopyEquiv f _)
    rw [intersectionHomotopyEquiv_inr, chartV_intersection_inr]
    rfl

end Wikipedia.HopfProblem.MappingTorus.HomologyCover
