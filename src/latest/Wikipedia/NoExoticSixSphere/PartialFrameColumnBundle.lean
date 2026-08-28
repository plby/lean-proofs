import Wikipedia.NoExoticSixSphere.PartialFrameColumnFiber
import Wikipedia.NoExoticSixSphere.OrthogonalColumnBundle

/-!
# Two-chart trivializations of the partial-frame column projection

The base chart is the whole unit sphere minus the antipode of its center.
The native trivialization has the actual operator-norm partial-frame space
as total space and the smaller partial-frame space as fiber. Two antipodal
centers cover the base. No abstract bundle or homotopy-type replacement is
assumed.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.ColumnBundle

open GLOrthonormalization Set Bundle
open OrthogonalColumnBundle (rotation rotation_apply)

variable {n r : ℕ}

def baseSet (c : UnitSphere (Vector (n + 1))) : Set (UnitSphere (Vector (n + 1))) :=
  {x | x ≠ antipode c}

theorem isOpen_baseSet (c : UnitSphere (Vector (n + 1))) : IsOpen (baseSet c) :=
  isClosed_singleton.isOpen_compl

theorem sum_ne_zero (c x : UnitSphere (Vector (n + 1))) (hx : x ∈ baseSet c) :
    c.val + x.val ≠ 0 := by
  intro h
  apply hx
  apply Subtype.ext
  change x.val = -c.val
  exact eq_neg_of_add_eq_zero_right h

theorem continuousOn_rotation (c : UnitSphere (Vector (n + 1))) :
    ContinuousOn (rotation c) (baseSet c) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hcol : Continuous (fun x : baseSet c ↦ x.val.val) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hc := continuous_localRotationOperator
    (fun _ : baseSet c ↦ c.val) (fun x : baseSet c ↦ x.val.val)
    continuous_const hcol (fun x ↦ ne_zero_of_mem_unit_sphere x.val)
    (fun x ↦ sum_ne_zero c x.val x.property)
  exact (hc.subtype_mk _).subtype_mk _

variable (v : UnitSphere (Vector (r + 1))) (c : UnitSphere (Vector (n + 1)))

def corrected (a : Space (n + 1) (r + 1)) : Space (n + 1) (r + 1) :=
  action (OrthogonalPaths.inverse (rotation c (column v a))) a

theorem corrected_column (a : Space (n + 1) (r + 1)) :
    (corrected v c a).val v.val = c.val := by
  change (OrthogonalPaths.inverse (rotation c (column v a))).val.val (column v a).val = _
  rw [← rotation_apply c (column v a)]
  exact OrthogonalPaths.inverse_apply_self _ _

def toCoordinates (a : Space (n + 1) (r + 1)) :
    UnitSphere (Vector (n + 1)) × Space n r :=
  (column v a, ColumnFiber.residual v c (corrected v c a) (corrected_column v c a))

def fromCoordinates (p : UnitSphere (Vector (n + 1)) × Space n r) :
    Space (n + 1) (r + 1) :=
  action (rotation c p.1) (ColumnFiber.reconstruct v c p.2)

theorem column_fromCoordinates (p : UnitSphere (Vector (n + 1)) × Space n r) :
    column v (fromCoordinates v c p) = p.1 := by
  apply Subtype.ext
  change (action (rotation c p.1) (ColumnFiber.reconstruct v c p.2)).val v.val = _
  rw [action_apply, ColumnFiber.reconstruct_column, rotation_apply]

theorem corrected_fromCoordinates (p : UnitSphere (Vector (n + 1)) × Space n r) :
    corrected v c (fromCoordinates v c p) = ColumnFiber.reconstruct v c p.2 := by
  rw [corrected, column_fromCoordinates, fromCoordinates, ← action_mul,
    OrthogonalPaths.inverse_mul, action_identity]

theorem fromCoordinates_toCoordinates (a : Space (n + 1) (r + 1)) :
    fromCoordinates v c (toCoordinates v c a) = a := by
  change action (rotation c (column v a))
    (ColumnFiber.reconstruct v c
      (ColumnFiber.residual v c (corrected v c a) (corrected_column v c a))) = a
  rw [ColumnFiber.reconstruct_residual, corrected, ← action_mul,
    OrthogonalPaths.mul_inverse, action_identity]

theorem toCoordinates_fromCoordinates (p : UnitSphere (Vector (n + 1)) × Space n r) :
    toCoordinates v c (fromCoordinates v c p) = p := by
  apply Prod.ext
  · exact column_fromCoordinates v c p
  · change ColumnFiber.residual v c (corrected v c (fromCoordinates v c p))
      (corrected_column v c (fromCoordinates v c p)) = p.2
    simp only [corrected_fromCoordinates, ColumnFiber.residual_reconstruct]

variable {X : Type*} [TopologicalSpace X]

theorem continuous_corrected (a : X → Space (n + 1) (r + 1)) (ha : Continuous a)
    (hcol : ∀ x, column v (a x) ∈ baseSet c) : Continuous (fun x ↦ corrected v c (a x)) := by
  have hrot := (continuousOn_rotation c).comp_continuous ((column v).continuous.comp ha) hcol
  exact continuous_action _ _ (OrthogonalPaths.continuous_inverse _ hrot) ha

theorem continuous_toCoordinates (a : X → Space (n + 1) (r + 1)) (ha : Continuous a)
    (hcol : ∀ x, column v (a x) ∈ baseSet c) :
    Continuous (fun x ↦ toCoordinates v c (a x)) :=
  ((column v).continuous.comp ha).prodMk
    (ColumnFiber.continuous_residual v c (fun x ↦ corrected v c (a x))
      (continuous_corrected v c a ha hcol) (fun x ↦ corrected_column v c (a x)))

theorem continuous_fromCoordinates (p : X → UnitSphere (Vector (n + 1)) × Space n r)
    (hp : Continuous p) (hcol : ∀ x, (p x).1 ∈ baseSet c) :
    Continuous (fun x ↦ fromCoordinates v c (p x)) :=
  continuous_action _ _ ((continuousOn_rotation c).comp_continuous hp.fst hcol)
    (ColumnFiber.continuous_reconstruct v c (fun x ↦ (p x).2) hp.snd)

def trivialization : Trivialization (Space n r) (column (n := n + 1) v) where
  toFun := toCoordinates v c
  invFun := fromCoordinates v c
  source := (column v) ⁻¹' baseSet c
  target := baseSet c ×ˢ univ
  map_source' _ ha := ⟨ha, mem_univ _⟩
  map_target' p hp := by
    change column v (fromCoordinates v c p) ∈ baseSet c
    rw [column_fromCoordinates]
    exact hp.1
  left_inv' a _ := fromCoordinates_toCoordinates v c a
  right_inv' p _ := toCoordinates_fromCoordinates v c p
  open_source := (isOpen_baseSet c).preimage (column v).continuous
  open_target := (isOpen_baseSet c).prod isOpen_univ
  continuousOn_toFun := continuousOn_iff_continuous_domRestrict.mpr
    (continuous_toCoordinates v c Subtype.val continuous_subtype_val Subtype.property)
  continuousOn_invFun := continuousOn_iff_continuous_domRestrict.mpr
    (continuous_fromCoordinates v c Subtype.val continuous_subtype_val (fun p ↦ p.2.1))
  baseSet := baseSet c
  open_baseSet := isOpen_baseSet c
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

theorem antipode_ne (c : UnitSphere (Vector (n + 1))) : antipode c ≠ c := by
  intro h
  have he : -c.val = c.val := congrArg Subtype.val h
  have hz : c.val = 0 := by
    have ht : (2 : ℝ) • c.val = 0 := by
      calc
        (2 : ℝ) • c.val = c.val + c.val := two_smul ℝ c.val
        _ = -c.val + c.val := congrArg (fun z ↦ z + c.val) he.symm
        _ = 0 := neg_add_cancel _
    exact (smul_eq_zero.mp ht).resolve_left (by norm_num)
  exact ne_zero_of_mem_unit_sphere c hz

theorem center_mem_baseSet : c ∈ (trivialization v c).baseSet :=
  (antipode_ne c).symm

theorem baseSets_cover : baseSet c ∪ baseSet (antipode c) = univ := by
  apply eq_univ_of_forall
  intro x
  by_cases hx : x = antipode c
  · right
    change x ≠ antipode (antipode c)
    rw [hx]
    exact (antipode_ne (antipode c)).symm
  · exact Or.inl hx

theorem sources_cover : (trivialization v c).source ∪
    (trivialization v (antipode c)).source = univ := by
  change (column v) ⁻¹' baseSet c ∪ (column v) ⁻¹' baseSet (antipode c) = univ
  rw [← preimage_union, baseSets_cover, preimage_univ]

def sourceHomeomorph : ((column v) ⁻¹' baseSet c) ≃ₜ baseSet c × Space n r :=
  (trivialization v c).sourceHomeomorphBaseSetProd

end NoExoticSixSphere.Stiefel.ColumnBundle
