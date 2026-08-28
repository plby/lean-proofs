import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionMaps
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Constructed local degree lifts in the Čech extension

On an open set contained in `U k`, an integer `n` lifts to the family
`b i = n • c i k`. These are actual sections of the extension presheaf.
The difference of the lifts indexed by `j` and `i` is `n • c i j` in
the original sheaf, fixing the sign of the resulting extension.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicPicard.CechExtension

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} X}
  {ι : Type} {U : ι → Opens X} (c : CechOneCocycle F U)

/-- A literal local splitting of the degree projection on `U k`. -/
def localLiftHom {V : Opens X} (k : ι) (hVk : V ≤ U k) :
    ULift.{0} ℤ →+ ExtensionSection c V where
  toFun n := ⟨⟨n, fun i => n.down •
    res F (le_inf inf_le_right (inf_le_left.trans hVk)) (c.value i k)⟩, by
    intro i j
    change res F _ (n.down • res F _ (c.value i k)) -
      res F _ (n.down • res F _ (c.value j k)) =
        n.down • res F _ (c.value i j)
    rw [map_zsmul, map_zsmul, res_trans, res_trans, ← smul_sub]
    apply congrArg (fun a => n.down • a)
    apply sub_eq_iff_eq_add.mpr
    exact (cocycle_condition_restrict c i j k
      (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)
      (inf_le_left.trans hVk)).symm⟩
  map_zero' := by
    apply extensionSection_ext
    · rfl
    · intro i
      exact zero_zsmul _
  map_add' n m := by
    apply extensionSection_ext
    · rfl
    · intro i
      exact add_zsmul _ _ _

@[simp] theorem localLiftHom_degree {V : Opens X} (k : ι) (hVk : V ≤ U k)
    (n : ULift.{0} ℤ) :
    degreeHom c V (localLiftHom c k hVk n) = n := rfl

@[simp] theorem localLiftHom_coordinate {V : Opens X} (k : ι) (hVk : V ≤ U k)
    (n : ULift.{0} ℤ) (i : ι) :
    coordinateHom c V i (localLiftHom c k hVk n) =
      n.down • res F (le_inf inf_le_right (inf_le_left.trans hVk)) (c.value i k) := rfl

/-- The constructed local lift is compatible with genuine restriction. -/
theorem restrict_localLiftHom {V W : Opens X} (hWV : W ≤ V)
    (k : ι) (hVk : V ≤ U k) (n : ULift.{0} ℤ) :
    restrict c hWV (localLiftHom c k hVk n) =
      localLiftHom c k (hWV.trans hVk) n := by
  apply extensionSection_ext
  · rfl
  · intro i
    change res F _ (n.down • res F _ (c.value i k)) =
      n.down • res F _ (c.value i k)
    rw [map_zsmul, res_trans]

/-- With the chosen convention, the `j` lift minus the `i` lift is
the inclusion of the original cocycle, with positive sign. -/
theorem localLiftHom_difference {V : Opens X} (i j : ι)
    (hi : V ≤ U i) (hj : V ≤ U j) (n : ULift.{0} ℤ) :
    localLiftHom c j hj n - localLiftHom c i hi n =
      includeHom c V (n.down • res F (le_inf hi hj) (c.value i j)) := by
  apply extensionSection_ext
  · exact sub_self n
  · intro k
    change n.down • res F _ (c.value k j) - n.down • res F _ (c.value k i) =
      res F inf_le_left (n.down • res F (le_inf hi hj) (c.value i j))
    rw [map_zsmul, res_trans, ← smul_sub]
    apply congrArg (fun a => n.down • a)
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using
      (cocycle_condition_restrict c k i j inf_le_right
        (inf_le_left.trans hi) (inf_le_left.trans hj)).symm

/-- An actual covering gives local surjectivity of the degree map;
no local lift or local coboundary is assumed. -/
theorem projectionPre_locallySurjective
    (hU : ∀ x : X, ∃ i : ι, x ∈ U i) :
    TopCat.Presheaf.IsLocallySurjective (projectionPre c) := by
  apply (TopCat.Presheaf.isLocallySurjective_iff (projectionPre c)).mpr
  intro V n x hx
  obtain ⟨k, hxk⟩ := hU x
  refine ⟨V ⊓ U k, inf_le_left,
    ⟨localLiftHom c k inf_le_right n, ?_⟩, ⟨hx, hxk⟩⟩
  rfl

end Wikipedia.HopfProblem.HolomorphicPicard.CechExtension
