import Wikipedia.NoExoticSixSphere.AnnulusDoublePointCompactness
import Wikipedia.NoExoticSixSphere.InvolutionQuotientTopology

/-!
# The genuine unordered annulus double-point space

The actual double-point closure is invariant under interchange of source
points. Its involution quotient is compact and Hausdorff. The diagonal
orbit set is the image of the fixed-point set of this actual swap map;
no curve or boundary structure is imposed by these definitions.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.AnnulusDoublePoints

open GLOrthonormalization

variable {p : ℕ} {Y : Type*} (g : Vector (p + 1) → Y)

abbrev ClosedPoints := closure (points g)

theorem swap_mem_closure {v : Vector (p + 1) × Vector (p + 1)}
    (hv : v ∈ closure (points g)) : Prod.swap v ∈ closure (points g) := by
  have hs : points g ⊆ Prod.swap ⁻¹' closure (points g) := by
    intro w hw
    exact subset_closure ⟨hw.2.1, hw.1, hw.2.2.1.symm, hw.2.2.2.symm⟩
  exact closure_minimal hs (isClosed_closure.preimage continuous_swap) hv

def swapClosure : ClosedPoints g ≃ₜ ClosedPoints g where
  toFun v := ⟨Prod.swap v.val, swap_mem_closure g v.property⟩
  invFun v := ⟨Prod.swap v.val, swap_mem_closure g v.property⟩
  left_inv v := by apply Subtype.ext; rfl
  right_inv v := by apply Subtype.ext; rfl
  continuous_toFun := (continuous_swap.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_swap.comp continuous_subtype_val).subtype_mk _

theorem swapClosure_involutive : Involutive (swapClosure g) := by
  intro v
  apply Subtype.ext
  rfl

theorem swapClosure_fixed_iff (v : ClosedPoints g) :
    swapClosure g v = v ↔ v.val.1 = v.val.2 := by
  constructor
  · intro he
    exact (congrArg (fun w : ClosedPoints g ↦ w.val.1) he).symm
  · intro he
    apply Subtype.ext
    exact Prod.ext he.symm he

abbrev Unordered := InvolutionQuotient.Orbit (swapClosure g) (swapClosure_involutive g)

def unorderedProj : ClosedPoints g → Unordered g :=
  InvolutionQuotient.proj (swapClosure g) (swapClosure_involutive g)

theorem isOpenQuotientMap_unorderedProj : IsOpenQuotientMap (unorderedProj g) :=
  InvolutionQuotient.isOpenQuotientMap_proj (swapClosure g) (swapClosure_involutive g)
    (swapClosure g).continuous

theorem t2Space_unordered : T2Space (Unordered g) :=
  InvolutionQuotient.t2Space_orbit (swapClosure g) (swapClosure_involutive g)
    (swapClosure g).continuous

theorem compactSpace_unordered : CompactSpace (Unordered g) := by
  let : CompactSpace (ClosedPoints g) := isCompact_iff_compactSpace.mp (isCompact_closure g)
  exact Function.Surjective.compactSpace (isOpenQuotientMap_unorderedProj g).continuous
    (isOpenQuotientMap_unorderedProj g).surjective

def diagonalOrbits : Set (Unordered g) :=
  unorderedProj g '' {v : ClosedPoints g | v.val.1 = v.val.2}

theorem diagonalOrbits_eq_fixed : diagonalOrbits g =
    unorderedProj g '' {v : ClosedPoints g | swapClosure g v = v} := by
  unfold diagonalOrbits
  congr 1
  ext v
  exact (swapClosure_fixed_iff g v).symm

theorem isClosed_diagonalOrbits : IsClosed (diagonalOrbits g) := by
  rw [diagonalOrbits_eq_fixed]
  exact InvolutionQuotient.isClosed_fixed_orbits (swapClosure g) (swapClosure_involutive g)
    (swapClosure g).continuous

theorem mem_diagonalOrbits_iff (v : ClosedPoints g) :
    unorderedProj g v ∈ diagonalOrbits g ↔ v.val.1 = v.val.2 := by
  rw [diagonalOrbits_eq_fixed]
  exact (InvolutionQuotient.mem_fixed_orbits_iff (swapClosure g)
    (swapClosure_involutive g) v).trans (swapClosure_fixed_iff g v)

end NoExoticSixSphere.AnnulusDoublePoints
