import Wikipedia.NoExoticSixSphere.DiskDoublePointCompactness
import Wikipedia.NoExoticSixSphere.InvolutionQuotientTopology

/-!
# The original unordered disk double-point space

Swapping the two actual source points preserves their double-point closure.
Its genuine involution quotient is compact and Hausdorff, and its diagonal
orbit set is the image of the actual fixed-point set. No curve structure
or parity statement is imposed on this topological construction.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.DiskDoublePoints

variable {E Y : Type*} [NormedAddCommGroup E] (g : E → Y)

abbrev ClosedPoints := closure (points g)

theorem swap_mem_closure {p : E × E} (hp : p ∈ closure (points g)) :
    Prod.swap p ∈ closure (points g) := by
  have hs : points g ⊆ Prod.swap ⁻¹' closure (points g) := by
    intro q hq
    exact subset_closure ⟨hq.2.1, hq.1, hq.2.2.1.symm, hq.2.2.2.symm⟩
  exact closure_minimal hs (isClosed_closure.preimage continuous_swap) hp

def swapClosure : ClosedPoints g ≃ₜ ClosedPoints g where
  toFun p := ⟨Prod.swap p.val, swap_mem_closure g p.property⟩
  invFun p := ⟨Prod.swap p.val, swap_mem_closure g p.property⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := by apply Subtype.ext; rfl
  continuous_toFun := (continuous_swap.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_swap.comp continuous_subtype_val).subtype_mk _

theorem swapClosure_involutive : Involutive (swapClosure g) := by
  intro p
  apply Subtype.ext
  rfl

theorem swapClosure_fixed_iff (p : ClosedPoints g) :
    swapClosure g p = p ↔ p.val.1 = p.val.2 := by
  constructor
  · intro he
    exact (congrArg (fun q : ClosedPoints g ↦ q.val.1) he).symm
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

theorem compactSpace_unordered [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    CompactSpace (Unordered g) := by
  let : CompactSpace (ClosedPoints g) := isCompact_iff_compactSpace.mp (isCompact_closure g)
  exact Function.Surjective.compactSpace (isOpenQuotientMap_unorderedProj g).continuous
    (isOpenQuotientMap_unorderedProj g).surjective

def diagonalOrbits : Set (Unordered g) :=
  unorderedProj g '' {p : ClosedPoints g | p.val.1 = p.val.2}

theorem diagonalOrbits_eq_fixed : diagonalOrbits g =
    unorderedProj g '' {p : ClosedPoints g | swapClosure g p = p} := by
  unfold diagonalOrbits
  congr 1
  ext p
  exact (swapClosure_fixed_iff g p).symm

theorem isClosed_diagonalOrbits : IsClosed (diagonalOrbits g) := by
  rw [diagonalOrbits_eq_fixed]
  exact InvolutionQuotient.isClosed_fixed_orbits (swapClosure g) (swapClosure_involutive g)
    (swapClosure g).continuous

theorem mem_diagonalOrbits_iff (p : ClosedPoints g) :
    unorderedProj g p ∈ diagonalOrbits g ↔ p.val.1 = p.val.2 := by
  rw [diagonalOrbits_eq_fixed]
  exact (InvolutionQuotient.mem_fixed_orbits_iff (swapClosure g)
    (swapClosure_involutive g) p).trans (swapClosure_fixed_iff g p)

end NoExoticSixSphere.DiskDoublePoints
