import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.UnitInterval

/-!
# Native cubical classes and relative affine homotopies

The construction is independent of the dimension. Coordinate equality planes
and outer cube faces are affine, so common-face interpolation gives literal
homotopies of the original generalized loops relative to their boundary.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision

abbrev NativeCube (N : Type*) := N → I

variable {N X : Type*} [TopologicalSpace X] {x : X}

/-- The additive class of an actual native generalized loop. -/
def nativeClass (p : GenLoop N X x) : Additive (HomotopyGroup N X x) :=
  Additive.ofMul (⟦p⟧ : HomotopyGroup N X x)

theorem nativeClass_homotopic {p q : GenLoop N X x}
    (h : GenLoop.Homotopic p q) : nativeClass p = nativeClass q :=
  congrArg (fun a : HomotopyGroup N X x => Additive.ofMul a) (Quotient.sound h)

theorem nativeClass_transAt [DecidableEq N] [Nontrivial N]
    (i : N) (p q : GenLoop N X x) :
    nativeClass (GenLoop.transAt i p q) = nativeClass p + nativeClass q :=
  congrArg Additive.ofMul ((HomotopyGroup.mul_spec (i := i) (p := q) (q := p)).symm.trans
    (mul_comm _ _))

theorem nativeClass_symmAt [DecidableEq N] [Nonempty N]
    (i : N) (p : GenLoop N X x) :
    nativeClass (GenLoop.symmAt i p) = -nativeClass p :=
  congrArg Additive.ofMul (HomotopyGroup.inv_spec (i := i) (p := p)).symm

@[simp] theorem nativeClass_const [DecidableEq N] [Nonempty N] :
    nativeClass (GenLoop.const : GenLoop N X x) = 0 := rfl

/-- Every coordinate equality plane is sent to the original base point. -/
def NativeCubeInternalBased (p : GenLoop N X x) : Prop :=
  ∀ u : NativeCube N, ∀ i j : N, i ≠ j → u i = u j → p u = x

/-- Both points lie in one common affine plane on which a based cube is constant. -/
inductive NativeCubeSameFlat (a b : NativeCube N) : Prop
  | zero (i : N) (ha : a i = 0) (hb : b i = 0)
  | one (i : N) (ha : a i = 1) (hb : b i = 1)
  | equal (i j : N) (hij : i ≠ j) (ha : a i = a j) (hb : b i = b j)

def nativeCubeBlend (t : I) (a b : NativeCube N) : NativeCube N :=
  fun i => Set.Icc.convexComb (a i) (b i) t

@[simp] theorem nativeCubeBlend_zero (a b : NativeCube N) : nativeCubeBlend 0 a b = a := by
  funext i
  exact Set.Icc.convexComb_zero _ _

@[simp] theorem nativeCubeBlend_one (a b : NativeCube N) : nativeCubeBlend 1 a b = b := by
  funext i
  exact Set.Icc.convexComb_one _ _

def nativeCubeBlendMap (f g : C(NativeCube N, NativeCube N)) :
    C(I × NativeCube N, NativeCube N) where
  toFun u := nativeCubeBlend u.1 (f u.2) (g u.2)
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact Set.Icc.continuous_convexComb_prod.comp
      (((continuous_apply i).comp (f.continuous.comp continuous_snd)).prodMk
        (((continuous_apply i).comp (g.continuous.comp continuous_snd)).prodMk
          continuous_fst))

theorem nativeCubeBlend_based (p : GenLoop N X x) (hp : NativeCubeInternalBased p)
    {a b : NativeCube N} (h : NativeCubeSameFlat a b) (t : I) :
    p (nativeCubeBlend t a b) = x := by
  cases h with
  | zero i ha hb =>
      exact p.property _ ⟨i, Or.inl (by simp [nativeCubeBlend, ha, hb])⟩
  | one i ha hb =>
      exact p.property _ ⟨i, Or.inr (by simp [nativeCubeBlend, ha, hb])⟩
  | equal i j hij ha hb =>
      exact hp _ i j hij (by simp only [nativeCubeBlend, ha, hb])

def nativeCubePullbackLoop (p : GenLoop N X x) (f : C(NativeCube N, NativeCube N))
    (hf : ∀ u ∈ Cube.boundary N, p (f u) = x) : GenLoop N X x :=
  ⟨p.val.comp f, hf⟩

@[simp] theorem nativeCubePullbackLoop_apply (p : GenLoop N X x)
    (f : C(NativeCube N, NativeCube N))
    (hf : ∀ u ∈ Cube.boundary N, p (f u) = x) (u : NativeCube N) :
    nativeCubePullbackLoop p f hf u = p (f u) := rfl

/-- Interpolation of actual cube points is a boundary-relative homotopy. -/
def nativeCubeLinearHomotopy (p : GenLoop N X x) (hp : NativeCubeInternalBased p)
    (f g : C(NativeCube N, NativeCube N))
    (hf : ∀ u ∈ Cube.boundary N, p (f u) = x)
    (hg : ∀ u ∈ Cube.boundary N, p (g u) = x)
    (hfg : ∀ u ∈ Cube.boundary N, NativeCubeSameFlat (f u) (g u)) :
    (nativeCubePullbackLoop p f hf).val.HomotopyRel
      (nativeCubePullbackLoop p g hg).val (Cube.boundary N) where
  toFun u := p (nativeCubeBlend u.1 (f u.2) (g u.2))
  continuous_toFun := p.val.continuous.comp (nativeCubeBlendMap f g).continuous
  map_zero_left u := by simp
  map_one_left u := by simp
  prop' t u hu := (nativeCubeBlend_based p hp (hfg u hu) t).trans (hf u hu).symm

theorem nativeClass_linear (p : GenLoop N X x) (hp : NativeCubeInternalBased p)
    (f g : C(NativeCube N, NativeCube N))
    (hf : ∀ u ∈ Cube.boundary N, p (f u) = x)
    (hg : ∀ u ∈ Cube.boundary N, p (g u) = x)
    (hfg : ∀ u ∈ Cube.boundary N, NativeCubeSameFlat (f u) (g u)) :
    nativeClass (nativeCubePullbackLoop p f hf) =
      nativeClass (nativeCubePullbackLoop p g hg) :=
  nativeClass_homotopic ⟨nativeCubeLinearHomotopy p hp f g hf hg hfg⟩

end Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision
