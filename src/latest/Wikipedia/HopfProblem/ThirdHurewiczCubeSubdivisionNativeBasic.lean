import Wikipedia.HopfProblem.ThirdHurewiczNativeMaps
import Mathlib.Tactic.FinCases

/-!
# Native cubical classes and relative affine homotopies in dimension three

The internal faces of the standard ordered tetrahedra are coordinate
equality planes. An affine interpolation stays based when its endpoints
lie on a common boundary plane or on one common internal equality plane.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

abbrev NativeCube := Fin 3 → I

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- The additive class of the original native generalized three-loop. -/
def nativeCubeClass (p : GenLoop (Fin 3) X x) : Additive (π_ 3 X x) :=
  Additive.ofMul (⟦p⟧ : π_ 3 X x)

theorem nativeCubeClass_homotopic {p q : GenLoop (Fin 3) X x}
    (h : GenLoop.Homotopic p q) : nativeCubeClass p = nativeCubeClass q :=
  congrArg (fun a : π_ 3 X x => Additive.ofMul a) (Quotient.sound h)

theorem nativeCubeClass_transAt (i : Fin 3) (p q : GenLoop (Fin 3) X x) :
    nativeCubeClass (GenLoop.transAt i p q) = nativeCubeClass p + nativeCubeClass q :=
  congrArg Additive.ofMul ((HomotopyGroup.mul_spec (i := i) (p := q) (q := p)).symm.trans
    (mul_comm _ _))

theorem nativeCubeClass_symmAt (i : Fin 3) (p : GenLoop (Fin 3) X x) :
    nativeCubeClass (GenLoop.symmAt i p) = -nativeCubeClass p :=
  congrArg Additive.ofMul (HomotopyGroup.inv_spec (i := i) (p := p)).symm

@[simp] theorem nativeCubeClass_const :
    nativeCubeClass (GenLoop.const : GenLoop (Fin 3) X x) = 0 := rfl

/-- Every coordinate equality plane is sent to the original base point. -/
def NativeCubeInternalBased (p : GenLoop (Fin 3) X x) : Prop :=
  ∀ u : NativeCube, ∀ i j : Fin 3, i ≠ j → u i = u j → p u = x

/-- The two points lie in one common affine face on which a based cube is constant. -/
inductive NativeCubeSameFlat (a b : NativeCube) : Prop
  | zero (i : Fin 3) (ha : a i = 0) (hb : b i = 0)
  | one (i : Fin 3) (ha : a i = 1) (hb : b i = 1)
  | equal (i j : Fin 3) (hij : i ≠ j) (ha : a i = a j) (hb : b i = b j)

def nativeCubeBlend (t : I) (a b : NativeCube) : NativeCube :=
  fun i => Set.Icc.convexComb (a i) (b i) t

@[simp] theorem nativeCubeBlend_zero (a b : NativeCube) : nativeCubeBlend 0 a b = a := by
  funext i
  exact Set.Icc.convexComb_zero _ _

@[simp] theorem nativeCubeBlend_one (a b : NativeCube) : nativeCubeBlend 1 a b = b := by
  funext i
  exact Set.Icc.convexComb_one _ _

def nativeCubeBlendMap (f g : C(NativeCube, NativeCube)) : C(I × NativeCube, NativeCube) where
  toFun u := nativeCubeBlend u.1 (f u.2) (g u.2)
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact Set.Icc.continuous_convexComb_prod.comp
      (((continuous_apply i).comp (f.continuous.comp continuous_snd)).prodMk
        (((continuous_apply i).comp (g.continuous.comp continuous_snd)).prodMk
          continuous_fst))

theorem nativeCubeBlend_based (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p)
    {a b : NativeCube} (h : NativeCubeSameFlat a b) (t : I) :
    p (nativeCubeBlend t a b) = x := by
  cases h with
  | zero i ha hb =>
      exact p.property _ ⟨i, Or.inl (by simp [nativeCubeBlend, ha, hb])⟩
  | one i ha hb =>
      exact p.property _ ⟨i, Or.inr (by simp [nativeCubeBlend, ha, hb])⟩
  | equal i j hij ha hb =>
      exact hp _ i j hij (by simp only [nativeCubeBlend, ha, hb])

def nativeCubePullbackLoop (p : GenLoop (Fin 3) X x) (f : C(NativeCube, NativeCube))
    (hf : ∀ u ∈ Cube.boundary (Fin 3), p (f u) = x) : GenLoop (Fin 3) X x :=
  ⟨p.val.comp f, hf⟩

@[simp] theorem nativeCubePullbackLoop_apply (p : GenLoop (Fin 3) X x)
    (f : C(NativeCube, NativeCube))
    (hf : ∀ u ∈ Cube.boundary (Fin 3), p (f u) = x) (u : NativeCube) :
    nativeCubePullbackLoop p f hf u = p (f u) := rfl

/-- A literal boundary-relative homotopy, obtained by interpolating actual cube points. -/
def nativeCubeLinearHomotopy (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p)
    (f g : C(NativeCube, NativeCube))
    (hf : ∀ u ∈ Cube.boundary (Fin 3), p (f u) = x)
    (hg : ∀ u ∈ Cube.boundary (Fin 3), p (g u) = x)
    (hfg : ∀ u ∈ Cube.boundary (Fin 3), NativeCubeSameFlat (f u) (g u)) :
    (nativeCubePullbackLoop p f hf).val.HomotopyRel
      (nativeCubePullbackLoop p g hg).val (Cube.boundary (Fin 3)) where
  toFun u := p (nativeCubeBlend u.1 (f u.2) (g u.2))
  continuous_toFun := p.val.continuous.comp (nativeCubeBlendMap f g).continuous
  map_zero_left u := by simp
  map_one_left u := by simp
  prop' t u hu := (nativeCubeBlend_based p hp (hfg u hu) t).trans (hf u hu).symm

theorem nativeCubeClass_linear (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p)
    (f g : C(NativeCube, NativeCube))
    (hf : ∀ u ∈ Cube.boundary (Fin 3), p (f u) = x)
    (hg : ∀ u ∈ Cube.boundary (Fin 3), p (g u) = x)
    (hfg : ∀ u ∈ Cube.boundary (Fin 3), NativeCubeSameFlat (f u) (g u)) :
    nativeCubeClass (nativeCubePullbackLoop p f hf) =
      nativeCubeClass (nativeCubePullbackLoop p g hg) :=
  nativeCubeClass_homotopic ⟨nativeCubeLinearHomotopy p hp f g hf hg hfg⟩

end Wikipedia.HopfProblem.ThirdHurewicz
