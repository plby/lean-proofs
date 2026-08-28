import Wikipedia.HopfProblem.HolomorphicPicardCechAlgebra

/-!
# An actual middle map gives a local Čech coboundary

Two systems of local lifts with the same degree are compared through a
genuine middle map of sheaf extensions. Their differences lie in the actual
kernel of the target sequence on each open set. Lifting through that kernel
and using sectionwise injectivity gives a literal solution of the difference
of the two original Čech cocycles.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicPicard.CechClassInjectivity

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} {F E₁ E₂ G : TopCat.Sheaf AddCommGrpCat.{0} X}
  {ι : Type} {U : ι → Opens X}

/-- A middle map preserving the actual inclusion and degree maps produces
an actual local coboundary between the two lift-difference cocycles. -/
theorem solvable_sub_of_middle_map (c d : CechOneCocycle F U)
    (ic : F ⟶ E₁) (pc : E₁ ⟶ G) (id : F ⟶ E₂) (pd : E₂ ⟶ G)
    (wd : id ≫ pd = 0) (hSd : (ShortComplex.mk id pd wd).ShortExact)
    (m : E₁ ⟶ E₂) (hi : ic ≫ m = id) (hp : m ≫ pd = pc)
    (tc : ∀ i, Section E₁ (U i)) (td : ∀ i, Section E₂ (U i))
    (ht : ∀ i, pc.hom.app (op (U i)) (tc i) = pd.hom.app (op (U i)) (td i))
    (hc : ∀ i j,
      res E₁ inf_le_right (tc j) - res E₁ inf_le_left (tc i) =
        ic.hom.app (op (U i ⊓ U j)) (c.value i j))
    (hd : ∀ i j,
      res E₂ inf_le_right (td j) - res E₂ inf_le_left (td i) =
        id.hom.app (op (U i ⊓ U j)) (d.value i j)) :
    (c - d).Solvable := by
  classical
  have hp_app (V : Opens X) (t : Section E₁ V) :
      pd.hom.app (op V) (m.hom.app (op V) t) = pc.hom.app (op V) t :=
    congrArg (fun f : E₁ ⟶ G => f.hom.app (op V) t) hp
  have hi_app (V : Opens X) (t : Section F V) :
      m.hom.app (op V) (ic.hom.app (op V) t) = id.hom.app (op V) t :=
    congrArg (fun f : F ⟶ E₂ => f.hom.app (op V) t) hi
  have hkernel (i : ι) :
      pd.hom.app (op (U i)) (td i - m.hom.app (op (U i)) (tc i)) = 0 := by
    rw [map_sub, hp_app, ← ht i, sub_self]
  choose b hb using fun i => section_kernel_lift hSd
    (td i - m.hom.app (op (U i)) (tc i)) (hkernel i)
  refine ⟨b, ?_⟩
  intro i j
  apply section_f_injective hSd (U i ⊓ U j)
  change id.hom.app (op (U i ⊓ U j))
      (res F inf_le_left (b i) - res F inf_le_right (b j)) =
    id.hom.app (op (U i ⊓ U j)) (c.value i j - d.value i j)
  have hbi : id.hom.app (op (U i ⊓ U j)) (res F inf_le_left (b i)) =
      res E₂ inf_le_left (td i - m.hom.app (op (U i)) (tc i)) :=
    (res_map id inf_le_left (b i)).symm.trans
      (congrArg (res E₂ inf_le_left) (hb i))
  have hbj : id.hom.app (op (U i ⊓ U j)) (res F inf_le_right (b j)) =
      res E₂ inf_le_right (td j - m.hom.app (op (U j)) (tc j)) :=
    (res_map id inf_le_right (b j)).symm.trans
      (congrArg (res E₂ inf_le_right) (hb j))
  calc
    id.hom.app (op (U i ⊓ U j))
        (res F inf_le_left (b i) - res F inf_le_right (b j)) =
        res E₂ inf_le_left (td i - m.hom.app (op (U i)) (tc i)) -
          res E₂ inf_le_right (td j - m.hom.app (op (U j)) (tc j)) := by
      rw [map_sub, hbi, hbj]
    _ = m.hom.app (op (U i ⊓ U j))
          (res E₁ inf_le_right (tc j) - res E₁ inf_le_left (tc i)) -
        (res E₂ inf_le_right (td j) - res E₂ inf_le_left (td i)) := by
      simp only [map_sub, res_map]
      abel
    _ = m.hom.app (op (U i ⊓ U j))
          (ic.hom.app (op (U i ⊓ U j)) (c.value i j)) -
        id.hom.app (op (U i ⊓ U j)) (d.value i j) := by
      rw [hc i j, hd i j]
    _ = id.hom.app (op (U i ⊓ U j)) (c.value i j - d.value i j) := by
      rw [hi_app, map_sub]

end Wikipedia.HopfProblem.HolomorphicPicard.CechClassInjectivity
