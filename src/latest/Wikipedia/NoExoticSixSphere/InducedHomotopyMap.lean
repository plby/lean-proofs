import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# The map on native higher homotopy classes induced by a based continuous map

Relative representatives give surjectivity, and relative homotopy reflection
gives injectivity. The quotient is mathlib's actual `HomotopyGroup`.
-/

open Set

namespace NoExoticSixSphere.HigherHomotopy

variable {N Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z] {y : Y} {z : Z}

noncomputable def genLoopMap (i : C(Y, Z)) (hi : i y = z) (p : GenLoop N Y y) : GenLoop N Z z :=
  ⟨i.comp p.1, fun x hx ↦ (congrArg i (p.2 x hx)).trans hi⟩

theorem genLoopMap_const (i : C(Y, Z)) (hi : i y = z) :
    genLoopMap (N := N) i hi GenLoop.const = GenLoop.const := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  exact hi

theorem genLoopMap_homotopic (i : C(Y, Z)) (hi : i y = z) {p q : GenLoop N Y y}
    (h : GenLoop.Homotopic p q) : GenLoop.Homotopic (genLoopMap i hi p) (genLoopMap i hi q) := by
  obtain ⟨F⟩ := h
  exact ⟨F.compContinuousMap i⟩

noncomputable def map (i : C(Y, Z)) (hi : i y = z) :
    HomotopyGroup N Y y → HomotopyGroup N Z z :=
  Quotient.map (genLoopMap i hi) (fun _ _ h ↦ genLoopMap_homotopic i hi h)

theorem map_mk (i : C(Y, Z)) (hi : i y = z) (p : GenLoop N Y y) :
    map i hi (Quotient.mk' p) = Quotient.mk' (genLoopMap i hi p) := rfl

theorem exists_genLoop_representative (i : C(Y, Z)) (hi : i y = z)
    (hinj : Function.Injective i)
    (hrep : ∀ p : C((N → unitInterval), Z), ∃ q : C((N → unitInterval), Y),
      Nonempty (p.HomotopyRel (i.comp q) (p ⁻¹' range i)))
    (p : GenLoop N Z z) : ∃ q : GenLoop N Y y, GenLoop.Homotopic p (genLoopMap i hi q) := by
  obtain ⟨q, ⟨G⟩⟩ := hrep p.1
  have hxrange (x : N → unitInterval) (hx : x ∈ Cube.boundary N) :
      x ∈ p.1 ⁻¹' range i := ⟨y, hi.trans (p.2 x hx).symm⟩
  have hq (x : N → unitInterval) (hx : x ∈ Cube.boundary N) : q x = y :=
    hinj ((G.fst_eq_snd (hxrange x hx)).symm.trans ((p.2 x hx).trans hi.symm))
  refine ⟨⟨q, hq⟩, ⟨{ toHomotopy := G.toHomotopy, prop' := ?_ }⟩⟩
  intro r x hx
  exact G.eq_fst r (hxrange x hx)

theorem map_surjective (i : C(Y, Z)) (hi : i y = z) (hinj : Function.Injective i)
    (hrep : ∀ p : C((N → unitInterval), Z), ∃ q : C((N → unitInterval), Y),
      Nonempty (p.HomotopyRel (i.comp q) (p ⁻¹' range i))) :
    Function.Surjective (map (N := N) i hi) := by
  intro p
  refine Quotient.inductionOn p ?_
  intro p
  obtain ⟨q, hq⟩ := exists_genLoop_representative i hi hinj hrep p
  exact ⟨Quotient.mk' q, Quotient.sound (GenLoop.Homotopic.symm hq)⟩

theorem map_injective (i : C(Y, Z)) (hi : i y = z)
    (hreflect : ∀ f g : C((N → unitInterval), Y), ∀ S : Set (N → unitInterval),
      Nonempty ((i.comp f).HomotopyRel (i.comp g) S) → Nonempty (f.HomotopyRel g S)) :
    Function.Injective (map (N := N) i hi) := by
  intro p q
  refine Quotient.inductionOn₂ p q ?_
  intro f g h
  apply Quotient.sound
  exact hreflect f.1 g.1 (Cube.boundary N) (Quotient.exact h)

theorem genLoopMap_transAt [DecidableEq N] (i : C(Y, Z)) (hi : i y = z)
    (j : N) (p q : GenLoop N Y y) :
    genLoopMap i hi (GenLoop.transAt j p q) =
      GenLoop.transAt j (genLoopMap i hi p) (genLoopMap i hi q) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  change i (if (t j : ℝ) ≤ 1 / 2 then
      p (Function.update t j (Set.projIcc 0 1 zero_le_one (2 * t j))) else
      q (Function.update t j (Set.projIcc 0 1 zero_le_one (2 * t j - 1)))) =
    if (t j : ℝ) ≤ 1 / 2 then
      i (p (Function.update t j (Set.projIcc 0 1 zero_le_one (2 * t j)))) else
      i (q (Function.update t j (Set.projIcc 0 1 zero_le_one (2 * t j - 1))))
  split_ifs <;> rfl

theorem map_mul [DecidableEq N] [Nonempty N] (i : C(Y, Z)) (hi : i y = z)
    (p q : HomotopyGroup N Y y) : map i hi (p * q) = map i hi p * map i hi q := by
  classical
  let j : N := Classical.choice inferInstance
  refine Quotient.inductionOn₂ p q ?_
  intro f g
  have hY := HomotopyGroup.mul_spec (i := j) (p := f) (q := g)
  have hZ := HomotopyGroup.mul_spec (i := j)
    (p := genLoopMap i hi f) (q := genLoopMap i hi g)
  have hmap := congrArg (fun r : GenLoop N Z z ↦ (Quotient.mk' r : HomotopyGroup N Z z))
    (genLoopMap_transAt i hi j g f)
  exact (congrArg (map (N := N) i hi) hY).trans (hmap.trans hZ.symm)

noncomputable def mapMonoidHom [DecidableEq N] [Nonempty N] (i : C(Y, Z)) (hi : i y = z) :
    HomotopyGroup N Y y →* HomotopyGroup N Z z where
  toFun := map i hi
  map_one' := congrArg (fun r : GenLoop N Z z ↦ (Quotient.mk' r : HomotopyGroup N Z z))
    (genLoopMap_const i hi)
  map_mul' := map_mul i hi

end NoExoticSixSphere.HigherHomotopy
