import Wikipedia.NoExoticSixSphere.ModTwoDualBiproduct

/-!
# Original mod-two cohomology maps in biproduct coordinates

The canonical product comparison converts a dual sum map to the two
original pullbacks and a dual diagonal map to their sum. The formulas
retain the native chain injections, projections, and homology maps.
-/

noncomputable section

open CategoryTheory Limits

namespace NoExoticSixSphere.ModTwoDualComplex

variable {K L N : ChainComplex (ModuleCat.{0} ℤ) ℕ}

theorem map_add (f g : K ⟶ L) : map (f + g) = map f + map g :=
  cochainDualFunctor.map_add

theorem map_neg (f : K ⟶ L) : map (-f) = -map f := cochainDualFunctor.map_neg (f := f.op)

/-- A dual sum map has precisely the two original cohomology pullbacks as coordinates. -/
theorem cohomologyBiprodEquiv_map_desc (f : K ⟶ N) (g : L ⟶ N) (n : ℕ)
    (a : (complex N).homology n) :
    cohomologyBiprodEquiv K L n
        ((HomologicalComplex.homologyMap (map (biprod.desc f g)) n).hom a) =
      ((HomologicalComplex.homologyMap (map f) n).hom a,
        (HomologicalComplex.homologyMap (map g) n).hom a) := by
  apply Prod.ext
  · rw [cohomologyBiprodEquiv_fst]
    have he := HomologicalComplex.homologyMap_comp (map (biprod.desc f g))
      (map (biprod.inl : K ⟶ K ⊞ L)) n
    rw [← map_comp, biprod.inl_desc] at he
    exact (congrArg (fun h => h.hom a) he).symm
  · rw [cohomologyBiprodEquiv_snd]
    have he := HomologicalComplex.homologyMap_comp (map (biprod.desc f g))
      (map (biprod.inr : L ⟶ K ⊞ L)) n
    rw [← map_comp, biprod.inr_desc] at he
    exact (congrArg (fun h => h.hom a) he).symm

/-- A dual diagonal map is the sum of the original pullbacks of the actual coordinates. -/
theorem cohomologyBiprodEquiv_map_lift (f : N ⟶ K) (g : N ⟶ L) (n : ℕ)
    (a : (complex (K ⊞ L)).homology n) :
    (HomologicalComplex.homologyMap (map (biprod.lift f g)) n).hom a =
      (HomologicalComplex.homologyMap (map f) n).hom (cohomologyBiprodEquiv K L n a).1 +
        (HomologicalComplex.homologyMap (map g) n).hom (cohomologyBiprodEquiv K L n a).2 := by
  have hl : biprod.lift f g = f ≫ biprod.inl + g ≫ biprod.inr := by
    apply biprod.hom_ext <;> simp
  have he := congrArg (fun h => HomologicalComplex.homologyMap (map h) n) hl
  rw [map_add, map_comp, map_comp, HomologicalComplex.homologyMap_add,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at he
  rw [cohomologyBiprodEquiv_fst, cohomologyBiprodEquiv_snd]
  exact congrArg (fun h => h.hom a) he

end NoExoticSixSphere.ModTwoDualComplex
