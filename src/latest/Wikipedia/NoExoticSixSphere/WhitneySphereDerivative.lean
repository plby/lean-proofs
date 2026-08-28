import Wikipedia.NoExoticSixSphere.WhitneySphereMap

/-!
# The Whitney sphere is an immersion in its original atlas

The polynomial ambient derivative is explicit. Its kernel has zero
intersection with the sphere tangent hyperplane. At either pole, projecting
the native sphere derivative onto the tail is surjective.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.WhitneySphere

open GLOrthonormalization SphereCylinder SphereThreeTangentFrame

def ambientDerivative (x : Vector 4) : Vector 4 →L[ℝ] (Vector 3 × Vector 3) :=
  (tail 2).prod (head x • tail 2 + head.smulRight (tail 2 x))

theorem ambientDerivative_apply (x v : Vector 4) :
    ambientDerivative x v = (tail 2 v, head x • tail 2 v + head v • tail 2 x) := rfl

theorem hasFDerivAt_ambientMap (x : Vector 4) :
    HasFDerivAt ambientMap (ambientDerivative x) x :=
  (tail 2).hasFDerivAt.prodMk (head.hasFDerivAt.smul (tail 2).hasFDerivAt)

theorem mfderiv_map (x : Sphere 3) :
    mfderiv (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) map x =
      (ambientDerivative x.val).comp (inclusionDerivative x) := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hi : ContMDiff (𝓡 3) (𝓡 4) ∞ (fun s : Sphere 3 ↦ s.val) := contMDiff_coe_sphere
  change mfderiv (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3)
    (ambientMap ∘ (fun s : Sphere 3 ↦ s.val)) x = _
  rw [mfderiv_comp x (contDiff_ambientMap.contMDiff.mdifferentiableAt (by simp))
    (hi.mdifferentiableAt (by simp)), mfderiv_eq_fderiv,
    (hasFDerivAt_ambientMap x.val).fderiv]
  rfl

theorem inner_of_tail_zero (x v : Vector 4) (hv : tail 2 v = 0) :
    inner ℝ x v = head v * head x := by
  rw [← join_head_tail v, hv]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ, head_apply]

theorem ambientDerivative_tangent_kernel (x : Sphere 3) (v : Vector 4)
    (ht : inner ℝ x.val v = 0) (hv : ambientDerivative x.val v = 0) : v = 0 := by
  have htail : tail 2 v = 0 := congrArg Prod.fst hv
  have hs : head v • tail 2 x.val = 0 := by
    have h : head x.val • tail 2 v + head v • tail 2 x.val = 0 := congrArg Prod.snd hv
    simpa only [ambientDerivative_apply, htail, smul_zero, zero_add] using h
  have hm : head v * head x.val = 0 := (inner_of_tail_zero x.val v htail).symm.trans ht
  have hh : head v = 0 := by
    rcases smul_eq_zero.mp hs with hh | hx
    · exact hh
    · have hnx : head x.val ≠ 0 := by
        intro hhx
        have hzero : x.val = 0 := by
          rw [← join_head_tail x.val, hhx, hx]
          exact map_zero (join 2)
        exact ne_zero_of_mem_unit_sphere x hzero
      exact (mul_eq_zero.mp hm).resolve_right hnx
  rw [← join_head_tail v, hh, htail]
  exact map_zero (join 2)

theorem injective_mfderiv_map (x : Sphere 3) :
    Injective (mfderiv (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) map x) := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hi : Injective (inclusionDerivative x) := by
    convert! injective_mvfderiv_subtypeVal_sphere x
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  have ht : inner ℝ x.val (inclusionDerivative x v) = 0 := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mp
    rw [← range_inclusionDerivative]
    exact ⟨v, rfl⟩
  rw [mfderiv_map] at hv
  have hz := ambientDerivative_tangent_kernel x (inclusionDerivative x v) ht hv
  exact hi (hz.trans (map_zero _).symm)

theorem inner_endPole_join (b : Bool) (u : Vector 3) :
    inner ℝ (endPole 2 b).val (join 2 (0, u)) = 0 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ, endPole]

theorem tail_inclusion_surjective_endPole (b : Bool) :
    Surjective ((tail 2).comp (inclusionDerivative (endPole 2 b))) := by
  intro u
  have hu : join 2 (0, u) ∈ (inclusionDerivative (endPole 2 b)).range := by
    rw [range_inclusionDerivative]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (inner_endPole_join b u)
  obtain ⟨v, hv⟩ := hu
  refine ⟨v, ?_⟩
  change tail 2 (inclusionDerivative (endPole 2 b) v) = u
  exact (congrArg (tail 2) hv).trans (tail_join 2 0 u)

theorem mfderiv_map_endPole_apply (b : Bool) (v : Vector 3) :
    mfderiv (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) map (endPole 2 b) v =
      (tail 2 (inclusionDerivative (endPole 2 b) v),
        (if b then (1 : ℝ) else -1) • tail 2 (inclusionDerivative (endPole 2 b) v)) := by
  rw [mfderiv_map]
  change ambientDerivative (endPole 2 b).val (inclusionDerivative (endPole 2 b) v) = _
  simp only [ambientDerivative_apply,
    head_apply, endPole_head, tail_endPole, smul_zero, add_zero]

end NoExoticSixSphere.WhitneySphere
