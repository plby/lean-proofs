import Wikipedia.NoExoticSixSphere.SphereSmashNativeCubes

/-!
# Bilinearity of the original native sixteen-cube smash pairing

Concatenation in either eight-coordinate block commutes exactly with
the original pairing. The resulting product on native homotopy groups
is a homomorphism in each variable, with no stability or abstract ring
structure used as a replacement for these representative identities.
-/

noncomputable section

open scoped Topology unitInterval

namespace NoExoticSixSphere.SphereSmashNative

theorem leftIndex_ne_rightIndex (i j : Fin 8) : i.castAdd 8 ≠ j.natAdd 8 := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = 8 + j.val at hv
  omega

theorem left_update_left (u : Fin 16 → I) (i : Fin 8) (t : I) :
    left (Function.update u (i.castAdd 8) t) = Function.update (left u) i t :=
  Function.update_comp_eq_of_injective u (Fin.castAdd_injective 8 8) i t

theorem right_update_left (u : Fin 16 → I) (i : Fin 8) (t : I) :
    right (Function.update u (i.castAdd 8) t) = right u :=
  Function.update_comp_eq_of_forall_ne u t (fun j ↦ (leftIndex_ne_rightIndex i j).symm)

theorem left_update_right (u : Fin 16 → I) (i : Fin 8) (t : I) :
    left (Function.update u (i.natAdd 8) t) = left u :=
  Function.update_comp_eq_of_forall_ne u t (fun j ↦ leftIndex_ne_rightIndex j i)

theorem right_update_right (u : Fin 16 → I) (i : Fin 8) (t : I) :
    right (Function.update u (i.natAdd 8) t) = Function.update (right u) i t := by
  apply Function.update_comp_eq_of_injective
  intro j k h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 8 + j.val = 8 + k.val at hv
  omega

theorem loop_const_left (q : Loop) : loop GenLoop.const q = GenLoop.const := by
  apply GenLoop.ext
  intro u
  exact JamesSphere.pairing_left_pole 5 (q (right u))

theorem loop_const_right (p : Loop) : loop p GenLoop.const = GenLoop.const := by
  apply GenLoop.ext
  intro u
  exact JamesSphere.pairing_right_pole 5 (p (left u))

theorem loop_transAt_left (p q r : Loop) (i : Fin 8) :
    loop (GenLoop.transAt i p q) r =
      GenLoop.transAt (i.castAdd 8) (loop p r) (loop q r) := by
  apply GenLoop.ext
  intro u
  change JamesSphere.pairing 5
    ((if (u (i.castAdd 8) : ℝ) ≤ 1 / 2 then
        p (Function.update (left u) i (Set.projIcc 0 1 zero_le_one (2 * u (i.castAdd 8)))) else
        q (Function.update (left u) i (Set.projIcc 0 1 zero_le_one (2 * u (i.castAdd 8) - 1)))),
      r (right u)) =
    if (u (i.castAdd 8) : ℝ) ≤ 1 / 2 then
      loop p r (Function.update u (i.castAdd 8)
        (Set.projIcc 0 1 zero_le_one (2 * u (i.castAdd 8)))) else
      loop q r (Function.update u (i.castAdd 8)
        (Set.projIcc 0 1 zero_le_one (2 * u (i.castAdd 8) - 1)))
  split_ifs <;> simp only [loop_apply, left_update_left, right_update_left]

theorem loop_transAt_right (p q r : Loop) (i : Fin 8) :
    loop p (GenLoop.transAt i q r) =
      GenLoop.transAt (i.natAdd 8) (loop p q) (loop p r) := by
  apply GenLoop.ext
  intro u
  change JamesSphere.pairing 5 (p (left u),
    (if (u (i.natAdd 8) : ℝ) ≤ 1 / 2 then
      q (Function.update (right u) i (Set.projIcc 0 1 zero_le_one (2 * u (i.natAdd 8)))) else
      r (Function.update (right u) i (Set.projIcc 0 1 zero_le_one (2 * u (i.natAdd 8) - 1))))) =
    if (u (i.natAdd 8) : ℝ) ≤ 1 / 2 then
      loop p q (Function.update u (i.natAdd 8)
        (Set.projIcc 0 1 zero_le_one (2 * u (i.natAdd 8)))) else
      loop p r (Function.update u (i.natAdd 8)
        (Set.projIcc 0 1 zero_le_one (2 * u (i.natAdd 8) - 1)))
  split_ifs <;> simp only [loop_apply, left_update_right, right_update_right]

theorem product_one_left (q : Source) : product 1 q = 1 := by
  induction q using Quotient.inductionOn with
  | h q =>
    change (Quotient.mk' (loop GenLoop.const q) : Target) = Quotient.mk' GenLoop.const
    exact congrArg (fun p : GenLoop (Fin 16) (Sphere 10) (spherePole 10) ↦
      (Quotient.mk' p : Target)) (loop_const_left q)

theorem product_one_right (p : Source) : product p 1 = 1 := by
  induction p using Quotient.inductionOn with
  | h p =>
    change (Quotient.mk' (loop p GenLoop.const) : Target) = Quotient.mk' GenLoop.const
    exact congrArg (fun q : GenLoop (Fin 16) (Sphere 10) (spherePole 10) ↦
      (Quotient.mk' q : Target)) (loop_const_right p)

theorem product_mul_left (p q r : Source) : product (p * q) r = product p r * product q r := by
  induction p using Quotient.inductionOn with
  | h p =>
    induction q using Quotient.inductionOn with
    | h q =>
      induction r using Quotient.inductionOn with
      | h r =>
        have hsource := HomotopyGroup.mul_spec (i := (0 : Fin 8)) (p := p) (q := q)
        have htarget := HomotopyGroup.mul_spec (i := (0 : Fin 8).castAdd 8)
          (p := loop p r) (q := loop q r)
        have hloop := congrArg (fun s : GenLoop (Fin 16) (Sphere 10) (spherePole 10) ↦
          (Quotient.mk' s : Target)) (loop_transAt_left q p r 0)
        exact (congrArg (fun s : Source ↦ product s (Quotient.mk' r)) hsource).trans
          (hloop.trans htarget.symm)

theorem product_mul_right (p q r : Source) : product p (q * r) = product p q * product p r := by
  induction p using Quotient.inductionOn with
  | h p =>
    induction q using Quotient.inductionOn with
    | h q =>
      induction r using Quotient.inductionOn with
      | h r =>
        have hsource := HomotopyGroup.mul_spec (i := (0 : Fin 8)) (p := q) (q := r)
        have htarget := HomotopyGroup.mul_spec (i := (0 : Fin 8).natAdd 8)
          (p := loop p q) (q := loop p r)
        have hloop := congrArg (fun s : GenLoop (Fin 16) (Sphere 10) (spherePole 10) ↦
          (Quotient.mk' s : Target)) (loop_transAt_right p r q 0)
        exact (congrArg (fun s : Source ↦ product (Quotient.mk' p) s) hsource).trans
          (hloop.trans htarget.symm)

def leftHom (q : Source) : Source →* Target where
  toFun := fun p ↦ product p q
  map_one' := product_one_left q
  map_mul' := fun p r ↦ product_mul_left p r q

def rightHom (p : Source) : Source →* Target where
  toFun := product p
  map_one' := product_one_right p
  map_mul' := product_mul_right p

theorem product_pow_left (p q : Source) (k : ℕ) : product (p ^ k) q = product p q ^ k :=
  (leftHom q).map_pow p k

theorem product_pow_right (p q : Source) (k : ℕ) : product p (q ^ k) = product p q ^ k :=
  (rightHom p).map_pow q k

end NoExoticSixSphere.SphereSmashNative
