import Wikipedia.HopfProblem.SheafCupProductCofaceIdentities

/-!
# Ring cofaces for a triangular double complex

The data consist of ten actual commutative rings, twelve families of
ring cofaces, the six ordinary cosimplicial identities, and the three
commuting mixed squares. No differential or cup-product identities are
assumed. The differentials are the literal alternating sums of cofaces.
-/

universe u

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalAlgebra

/-- The ordinary coface relation between two adjacent levels. -/
def FaceIdentities {n : ℕ} {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : Fin (n + 2) → A →+* B) (g : Fin (n + 3) → B →+* C) : Prop :=
  ∀ i j, i ≤ j → (g j.succ).comp (f i) = (g i.castSucc).comp (f j)

namespace FaceIdentities

variable {n : ℕ} {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  {f : Fin (n + 2) → A →+* B} {g : Fin (n + 3) → B →+* C}

theorem apply (h : FaceIdentities f g) (i j : Fin (n + 2)) (hij : i ≤ j) (x : A) :
    g j.succ (f i x) = g i.castSucc (f j x) :=
  congrArg (fun φ : A →+* C => φ x) (h i j hij)

theorem low00 {f : Fin 2 → A →+* B} {g : Fin 3 → B →+* C}
    (h : FaceIdentities f g) (x : A) : g 1 (f 0 x) = g 0 (f 0 x) := by
  simpa using h.apply 0 0 (by decide) x

theorem low01 {f : Fin 2 → A →+* B} {g : Fin 3 → B →+* C}
    (h : FaceIdentities f g) (x : A) : g 2 (f 0 x) = g 0 (f 1 x) := by
  simpa using h.apply 0 1 (by decide) x

theorem low11 {f : Fin 2 → A →+* B} {g : Fin 3 → B →+* C}
    (h : FaceIdentities f g) (x : A) : g 2 (f 1 x) = g 1 (f 1 x) := by
  simpa using h.apply 1 1 (by decide) x

end FaceIdentities

def alternating0 {A B : Type u} [CommRing A] [CommRing B]
    (f : Fin 2 → A →+* B) : A →+ B :=
  (f 0).toAddMonoidHom - (f 1).toAddMonoidHom

def alternating1 {A B : Type u} [CommRing A] [CommRing B]
    (f : Fin 3 → A →+* B) : A →+ B :=
  (f 0).toAddMonoidHom - (f 1).toAddMonoidHom + (f 2).toAddMonoidHom

def alternating2 {A B : Type u} [CommRing A] [CommRing B]
    (f : Fin 4 → A →+* B) : A →+ B :=
  (f 0).toAddMonoidHom - (f 1).toAddMonoidHom +
    (f 2).toAddMonoidHom - (f 3).toAddMonoidHom

@[simp] theorem alternating0_apply {A B : Type u} [CommRing A] [CommRing B]
    (f : Fin 2 → A →+* B) (x : A) : alternating0 f x = f 0 x - f 1 x := rfl

@[simp] theorem alternating1_apply {A B : Type u} [CommRing A] [CommRing B]
    (f : Fin 3 → A →+* B) (x : A) : alternating1 f x = f 0 x - f 1 x + f 2 x := rfl

@[simp] theorem alternating2_apply {A B : Type u} [CommRing A] [CommRing B]
    (f : Fin 4 → A →+* B) (x : A) :
    alternating2 f x = f 0 x - f 1 x + f 2 x - f 3 x := rfl

theorem alternating1_alternating0 {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    {f : Fin 2 → A →+* B} {g : Fin 3 → B →+* C}
    (h : FaceIdentities f g) (x : A) : alternating1 g (alternating0 f x) = 0 := by
  simp only [alternating1_apply, alternating0_apply, map_sub]
  rw [h.low00, h.low01, h.low11]
  abel

/-- The actual low-degree bicosimplicial ring data. -/
structure Data (R00 R10 R01 R20 R11 R02 R30 R21 R12 R03 : Type u)
    [CommRing R00] [CommRing R10] [CommRing R01] [CommRing R20] [CommRing R11]
    [CommRing R02] [CommRing R30] [CommRing R21] [CommRing R12] [CommRing R03] where
  v00 : Fin 2 → R00 →+* R10
  h00 : Fin 2 → R00 →+* R01
  v10 : Fin 3 → R10 →+* R20
  h10 : Fin 2 → R10 →+* R11
  v01 : Fin 2 → R01 →+* R11
  h01 : Fin 3 → R01 →+* R02
  v20 : Fin 4 → R20 →+* R30
  h20 : Fin 2 → R20 →+* R21
  v11 : Fin 3 → R11 →+* R21
  h11 : Fin 3 → R11 →+* R12
  v02 : Fin 2 → R02 →+* R12
  h02 : Fin 4 → R02 →+* R03
  cofaceV00 : FaceIdentities v00 v10
  cofaceV10 : FaceIdentities v10 v20
  cofaceV01 : FaceIdentities v01 v11
  cofaceH00 : FaceIdentities h00 h01
  cofaceH01 : FaceIdentities h01 h02
  cofaceH10 : FaceIdentities h10 h11
  mixed00 : ∀ i j, (v01 i).comp (h00 j) = (h10 j).comp (v00 i)
  mixed10 : ∀ i j, (v11 i).comp (h10 j) = (h20 j).comp (v10 i)
  mixed01 : ∀ i j, (v02 i).comp (h01 j) = (h11 j).comp (v01 i)

namespace Data

variable {R00 R10 R01 R20 R11 R02 R30 R21 R12 R03 : Type u}
  [CommRing R00] [CommRing R10] [CommRing R01] [CommRing R20] [CommRing R11]
  [CommRing R02] [CommRing R30] [CommRing R21] [CommRing R12] [CommRing R03]
  (D : Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03)

def vertical : SheafCupProduct.Coface.Data R00 R10 R20 R30 where
  δ0 := D.v00
  δ1 := D.v10
  δ2 := D.v20
  coface01 := D.cofaceV00
  coface12 := D.cofaceV10

def horizontal : SheafCupProduct.Coface.Data R00 R01 R02 R03 where
  δ0 := D.h00
  δ1 := D.h01
  δ2 := D.h02
  coface01 := D.cofaceH00
  coface12 := D.cofaceH01

abbrev dv00 : R00 →+ R10 := alternating0 D.v00
abbrev dh00 : R00 →+ R01 := alternating0 D.h00
abbrev dv10 : R10 →+ R20 := alternating1 D.v10
abbrev dh10 : R10 →+ R11 := alternating0 D.h10
abbrev dv01 : R01 →+ R11 := alternating0 D.v01
abbrev dh01 : R01 →+ R02 := alternating1 D.h01
abbrev dv20 : R20 →+ R30 := alternating2 D.v20
abbrev dh20 : R20 →+ R21 := alternating0 D.h20
abbrev dv11 : R11 →+ R21 := alternating1 D.v11
abbrev dh11 : R11 →+ R12 := alternating1 D.h11
abbrev dv02 : R02 →+ R12 := alternating0 D.v02
abbrev dh02 : R02 →+ R03 := alternating2 D.h02

theorem mixed00_apply (i j : Fin 2) (x : R00) :
    D.v01 i (D.h00 j x) = D.h10 j (D.v00 i x) :=
  congrArg (fun φ : R00 →+* R11 => φ x) (D.mixed00 i j)

theorem mixed10_apply (i : Fin 3) (j : Fin 2) (x : R10) :
    D.v11 i (D.h10 j x) = D.h20 j (D.v10 i x) :=
  congrArg (fun φ : R10 →+* R21 => φ x) (D.mixed10 i j)

theorem mixed01_apply (i : Fin 2) (j : Fin 3) (x : R01) :
    D.v02 i (D.h01 j x) = D.h11 j (D.v01 i x) :=
  congrArg (fun φ : R01 →+* R12 => φ x) (D.mixed01 i j)

end Data

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalAlgebra
