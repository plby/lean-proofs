import Mathlib

/-!
A small, self-contained chain model for order-complex flags.

The empty list is the augmented (-1)-simplex.  A nonempty list has the
usual alternating deletion boundary.  We deliberately work first in the
free module on all lists: strict flags form a boundary-stable submodule,
while the algebraic cone/prism identities are simplest in the ambient
module.
-/

namespace SourceFlags

open scoped BigOperators

noncomputable section

variable {α β γ : Type*}

abbrev Chain (α : Type*) := List α →₀ ℤ

def basis (l : List α) : Chain α := Finsupp.single l 1

def linearOfBasis (f : List α → Chain β) : Chain α →ₗ[ℤ] Chain β :=
  (Finsupp.lift (Chain β) ℤ (List α)) f

@[simp] theorem linearOfBasis_basis (f : List α → Chain β) (l : List α) :
    linearOfBasis f (basis l) = f l := by
  simp [linearOfBasis, basis]

def mapLists (f : List α → List β) : Chain α →ₗ[ℤ] Chain β :=
  linearOfBasis fun l => basis (f l)

@[simp] theorem mapLists_basis (f : List α → List β) (l : List α) :
    mapLists f (basis l) = basis (f l) := by
  simp [mapLists]

def mapVertices (f : α → β) : Chain α →ₗ[ℤ] Chain β :=
  mapLists (List.map f)

@[simp] theorem mapVertices_basis (f : α → β) (l : List α) :
    mapVertices f (basis l) = basis (l.map f) := by
  simp [mapVertices]

@[simp] theorem mapVertices_id_apply (c : Chain α) :
    mapVertices id c = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single l z =>
      rw [show Finsupp.single l z = z • basis l by simp [basis]]
      simp

def prepend (x : α) : Chain α →ₗ[ℤ] Chain α :=
  mapLists (List.cons x)

@[simp] theorem prepend_basis (x : α) (l : List α) :
    prepend x (basis l) = basis (x :: l) := by
  simp [prepend]

/- The recursive formula is exactly
   d[x0,...,xq] = [x1,...,xq] - x0 * d[x1,...,xq]. -/
def boundaryBasis : List α → Chain α
  | [] => 0
  | x :: xs => basis xs - prepend x (boundaryBasis xs)

def boundary : Chain α →ₗ[ℤ] Chain α :=
  linearOfBasis boundaryBasis

@[simp] theorem boundary_basis (l : List α) :
    boundary (basis l) = boundaryBasis l := by
  simp [boundary]

@[simp] theorem boundaryBasis_nil : boundaryBasis ([] : List α) = 0 := rfl

@[simp] theorem boundaryBasis_cons (x : α) (xs : List α) :
    boundaryBasis (x :: xs) = basis xs - prepend x (boundaryBasis xs) := rfl

theorem boundary_prepend (x : α) (c : Chain α) :
    boundary (prepend x c) = c - prepend x (boundary c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
      simp only [map_add]
      rw [hc, hd]
      module
  | single l z =>
    rw [show Finsupp.single l z = z • basis l by simp [basis]]
    simp [boundaryBasis_cons, smul_sub]

theorem mapVertices_prepend (f : α → β) (x : α) (c : Chain α) :
    mapVertices f (prepend x c) = prepend (f x) (mapVertices f c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single l z =>
    rw [show Finsupp.single l z = z • basis l by simp [basis]]
    simp

theorem boundary_mapVertices_basis (f : α → β) (l : List α) :
    boundary (mapVertices f (basis l)) = mapVertices f (boundary (basis l)) := by
  induction l with
  | nil => simp [boundaryBasis]
  | cons x xs ih =>
      simp only [mapVertices_basis, List.map_cons, boundary_basis, boundaryBasis_cons,
        map_sub, mapVertices_basis, mapVertices_prepend]
      rw [show boundaryBasis (List.map f xs) = boundary (basis (List.map f xs)) by simp]
      rw [show mapVertices f (boundaryBasis xs) =
          mapVertices f (boundary (basis xs)) by simp]
      have ih' : boundary (basis (List.map f xs)) =
          mapVertices f (boundary (basis xs)) := by simpa using ih
      rw [ih']

theorem boundary_mapVertices (f : α → β) (c : Chain α) :
    boundary (mapVertices f c) = mapVertices f (boundary c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single l z =>
      rw [show Finsupp.single l z = z • basis l by simp [basis]]
      simp only [map_smul]
      rw [boundary_mapVertices_basis]

theorem boundary_boundary_basis (l : List α) : boundary (boundary (basis l)) = 0 := by
  induction l with
  | nil => simp [boundaryBasis]
  | cons x xs ih =>
      simp only [boundary_basis, boundaryBasis_cons, map_sub, boundary_prepend]
      rw [show boundaryBasis xs = boundary (basis xs) by simp]
      rw [ih]
      simp

theorem boundary_boundary (c : Chain α) : boundary (boundary c) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [map_add, hc, hd]
  | single l z =>
    rw [show Finsupp.single l z = z • basis l by simp [basis]]
    simp only [map_smul]
    rw [boundary_boundary_basis]
    simp

/- Cone on the image of a vertex map. -/
def cone (v : β) (J : α → β) : Chain α →ₗ[ℤ] Chain β :=
  (prepend v).comp (mapVertices J)

theorem boundary_cone (v : β) (J : α → β) (c : Chain α) :
    boundary (cone v J c) + cone v J (boundary c) = mapVertices J c := by
  simp [cone, boundary_prepend, boundary_mapVertices]

/- The usual prism for the pointwise-comparable maps f and g.  The order
assumptions are needed only to know that its terms are flags; the chain
identity itself is purely algebraic. -/
def prismBasis (f g : α → β) : List α → Chain β
  | [] => 0
  | x :: xs =>
      basis (f x :: g x :: xs.map g) - prepend (f x) (prismBasis f g xs)

def prism (f g : α → β) : Chain α →ₗ[ℤ] Chain β :=
  linearOfBasis (prismBasis f g)

@[simp] theorem prism_basis (f g : α → β) (l : List α) :
    prism f g (basis l) = prismBasis f g l := by
  simp [prism]

@[simp] theorem prismBasis_nil (f g : α → β) :
    prismBasis f g [] = 0 := rfl

@[simp] theorem prismBasis_cons (f g : α → β) (x : α) (xs : List α) :
    prismBasis f g (x :: xs) =
      basis (f x :: g x :: xs.map g) - prepend (f x) (prismBasis f g xs) := rfl

theorem prism_prepend (f g : α → β) (x : α) (c : Chain α) :
    prism f g (prepend x c) =
      prepend (f x) (prepend (g x) (mapVertices g c)) -
        prepend (f x) (prism f g c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
      simp only [map_add]
      rw [hc, hd]
      module
  | single l z =>
    rw [show Finsupp.single l z = z • basis l by simp [basis]]
    simp [prism, prismBasis_cons, sub_eq_add_neg]

theorem boundary_prism_add_prism_boundary_basis
    (f g : α → β) (l : List α) :
    boundary (prism f g (basis l)) + prism f g (boundary (basis l)) =
      mapVertices g (basis l) - mapVertices f (basis l) := by
  induction l with
  | nil => simp [prismBasis, boundaryBasis]
  | cons x xs ih =>
      simp only [prism_basis, prismBasis_cons, map_sub, boundary_prepend,
        boundary_basis, boundaryBasis_cons, prism_prepend, mapVertices_basis,
        List.map_cons]
      have hmap := boundary_mapVertices_basis g xs
      simp only [mapVertices_basis, boundary_basis] at hmap
      have ih' := ih
      simp only [prism_basis, boundary_basis, mapVertices_basis] at ih'
      rw [hmap]
      have ih'' := congrArg (prepend (f x)) ih'
      simp only [map_add, map_sub] at ih''
      rw [show basis (f x :: List.map f xs) =
        prepend (f x) (basis (List.map f xs)) by simp]
      calc
        basis (g x :: List.map g xs) -
              (prepend (f x) (basis (List.map g xs)) -
                prepend (f x) (prepend (g x) (mapVertices g (boundaryBasis xs)))) -
              (prismBasis f g xs - prepend (f x) (boundary (prismBasis f g xs))) +
              (prismBasis f g xs -
                (prepend (f x) (prepend (g x) (mapVertices g (boundaryBasis xs))) -
                  prepend (f x) (prism f g (boundaryBasis xs)))) =
            basis (g x :: List.map g xs) - prepend (f x) (basis (List.map g xs)) +
              (prepend (f x) (boundary (prismBasis f g xs)) +
                prepend (f x) (prism f g (boundaryBasis xs))) := by module
        _ = basis (g x :: List.map g xs) - prepend (f x) (basis (List.map g xs)) +
              (prepend (f x) (basis (List.map g xs)) -
                prepend (f x) (basis (List.map f xs))) := by rw [ih'']
        _ = basis (g x :: List.map g xs) - prepend (f x) (basis (List.map f xs)) := by
          module

theorem boundary_prism_add_prism_boundary (f g : α → β) (c : Chain α) :
    boundary (prism f g c) + prism f g (boundary c) =
      mapVertices g c - mapVertices f c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
      simp only [map_add]
      calc
        boundary (prism f g c) + boundary (prism f g d) +
              (prism f g (boundary c) + prism f g (boundary d)) =
            (boundary (prism f g c) + prism f g (boundary c)) +
              (boundary (prism f g d) + prism f g (boundary d)) := by module
        _ = (mapVertices g c - mapVertices f c) +
              (mapVertices g d - mapVertices f d) := by rw [hc, hd]
        _ = mapVertices g c + mapVertices g d -
              (mapVertices f c + mapVertices f d) := by module
  | single l z =>
    rw [show Finsupp.single l z = z • basis l by simp [basis]]
    simp only [map_smul]
    have h := boundary_prism_add_prism_boundary_basis f g l
    calc
      z • boundary (prism f g (basis l)) +
          z • prism f g (boundary (basis l)) =
        z • (boundary (prism f g (basis l)) +
          prism f g (boundary (basis l))) := by module
      _ = z • (mapVertices g (basis l) - mapVertices f (basis l)) := by rw [h]
      _ = z • mapVertices g (basis l) - z • mapVertices f (basis l) := by module

/- Fresh-join contraction: J is the operation A |-> A union {fresh}; v is
the fresh singleton. -/
def freshFill (v : α) (J : α → α) : Chain α →ₗ[ℤ] Chain α :=
  cone v J - prism id J

theorem boundary_freshFill_add_freshFill_boundary
    (v : α) (J : α → α) (c : Chain α) :
    boundary (freshFill v J c) + freshFill v J (boundary c) = c := by
  rw [show freshFill v J c = cone v J c - prism id J c by rfl]
  rw [show freshFill v J (boundary c) =
      cone v J (boundary c) - prism id J (boundary c) by rfl]
  have hc := boundary_cone v J c
  have hp := boundary_prism_add_prism_boundary id J c
  simp only [map_sub]
  simp only [mapVertices_id_apply] at hp
  calc
    boundary (cone v J c) - boundary (prism id J c) +
        (cone v J (boundary c) - prism id J (boundary c)) =
      (boundary (cone v J c) + cone v J (boundary c)) -
        (boundary (prism id J c) + prism id J (boundary c)) := by module
    _ = mapVertices J c - (mapVertices J c - c) := by rw [hc, hp]
    _ = c := by module

theorem boundary_freshFill_of_cycle
    (v : α) (J : α → α) (c : Chain α) (hc : boundary c = 0) :
    boundary (freshFill v J c) = c := by
  have h := boundary_freshFill_add_freshFill_boundary v J c
  simpa [hc] using h

/- Strict order-complex flags. -/
def IsFlag (r : α → α → Prop) (l : List α) : Prop := l.Pairwise r

/- The group action on chains is just pointwise action on flag vertices. -/
section Action

variable (G : Type*) [Group G] [MulAction G α]

def act (g : G) : Chain α →ₗ[ℤ] Chain α :=
  mapVertices (g • ·)

@[simp] theorem act_basis (g : G) (l : List α) :
    act G g (basis l) = basis (l.map (g • ·)) := by
  simp [act]

theorem boundary_act (g : G) (c : Chain α) :
    boundary (act G g c) = act G g (boundary c) :=
  boundary_mapVertices _ _

end Action

/- Abstract recursion underlying the generalized-sphere chains.  It is
stated for arbitrary alternating operators; the concrete operators are
tau and norm on cyclic group chains. -/
section Recursion

variable (A B F : Chain α →ₗ[ℤ] Chain α)

def alternatingOp (i : ℕ) : Chain α →ₗ[ℤ] Chain α :=
  if i % 2 = 0 then B else A

def sphereChain (x0 : Chain α) : ℕ → Chain α
  | 0 => x0
  | i + 1 => F (alternatingOp A B (i + 1) (sphereChain x0 i))

theorem fill_operator_of_cycle
    (hF : ∀ c, boundary (F c) + F (boundary c) = c)
    {c : Chain α} (hc : boundary c = 0) : boundary (F c) = c := by
  simpa [hc] using hF c

theorem alternating_step_A
    (hF : ∀ c, boundary (F c) + F (boundary c) = c)
    (hA : ∀ c, boundary (A c) = A (boundary c))
    (hAB : ∀ c, A (B c) = 0)
    {x y : Chain α} (hy : boundary y = B x) :
    boundary (F (A y)) = A y := by
  apply fill_operator_of_cycle F hF
  rw [hA, hy, hAB]

theorem alternating_step_B
    (hF : ∀ c, boundary (F c) + F (boundary c) = c)
    (hB : ∀ c, boundary (B c) = B (boundary c))
    (hBA : ∀ c, B (A c) = 0)
    {x y : Chain α} (hy : boundary y = A x) :
    boundary (F (B y)) = B y := by
  apply fill_operator_of_cycle F hF
  rw [hB, hy, hBA]

end Recursion

end

end SourceFlags
