import CategoryTheory.Category

namespace Category_theory

open CategoryTheory
open Category

variable (J : HomStruct) [Category J]
variable {C : HomStruct} [Category C]

def const (c: C.obj) : Functor J C := {
  obj := (fun _ => c),
  map := (fun _ => id' c),
  map_id := rfl,
  map_comp := by
    intros
    simp
}

def constf : Functor C (FunctorCat J C) := {
  obj := @const J _ C _
  map := fun f => {
    app := fun _ => f,
    naturality := by
      intros
      simp [const]
  }
  map_id := by
    intros
    apply nat_ext
    simp [id', idTrans]
    apply funext
    intros
    simp [const]
  map_comp := by
    intros
    apply nat_ext
    simp [comp, vComp]
}

-- Should be the constant Functor composed with the yoneda embedding
-- https://github.com/leanprover-community/mathlib/blob/4ddbdc1b476032fb56a9b8ccc4a55c81f6523ec8/src/Category_theory/limits/cones.lean
-- def cone : Functor Cᵒᵖ (Type v) := nat_trans (const )
