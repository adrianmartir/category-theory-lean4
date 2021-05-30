import category_theory.Category

namespace category_theory

-- Variable declarations seem to be a good way to do implicit arguments
-- We already saw that they are quite natural in natural language in naproche.
variable (J : hom_struct) [category J]
variable {C : hom_struct} [category C]

-- I also guess that we could simply annotate the latex code with
-- identifiers. Patterns are defined in definitions, which can be
-- named in latex, so that gives us lean identifiers for free.
-- Theorems are also named, so we can just reuse the identifiers from there.

-- (We may also want anonymous proofs, not being part of a struct declaration.
-- One could do that by writing terms like `\prove_later{[proof_label]}`, but this is
-- not a feature that is absolutely necessary.)

-- Accessing lean from tex should also be easy. I think that I simply need
-- to allow lean identifier literals and imports in the beginning of the 
-- file.

def const (c: C.obj) : functor J C := {
  obj := (fun _ => c),
  map := (fun _ => id' c),
  map_id := rfl,
  map_comp := by
    intros
    simp
}

def constf : functor C (functor_cat J C) := {
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
    simp [id', id_trans]
    apply funext
    intros
    simp [const]
  map_comp := by
    intros
    apply nat_ext
    simp [comp, vcomp]
}

-- Should be the constant functor composed with the yoneda embedding
-- https://github.com/leanprover-community/mathlib/blob/4ddbdc1b476032fb56a9b8ccc4a55c81f6523ec8/src/category_theory/limits/cones.lean
-- def cone : functor Cᵒᵖ (Type v) := nat_trans (const )