-- Some basic category-theoretic constructions
namespace CategoryTheory

structure HomStruct where
  obj : Type u
  hom : obj → obj → Type v


class Category (C : HomStruct) where
  id' : (c : C.obj) → C.hom c c
  comp : {c d e : C.obj} → C.hom c d → C.hom d e → C.hom c e
  id_comp : {c d : C.obj} → (f : C.hom c d) → comp (id' c) f = f
  comp_id : {c d : C.obj} → (f : C.hom c d) → comp f (id' d) = f
  assoc : {a b c d : C.obj} → (f : C.hom a b) → (g : C.hom b c)
      → (h : C.hom c d) → comp (comp f g) h = comp f (comp g h)

open HomStruct
open Category

notation:80 lhs " ∘ " rhs:81  => comp rhs lhs

attribute [simp] id_comp comp_id assoc

section Set

universe u

abbrev SmallCategory (C : HomStruct) := Category.{u,u} C
abbrev LargeCategory (C : HomStruct) := Category.{u+1,u} C


def Set : HomStruct := {
  obj := Type u,
  hom := fun a b => a → b
}

instance Set.Category : LargeCategory Set :=
{ id'     := fun a x => x
  comp    := fun f g x => g (f x)
  id_comp := by
    intros
    simp
  comp_id := by
    intros
    simp
  assoc := by
    intros
    simp
}

end Set


def HomStruct.opposite (C: HomStruct) : HomStruct := {
  obj := C.obj
  hom := fun f g => C.hom g f
}

notation:1030 arg "ᵒᵖ"  => HomStruct.opposite arg

instance Category.opposite (C: HomStruct) [Category C]: Category Cᵒᵖ := {
  id' := fun c => id' (C := C) c
  comp := fun f g => comp (C := C) g f
  id_comp := by
    intros
    simp
  comp_id := by
    intros
    simp
  assoc := by
    intros
    simp
}

-- Note that this doesn't allow for the usual trick where we
-- replace `C` by `Cᵒᵖ` in a lemma and then reduce `Cᵒᵖᵒᵖ` to `C`
-- since this is *an equality of `HomStruct`s* and that means that
-- we can't construct a motive where the `HomStruct` `C` has the
-- `[Category C]` instance.
-- We would need bundled structures to actually use this trick.
theorem opop (C: HomStruct) : Cᵒᵖᵒᵖ = C  := by
  revert C
  intro { obj := obj, hom := hom}
  simp [HomStruct.opposite]

attribute [simp] opop


def inverses (C: HomStruct) [Category C] {c d: C.obj} (f: C.hom c d) (g: C.hom d c) := g ∘ f = id' c ∧ f ∘ g = id' d

theorem inverse_unique (C: HomStruct) [Category C] {c d: C.obj} (f: C.hom c d) (g h: C.hom d c) : inverses C f g ∧ inverses C f h → g = h := by
  intro ⟨⟨_,p⟩,⟨q,_⟩⟩
  have r : (h ∘ f) ∘ g = h := by
    rw [<- assoc, p, id_comp]

  rw [<- r, q, comp_id]

def isomorphism (C: HomStruct) [Category C] {c d: C.obj} (f: C.hom c d) :=
  exists (g: C.hom d c), inverses C f g

namespace Function

variable {A: Type _} {B: Type _}

def inverses (f: A → B) (g: B → A) :=
  (Function.comp g f = id) ∧ (Function.comp f g  = id)

theorem inverses_sym (f: A → B) (g: B → A) : inverses f g <-> inverses g f := by
  simp [inverses]
  exact ⟨
    by
      intro ⟨p,q⟩
      exact ⟨q,p⟩,
    by
      intro ⟨p,q⟩
      exact ⟨q,p⟩
  ⟩


def isomorphism (f: A → B) :=
  exists (g: B → A), inverses f g

end Function

structure Functor (C D: HomStruct) [Category C] [Category D] where
  obj : C.obj → D.obj
  map : {c d : C.obj} → C.hom c d → D.hom (obj c) (obj d)
  map_id : {c : C.obj} → map (id' c) = id' (obj c)
  map_comp : {c d e : C.obj} → (f : C.hom c d) → (g : C.hom d e) → map (g ∘ f) = map g ∘ map f

attribute [simp] Functor.map_id Functor.map_comp

theorem Functor.ext {C D : HomStruct} [Category C] [Category D]: (F G : Functor C D) → (p: F.obj = G.obj) →
  (q: (fun c d (f: C.hom c d) => F.map f)
    ≅ (fun c d (f: C.hom c d) => G.map f))
  → F = G
  := by
  intro { obj := F, map := FMap, ..}
  intro { obj := G, map := GMap, ..}
  intro p q
  simp at p q
  simp -- applies propext
  exact ⟨p,q⟩


def fId (C: HomStruct) [Category C] : Functor C C := {
  obj := id
  map := id
  map_id := by
    intros
    rfl
  map_comp := by
    intros
    rfl
}

def fComp {C D E: HomStruct} [Category C] [Category D] [Category E] (F: Functor C D) (G: Functor D E) : Functor C E := {
  obj := Function.comp G.obj F.obj
  map := fun f => G.map (F.map f)
  map_id := by
    intros
    simp
  map_comp := by
    intros
    simp
}


structure BundledCategory where
  base : HomStruct
  inst : Category base

instance (C: BundledCategory) : Category C.base := C.inst

def Cat : HomStruct.{max (u + 1) (v + 1), max u v} := {
  obj := BundledCategory.{u,v},
  hom := fun C D => Functor C.base D.base
}

instance : Category Cat where
  id' := fun {C} => fId C.base
  comp := fComp
  id_comp := by
    intros
    simp [fComp, fId]

    apply Functor.ext
    simp [Function.comp]
    simp
    exact HEq.rfl

  comp_id := by
    intros
    simp [fComp, fId]

    apply Functor.ext
    simp [Function.comp]
    simp
    exact HEq.rfl

  assoc := by
    intros
    simp [fComp]

    apply Functor.ext
    simp [Function.comp]
    simp
    exact HEq.rfl


def fully_faithful {C: HomStruct} [Category C] {D: HomStruct} [Category D] (F: Functor C D) :=
  forall c d : C.obj, Function.isomorphism (F.map (c := c) (d := d))

section NatTrans

variable {C : HomStruct} [Category C]
variable {D : HomStruct} [Category D]

structure NatTrans (F G : Functor C D) :=
  app : (c : C.obj) → D.hom (F.obj c) (G.obj c)
  naturality : {c d : C.obj} → (f : C.hom c d) → app d ∘ (F.map f) = (G.map f) ∘ app c

open NatTrans

theorem NatTrans.ext {F G : Functor C D} : (η μ : NatTrans F G) → (p: η.app = μ.app) → (η = μ) := by
  intro { app := η, .. }
  intro { app := μ, .. }
  intro p
  simp at p
  simp -- applies propext
  exact p


def FunctorCat (C: HomStruct) [Category C] (D: HomStruct) [Category D]: HomStruct := {
  obj := Functor C D
  hom := NatTrans
}

def idTrans (F : Functor C D) : NatTrans F F := {
  app := fun c => id' (Functor.obj F c),
  naturality := by
    intro c d f
    simp
}

def vComp {F G H : Functor C D} (η : NatTrans F G) (μ : NatTrans G H) : NatTrans F H := {
  app := fun c => (app μ c) ∘ (app η c),
  naturality := by
    intro c d f
    simp
    rw [<- naturality μ f]
    rw [<- Category.assoc]
    rw [naturality η f]
    rw [Category.assoc]
}

instance : Category (FunctorCat C D) := {
  id'     := idTrans,
  comp    := vComp,
  id_comp := by
    intros
    apply NatTrans.ext
    simp [id', idTrans, comp, vComp]
  comp_id := by
    intros
    apply NatTrans.ext
    simp [id', idTrans, comp, vComp]
  assoc := by
    intros
    apply NatTrans.ext
    simp [comp, vComp]
}

end NatTrans

section Yoneda

universes u v


variable {C : HomStruct.{u,v}} [Category C]


def yObj (c: C.obj) : (Functor Cᵒᵖ Set.{v}) := {
    obj := fun d => C.hom d c
    -- f gets sent to precomposition with f
    map := fun f g => g ∘ f
    map_id := by
      intros
      simp [id']
    map_comp := by
      intros
      simp [comp]
  }


def yMap {c d: C.obj} (f: C.hom c d) : NatTrans (yObj c) (yObj d) := {
  app := fun c g => f ∘ g
  naturality := by
    intros
    simp [yObj, comp]
}

def y : Functor C (FunctorCat Cᵒᵖ Set.{v}) := {
  obj := yObj
  map := yMap
  map_id := by
    intros
    apply NatTrans.ext
    simp [yMap, id', idTrans]
  map_comp := by
    intros
    apply NatTrans.ext
    simp [yMap, comp, vComp]
}


def yonedaMap (c : C.obj) (F: Functor Cᵒᵖ Set.{v}) (η: NatTrans (y.obj c) F) : F.obj c := η.app c (id' c)

def yonedaMapInv (c : C.obj) (F: Functor Cᵒᵖ Set.{v}) (x: F.obj c) : NatTrans (y.obj c) F := {
  app := fun d f => F.map f x
  naturality := by
    intros d e f
    simp [y, yObj, comp]
    apply funext
    intros h
    -- It honestly is a bit confusing not knowing in which category
    -- the composition takes place
    have p: comp (C := C) f h = comp (C := Cᵒᵖ) h f  := by rfl
    rw [p, Functor.map_comp]
    simp [comp]
}


theorem yoneda (c : C.obj) (F: Functor Cᵒᵖ Set.{v}) : Function.inverses (yonedaMap c F) (yonedaMapInv c F) := ⟨
  by
    simp [yonedaMap, yonedaMapInv]
    apply funext
    intro { app := η, naturality := nat }
    simp [comp,id',y,yObj]
    funext d f
    -- Rewrite the application in the goal as a composition in order
    -- to apply naturality
    have p: F.map f (η c (id' c)) = (comp (η c) (F.map f)) (id' c) := by rfl
    rw [p, <- nat f]
    simp [y, yObj, comp],
  by
    simp [yonedaMap, yonedaMapInv, Function.comp]
    funext x
    have p: id' (C := C) c = id' (C := Cᵒᵖ) c  := by rfl
    rw [p, Functor.map_id]
    simp [id']
⟩


theorem y_fully_faithful: fully_faithful (y (C := C)) := by
  simp [fully_faithful, Function.isomorphism]
  intros c d

  -- The crucial insight is that `y.map` is in fact equal to `yonedaMapInverse` and thus by the yoneda lemma has an inverse
  have yoneda := yoneda c (y.obj d)

  refine ⟨ yonedaMap c (y.obj d), ?_ ⟩

  have p: yonedaMapInv c (Functor.obj y d) = y.map := by
    funext f
    apply NatTrans.ext
    simp [yonedaMapInv, y, yMap, yObj]

  rw [<- p, Function.inverses_sym]
  exact yoneda

end Yoneda

end CategoryTheory
