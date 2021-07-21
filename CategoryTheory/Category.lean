-- Some basic category-theoretic constructions
namespace CategoryTheory

structure HomStruct where
  obj : Type u
  hom : obj → obj → Type v


class IsCategory (C : HomStruct) where
  id' : (c : C.obj) → C.hom c c
  comp : {c d e : C.obj} → C.hom c d → C.hom d e → C.hom c e
  id_comp : {c d : C.obj} → (f : C.hom c d) → comp (id' c) f = f
  comp_id : {c d : C.obj} → (f : C.hom c d) → comp f (id' d) = f
  assoc : {a b c d : C.obj} → (f : C.hom a b) → (g : C.hom b c)
      → (h : C.hom c d) → comp (comp f g) h = comp f (comp g h)

open HomStruct
open IsCategory

theorem IsCategory.ext (C: HomStruct):
  (s t: IsCategory C)
  → @comp C s = @comp C t
  → (r: s.id' = t.id')
  → s = t := by
    intro {comp := sComp, id' := sId, ..}
    intro {comp := tComp, id' := tId, ..}
    intro p q
    simp [id'] at q
    simp [comp] at p
    subst p q
    simp

notation:80 lhs " ∘ " rhs:81  => comp rhs lhs

attribute [simp] id_comp comp_id assoc


structure Category where
  base : HomStruct
  inst : IsCategory base

-- We also want all `HomStruct` fields
def Category.obj (C: Category) := C.base.obj

def Category.hom (C: Category) := C.base.hom

-- Bundled to unbundled automatic conversion
instance (C: Category) : IsCategory C.base := C.inst

def bundle (C: HomStruct) [inst: IsCategory C] : Category where
  base := C
  inst := inst

-- Unbundled to bundled automatic conversion
-- This can only be used for resolving unification problems!
unif_hint (C : Category) (base : HomStruct) [IsCategory base] where
  C =?= bundle base
  |-
  C.base =?= base

-- set_option trace.Meta.Tactic.subst true in
set_option pp.explicit true in
theorem Category.ext :
  (C D: Category)
  → (p: C.base = D.base)
  → C.inst ≅ D.inst
  → C = D := by
  intro { base := CBase, inst := CInst }
  intro { base := DBase, inst := DInst }
  intro p q
  simp at p
  simp -- applies extensionality for records
  refine ⟨p, ?m⟩
  subst p
  exact q

section Set

universe u

abbrev SmallCategory := Category.{u,u}
abbrev LargeCategory := Category.{u+1,u}


-- Note that we don't even to construct this by providing an instance
def Set : LargeCategory where
  base := {
    obj := Type u,
    hom := fun a b => a → b
  }
  inst := {
    id':= fun a x => x
    comp := fun f g x => g (f x)
    id_comp := by
      intros
      simp [id', comp]
    comp_id := by
      intros
      simp [id', comp]
    assoc := by
      intros
      simp [comp]
  }

end Set

@[reducible]
def HomStruct.opposite (C: HomStruct) : HomStruct := {
  obj := C.obj
  hom := fun f g => C.hom g f
}

notation:1030 arg "ᵒᵖ"  => HomStruct.opposite arg

@[reducible]
def Category.opposite (C: Category): Category where
  base := HomStruct.opposite C.base
  inst := {
    id' := fun c => id' (C := C.base) c
    comp := fun f g => comp (C := C.base) g f
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

notation:1030 arg "ᵒᵖ"  => Category.opposite arg

@[simp] theorem HomStruct.opop (C: HomStruct) : Cᵒᵖᵒᵖ = C  :=
  match C with
  | { obj := obj, hom := hom } => rfl

-- This innocent-looking proof took a long time to write.
-- The insight is that we *cannot* apply `HomStruct.opposite`
-- because because that breaks type checking for `inst`
-- part of the category. Instead, we expand the opposite
-- definitions until the `inst` fields are in definitionally
-- equal types. At this point we can simply reduce our
-- heterogeneous equality to a regular equality and
-- everything is easy.
-- set_option pp.explicit true in
@[simp] theorem Category.opop (C: Category) : Cᵒᵖᵒᵖ = C := by
  revert C
  intro { base := { obj := obj, hom := hom}, inst := inst }
  apply Category.ext
  case p =>
    rfl
  case a =>
    apply heqOfEq
    apply IsCategory.ext
    case h.a =>
      -- Here we need to actually expand `comp` for the opposite
      -- category, which currently is a barrier
      -- to having `C` be definitionally equal to `Cᵒᵖᵒᵖ`
      simp [↑comp]
      -- Moreover, `simp only` doesn't even work here.
    case h.r =>
      simp [id']


def inverses (C: Category) {c d: C.obj} (f: C.hom c d) (g: C.hom d c) := g ∘ f = id' c ∧ f ∘ g = id' d

theorem inverse_unique (C: Category) {c d: C.obj} (f: C.hom c d) (g h: C.base.hom d c) : inverses C f g ∧ inverses C f h → g = h := by
  intro ⟨⟨_,p⟩,⟨q,_⟩⟩
  have r : (h ∘ f) ∘ g = h := by
    rw [<- assoc, p, id_comp]

  rw [<- r, q, comp_id]

def isomorphism (C: Category) {c d: C.obj} (f: C.hom c d) :=
  exists (g: C.hom d c), inverses C f g

namespace Function

variable {A: Type _} {B: Type _}

def inverses (f: A → B) (g: B → A) :=
  (Function.comp g f = id) ∧ (Function.comp f g  = id)

theorem inverses_sym (f: A → B) (g: B → A) : inverses f g <-> inverses g f := by
  simp [inverses]
  constructor
  case mp =>
    simp_all
  case mpr =>
    simp_all


def isomorphism (f: A → B) :=
  exists (g: B → A), inverses f g

end Function

structure Functor (C D: Category) where
  obj : C.obj → D.obj
  map : {c d : C.obj} → C.hom c d → D.hom (obj c) (obj d)
  map_id : {c : C.obj} → map (id' c) = id' (obj c)
  map_comp : {c d e : C.obj} → (f : C.hom c d) → (g : C.hom d e) → map (g ∘ f) = map g ∘ map f

attribute [simp] Functor.map_id Functor.map_comp

theorem Functor.ext {C D : Category}: (F G : Functor C D) → (p: F.obj = G.obj) →
  (q: (fun c d (f: C.hom c d) => F.map f)
    ≅ (fun c d (f: C.hom c d) => G.map f))
  → F = G
  := by
  intro { obj := F, map := FMap, ..}
  intro { obj := G, map := GMap, ..}
  intro p q
  simp_all


def fId (C: Category) : Functor C C := {
  obj := id
  map := id
  map_id := by
    intros
    rfl
  map_comp := by
    intros
    rfl
}

def fComp {C D E: Category} (F: Functor C D) (G: Functor D E) : Functor C E := {
  obj := Function.comp G.obj F.obj
  map := fun f => G.map (F.map f)
  map_id := by
    intros
    simp
  map_comp := by
    intros
    simp
}

def Cat : HomStruct.{max (u + 1) (v + 1), max u v} := {
  obj := Category.{u,v},
  hom := fun C D => Functor C D
}

instance : IsCategory Cat where
  id' := fun {C} => fId C
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


def fully_faithful {C D: Category} (F: Functor C D) :=
  forall c d : C.obj, Function.isomorphism (F.map (c := c) (d := d))

section NatTrans

variable {C D: Category}

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


def vComp {F G H : Functor C D} (η : NatTrans F G) (μ : NatTrans G H) : NatTrans F H := {
  app := fun c => (app μ c) ∘ (app η c),
  naturality := by
    intro c d f
    simp
    rw [<- naturality μ f]
    rw [<- IsCategory.assoc]
    rw [naturality η f]
    rw [IsCategory.assoc]
}

def idTrans (F : Functor C D) : NatTrans F F := {
  app := fun c => id' (Functor.obj F c),
  naturality := by
    intro c d f
    simp
}

def FunctorCat (C D: Category): Category := {
  base := {
    obj := Functor C D
    hom := NatTrans
  }
  inst := {
    id'     := idTrans,
    comp    := vComp,
    id_comp := by
      intros
      apply NatTrans.ext
      simp [idTrans, vComp]
    comp_id := by
      intros
      apply NatTrans.ext
      simp [idTrans, vComp]
    assoc := by
      intros
      apply NatTrans.ext
      simp [vComp]
}
}

end NatTrans

section Yoneda

universe u v


variable {C : Category.{u,v}}


def yObj (c: C.obj) : (Functor Cᵒᵖ Set.{v}) where
  obj := fun d => C.hom d c
  -- f gets sent to precomposition with f
  map := fun f g => g ∘ f
  map_id := by
    intro d
    simp
    funext f
    -- While it seems like the lhs can be simplified, this is not true
    -- since `id'` is in `Cᵒᵖ` and not in `C`
    -- I need a better solution for this...
    -- We could try to state this lemma in general in order to apply it
    -- here and in similar cases
    have p: id' (C := C.base) d = id' (C := Cᵒᵖ.base) d  := by rfl
    rw [<- p]
    simp
    rfl

  map_comp := by
    intros x y z f g
    simp
    funext h
    have p: comp (C := C.base) g f = comp (C := Cᵒᵖ.base) f g  := by rfl
    rw [<- p]
    simp [comp, Set]


def yObjOp (c: C.obj) : (Functor C Set.{v}) where
  obj := fun d => C.hom c d
  -- f gets sent to postcomposition with f
  map := fun f g => f ∘ g
  map_id := by
    intro d
    simp
    funext f
    rfl
  map_comp := by
    intros x y z f g
    simp
    funext h
    simp [comp, Set]


def yMap {c d: C.obj} (f: C.hom c d) : NatTrans (yObj c) (yObj d) where
  app := fun e g => f ∘ g
  naturality := by
    intros
    simp [yObj, comp, Set]


def yMapOp {c d: C.obj} (f: C.hom d c) : NatTrans (yObjOp c) (yObjOp d) where
  app := fun e g => g ∘ f
  naturality := by
    intros
    simp [yObjOp, comp, Set]

def y : Functor C (FunctorCat Cᵒᵖ Set.{v}) := {
  obj := yObj
  map := yMap
  map_id := by
    intros c
    -- Apparently you can `simp` a hidden argument
    simp [id', FunctorCat]
    apply NatTrans.ext
    simp [yMap, idTrans, yObj, id', Set]
  map_comp := by
    intros
    apply NatTrans.ext
    simp [yMap, comp, vComp, FunctorCat, Set]
}

def yOp : Functor Cᵒᵖ (FunctorCat C Set.{v}) := by
  have x := y (C := Cᵒᵖ)
  rw [C.opop] at x
  exact x


def yonedaMap (c : C.obj) (F: Functor Cᵒᵖ Set.{v}) (η: NatTrans (y.obj c) F) : F.obj c := η.app c (id' c)

def yonedaMapOp (c : C.obj) (F: Functor C Set.{v}) (η: NatTrans ((y (C := Cᵒᵖ)).obj c) F) : F.obj c := η.app c (by
  simp [yOp]
  )

def yonedaMapInv (c : C.obj) (F: Functor Cᵒᵖ Set.{v}) (x: F.obj c) : NatTrans (y.obj c) F := {
  app := fun d f => F.map f x
  naturality := by
    intros d e f
    simp [y, yObj, comp, Set]
    funext g
    -- It honestly is a bit confusing not knowing in which category
    -- the composition takes place
    have p: comp (C := C.base) f g = comp (C := Cᵒᵖ.base) g f  := by rfl
    rw [p, Functor.map_comp]
    simp [comp]
}


theorem yoneda (c : C.obj) (F: Functor Cᵒᵖ Set.{v}) : Function.inverses (yonedaMap c F) (yonedaMapInv c F) := ⟨
  by
    simp [yonedaMap, yonedaMapInv]
    apply funext
    intro { app := η, naturality := nat }
    simp [comp, id', y, yObj, Set]
    funext d f
    -- Rewrite the application in the goal as a composition in order
    -- to apply naturality
    have p: F.map f (η c (id' c)) = (comp (η c) (F.map f)) (id' c) := by rfl
    rw [p, <- nat f]
    simp [y, yObj, comp, Set],
  by
    simp [yonedaMap, yonedaMapInv, Function.comp, Set]
    funext x
    have p: id' (C := C.base) c = id' (C := Cᵒᵖ.base) c  := by rfl
    rw [p, Functor.map_id]
    simp [id', Set]
⟩


theorem y_fully_faithful: fully_faithful (y (C := C)) := by
  simp [fully_faithful, Function.isomorphism]
  intros c d

  -- The crucial insight is that `y.map` is in fact equal to `yonedaMapInverse` and thus by the yoneda lemma has an inverse
  have yoneda := yoneda c (y.obj d)

  exact ⟨ yonedaMap c (y.obj d), by
    have p: yonedaMapInv c (Functor.obj y d) = y.map := by
      funext f
      apply NatTrans.ext
      simp [yonedaMapInv, y, yMap, yObj]

    rw [<- p, Function.inverses_sym]
    exact yoneda
  ⟩

end Yoneda

end CategoryTheory
