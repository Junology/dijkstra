/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Classes.LawfulMonad

/-!

# Subregular functors

We say a functor `f : Type u → Type v` is ***subregular*** if it preserves monomorphisms.
Under the existence of a subobject classifier (i.e. `Prop`), this is equivalent to the following: for each type `α : Type u` and each predicate `p : α → Prop`, the image `f (Subtype p)` is a subtype of `f α` with `Functor.map Subtype.val : f (Subtype p) → f α` as the inclusion.
In other words, `f` is subregular if the canonical map

```lean
def f_incl : f (Subtype p) → {x : f α // ∃ (z : f (Subtype p)), f <$> z = x} :=
  λ z => Subtype.mk (f <$> z) ⟨z, rfl⟩
```

is invertible.

-/

universe u v w

--- The predicate transformer classifying the image of `f (Subtype p) → f α` for each predicate `p : α → Type u`.
-- def SatisfiesM {f : Type u → Type v} [Functor f] {α : Type u} (p : α → Prop) : f α → Prop :=
 --  λ x => ∃ (z : f (Subtype p)), Subtype.val <$> z = x

class SubregFunctor (f : Type u → Type v) [Functor f] where
  ensureF {α : Type u} {p : α → Prop} (x : f α) : SatisfiesM p x → f (Subtype p)
  val_ensureF {α : Type u} {p : α → Prop} (x : f α) {h : SatisfiesM p x} : Subtype.val <$> ensureF x h = x
  val_inj {α : Type u} {p : α → Prop} {x y : f (Subtype p)} : Subtype.val <$> x = Subtype.val <$> y → x = y


/-!
## `Id`
-/

namespace Id

instance instSubregFunctorId : SubregFunctor Id where
  ensureF a ha := Subtype.mk a $
    ha.elim (fun x hx => hx ▸ x.property)
  val_ensureF _ := rfl
  val_inj h := Subtype.eq h

end Id


/-!
## `Option`
-/

namespace Option

instance instSubregFunctorOption : SubregFunctor Option where
  ensureF x h := match x with
    | none => none
    | some a => some ⟨a, SatisfiesM_Option_eq.mp h a rfl⟩
  val_ensureF x := by intros; cases x <;> rfl
  val_inj {α} {p} {x} {y} h := match x, y with
    | none, none => rfl
    | some a, some b => Subtype.eq (Option.some.inj h) ▸ rfl

end Option


/-!
## List
-/

namespace List

def forAll {α : Type u} (p : α → Prop) : List α → Prop
| [] => True
| (a::as) => p a ∧ forAll p as

def zipProof {α : Type u} {p : α → Prop} : (as : List α) → as.forAll p → List (Subtype p)
| [], _ => []
| (a::as), And.intro ha has => ⟨a,ha⟩ :: zipProof as has

theorem val_zipProof {α : Type u} {p : α → Prop} (as : List α) {h : as.forAll p} : Subtype.val <$> zipProof as h = as := by
  induction as
  case nil => rfl
  case cons a as h_ind =>
    cases h with | intro ha has =>
    dsimp [Functor.map, zipProof, List.map] at *
    rw [h_ind]

theorem SatisfiesM_List_eq {α : Type u} {p : α → Prop} {as : List α} : SatisfiesM p as ↔ forAll p as where
  mp h := by
    cases h with | intro xs hx =>
    cases hx
    induction xs
    case nil => exact True.intro
    case cons a as h_ind =>
      exact ⟨a.property, h_ind⟩
  mpr h := by
    exists zipProof as h
    exact val_zipProof as

instance instSubregFunctorList : SubregFunctor List where
  ensureF x h := zipProof x (SatisfiesM_List_eq.mp h)
  val_ensureF x := val_zipProof x
  val_inj {_} {p} {as} {bs} h :=
    let rec aux : (as bs : List (Subtype p)) → Subtype.val <$> as = Subtype.val <$> bs → as = bs
    | [], [], _ => rfl
    | (a::as), (b::bs), h => by
      have := List.cons.inj h
      rw [Subtype.eq this.left, aux as bs this.right]
    aux as bs h

end List


/-!
## `ExceptT`
-/

namespace ExceptT

variable {α β ε : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m] [SubregFunctor m]

def errorOrApply (f : α → β) : Except ε α → Except ε β
| Except.error e => Except.error e
| Except.ok a => Except.ok (f a)

theorem map_eq_map_errorOrApply (f : α → β) (x : ExceptT ε m α) : (Functor.map f x) = errorOrApply f <$> x := by
  rw [Functor.map, Applicative.toFunctor, Monad.toApplicative]
  unfold instMonadExceptT
  simp
  unfold ExceptT.map
  rw [map_eq_pure_bind]
  apply bind_congr
  intro e; cases e <;> rfl

@[reducible]
def ok_implies_true (p : α → Prop) : Except ε α → Prop :=
  λ x => ∀ a, x = Except.ok a → p a

def toSubtype{p : α → Prop} : Except ε (Subtype p) → Subtype (ok_implies_true (ε:=ε) p)
| Except.error e => ⟨Except.error e, by intro _ h; cases h⟩
| Except.ok a => ⟨Except.ok a, λ _ h => Except.ok.inj h ▸ a.property⟩

def fromSubtype {p : α → Prop} : Subtype (ok_implies_true (ε:=ε) p) → Except ε (Subtype p)
| Subtype.mk (Except.error e) _ => Except.error e
| Subtype.mk (Except.ok a) ha => Except.ok ⟨a,ha a rfl⟩

theorem errorOrApply_val {p : α → Prop} : errorOrApply (ε:=ε) (Subtype.val (p:=p)) = Subtype.val ∘ toSubtype (p:=p) := by
  funext x
  cases x <;> rfl

theorem from_toSubtype {p : α → Prop} : fromSubtype (ε:=ε) (p:=p) ∘ toSubtype = id := by
  funext x
  cases x <;> rfl

instance instSubregFunctorExceptT : SubregFunctor (ExceptT ε m) where
  ensureF {α} {p} x hx :=
    Functor.map (f:=m) fromSubtype $
      SubregFunctor.ensureF (f:=m) x (SatisfiesM_ExceptT_eq.mp hx)
  val_ensureF {α} {p} x hx := by
    rw [map_eq_map_errorOrApply]
    rw [←comp_map]
    have : errorOrApply (ε:=ε) (Subtype.val (p:=p)) ∘ fromSubtype = Subtype.val := by
      apply funext
      intro e; cases e with | mk e he =>
      cases e <;> rfl
    rw [this]
    rw [SubregFunctor.val_ensureF (f:=m) x]
  val_inj {_} {p} {x} {y} h := by
    conv at h =>
      rw [map_eq_map_errorOrApply, map_eq_map_errorOrApply]
      rw [errorOrApply_val, comp_map, comp_map]
    have h' := SubregFunctor.val_inj h
    conv =>
      rw [←id_map (f:=m) x, ←id_map (f:=m) y]
      rw [←from_toSubtype (ε:=ε) (p:=p)]
      rw [comp_map, comp_map]
      rw [h']

end ExceptT


/-!
## `ReaderT`
-/

/-- `Classical`-free variant of `SatisfiesM_ReaderT_eq`; This version requires `SubregFunctor m` instead. -/
theorem SatisfiesM_ReaderT_eq' {m : Type u → Type v} [Monad m] [SubregFunctor m] {ρ α : Type u} {p : α → Prop} {x : ReaderT ρ m α} : SatisfiesM (m:=ReaderT ρ m) p x ↔ ∀ s, SatisfiesM p (x s) where
  mp h s := by
    cases h with | intro x h =>
    cases h
    exists x s
  mpr h := by
    exists λ s => SubregFunctor.ensureF (f:=m) (x s) (h s)
    funext s; dsimp [Functor.map]
    rw [SubregFunctor.val_ensureF]

instance instSubregFunctorReaderT (ρ : Type u) (m : Type u → Type v) [Monad m] [SubregFunctor m] : SubregFunctor (ReaderT ρ m) where
  ensureF x h s := SubregFunctor.ensureF (x s) $ SatisfiesM_ReaderT_eq'.mp h s
  val_ensureF {α} {p} x hx := by
    funext _
    cases hx with | intro w hw =>
    cases hw
    dsimp [Functor.map]
    rw [SubregFunctor.val_ensureF]
  val_inj {_} {p} {x} {y} h:= by
    conv at h => dsimp [Functor.map]
    funext s
    apply SubregFunctor.val_inj (f:=m)
    conv =>
      lhs; change (λ r => (Subtype.val <$> x r)) s; rw [h]


/-!
## `StateRefT`
-/

theorem SatisfiesM_StateRefT_eq' {m : Type → Type} [Monad m] [SubregFunctor m] {ω σ α : Type} {p : α → Prop} {x : StateRefT' ω σ m α} : SatisfiesM p x ↔ ∀ (s : ST.Ref ω σ), SatisfiesM p (x s) :=
  SatisfiesM_ReaderT_eq'

instance {ω σ : Type} {m : Type → Type} [Monad m] [SubregFunctor m] : SubregFunctor (StateRefT' ω σ m) :=
  inferInstanceAs (SubregFunctor (ReaderT (ST.Ref ω σ) m))


/-!
## `StateT`
-/

def Prod.fstToSubtype {α σ : Type u} {p : α → Prop} : (Subtype p) × σ → Subtype (α:=α×σ) (p ∘ Prod.fst) :=
  λ x => ⟨⟨x.1.val, x.2⟩, x.1.property⟩

def Prod.fstFromSubtype {α σ : Type u} {p : α → Prop} : Subtype (α:=α×σ) (p ∘ Prod.fst) → Subtype p × σ :=
  λ x => ⟨⟨x.val.1, x.property⟩, x.val.2⟩

theorem Prod.fst_from_to_subtype {α σ : Type u} {p : α → Prop} : Prod.fstFromSubtype (σ:=σ) (p:=p) ∘ Prod.fstToSubtype = id := by
  funext x
  cases x; rfl

theorem Prod.map_val_id {α σ : Type u} {p : α → Prop} : Prod.map (Subtype.val (p:=p)) (id (α:=σ)) = Subtype.val ∘ Prod.fstToSubtype := by
  funext x
  cases x; rfl

theorem SatisfiesM_StateT_eq' {m : Type u → Type v} [Monad m] [LawfulMonad m] [SubregFunctor m] {α ρ : Type u} {p : α → Prop} {x : StateT ρ m α} : SatisfiesM p x ↔ ∀ (s : ρ), SatisfiesM (fun x => p x.fst) (x s) where
  mp h s := by
    cases h with | intro w hw =>
    cases hw
    exists Prod.fstToSubtype (p:=p) <$> w s
    dsimp [Functor.map, StateT.map]
    rw [←comp_map, ←map_eq_pure_bind]
    apply map_congr
    intro x; rfl
  mpr h := by
    exists fun s => Prod.fstFromSubtype <$> SubregFunctor.ensureF (x s) (h s)
    apply funext; intro s
    dsimp [Functor.map, StateT.map]
    rw [←map_eq_pure_bind, ←comp_map]
    conv =>
      lhs; lhs; ext as; dsimp [Prod.map]; change as.val
    conv => lhs; lhs; change Subtype.val
    rw [SubregFunctor.val_ensureF (x s)]

instance instSubregFunctorStateT {m : Type u → Type v} [Monad m] [LawfulMonad m] [SubregFunctor m] {σ : Type u} : SubregFunctor (StateT σ m) where
  ensureF x hx s := Prod.fstFromSubtype <$> SubregFunctor.ensureF (x s) (SatisfiesM_StateT_eq'.mp hx s)
  val_ensureF x hx := by
    funext s
    dsimp [Functor.map, StateT.map]
    rw [←map_eq_pure_bind, ←comp_map]
    exact SubregFunctor.val_ensureF _
  val_inj {_} {p} {x y} h := by
    funext s
    rw [←id_map (f:=m) (x s), ←id_map (f:=m) (y s)]
    rw [←Prod.fst_from_to_subtype]
    rw [comp_map, comp_map]
    have h' := congrFun h
    conv at h' =>
      ext s
      dsimp [Functor.map, StateT.map]
      rw [←map_eq_pure_bind, ←map_eq_pure_bind]
      change (Subtype.val ∘ Prod.fstToSubtype) <$> x s = (Subtype.val ∘ Prod.fstToSubtype) <$> y s
      rw [comp_map, comp_map]
    rw [SubregFunctor.val_inj (h' s)]


/-!
## `EStateM`
-/

namespace EStateM

variable {ε σ : Type u}

namespace Result

def map {α β : Type u} (f : α → β) : Result ε σ α → Result ε σ β
| ok a s => ok (f a) s
| error err s => error err s

@[reducible, inline]
def okThenTrue {α : Type u} (p : α → Prop) : Result ε σ α → Prop :=
  λ x => ∀ a s, x = Result.ok a s → p a

def zipProof {α : Type u} {p : α → Prop} : (x : Result ε σ α) → okThenTrue (ε:=ε) (σ:=σ) p x → Result ε σ (Subtype p)
| ok a s, h => ok ⟨a,h _ _ rfl⟩ s
| error e s, _ => error e s

theorem map_val_zipProof {α : Type u} {p : α → Prop} : ∀ (x : Result ε σ α) {h : okThenTrue (ε:=ε) (σ:=σ) p x}, map Subtype.val (zipProof x h) = x
| ok _ _, _ => rfl
| error _ _, _ => rfl

end Result

theorem SatisfiesM_EStateM_eq {α : Type u} {p : α → Prop} {x : EStateM ε σ α} : (SatisfiesM p x) ↔ (∀ s a s', (x s) = Result.ok a s' → p a) where
  mp hx s a _ := by
    cases hx with | intro w hw =>
    cases hw
    dsimp [Functor.map, EStateM.map]
    cases w s <;> intro h
    case ok a s' => exact (Result.ok.inj h).left ▸ a.property
    case error e s' => cases h
  mpr h := by
    exists λ s => (x s).zipProof (h s)
    funext s
    dsimp [Functor.map, EStateM.map]
    conv =>
      lhs; change Result.map (Subtype.val (p:=p)) ((x s).zipProof (h s))
      rw [Result.map_val_zipProof]

instance instSubregFunctorEStateM : SubregFunctor (EStateM ε σ) where
  ensureF x hx s := (x s).zipProof (SatisfiesM_EStateM_eq.mp hx s)
  val_ensureF {_} {p} x hx := by
    funext s
    conv =>
      lhs; change Result.map Subtype.val ((x s).zipProof (SatisfiesM_EStateM_eq.mp hx s))
      rw [Result.map_val_zipProof]
  val_inj {_} {p} {x y} h := by
    funext s
    have hs := congrFun h s
    conv at hs =>
      dsimp [Functor.map, EStateM.map]
    cases hx : x s
      <;> cases hy : y s
      <;> conv at hs => rw [hx, hy]; dsimp [Result.map]
    case h.ok.ok a sa b sb =>
      have := Result.ok.inj hs
      rw [Subtype.eq this.left, this.right]
    case h.error.error ea sa eb sb =>
      have := Result.error.inj hs
      rw [this.left, this.right]
    all_goals {cases hs}

end EStateM

