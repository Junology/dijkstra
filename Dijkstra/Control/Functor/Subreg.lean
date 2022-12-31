/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

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
def mapProp {f : Type u → Type v} [Functor f] {α : Type u} (p : α → Prop) : f α → Prop :=
  λ x => ∃ (z : f (Subtype p)), Subtype.val <$> z = x

class SubregFunctor (f : Type u → Type v) [Functor f] where
  ensureF {α : Type u} {p : α → Prop} (x : f α) : mapProp p x → f (Subtype p)
  val_ensureF {α : Type u} {p : α → Prop} (x : f α) {h : mapProp p x} : Subtype.val <$> ensureF x h = x


/-!
## `Id`
-/

namespace Id

theorem mapProp_iff_id {α : Type u} {p : α → Prop} : ∀ a, mapProp (f:=Id) p a ↔ p a := by
  intro a
  constructor
  case mp =>
    intro ha; cases ha with | intro w hw =>
    exact hw ▸ w.property
  case mpr =>
    intro ha
    exact ⟨Subtype.mk (p:=p) a ha, rfl⟩

theorem mapProp_eq_id {α : Type u} (p : α → Prop) : mapProp (f:=Id) p = p :=
  funext $ fun a => propext (mapProp_iff_id a)

instance instSubregFunctorId : SubregFunctor Id where
  ensureF a ha := Subtype.mk a $
    ha.elim (fun x hx => hx ▸ x.property)
  val_ensureF _ := rfl

end Id


/-!
## `Option`
-/

namespace Option

variable {α : Type u}

def noneOrTrue (p : α → Prop) : Option α → Prop
| none => True
| some a => p a

theorem mapProp_iff_noneOrTrue {p : α → Prop} {x : Option α} : mapProp p x ↔ noneOrTrue p x := by
  constructor
  case mp =>
    intro h; cases h with | intro w hw =>
    cases hw
    cases w with
    | none => dsimp [Functor.map, Option.map, noneOrTrue]
    | some a => dsimp [Functor.map, noneOrTrue]; exact a.property
  case mpr =>
    intro h
    cases x with
    | none => exists none (α:=Subtype p)
    | some a => exists some (α:=Subtype p) ⟨a,h⟩

def ensureF {p : α → Prop} : (x : Option α) → mapProp p x → Option (Subtype p)
| none, _ => none
| some a, h => some ⟨a,mapProp_iff_noneOrTrue.mp h⟩

instance instSubregFunctorOption : SubregFunctor Option where
  ensureF := ensureF
  val_ensureF x := by intros; cases x <;> rfl
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

theorem mapProp_iff_forAll {α : Type u} {p : α → Prop} {as : List α} : mapProp p as ↔ forAll p as where
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
  ensureF x h := zipProof x (mapProp_iff_forAll.mp h)
  val_ensureF x := val_zipProof x

end List


/-!
## `ExceptT`
-/

namespace ExceptT

variable {α β ε : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m] [SubregFunctor m]

def errorOrApply (f : α → β) : Except ε α → Except ε β
| Except.error e => Except.error e
| Except.ok a => Except.ok (f a)

theorem map_eq_map_error_or_apply (f : α → β) (x : ExceptT ε m α) : (Functor.map f x) = errorOrApply f <$> x := by
  rw [Functor.map, Applicative.toFunctor, Monad.toApplicative]
  unfold instMonadExceptT
  simp
  unfold ExceptT.map
  rw [map_eq_pure_bind]
  apply bind_congr
  intro e <;> cases e <;> rfl

def is_error_or_true (p : α → Prop) : Except ε α → Prop :=
  fun e => e.casesOn (motive:=fun _ => Prop) (fun _ => True) p

def toSubtype{p : α → Prop} : Except ε (Subtype p) → Subtype (is_error_or_true (ε:=ε) p)
| Except.error e =>
  Subtype.mk (Except.error e) $ by
    unfold is_error_or_true
    simp
| Except.ok a =>
  Subtype.mk (Except.ok a.val) $ by
    unfold is_error_or_true
    simp
    exact a.property

def fromSubtype {p : α → Prop} : Subtype (is_error_or_true (ε:=ε) p) → Except ε (Subtype p)
| Subtype.mk (Except.error e) _ => Except.error e
| Subtype.mk (Except.ok a) ha => Except.ok ⟨a,ha⟩

theorem is_error_or_true_apply (p : β → Prop) (f : α → β) : (is_error_or_true (ε:=ε) p ∘ errorOrApply f) = is_error_or_true (p ∘ f) := by
  apply funext
  intros e <;> cases e <;> rfl

theorem mapProp_iff_error_or_true {α : Type u} {p : α → Prop} : ∀ x, mapProp (f:=ExceptT ε m) p x ↔ mapProp (f:=m) (is_error_or_true p) x := by
  intro x
  constructor
  case mp =>
    intro hx
    cases hx with | intro w hw =>
    cases hw
    exists toSubtype <$> w
    rw [←comp_map]
    rw [map_eq_map_error_or_apply]
    apply map_congr
    intro e <;> cases e <;> rfl
  case mpr =>
    intro hx
    cases hx with | intro w hw =>
    cases hw
    unfold mapProp
    exists Functor.map (f:=m) fromSubtype w
    rw [map_eq_map_error_or_apply, ←comp_map]
    apply map_congr
    intro e <;> cases e with | mk e he =>
    cases e <;> rfl

def ensureF {α : Type u} {p : α → Prop} (x : ExceptT ε m α) (hx : mapProp p x) : ExceptT ε m (Subtype p) :=
  Functor.map (f:=m) fromSubtype $
    SubregFunctor.ensureF (f:=m) x $
      (mapProp_iff_error_or_true x).mp hx

instance instSubregFunctorExceptT : SubregFunctor (ExceptT ε m) where
  ensureF := ensureF
  val_ensureF {α} {p} x hx := by
    unfold ensureF
    rw [map_eq_map_error_or_apply]
    rw [←comp_map]
    have : errorOrApply (ε:=ε) (Subtype.val (p:=p)) ∘ fromSubtype = Subtype.val := by
      apply funext
      intro e <;> cases e with | mk e he =>
      cases e <;> rfl
    rw [this]
    rw [SubregFunctor.val_ensureF (f:=m) x]

end ExceptT


/-!
## `ReaderT`
-/

namespace ReaderT

variable {ρ : Type u} {m : Type u → Type v} [Monad m] [SubregFunctor m]

def ensureF {α : Type u} {p : α → Prop} (x : ReaderT ρ m α) (hx : mapProp p x) : ReaderT ρ m (Subtype p) :=
  fun r =>
    SubregFunctor.ensureF (f:=m) (x r) $ by
      cases hx with | intro x hx =>
      cases hx
      unfold mapProp
      exists x r

theorem map_eq_map_ap {α β : Type u} (f : α → β) (x : ReaderT ρ m α) : ∀ r, (f <$> x) r = f <$> (x r) := fun _ => rfl

instance instSubregFunctorReaderT : SubregFunctor (ReaderT ρ m) where
  ensureF := ensureF
  val_ensureF {α} {p} x hx := by
    apply funext
    intro r
    cases hx with | intro w hw =>
    cases hw
    unfold ensureF
    simp
    rw [map_eq_map_ap, SubregFunctor.val_ensureF]

end ReaderT


/-!
## `StateRefT`
-/

instance {ω σ : Type} {m : Type → Type} [Monad m] [SubregFunctor m] : SubregFunctor (StateRefT' ω σ m) :=
  inferInstanceAs (SubregFunctor (ReaderT (ST.Ref ω σ) m))


/-!
## `StateT`
-/

namespace StateT

variable {σ α β : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m] [SubregFunctor m]

theorem map_eq_map_comp (f : α → β) (x : StateT σ m α) : (f <$> x) = Functor.map (f:=m) (Prod.map f id) ∘ x := by
  apply funext; intro s
  rw [Functor.map, Applicative.toFunctor, Monad.toApplicative]
  unfold instMonadStateT
  simp
  unfold StateT.map
  rw [map_eq_pure_bind]
  apply bind_congr
  intro w; rfl

theorem mapProp_eq_forall_mapProp_fst {p : α → Prop} {x : StateT σ m α} : (mapProp p x) = ∀ s, mapProp (p ∘ Prod.fst) (x s) := by
  apply propext; constructor
  case a.mp =>
    intro hx s
    cases hx with | intro w hw =>
    cases hw
    exists (λ as => Subtype.mk ⟨as.1.val, as.2⟩ as.1.property) <$> w s
    rw [←comp_map, map_eq_map_comp]
    simp
    apply map_congr
    intro x; rfl
  case a.mpr =>
    intro h
    exists fun s => (λ x => ⟨⟨x.val.1, x.property⟩, x.val.2⟩) <$> SubregFunctor.ensureF (x s) (h s)
    apply funext; intro s
    rw [map_eq_map_comp]
    dsimp
    rw [←comp_map]
    conv =>
      lhs; lhs; ext as; dsimp [Prod.map]; change as.val
    conv => lhs; lhs; change Subtype.val
    rw [SubregFunctor.val_ensureF (x s)]

def ensureF {p : α → Prop} (x : StateT σ m α) (hx : mapProp p x) : StateT σ m (Subtype p) :=
  have : ∀ s, mapProp (p ∘ Prod.fst) (x s) := by
    rw [mapProp_eq_forall_mapProp_fst] at hx
    exact hx
  fun s => (λ x => ⟨⟨x.val.1, x.property⟩, x.val.2⟩) <$> SubregFunctor.ensureF (x s) (this s)

instance instSubregFunctorStateT : SubregFunctor (StateT σ m) where
  ensureF := ensureF
  val_ensureF x hx := by
    apply funext; intro s
    unfold ensureF
    rw [map_eq_map_comp]
    dsimp
    rw [←comp_map]
    exact SubregFunctor.val_ensureF _

end StateT


/-!
## `EStateM`
-/

namespace EStateM

variable {ε σ α β : Type u}

namespace Result

def map (f : α → β) : Result ε σ α → Result ε σ β
| ok a s => ok (f a) s
| error err s => error err s

def errorOrTrue (p : α → Prop) : Result ε σ α → Prop
| ok a _ => p a
| error _ _ => True

def fromSubtype {p : α → Prop} : Subtype (errorOrTrue (ε:=ε) (σ:=σ) p) → Result ε σ (Subtype p)
| Subtype.mk (ok a s) h => ok ⟨a,h⟩ s
| Subtype.mk (error e s) _ => error e s

theorem map_val_fromSubtype {p : α → Prop} (x : Subtype (errorOrTrue (ε:=ε) (σ:=σ) p)) : map Subtype.val (fromSubtype x) = x.val := by
  cases x with | mk a ha =>
  unfold fromSubtype; unfold map
  cases a <;> simp

end Result

theorem map_eq_map_comp {β : Type _} (f : α → β) (x : EStateM ε σ α) : (f <$> x) = Result.map f ∘ x := by
  apply funext; intro s
  rw [Functor.map, Applicative.toFunctor, Monad.toApplicative, instMonadEStateM]
  simp
  unfold EStateM.map
  cases x s <;> unfold Result.map <;> rfl

theorem mapProp_iff_forall_error_or_true {p : α → Prop} {x : EStateM ε σ α} : (mapProp p x) ↔ ∀ s, (x s).errorOrTrue p := by
  constructor
  case mp =>
    intro hx s
    cases hx with | intro w hw =>
    cases hw
    rw [Functor.map, Applicative.toFunctor, Monad.toApplicative, instMonadEStateM]
    simp
    unfold EStateM.map
    cases w s with
    | ok a s =>
      unfold Result.errorOrTrue; simp
      exact a.property
    | error e s => unfold Result.errorOrTrue; simp
  case mpr =>
    intro h
    exists fun s => Result.fromSubtype ⟨x s, h s⟩
    apply funext
    intro s
    rw [map_eq_map_comp]
    simp
    rw [Result.map_val_fromSubtype]

def ensureF {p : α → Prop} (x : EStateM ε σ α) (hx : mapProp p x) : EStateM ε σ (Subtype p) :=
  fun s =>
    Result.fromSubtype $ Subtype.mk (x s) $
      mapProp_iff_forall_error_or_true.mp hx s

instance instSubregFunctorEStateM : SubregFunctor (EStateM ε σ) where
  ensureF := ensureF
  val_ensureF x hx := by
    apply funext; intro s
    cases hx with | intro w hw =>
    cases hw
    rw [map_eq_map_comp]
    simp
    unfold ensureF
    rw [Result.map_val_fromSubtype]

end EStateM

