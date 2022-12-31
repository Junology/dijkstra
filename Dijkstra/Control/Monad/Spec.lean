/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Dijkstra.Control.Monad.Rel

/-!

# Specification Monads

(based on [Dijkstra Mondads for All](https://arxiv.org/abs/1903.01237) by K. Maillard, D. Ahman, R. Atkey, G. Martinez, C. Hritcu, E. Rivas, É. Tanter)

A ***specification*** monad is a monad that is used to represent pre/post-conditions of computation.
It is usually associated to a specific monad that provides actual computation semantics.

The idea is based on the notion of ***predicate transformer*** introduced by Dijkstra in the paper *"Guarded commands, nondeterminacy and formal derivation of programs"*.
For example, a specification monad `WPPure` for the monad `Id`, which is the "pure computation", is as follows:

```lean
WPPure α ≡ {wp : (α → Prop) → Prop // ∀ (p q : α → Prop), (∀ a, p a → q a) → wp p → wp q}
```

Indeed, it (coherently) transforms a post-condition `p : α → Prop` into the *weakest precondition* `wp p : Prop` which ensures `p` after computation.

In spite of the origin of the notion, not all specification monads are of this form.
Actually, we call a monad `m` a specification monad provided it is equipped with a ***monadic relation***; e.g. a relation on each `m α` which is respected by `pure` and `bind`.
For example, the specification monad `WPPure` above has a canonical order so that, for `x y : WPPure α`, 

```lean
x ≤ y ≡ ∀ (p : α → Prop), y p → x p
```

In other words, `x ≤ y` means that `y` requires a stronger pre-condition than `x` does.
For more details on monadic relations, see [Rel.lean](Dijkstra/Control/Monad/Rel.lean).

-/

universe u v w


/-!

## Definition of specification monads

-/

/-- `SpecMonad` is a monad which is equipped with a transitive monadic relation. -/
class SpecMonad (m : Type u → Type v) [Monad m] where
  rel : MonadRel m m
  trans {α : Type u} {x y z : m α} : rel.rel x y → rel.rel y z → rel.rel x z

def mrel {m : Type u → Type v} [Monad m] [self : SpecMonad m] {α : Type u} : m α → m α → Prop :=
  self.rel.rel

theorem mrel_pure {m : Type u → Type v} [Monad m] [self : SpecMonad m] {α : Type u} (a : α) : mrel (m:=m) (pure a) (pure a) :=
  self.rel.pure a

theorem mrel_bind {m : Type u → Type v} [Monad m] [self : SpecMonad m] {α β : Type u} {x y : m α} {f g : α → m β} : mrel x y → (∀ a, mrel (f a) (g a)) → mrel (x >>= f) (y >>= g) :=
  self.rel.bind

theorem mrel_trans {m : Type u → Type v} [Monad m] [self : SpecMonad m] {α : Type u} {x y z : m α} : mrel x y → mrel y z → mrel x z :=
  self.trans

instance {m : Type u → Type v} [Monad m] [SpecMonad m] {α : Type u} (x y z : m α) : Trans (mrel (m:=m) (α:=α)) (mrel (m:=m)) (mrel (m:=m)) where
  trans := mrel_trans


/-!

## Examples of specification monads

-/

/-!
### Predicate monad

For `α : Type u`, `Pred α = α → Prop` is the type of predicates on the terms of `α`.
As it is identified with the set of subtypes of `α`, `Pred` can also be seen as the (covariant) power-set operator and hence admits a canonical structure of a monad.
The `pure : α → Pred α` forms a singleton subtype, and the `bind : Pred α → (α → Pred β) → Pred β` takes the union of an `α`-indexed subtype-family over a subset.
In terms of predicates, `(p >>= q) b` holds precisely if there is a term `a : α` such that both `p a` and `q a b` are satisfied.

-/

def Pred (α : Type u) : Type u := α → Prop

/-- Equality of `Pred α` from `funext` and `propext`. -/
protected
def Pred.ext {α : Type u} {p q : Pred α} : (∀ a, p a ↔ q a) → p = q :=
  λ hpq => funext (λ a => propext (hpq a))

instance instMonadPred : Monad Pred where
  pure a := Eq a
  bind p f := λ b => ∃ a, p a ∧ f a b

instance instLawfulMonadPred : LawfulMonad Pred where
  map_const := rfl
  id_map p := by
    funext a; dsimp [Functor.map]
    apply propext
    constructor
    case mp =>
      intro h; cases h with | intro a ha => exact ha.2 ▸ ha.1
    case mpr =>
      intro h; exists a
  seqLeft_eq p q := by
    dsimp [Seq.seq, SeqLeft.seqLeft, Functor.map]
    funext a; apply propext
    constructor
    case mp =>
      intro h; cases h with | intro a₁ ha₁ =>
      exists (λ _ => a₁)
      exact ⟨Exists.intro a₁ ⟨ha₁.left, rfl⟩, ha₁.right⟩
    case mpr =>
      intro h; cases h with | intro f hf =>
      cases hf.left with | intro a₁ ha₁ =>
      rw [←ha₁.right] at hf
      exact Exists.intro a₁ $ ⟨ha₁.left, hf.right⟩
  seqRight_eq p q := by
    dsimp [SeqRight.seqRight, Seq.seq, Functor.map]
    funext b; apply propext
    constructor
    case mp =>
      intro h; cases h with | intro a ha =>
      exists id
      exact And.intro ⟨a, ⟨ha.left, rfl⟩⟩ ⟨b, ⟨ha.right, rfl⟩⟩
    case mpr =>
      intro h; cases h with | intro f hf =>
      cases hf.left with | intro a ha =>
      cases hf.right with | intro b₁ hb₁ =>
      cases hb₁.right
      rw [←ha.right] at *
      exact ⟨a, ⟨ha.left, hb₁.left⟩⟩
  pure_seq f p := by
    dsimp [Seq.seq, Pure.pure, Functor.map]
    funext b; apply propext
    constructor
    case mp =>
      intro h; cases h with | intro f₁ hf₁ =>
      cases hf₁.left.symm
      exact hf₁.right
    case mpr =>
      intro h; exact ⟨f, ⟨rfl, h⟩⟩
  bind_pure_comp f p := rfl
  bind_map p q := rfl
  pure_bind a f := by
    dsimp [pure, bind]
    funext b; apply propext
    constructor
    case mp =>
      intro h; cases h with | intro a ha =>
      rw [ha.left]; exact ha.right
    case mpr =>
      intro hf
      exact ⟨a, ⟨rfl, hf⟩⟩
  bind_assoc p f g := by
    dsimp [bind]
    funext b; apply propext
    constructor
    case mp =>
      intro h; cases h with | intro b₁ hb₁ =>
      cases hb₁.left with | intro a ha =>
      exists a; apply And.intro ha.left ⟨b₁, ⟨ha.right, hb₁.right⟩⟩
    case mpr =>
      intro h; cases h with | intro a ha =>
      cases ha.right with | intro b₁ hb₁ =>
      exists b₁
      exact And.intro ⟨a, ⟨ha.left, hb₁.left⟩⟩ hb₁.right

/-- The power-set `Pred α` is ordered by inclusion. In terms of predicates, the order agrees with the "implication". -/
protected
def Pred.rel : MonadRel Pred Pred where
  rel p q := ∀ a, p a → q a
  pure a := by dsimp [Pure.pure]; intro _; exact id
  bind := by
    intro _ _ p q f g hpq hfg b hb
    dsimp [bind] at *
    cases hb with | intro a ha =>
    exists a
    exact ⟨hpq a ha.left, hfg a b ha.right⟩

instance instSpecMonad : SpecMonad Pred where
  rel := Pred.rel
  trans hpq hqr := λ a hp => hqr a (hpq a hp)


/-!
### Weakest predicate for pure computations
-/

structure WPPure (α : Type u) where
  predT : (α → Prop) → Prop
  monotonic {p q : α → Prop} (h : ∀ a, p a → q a) : predT p → predT q

instance coeWPPurePredT (α :Type u) : CoeFun (WPPure α) (λ _ => (α → Prop) → Prop) where
  coe wp := wp.predT

/-- A utility lemma to prove equality on `WPPure α`. -/
protected
theorem WPPure.eq {α : Type u} : ∀ {wp wq : WPPure α}, wp.predT = wq.predT → wp = wq
| mk _ _, mk _ _, rfl => rfl

/-- Equality on `WPPure α` from `funext` and `propext`. -/
protected
theorem WPPure.ext {α : Type u} {wp wq : WPPure α} : (∀ (p : α → Prop), wp.predT p ↔ wq.predT p) → wp = wq :=
  λ hpq => WPPure.eq $ funext λ p => propext (hpq p)

instance instMonadWPPure : Monad WPPure where
  pure a := {
    predT := λ p => p a
    monotonic := by
      intro p q hpq hpa
      exact hpq a hpa
  }
  bind x f := {
    predT := λ p => x.predT (λ a => (f a).predT p)
    monotonic := by
      intro p q hpq hxp
      exact x.monotonic (λ a => (f a).monotonic hpq) hxp
  }

instance instLawfulMonadWPPure : LawfulMonad WPPure where
  map_const := rfl
  id_map _ := rfl
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  pure_seq _ _ := rfl
  bind_pure_comp _ _ := rfl
  bind_map _ _ := rfl
  pure_bind _ _ := rfl
  bind_assoc _ _ _ := rfl

protected
def WPPure.rel : MonadRel WPPure WPPure where
  rel x y := ∀ p, y.predT p → x.predT p
  pure a := by dsimp; intro _; exact id
  bind := by
    dsimp [bind]; intro _ _ x y f g hxy hfg hb p
    apply hxy
    exact y.monotonic (λ a => hfg a hb) p

instance instSpecMonadWPPure : SpecMonad WPPure where
  rel := WPPure.rel
  trans hxy hyz := λ p hz => hxy p (hyz p hz)


/-!

## Relations between specification monads

For monadic relations between specification monads, we assume compatibility with the intrinsic relations in addition to compatibility with monadic structures.

-/

structure SpecMonadRel (m : Type u → Type v) [Monad m] [SpecMonad m] (n : Type u → Type w) [Monad n] [SpecMonad n] extends MonadRel m n where
  trans_left {α : Type u} {mx my : m α} {nz : n α} : mrel mx my → rel my nz → rel mx nz
  trans_right {α : Type u} {mx : m α} {ny nz : n α} : rel mx ny → mrel ny nz → rel mx nz

def WPPure.ensure : SpecMonadRel WPPure Pred where
  rel wp p := wp.predT p
  pure a := rfl
  bind {α} {β} wa pa wf pf hwp hf := by
    dsimp [bind] at *
    apply wa.monotonic (p:=pa) _ hwp
    intro a ha
    apply (wf a).monotonic _ (hf a)
    intro b hb
    exact ⟨a, ⟨ha, hb⟩⟩
  trans_left := by
    dsimp [mrel, SpecMonad.rel, WPPure.rel]
    intro α wx wy p hxy hp
    exact hxy p hp
  trans_right := by
    dsimp [mrel, SpecMonad.rel, Pred.rel]
    intro α wx p q hp hpq
    exact wx.monotonic hpq hp
