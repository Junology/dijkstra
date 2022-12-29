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

## Ordered Monad

-/

/-- `SpecMonad` is a monad which is equipped with a monadic relation. -/
class SpecMonad (m : Type u → Type v) [Monad m] extends MonadRel m m

/-!

## Examples of specification monads

-/

/-!
### Predicate monad
-/

def Pred (α : Type u) : Type u := α → Prop

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

instance instSpecMonad : SpecMonad Pred where
  rel p q := ∀ a, p a → q a
  rel_pure a := by dsimp [Pure.pure]; intro _; exact id
  rel_bind := by
    intro _ _ p q f g hpq hfg b hb
    dsimp [bind] at *
    cases hb with | intro a ha =>
    exists a
    exact ⟨hpq a ha.left, hfg a b ha.right⟩

/-!
### Weakest predicate for pure computations
-/

structure WPPure (α : Type u) where
  predT : (α → Prop) → Prop
  monotonic {p q : α → Prop} (h : ∀ a, p a → q a) : predT p → predT q

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

instance instSpecMonadWPPure : SpecMonad WPPure where
  rel x y := ∀ p, y.predT p → x.predT p
  rel_pure a := by dsimp; intro _; exact id
  rel_bind := by
    dsimp [bind]; intro _ _ x y f g hxy hfg hb p
    apply hxy
    exact y.monotonic (λ a => hfg a hb) p
