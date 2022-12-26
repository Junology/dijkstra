/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

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
Actually, we call a monad `m` a specification monad provided it is an ***ordered monad*** in the sense that the type `m α` is equipped with an order relation for each type `α` so that the operation `bind` is monotonic.
For example, the specification monad `WPPure` above is ordered so that, for `x y : WPPure α`, 

```lean
x ≤ y ≡ ∀ (p : α → Prop), y p → x p
```

In other words, `x ≤ y` means that `y` is a stronger condition than `x`.

-/

universe u v w


/-!

## Ordered Monad

-/

/-- A monad `m : Type u → Type v` is called an ordered monad provided, for each `α : Type u`, the type `m α : Type v` is equipped with an order relation so that `bind` is monotonic in each variable. -/
class OrderedMonad (m : Type u → Type v) [Monad m] where
  le : {α : Type u} → m α → m α → Prop
  bind_le {α β : Type u} {x₁ x₂ : m α} (ha : le x₁ x₂) {f₁ f₂ : α → m β} (hb : ∀ a, le (f₁ a) (f₂ a)) : le (x₁ >>= f₁) (x₂ >>= f₂)


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

instance instOrderedMonadPred : OrderedMonad Pred where
  le p q := ∀ a, p a → q a
  bind_le := by
    intro _ _ p q hpq f g hfg b hb
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

instance instOrderedMonadWPPure : OrderedMonad WPPure where
  le x y := ∀ p, y.predT p → x.predT p
  bind_le := by
    dsimp [bind]; intro _ _ x₁ x₂ ha f₁ f₂ hb
    intro p h₂
    apply ha
    exact x₂.monotonic (λ a => hb a p) h₂
