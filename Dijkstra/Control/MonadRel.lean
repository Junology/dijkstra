/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Dijkstra.Control.SpecMonad

/-!

# Binary relation on monads

Since the category of monads has finite products, we can define the notion of ***relations*** between two monads.
Namely, given monads `m : Type u → Type v` and `n : Type u → Type w`, we define a relation `r` between `m` and `n` to be a submonad of the monad

```lean
def MonadPair (m : Type u → Type v) [Monad m] (n : Type u → Type v) [Monad n] : Type u → Type (max u v) := λ α ↦ m α × n α
```

Thus, as an endo-functor, `r` is identified with a characteristic map `r : {α : Type u} → m α → n α → Prop`.
In order for the resulting subfunctor to inherit the structure of a monad, it has to satisfy the following closedness properties:

```lean
MonadRel.pure {α : Type u} : ∀ (a : α), r (pure a) (pure a)
MonadRel.bind {α β : Type u} {x : m α} {y : n α} {f : α → m β} {g : α → n β} : r x y → (∀ a, r (f a) (g a)) → r (x >>= f) (y >>= g)
```

-/

universe u v v₁ v₂ v₃ w

structure MonadRel (m : Type u → Type v) [Monad m] (n : Type u → Type w) [Monad n] where
  rel {α : Type u} : m α → n α → Prop
  pure {α : Type u} (a : α) : rel (pure a) (pure a)
  bind {α β : Type u} {x : m α} {y : n α} {f : α → m β} {g : α → n β} : rel x y → (∀ a, rel (f a) (g a)) → rel (x >>= f) (y >>=g)


namespace MonadRel

protected
def Eq {m : Type u → Type v} [Monad m] : MonadRel m m where
  rel := Eq
  pure _ := rfl
  bind h hfg := h ▸ bind_congr hfg

/-- @warning: the composition of monad relations requires `Classical.Choice`. -/
def comp {m₁ : Type u → Type v₁} [Monad m₁] {m₂ : Type u → Type v₂} [Monad m₂] {m₃ : Type u → Type v₃} [Monad m₃] (r₁ : MonadRel m₁ m₂) (r₂ : MonadRel m₂ m₃) : MonadRel m₁ m₃ where
  rel x z := ∃ y, r₁.rel x y ∧ r₂.rel y z
  pure a := Exists.intro (Pure.pure a) ⟨r₁.pure a, r₂.pure a⟩
  bind := by
    dsimp; intro α β x z f h hxz hfh
    cases hxz with | intro y hy =>
    cases Classical.axiomOfChoice hfh with | intro g hg =>
    exists y >>= g
    exact ⟨r₁.bind hy.left (λ a => (hg a).left), r₂.bind hy.right (λ a => (hg a).right)⟩

end MonadRel
