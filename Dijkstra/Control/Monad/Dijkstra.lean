/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Dijkstra.Init
import Dijkstra.Control.Lawful
import Dijkstra.Control.Monad.Hom
import Dijkstra.Control.Monad.Rel


/-!

# Dijkstra monads

A ***Dijkstra monad*** is a dependent analogue of a monad which is parametrized by a specific monad, called the *underlying monad*, so that the operations `pure` and `bind` are defined along with those on the underlying monad.
More precisely, given monad `W : Type u → Type v`, a type-family `M : (α : Type u) → W α → Type v` is a Dijkstra monad if it is equipped with the following two operations:

```lean
dpure {α : Type u} (a : α) :  M (pure a)
dbind {α β : Type u} {wa : W α} {wf : α → W β} : M α wa → ((a : α) → M β (wf a)) → M β (wa >>= wf)
```

In addition, these operations are supposed to satisfy dependent analogues of the ordinary monad relations.
There is, however, a problem to write down such conditions.
For example, one would expect that the left unitality of `dbind` can be written to be of the type `dbind (dpure a) f = f a`, thouth it is not type-correct.
Indeed, for `a : α`, `wb : W β`, and `f : α → M β wb`, we have

```lean
#check dbind (dpure a) f -- M β (pure a >>= λ _ => wb)
#check f a               -- M β wb
```

and it turns out that the dependent parameters are not definitionally equal (even if one has `[LawfulMonad W]`).
This is why we need `DEq` a dependent analogue of `Eq` for type families; see [Init.lean](Dijkstra/Init.lean).

-/

universe u v w

/-- The main structures of Dijkstra monads. -/
class DijkstraMonad (W : Type u → Type v) [Monad W] (M : (α : Type u) → W α → Type w) where
  dpure {α : Type u} (a : α) : M α (return a)
  dbind {α β : Type u} {wa : W α} {wf : α → W β} : M α wa → ((a : α) → M β (wf a)) → M β (wa >>= wf)

export DijkstraMonad (dpure dbind)

/-- The dependent monad laws for Dijkstra monads. -/
class DijkstraMonad.Lawful (W : Type u → Type v) [Monad W] (M : (α : Type u) → W α → Type w) [DijkstraMonad W M] where
  --- right unitality
  dbind_dpure {α : Type u} {wa : W α} {x : M α wa} : DEq (M α) (dbind x dpure) x
  --- left unitality
  dpure_dbind {α β : Type u} {wf : α → W β} (a : α) (f : (a : α) → M β (wf a)) : DEq (M β) (dbind (dpure a) f) (f a)
  --- associativity
  dbind_assoc {α β γ : Type u} {wa : W α} {wf : α → W β} {wg : β → W γ} (x : M α wa) (f : (a : α) → M β (wf a)) (g : (b : β) → M γ (wg b)) : DEq (M γ) (dbind (dbind x f) g) (dbind x (λ a => dbind (f a) g))

namespace DijkstraMonad


/-!

## Basic lemmas

-/

theorem dbind_congr {W : Type u → Type v} [Monad W] {M : (α : Type u) → W α → Type w} [DijkstraMonad W M] {α β : Type u} : ∀ {wa₁ wa₂ : W α} {wf₁ wf₂ : α → W β} {x₁ : M α wa₁} {x₂ : M α wa₂} {f₁ : (a : α) → M β (wf₁ a)} {f₂ : (a : α) → M β (wf₂ a)}, DEq (M α) x₁ x₂ → (∀ a, DEq (M β) (f₁ a) (f₂ a)) → DEq (M β) (dbind x₁ f₁) (dbind x₂ f₂)
| _, _, wf₁, wf₂, _, _, f₁, f₂, DEq.refl _, hf => by
  have : wf₁ = wf₂ := by
    funext a
    exact (hf a).eq_param
  cases this
  have : f₁ = f₂ := by
    funext a
    exact (hf a).eq_of_deq
  cases this
  exact DEq.refl _

theorem dbind_congrRight {W : Type u → Type v} [Monad W] {M : (α : Type u) → W α → Type w} [DijkstraMonad W M] {α β : Type u} : ∀ {wa : W α} {wf₁ wf₂ : α → W β} {x : M α wa} {f₁ : (a : α) → M β (wf₁ a)} {f₂ : (a : α) → M β (wf₂ a)}, (∀ a, DEq (M β) (f₁ a) (f₂ a)) → DEq (M β) (dbind x f₁) (dbind x f₂) :=
  dbind_congr (DEq.refl _) 

theorem dbind_congrLeft {W : Type u → Type v} [Monad W] {M : (α : Type u) → W α → Type w} [DijkstraMonad W M] {α β : Type u} : ∀ {wa₁ wa₂ : W α} {wf : α → W β} {x₁ : M α wa₁} {x₂ : M α wa₂} {f : (a : α) → M β (wf a)}, DEq (M α) x₁ x₂ → DEq (M β) (dbind x₁ f) (dbind x₂ f) :=
  λ h => dbind_congr h (λ _ => DEq.refl _)


/-!

## Change of underlying monads

As is the case for parametrized type families, one can translate Dijkstra monads into other along monad homomorphisms on underlying monads.
In particular, given a monad homomorphism `F : MonadHom W₁ W₂`, we define the "push-forward" `DijkstraMonad W₁ M → DijkstraMonad W₂ (Push F M)` and the "pull-back" `DijkstraMonad W₂ M → DijkstraMonad W₁ (Pull F M)`.

-/

section underlying

universe v₁ v₂

variable {W₁ : Type u → Type v₁} [Monad W₁] {W₂ : Type u → Type v₂} [Monad W₂]

/-- Pushforward of Dijkstra monads along a monad homomorphism. -/
structure Push (F : MonadHom W₁ W₂) (M : (α : Type u) → W₁ α → Type w) (α : Type u) (wa₂ : W₂ α) : Type (max v₁ w) where
  base : W₁ α
  body : M α base
  underly : F.app base = wa₂

namespace Push

variable {F : MonadHom W₁ W₂} {M : (α : Type u) → W₁ α → Type w}

protected
theorem eq {α : Type u} {wa₂ : W₂ α} : ∀ {x y : Push F M α wa₂}, x.base = y.base → DEq (M α) x.body y.body → x = y
| mk _ _ _, mk _ _ _, rfl, DEq.refl _ => rfl

protected
theorem deq {α : Type u} {wa₂ wa₂': W₂ α} : ∀ {x : Push F M α wa₂} {y : Push F M α wa₂'}, x.base = y.base → DEq (M α) x.body y.body → DEq (Push F M α) x y
| mk base _ hx, mk _ _ hy, rfl, DEq.refl _ => by
  cases (Eq.trans hy.symm hx)
  exact DEq.refl _

instance instDijkstraMonadPush [DijkstraMonad W₁ M] : DijkstraMonad W₂ (Push F M) where
  dpure a := {
    base := pure a
    body := dpure a
    underly := F.app_pure a
  }
  dbind x f := {
    base := x.base >>= (λ a => (f a).base)
    body := dbind x.body (λ a => (f a).body)
    underly := by
      rw [F.app_bind, x.underly]
      apply bind_congr
      intro a; dsimp
      exact (f a).underly
  }

instance instDijkstraMonadLawfulPush [LawfulMonad W₁] [DijkstraMonad W₁ M] [DijkstraMonad.Lawful W₁ M] : DijkstraMonad.Lawful W₂ (Push F M) where
  dbind_dpure := by
    intro α wa₂ x
    cases x with | mk x_base x_body hx =>
    apply Push.deq <;> dsimp [dbind, dpure]
    . rw [bind_pure]; 
    . exact DijkstraMonad.Lawful.dbind_dpure (M:=M)
  dpure_dbind := by
    intro α β wb₂ a f
    apply Push.deq <;> dsimp [dbind, dpure]
    . rw [pure_bind]
    . exact DijkstraMonad.Lawful.dpure_dbind (M:=M) _ _
  dbind_assoc := by
    intro α β γ wa₂ wf wg x f g
    apply Push.deq <;> dsimp [dbind, dpure]
    . rw [bind_assoc]
    . exact DijkstraMonad.Lawful.dbind_assoc (M:=M) _ _ _

end Push

/-- Pullback of Dijkstra monads along a monad homomorphisms. -/
def Pull (F : MonadHom W₁ W₂) (M : (α : Type u) → W₂ α → Type w) (α : Type u) (wa₁ : W₁ α) : Type w :=
  M α (F.app wa₁)

namespace Pull

variable {F : MonadHom W₁ W₂} {M : (α : Type u) → W₂ α → Type w}

instance instDijkstraMonadPull [DijkstraMonad W₂ M] : DijkstraMonad W₁ (Pull F M) where
  dpure {α} a := (F.app_pure a).symm.rec (motive:=λ wa _ => M α wa) (dpure a)
  dbind {_} {β} {wa} {wf} x f :=
    (F.app_bind wa wf).symm.rec (motive:=λ wb _=> M β wb) (dbind (M:=M) (wf:=λ a => F.app (wf a)) x f)

protected
theorem deq {α : Type u} : ∀ {w₁ w₁' : W₁ α} {x : Pull F M α w₁} {y : Pull F M α w₁'}, w₁ = w₁' → DEq (M α) x y → DEq (Pull F M α) x y
| _, _, _, _, rfl, DEq.refl _ => DEq.refl _

theorem dpure_deq [DijkstraMonad W₂ M] {α : Type u} (a : α) : DEq (β:=M α) (dpure (M:=Pull F M) a) (dpure (M:=M) a) :=
  DEq.subst_deq

theorem dbind_deq [DijkstraMonad W₂ M] {α β : Type u} {wa : W₁ α} {wf : α → W₁ β} (x : Pull F M α wa) (f : (a : α) → Pull F M β (wf a)) : DEq (β:=M β) (dbind (M:=Pull F M) x f) (dbind (M:=M) x f) :=
  DEq.subst_deq

instance instDijkstraMonadLawfulPull [LawfulMonad W₁] [DijkstraMonad W₂ M] [DijkstraMonad.Lawful W₂ M] : DijkstraMonad.Lawful W₁ (Pull F M) where
  dbind_dpure := by
    intro α wa₁ x
    apply Pull.deq (bind_pure _)
    apply DEq.trans (Pull.dbind_deq x dpure) _
    apply DEq.trans (dbind_congrRight (W:=W₂) (M:=M) Pull.dpure_deq) _
    exact Lawful.dbind_dpure (M:=M)
  dpure_dbind := by
    intro α β wf a f
    apply Pull.deq (pure_bind _ _)
    apply DEq.trans (Pull.dbind_deq (dpure a) f) _
    apply DEq.trans (dbind_congrLeft (W:=W₂) (M:=M) (Pull.dpure_deq a))
    exact Lawful.dpure_dbind (M:=M) a f
  dbind_assoc := by
    intro α β γ wa wf wg x f g
    apply Pull.deq (bind_assoc _ _ _)
    apply DEq.trans (Pull.dbind_deq _ _)
    apply DEq.trans (dbind_congrLeft (W:=W₂) (M:=M) (Pull.dbind_deq _ _))
    apply DEq.trans (Lawful.dbind_assoc (M:=M) _ _ _)
    apply DEq.trans _ (Pull.dbind_deq x (λ a => dbind (f a) g)).symm
    apply dbind_congrRight
    intro a
    exact (Pull.dbind_deq _ _).symm

end Pull

end underlying


/-!

## Dijkstra monads from monadic relations

Given a monadic relation `r : MonadRel m n` for monads `m : Type u → Type v` and `n : Type u → Type w`, the associated submonad of `m × n` can be seen as a Dijkstra monad.
Although its underlying monad is a priori the product `m × n`, we define it as a Dijkstra monad over the second monad `n`.
In fact, the latter is obtained from the former by applying `Push` along the second projection.
It however turns out that our direct definition has more straightforward description.

-/

def Graph {m : Type u → Type v} [Monad m] {W : Type u → Type w} [Monad W] (r : MonadRel m W) (α : Type u) (wa : W α) : Type v :=
  {x : m α // r.rel x wa}

namespace Graph

variable {m : Type u → Type v} [Monad m] {W : Type u → Type v} [Monad W] {r : MonadRel m W}

protected
theorem deq {α : Type u} {wa₁ wa₂ : W α} : ∀ (x₁ : Graph r α wa₁) (x₂ : Graph r α wa₂), wa₁ = wa₂ → x₁.val = x₂.val → DEq (Graph r α) x₁ x₂
| Subtype.mk _ _, Subtype.mk _ _, rfl, rfl => DEq.refl _

instance instDijkstraMonadGraph : DijkstraMonad W (Graph r) where
  dpure a := Subtype.mk (pure a) (r.rel_pure a)
  dbind x f := Subtype.mk (x.val >>= (λ a => (f a).val)) $ r.rel_bind x.property (λ a => (f a).property)

end Graph

end DijkstraMonad
