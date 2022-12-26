import Dijkstra.Control.Lawful
import Dijkstra.Control.MonadHom
import Dijkstra.Control.MonadTransformer
import Dijkstra.Control.SpecMonad

universe u v v₁ v₂ v₃ w


class DijkstraMonad {w : Type u → Type v} [Monad w] (mw : {α : Type u} → w α → Type v) where
  pure {α : Type u} (a : α) : mw (return a)
  bind {α β : Type u} {a : α} {wa : w α} (c : mw wa) {wf : α → w β} (f : (a : α) → mw (wf a)) : mw (wa >>= wf)

def WriterT (m : Type (max u w) → Type v) (σ : Type w) (α : Type u) : Type v :=
  m (σ × α)

