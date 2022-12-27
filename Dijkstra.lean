import Dijkstra.Init
import Dijkstra.Control.Lawful
import Dijkstra.Control.MonadHom
import Dijkstra.Control.MonadTransformer
import Dijkstra.Control.SpecMonad

universe u v v₁ v₂ v₃ w

class DijkstraMonad (WP : Type u → Type v) [Monad WP] (M : {α : Type u} → WP α → Type v) where
  dpure {α : Type u} (a : α) : M (return a)
  dbind {α β : Type u} {wa : WP α} (c : M wa) {wf : α → WP β} (f : (a : α) → M (wf a)) : M (wa >>= wf)

class LawfulDijkstraMonad (WP : Type u → Type v) [Monad WP] (M : {α : Type u} → WP α → Type v) [DijkstraMonad WP M] where
  dbind_dpure {α : Type u} {wa : WP α} {x : M wa} : DEq M (DijkstraMonad.dbind x DijkstraMonad.dpure) x
  dpure_dbind {α β : Type u} (a : α) {wb : WP β} (wf : α → M wb) : DEq M (DijkstraMonad.dbind (DijkstraMonad.dpure a) wf) (wf a)
  dbind_assoc {α β γ : Type u} {wa : WP α} {wb : WP β} {wc : WP γ} (x : M wa) (f : α → M wb) (g : β → M wc) : DEq M (DijkstraMonad.dbind (DijkstraMonad.dbind x f) g) (DijkstraMonad.dbind x (λ a => DijkstraMonad.dbind (f a) g))

