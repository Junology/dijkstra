import Lake
open Lake DSL

package «dijkstra» {
  -- add package configuration options here
}

@[default_target]
lean_lib Dijkstra {
  -- add library configuration options here
}

meta if get_config? doc = some "on" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

require «std» from git
  "https://github.com/leanprover/std4" @ "28459f72f3190b0f540b49ab769745819eeb1c5e"
