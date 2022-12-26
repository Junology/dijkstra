import Lake
open Lake DSL

package dijkstra {
  -- add package configuration options here
}

lean_lib Dijkstra {
  -- add library configuration options here
}

@[default_target]
lean_exe dijkstra {
  root := `Main
}
