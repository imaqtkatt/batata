import Lake
open Lake DSL

package «batata» where
  -- add package configuration options here

lean_lib «Batata» where
  -- add library configuration options here

@[default_target]
lean_exe «batata» where
  root := `Main
